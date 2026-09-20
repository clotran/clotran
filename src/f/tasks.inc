  ! ---- tasks: the thread primitive -------------------------------------
  !
  ! A task is a closure run in a context of its own (PLAN.md: a thread
  ! is an evaluator context). One OS thread runs them all, so a task
  ! runs when it is submitted, until it finishes or BLOCKS -- on another
  ! task, on a latch, or on the clock -- and then it yields: its stacks
  ! stay parked in its context and whoever stepped it gets control
  ! back. That is a green thread. core.clj's future, promise, pmap and
  ! deref are its own definitions, verbatim, over the Java objects they
  ! expect: Agent/soloExecutor.submit answers a task, a task answers
  ! .get, .isDone and .cancel, and a CountDownLatch is an atom holding
  ! its count.
  !
  ! Yielding is only possible at a task's OUTERMOST run. A block reached
  ! through a native frame -- a callback from map, a nested eval -- has
  ! Fortran below it that cannot be parked, so it is PINNED, as Loom
  ! calls it, and the other tasks run right there, nested, until what
  ! it waits for is ready. The main context has no one to yield to and
  ! always does that. A wait nothing left to run can satisfy is a
  ! deadlock, and an error rather than a hang.
  !
  ! The pieces: task_submit makes and starts one; task_step runs one
  ! until it finishes or yields, bracketed like the debugger's handler
  ! (take_break); block_on is the one blocking primitive -- .get,
  ! .await and Thread.sleep are all it -- and decides between yielding
  ! and scheduling here; pick_runnable is the scheduler, a scan.

  ! Milliseconds of the system clock, for deadlines.
  function now_ms() result(ms)
    integer(gc_ip) :: ms, cnt, rate
    call system_clock(cnt, rate)
    ms = cnt / max(1_gc_ip, rate / 1000_gc_ip)
  end function now_ms

  ! (.submit executor f): a task over f, remembered until it finishes,
  ! and started now.
  recursive function task_submit(f) result(task)
    type(gc_value), intent(in) :: f
    type(gc_value) :: task, all
    integer :: base
    base = vs_enter(2)
    call vs_set(base + 1, f)
    task = gc_obj(OBJ_TASK, [vs_get(base + 1), gc_nil(), gc_nil(), gc_nil()], [vs_get(base + 1)])
    call vs_set(base + 2, task)
    if (.not. gc_root_live(tasks_root)) call gc_global_keep(tasks_root, gcv_empty([vs_get(base + 2)]))
    all = gcv_conj(gc_root_get(tasks_root), vs_get(base + 2), [vs_get(base + 2)])
    call gc_global_keep(tasks_root, all)
    call task_step(vs_get(base + 2))
    task = vs_get(base + 2)
    call vs_leave(base)
  end function task_submit

  ! Runs `task` in its context until it finishes or yields, then comes
  ! back. The switch is bracketed inside this call, the one safe shape
  ! (gce_ctx_switch): the caller's run never executes under the task's
  ! context. The first step binds the closure and pushes its body; a
  ! later one resumes the loop over the frames parked at the yield,
  ! which re-executes the node that blocked.
  recursive subroutine task_step(task)
    type(gc_value), intent(in) :: task
    type(gc_value) :: saved_task, frame, body, val, fn
    type(gc_value) :: none(0)
    integer :: here, id, saved_depth, base
    logical :: ok
    if (gc_i1(task) >= TASK_DONE .or. gc_i1(task) == TASK_RUNNING) return
    if (.not. task_trace_read) then
       block
         character(len=8) :: tb
         call get_environment_variable("CLOTRAN_TASK_TRACE", tb)
         task_trace = (trim(tb) == "1")
         task_trace_read = .true.
       end block
    end if
    here = gce_ctx_current()
    id = gc_i2(task)
    if (id == 0) then
       id = gce_ctx_new()
       call gc_set_i2(task, id)
    end if
    saved_task = cur_task
    saved_depth = task_loop_depth
    ctxs(id)%ev_depth = ev_depth   ! one Fortran stack: the nesting limit counts on
    cur_task = task
    call gce_ctx_switch(id)
    call gce_clear_error()
    yield_flag = .false.
    ev_depth = ev_depth + 1
    task_loop_depth = ev_depth
    if (gc_i1(task) == TASK_NEW) then
       base = vs_enter(1)   ! slot 1 of the fresh stack: run_loop's value slot
       fn = gc_slot(task, 1)
       call push_frame(fn, 0)
       ok = bind_closure(fn, gcv_empty(none), frame, body)
       if (ok) then
          call k_push(body, frame, ior(KF_FNBODY, KF_RESTART), body)
          call vs_set(kst(ksp)%base + 7, fn)
       else
          call pop_frame()
       end if
    end if
    call gc_set_i1(task, TASK_RUNNING)
    val = gc_nil()
    if (task_trace .and. ksp > 0) write(0, '(A,I0,A,I0,A,I0)') "task_step: resume top node kind=", &
         gc_i1(vs_get(kst(ksp)%base + 1)), " pc=", kst(ksp)%pc, " ksp=", ksp
    if (.not. has_error) val = run_loop(0, 0)
    if (task_trace) write(0, '(A,L1,A,L1,A,I0)') "task_step: back yield=", yield_flag, " err=", has_error, " ksp=", ksp
    ev_depth = ev_depth - 1
    if (yield_flag) then
       yield_flag = .false.
       if (gc_i1(task) == TASK_RUNNING) call gc_set_i1(task, TASK_RUNNABLE)
    else
       if (has_error) then
          call gc_set_slot(task, 2, failure_value())
          if (gc_i1(task) == TASK_RUNNING) call gc_set_i1(task, TASK_FAILED)
          call gce_clear_error()
       else if (gc_i1(task) == TASK_RUNNING) then
          call gc_set_slot(task, 2, val)
          call gc_set_i1(task, TASK_DONE)
       end if
       call vs_leave(0)
    end if
    call gce_ctx_switch(here)
    cur_task = saved_task
    task_loop_depth = saved_depth
    if (gc_i1(task) >= TASK_DONE) then
       call ctx_release(id)
       call gc_set_i2(task, 0)
    end if
  end subroutine task_step

  ! A failed task's failure: what it threw, or the host's message.
  function failure_value() result(v)
    type(gc_value) :: v
    type(gc_value) :: none(0)
    v = thrown_value()
    if (v%tag == GCT_NIL) v = error_value(gce_error(), none)
  end function failure_value

  ! What ExecutionException says: the failure's class and message.
  function failure_text(e) result(s)
    type(gc_value), intent(in) :: e
    character(len=:), allocatable :: s
    if (gc_kind(e) == OBJ_ERR) then
       s = class_name_of(e) // ": " // text_of(gc_slot(e, 2))
    else if (gca_is(e)) then
       s = text_of(gca_get(e, gc_key("error", [e])))
    else
       s = gcp_str(e, .true.)
    end if
  end function failure_text

  ! (.get task), or (.get task timeout unit) with a deadline: the value;
  ! the failure rethrown as ExecutionException; TimeoutException at the
  ! deadline; CancellationException if cancelled -- java.util.concurrent's
  ! names, which core.clj's deref-future catches.
  recursive function task_get(task, deadline) result(out)
    type(gc_value), intent(in) :: task
    integer(gc_ip), intent(in) :: deadline
    type(gc_value) :: out
    logical :: ready
    out = gc_nil()
    ready = block_on(task, deadline)
    if (yield_flag .or. has_error) return
    if (.not. ready) then
       call raise_class("java.util.concurrent.TimeoutException", "the future did not finish in time", [task])
       return
    end if
    select case (gc_i1(task))
    case (TASK_DONE)
       out = gc_slot(task, 2)
    case (TASK_CANCELLED)
       call raise_class("java.util.concurrent.CancellationException", "the future was cancelled", [task])
    case default
       call raise_class("java.util.concurrent.ExecutionException", failure_text(gc_slot(task, 2)), [task])
    end select
  end function task_get

  ! (.cancel task interrupt?): a task not yet finished is cancelled and
  ! never resumed, and its context goes back. One running now -- it is
  ! cancelling itself -- finishes its step first.
  function task_cancel(task) result(yes)
    type(gc_value), intent(in) :: task
    logical :: yes
    yes = .false.
    if (gc_kind(task) /= OBJ_TASK) return
    if (gc_i1(task) >= TASK_DONE) return
    yes = .true.
    if (gc_i1(task) /= TASK_RUNNING .and. gc_i2(task) /= 0) then
       call ctx_release(gc_i2(task))
       call gc_set_i2(task, 0)
    end if
    call gc_set_i1(task, TASK_CANCELLED)
  end function task_cancel

  ! Whether what a wait is for has happened: a task finished, a latch
  ! (an atom holding its count) at zero. Nil is the clock alone, and
  ! never ready by itself.
  function satisfied(target) result(yes)
    type(gc_value), intent(in) :: target
    logical :: yes
    type(gc_value) :: c
    yes = .true.
    if (target%tag == GCT_NIL) then
       yes = .false.
    else if (gc_kind(target) == OBJ_TASK) then
       yes = gc_i1(target) >= TASK_DONE
    else if (gc_kind(target) == OBJ_ATOM) then
       c = gc_slot(target, 1)
       if (c%tag == GCT_INT) yes = c%ival <= 0
    end if
  end function satisfied

  ! Done waiting: the running task's wait slots are cleared.
  subroutine clear_wait()
    if (gc_kind(cur_task) /= OBJ_TASK) return
    call gc_set_slot(cur_task, 3, gc_nil())
    call gc_set_slot(cur_task, 4, gc_nil())
  end subroutine clear_wait

  ! Parked, and its wait is over: what it waited for is ready, or its
  ! deadline has passed.
  function runnable_now(x) result(yes)
    type(gc_value), intent(in) :: x
    logical :: yes
    type(gc_value) :: dl
    yes = .false.
    if (gc_kind(x) /= OBJ_TASK) return
    if (gc_i1(x) /= TASK_RUNNABLE) return
    if (satisfied(gc_slot(x, 3))) then
       yes = .true.
       return
    end if
    dl = gc_slot(x, 4)
    if (dl%tag == GCT_INT) yes = now_ms() >= dl%ival
  end function runnable_now

  ! The scheduler: a task that can go on, `target` first so a deref runs
  ! the thing it waits for before anything else, else the first parked
  ! task whose wait is over. `sleeping` says whether any parked task
  ! has a deadline still to come, so a caller can tell a wait from a
  ! deadlock. Finished tasks are dropped from the list on the way.
  ! ponytail: a linear scan per decision; a run queue if task counts
  ! ever make it show.
  function pick_runnable(target, sleeping) result(t)
    type(gc_value), intent(in) :: target
    logical, intent(out) :: sleeping
    type(gc_value) :: t, all, kept, x, dl
    integer :: i, n, base
    logical :: prune
    t = gc_nil()
    sleeping = .false.
    if (runnable_now(target)) then
       t = target
       return
    end if
    if (.not. gc_root_live(tasks_root)) return
    all = gc_root_get(tasks_root)
    n = gcv_count(all)
    prune = .false.
    do i = 0, n - 1
       x = gcv_nth(all, i)
       if (gc_i1(x) >= TASK_DONE) then
          prune = .true.
          cycle
       end if
       if (t%tag == GCT_NIL) then
          if (runnable_now(x)) then
             t = x
             cycle
          end if
       end if
       if (gc_i1(x) == TASK_RUNNABLE) then
          dl = gc_slot(x, 4)
          if (dl%tag == GCT_INT) sleeping = .true.
       end if
    end do
    if (.not. prune) return
    base = vs_enter(1)
    kept = gcv_empty([all])
    call vs_set(base + 1, kept)
    do i = 0, n - 1
       x = gcv_nth(all, i)
       if (gc_i1(x) < TASK_DONE) then
          kept = gcv_conj(vs_get(base + 1), x, [vs_get(base + 1), all])
          call vs_set(base + 1, kept)
       end if
    end do
    call gc_global_keep(tasks_root, vs_get(base + 1))
    call vs_leave(base)
  end function pick_runnable

  function describe_wait(target) result(s)
    type(gc_value), intent(in) :: target
    character(len=:), allocatable :: s
    if (gc_kind(target) == OBJ_TASK) then
       s = "the future"
    else if (gc_kind(target) == OBJ_ATOM) then
       s = "the promise"
    else
       s = "the clock"
    end if
  end function describe_wait

  ! The one blocking primitive. Waits for `target` -- a task, a latch,
  ! or nil for the clock alone -- until `deadline` (now_ms, or -1 for
  ! none). .true. when the target is ready, .false. at the deadline, an
  ! error on deadlock. Inside a task at its outermost run this YIELDS:
  ! the task parks with the target and deadline on it and whoever
  ! stepped it goes on; the builtin that called this returns nil, and
  ! is re-executed when the task resumes, which is why a deadline it
  ! computed rides on the task rather than restarting. Anywhere else --
  ! the main context, or a task pinned under a native frame -- the
  ! other tasks run right here, nested, until the wait is over. With
  ! nothing runnable and a deadline still to come this spins; sleeping
  ! is the one thing a single thread cannot delegate.
  recursive function block_on(target, deadline0) result(ready)
    type(gc_value), intent(in) :: target
    integer(gc_ip), intent(in) :: deadline0
    logical :: ready
    integer(gc_ip) :: deadline
    type(gc_value) :: t, dl
    logical :: sleeping
    ready = satisfied(target)
    if (ready) then
       call clear_wait()
       return
    end if
    deadline = deadline0
    if (gc_kind(cur_task) == OBJ_TASK) then
       dl = gc_slot(cur_task, 4)
       if (dl%tag == GCT_INT) deadline = dl%ival
    end if
    if (deadline >= 0) then
       if (now_ms() >= deadline) then
          call clear_wait()
          return
       end if
    end if
    if (task_trace) write(0, '(A,I0,A,I0,A,I0,A,I0,A,I0,A,I0)') "block_on: cur_task kind=", gc_kind(cur_task), &
         " ev_depth=", ev_depth, " loop_depth=", task_loop_depth, " target kind=", gc_kind(target), &
         " top node kind=", gc_i1(vs_get(kst(ksp)%base + 1)), " ksp=", ksp
    if (gc_kind(cur_task) == OBJ_TASK .and. ev_depth == task_loop_depth) then
       call gc_set_slot(cur_task, 3, target)
       if (deadline >= 0) then
          call gc_set_slot(cur_task, 4, gc_int(deadline))
       else
          call gc_set_slot(cur_task, 4, gc_nil())
       end if
       yield_flag = .true.
       return
    end if
    do
       t = pick_runnable(target, sleeping)
       if (gc_kind(t) == OBJ_TASK) then
          call task_step(t)
          if (has_error) return
       else if (deadline < 0 .and. .not. sleeping) then
          call fail("deadlock: nothing left to run can make " // describe_wait(target) // " ready")
          return
       end if
       ready = satisfied(target)
       if (ready) then
          call clear_wait()
          return
       end if
       if (deadline >= 0) then
          if (now_ms() >= deadline) then
             call clear_wait()
             return
          end if
       end if
    end do
  end function block_on

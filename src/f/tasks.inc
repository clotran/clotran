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

  ! ---- the baton (PLAN.md step 11, stage 1) --------------------------
  !
  ! Every task runs on its OWN OS thread (Threads.f90), so a task that
  ! blocks -- even below compiled code, with Fortran frames on its stack
  ! -- waits where it is, and is resumed there. Only one thread runs
  ! clotran code at a time: the one whose context holds the baton. The
  ! heap and the interpreter's globals stay single-threaded, and every
  ! answer is what it was.
  !
  ! Handing over is a context switch plus a wake-up: the holder switches
  ! the interpreter's globals to the next context (gce_ctx_switch, whose
  ! stacks the collector already scans in every context), names it in
  ! baton_ctx and wakes the waiters; the named thread goes on. Whoever
  ! hands a task the baton -- its STEPPER -- gets it back when the task
  ! blocks or ends, so scheduling is what it was under the green threads:
  ! deterministic, a future running when made until it blocks.

  subroutine baton_setup()
    logical :: ok
    if (baton_up) return
    ok = th_lock_init(baton_lock)
    ok = th_cond_init(baton_cond)
    baton_ctx = gce_ctx_current()
    call ctx_arrays(baton_ctx)
    ctx_task(baton_ctx) = gc_nil()
    baton_up = .true.
  end subroutine baton_setup

  ! The per-context arrays the baton keeps, grown to hold context `id`.
  subroutine ctx_arrays(id)
    integer, intent(in) :: id
    integer, allocatable :: ci(:)
    logical, allocatable :: cl(:)
    type(gc_value), allocatable :: ct(:)
    integer :: n
    if (.not. allocated(came_from)) then
       allocate(came_from(16), ctx_dying(16), ctx_task(16), ctx_native(16))
       came_from = 0
       ctx_dying = .false.
       ctx_native = .false.
       ctx_task = gc_nil()
    end if
    if (id <= size(came_from)) return
    n = max(2 * size(came_from), id)
    allocate(ci(n), cl(n), ct(n))
    ci = 0
    cl = .false.
    ct = gc_nil()
    ci(1:size(came_from)) = came_from
    cl(1:size(came_from)) = ctx_dying
    ct(1:size(came_from)) = ctx_task
    call move_alloc(ci, came_from)
    call move_alloc(cl, ctx_dying)
    call move_alloc(ct, ctx_task)
    allocate(cl(n))
    cl = .false.
    cl(1:size(ctx_native)) = ctx_native
    call move_alloc(cl, ctx_native)
  end subroutine ctx_arrays

  ! Give the baton to context `next`, and wait -- on this thread's own
  ! stack -- until it comes back. A context cancelled while it waits
  ! (task_cancel) ends its thread here instead.
  recursive subroutine hand_to(next)
    integer, intent(in) :: next
    integer :: me
    logical :: ok
    me = gce_ctx_current()
    call ctx_arrays(max(me, next))
    came_from(next) = me
    call gce_ctx_switch(next)
    cur_task = ctx_task(next)
    ok = th_lock_acquire(baton_lock)
    baton_ctx = next
    ok = th_cond_broadcast(baton_cond)
    do while (baton_ctx /= me)
       if (ctx_dying(me)) then
          ok = th_lock_release(baton_lock)
          call th_exit()
       end if
       ok = th_cond_wait(baton_cond, baton_lock)
    end do
    ok = th_lock_release(baton_lock)
  end subroutine hand_to

  ! ---- native calls off the baton (PLAN.md step 11, stage 2) ----------
  !
  ! A task calling a Fortran package touches no heap while the routine
  ! runs -- its arrays are buffers that never move, kept alive by the
  ! task's own parked stack -- so it gives the baton away for the call:
  ! parks as "native", hands the baton to its stepper WITHOUT waiting,
  ! and runs the routine. Meanwhile clotran code goes on elsewhere, and
  ! other tasks' routines run at the same time: (pmap solve molecules)
  ! with ChemSol behind solve uses every core. When the routine returns
  ! the task waits to be stepped again, and only then touches the heap.
  ! The main context keeps the baton through its own native calls: no
  ! one would be stepped meanwhile.

  ! Give the baton to `next` and go on without waiting for it back.
  subroutine give_baton(next)
    integer, intent(in) :: next
    logical :: ok
    call gce_ctx_switch(next)
    cur_task = ctx_task(next)
    ok = th_lock_acquire(baton_lock)
    baton_ctx = next
    ok = th_cond_broadcast(baton_cond)
    ok = th_lock_release(baton_lock)
  end subroutine give_baton

  ! Before a native call: a task parks as native and lets its stepper
  ! go on. `me` is its context; `released` whether the baton was given.
  subroutine native_begin(me, released)
    integer, intent(out) :: me
    logical, intent(out) :: released
    logical :: ok
    released = .false.
    me = 0
    if (.not. baton_up) return
    if (gc_kind(cur_task) /= OBJ_TASK) return
    me = gce_ctx_current()
    call ctx_arrays(me)
    ! parked with nothing to wait for but the call itself: runnable as
    ! soon as it returns (a deadline already past; runnable_now)
    call gc_set_slot(cur_task, 3, gc_nil())
    call gc_set_slot(cur_task, 4, gc_int(0_gc_ip))
    call gc_set_i1(cur_task, TASK_RUNNABLE)
    ok = th_lock_acquire(baton_lock)
    ctx_native(me) = .true.
    natives_running = natives_running + 1
    ok = th_lock_release(baton_lock)
    call give_baton(came_from(me))
    released = .true.
  end subroutine native_begin

  ! After it: say so, wake whoever waits for a native call to end, and
  ! wait to be stepped -- the stepper switches the globals back to `me`.
  subroutine native_end(me)
    integer, intent(in) :: me
    logical :: ok
    ok = th_lock_acquire(baton_lock)
    ctx_native(me) = .false.
    natives_running = natives_running - 1
    native_gen = native_gen + 1
    ok = th_cond_broadcast(baton_cond)
    do while (baton_ctx /= me)
       if (ctx_dying(me)) then
          ok = th_lock_release(baton_lock)
          call th_exit()
       end if
       ok = th_cond_wait(baton_cond, baton_lock)
    end do
    ok = th_lock_release(baton_lock)
    call clear_wait()
  end subroutine native_end

  ! The native section for code outside this module -- compiled code,
  ! through ClotranABI.
  subroutine gce_native_begin(me, released)
    integer, intent(out) :: me
    logical, intent(out) :: released
    call native_begin(me, released)
  end subroutine gce_native_begin

  subroutine gce_native_end(me)
    integer, intent(in) :: me
    call native_end(me)
  end subroutine gce_native_end

  ! Whether context `id` is inside a native call now.
  logical function in_native(id)
    integer, intent(in) :: id
    logical :: ok
    in_native = .false.
    if (.not. baton_up) return
    if (id < 1 .or. .not. allocated(ctx_native)) return
    if (id > size(ctx_native)) return
    ok = th_lock_acquire(baton_lock)
    in_native = ctx_native(id)
    ok = th_lock_release(baton_lock)
  end function in_native

  ! The generation of finished native calls, and how many still run.
  subroutine native_state(gen, running)
    integer, intent(out) :: gen, running
    logical :: ok
    gen = 0
    running = 0
    if (.not. baton_up) return
    ok = th_lock_acquire(baton_lock)
    gen = native_gen
    running = natives_running
    ok = th_lock_release(baton_lock)
  end subroutine native_state

  ! Wait until a native call that was running at generation `gen` ends.
  subroutine wait_native(gen)
    integer, intent(in) :: gen
    logical :: ok
    ok = th_lock_acquire(baton_lock)
    do while (native_gen == gen .and. natives_running > 0)
       ok = th_cond_wait(baton_cond, baton_lock)
    end do
    ok = th_lock_release(baton_lock)
  end subroutine wait_native

  ! A task's thread: wait for the baton, run the task's body to its end,
  ! give its context back and the baton to its stepper, and finish.
  recursive function task_thread_main(arg) result(r) bind(C)
    type(c_ptr), value :: arg
    type(c_ptr) :: r
    type(gc_value) :: task, fn, frame, body, val
    type(gc_value) :: none(0)
    integer :: me, next, base
    logical :: ok
    r = c_null_ptr
    me = int(transfer(arg, 0_c_intptr_t))
    ok = th_lock_acquire(baton_lock)
    do while (baton_ctx /= me)
       if (ctx_dying(me)) then
          ok = th_lock_release(baton_lock)
          return
       end if
       ok = th_cond_wait(baton_cond, baton_lock)
    end do
    ok = th_lock_release(baton_lock)
    ! the stepper switched the globals to this context before handing over
    task = ctx_task(me)
    call gce_clear_error()
    val = gc_nil()
    base = vs_enter(1)   ! slot 1 of the fresh stack: run_loop's value slot
    fn = gc_slot(task, 1)
    call push_frame(fn, 0)
    ok = bind_closure(fn, gcv_empty(none), frame, body)
    if (ok) then
       call k_push(body, frame, ior(KF_FNBODY, KF_RESTART), body)
       call vs_set(kst(ksp)%base + 7, fn)
       if (task_trace) write(0, '(A,I0)') "task thread: running context ", me
       if (.not. has_error) val = run_loop(0, 0)
    else
       call pop_frame()
    end if
    if (has_error) then
       call gc_set_slot(task, 2, failure_value())
       if (gc_i1(task) == TASK_RUNNING) call gc_set_i1(task, TASK_FAILED)
       call gce_clear_error()
    else if (gc_i1(task) == TASK_RUNNING) then
       call gc_set_slot(task, 2, val)
       call gc_set_i1(task, TASK_DONE)
    end if
    call vs_leave(0)
    ! back to the stepper, for good: this context goes back for reuse
    next = came_from(me)
    call gce_ctx_switch(next)
    cur_task = ctx_task(next)
    ctx_task(me) = gc_nil()
    call ctx_release(me)
    ok = th_lock_acquire(baton_lock)
    baton_ctx = next
    ok = th_cond_broadcast(baton_cond)
    ok = th_lock_release(baton_lock)
  end function task_thread_main

  ! Runs `task` until it finishes or blocks, then comes back: a new one
  ! gets a context and a thread; a parked one is handed the baton where
  ! it waits.
  recursive subroutine task_step(task)
    type(gc_value), intent(in) :: task
    integer :: id
    if (gc_i1(task) >= TASK_DONE .or. gc_i1(task) == TASK_RUNNING) return
    if (.not. task_trace_read) then
       block
         character(len=8) :: tb
         call get_environment_variable("CLOTRAN_TASK_TRACE", tb)
         task_trace = (trim(tb) == "1")
         task_trace_read = .true.
       end block
    end if
    call baton_setup()
    id = gc_i2(task)
    if (id == 0) then
       id = gce_ctx_new()
       call gc_set_i2(task, id)
       call ctx_arrays(id)
       ctx_task(id) = task
       ctx_dying(id) = .false.
       call gc_set_i1(task, TASK_RUNNING)
       if (.not. th_spawn(c_funloc(task_thread_main), transfer(int(id, c_intptr_t), c_null_ptr), &
            TASK_STACK_BYTES)) then
          call gc_set_i1(task, TASK_FAILED)
          call gc_set_slot(task, 2, error_value("could not start a thread for the future", [task]))
          ctx_task(id) = gc_nil()
          call ctx_release(id)
          call gc_set_i2(task, 0)
          return
       end if
    else
       call gc_set_i1(task, TASK_RUNNING)
    end if
    if (task_trace) write(0, '(A,I0)') "task_step: handing the baton to context ", id
    call hand_to(id)
    ! the baton is back: the task has ended -- its context went back with
    ! it -- or it is parked, waiting
    if (gc_i1(task) >= TASK_DONE) call gc_set_i2(task, 0)
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
       ! its thread waits for the baton: tell it to end, and wake it.
       ! ponytail: the context id is not reused -- a woken thread checking
       ! a reused id could run -- so each cancelled parked task keeps one.
       block
         logical :: ok
         ctx_dying(gc_i2(task)) = .true.
         ctx_task(gc_i2(task)) = gc_nil()
         ok = th_lock_acquire(baton_lock)
         ok = th_cond_broadcast(baton_cond)
         ok = th_lock_release(baton_lock)
       end block
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
       if (c%tag == GCT_INT) then
          yes = c%ival <= 0          ! a latch: its count
       else if (gcv_is(c)) then
          yes = gcv_count(c) > 0     ! a mailbox: a message
       end if
    end if
  end function satisfied

  ! A task's mailbox -- slot 5 -- or the main context's: an atom holding
  ! a vector of messages, made on first use. As a block_on target it is
  ! ready when it holds one (satisfied); the protocol's send! and
  ! receive are conj and a take (clotran/thread.cljf).
  function task_mailbox(t) result(mb)
    type(gc_value), intent(in) :: t
    type(gc_value) :: mb, v
    integer :: base
    mb = gc_nil()
    if (gc_kind(t) == OBJ_TASK) then
       mb = gc_slot(t, 5)
    else if (gc_root_live(main_mailbox_root)) then
       mb = gc_root_get(main_mailbox_root)
    end if
    if (gc_kind(mb) == OBJ_ATOM) return
    base = vs_enter(1)
    v = gcv_empty([t])
    call vs_set(base + 1, v)
    mb = gc_obj(OBJ_ATOM, [vs_get(base + 1), gc_nil()], [t, vs_get(base + 1)])
    if (gc_kind(t) == OBJ_TASK) then
       call gc_set_slot(t, 5, mb)
    else
       call gc_global_keep(main_mailbox_root, mb)
    end if
    call vs_leave(base)
  end function task_mailbox

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
    if (in_native(gc_i2(x))) return
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
       s = "the promise or mailbox"
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
    integer :: ngen, nrun
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
    if (gc_kind(cur_task) == OBJ_TASK) then
       ! A TASK parks right here, on its own thread's stack -- below
       ! compiled code or not -- and gives the baton back to its stepper,
       ! who steps it again once what it waits for is ready or its
       ! deadline has passed (runnable_now).
       call gc_set_slot(cur_task, 3, target)
       if (deadline >= 0) then
          call gc_set_slot(cur_task, 4, gc_int(deadline))
       else
          call gc_set_slot(cur_task, 4, gc_nil())
       end if
       call gc_set_i1(cur_task, TASK_RUNNABLE)
       call hand_to(came_from(gce_ctx_current()))
       ready = satisfied(target)
       call clear_wait()
       return
    end if
    do
       call native_state(ngen, nrun)
       t = pick_runnable(target, sleeping)
       if (gc_kind(t) == OBJ_TASK) then
          call task_step(t)
          if (has_error) return
       else if (nrun > 0) then
          ! tasks are inside native calls: one of them ending is progress
          call wait_native(ngen)
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

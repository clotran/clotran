  ! ---- tasks: the thread primitive -------------------------------------
  !
  ! A task is a closure run on an OS thread of its own, in an evaluator
  ! context of its own (PLAN.md: a thread is an evaluator context), and
  ! since step 14f the threads run AT ONCE: there is no baton. A future
  ! starts on its thread when it is made and goes on beside whoever made
  ! it. core.clj's future, promise, pmap and deref are its own
  ! definitions, verbatim, over the Java objects they expect:
  ! Agent/soloExecutor.submit answers a task, a task answers .get,
  ! .isDone and .cancel, and a CountDownLatch is an atom holding its
  ! count.
  !
  ! Waiting is waiting: block_on sleeps on the state lock's condition
  ! (GC.f90, gc_state_wait) until what it waits for is ready or its
  ! deadline passes, out of the running mutators meanwhile so the
  ! collector never waits for it. A wait nothing can satisfy -- every
  ! thread that could still run is waiting too, with no deadline -- is
  ! a deadlock, and an error rather than a hang (the progress counters,
  ! live_threads and blocked_*).
  !
  ! What makes a wait end is announced: a task finishing, a promise
  ! delivered, a latch counted down, a message sent all call
  ! gc_state_notify.

  ! Milliseconds of the system clock, for deadlines.
  function now_ms() result(ms)
    integer(gc_ip) :: ms, cnt, rate
    call system_clock(cnt, rate)
    ms = cnt / max(1_gc_ip, rate / 1000_gc_ip)
  end function now_ms

  ! (.submit executor f): a task over f, started now on its own thread.
  recursive function task_submit(f) result(task)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: f
    type(gc_value) :: task
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, f)
    task = gc_obj(OBJ_TASK, [vs_get(vst, base + 1), gc_nil(), gc_nil(), gc_nil()], [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, task)
    call task_start(vs_get(vst, base + 2))
    task = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function task_submit

  ! A new task's thread, started now. It counts as live from here, so a
  ! wait for it made before it runs is not taken for a deadlock.
  recursive subroutine task_start(task)
    type(gc_value), intent(in) :: task
    integer :: id
    if (.not. task_trace_read) then
       block
         character(len=8) :: tb
         call get_environment_variable("CLOTRAN_TASK_TRACE", tb)
         task_trace = (trim(tb) == "1")
         task_trace_read = .true.
       end block
    end if
    id = gce_ctx_new()
    ctxs(id)%c%task = task
    ctxs(id)%c%cur_task = task
    ! its context's root holds it until its thread is done: nothing else
    ! need hold a future someone started and dropped
    call gc_global_keep(ctxs(id)%c%task_root, task)
    call gc_state_lock()
    call gc_set_i2(task, id)
    call gc_set_i1(task, TASK_RUNNING)
    live_threads = live_threads + 1
    call gc_state_unlock()
    if (task_trace) write(0, '(A,I0)') "task_start: a thread for context ", id
    if (.not. th_spawn(c_funloc(task_thread_main), c_loc(ctxs(id)%c), TASK_STACK_BYTES)) then
       call gc_state_lock()
       call gc_set_i1(task, TASK_FAILED)
       live_threads = live_threads - 1
       call gc_state_unlock()
       call gc_set_slot(task, 2, error_value("could not start a thread for the future", [task]))
       ctxs(id)%c%task = gc_nil()
       call gc_global_keep(ctxs(id)%c%task_root, gc_nil())
       call ctx_release(id)
       call gc_state_notify()
    end if
  end subroutine task_start

  ! A task's thread: run the task's body to its end, record how it
  ! ended, announce it, give its context back, and finish.
  recursive function task_thread_main(arg) result(r) bind(C)
    type(eval_ctx), pointer :: tctx
    type(c_ptr), value :: arg
    type(c_ptr) :: r
    type(gc_value) :: task, fn, frame, body, val, res
    type(gc_value) :: none(0)
    integer :: me, base
    logical :: ok, failed
    type(eval_ctx), pointer :: mine
    r = c_null_ptr
    ! its context by address: the table may grow meanwhile
    call c_f_pointer(arg, mine)
    me = mine%id
    ! a mutator before it reads any shared table: a stop (collection,
    ! growth) now waits for this thread, and none is under way as it
    ! starts reading them
    call gc_mutator_enter()
    call gc_stack_bind(me)
    ok = th_key_set(ctx_key, c_loc(mine))
    call gc_bindings_set(gc_nil())   ! a new thread has none; binding-conveyor-fn gives it its maker's
    tctx => ctx_self()
    task = mine%task
    call gce_clear_error()
    val = gc_nil()
    base = vs_enter(2)   ! slot 1 of the fresh stack: run_loop's value slot
    call vs_set(base + 2, task)
    fn = gc_slot(task, 1)
    if (.not. is_node_closure(fn)) then
       ! a compiled fn -- a compiled closure since PLAN.md step 10a -- or
       ! a builtin: apply knows every kind
       if (task_trace) write(0, '(A,I0)') "task thread: applying in context ", me
       val = apply(fn, gcv_empty(none))
    else
       call push_frame(tctx, fn, 0)
       ok = bind_closure(fn, gcv_empty(none), frame, body)
       if (ok) then
          call k_push(body, frame, ior(KF_FNBODY, KF_RESTART), body)
          call vs_set(tctx%kst(tctx%ksp)%base + 7, fn)
          if (task_trace) write(0, '(A,I0)') "task thread: running context ", me
          if (.not. tctx%has_error) val = run_loop(0, 0)
       else
          call pop_frame(tctx)
       end if
    end if
    task = vs_get(base + 2)
    failed = tctx%has_error
    if (failed) then
       res = failure_value()
       call gce_clear_error()
    else
       res = val
    end if
    ! how it ended, unless it was cancelled meanwhile -- then its answer
    ! is dropped, as a cancelled Future's is
    call gc_state_lock()
    if (gc_i1(task) == TASK_RUNNING) then
       call gc_set_slot(task, 2, res)
       if (failed) then
          call gc_set_i1(task, TASK_FAILED)
       else
          call gc_set_i1(task, TASK_DONE)
       end if
    end if
    call gc_set_i2(task, 0)
    live_threads = live_threads - 1
    call gc_state_unlock()
    call gc_state_notify()
    call vs_leave(0)
    mine%task = gc_nil()
    mine%cur_task = gc_nil()
    call gc_global_keep(mine%task_root, gc_nil())
    call gc_bindings_set(gc_nil())
    ! this thread is done with its context: it goes back for reuse
    ok = th_key_set(ctx_key, c_null_ptr)
    call ctx_release(me)
    call gc_mutator_leave()
  end function task_thread_main

  ! A failed task's failure: what it threw, or the host's message.
  function failure_value() result(v)
    type(gc_value) :: v
    type(gc_value) :: none(0)
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    v = thrown_value()
    if (v%tag == GCT_NIL) then
       block
          call gce_error(s=dlt_1)
          v = error_value(dlt_1, none)
       end block
    end if
  end function failure_value

  ! What ExecutionException says: the failure's class and message.
  subroutine failure_text(e, s)
    type(gc_value), intent(in) :: e
    character(len=:), allocatable, intent(out) :: s
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    if (gc_kind(e) == OBJ_ERR) then
       block
          call class_name_of(e, s=dlt_1)
          call text_of(gc_slot(e, 2), s=dlt_2)
          s = dlt_1 // ": " // dlt_2
       end block
    else if (gca_is(e)) then
       block
          call text_of(gca_get(e, gc_key("error", [e])), s=dlt_1)
          s = dlt_1
       end block
    else
       block
          call gcp_str(e, .true., s=dlt_1)
          s = dlt_1
       end block
    end if
  end subroutine failure_text

  ! (.get task), or (.get task timeout unit) with a deadline: the value;
  ! the failure rethrown as ExecutionException; TimeoutException at the
  ! deadline; CancellationException if cancelled -- java.util.concurrent's
  ! names, which core.clj's deref-future catches.
  recursive function task_get(task, deadline) result(out)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: task
    integer(gc_ip), intent(in) :: deadline
    type(gc_value) :: out
    logical :: ready
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    out = gc_nil()
    ready = block_on(task, deadline)
    if (tctx%yield_flag .or. tctx%has_error) return
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
       block
          call failure_text(gc_slot(task, 2), s=dlt_1)
          call raise_class("java.util.concurrent.ExecutionException", dlt_1, [task])
       end block
    end select
  end function task_get

  ! (.cancel task interrupt?): a task not yet finished is cancelled --
  ! its thread's answer is dropped when it comes, a sleep in it ends at
  ! once, and a deref of it throws CancellationException. True if it was
  ! not finished, as Future.cancel answers.
  function task_cancel(task) result(yes)
    type(gc_value), intent(in) :: task
    logical :: yes
    yes = .false.
    if (gc_kind(task) /= OBJ_TASK) return
    call gc_state_lock()
    if (gc_i1(task) < TASK_DONE) then
       call gc_set_i1(task, TASK_CANCELLED)
       yes = .true.
    end if
    call gc_state_unlock()
    if (yes) call gc_state_notify()
  end function task_cancel

  ! Whether what a wait is for has happened: a task finished, a latch
  ! (an atom holding its count) at zero, a mailbox with a message. Nil
  ! is the clock alone, and never ready by itself. Read under the state
  ! lock, which the writers of all three hold.
  function satisfied(target) result(yes)
    type(gc_value), intent(in) :: target
    logical :: yes
    type(gc_value) :: c
    yes = .true.
    call gc_state_lock()
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
    call gc_state_unlock()
  end function satisfied

  ! A task's mailbox -- slot 5 -- or the main context's: an atom holding
  ! a vector of messages, made on first use. As a block_on target it is
  ! ready when it holds one (satisfied); the protocol's send! and
  ! receive are conj and a take (clotran/thread.cljf). Two threads
  ! making it at once keep ONE: the second finds the first's.
  function task_mailbox(t) result(mb)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: t
    type(gc_value) :: mb, v
    integer :: base
    vst => gc_my_stack()
    mb = gc_nil()
    if (gc_kind(t) == OBJ_TASK) then
       mb = gc_cell_get(t, 5)
    else if (gc_root_live(main_mailbox_root)) then
       mb = gc_root_get(main_mailbox_root)
    end if
    if (gc_kind(mb) == OBJ_ATOM) return
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 2, t)
    v = gcv_empty([vs_get(vst, base + 2)])
    call vs_set(vst, base + 1, v)
    mb = gc_obj(OBJ_ATOM, [vs_get(vst, base + 1), gc_nil()], [vs_get(vst, base + 2), vs_get(vst, base + 1)])
    call vs_set(vst, base + 1, mb)
    if (gc_kind(vs_get(vst, base + 2)) == OBJ_TASK) then
       if (.not. gc_cell_cas(vs_get(vst, base + 2), 5, gc_nil(), mb)) mb = gc_cell_get(vs_get(vst, base + 2), 5)
    else
       if (.not. gc_root_cas(main_mailbox_root, gc_nil(), mb)) mb = gc_root_get(main_mailbox_root)
    end if
    call vs_leave(vst, base)
  end function task_mailbox

  subroutine describe_wait(target, s)
    type(gc_value), intent(in) :: target
    character(len=:), allocatable, intent(out) :: s
    if (gc_kind(target) == OBJ_TASK) then
       s = "the future"
    else if (gc_kind(target) == OBJ_ATOM) then
       s = "the promise or mailbox"
    else
       s = "the clock"
    end if
  end subroutine describe_wait

  ! The one blocking primitive. Waits for `target` -- a task, a latch or
  ! mailbox, or nil for the clock alone -- until `deadline` (now_ms, or
  ! -1 for none). .true. when the target is ready, .false. at the
  ! deadline, an error on deadlock: when every thread that could still
  ! run waits too, with no deadline among them. A cancelled task's own
  ! sleep ends at once. The wait is on the state lock's condition, out
  ! of the running mutators (GC.f90, gc_state_wait).
  recursive function block_on(target, deadline) result(ready)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: target
    integer(gc_ip), intent(in) :: deadline
    logical :: ready, dead, cancelled, suspect
    integer(gc_ip) :: left
    integer :: seen
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    ready = .false.
    dead = .false.
    suspect = .false.
    seen = 0
    call gc_state_lock()
    do
       if (satisfied(target)) then
          ready = .true.
          exit
       end if
       if (deadline >= 0) then
          left = deadline - now_ms()
          if (left <= 0) exit
       end if
       cancelled = .false.
       if (gc_kind(tctx%cur_task) == OBJ_TASK) cancelled = gc_i1(tctx%cur_task) == TASK_CANCELLED
       if (cancelled) exit
       ! Every live thread waiting, none with a deadline, looks like a
       ! deadlock -- but a waiter whose target was just made ready still
       ! counts as blocked until it wakes and takes the lock. So the verdict
       ! stands only if it holds again after a short wait in which nothing
       ! was announced (notify_gen unchanged): a thread that was about to
       ! run would have run, and announced it, by then.
       if (deadline < 0 .and. blocked_dl == 0 .and. blocked_nodl + 1 >= live_threads) then
          if (suspect .and. gc_notify_gen() == seen) then
             dead = .true.
             exit
          end if
          suspect = .true.
          seen = gc_notify_gen()
          blocked_dl = blocked_dl + 1
          call gc_state_wait(100_8)
          blocked_dl = blocked_dl - 1
          cycle
       end if
       suspect = .false.
       ! PARKED while it waits -- what a task's state reports (thread.cljf)
       ! -- and running again after, unless it was cancelled meanwhile
       if (gc_kind(tctx%cur_task) == OBJ_TASK) then
          if (gc_i1(tctx%cur_task) == TASK_RUNNING) call gc_set_i1(tctx%cur_task, TASK_RUNNABLE)
       end if
       if (deadline < 0) then
          blocked_nodl = blocked_nodl + 1
          call gc_state_wait(-1_8)
          blocked_nodl = blocked_nodl - 1
       else
          blocked_dl = blocked_dl + 1
          call gc_state_wait(int(left, 8))
          blocked_dl = blocked_dl - 1
       end if
       if (gc_kind(tctx%cur_task) == OBJ_TASK) then
          if (gc_i1(tctx%cur_task) == TASK_RUNNABLE) call gc_set_i1(tctx%cur_task, TASK_RUNNING)
       end if
    end do
    call gc_state_unlock()
    ! a waiter's exit may leave the others with no one to wait for
    call gc_state_notify()
    if (dead) then
       block
          call describe_wait(target, s=dlt_1)
          call fail("deadlock: nothing left to run can make " // dlt_1 // " ready")
       end block
    end if
  end function block_on

  ! ---- native calls (PLAN.md step 11, stage 2; step 14f) ---------------
  !
  ! A Fortran package's routine, or a compiled loop that touches no
  ! heap, runs outside the running mutators: a collection elsewhere does
  ! not wait for it. It is still progress, not a wait.

  subroutine native_begin(me, released)
    integer, intent(out) :: me
    logical, intent(out) :: released
    me = 0
    released = .true.
    call gc_mutator_leave()
  end subroutine native_begin

  subroutine native_end(me)
    integer, intent(in) :: me
    call gc_mutator_enter()
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

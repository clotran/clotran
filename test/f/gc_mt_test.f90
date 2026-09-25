! gc_mt_test -- the collector with several threads allocating at once
! (PLAN.md step 14c). Each thread builds rooted chains on its own value
! stack while the others do the same; under torture EVERY allocation
! collects, so every allocation has to stop the other threads at a
! safepoint, mark their stacks and their in-flight roots, and let them
! go. A chain that comes back short or wrong is a lost root or a slot
! handed out twice. Run under both compilers by `make test`.
module gc_mt_work
  use iso_c_binding
  use GC
  implicit none
  integer, parameter :: NTHREADS = 4, ROUNDS = 6, LEN = 150
  integer, save :: bad(NTHREADS) = 0
contains
  function worker(arg) result(r) bind(C)
    type(c_ptr), value :: arg
    type(c_ptr) :: r
    integer :: me, round, i, n, base
    type(gc_value) :: head, roots(1), p, v
    me = int(transfer(arg, 0_c_intptr_t))
    call gc_stack_bind(me + 1)          ! stack 1 is the main thread's
    call gc_mutator_enter()
    base = vs_enter(1)
    do round = 1, ROUNDS
       head = gc_nil()
       do i = 1, LEN
          roots(1) = head
          ! a string and a cons per step: two pools, each a safepoint
          head = gc_cons(gc_int(int(me * 100000 + i, gc_ip)), head, roots)
          ! the new cell lives ONLY in this call's roots: if this thread
          ! parks here, another thread's collection must see it through
          ! what the parked allocation published
          roots(1) = head
          p = gc_str("x", roots)
          call vs_set(base + 1, head)
       end do
       ! read back: LEN cells, counting down from this thread's last
       n = 0
       p = vs_get(base + 1)
       do while (gc_kind(p) == OBJ_CONS .and. n <= LEN)   ! bounded: a corrupt chain can loop
          v = gc_car(p)
          if (v%ival /= me * 100000 + LEN - n) bad(me) = bad(me) + 1
          n = n + 1
          p = gc_cdr(p)
       end do
       if (n /= LEN) bad(me) = bad(me) + 1
    end do
    call vs_leave(base)
    call gc_mutator_leave()
    r = c_null_ptr
  end function worker
end module gc_mt_work

program gc_mt_test
  use iso_c_binding
  use Threads
  use GC
  use gc_mt_work
  implicit none
  type(th_thread) :: ts(NTHREADS)
  integer :: i, fails
  integer(8) :: before
  fails = 0
  call gc_init(8)
  do i = 1, NTHREADS
     call gc_stack_new(i + 1)
  end do
  gc_torture = .true.
  before = gc_collections
  ! the main thread allocates nothing while they run: it steps aside, or
  ! every stop would wait for it
  call gc_mutator_leave()
  do i = 1, NTHREADS
     if (.not. th_start(ts(i), c_funloc(worker), transfer(int(i, c_intptr_t), c_null_ptr))) fails = fails + 1
  end do
  do i = 1, NTHREADS
     if (.not. th_join(ts(i))) fails = fails + 1
  end do
  call gc_mutator_enter()
  gc_torture = .false.
  do i = 1, NTHREADS
     if (bad(i) /= 0) then
        print '(a, i0, a, i0)', 'FAIL - thread ', i, ': chains wrong ', bad(i)
        fails = fails + 1
     end if
  end do
  if (gc_collections - before < NTHREADS * ROUNDS * LEN) then
     print '(a, i0)', 'FAIL - torture did not collect at every allocation: ', gc_collections - before
     fails = fails + 1
  end if
  if (fails == 0) then
     print '(a)', ' GC MT TESTS PASSED'
  else
     print '(a, i0)', ' GC MT TESTS FAILED: ', fails
     error stop 1
  end if
end program gc_mt_test

! threads_test -- the Threads module (src/f/Threads.f90) on its own:
! a strict hand-off between two threads, and many threads counting under
! one lock. Run under both compilers by `make test`.
module threads_test_work
  use iso_c_binding
  use Threads
  implicit none
  type(th_lock), save :: lk
  type(th_cond), save :: cv
  integer, save :: turn = 0, log_n = 0, log(20) = 0
  integer(c_int64_t), save :: counter = 0
contains
  ! thread 2's half of the hand-off: waits for its turn five times
  function pinger(arg) result(r) bind(C)
    type(c_ptr), value :: arg
    type(c_ptr) :: r
    integer :: i
    logical :: ok
    do i = 1, 5
       ok = th_lock_acquire(lk)
       do while (turn /= 1)
          ok = th_cond_wait(cv, lk)
       end do
       log_n = log_n + 1; log(log_n) = 2
       turn = 0
       ok = th_cond_broadcast(cv)
       ok = th_lock_release(lk)
    end do
    r = c_null_ptr
  end function pinger
  function adder(arg) result(r) bind(C)
    type(c_ptr), value :: arg
    type(c_ptr) :: r
    integer :: i
    logical :: ok
    do i = 1, 100000
       ok = th_lock_acquire(lk)
       counter = counter + 1
       ok = th_lock_release(lk)
    end do
    r = c_null_ptr
  end function adder
end module threads_test_work

program threads_test
  use iso_c_binding
  use Threads
  use threads_test_work
  implicit none
  type(th_thread) :: t, ts(4)
  integer :: i, fails
  logical :: ok
  fails = 0
  if (.not. th_lock_init(lk)) fails = fails + 1
  if (.not. th_cond_init(cv)) fails = fails + 1

  ! a strict hand-off: 1 2 1 2 ... -- neither thread ever runs twice
  if (.not. th_start(t, c_funloc(pinger), c_null_ptr)) fails = fails + 1
  do i = 1, 5
     ok = th_lock_acquire(lk)
     do while (turn /= 0)
        ok = th_cond_wait(cv, lk)
     end do
     log_n = log_n + 1; log(log_n) = 1
     turn = 1
     ok = th_cond_broadcast(cv)
     ok = th_lock_release(lk)
  end do
  if (.not. th_join(t)) fails = fails + 1
  if (any(log(1:10) /= [1, 2, 1, 2, 1, 2, 1, 2, 1, 2])) then
     print '(a, 10i2)', 'FAIL - hand-off order', log(1:10)
     fails = fails + 1
  end if

  ! four threads, one lock, one counter: no increment lost
  do i = 1, 4
     if (.not. th_start(ts(i), c_funloc(adder), c_null_ptr)) fails = fails + 1
  end do
  do i = 1, 4
     if (.not. th_join(ts(i))) fails = fails + 1
  end do
  if (counter /= 400000) then
     print '(a, i0)', 'FAIL - counted ', counter
     fails = fails + 1
  end if

  if (fails == 0) then
     print '(a)', ' THREADS TESTS PASSED'
  else
     print '(a, i0)', ' THREADS TESTS FAILED: ', fails
     error stop 1
  end if
end program threads_test

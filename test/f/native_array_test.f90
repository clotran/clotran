! native_array_test: what compiled code relies on the array registry for.
!
! A compiled loop over a ^doubles parameter holds a POINTER into that
! array's buffer for the loop's whole run, and the loop may allocate
! other arrays while it runs. So a buffer must stay where it is when the
! registry grows. It did not: growth assigned the nodes to a bigger
! registry, which deep-copies every allocatable component, and every
! buffer moved.
!
! This checks the invariant directly -- the address before and after,
! and the values still there -- rather than trying to catch a read of
! freed memory, which depends on the allocator and proves nothing on a
! platform that happens not to reuse the block.
program native_array_test
  use iso_c_binding
  use NativeArray
  implicit none

  integer, parameter :: dp = kind(1.0d0)
  integer :: failures, h, i, other
  character(len=:), allocatable :: err
  real(dp), pointer, contiguous :: p(:)
  integer(8), pointer, contiguous :: q(:)
  integer(c_intptr_t) :: before, after
  logical :: ok

  failures = 0

  h = gcna_new("real8", [5], [0], err)
  call gcna_real8_ptr(h, p, ok)
  call check("a real8 array hands out a pointer", ok)
  do i = 1, 5
     p(i) = real(i, dp) * 1.5_dp
  end do
  before = transfer(c_loc(p(1)), before)

  ! enough arrays that the registry has to grow several times over
  do i = 1, 200
     other = gcna_new("real8", [5], [0], err)
  end do

  call gcna_real8_ptr(h, p, ok)
  after = transfer(c_loc(p(1)), after)
  call check("the buffer is where it was after the registry grew", before == after)
  call check("and still holds what was written", &
       abs(p(1) - 1.5_dp) < 1.0e-12_dp .and. abs(p(5) - 7.5_dp) < 1.0e-12_dp)

  h = gcna_new("int8", [3], [0], err)
  call gcna_int8_ptr(h, q, ok)
  call check("an int8 array hands out a pointer too", ok .and. size(q) == 3)
  call gcna_real8_ptr(h, p, ok)
  call check("and is not a real8 one", .not. ok)

  ! a freed slot is taken again, the lowest first: claim() searches from
  ! a hint, not from 1, and a release must move the hint back down
  call gcna_release(other - 100)
  call gcna_release(other - 150)
  call check("a freed slot is reused, the lowest first", gcna_new("real8", [1], [0], err) == other - 150)
  call check("then the next freed one", gcna_new("real8", [1], [0], err) == other - 100)
  call check("then a new one past the last", gcna_new("real8", [1], [0], err) == h + 1)

  if (failures == 0) then
     print *, "NATIVE ARRAY TESTS PASSED"
  else
     print *, "NATIVE ARRAY TESTS FAILED:", failures
     stop 1
  end if

contains

  subroutine check(label, cond)
    character(len=*), intent(in) :: label
    logical, intent(in) :: cond
    if (cond) then
       print *, "ok   - ", label
    else
       print *, "FAIL - ", label
       failures = failures + 1
    end if
  end subroutine check

end program native_array_test

! Validates rc_module's refcounting on gfortran and flang. Checked
! automatically; the final check confirms every box was freed once.
module holder_module
  use rc_module
  implicit none

  ! No assignment(=) here: demonstrates the aliasing hazard.
  type :: holder_naive
     type(rc) :: slots(2)
  end type holder_naive

  ! The correct pattern: explicit assignment(=) below propagates by hand.
  type :: holder
     type(rc) :: slots(2)
  end type holder

  interface assignment(=)
     module procedure holder_assign
  end interface assignment(=)

contains

  subroutine holder_assign(lhs, rhs)
    type(holder), intent(inout) :: lhs
    type(holder), intent(in) :: rhs
    lhs%slots(1) = rhs%slots(1)
    lhs%slots(2) = rhs%slots(2)
  end subroutine holder_assign

end module holder_module

program rc_test
  use rc_module
  use holder_module
  implicit none

  logical :: all_ok
  type(rc) :: a, b, c

  all_ok = .true.

  ! 1. Scope exit runs FINAL.
  block
    integer :: freed_before
    freed_before = rc_total_freed
    block
      type(rc) :: h
      h = rc_new(1)
      call expect_eq("1a. fresh handle has refcount 1: ", rc_refcount(h), 1, all_ok)
    end block
    call expect_eq("1b. block-scope exit freed the box: ", rc_total_freed - freed_before, 1, all_ok)
  end block

  ! 2. Assignment shares the box; releasing one handle doesn't free it.
  a = rc_new(10)
  b = a
  call expect_eq("2a. refcount after a=rc_new; b=a: ", rc_refcount(a), 2, all_ok)
  call expect_eq("2b. both handles see the same refcount: ", rc_refcount(b), 2, all_ok)
  call expect_eq("2c. payload reads through either handle: ", rc_payload(b), 10, all_ok)
  call rc_release(b)
  call expect_eq("2d. releasing b drops a's refcount to 1: ", rc_refcount(a), 1, all_ok)
  call rc_release(a)

  ! 3. Reassignment releases the old reference.
  block
    integer :: freed_before
    a = rc_new(20)
    b = rc_new(30)
    freed_before = rc_total_freed
    a = b ! a's old box (20) should be dropped to 0 and freed here
    call expect_eq("3a. a=b frees a's old box immediately: ", rc_total_freed - freed_before, 1, all_ok)
    call expect_eq("3b. a and b now share refcount 2: ", rc_refcount(a), 2, all_ok)
    call rc_release(a)
    call rc_release(b)
  end block

  ! 4. Self-assignment is a no-op, not a use-after-free.
  a = rc_new(5)
  a = a
  call expect_eq("4a. self-assignment leaves refcount at 1: ", rc_refcount(a), 1, all_ok)
  call expect_eq("4b. and the payload intact: ", rc_payload(a), 5, all_ok)
  call rc_release(a)

  ! 5. Array deallocation frees every element (impure elemental FINAL).
  block
    type(rc), allocatable :: arr(:)
    integer :: freed_before
    allocate(arr(3))
    arr(1) = rc_new(100)
    arr(2) = rc_new(200)
    arr(3) = rc_new(300)
    freed_before = rc_total_freed
    deallocate(arr)
    call expect_eq("5. deallocating an array frees all 3 elements: ", &
         rc_total_freed - freed_before, 3, all_ok)
  end block

  ! 6. A handle returned from a function isn't leaked to refcount 2.
  c = make_handle(99)
  call expect_eq("6a. handle returned from a function has refcount 1: ", rc_refcount(c), 1, all_ok)
  call expect_eq("6b. and the right payload: ", rc_payload(c), 99, all_ok)
  call rc_release(c)

  ! 7a. Default assignment aliases without bumping refcount (h2 is a
  !     leaked pointer on purpose, so its dangling alias is never touched).
  block
    type(holder_naive) :: h1
    type(holder_naive), pointer :: h2
    h1%slots(1) = rc_new(111)
    allocate(h2)
    h2 = h1
    call expect_eq("7a. default assignment does NOT bump the embedded refcount: ", &
         rc_refcount(h1%slots(1)), 1, all_ok)
    call rc_release(h1%slots(1))
  end block

  ! 7b-d. holder's own assignment(=) does it correctly.
  block
    type(holder) :: h1, h2
    h1%slots(1) = rc_new(111)
    h1%slots(2) = rc_new(222)
    h2 = h1
    call expect_eq("7b. holder's own assignment(=) shares slot 1 correctly: ", &
         rc_refcount(h1%slots(1)), 2, all_ok)
    call expect_eq("7c. ...and slot 2: ", rc_refcount(h1%slots(2)), 2, all_ok)
    call rc_release(h1%slots(1))
    call rc_release(h1%slots(2))
    call expect_eq("7d. releasing h1's slots still leaves h2 valid: ", &
         rc_refcount(h2%slots(1)), 1, all_ok)
    call rc_release(h2%slots(1))
    call rc_release(h2%slots(2))
  end block

  ! 9. Whole-array assignment works if both sides are pre-allocated
  !    (auto-reallocating the LHS instead crashes on both compilers).
  block
    type(rc), allocatable :: arr_a(:), arr_b(:)
    integer :: i
    allocate(arr_a(2), arr_b(2))
    arr_a(1) = rc_new(700)
    arr_a(2) = rc_new(800)
    arr_b = arr_a
    call expect_eq("9a. whole-array assignment shares refcount 2: ", &
         rc_refcount(arr_a(1)), 2, all_ok)
    call expect_eq("9b. ...and reads the right payload: ", rc_payload(arr_b(2)), 800, all_ok)
    do i = 1, 2
       call rc_release(arr_a(i))
       call rc_release(arr_b(i))
    end do
  end block

  ! Everything should be freed now (7a's box was freed via h1, not h2).
  call expect_eq("10. every allocated box was freed exactly once: ", &
       rc_total_freed, rc_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL RC CHECKS PASSED"
  else
     print *, ""
     print *, "RC CHECKS FAILED"
     stop 1
  end if

contains

  function make_handle(payload) result(h)
    integer, intent(in) :: payload
    type(rc) :: h
    h = rc_new(payload)
  end function make_handle

  subroutine expect_eq(label, actual, expected, ok)
    character(len=*), intent(in) :: label
    integer, intent(in) :: actual, expected
    logical, intent(inout) :: ok
    if (actual == expected) then
       print '(A,A,I0)', "ok   - ", label, actual
    else
       print '(A,A,I0,A,I0,A)', "FAIL - ", label, actual, "  (expected ", expected, ")"
       ok = .false.
    end if
    flush(6) ! so a later crash doesn't hide every check up to that point
  end subroutine expect_eq

end program rc_test

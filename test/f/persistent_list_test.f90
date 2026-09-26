! Exercises the GC-backed persistent list on its own. The interesting
! cases are the ones a refcounted list makes expensive or unsafe:
! two lists sharing a tail, and a long chain rooted only from its head
! while every allocation collects.
program persistent_list_test
  use GC
  use PersistentList
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_empty()
  call check_cons_first_rest()
  call check_shared_tail()
  call check_survives_collection()
  call check_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCLIST CHECKS PASSED"
  else
     print *, ""
     print *, "GCLIST CHECKS FAILED"
     stop 1
  end if

contains

  subroutine ok(label, condition)
    character(len=*), intent(in) :: label
    logical, intent(in) :: condition
    if (condition) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok

  subroutine ok_int(label, got, expected)
    character(len=*), intent(in) :: label
    integer, intent(in) :: got, expected
    if (got == expected) then
       print '(A,A,I0)', "ok   - ", label, got
    else
       print '(A,A,I0,A,I0,A)', "FAIL - ", label, got, "  (expected ", expected, ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok_int

  subroutine check_empty()
    type(gc_value) :: a, b
    call gc_init(64)
    a = gcl_empty(no_roots)
    b = gcl_empty(no_roots)
    call ok("1a. the empty list is a list: ", gcl_is(a))
    call ok_int("1b. ...with count 0: ", gcl_count(a), 0)
    ! Identity, not just equality: () must be the same object every
    ! time, which is what makes it a singleton rather than a value.
    call ok("1c. ...and is a singleton: ", same(a, b))
    call ok_int("1d. first of empty is nil: ", first_tag(a), GCT_NIL)
    call ok("1e. rest of empty is the empty list: ", same(gcl_rest(a, no_roots), a))
  end subroutine check_empty

  subroutine check_cons_first_rest()
    type(gc_value) :: l, roots(1)
    integer :: i, bad
    call gc_init(64)
    l = gcl_empty(no_roots)
    do i = 1, 50
       roots(1) = l
       l = gcl_cons(gc_int(i), l, roots)
    end do
    call ok_int("2a. count is cached, not walked: ", gcl_count(l), 50)
    call ok_int("2b. first is the most recent cons: ", first_int(l), 50)
    ! Walk the whole chain back down; 50 cons'd in order means the
    ! values come off in reverse.
    bad = 0
    roots(1) = l
    do i = 50, 1, -1
       if (first_int(l) /= i) bad = bad + 1
       l = gcl_rest(l, roots)
       roots(1) = l
    end do
    call ok_int("2c. the whole chain walks correctly: ", bad, 0)
    call ok_int("2d. ...ending at the empty list: ", gcl_count(l), 0)
  end subroutine check_cons_first_rest

  ! Two lists sharing a tail is the case refcounting pays for on every
  ! copy and tracing gets for nothing.
  subroutine check_shared_tail()
    type(gc_value) :: tail, a, b, roots(3)
    integer :: i
    call gc_init(64)
    tail = gcl_empty(no_roots)
    do i = 1, 10
       roots(1) = tail
       tail = gcl_cons(gc_int(i), tail, roots)
    end do
    roots(1) = tail
    a = gcl_cons(gc_int(100), tail, roots)
    roots(2) = a
    b = gcl_cons(gc_int(200), tail, roots)
    roots(3) = b
    call ok_int("3a. both lists see their own head: ", first_int(a), 100)
    call ok_int("3b. ...independently: ", first_int(b), 200)
    call ok("3c. ...and share one tail object: ", &
         same(gcl_rest(a, roots), gcl_rest(b, roots)))
    call gc_collect(roots)
    call ok_int("3d. the shared tail survives collection: ", &
         first_int(gcl_rest(a, roots)), 10)
    call ok_int("3e. ...with both counts intact: ", gcl_count(b), 11)
  end subroutine check_shared_tail

  ! A long chain held only by its head: the collector has to walk cdr
  ! to cdr without recursing into the real stack, which is why the
  ! mark stack is explicit.
  subroutine check_survives_collection()
    type(gc_value) :: l, roots(1)
    integer :: base, i, n, bad
    n = 2000
    call gc_init(16)
    l = gcl_empty(no_roots)
    do i = 1, n
       roots(1) = l
       l = gcl_cons(gc_int(i), l, roots)
    end do
    base = vs_enter(1)
    call vs_set(base + 1, l)
    call gc_collect(no_roots)
    call ok_int("4a. a 2000-cell chain survives on the stack alone: ", &
         gcl_count(vs_get(base + 1)), n)
    bad = 0
    l = vs_get(base + 1)
    roots(1) = l
    do i = n, 1, -1
       if (first_int(l) /= i) bad = bad + 1
       l = gcl_rest(l, roots)
       roots(1) = l
    end do
    call ok_int("4b. ...every cell intact: ", bad, 0)
    call vs_leave(base)
    call gc_collect(no_roots)
    ! The empty-list singleton is a global root and stays live; that is
    ! the point of it, so one object remaining is correct.
    call ok_int("4c. leaving the frame collects the chain: ", gc_live_count(), 1)
  end subroutine check_survives_collection

  subroutine check_torture()
    type(gc_value) :: l, roots(1)
    integer :: i, bad
    call gc_init(8)
    gc_torture = .true.
    l = gcl_empty(no_roots)
    do i = 1, 120
       roots(1) = l
       l = gcl_cons(gc_int(i), l, roots)
    end do
    roots(1) = l
    block
       character(len=:), allocatable :: dlr_1
       call gc_check_heap(problem=dlr_1)
       call ok("5a. the heap audits clean under torture: ", dlr_1 == "")
    end block
    call ok_int("5b. ...with the chain whole: ", gcl_count(l), 120)
    bad = 0
    do i = 120, 1, -1
       if (first_int(l) /= i) bad = bad + 1
       l = gcl_rest(l, roots)
       roots(1) = l
    end do
    call ok_int("5c. ...and every value intact: ", bad, 0)
    gc_torture = .false.
  end subroutine check_torture

  ! --- helpers (flang cannot take a component off a function result) ---

  function same(a, b) result(yes)
    type(gc_value), intent(in) :: a, b
    logical :: yes
    yes = (a%tag == b%tag .and. a%ref == b%ref .and. a%ref /= 0)
  end function same

  function first_int(l) result(n)
    type(gc_value), intent(in) :: l
    type(gc_value) :: x
    integer :: n
    x = gcl_first(l)
    n = x%ival
  end function first_int

  function first_tag(l) result(t)
    type(gc_value), intent(in) :: l
    type(gc_value) :: x
    integer :: t
    x = gcl_first(l)
    t = x%tag
  end function first_tag

end program persistent_list_test

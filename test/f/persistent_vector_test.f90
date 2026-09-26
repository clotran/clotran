! Exercises the GC-backed persistent vector on its own, before anything
! in clotran uses it. The cases that matter are the ones the refcounted
! version got wrong or could not do: structural sharing surviving
! collection, and a vector that stays correct when every allocation
! collects (torture), rooted only by the value stack.
program persistent_vector_test
  use GC
  use PersistentVector
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_empty()
  call check_conj_and_nth()
  call check_growth_past_one_level()
  call check_assoc_shares()
  call check_survives_collection()
  call check_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCVECTOR CHECKS PASSED"
  else
     print *, ""
     print *, "GCVECTOR CHECKS FAILED"
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
    type(gc_value) :: v
    call gc_init(64)
    v = gcv_empty(no_roots)
    call ok("1a. an empty vector is a vector: ", gcv_is(v))
    call ok_int("1b. ...with count 0: ", gcv_count(v), 0)
    call ok_int("1c. nth out of range is nil: ", nth_tag(v, 0), GCT_NIL)
  end subroutine check_empty

  subroutine check_conj_and_nth()
    type(gc_value) :: v, roots(1)
    integer :: i, bad
    call gc_init(64)
    v = gcv_empty(no_roots)
    do i = 0, 31
       roots(1) = v
       v = gcv_conj(v, gc_int(i * 10), roots)
    end do
    call ok_int("2a. conj counts up: ", gcv_count(v), 32)
    bad = 0
    do i = 0, 31
       if (nth_int(v, i) /= i * 10) bad = bad + 1
    end do
    call ok_int("2b. every element reads back: ", bad, 0)
    call ok_int("2c. past the end is nil: ", nth_tag(v, 32), GCT_NIL)
  end subroutine check_conj_and_nth

  ! 33 elements needs a second level: the trie has to grow a new root
  ! whose first child is the old one. This is the case a 32-way trie
  ! gets wrong if the push-down is mis-shifted.
  subroutine check_growth_past_one_level()
    type(gc_value) :: v, roots(1)
    integer :: i, bad, n
    n = 200
    call gc_init(64)
    v = gcv_empty(no_roots)
    do i = 0, n - 1
       roots(1) = v
       v = gcv_conj(v, gc_int(i), roots)
    end do
    call ok_int("3a. growing past one level keeps the count: ", gcv_count(v), n)
    bad = 0
    do i = 0, n - 1
       if (nth_int(v, i) /= i) bad = bad + 1
    end do
    call ok_int("3b. ...and every element, across levels: ", bad, 0)
  end subroutine check_growth_past_one_level

  ! assoc must not disturb the original -- that is what "persistent"
  ! means, and it is the whole reason nodes are path-copied.
  subroutine check_assoc_shares()
    type(gc_value) :: a, b, roots(2)
    integer :: i
    call gc_init(64)
    a = gcv_empty(no_roots)
    do i = 0, 99
       roots(1) = a
       a = gcv_conj(a, gc_int(i), roots)
    end do
    roots(1) = a
    b = gcv_assoc(a, 50, gc_int(999), roots)
    roots(2) = b
    call ok_int("4a. assoc changes the new vector: ", nth_int(b, 50), 999)
    call ok_int("4b. ...and leaves the old one alone: ", nth_int(a, 50), 50)
    call ok_int("4c. ...with both counts intact: ", gcv_count(b), gcv_count(a))
    call gc_collect(roots)
    call ok_int("4d. shared structure survives collection: ", nth_int(a, 77), 77)
    call ok_int("4e. ...for both vectors: ", nth_int(b, 77), 77)
  end subroutine check_assoc_shares

  ! Rooted ONLY through the value stack, with nothing passed as an
  ! argument root -- the shape the evaluator will actually use.
  subroutine check_survives_collection()
    type(gc_value) :: v, roots(1)
    integer :: base, i, bad
    call gc_init(16)
    v = gcv_empty(no_roots)
    do i = 0, 149
       roots(1) = v
       v = gcv_conj(v, gc_int(i), roots)
    end do
    base = vs_enter(1)
    call vs_set(base + 1, v)
    call gc_collect(no_roots)
    bad = 0
    do i = 0, 149
       if (nth_int(vs_get(base + 1), i) /= i) bad = bad + 1
    end do
    call ok_int("5a. a vector rooted only by the value stack survives: ", bad, 0)
    call vs_leave(base)
    call gc_collect(no_roots)
    call ok_int("5b. ...and is collected once the frame is left: ", gc_live_count(), 0)
  end subroutine check_survives_collection

  ! The one refcounting could not do safely: collect at EVERY
  ! allocation while the structure is being built. PLAN.md 4a'' is a
  ! vec_node freed while still referenced; under tracing that is not
  ! expressible, and this is the check that says so.
  subroutine check_torture()
    type(gc_value) :: v, roots(1)
    integer :: i, bad
    call gc_init(8)
    gc_torture = .true.
    v = gcv_empty(no_roots)
    do i = 0, 99
       roots(1) = v
       v = gcv_conj(v, gc_int(i), roots)
    end do
    roots(1) = v
    block
       character(len=:), allocatable :: dlr_1
       call gc_check_heap(problem=dlr_1)
       call ok("6a. the heap audits clean under torture: ", dlr_1 == "")
    end block
    bad = 0
    do i = 0, 99
       if (nth_int(v, i) /= i) bad = bad + 1
    end do
    call ok_int("6b. ...with every element intact: ", bad, 0)
    call ok_int("6c. ...and the count right: ", gcv_count(v), 100)
    gc_torture = .false.
  end subroutine check_torture

  ! --- helpers (flang cannot take a component off a function result) ---

  function nth_int(v, i) result(n)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: x
    integer :: n
    x = gcv_nth(v, i)
    n = x%ival
  end function nth_int

  function nth_tag(v, i) result(t)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: x
    integer :: t
    x = gcv_nth(v, i)
    t = x%tag
  end function nth_tag

end program persistent_vector_test

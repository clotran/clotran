! Exercises the GC-backed environment on its own.
!
! The check that matters most is 5: a closure bound into its own frame
! is a CYCLE, which refcounting structurally cannot collect and which
! clotran leaks today for every named fn. Building that cycle and then
! watching it go is the correctness half of why the GC exists.
program env_test
  use GC
  use PersistentArrayMap
  use Env
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_empty()
  call check_set_and_get()
  call check_chain()
  call check_shadowing()
  call check_cycle_is_collected()
  call check_defining_ns()
  call check_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCENV CHECKS PASSED"
  else
     print *, ""
     print *, "GCENV CHECKS FAILED"
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
    type(gc_value) :: e, v
    logical :: found
    call gc_init(256)
    e = gce_new(gc_nil(), no_roots)
    call ok("1a. a fresh env is an env: ", gce_is(e))
    found = gce_find(e, gc_sym("x", no_roots), v)
    call ok("1b. nothing is bound in it: ", .not. found)
    call ok_int("1c. its outer is nil: ", outer_tag(e), GCT_NIL)
  end subroutine check_empty

  subroutine check_set_and_get()
    type(gc_value) :: e, k, v, roots(2)
    logical :: found
    call gc_init(256)
    e = gce_new(gc_nil(), no_roots)
    roots(1) = e
    k = gc_sym("x", roots)
    roots(2) = k
    call gce_set(e, k, gc_int(42), roots)
    found = gce_find(e, k, v)
    call ok("2a. a binding is found: ", found)
    call ok_int("2b. ...with its value: ", int(v%ival, kind=4), 42)
    ! Bound-to-nil must still count as FOUND -- the evaluator needs to
    ! tell "no such local" from "a local holding nil".
    call gce_set(e, k, gc_nil(), roots)
    found = gce_find(e, k, v)
    call ok("2c. bound to nil is still bound: ", found)
    call ok_int("2d. ...and reads back as nil: ", v%tag, GCT_NIL)
  end subroutine check_set_and_get

  subroutine check_chain()
    type(gc_value) :: outer, inner, k, v, roots(3)
    logical :: found
    call gc_init(256)
    outer = gce_new(gc_nil(), no_roots)
    roots(1) = outer
    k = gc_sym("y", roots)
    roots(2) = k
    call gce_set(outer, k, gc_int(7), roots)
    inner = gce_new(outer, roots)
    roots(3) = inner
    found = gce_find(inner, k, v)
    call ok("3a. an inner frame sees an outer binding: ", found)
    call ok_int("3b. ...with the outer value: ", int(v%ival, kind=4), 7)
    ! Setting in the inner frame must NOT reach back out.
    call gce_set(inner, k, gc_int(8), roots)
    found = gce_find(outer, k, v)
    call ok_int("3c. an inner binding does not leak outward: ", int(v%ival, kind=4), 7)
  end subroutine check_chain

  subroutine check_shadowing()
    type(gc_value) :: e1, e2, e3, k, v, roots(4)
    logical :: found
    call gc_init(256)
    e1 = gce_new(gc_nil(), no_roots)
    roots(1) = e1
    k = gc_sym("z", roots)
    roots(2) = k
    call gce_set(e1, k, gc_int(1), roots)
    e2 = gce_new(e1, roots)
    roots(3) = e2
    call gce_set(e2, k, gc_int(2), roots)
    e3 = gce_new(e2, roots)
    roots(4) = e3
    found = gce_find(e3, k, v)
    call ok_int("4a. the nearest frame wins: ", int(v%ival, kind=4), 2)
    found = gce_find(e1, k, v)
    call ok_int("4b. ...and the outermost is untouched: ", int(v%ival, kind=4), 1)
  end subroutine check_shadowing

  ! THE case refcounting cannot do. A named fn binds its own closure
  ! into its own frame so `recur` can find it: closure -> env -> closure.
  ! Refcounting never sees either drop to zero, so clotran leaks one of
  ! these per named fn for the life of the process. Here it is built,
  ! dropped, and collected.
  subroutine check_cycle_is_collected()
    type(gc_value) :: e, closure, k, roots(3)
    integer :: before
    call gc_init(64)

    e = gce_new(gc_nil(), no_roots)
    roots(1) = e
    k = gc_sym("recur", roots)
    roots(2) = k
    ! A closure whose captured env is e ...
    closure = gc_obj(OBJ_CLOSURE, [gc_nil(), gc_nil(), e, gc_nil()], roots)
    roots(3) = closure
    ! ... and e binds that same closure. The cycle is now closed.
    call gce_set(e, k, closure, roots)

    call gc_collect(roots)
    before = gc_live_count()
    call ok("5a. the cycle is intact while rooted: ", &
         gc_kind(gce_get(e, k)) == OBJ_CLOSURE)
    call ok("5b. ...and it really is a cycle: ", &
         same(gc_slot(gce_get(e, k), 3), e))
    call ok("5c. ...holding live objects: ", before > 0)

    ! Drop every reference. Refcounting would keep all of this forever.
    call gc_collect(no_roots)
    call ok_int("5d. an unreachable cycle IS collected: ", gc_live_count(), 0)
  end subroutine check_cycle_is_collected

  subroutine check_defining_ns()
    type(gc_value) :: outer, inner, roots(2)
    call gc_init(256)
    outer = gce_new(gc_nil(), no_roots)
    roots(1) = outer
    call gce_set_ns(outer, 3)
    inner = gce_new(outer, roots)
    roots(2) = inner
    call ok_int("6a. a frame reports its own defining ns: ", gce_defining_ns(outer), 3)
    call ok_int("6b. ...and an inner frame inherits it: ", gce_defining_ns(inner), 3)
    call gce_set_ns(inner, 9)
    call ok_int("6c. ...until it has one of its own: ", gce_defining_ns(inner), 9)
    call ok_int("6d. ...which does not disturb the outer: ", gce_defining_ns(outer), 3)
  end subroutine check_defining_ns

  subroutine check_torture()
    type(gc_value) :: e, k, v, roots(2)
    character(len=16) :: buf
    integer :: i, bad
    logical :: found
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call gc_init(8)
    gc_torture = .true.
    e = gce_new(gc_nil(), no_roots)
    roots(1) = e
    do i = 1, 40
       write(buf, '(A,I0)') "v", i
       k = gc_sym(trim(buf), roots)
       roots(2) = k
       call gce_set(e, k, gc_int(i), roots)
    end do
    roots(2) = gc_nil()
    block
       call gc_check_heap(problem=dlt_1)
       call ok("7a. the heap audits clean under torture: ", dlt_1 == "")
    end block
    bad = 0
    do i = 1, 40
       write(buf, '(A,I0)') "v", i
       found = gce_find(e, gc_sym(trim(buf), roots), v)
       if (.not. found) then
          bad = bad + 1
       else if (v%ival /= i) then
          bad = bad + 1
       end if
    end do
    call ok_int("7b. ...with every binding intact: ", bad, 0)
    gc_torture = .false.
  end subroutine check_torture

  ! --- helpers (flang cannot take a component off a function result) ---

  function same(a, b) result(yes)
    type(gc_value), intent(in) :: a, b
    logical :: yes
    yes = (a%tag == b%tag .and. a%ref == b%ref .and. a%ref /= 0)
  end function same

  function outer_tag(e) result(t)
    type(gc_value), intent(in) :: e
    type(gc_value) :: x
    integer :: t
    x = gce_outer(e)
    t = x%tag
  end function outer_tag

end program env_test

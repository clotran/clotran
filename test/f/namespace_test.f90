! Validates Namespace: find-or-create is idempotent by name, intern/
! resolve round-trips, the clojure.core auto-refer fallback, and that
! resolve correctly reports which namespace actually owns a binding
! (the thing syntax-quote qualification depends on).
program namespace_test
  use values
  use Namespace
  implicit none

  logical :: all_ok
  type(ns_ref) :: core, user
  type(cons_value) :: v
  logical :: found
  character(len=:), allocatable :: owner

  all_ok = .true.

  core = ns_find_or_create("clojure.core")
  call ns_intern(core, "+", mkint(1))

  call expect_true("1. find-or-create is idempotent: ", &
       same_ns(ns_find_or_create("clojure.core"), core), all_ok)

  user = ns_find_or_create("user")
  call ns_intern(user, "x", mkint(42))
  found = ns_get_own(user, "x", v)
  call expect_true("2. intern then get-own finds it: ", found, all_ok)
  call expect_eq("2b. ...with the right value: ", as_int(v), 42, all_ok)

  found = ns_get_own(user, "+", v)
  call expect_true("3. get-own does NOT fall back to clojure.core: ", .not. found, all_ok)

  found = ns_resolve(user, "+", v, owner)
  call expect_true("4. resolve DOES fall back to clojure.core: ", found, all_ok)
  call expect_true("4b. ...and reports clojure.core as the owner: ", owner == "clojure.core", all_ok)

  found = ns_resolve(user, "x", v, owner)
  call expect_true("5. resolve finds user's own binding first: ", found, all_ok)
  call expect_true("5b. ...reports user, not clojure.core, as owner: ", owner == "user", all_ok)

  found = ns_resolve(user, "nope", v, owner)
  call expect_true("6. resolve fails for a truly unbound symbol: ", .not. found, all_ok)

  call ns_set_current(user)
  call expect_true("7. current namespace round-trips: ", ns_name_of(ns_current()) == "user", all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL NAMESPACE CHECKS PASSED"
  else
     print *, ""
     print *, "NAMESPACE CHECKS FAILED"
     stop 1
  end if

contains

  function same_ns(a, b) result(same)
    type(ns_ref), intent(in) :: a, b
    logical :: same
    same = (ns_name_of(a) == ns_name_of(b))
  end function same_ns

  function mkint(i) result(v)
    integer, intent(in) :: i
    type(cons_value) :: v
    v%tag = TAG_INT
    v%int_val = i
  end function mkint

  function as_int(v) result(i)
    type(cons_value), intent(in) :: v
    integer :: i
    i = v%int_val
  end function as_int

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
    flush(6)
  end subroutine expect_eq

  subroutine expect_true(label, actual, ok)
    character(len=*), intent(in) :: label
    logical, intent(in) :: actual
    logical, intent(inout) :: ok
    if (actual) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       ok = .false.
    end if
    flush(6)
  end subroutine expect_true

end program namespace_test

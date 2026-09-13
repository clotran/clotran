! Validates Env: set/get/find correctness, outer-chain lookup, mutation
! visible through a shared reference (unlike everything persistent so
! far), and that every env allocated is eventually freed.
program env_test
  use values
  use Env
  implicit none

  logical :: all_ok

  all_ok = .true.

  block
    type(env_ref) :: e0
    e0 = env_new()
    call env_set(e0, mksym("x"), mkint(1))
  call expect_eq("1. set then get: ", as_int(env_get(e0, mksym("x"))), 1, all_ok)

  block
    type(cons_value) :: v
    logical :: found
    found = env_find(e0, mksym("nope"), v)
    call expect_true("2. unbound symbol is not found: ", .not. found, all_ok)
  end block

  ! 3. Outer chain: a child env sees its parent's bindings, and can
  !    shadow them without touching the parent.
  block
    type(env_ref) :: child
    child = env_new(e0)
    call expect_eq("3a. child sees parent's binding: ", as_int(env_get(child, mksym("x"))), 1, all_ok)
    call env_set(child, mksym("x"), mkint(99))
    call expect_eq("3b. shadowing in the child doesn't touch the parent: ", &
         as_int(env_get(e0, mksym("x"))), 1, all_ok)
    call expect_eq("3c. ...and the child sees its own value: ", as_int(env_get(child, mksym("x"))), 99, all_ok)
  end block

  ! 4. Mutation is visible through every reference to the same env --
  !    the actual point of Env not being persistent like everything else.
  block
    type(env_ref) :: alias
    alias = e0
    call env_set(alias, mksym("y"), mkint(7))
    call expect_eq("4. setting through alias is visible through e0: ", as_int(env_get(e0, mksym("y"))), 7, all_ok)
  end block

    ! 5. A symbol bound to nil is found, distinct from being unbound.
    block
      type(cons_value) :: v
      logical :: found
      call env_set(e0, mksym("z"), nil_val())
      found = env_find(e0, mksym("z"), v)
      call expect_true("5. a nil-bound symbol is still found: ", found, all_ok)
    end block
  end block ! e0 (and everything built on it above) goes out of scope here

  ! 6. Everything freed once nothing references it.
  call expect_eq("6. dropping every reference frees all envs: ", &
       env_total_freed, env_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL ENV CHECKS PASSED (", env_total_allocated, " envs)"
  else
     print *, ""
     print *, "ENV CHECKS FAILED"
     stop 1
  end if

contains

  function mksym(s) result(v)
    character(len=*), intent(in) :: s
    type(cons_value) :: v
    v%tag = TAG_SYMBOL
    v%str_val = s
  end function mksym

  function mkint(i) result(v)
    integer, intent(in) :: i
    type(cons_value) :: v
    v%tag = TAG_INT
    v%int_val = i
  end function mkint

  function nil_val() result(v)
    type(cons_value) :: v
  end function nil_val

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

end program env_test

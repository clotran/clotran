! Validates Atom: construction, deref, mutation visible through every
! shared reference (like Env, unlike everything persistent), and that
! every atom allocated is eventually freed.
program atom_test
  use values
  use Atom
  implicit none

  logical :: all_ok

  all_ok = .true.

  block
    type(cons_value) :: a

    a = atom_new(mkint(2))
    call expect_true("1. atom_new produces an atom: ", atom_p(a), all_ok)
    call expect_true("2. an ordinary value is not an atom: ", .not. atom_p(mkint(2)), all_ok)
    call expect_eq("3. deref reads the initial value: ", as_int(atom_deref(a)), 2, all_ok)

    call atom_reset(a, mkint(9))
    call expect_eq("4. reset changes what deref sees: ", as_int(atom_deref(a)), 9, all_ok)

    ! 5. Mutation is visible through every reference to the same atom --
    ! the actual point of Atom not being persistent like everything else.
    block
      type(cons_value) :: alias
      alias = a
      call atom_reset(alias, mkint(42))
      call expect_eq("5. resetting through an alias is visible through a: ", as_int(atom_deref(a)), 42, all_ok)
    end block
  end block ! a (and its alias) go out of scope here

  call expect_eq("6. dropping every reference frees all atoms: ", &
       atom_node_total_freed, atom_node_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL ATOM CHECKS PASSED (", atom_node_total_allocated, " atoms)"
  else
     print *, ""
     print *, "ATOM CHECKS FAILED"
     stop 1
  end if

contains

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

end program atom_test

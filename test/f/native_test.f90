! Validates the plan for holding arbitrary Fortran interop values (any
! scalar kind, any derived-type struct) inside cons_value: a
! polymorphic POINTER component, not type(c_ptr) and not an
! allocatable component. Checked on both compilers before this
! becomes real cons_value/Var work -- see NOTES.md.
!
! Pointer, not allocatable: intrinsic structure assignment on a
! pointer component does pointer association (copy the reference),
! never invokes assignment(=)/FINAL on the target -- sidesteps the
! "class(*) allocatable doesn't dispatch defined assignment" gotcha
! found earlier, and matches Java reference semantics (assignment
! aliases, never deep-copies) exactly.
!
! Checks 5+ go further: arbitrary-depth nesting in both directions --
! a clotran cons_value holding a native struct as a leaf, AND a native
! struct holding a real cons_value (our own string, our own list) as
! ONE OF ITS OWN FIELDS, plus a native struct built from another
! native struct (native-in-native). Values.f90 already flags (see
! closure_t_assign's own comment) that default struct assignment does
! NOT reliably cascade into an embedded type's own defined
! assignment(=) on this project's compilers -- checks 6/7 exist
! specifically to confirm whether that gotcha also bites a brand new
! host type that embeds a cons_value with NO assignment(=) of its own,
! using cons_cell_total_allocated/_freed (the same "everything
! allocated is freed exactly once" check persistent_list_test.f90
! uses) as the tell.
module native_holder
  use values
  use PersistentList, only: list_of, list_count
  implicit none

  type :: box
     class(*), pointer :: payload => null()
  end type box

  ! A box's payload is scalar (rank 0), so a "children" container needs
  ! its own wrapper type rather than pointing directly at a rank-1
  ! array -- mirrors a map/vector's real shape (a container object
  ! holding an array), not a bare array reference.
  type :: kids
     type(box), allocatable :: items(:)
  end type kids

  ! A stand-in "struct" -- an arbitrary Fortran derived type a real
  ! interop library might define, unrelated to cons_value itself.
  type :: molecule
     character(len=8) :: name
     real(8) :: energy
     integer :: natoms
  end type molecule

  ! A native struct built from OTHER native objects: points at another
  ! molecule via the same polymorphic-pointer mechanism as box, plus a
  ! real clotran string as one of its own fields (native-in-native AND
  ! native-holds-clotran, at once). Deliberately no assignment(=).
  type :: assembly
     class(*), pointer :: part => null()
     type(cons_value) :: label
  end type assembly

  ! Deliberately NO assignment(=) -- confirmed (check 6a) to alias
  ! without bumping the embedded cons_value's refcount, exactly the
  ! "default assignment does NOT bump the embedded refcount" hazard
  ! rc_test.f90's own holder_naive demonstrates for rc_module. Used
  ! ONLY for that demonstration below, via a leaked pointer copy that's
  ! never touched again -- same safe pattern rc_test.f90 uses for h2.
  type :: has_cons_list_naive
     type(cons_value) :: items
  end type has_cons_list_naive

  ! The fix: an explicit assignment(=) that forwards to cons_value's
  ! own defined assignment field-by-field, same pattern as
  ! closure_t_assign. Required, not optional, for ANY new host type
  ! that embeds a cons_value (or any other clotran ref type) --
  ! checks 6a/6b below prove Fortran's default assignment does not
  ! reliably do this on its own.
  type :: has_cons_string
     integer :: id
     type(cons_value) :: label ! a real clotran string (TAG_STRING)
  end type has_cons_string

  type :: has_cons_list
     type(cons_value) :: items ! a real clotran list (TAG_LIST), refcounted internals
  end type has_cons_list

  interface assignment(=)
     module procedure has_cons_string_assign
     module procedure has_cons_list_assign
  end interface assignment(=)

contains

  subroutine has_cons_string_assign(lhs, rhs)
    type(has_cons_string), intent(inout) :: lhs
    type(has_cons_string), intent(in) :: rhs
    lhs%id = rhs%id
    lhs%label = rhs%label
  end subroutine has_cons_string_assign

  subroutine has_cons_list_assign(lhs, rhs)
    type(has_cons_list), intent(inout) :: lhs
    type(has_cons_list), intent(in) :: rhs
    lhs%items = rhs%items
  end subroutine has_cons_list_assign

  subroutine expect_true(label, cond, ok)
    character(len=*), intent(in) :: label
    logical, intent(in) :: cond
    logical, intent(inout) :: ok
    if (cond) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       ok = .false.
    end if
    flush(6) ! so a later crash doesn't hide every check up to that point
  end subroutine expect_true

  ! Builds a 3-element clotran list value (bumps cons_cell_total_allocated
  ! by exactly 3), for checks 6/7.
  function make_test_list() result(v)
    type(cons_value) :: v
    type(cons_value) :: items(3)
    items(1)%tag = TAG_INT
    items(1)%int_val = 10
    items(2)%tag = TAG_INT
    items(2)%int_val = 20
    items(3)%tag = TAG_INT
    items(3)%int_val = 30
    v%tag = TAG_LIST
    allocate(v%list_val)
    v%list_val = list_of(items)
  end function make_test_list

end module native_holder

program native_test
  use native_holder
  use values
  use PersistentList, only: list_of, list_count
  implicit none

  logical :: all_ok
  type(box) :: b1, b2
  real(4), pointer :: r4
  integer(8), pointer :: i8
  type(molecule), pointer :: mol

  all_ok = .true.

  ! 1. Scalars of odd kinds round-trip exactly through the polymorphic
  ! pointer, retrieved via select type.
  allocate(r4)
  r4 = 1.5_4
  b1%payload => r4
  block
    logical :: got
    got = .false.
    select type (p => b1%payload)
    type is (real(4))
       got = (p == 1.5_4)
    end select
    call expect_true("1a. real(4) scalar round-trips via select type", got, all_ok)
  end block

  allocate(i8)
  i8 = 123456789012_8
  b1%payload => i8
  block
    logical :: got
    got = .false.
    select type (p => b1%payload)
    type is (integer(8))
       got = (p == 123456789012_8)
    end select
    call expect_true("1b. integer(8) scalar round-trips via select type", got, all_ok)
  end block

  ! 2. A derived-type struct round-trips, and survives being copied
  ! box-to-box (intrinsic structure assignment) without corruption.
  allocate(mol)
  mol%name = "water"
  mol%energy = -76.4_8
  mol%natoms = 3
  b1%payload => mol

  b2 = b1
  block
    logical :: got
    got = .false.
    select type (p => b2%payload)
    type is (molecule)
       got = (trim(p%name) == "water" .and. p%energy == -76.4_8 .and. p%natoms == 3)
    end select
    call expect_true("2a. struct survives box-to-box assignment", got, all_ok)
  end block

  ! 3. Real identity, not an accidental copy: mutating through the
  ! ORIGINAL pointer is visible through the b2 alias -- proves b2
  ! points at the SAME molecule, matching Java reference semantics.
  mol%energy = -99.0_8
  block
    logical :: got
    got = .false.
    select type (p => b2%payload)
    type is (molecule)
       got = (p%energy == -99.0_8)
    end select
    call expect_true("3a. mutation through one alias is visible through another", got, all_ok)
  end block

  ! 4. Survives an array of boxes and a function-argument boundary.
  block
    type(box) :: arr(3)
    arr(2) = b2
    call check_via_array(arr, all_ok)
  end block

  ! 5. A native struct with a real clotran string as ONE OF ITS OWN
  ! FIELDS (not a pointer to one -- an ordinary, embedded cons_value
  ! component), no assignment(=) of its own, copied around directly.
  block
    type(has_cons_string) :: h1, h2
    logical :: got
    h1%id = 7
    h1%label%tag = TAG_STRING
    call set_str(h1%label, "hello")
    h2 = h1
    call set_str(h1%label, "clobbered") ! h2 must NOT see this -- str_val copies by value
    got = (h2%id == 7 .and. str_is(h2%label, "hello"))
    call expect_true("5a. struct-embedded cons_value string copies correctly, by value", got, all_ok)
  end block

  ! 6a. The embedded cons_value holds a LIST -- refcounted internals,
  ! not a plain allocatable string -- to actually exercise whether
  ! default assignment cascades into cons_value's OWN defined
  ! assignment(=). It does NOT: confirmed by an earlier version of
  ! this test that crashed ("DEALLOCATE of a pointer that is not the
  ! whole content of a pointer ALLOCATE") the moment a naively-copied
  ! has_cons_list_naive went out of scope -- both copies thought they
  ! owned the only reference, so both tried to free the same cells.
  ! Demonstrated safely here the same way rc_test.f90's holder_naive
  ! does: l2 is a leaked pointer, never touched again after the check,
  ! so its dangling alias is never dereferenced.
  block
    type(has_cons_list_naive) :: l1
    type(has_cons_list_naive), pointer :: l2
    l1%items = make_test_list()
    allocate(l2)
    l2 = l1
    call expect_true("6a. default assignment does NOT bump the embedded cons cell's refcount", &
         l1%items%list_val%ptr%refcount == 1, all_ok)
  end block

  ! 6b. has_cons_list's own assignment(=) (forwarding to cons_value's,
  ! see has_cons_list_assign) does it correctly -- copied through a
  ! struct-to-struct assign, an array, and a function arg, then
  ! everything drops out of scope -- cons_cell_total_freed must end up
  ! equal to cons_cell_total_allocated (checked at the very end, after
  ! this block and its copies are all gone).
  block
    type(has_cons_list) :: l1, l2
    type(has_cons_list) :: arr(2)
    logical :: got
    l1%items = make_test_list()
    l2 = l1
    got = (l1%items%list_val%ptr%refcount == 2)
    call expect_true("6b. has_cons_list's own assignment(=) DOES bump the refcount", got, all_ok)
    arr(1) = l2
    got = (list_count(l2%items%list_val) == 3 .and. list_count(arr(1)%items%list_val) == 3)
    call expect_true("6c. ...and struct-embedded cons_value list still reads correctly", got, all_ok)
    call check_list_via_arg(arr(1), all_ok)
  end block

  ! 7. The full nested-map-literal shape: a tree of boxes mixing an
  ! int(8) leaf, a real(4) leaf, a clotran string leaf, a plain
  ! struct, and a native-in-native "assembly" (points at another
  ! native struct AND carries a clotran string of its own) -- then
  ! pulled back out through several levels of select-type traversal.
  block
    type(box) :: root, c_branch, g_leaf
    type(box) :: r4_leaf, i8_leaf, e_leaf, f_leaf
    type(assembly), pointer :: asm
    logical :: got

    allocate(r4)
    r4 = 2.5_4
    r4_leaf%payload => r4

    allocate(i8)
    i8 = 99_8
    i8_leaf%payload => i8

    block
      type(cons_value), pointer :: e_str
      allocate(e_str)
      e_str%tag = TAG_STRING
      call set_str(e_str, "leaf-e")
      e_leaf%payload => e_str
    end block

    allocate(mol)
    mol%name = "co2"
    mol%energy = -188.0_8
    mol%natoms = 3
    f_leaf%payload => mol

    allocate(asm)
    asm%part => mol ! native-in-native: assembly points at the SAME molecule
    asm%label%tag = TAG_STRING
    call set_str(asm%label, "assembly-g")
    g_leaf%payload => asm

    ! :c { :d r4_leaf :e e_leaf }, boxed as its own native container.
    block
      type(kids), pointer :: c_kids
      allocate(c_kids)
      allocate(c_kids%items(2))
      c_kids%items(1) = r4_leaf
      c_kids%items(2) = e_leaf
      c_branch%payload => c_kids
    end block

    ! root { :b i8_leaf :c c_branch :f f_leaf :g g_leaf }
    block
      type(kids), pointer :: root_kids
      allocate(root_kids)
      allocate(root_kids%items(4))
      root_kids%items(1) = i8_leaf
      root_kids%items(2) = c_branch
      root_kids%items(3) = f_leaf
      root_kids%items(4) = g_leaf
      root%payload => root_kids
    end block

    got = .false.
    select type (rk => root%payload)
    type is (kids)
       block
         logical :: b_ok, c_ok, f_ok, g_ok
         b_ok = .false.; c_ok = .false.; f_ok = .false.; g_ok = .false.

         select type (p => rk%items(1)%payload) ! :b
         type is (integer(8))
            b_ok = (p == 99_8)
         end select

         select type (cb => rk%items(2)%payload) ! :c
         type is (kids)
            block
              logical :: d_ok, e_ok
              d_ok = .false.; e_ok = .false.
              select type (p => cb%items(1)%payload) ! :d
              type is (real(4))
                 d_ok = (p == 2.5_4)
              end select
              select type (p => cb%items(2)%payload) ! :e
              type is (cons_value)
                 e_ok = (p%tag == TAG_STRING .and. str_is(p, "leaf-e"))
              end select
              c_ok = d_ok .and. e_ok
            end block
         end select

         select type (p => rk%items(3)%payload) ! :f
         type is (molecule)
            f_ok = (trim(p%name) == "co2" .and. p%natoms == 3)
         end select

         select type (p => rk%items(4)%payload) ! :g
         type is (assembly)
            block
              logical :: part_ok
              part_ok = .false.
              select type (q => p%part)
              type is (molecule)
                 part_ok = (trim(q%name) == "co2")
              end select
              g_ok = part_ok .and. p%label%tag == TAG_STRING .and. str_is(p%label, "assembly-g")
            end block
         end select

         got = b_ok .and. c_ok .and. f_ok .and. g_ok
       end block
    end select
    call expect_true("7a. deep nested box tree (mixed clotran + native, 3 levels) round-trips", got, all_ok)
  end block

  if (all_ok) then
     print *, ""
     print *, "ALL NATIVE CHECKS PASSED"
  else
     print *, ""
     print *, "NATIVE CHECKS FAILED"
     stop 1
  end if

  ! Everything from check 6 (l1/l2/arr, and the copy check_list_via_arg
  ! took) is out of scope by now -- confirms default struct assignment
  ! really did cascade cons_value's own refcount-safe assignment(=)
  ! for has_cons_list (no leak, no double-free), not just that reads
  ! looked right while things were still in scope.
  call expect_true("6d. every cons cell from check 6 freed exactly once", &
       cons_cell_total_freed == cons_cell_total_allocated, all_ok)
  if (.not. all_ok) stop 1

contains

  subroutine check_via_array(arr, ok)
    type(box), intent(in) :: arr(3)
    logical, intent(inout) :: ok
    logical :: got
    got = .false.
    select type (p => arr(2)%payload)
    type is (molecule)
       got = (p%natoms == 3 .and. p%energy == -99.0_8)
    end select
    call expect_true("4a. struct survives array-of-boxes + function-arg passing", got, ok)
  end subroutine check_via_array

  subroutine check_list_via_arg(h, ok)
    type(has_cons_list), intent(in) :: h
    logical, intent(inout) :: ok
    call expect_true("6c'. ...and still correct across a function-arg boundary", &
         list_count(h%items%list_val) == 3, ok)
  end subroutine check_list_via_arg

end program native_test

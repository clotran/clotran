! Reference-counted handle for acyclic graphs (trie nodes). assignment(=)
! bumps the refcount; FINAL drops it and frees at zero. Payload is a
! plain integer here on purpose -- see rc_test.f90.
module rc_module
  implicit none
  private

  type :: rc_box
     integer :: refcount = 0
     integer :: payload = 0
  end type rc_box

  type, public :: rc
     type(rc_box), pointer :: box => null()
   contains
     final :: rc_finalize
  end type rc

  ! For rc_test.f90 to confirm every box is eventually freed.
  integer, public :: rc_total_allocated = 0
  integer, public :: rc_total_freed = 0

  public :: assignment(=)
  public :: rc_new, rc_payload, rc_refcount, rc_is_null, rc_release

  interface assignment(=)
     module procedure rc_assign
  end interface assignment(=)

contains

  function rc_new(payload) result(h)
    integer, intent(in) :: payload
    type(rc) :: h
    allocate(h%box)
    h%box%refcount = 1
    h%box%payload = payload
    rc_total_allocated = rc_total_allocated + 1
  end function rc_new

  function rc_is_null(h) result(bool)
    type(rc), intent(in) :: h
    logical :: bool
    bool = .not. associated(h%box)
  end function rc_is_null

  function rc_refcount(h) result(n)
    type(rc), intent(in) :: h
    integer :: n
    if (associated(h%box)) then
       n = h%box%refcount
    else
       n = 0
    end if
  end function rc_refcount

  function rc_payload(h) result(i)
    type(rc), intent(in) :: h
    integer :: i
    i = h%box%payload
  end function rc_payload

  ! Decrements and frees at zero; public so a handle can be released
  ! deliberately, not just via FINAL at scope exit.
  recursive subroutine rc_release(h)
    type(rc), intent(inout) :: h
    if (.not. associated(h%box)) return
    h%box%refcount = h%box%refcount - 1
    if (h%box%refcount <= 0) then
       deallocate(h%box)
       rc_total_freed = rc_total_freed + 1
    end if
    h%box => null()
  end subroutine rc_release

  ! impure elemental: covers array assignment too (see rc_test.f90).
  impure elemental subroutine rc_assign(lhs, rhs)
    type(rc), intent(inout) :: lhs
    type(rc), intent(in) :: rhs
    if (associated(lhs%box, rhs%box)) return ! self-assignment guard
    call rc_release(lhs)
    lhs%box => rhs%box
    if (associated(lhs%box)) lhs%box%refcount = lhs%box%refcount + 1
  end subroutine rc_assign

  ! impure elemental so it covers arrays, not just scalars (see rc_test.f90).
  impure elemental subroutine rc_finalize(h)
    type(rc), intent(inout) :: h
    call rc_release(h)
  end subroutine rc_finalize

end module rc_module

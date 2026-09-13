! Atom: mirrors clojure.lang.Atom -- one genuinely mutable slot, shared
! by reference (like Env, unlike every persistent structure elsewhere).
module Atom
  use values
  implicit none
  private

  public :: atom_new, atom_p, atom_deref, atom_reset

contains

  function atom_new(v) result(val)
    type(cons_value), intent(in) :: v
    type(cons_value) :: val
    val%tag = TAG_ATOM
    allocate(val%atom_val)
    allocate(val%atom_val%ptr)
    val%atom_val%ptr%refcount = 1
    atom_node_total_allocated = atom_node_total_allocated + 1
    val%atom_val%ptr%val = v
  end function atom_new

  function atom_p(v) result(is_atom)
    type(cons_value), intent(in) :: v
    logical :: is_atom
    is_atom = (v%tag == TAG_ATOM)
  end function atom_p

  function atom_deref(a) result(v)
    type(cons_value), intent(in) :: a
    type(cons_value) :: v
    if (allocated(a%atom_val)) then
       if (associated(a%atom_val%ptr)) v = a%atom_val%ptr%val
    end if
  end function atom_deref

  ! Mutates in place -- every cons_value sharing this atom_ref sees it.
  subroutine atom_reset(a, v)
    type(cons_value), intent(in) :: a
    type(cons_value), intent(in) :: v
    if (allocated(a%atom_val)) then
       if (associated(a%atom_val%ptr)) a%atom_val%ptr%val = v
    end if
  end subroutine atom_reset

end module Atom

! Atom: mirrors clojure.lang.Atom -- one genuinely mutable slot, shared
! by reference (like Env, unlike every persistent structure elsewhere).
module Atom
  use values
  implicit none
  private

  public :: atom_new, atom_p, atom_deref, atom_reset, var_dyn_push, var_dyn_pop, var_set

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

  ! The current value: the top of the Var dynamic-binding stack if
  ! `binding` has pushed one, otherwise the root -- same function
  ! either way, since a plain atom's dyn_stack is simply never
  ! populated. Real Clojure's Var.get() does exactly this dispatch.
  function atom_deref(a) result(v)
    type(cons_value), intent(in) :: a
    type(cons_value) :: v
    integer :: n
    if (allocated(a%atom_val)) then
       if (associated(a%atom_val%ptr)) then
          if (allocated(a%atom_val%ptr%dyn_stack)) then
             n = size(a%atom_val%ptr%dyn_stack)
             if (n > 0) then
                v = a%atom_val%ptr%dyn_stack(n)
                return
             end if
          end if
          v = a%atom_val%ptr%val
       end if
    end if
  end function atom_deref

  ! Mutates in place -- every cons_value sharing this atom_ref sees it.
  ! Always the ROOT, never the dyn_stack top -- reset!/def! redefine
  ! the Var itself, they're not `binding`'s job (see var_dyn_push).
  subroutine atom_reset(a, v)
    type(cons_value), intent(in) :: a
    type(cons_value), intent(in) :: v
    if (allocated(a%atom_val)) then
       if (associated(a%atom_val%ptr)) a%atom_val%ptr%val = v
    end if
  end subroutine atom_reset

  ! push-thread-bindings' job, per Var: push a new dynamic value.
  ! Grows the stack by one -- explicit allocate + pre-sized copy +
  ! move_alloc, not auto-reallocating array assignment (crashes on
  ! both compilers -- see NOTES.md's Fortran gotchas catalog).
  subroutine var_dyn_push(a, v)
    type(cons_value), intent(in) :: a
    type(cons_value), intent(in) :: v
    type(cons_value), allocatable :: grown(:)
    integer :: n
    if (.not. allocated(a%atom_val)) return
    if (.not. associated(a%atom_val%ptr)) return
    if (.not. allocated(a%atom_val%ptr%dyn_stack)) then
       allocate(a%atom_val%ptr%dyn_stack(1))
       a%atom_val%ptr%dyn_stack(1) = v
       return
    end if
    n = size(a%atom_val%ptr%dyn_stack)
    allocate(grown(n + 1))
    grown(1:n) = a%atom_val%ptr%dyn_stack(1:n)
    grown(n + 1) = v
    call move_alloc(grown, a%atom_val%ptr%dyn_stack)
  end subroutine var_dyn_push

  ! (set! *var* v): writes the INNERMOST dynamic binding if one is in
  ! effect, falling back to the root -- the opposite of atom_reset,
  ! which always writes the root. Real Clojure refuses set! on a Var
  ! with no thread binding; clotran has no threads, so the root is the
  ! honest place for it to land rather than an error.
  subroutine var_set(a, v)
    type(cons_value), intent(in) :: a
    type(cons_value), intent(in) :: v
    integer :: n
    if (.not. allocated(a%atom_val)) return
    if (.not. associated(a%atom_val%ptr)) return
    if (allocated(a%atom_val%ptr%dyn_stack)) then
       n = size(a%atom_val%ptr%dyn_stack)
       if (n > 0) then
          a%atom_val%ptr%dyn_stack(n) = v
          return
       end if
    end if
    a%atom_val%ptr%val = v
  end subroutine var_set

  ! pop-thread-bindings' job, per Var: undo the most recent push.
  subroutine var_dyn_pop(a)
    type(cons_value), intent(in) :: a
    type(cons_value), allocatable :: shrunk(:)
    integer :: n
    if (.not. allocated(a%atom_val)) return
    if (.not. associated(a%atom_val%ptr)) return
    if (.not. allocated(a%atom_val%ptr%dyn_stack)) return
    n = size(a%atom_val%ptr%dyn_stack)
    if (n <= 1) then
       deallocate(a%atom_val%ptr%dyn_stack)
       return
    end if
    allocate(shrunk(n - 1))
    shrunk(:) = a%atom_val%ptr%dyn_stack(1:n - 1)
    call move_alloc(shrunk, a%atom_val%ptr%dyn_stack)
  end subroutine var_dyn_pop

end module Atom

! PersistentVector: the 32-way branching trie's operations (nth/conj).
! Types (vec_t, vec_node, node_ref) live in Values.f90 -- see its header
! for why. The generic, type-dispatching nth/conj/count/etc. that
! anything actually calls live in RT.f90.
module PersistentVector
  use values
  implicit none
  private

  public :: vector_empty, vector_count, vector_nth, vector_conj, vector_assoc
  public :: has_vector, val_vec_count, val_vec_nth, set_vector, val_vec_conj, val_vec_assoc

contains

  function vector_empty() result(v)
    type(vec_t) :: v
  end function vector_empty

  function vector_count(v) result(n)
    type(vec_t), intent(in) :: v
    integer :: n
    n = v%count
  end function vector_count

  recursive function node_nth(node, shift, i) result(val)
    type(node_ref), intent(in) :: node
    integer, intent(in) :: shift, i
    type(cons_value) :: val
    integer :: idx
    if (shift == 0) then
       val = node%ptr%items(iand(i, MASK) + 1)
    else
       idx = iand(ishft(i, -shift), MASK) + 1
       val = node_nth(node%ptr%children(idx), shift - BITS, i)
    end if
  end function node_nth

  function vector_nth(v, i) result(val)
    type(vec_t), intent(in) :: v
    integer, intent(in) :: i ! 0-based
    type(cons_value) :: val
    val = node_nth(v%root, v%shift, i)
  end function vector_nth

  ! Path-copies from node_in down to index i, sharing every untouched
  ! child by reference. node_in may be a not-yet-associated ref (creates a
  ! fresh subtree, used when growing).
  recursive function node_assoc(node_in, shift, i, x) result(new_ref)
    type(node_ref), intent(in) :: node_in
    integer, intent(in) :: shift, i
    type(cons_value), intent(in) :: x
    type(node_ref) :: new_ref
    type(vec_node), pointer :: new_node
    type(node_ref) :: empty_ref
    integer :: idx, n_old

    allocate(new_node)
    new_node%refcount = 1
    vec_node_total_allocated = vec_node_total_allocated + 1

    if (shift == 0) then
       idx = iand(i, MASK) + 1
       if (associated(node_in%ptr)) then
          n_old = size(node_in%ptr%items)
       else
          n_old = 0
       end if
       allocate(new_node%items(max(n_old, idx)))
       if (n_old > 0) new_node%items(1:n_old) = node_in%ptr%items(1:n_old)
       new_node%items(idx) = x
    else
       idx = iand(ishft(i, -shift), MASK) + 1
       if (associated(node_in%ptr)) then
          n_old = size(node_in%ptr%children)
       else
          n_old = 0
       end if
       allocate(new_node%children(max(n_old, idx)))
       if (n_old > 0) new_node%children(1:n_old) = node_in%ptr%children(1:n_old)
       if (idx > n_old) then
          new_node%children(idx) = node_assoc(empty_ref, shift - BITS, i, x)
       else
          new_node%children(idx) = node_assoc(node_in%ptr%children(idx), shift - BITS, i, x)
       end if
    end if

    new_ref%ptr => new_node
  end function node_assoc

  ! Appends x, growing the tree by one level once the current one fills up.
  function vector_conj(v, x) result(new_v)
    type(vec_t), intent(in) :: v
    type(cons_value), intent(in) :: x
    type(vec_t) :: new_v
    integer :: capacity
    type(vec_node), pointer :: new_root
    type(node_ref) :: empty_ref

    new_v%count = v%count + 1

    if (v%count == 0) then
       new_v%shift = 0
       new_v%root = node_assoc(empty_ref, 0, 0, x)
       return
    end if

    capacity = ishft(1, v%shift + BITS)
    if (v%count < capacity) then
       new_v%shift = v%shift
       new_v%root = node_assoc(v%root, v%shift, v%count, x)
    else
       ! Old root becomes child 1 of a fresh, one-level-taller root.
       new_v%shift = v%shift + BITS
       allocate(new_root)
       new_root%refcount = 1
       vec_node_total_allocated = vec_node_total_allocated + 1
       allocate(new_root%children(2))
       new_root%children(1) = v%root
       new_root%children(2) = node_assoc(empty_ref, v%shift, v%count, x)
       new_v%root%ptr => new_root
    end if
  end function vector_conj

  ! Real Clojure's vector assoc: index == count appends (same as
  ! conj), 0 <= index < count path-copies that one slot (both
  ! O(log32 n)); an out-of-range index is left unvalidated here, same
  ! as vector_nth already is -- callers that need an IndexOutOfBounds-
  ! style error check first.
  function vector_assoc(v, i, x) result(new_v)
    type(vec_t), intent(in) :: v
    integer, intent(in) :: i ! 0-based
    type(cons_value), intent(in) :: x
    type(vec_t) :: new_v
    if (i == v%count) then
       new_v = vector_conj(v, x)
    else
       new_v%count = v%count
       new_v%shift = v%shift
       new_v%root = node_assoc(v%root, v%shift, i, x)
    end if
  end function vector_assoc

  ! ---- cons_value-level accessors --------------------------------
  !
  ! These live HERE and not in Values.f90 because reaching an element
  ! means walking the trie, and Values cannot use this module -- the
  ! dependency runs one way only (PersistentVector uses values). So for
  ! vectors, "the one place that knows the representation" is this
  ! section plus the type declaration in Values. See PLAN.md 3c.
  !
  ! Each absorbs the allocated() guard its callers used to repeat: a
  ! value holding no vector counts 0 and nths to nil, which is what
  ! every call site did by hand.

  function has_vector(v) result(yes)
    type(cons_value), intent(in) :: v
    logical :: yes
    yes = allocated(v%vector_val)
  end function has_vector

  function val_vec_count(v) result(n)
    type(cons_value), intent(in) :: v
    integer :: n
    n = 0
    if (allocated(v%vector_val)) n = vector_count(v%vector_val)
  end function val_vec_count

  function val_vec_nth(v, i) result(x)
    type(cons_value), intent(in) :: v
    integer, intent(in) :: i ! 0-based
    type(cons_value) :: x
    if (.not. allocated(v%vector_val)) return
    if (i < 0 .or. i >= vector_count(v%vector_val)) return
    x = vector_nth(v%vector_val, i)
  end function val_vec_nth

  subroutine set_vector(v, vec)
    type(cons_value), intent(inout) :: v
    type(vec_t), intent(in) :: vec
    v%tag = TAG_VECTOR
    if (.not. allocated(v%vector_val)) allocate(v%vector_val)
    v%vector_val = vec
  end subroutine set_vector

  ! conj/assoc on a VALUE rather than a vec_t, so a caller never has to
  ! unwrap one. An absent vector conjes onto the empty vector, which is
  ! what (conj nil x) means anyway.
  function val_vec_conj(v, x) result(out)
    type(cons_value), intent(in) :: v, x
    type(cons_value) :: out
    if (allocated(v%vector_val)) then
       call set_vector(out, vector_conj(v%vector_val, x))
    else
       call set_vector(out, vector_conj(vector_empty(), x))
    end if
  end function val_vec_conj

  function val_vec_assoc(v, i, x) result(out)
    type(cons_value), intent(in) :: v, x
    integer, intent(in) :: i
    type(cons_value) :: out
    if (.not. allocated(v%vector_val)) return
    call set_vector(out, vector_assoc(v%vector_val, i, x))
  end function val_vec_assoc

end module PersistentVector

! PersistentVector: the 32-way branching trie's operations (nth/conj).
! Types (vec_t, vec_node, node_ref) live in Values.f90 -- see its header
! for why. The generic, type-dispatching nth/conj/count/etc. that
! anything actually calls live in RT.f90.
module PersistentVector
  use values
  implicit none
  private

  public :: vector_empty, vector_count, vector_nth, vector_conj

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

end module PersistentVector

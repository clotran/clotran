! PersistentArrayMap: a flat, linear-scan key/value array -- what real
! Clojure actually uses for maps up to 8 entries (only switching to a
! real hash trie, PersistentHashMap, beyond that). Every map here is
! that small for now, so this is the only map representation so far.
module PersistentArrayMap
  use values
  implicit none
  private

  public :: array_map_empty, array_map_count, array_map_get, array_map_assoc
  public :: array_map_nth_key, array_map_nth_val, array_map_contains, value_equal
  public :: array_map_dissoc

contains

  function array_map_empty() result(m)
    type(array_map_t) :: m
  end function array_map_empty

  function array_map_count(m) result(n)
    type(array_map_t), intent(in) :: m
    integer :: n
    n = 0
    if (associated(m%root%ptr)) n = size(m%root%ptr%keys)
  end function array_map_count

  ! 0-based, for RT/printer iteration.
  function array_map_nth_key(m, i) result(k)
    type(array_map_t), intent(in) :: m
    integer, intent(in) :: i
    type(cons_value) :: k
    k = m%root%ptr%keys(i + 1)
  end function array_map_nth_key

  function array_map_nth_val(m, i) result(v)
    type(array_map_t), intent(in) :: m
    integer, intent(in) :: i
    type(cons_value) :: v
    v = m%root%ptr%vals(i + 1)
  end function array_map_nth_val

  ! Value equality for map keys: same tag and same scalar/text content.
  ! Lists/vectors/maps as keys aren't compared deeply yet.
  function value_equal(a, b) result(eq)
    type(cons_value), intent(in) :: a, b
    logical :: eq
    eq = .false.
    if (a%tag /= b%tag) return
    select case (a%tag)
    case (TAG_NIL)
       eq = .true.
    case (TAG_BOOL)
       eq = (a%bool_val .eqv. b%bool_val)
    case (TAG_INT)
       eq = (a%int_val == b%int_val)
    case (TAG_REAL)
       eq = (a%real_val == b%real_val)
    case (TAG_STRING, TAG_SYMBOL, TAG_KEYWORD)
       if (allocated(a%str_val) .and. allocated(b%str_val)) then
          eq = (a%str_val == b%str_val)
       else
          eq = (.not. allocated(a%str_val) .and. .not. allocated(b%str_val))
       end if
    end select
  end function value_equal

  ! Distinguishes "unbound" from "bound to nil" -- array_map_get alone can't.
  function array_map_contains(m, key) result(bool)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key
    logical :: bool
    integer :: i
    bool = .false.
    if (associated(m%root%ptr)) then
       do i = 1, size(m%root%ptr%keys)
          if (value_equal(m%root%ptr%keys(i), key)) then
             bool = .true.
             return
          end if
       end do
    end if
  end function array_map_contains

  function array_map_get(m, key) result(val)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key
    type(cons_value) :: val
    integer :: i
    if (associated(m%root%ptr)) then
       do i = 1, size(m%root%ptr%keys)
          if (value_equal(m%root%ptr%keys(i), key)) then
             val = m%root%ptr%vals(i)
             return
          end if
       end do
    end if
  end function array_map_get

  ! Copies the whole (small) array -- fine at this size, same as real
  ! Clojure's array map.
  function array_map_assoc(m, key, val) result(new_m)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key, val
    type(array_map_t) :: new_m
    type(array_map_node), pointer :: new_node
    integer :: i, n, idx

    n = array_map_count(m)
    idx = 0
    do i = 1, n
       if (value_equal(m%root%ptr%keys(i), key)) then
          idx = i
          exit
       end if
    end do

    allocate(new_node)
    new_node%refcount = 1
    array_map_node_total_allocated = array_map_node_total_allocated + 1

    if (idx > 0) then
       allocate(new_node%keys(n))
       allocate(new_node%vals(n))
       new_node%keys(1:n) = m%root%ptr%keys(1:n)
       new_node%vals(1:n) = m%root%ptr%vals(1:n)
       new_node%vals(idx) = val
    else
       allocate(new_node%keys(n + 1))
       allocate(new_node%vals(n + 1))
       if (n > 0) then
          new_node%keys(1:n) = m%root%ptr%keys(1:n)
          new_node%vals(1:n) = m%root%ptr%vals(1:n)
       end if
       new_node%keys(n + 1) = key
       new_node%vals(n + 1) = val
    end if
    new_m%root%ptr => new_node
  end function array_map_assoc

  ! Copies the whole (small) array, skipping the matching key -- same
  ! approach as assoc. A missing key returns the map unchanged (a real
  ! copy via defined assignment, same as real Clojure's without()
  ! returning `this` when the key isn't present).
  function array_map_dissoc(m, key) result(new_m)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key
    type(array_map_t) :: new_m
    type(array_map_node), pointer :: new_node
    integer :: i, n, idx, j

    n = array_map_count(m)
    idx = 0
    do i = 1, n
       if (value_equal(m%root%ptr%keys(i), key)) then
          idx = i
          exit
       end if
    end do

    if (idx == 0) then
       new_m = m
       return
    end if

    allocate(new_node)
    new_node%refcount = 1
    array_map_node_total_allocated = array_map_node_total_allocated + 1
    allocate(new_node%keys(n - 1))
    allocate(new_node%vals(n - 1))
    j = 0
    do i = 1, n
       if (i == idx) cycle
       j = j + 1
       new_node%keys(j) = m%root%ptr%keys(i)
       new_node%vals(j) = m%root%ptr%vals(i)
    end do
    new_m%root%ptr => new_node
  end function array_map_dissoc

end module PersistentArrayMap

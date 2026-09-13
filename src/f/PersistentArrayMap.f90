! PersistentArrayMap: a flat, linear-scan key/value array -- what real
! Clojure actually uses for maps up to 8 entries, transparently
! promoting to a real hash trie (PersistentHashMap.f90) beyond that --
! array_map_assoc below does the promoting; every other function here
! just dispatches on whether a map has been promoted yet (m%big
! allocated) or not, so every caller (RT.f90, Namespace.f90, Env.f90,
! Eval.f90, printer.f90) gets the right asymptotic behavior for free,
! with no change needed on their end. Confirmed against the real
! `clojure` CLI: 8 entries stays a PersistentArrayMap, 9 becomes a
! PersistentHashMap -- same threshold here.
!
! Once promoted, iteration order (array_map_entries) is hash order,
! not insertion order -- also matching real Clojure exactly (only
! ArrayMap preserves insertion order; HashMap never promises to).
module PersistentArrayMap
  use values
  use PersistentHashMap, only: hamt_from_pairs, hamt_get, hamt_contains, &
       hamt_assoc, hamt_dissoc, hamt_entries
  implicit none
  private

  integer, parameter :: ARRAY_MAP_MAX = 8

  public :: array_map_empty, array_map_count, array_map_get, array_map_assoc
  public :: array_map_contains, array_map_dissoc, array_map_entries

contains

  function array_map_empty() result(m)
    type(array_map_t) :: m
  end function array_map_empty

  function array_map_count(m) result(n)
    type(array_map_t), intent(in) :: m
    integer :: n
    if (allocated(m%big)) then
       n = m%big_count
    else
       n = 0
       if (associated(m%root%ptr)) n = size(m%root%ptr%keys)
    end if
  end function array_map_count

  function array_map_contains(m, key) result(bool)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key
    logical :: bool
    integer :: i
    if (allocated(m%big)) then
       bool = hamt_contains(m%big, key)
       return
    end if
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
    if (allocated(m%big)) then
       val = hamt_get(m%big, key)
       return
    end if
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
  ! Clojure's array map -- until the (n+1)-th distinct key would push
  ! past ARRAY_MAP_MAX, at which point this promotes to a real hash
  ! trie instead (one-way: a promoted map never copies back down, even
  ! if dissoc later shrinks it below 8, same as real Clojure).
  function array_map_assoc(m, key, val) result(new_m)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key, val
    type(array_map_t) :: new_m
    type(array_map_node), pointer :: new_node
    type(cons_value), allocatable :: seed_keys(:), seed_vals(:)
    logical :: is_new
    integer :: i, n, idx

    if (allocated(m%big)) then
       allocate(new_m%big)
       new_m%big = hamt_assoc(m%big, key, val, is_new)
       new_m%big_count = m%big_count + merge(1, 0, is_new)
       return
    end if

    n = array_map_count(m)
    idx = 0
    do i = 1, n
       if (value_equal(m%root%ptr%keys(i), key)) then
          idx = i
          exit
       end if
    end do

    if (idx == 0 .and. n + 1 > ARRAY_MAP_MAX) then
       allocate(seed_keys(n + 1), seed_vals(n + 1))
       seed_keys(1:n) = m%root%ptr%keys(1:n)
       seed_vals(1:n) = m%root%ptr%vals(1:n)
       seed_keys(n + 1) = key
       seed_vals(n + 1) = val
       allocate(new_m%big)
       new_m%big = hamt_from_pairs(seed_keys, seed_vals)
       new_m%big_count = n + 1
       return
    end if

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
  ! returning `this` when the key isn't present). Once promoted, stays
  ! promoted even if this empties back out below ARRAY_MAP_MAX -- same
  ! one-way rule as assoc, matching real Clojure.
  function array_map_dissoc(m, key) result(new_m)
    type(array_map_t), intent(in) :: m
    type(cons_value), intent(in) :: key
    type(array_map_t) :: new_m
    type(array_map_node), pointer :: new_node
    logical :: removed
    integer :: i, n, idx, j

    if (allocated(m%big)) then
       allocate(new_m%big)
       new_m%big = hamt_dissoc(m%big, key, removed)
       new_m%big_count = m%big_count - merge(1, 0, removed)
       if (.not. removed) new_m = m
       return
    end if

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

  ! Every (key, val), in one O(n) pass -- insertion order for a small
  ! map, hash order once promoted (see module header). Real Clojure has
  ! no O(1) "nth entry of a map" either way; iteration is always a
  ! single full walk, never random access, so this replaces what used
  ! to be a per-index array_map_nth_key/val loop at every call site.
  !
  ! A function returning the allocatable array directly (this used to
  ! be two of those, array_map_keys/array_map_vals) is unreliable here:
  ! confirmed via an isolated repro that flang's automatic-reallocate-
  ! on-assignment for `x = f(...)` does not reliably resize x to the
  ! function's real result size, for an array of a type with defined
  ! assignment (cons_value) -- not just for the pointer-dereferenced-
  ! component or self-slice shapes documented elsewhere, but for a
  ! perfectly ordinary function call assigned into a fresh, distinct
  ! variable too. A subroutine with intent(out) allocatable arguments
  ! sidesteps it: the array comes back via argument association, not
  ! assignment(=) -- the same reliable pattern read_items already uses
  ! in LispReader.f90.
  subroutine array_map_entries(m, keys, vals)
    type(array_map_t), intent(in) :: m
    type(cons_value), allocatable, intent(out) :: keys(:), vals(:)
    integer :: n
    if (allocated(m%big)) then
       call hamt_entries(m%big, keys, vals)
    else if (associated(m%root%ptr)) then
       n = size(m%root%ptr%keys)
       allocate(keys(n), vals(n))
       keys(:) = m%root%ptr%keys(:)
       vals(:) = m%root%ptr%vals(:)
    else
       allocate(keys(0), vals(0))
    end if
  end subroutine array_map_entries

end module PersistentArrayMap

! Assoc: the map clotran actually uses, over the GC heap.
!
! A map is an array map up to 8 entries and a hash trie beyond, which
! is exactly what real Clojure does (confirmed against the `clojure`
! CLI: 8 entries stays a PersistentArrayMap, 9 becomes a
! PersistentHashMap). Small maps are the common case by a wide margin
! -- a destructuring form, a metadata map, an options map -- and a
! linear scan over 8 pairs beats hashing.
!
! This lives in a THIRD module rather than inside PersistentArrayMap, and that is
! forced rather than stylistic: PersistentHashMap already uses PersistentArrayMap for its
! collision buckets, so PersistentArrayMap using PersistentHashMap would be a module cycle.
! Fortran would reject it, and the arrangement is better anyway --
! neither representation knows the other exists, and the promotion
! rule is in one readable place.
!
! Promotion is ONE-WAY. Dropping back below 8 entries leaves a trie a
! trie, matching Clojure (a PersistentHashMap never demotes). Anything
! that assumed "small implies array map" would be wrong, which is why
! every operation here dispatches on the object's kind rather than on
! its count.
module Assoc
  use GC
  use PersistentArrayMap
  use PersistentHashMap
  implicit none
  private

  ! The threshold real Clojure uses. Crossing it is what triggers the
  ! one-way promotion.
  integer, parameter, public :: GCA_ARRAY_MAX = 8
  ! Sorted maps: the array map with its keys in comparator order. i2 = 1
  ! marks one and slot 3 holds its comparator (nil: Clojure's compare);
  ! it is never promoted, its keys are found by binary search, and each
  ! edit is a positional copy of the two runs -- O(n) per assoc, which
  ! is the ponytail ceiling; a balanced tree if a sorted map of many
  ! thousands ever matters. Ordering may run a Clojure fn, so it goes
  ! through `comparer`, which Eval supplies (compare_via); a comparer
  ! that fails answers huge(0) and the search stops.
  abstract interface
     function cmp_i(comparator, a, b) result(c)
       import :: gc_value
       type(gc_value), intent(in) :: comparator, a, b
       integer :: c
     end function cmp_i
  end interface
  procedure(cmp_i), pointer, save :: comparer => null()
  public :: gca_find_key
  public :: gca_set_comparer, gca_sorted_empty, gca_is_sorted, gca_comparator, &
       gca_key_at, gca_val_at, gca_sorted_from

  public :: gca_empty, gca_is, gca_count, gca_get, gca_contains, &
       gca_assoc, gca_dissoc, gca_is_array_map, gca_entries

contains

  function gca_empty(roots) result(m)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    m = gcm_empty(roots)
  end function gca_empty

  subroutine gca_set_comparer(f)
    procedure(cmp_i) :: f
    comparer => f
  end subroutine gca_set_comparer

  function gca_sorted_empty(comparator, roots) result(m)
    type(gc_value), intent(in) :: comparator
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    m = gcm_empty(with(roots, comparator))
    call gc_set_i2(m, 1)
    call gc_set_slot(m, 3, comparator)
  end function gca_sorted_empty

  function gca_is_sorted(m) result(yes)
    type(gc_value), intent(in) :: m
    logical :: yes
    yes = .false.
    if (gcm_is(m)) yes = (gc_i2(m) == 1)
  end function gca_is_sorted

  function gca_comparator(m) result(c)
    type(gc_value), intent(in) :: m
    type(gc_value) :: c
    c = gc_nil()
    if (gca_is_sorted(m)) c = gc_slot(m, 3)
  end function gca_comparator

  function gca_key_at(m, i) result(k)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: k
    k = gcm_key_at(m, i)
  end function gca_key_at

  function gca_val_at(m, i) result(v)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: v
    v = gcm_val_at(m, i)
  end function gca_val_at

  ! Binary search: `pos` is the first position whose key is not before
  ! k, count + 1 when every key is; `found` when one is equal to it.
  ! m and k are rooted here because the comparer may allocate.
  subroutine sorted_search(m, k, pos, found)
    type(gc_value), intent(in) :: m, k
    integer, intent(out) :: pos
    logical, intent(out) :: found
    integer :: lo, hi, mid, c, base
    found = .false.
    base = vs_enter(2)
    call vs_set(base + 1, m)
    call vs_set(base + 2, k)
    lo = 1
    hi = gcm_count(m)
    pos = hi + 1
    do while (lo <= hi)
       mid = (lo + hi) / 2
       c = comparer(gc_slot(vs_get(base + 1), 3), gcm_key_at(vs_get(base + 1), mid), vs_get(base + 2))
       if (c == huge(0)) then
          pos = gcm_count(m) + 1
          found = .false.
          exit
       end if
       if (c < 0) then
          lo = mid + 1
       else
          pos = mid
          hi = mid - 1
          if (c == 0) then
             found = .true.
             exit
          end if
       end if
    end do
    call vs_leave(base)
  end subroutine sorted_search

  ! For seqFrom: the first position at or after k, ascending, or the
  ! last at or before it, descending -- count + 1 or 0 when none.
  function gca_sorted_from(m, k, ascending) result(pos)
    type(gc_value), intent(in) :: m, k
    logical, intent(in) :: ascending
    integer :: pos
    logical :: found
    call sorted_search(m, k, pos, found)
    if (.not. ascending .and. .not. found) pos = pos - 1
  end function gca_sorted_from

  function gca_is(m) result(yes)
    type(gc_value), intent(in) :: m
    logical :: yes
    yes = gcm_is(m) .or. gch_is(m)
  end function gca_is

  ! Exposed so tests (and a future printer) can tell which
  ! representation a map is in without guessing from its count.
  function gca_is_array_map(m) result(yes)
    type(gc_value), intent(in) :: m
    logical :: yes
    yes = gcm_is(m)
  end function gca_is_array_map

  function gca_count(m) result(n)
    type(gc_value), intent(in) :: m
    integer :: n
    if (gcm_is(m)) then
       n = gcm_count(m)
    else if (gch_is(m)) then
       n = gch_count(m)
    else
       n = 0
    end if
  end function gca_count

  function gca_get(m, k) result(v)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: v
    integer :: pos
    logical :: found
    if (gca_is_sorted(m)) then
       v = gc_nil()
       call sorted_search(m, k, pos, found)
       if (found) v = gcm_val_at(m, pos)
    else if (gcm_is(m)) then
       v = gcm_get(m, k)
    else if (gch_is(m)) then
       v = gch_get(m, k)
    else
       v = gc_nil()
    end if
  end function gca_get

  function gca_contains(m, k) result(yes)
    type(gc_value), intent(in) :: m, k
    logical :: yes
    integer :: pos
    if (gca_is_sorted(m)) then
       call sorted_search(m, k, pos, yes)
    else if (gcm_is(m)) then
       yes = gcm_contains(m, k)
    else if (gch_is(m)) then
       yes = gch_contains(m, k)
    else
       yes = .false.
    end if
  end function gca_contains

  function gca_assoc(m, k, v, roots) result(out)
    type(gc_value), intent(in) :: m, k, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    type(gc_value), allocatable :: r2(:)

    out = gc_nil()
    if (gch_is(m)) then
       out = gch_assoc(m, k, v, roots)
       return
    end if
    if (.not. gcm_is(m)) return
    if (gca_is_sorted(m)) then
       ! in place of an equal key, or before the first key after it;
       ! the first key of all is compared with itself, which is where
       ! the comparer refuses one it cannot order (compare_via)
       block
         integer :: at
         logical :: found
         if (gcm_count(m) == 0) then
            if (comparer(gc_slot(m, 3), k, k) == huge(0)) then
               out = m
               return
            end if
         end if
         call sorted_search(m, k, at, found)
         r2 = with(with(roots, m), gc_slot(m, 3))
         if (found) then
            out = gcm_replace_at(m, at, v, r2)
         else
            out = gcm_insert_at(m, at, k, v, r2)
         end if
         call gc_set_i2(out, 1)
         call gc_set_slot(out, 3, gc_slot(m, 3))
       end block
       return
    end if

    ! Only a NEW key can push the map over the threshold; replacing an
    ! existing one leaves the count where it was, so a full array map
    ! stays an array map when you overwrite a key it already has.
    if (gcm_count(m) >= GCA_ARRAY_MAX .and. .not. gcm_contains(m, k)) then
       r2 = with(with(with(roots, m), k), v)
       out = promote(m, r2)
       out = gch_assoc(out, k, v, with(r2, out))
    else
       out = gcm_assoc(m, k, v, roots)
    end if
  end function gca_assoc

  ! No demotion: a trie stays a trie. See the module comment.
  function gca_dissoc(m, k, roots) result(out)
    type(gc_value), intent(in) :: m, k
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    out = m
    if (gca_is_sorted(m)) then
       block
         integer :: at
         logical :: found
         call sorted_search(m, k, at, found)
         if (found) then
            out = gcm_remove_at(m, at, with(with(roots, m), gc_slot(m, 3)))
            call gc_set_i2(out, 1)
            call gc_set_slot(out, 3, gc_slot(m, 3))
         end if
       end block
    else if (gcm_is(m)) then
       out = gcm_dissoc(m, k, roots)
    else if (gch_is(m)) then
       out = gch_dissoc(m, k, roots)
    end if
  end function gca_dissoc

  ! The key the map holds for k -- equal to it, but the map's OWN
  ! object, with the metadata it was stored with. find's entry carries
  ! it, as MapEntry(key, val) does; the lookup key answered instead.
  function gca_find_key(m, k) result(out)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: out
    integer :: i, at
    logical :: found
    out = gc_nil()
    if (gca_is_sorted(m)) then
       call sorted_search(m, k, at, found)
       if (found) out = gca_key_at(m, at)
    else if (gcm_is(m)) then
       do i = 1, gcm_count(m)
          if (gc_equal(gcm_key_at(m, i), k)) then
             out = gcm_key_at(m, i)
             return
          end if
       end do
    else if (gch_is(m)) then
       out = gch_find_key(m, k)
    end if
  end function gca_find_key

  ! Every entry, whichever representation the map is in.
  subroutine gca_entries(m, keys, vals)
    type(gc_value), intent(in) :: m
    type(gc_value), allocatable, intent(out) :: keys(:), vals(:)
    integer :: i
    if (gch_is(m)) then
       call gch_entries(m, keys, vals)
    else if (gcm_is(m)) then
       allocate(keys(gcm_count(m)), vals(gcm_count(m)))
       do i = 1, gcm_count(m)
          keys(i) = gcm_key_at(m, i)
          vals(i) = gcm_val_at(m, i)
       end do
    else
       allocate(keys(0), vals(0))
    end if
  end subroutine gca_entries

  ! Copies every entry of an array map into a fresh trie. The entries
  ! are read positionally rather than through get, so a key bound to
  ! nil survives -- reading them back with get would be unable to tell
  ! "absent" from "present and nil" and would quietly drop it.
  function promote(m, roots) result(t)
    type(gc_value), intent(in) :: m
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: t
    type(gc_value), allocatable :: r2(:)
    integer :: i
    r2 = with(roots, m)
    t = gch_empty(r2)
    do i = 1, gcm_count(m)
       t = gch_assoc(t, gcm_key_at(m, i), gcm_val_at(m, i), with(r2, t))
    end do
  end function promote

  function with(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function with

end module Assoc

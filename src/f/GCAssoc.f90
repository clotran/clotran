! GCAssoc: the map clotran actually uses, over the GC heap.
!
! A map is an array map up to 8 entries and a hash trie beyond, which
! is exactly what real Clojure does (confirmed against the `clojure`
! CLI: 8 entries stays a PersistentArrayMap, 9 becomes a
! PersistentHashMap). Small maps are the common case by a wide margin
! -- a destructuring form, a metadata map, an options map -- and a
! linear scan over 8 pairs beats hashing.
!
! This lives in a THIRD module rather than inside GCMap, and that is
! forced rather than stylistic: GCHamt already uses GCMap for its
! collision buckets, so GCMap using GCHamt would be a module cycle.
! Fortran would reject it, and the arrangement is better anyway --
! neither representation knows the other exists, and the promotion
! rule is in one readable place.
!
! Promotion is ONE-WAY. Dropping back below 8 entries leaves a trie a
! trie, matching Clojure (a PersistentHashMap never demotes). Anything
! that assumed "small implies array map" would be wrong, which is why
! every operation here dispatches on the object's kind rather than on
! its count.
module GCAssoc
  use GC
  use GCMap
  use GCHamt
  implicit none
  private

  ! The threshold real Clojure uses. Crossing it is what triggers the
  ! one-way promotion.
  integer, parameter, public :: GCA_ARRAY_MAX = 8

  public :: gca_empty, gca_is, gca_count, gca_get, gca_contains, &
       gca_assoc, gca_dissoc, gca_is_array_map, gca_entries

contains

  function gca_empty(roots) result(m)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    m = gcm_empty(roots)
  end function gca_empty

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
    if (gcm_is(m)) then
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
    if (gcm_is(m)) then
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
    if (gcm_is(m)) then
       out = gcm_dissoc(m, k, roots)
    else if (gch_is(m)) then
       out = gch_dissoc(m, k, roots)
    end if
  end function gca_dissoc

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

end module GCAssoc

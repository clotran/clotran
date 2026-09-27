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
  ! Sorted maps: an OBJ_MAP with i2 = 1 over a counted B+-tree (see
  ! "sorted maps" below), never promoted. Ordering may run a Clojure fn, so it goes
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
  ! the most entries in a leaf, and children under an internal node
  integer, parameter :: ST_MAX = 32
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
    type(gc_value) :: m, root
    root = gc_vec(0, with(roots, comparator))
    m = st_make(root, 0, 0, comparator, with(with(roots, comparator), root))
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
    if (gca_is_sorted(m)) then
       k = st_at(m, i, .true.)
    else
       k = gcm_key_at(m, i)
    end if
  end function gca_key_at

  function gca_val_at(m, i) result(v)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: v
    if (gca_is_sorted(m)) then
       v = st_at(m, i, .false.)
    else
       v = gcm_val_at(m, i)
    end if
  end function gca_val_at

  ! Binary search: `pos` is the first position whose key is not before
  ! k, count + 1 when every key is; `found` when one is equal to it.
  ! m and k are rooted here because the comparer may allocate.
  subroutine sorted_search(m, k, pos, found)
    type(gc_value), intent(in) :: m, k
    integer, intent(out) :: pos
    logical, intent(out) :: found
    call st_rank(m, k, pos, found)
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
       if (found) v = gca_val_at(m, pos)
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
       out = st_assoc(m, k, v, roots)
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
       out = st_dissoc(m, k, roots)
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
    if (gca_is_sorted(m)) then
       allocate(keys(gc_i1(m)), vals(gc_i1(m)))
       i = 0
       call st_fill(gc_slot(m, 1), st_height(m), keys, vals, i)
    else if (gch_is(m)) then
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

  ! ---- sorted maps: a counted B+-tree ------------------------------
  !
  ! A sorted map is an OBJ_MAP with i2 = 1: i1 its count, slot 1 the
  ! root node, slot 3 its comparator (nil: Clojure's compare), slot 4
  ! the height (0: the root is a leaf). A LEAF is a raw vec k1 v1 k2 v2
  ! ...; an INTERNAL node a raw vec of triples: a child, the count of
  ! its subtree, and the first key under it. An edit copies one path
  ! from the root, so assoc is O(log n) where the sorted array this
  ! replaced copied every entry: into a sorted-set of 100,000 took
  ! minutes. The counts make position i, and the position of the first
  ! key at or past k, O(log n) as well -- what seqs and subseq ask.
  ! ponytail: dissoc drops an emptied node but never merges thin
  ! siblings; heavy deletion leaves a shallow, sparse tree, still
  ! correct. Merge on underflow if that ever shows.
  !
  ! The comparer may run a Clojure fn and so collect: every node below
  ! is reachable from the map, which the entry points root, and every
  ! node made here is rooted before the next allocation.

  function st_make(root, n, height, comparator, roots) result(m)
    type(gc_value), intent(in) :: root, comparator
    integer, intent(in) :: n, height
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    m = gc_obj(OBJ_MAP, [root, gc_nil(), comparator, gc_int(height)], roots)
    call gc_set_i1(m, n)
    call gc_set_i2(m, 1)
  end function st_make

  integer function st_height(m)
    type(gc_value), intent(in) :: m
    type(gc_value) :: h
    h = gc_slot(m, 4)
    st_height = int(h%ival)
  end function st_height

  integer function st_len(node, h)
    type(gc_value), intent(in) :: node
    integer, intent(in) :: h
    if (h == 0) then
       st_len = gc_vec_len(node) / 2
    else
       st_len = gc_vec_len(node) / 3
    end if
  end function st_len

  integer function st_cnt(node, i)
    type(gc_value), intent(in) :: node
    integer, intent(in) :: i
    type(gc_value) :: c
    c = gc_vec_get(node, 3 * i - 1)
    st_cnt = int(c%ival)
  end function st_cnt

  ! the number of entries under a node
  integer function st_total(node, h) result(n)
    type(gc_value), intent(in) :: node
    integer, intent(in) :: h
    integer :: i
    if (h == 0) then
       n = gc_vec_len(node) / 2
    else
       n = 0
       do i = 1, gc_vec_len(node) / 3
          n = n + st_cnt(node, i)
       end do
    end if
  end function st_total

  function st_first_key(node, h) result(k)
    type(gc_value), intent(in) :: node
    integer, intent(in) :: h
    type(gc_value) :: k
    if (h == 0) then
       k = gc_vec_get(node, 1)
    else
       k = gc_vec_get(node, 3)
    end if
  end function st_first_key

  ! In a leaf: pos is the first entry whose key is not before k (n + 1
  ! when all are), found when it is equal; fail when the comparer could
  ! not order them.
  subroutine st_leaf_search(cmpv, leaf, k, pos, found, fail)
    type(gc_value), intent(in) :: cmpv, leaf, k
    integer, intent(out) :: pos
    logical, intent(out) :: found, fail
    integer :: lo, hi, mid, c
    found = .false.; fail = .false.
    lo = 1
    hi = gc_vec_len(leaf) / 2
    pos = hi + 1
    do while (lo <= hi)
       mid = (lo + hi) / 2
       c = comparer(cmpv, gc_vec_get(leaf, 2 * mid - 1), k)
       if (c == huge(0)) then
          fail = .true.
          return
       end if
       if (c < 0) then
          lo = mid + 1
       else
          pos = mid
          hi = mid - 1
          if (c == 0) then
             found = .true.
             return
          end if
       end if
    end do
  end subroutine st_leaf_search

  ! In an internal node: the last child whose first key is not after k
  ! (the first child when none is).
  integer function st_pick(cmpv, node, k, fail) result(i)
    type(gc_value), intent(in) :: cmpv, node, k
    logical, intent(out) :: fail
    integer :: lo, hi, mid, c
    fail = .false.
    i = 1
    lo = 2
    hi = gc_vec_len(node) / 3
    do while (lo <= hi)
       mid = (lo + hi) / 2
       c = comparer(cmpv, gc_vec_get(node, 3 * mid), k)
       if (c == huge(0)) then
          fail = .true.
          return
       end if
       if (c <= 0) then
          i = mid
          lo = mid + 1
       else
          hi = mid - 1
       end if
    end do
  end function st_pick

  ! The position (1-based) of the first key not before k, count + 1 when
  ! every key is; found when that key is equal to k.
  subroutine st_rank(m, k, pos, found)
    type(gc_value), intent(in) :: m, k
    integer, intent(out) :: pos
    logical, intent(out) :: found
    type(gc_value) :: node
    integer :: h, i, j, before, lp, base
    logical :: fail
    base = vs_enter(2)
    call vs_set(base + 1, m)
    call vs_set(base + 2, k)
    node = gc_slot(m, 1)
    before = 0
    found = .false.
    fail = .false.
    do h = st_height(m), 1, -1
       i = st_pick(gc_slot(m, 3), node, k, fail)
       if (fail) exit
       do j = 1, i - 1
          before = before + st_cnt(node, j)
       end do
       node = gc_vec_get(node, 3 * i - 2)
    end do
    if (.not. fail) call st_leaf_search(gc_slot(m, 3), node, k, lp, found, fail)
    if (fail) then
       pos = gc_i1(m) + 1
       found = .false.
    else
       pos = before + lp
    end if
    call vs_leave(base)
  end subroutine st_rank

  ! Entry i (1-based): its key when want_key, else its value.
  function st_at(m, i0, want_key) result(x)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i0
    logical, intent(in) :: want_key
    type(gc_value) :: x, node
    integer :: h, i, j
    x = gc_nil()
    i = i0
    if (i < 1 .or. i > gc_i1(m)) return
    node = gc_slot(m, 1)
    do h = st_height(m), 1, -1
       do j = 1, gc_vec_len(node) / 3
          if (i <= st_cnt(node, j)) exit
          i = i - st_cnt(node, j)
       end do
       node = gc_vec_get(node, 3 * j - 2)
    end do
    if (want_key) then
       x = gc_vec_get(node, 2 * i - 1)
    else
       x = gc_vec_get(node, 2 * i)
    end if
  end function st_at

  ! An internal node from `n` triples of children (child, its height
  ! below), counted and keyed from the children themselves.
  function st_internal(kids, n, h, roots) result(node)
    type(gc_value), intent(in) :: kids(:)
    integer, intent(in) :: n, h
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: node
    integer :: j
    node = gc_vec(3 * n, [roots, kids(1:n)])
    do j = 1, n
       call gc_vec_set(node, 3 * j - 2, kids(j))
       call gc_vec_set(node, 3 * j - 1, gc_int(st_total(kids(j), h - 1)))
       call gc_vec_set(node, 3 * j, st_first_key(kids(j), h - 1))
    end do
  end function st_internal

  ! Insert or replace k under `node` of height h. `out` is its new
  ! version and `sib` a second node when it split (nil otherwise);
  ! `added` when k was not there before.
  recursive subroutine st_ins(cmpv, node, h, k, v, out, sib, added, fail, roots)
    type(gc_value), intent(in) :: cmpv, node, k, v
    integer, intent(in) :: h
    type(gc_value), intent(out) :: out, sib
    logical, intent(out) :: added, fail
    type(gc_value), intent(in) :: roots(:)
    type(gc_value), allocatable :: kids(:)
    type(gc_value) :: c_out, c_sib
    integer :: n, pos, i, j, base, half
    logical :: found
    out = node
    sib = gc_nil()
    added = .false.
    base = vs_enter(4)
    call vs_set(base + 1, node)
    if (h == 0) then
       call st_leaf_search(cmpv, node, k, pos, found, fail)
       if (fail) then
          call vs_leave(base)
          return
       end if
       n = gc_vec_len(node) / 2
       if (found) then
          out = gc_vec(2 * n, [roots, node, k, v])
          do i = 1, 2 * n
             call gc_vec_set(out, i, gc_vec_get(node, i))
          end do
          call gc_vec_set(out, 2 * pos, v)
       else
          added = .true.
          ! entries 1..n+1 with (k, v) at pos; a leaf over ST_MAX halves
          half = n + 1
          if (n + 1 > ST_MAX) half = (n + 1) / 2
          out = gc_vec(2 * half, [roots, node, k, v])
          call vs_set(base + 2, out)
          if (half < n + 1) then
             sib = gc_vec(2 * (n + 1 - half), [roots, node, k, v, out])
             call vs_set(base + 3, sib)
          end if
          do j = 1, n + 1
             block
               type(gc_value) :: ek, ev
               if (j < pos) then
                  ek = gc_vec_get(node, 2 * j - 1); ev = gc_vec_get(node, 2 * j)
               else if (j == pos) then
                  ek = k; ev = v
               else
                  ek = gc_vec_get(node, 2 * j - 3); ev = gc_vec_get(node, 2 * j - 2)
               end if
               if (j <= half) then
                  call gc_vec_set(out, 2 * j - 1, ek); call gc_vec_set(out, 2 * j, ev)
               else
                  call gc_vec_set(sib, 2 * (j - half) - 1, ek); call gc_vec_set(sib, 2 * (j - half), ev)
               end if
             end block
          end do
       end if
       call vs_leave(base)
       return
    end if
    i = st_pick(cmpv, node, k, fail)
    if (fail) then
       call vs_leave(base)
       return
    end if
    call st_ins(cmpv, gc_vec_get(node, 3 * i - 2), h - 1, k, v, c_out, c_sib, added, fail, [roots, node])
    if (fail) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 2, c_out)
    call vs_set(base + 3, c_sib)
    n = gc_vec_len(node) / 3
    allocate(kids(n + 1))
    j = 0
    do pos = 1, n
       if (pos == i) then
          j = j + 1; kids(j) = c_out
          if (c_sib%tag /= GCT_NIL) then
             j = j + 1; kids(j) = c_sib
          end if
       else
          j = j + 1; kids(j) = gc_vec_get(node, 3 * pos - 2)
       end if
    end do
    if (j <= ST_MAX) then
       out = st_internal(kids, j, h, [roots, node, c_out, c_sib])
    else
       half = j / 2
       out = st_internal(kids(1:half), half, h, [roots, node, c_out, c_sib])
       call vs_set(base + 4, out)
       sib = st_internal(kids(half + 1:j), j - half, h, [roots, node, c_out, c_sib, out])
    end if
    call vs_leave(base)
  end subroutine st_ins

  ! Remove k from under `node`: `out` its new version, `emptied` when
  ! nothing is left in it, `removed` when k was there.
  recursive subroutine st_del(cmpv, node, h, k, out, emptied, removed, roots)
    type(gc_value), intent(in) :: cmpv, node, k
    integer, intent(in) :: h
    type(gc_value), intent(out) :: out
    logical, intent(out) :: emptied, removed
    type(gc_value), intent(in) :: roots(:)
    type(gc_value), allocatable :: kids(:)
    type(gc_value) :: c_out
    integer :: n, pos, i, j, base
    logical :: found, fail, c_empty
    out = node
    emptied = .false.
    removed = .false.
    base = vs_enter(2)
    call vs_set(base + 1, node)
    if (h == 0) then
       call st_leaf_search(cmpv, node, k, pos, found, fail)
       if (found .and. .not. fail) then
          removed = .true.
          n = gc_vec_len(node) / 2
          emptied = (n == 1)
          out = gc_vec(2 * (n - 1), [roots, node])
          j = 0
          do i = 1, n
             if (i == pos) cycle
             j = j + 1
             call gc_vec_set(out, 2 * j - 1, gc_vec_get(node, 2 * i - 1))
             call gc_vec_set(out, 2 * j, gc_vec_get(node, 2 * i))
          end do
       end if
       call vs_leave(base)
       return
    end if
    i = st_pick(cmpv, node, k, fail)
    if (fail) then
       call vs_leave(base)
       return
    end if
    call st_del(cmpv, gc_vec_get(node, 3 * i - 2), h - 1, k, c_out, c_empty, removed, [roots, node])
    if (.not. removed) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 2, c_out)
    n = gc_vec_len(node) / 3
    allocate(kids(n))
    j = 0
    do pos = 1, n
       if (pos == i) then
          if (c_empty) cycle
          j = j + 1; kids(j) = c_out
       else
          j = j + 1; kids(j) = gc_vec_get(node, 3 * pos - 2)
       end if
    end do
    emptied = (j == 0)
    if (emptied) then
       out = gc_vec(0, [roots, node])
    else
       out = st_internal(kids, j, h, [roots, node, c_out])
    end if
    call vs_leave(base)
  end subroutine st_del

  function st_assoc(m, k, v, roots) result(out)
    type(gc_value), intent(in) :: m, k, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, nroot, sib, top
    integer :: base, h
    logical :: added, fail
    out = m
    base = vs_enter(5)
    call vs_set(base + 1, m); call vs_set(base + 2, k); call vs_set(base + 3, v)
    ! an empty map still asks the comparer about its first key, which is
    ! where one it cannot order is refused (compare_via)
    if (gc_i1(m) == 0) then
       if (comparer(gc_slot(m, 3), k, k) == huge(0)) then
          call vs_leave(base)
          return
       end if
    end if
    h = st_height(m)
    call st_ins(gc_slot(m, 3), gc_slot(m, 1), h, k, v, nroot, sib, added, fail, [roots, m, k, v])
    if (fail) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, nroot)
    call vs_set(base + 5, sib)
    if (sib%tag /= GCT_NIL) then
       ! the root split: a new root over the two halves
       top = st_internal([nroot, sib], 2, h + 1, [roots, m, nroot, sib])
       call vs_set(base + 4, top)
       h = h + 1
    end if
    out = st_make(vs_get(base + 4), gc_i1(m) + merge(1, 0, added), h, gc_slot(m, 3), &
         [roots, m, vs_get(base + 4)])
    call vs_leave(base)
  end function st_assoc

  function st_dissoc(m, k, roots) result(out)
    type(gc_value), intent(in) :: m, k
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, nroot
    integer :: base, h
    logical :: emptied, removed
    out = m
    base = vs_enter(3)
    call vs_set(base + 1, m); call vs_set(base + 2, k)
    h = st_height(m)
    call st_del(gc_slot(m, 3), gc_slot(m, 1), h, k, nroot, emptied, removed, [roots, m, k])
    if (removed) then
       if (emptied) then
          nroot = gc_vec(0, [roots, m])
          h = 0
       end if
       ! a root with one child is that child
       do while (h > 0)
          if (gc_vec_len(nroot) /= 3) exit
          nroot = gc_vec_get(nroot, 1)
          h = h - 1
       end do
       call vs_set(base + 3, nroot)
       out = st_make(nroot, gc_i1(m) - 1, h, gc_slot(m, 3), [roots, m, nroot])
    end if
    call vs_leave(base)
  end function st_dissoc

  ! Every entry, in order.
  recursive subroutine st_fill(node, h, keys, vals, n)
    type(gc_value), intent(in) :: node
    integer, intent(in) :: h
    type(gc_value), intent(inout) :: keys(:), vals(:)
    integer, intent(inout) :: n
    integer :: i
    if (h == 0) then
       do i = 1, gc_vec_len(node) / 2
          n = n + 1
          keys(n) = gc_vec_get(node, 2 * i - 1)
          vals(n) = gc_vec_get(node, 2 * i)
       end do
    else
       do i = 1, gc_vec_len(node) / 3
          call st_fill(gc_vec_get(node, 3 * i - 2), h - 1, keys, vals, n)
       end do
    end if
  end subroutine st_fill

  function with(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function with

end module Assoc

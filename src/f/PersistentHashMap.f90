! PersistentHashMap: the hash array mapped trie, over the GC heap.
!
! What a real Clojure map promotes into past 8 entries. Five bits of
! the hash per level, so a node is 32 slots wide and a lookup is at
! most seven hops for a 32-bit hash.
!
! Shape:
!
!   trie   an object: slot 1 = root node, i1 = count
!   node   a vec run of 32 slots, each one of:
!            nil            empty
!            OBJ_HAMT_LEAF  slot 1 = key, slot 2 = val
!            a vec run      a child node, one level deeper
!            OBJ_MAP        a hash-collision bucket
!
! Collision buckets reuse PersistentArrayMap deliberately: a set of keys with the
! same 32-bit hash IS a small linear map, and writing a second linear
! scan here would be the same code twice. Collisions are rare enough
! that the linear cost never matters; correctness under them is what
! matters, and check 4 forces the case with deliberately colliding
! keys rather than hoping to stumble on one.
module PersistentHashMap
  use GC
  use PersistentArrayMap
  implicit none
  private

  integer, parameter :: HBITS = 5
  integer, parameter :: HBRANCH = 32
  integer, parameter :: HMASK = 31
  integer, parameter :: HMAX_SHIFT = 30 ! 6 levels of 5 bits, then buckets

  public :: gch_empty, gch_count, gch_is, gch_get, gch_contains, gch_assoc, gch_dissoc, gch_find_key
  public :: gch_entries
  public :: gch_cursor_first, gch_cursor_next, gch_cursor_key, gch_cursor_val

contains

  ! Rooting, throughout this module: a procedure's own values go on the
  ! value stack (vs_enter), and the caller's `roots` are passed on as
  ! they are. Root lists grown with with() -- an allocatable array made
  ! one element longer and copied, four of them per trie level -- were
  ! most of what an assoc cost (2.3 us into a 50000-entry map).
  function gch_empty(roots) result(t)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: t, root
    integer :: base
    root = gc_vec(HBRANCH, roots)
    base = vs_enter(1)
    call vs_set(base + 1, root)
    t = gc_obj(OBJ_HAMT, [root], roots)
    call gc_set_i1(t, 0)
    call vs_leave(base)
  end function gch_empty

  function gch_is(t) result(yes)
    type(gc_value), intent(in) :: t
    logical :: yes
    yes = (gc_kind(t) == OBJ_HAMT)
  end function gch_is

  function gch_count(t) result(n)
    type(gc_value), intent(in) :: t
    integer :: n
    n = 0
    if (gch_is(t)) n = gc_i1(t)
  end function gch_count

  function gch_get(t, k) result(v)
    type(gc_value), intent(in) :: t, k
    type(gc_value) :: v
    v = gc_nil()
    if (.not. gch_is(t)) return
    v = node_get(gc_slot(t, 1), gc_hash(k), 0, k)
  end function gch_get

  ! The key the map HOLDS for k: equal to it, and the map's own object,
  ! metadata and all -- what find's entry carries, as MapEntry does.
  function gch_find_key(t, k) result(out)
    type(gc_value), intent(in) :: t, k
    type(gc_value) :: out, node
    integer :: i
    out = gc_nil()
    if (.not. gch_is(t)) return
    node = node_find(gc_slot(t, 1), gc_hash(k), 0, k)
    select case (gc_kind(node))
    case (OBJ_HAMT_LEAF)
       out = gc_slot(node, 1)
    case (OBJ_MAP)
       do i = 1, gcm_count(node)
          if (gc_equal(gcm_key_at(node, i), k)) then
             out = gcm_key_at(node, i)
             return
          end if
       end do
    end select
  end function gch_find_key

  function gch_contains(t, k) result(yes)
    type(gc_value), intent(in) :: t, k
    type(gc_value) :: node
    logical :: yes
    yes = .false.
    if (.not. gch_is(t)) return
    node = node_find(gc_slot(t, 1), gc_hash(k), 0, k)
    yes = (node%tag /= GCT_NIL)
  end function gch_contains

  ! Walks to the slot k would live in and returns the LEAF or bucket
  ! entry, or nil. Separate from gch_get because "absent" and "present
  ! and nil" are different answers, and contains? needs the first.
  recursive function node_find(node, h, shift, k) result(found)
    type(gc_value), intent(in) :: node, k
    integer, intent(in) :: h, shift
    type(gc_value) :: found, slot
    integer :: idx

    found = gc_nil()
    if (node%tag /= GCT_VEC) return
    idx = iand(ishft(h, -shift), HMASK) + 1
    slot = gc_vec_get(node, idx)

    select case (gc_kind(slot))
    case (OBJ_HAMT_LEAF)
       if (gc_equal(gc_slot(slot, 1), k)) found = slot
    case (OBJ_MAP)
       if (gcm_contains(slot, k)) found = slot
    case default
       if (slot%tag == GCT_VEC) found = node_find(slot, h, shift + HBITS, k)
    end select
  end function node_find

  recursive function node_get(node, h, shift, k) result(v)
    type(gc_value), intent(in) :: node, k
    integer, intent(in) :: h, shift
    type(gc_value) :: v, slot
    integer :: idx

    v = gc_nil()
    if (node%tag /= GCT_VEC) return
    idx = iand(ishft(h, -shift), HMASK) + 1
    slot = gc_vec_get(node, idx)

    select case (gc_kind(slot))
    case (OBJ_HAMT_LEAF)
       if (gc_equal(gc_slot(slot, 1), k)) v = gc_slot(slot, 2)
    case (OBJ_MAP)
       v = gcm_get(slot, k)
    case default
       if (slot%tag == GCT_VEC) v = node_get(slot, h, shift + HBITS, k)
    end select
  end function node_get

  function gch_assoc(t, k, v, roots) result(out)
    type(gc_value), intent(in) :: t, k, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, new_root
    logical :: added
    integer :: base

    out = gc_nil()
    if (.not. gch_is(t)) return

    base = vs_enter(4)
    call vs_set(base + 1, t)
    call vs_set(base + 2, k)
    call vs_set(base + 3, v)
    added = .false.
    new_root = node_assoc(gc_slot(t, 1), gc_hash(k), 0, k, v, added, roots)
    call vs_set(base + 4, new_root)
    out = gc_obj(OBJ_HAMT, [new_root], roots)
    if (added) then
       call gc_set_i1(out, gc_i1(t) + 1)
    else
       call gc_set_i1(out, gc_i1(t))
    end if
    call vs_leave(base)
  end function gch_assoc

  ! Path-copies the one node on the way to k's slot and shares every
  ! other branch, exactly as the vector's assoc does. `added` comes
  ! back false when an existing key was replaced, so the caller keeps
  ! the count right without walking the trie to recount.
  recursive function node_assoc(node, h, shift, k, v, added, roots) result(out)
    type(gc_value), intent(in) :: node, k, v
    integer, intent(in) :: h, shift
    logical, intent(inout) :: added
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, slot, leaf, sub
    integer :: idx, i, base

    base = vs_enter(4)
    call vs_set(base + 1, node)
    call vs_set(base + 2, k)
    call vs_set(base + 3, v)
    out = gc_vec_clone(node, roots)
    call vs_set(base + 4, out)

    idx = iand(ishft(h, -shift), HMASK) + 1
    slot = gc_vec_get(out, idx)

    select case (gc_kind(slot))
    case (OBJ_HAMT_LEAF)
       if (gc_equal(gc_slot(slot, 1), k)) then
          ! Same key: replace the value, count unchanged.
          leaf = gc_obj(OBJ_HAMT_LEAF, [k, v], roots)
          call gc_vec_set(out, idx, leaf)
       else
          sub = split(slot, h, shift, k, v, roots)
          call gc_vec_set(out, idx, sub)
          added = .true.
       end if
    case (OBJ_MAP)
       ! A bucket already: adding to it is an array-map assoc, and the
       ! count only grows if the key was not already in there.
       if (.not. gcm_contains(slot, k)) added = .true.
       sub = gcm_assoc(slot, k, v, roots)
       call gc_vec_set(out, idx, sub)
    case default
       if (slot%tag == GCT_VEC) then
          sub = node_assoc(slot, h, shift + HBITS, k, v, added, roots)
          call gc_vec_set(out, idx, sub)
       else
          ! Empty: a fresh leaf.
          leaf = gc_obj(OBJ_HAMT_LEAF, [k, v], roots)
          call gc_vec_set(out, idx, leaf)
          added = .true.
       end if
    end select
    call vs_leave(base)
  end function node_assoc

  ! Two different keys wanting the same slot. Push both down a level
  ! and retry; if the hashes are equal all the way down (a genuine
  ! collision, not merely a shared prefix), stop and make a bucket.
  recursive function split(old_leaf, h, shift, k, v, roots) result(out)
    type(gc_value), intent(in) :: old_leaf, k, v
    integer, intent(in) :: h, shift
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, ok_, ov
    integer :: oh, base
    logical :: ignored

    base = vs_enter(4)
    call vs_set(base + 1, old_leaf)
    call vs_set(base + 2, k)
    call vs_set(base + 3, v)
    ok_ = gc_slot(old_leaf, 1)
    ov = gc_slot(old_leaf, 2)
    oh = gc_hash(ok_)

    if (oh == h .or. shift >= HMAX_SHIFT) then
       ! True collision: a bucket, which is just a tiny linear map.
       out = gcm_empty(roots)
       call vs_set(base + 4, out)
       out = gcm_assoc(out, ok_, ov, roots)
       call vs_set(base + 4, out)
       out = gcm_assoc(out, k, v, roots)
       call vs_leave(base)
       return
    end if

    out = gc_vec(HBRANCH, roots)
    call vs_set(base + 4, out)
    ignored = .false.
    out = node_assoc(out, oh, shift + HBITS, ok_, ov, ignored, roots)
    call vs_set(base + 4, out)
    ignored = .false.
    out = node_assoc(out, h, shift + HBITS, k, v, ignored, roots)
    call vs_leave(base)
  end function split

  ! Removes k. Nodes are NOT collapsed when they empty out: an empty
  ! child stays an empty child rather than reverting to nil, and a
  ! one-entry bucket stays a bucket. That is correct but slightly
  ! wasteful -- real Clojure collapses -- and it is deliberate: the
  ! collapse is where trie deletion gets subtle, and nothing here needs
  ! the space yet. Lookups are unaffected; an empty node simply has no
  ! matching slot.
  function gch_dissoc(t, k, roots) result(out)
    type(gc_value), intent(in) :: t, k
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, new_root
    logical :: removed
    integer :: base

    out = t
    if (.not. gch_is(t)) return
    if (.not. gch_contains(t, k)) return

    base = vs_enter(3)
    call vs_set(base + 1, t)
    call vs_set(base + 2, k)
    removed = .false.
    new_root = node_dissoc(gc_slot(t, 1), gc_hash(k), 0, k, removed, roots)
    if (removed) then
       call vs_set(base + 3, new_root)
       out = gc_obj(OBJ_HAMT, [new_root], roots)
       call gc_set_i1(out, gc_i1(t) - 1)
    end if
    call vs_leave(base)
  end function gch_dissoc

  recursive function node_dissoc(node, h, shift, k, removed, roots) result(out)
    type(gc_value), intent(in) :: node, k
    integer, intent(in) :: h, shift
    logical, intent(inout) :: removed
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, slot, sub
    integer :: idx, i, base

    base = vs_enter(3)
    call vs_set(base + 1, node)
    call vs_set(base + 2, k)
    out = gc_vec_clone(node, roots)
    call vs_set(base + 3, out)

    idx = iand(ishft(h, -shift), HMASK) + 1
    slot = gc_vec_get(out, idx)

    select case (gc_kind(slot))
    case (OBJ_HAMT_LEAF)
       if (gc_equal(gc_slot(slot, 1), k)) then
          call gc_vec_set(out, idx, gc_nil())
          removed = .true.
       end if
    case (OBJ_MAP)
       if (gcm_contains(slot, k)) then
          sub = gcm_dissoc(slot, k, roots)
          call gc_vec_set(out, idx, sub)
          removed = .true.
       end if
    case default
       if (slot%tag == GCT_VEC) then
          sub = node_dissoc(slot, h, shift + HBITS, k, removed, roots)
          call gc_vec_set(out, idx, sub)
       end if
    end select
    call vs_leave(base)
  end function node_dissoc

  ! Every key/value pair, in trie order (which is hash order, i.e.
  ! arbitrary -- a hash map is unordered and this does not pretend
  ! otherwise). Fills caller-allocated arrays rather than taking a
  ! callback: flang segfaults passing an internal procedure as a
  ! callback on macOS/ARM64 (see NOTES.md), so the whole codebase
  ! avoids that shape.
  subroutine gch_entries(t, keys, vals)
    type(gc_value), intent(in) :: t
    type(gc_value), allocatable, intent(out) :: keys(:), vals(:)
    integer :: n
    allocate(keys(gch_count(t)), vals(gch_count(t)))
    n = 0
    if (gch_is(t)) call walk(gc_slot(t, 1), keys, vals, n)
  end subroutine gch_entries

  recursive subroutine walk(node, keys, vals, n)
    type(gc_value), intent(in) :: node
    type(gc_value), intent(inout) :: keys(:), vals(:)
    integer, intent(inout) :: n
    type(gc_value) :: slot
    integer :: i, j
    if (node%tag /= GCT_VEC) return
    do i = 1, HBRANCH
       slot = gc_vec_get(node, i)
       select case (gc_kind(slot))
       case (OBJ_HAMT_LEAF)
          if (n < size(keys)) then
             n = n + 1
             keys(n) = gc_slot(slot, 1)
             vals(n) = gc_slot(slot, 2)
          end if
       case (OBJ_MAP)
          do j = 1, gcm_count(slot)
             if (n < size(keys)) then
                n = n + 1
                keys(n) = gcm_key_at(slot, j)
                vals(n) = gcm_val_at(slot, j)
             end if
          end do
       case default
          if (slot%tag == GCT_VEC) call walk(slot, keys, vals, n)
       end select
    end do
  end subroutine walk

  ! --- the cursor (model/hashmap.lisp) ---------------------------------
  !
  ! A seq over the trie, in the order gch_entries walks it, made one
  ! entry at a time where seq_snapshot copied every entry first: (first
  ! m) was O(n). A cursor is a FRAME, a vec run [node, slot, parent]:
  ! node a trie node with the entry in its slot, or a collision bucket
  ! (OBJ_MAP) with the slot its entry's position; parent the frame of
  ! the slot that led here, nil at the root. Frames are never changed,
  ! only made, so a seq that has moved on shares its parents. Each node
  ! is entered once and left once in a walk: next is O(1) amortized and
  ! first O(log32 n), as clj's NodeSeq.

  function mk_frame(node, slot, parent, roots) result(f)
    type(gc_value), intent(in) :: node, parent
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: f
    f = gc_vec(3, [roots, node, parent])
    call gc_vec_set(f, 1, node)
    call gc_vec_set(f, 2, gc_int(int(slot, gc_ip)))
    call gc_vec_set(f, 3, parent)
  end function mk_frame

  integer function frame_slot(f)
    type(gc_value), intent(in) :: f
    type(gc_value) :: s
    s = gc_vec_get(f, 2)
    frame_slot = int(s%ival)
  end function frame_slot

  ! the first entry of node at slot `from` or after, under parent; nil
  ! when the rest of the node holds none
  recursive function scan(node, from, parent, roots) result(f)
    type(gc_value), intent(in) :: node, parent
    integer, intent(in) :: from
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: f, slot, here
    integer :: i, base
    f = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, node)
    call vs_set(base + 2, parent)
    do i = from, HBRANCH
       slot = gc_vec_get(vs_get(base + 1), i)
       select case (gc_kind(slot))
       case (OBJ_HAMT_LEAF)
          f = mk_frame(vs_get(base + 1), i, vs_get(base + 2), roots)
          exit
       case (OBJ_MAP)
          if (gcm_count(slot) > 0) then
             here = mk_frame(vs_get(base + 1), i, vs_get(base + 2), roots)
             call vs_set(base + 3, here)
             f = mk_frame(gc_vec_get(gc_vec_get(vs_get(base + 3), 1), i), 1, vs_get(base + 3), roots)
             exit
          end if
       case default
          if (slot%tag == GCT_VEC) then
             here = mk_frame(vs_get(base + 1), i, vs_get(base + 2), roots)
             call vs_set(base + 3, here)
             f = scan(gc_vec_get(gc_vec_get(vs_get(base + 3), 1), i), 1, vs_get(base + 3), roots)
             if (f%tag /= GCT_NIL) exit
          end if
       end select
    end do
    call vs_leave(base)
  end function scan

  ! the cursor at the trie's first entry, nil when it has none
  function gch_cursor_first(t, roots) result(f)
    type(gc_value), intent(in) :: t
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: f
    f = gc_nil()
    if (gch_is(t)) f = scan(gc_slot(t, 1), 1, gc_nil(), [roots, t])
  end function gch_cursor_first

  ! the cursor at the entry after f's, nil after the last
  recursive function gch_cursor_next(f0, roots) result(f)
    type(gc_value), intent(in) :: f0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: f, node, par
    integer :: base
    f = gc_nil()
    base = vs_enter(1)
    call vs_set(base + 1, f0)
    node = gc_vec_get(f0, 1)
    if (gc_kind(node) == OBJ_MAP) then
       ! a collision bucket: its next entry, else on past its slot
       if (frame_slot(f0) < gcm_count(node)) then
          f = mk_frame(node, frame_slot(f0) + 1, gc_vec_get(f0, 3), roots)
       else
          f = gch_cursor_next(gc_vec_get(vs_get(base + 1), 3), roots)
       end if
    else
       f = scan(node, frame_slot(f0) + 1, gc_vec_get(f0, 3), roots)
       par = gc_vec_get(vs_get(base + 1), 3)
       if (f%tag == GCT_NIL .and. par%tag /= GCT_NIL) f = gch_cursor_next(par, roots)
    end if
    call vs_leave(base)
  end function gch_cursor_next

  function gch_cursor_key(f) result(k)
    type(gc_value), intent(in) :: f
    type(gc_value) :: k, node
    node = gc_vec_get(f, 1)
    if (gc_kind(node) == OBJ_MAP) then
       k = gcm_key_at(node, frame_slot(f))
    else
       k = gc_slot(gc_vec_get(node, frame_slot(f)), 1)
    end if
  end function gch_cursor_key

  function gch_cursor_val(f) result(v)
    type(gc_value), intent(in) :: f
    type(gc_value) :: v, node
    node = gc_vec_get(f, 1)
    if (gc_kind(node) == OBJ_MAP) then
       v = gcm_val_at(node, frame_slot(f))
    else
       v = gc_slot(gc_vec_get(node, frame_slot(f)), 2)
    end if
  end function gch_cursor_val

  ! --- helpers ---


end module PersistentHashMap

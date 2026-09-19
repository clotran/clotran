! GCHamt: the hash array mapped trie, over the GC heap.
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
! Collision buckets reuse GCMap deliberately: a set of keys with the
! same 32-bit hash IS a small linear map, and writing a second linear
! scan here would be the same code twice. Collisions are rare enough
! that the linear cost never matters; correctness under them is what
! matters, and check 4 forces the case with deliberately colliding
! keys rather than hoping to stumble on one.
module GCHamt
  use GC
  use GCMap
  implicit none
  private

  integer, parameter :: HBITS = 5
  integer, parameter :: HBRANCH = 32
  integer, parameter :: HMASK = 31
  integer, parameter :: HMAX_SHIFT = 30 ! 6 levels of 5 bits, then buckets

  public :: gch_empty, gch_count, gch_is, gch_get, gch_contains, gch_assoc, gch_dissoc
  public :: gch_entries

contains

  function gch_empty(roots) result(t)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: t, root
    root = gc_vec(HBRANCH, roots)
    block
      type(gc_value), allocatable :: r2(:)
      r2 = with(roots, root)
      t = gc_obj(OBJ_HAMT, [root], r2)
    end block
    call gc_set_i1(t, 0)
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
    type(gc_value), allocatable :: r2(:)
    logical :: added

    out = gc_nil()
    if (.not. gch_is(t)) return

    r2 = with(with(with(roots, t), k), v)
    added = .false.
    new_root = node_assoc(gc_slot(t, 1), gc_hash(k), 0, k, v, added, r2)

    block
      type(gc_value), allocatable :: r3(:)
      r3 = with(r2, new_root)
      out = gc_obj(OBJ_HAMT, [new_root], r3)
    end block
    if (added) then
       call gc_set_i1(out, gc_i1(t) + 1)
    else
       call gc_set_i1(out, gc_i1(t))
    end if
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
    type(gc_value), allocatable :: r2(:)
    integer :: idx, i

    r2 = with(with(with(roots, node), k), v)
    out = gc_vec(HBRANCH, r2)
    do i = 1, HBRANCH
       call gc_vec_set(out, i, gc_vec_get(node, i))
    end do
    r2 = with(r2, out)

    idx = iand(ishft(h, -shift), HMASK) + 1
    slot = gc_vec_get(out, idx)

    select case (gc_kind(slot))
    case (OBJ_HAMT_LEAF)
       if (gc_equal(gc_slot(slot, 1), k)) then
          ! Same key: replace the value, count unchanged.
          leaf = gc_obj(OBJ_HAMT_LEAF, [k, v], r2)
          call gc_vec_set(out, idx, leaf)
       else
          call gc_vec_set(out, idx, split(slot, h, shift, k, v, r2))
          added = .true.
       end if
    case (OBJ_MAP)
       ! A bucket already: adding to it is an array-map assoc, and the
       ! count only grows if the key was not already in there.
       if (.not. gcm_contains(slot, k)) added = .true.
       call gc_vec_set(out, idx, gcm_assoc(slot, k, v, r2))
    case default
       if (slot%tag == GCT_VEC) then
          sub = node_assoc(slot, h, shift + HBITS, k, v, added, r2)
          call gc_vec_set(out, idx, sub)
       else
          ! Empty: a fresh leaf.
          leaf = gc_obj(OBJ_HAMT_LEAF, [k, v], r2)
          call gc_vec_set(out, idx, leaf)
          added = .true.
       end if
    end select
  end function node_assoc

  ! Two different keys wanting the same slot. Push both down a level
  ! and retry; if the hashes are equal all the way down (a genuine
  ! collision, not merely a shared prefix), stop and make a bucket.
  recursive function split(old_leaf, h, shift, k, v, roots) result(out)
    type(gc_value), intent(in) :: old_leaf, k, v
    integer, intent(in) :: h, shift
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, ok_, ov
    type(gc_value), allocatable :: r2(:)
    integer :: oh
    logical :: ignored

    ok_ = gc_slot(old_leaf, 1)
    ov = gc_slot(old_leaf, 2)
    oh = gc_hash(ok_)
    r2 = with(with(with(with(roots, old_leaf), k), v), ok_)

    if (oh == h .or. shift >= HMAX_SHIFT) then
       ! True collision: a bucket, which is just a tiny linear map.
       out = gcm_empty(r2)
       out = gcm_assoc(out, ok_, ov, with(r2, out))
       out = gcm_assoc(out, k, v, with(r2, out))
       return
    end if

    out = gc_vec(HBRANCH, r2)
    r2 = with(r2, out)
    ignored = .false.
    out = node_assoc(out, oh, shift + HBITS, ok_, ov, ignored, r2)
    ignored = .false.
    out = node_assoc(out, h, shift + HBITS, k, v, ignored, with(r2, out))
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
    type(gc_value), allocatable :: r2(:)
    logical :: removed

    out = t
    if (.not. gch_is(t)) return
    if (.not. gch_contains(t, k)) return

    r2 = with(with(roots, t), k)
    removed = .false.
    new_root = node_dissoc(gc_slot(t, 1), gc_hash(k), 0, k, removed, r2)
    if (.not. removed) return

    block
      type(gc_value), allocatable :: r3(:)
      r3 = with(r2, new_root)
      out = gc_obj(OBJ_HAMT, [new_root], r3)
    end block
    call gc_set_i1(out, gc_i1(t) - 1)
  end function gch_dissoc

  recursive function node_dissoc(node, h, shift, k, removed, roots) result(out)
    type(gc_value), intent(in) :: node, k
    integer, intent(in) :: h, shift
    logical, intent(inout) :: removed
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, slot, sub
    type(gc_value), allocatable :: r2(:)
    integer :: idx, i

    r2 = with(with(roots, node), k)
    out = gc_vec(HBRANCH, r2)
    do i = 1, HBRANCH
       call gc_vec_set(out, i, gc_vec_get(node, i))
    end do
    r2 = with(r2, out)

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
          call gc_vec_set(out, idx, gcm_dissoc(slot, k, r2))
          removed = .true.
       end if
    case default
       if (slot%tag == GCT_VEC) then
          sub = node_dissoc(slot, h, shift + HBITS, k, removed, r2)
          call gc_vec_set(out, idx, sub)
       end if
    end select
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

  ! --- helpers ---

  function with(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function with

end module GCHamt

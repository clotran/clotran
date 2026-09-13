! PersistentHashMap: a real hash-array-mapped trie (HAMT), the same
! algorithm PersistentVector.f90 uses -- branching 32 ways per level,
! path-copying on write -- except keyed on hash bits instead of a
! sequential index, and each node uses a full BRANCH-slot array rather
! than real Clojure's bitmap-compressed sparse array (same O(log32 n),
! effectively O(1) since depth <= 7 for a 32-bit hash; just a higher
! constant memory factor per node -- see NOTES.md).
!
! PersistentArrayMap.f90 is what actually gets called for every map/
! set/namespace/env; it promotes into this module once past 8 entries
! (real Clojure's own threshold, confirmed via the `clojure` CLI) and
! never demotes back, same as upstream. Nothing else calls here
! directly.
module PersistentHashMap
  use values
  implicit none
  private

  public :: hamt_from_pairs, hamt_get, hamt_contains, hamt_assoc, &
       hamt_dissoc, hamt_entries

contains

  ! ---- hashing: doesn't need to match Java's hashCode bit-for-bit,
  ! only to be internally consistent (equal keys hash equal) and well
  ! distributed. mix32 is Murmur3's finalizer; fnv1a is the standard
  ! string hash. Compound keys (vectors/lists/maps used as map keys)
  ! all hash to 0 -- they'd all land in one bucket, linear-scanned by
  ! value_equal, which doesn't compare them deeply yet either (a
  ! pre-existing gap, same in the small-map tier; not made any worse
  ! here, just not fixed here).

  function mix32(x) result(h)
    integer, intent(in) :: x
    integer :: h
    h = x
    h = ieor(h, ishft(h, -16))
    h = h * (-2048144789) ! 0x85ebca6b as signed 32-bit
    h = ieor(h, ishft(h, -13))
    h = h * (-1028477387) ! 0xc2b2ae35 as signed 32-bit
    h = ieor(h, ishft(h, -16))
  end function mix32

  function fnv1a(s) result(h)
    character(len=*), intent(in) :: s
    integer :: h, i
    h = -2128831035 ! FNV offset basis, 0x811c9dc5, as signed 32-bit
    do i = 1, len(s)
       h = ieor(h, iachar(s(i:i)))
       h = h * 16777619 ! FNV prime
    end do
  end function fnv1a

  function hash_of(v) result(h)
    type(cons_value), intent(in) :: v
    integer :: h
    integer(kind=8) :: bits8
    select case (v%tag)
    case (TAG_NIL)
       h = 0
    case (TAG_BOOL)
       if (v%bool_val) then
          h = 1231
       else
          h = 1237
       end if
    case (TAG_INT)
       h = mix32(v%int_val)
    case (TAG_REAL)
       bits8 = transfer(v%real_val, bits8)
       h = mix32(int(ieor(bits8, ishft(bits8, -32)), kind=4))
    case (TAG_STRING, TAG_SYMBOL, TAG_KEYWORD)
       if (allocated(v%str_val)) then
          h = mix32(ieor(fnv1a(v%str_val), v%tag))
       else
          h = mix32(v%tag)
       end if
    case default
       h = 0
    end select
  end function hash_of

  ! ---- node-level operations, keyed by (shift, hash) ----

  recursive function node_get(node, shift, h, key, found) result(val)
    type(hamt_ref), intent(in) :: node
    integer, intent(in) :: shift, h
    type(cons_value), intent(in) :: key
    logical, intent(out) :: found
    type(cons_value) :: val
    integer :: idx, j

    found = .false.
    if (.not. associated(node%ptr)) return
    idx = iand(ishft(h, -shift), MASK) + 1
    select case (node%ptr%slots(idx)%kind)
    case (HAMT_LEAF)
       if (value_equal(node%ptr%slots(idx)%key, key)) then
          val = node%ptr%slots(idx)%val
          found = .true.
       end if
    case (HAMT_CHILD)
       val = node_get(node%ptr%slots(idx)%child, shift + BITS, h, key, found)
    case (HAMT_BUCKET)
       do j = 1, size(node%ptr%slots(idx)%bucket_keys)
          if (value_equal(node%ptr%slots(idx)%bucket_keys(j), key)) then
             val = node%ptr%slots(idx)%bucket_vals(j)
             found = .true.
             return
          end if
       end do
    end select
  end function node_get

  ! Path-copies from node_in down to key's slot, sharing every
  ! untouched sibling by reference (same structural-sharing shape as
  ! PersistentVector's node_assoc). is_new is set so callers can
  ! maintain an O(1) count without a separate lookup pass.
  recursive function node_assoc(node_in, shift, h, key, val, is_new) result(new_ref)
    type(hamt_ref), intent(in) :: node_in
    integer, intent(in) :: shift, h
    type(cons_value), intent(in) :: key, val
    logical, intent(out) :: is_new
    type(hamt_ref) :: new_ref
    type(hamt_node), pointer :: new_node
    type(hamt_ref) :: empty_child
    integer :: idx, j, n_old
    type(cons_value), allocatable :: new_keys(:), new_vals(:)

    allocate(new_node)
    new_node%refcount = 1
    hamt_node_total_allocated = hamt_node_total_allocated + 1
    ! Pre-allocated to exactly BRANCH, then assigned in place -- never
    ! a bare `new_node%slots = node_in%ptr%slots` relying on automatic
    ! reallocate-on-assignment, confirmed unreliable for an array of a
    ! type with defined assignment (see array_map_keys's own fix in
    ! PersistentArrayMap.f90 for the full story).
    allocate(new_node%slots(BRANCH))
    if (associated(node_in%ptr)) then
       new_node%slots(:) = node_in%ptr%slots(:)
    end if

    idx = iand(ishft(h, -shift), MASK) + 1
    select case (new_node%slots(idx)%kind)
    case (HAMT_EMPTY)
       new_node%slots(idx)%kind = HAMT_LEAF
       new_node%slots(idx)%key = key
       new_node%slots(idx)%val = val
       is_new = .true.
    case (HAMT_LEAF)
       if (value_equal(new_node%slots(idx)%key, key)) then
          new_node%slots(idx)%val = val
          is_new = .false.
       else if (shift + BITS < 32) then
          ! Two different keys landed on the same slot -- push the
          ! existing leaf down one level alongside the new key. Two
          ! DISTINCT temporaries (step1, step2), never a variable
          ! assigned from a node_assoc call that itself takes that
          ! same variable as input -- x = node_assoc(x, ...) corrupts
          ! the trie under flang once enough push-downs have happened
          ! (confirmed via an isolated repro outside this file), even
          ! for a plain local hamt_ref, not just a derived-type
          ! component.
          block
            type(cons_value) :: old_key, old_val
            type(hamt_ref) :: step1, step2
            old_key = new_node%slots(idx)%key
            old_val = new_node%slots(idx)%val
            step1 = node_assoc(empty_child, shift + BITS, hash_of(old_key), old_key, old_val, is_new)
            step2 = node_assoc(step1, shift + BITS, h, key, val, is_new)
            new_node%slots(idx)%kind = HAMT_CHILD
            new_node%slots(idx)%child = step2
          end block
          is_new = .true.
       else
          ! Hash bits fully exhausted and still a different key: a
          ! genuine full hash collision (vanishingly rare) -- fall
          ! back to a small linear bucket.
          allocate(new_keys(2), new_vals(2))
          new_keys(1) = new_node%slots(idx)%key
          new_vals(1) = new_node%slots(idx)%val
          new_keys(2) = key
          new_vals(2) = val
          new_node%slots(idx)%kind = HAMT_BUCKET
          call move_alloc(new_keys, new_node%slots(idx)%bucket_keys)
          call move_alloc(new_vals, new_node%slots(idx)%bucket_vals)
          is_new = .true.
       end if
    case (HAMT_CHILD)
       ! Same self-referencing-component hazard as the push-down case
       ! above -- go through a local tmp_child rather than assigning
       ! new_node%slots(idx)%child from a node_assoc call that itself
       ! takes new_node%slots(idx)%child as input.
       block
         type(hamt_ref) :: tmp_child
         tmp_child = node_assoc(new_node%slots(idx)%child, shift + BITS, h, key, val, is_new)
         new_node%slots(idx)%child = tmp_child
       end block
    case (HAMT_BUCKET)
       n_old = size(new_node%slots(idx)%bucket_keys)
       do j = 1, n_old
          if (value_equal(new_node%slots(idx)%bucket_keys(j), key)) then
             new_node%slots(idx)%bucket_vals(j) = val
             is_new = .false.
             new_ref%ptr => new_node
             return
          end if
       end do
       allocate(new_keys(n_old + 1), new_vals(n_old + 1))
       new_keys(1:n_old) = new_node%slots(idx)%bucket_keys(1:n_old)
       new_vals(1:n_old) = new_node%slots(idx)%bucket_vals(1:n_old)
       new_keys(n_old + 1) = key
       new_vals(n_old + 1) = val
       call move_alloc(new_keys, new_node%slots(idx)%bucket_keys)
       call move_alloc(new_vals, new_node%slots(idx)%bucket_vals)
       is_new = .true.
    end select

    new_ref%ptr => new_node
  end function node_assoc

  ! Path-copies from node_in down to key's slot, removing it; collapses
  ! a slot back to empty when that empties out a child subtree too, so
  ! repeated dissoc doesn't leak ever-deeper trie shape.
  recursive function node_dissoc(node_in, shift, h, key, removed) result(new_ref)
    type(hamt_ref), intent(in) :: node_in
    integer, intent(in) :: shift, h
    type(cons_value), intent(in) :: key
    logical, intent(out) :: removed
    type(hamt_ref) :: new_ref
    type(hamt_node), pointer :: new_node
    integer :: idx, j, n_old
    type(cons_value), allocatable :: new_keys(:), new_vals(:)

    removed = .false.
    if (.not. associated(node_in%ptr)) return

    allocate(new_node)
    new_node%refcount = 1
    hamt_node_total_allocated = hamt_node_total_allocated + 1
    ! Pre-allocated then assigned in place -- see node_assoc's own
    ! comment on this same pattern.
    allocate(new_node%slots(BRANCH))
    new_node%slots(:) = node_in%ptr%slots(:)

    idx = iand(ishft(h, -shift), MASK) + 1
    select case (new_node%slots(idx)%kind)
    case (HAMT_LEAF)
       if (value_equal(new_node%slots(idx)%key, key)) then
          new_node%slots(idx)%kind = HAMT_EMPTY
          removed = .true.
       end if
    case (HAMT_CHILD)
       ! Same self-referencing-component hazard as node_assoc's own
       ! HAMT_CHILD case -- see there.
       block
         type(hamt_ref) :: tmp_child
         tmp_child = node_dissoc(new_node%slots(idx)%child, shift + BITS, h, key, removed)
         new_node%slots(idx)%child = tmp_child
       end block
       if (removed .and. .not. associated(new_node%slots(idx)%child%ptr)) then
          new_node%slots(idx)%kind = HAMT_EMPTY
       end if
    case (HAMT_BUCKET)
       n_old = size(new_node%slots(idx)%bucket_keys)
       do j = 1, n_old
          if (value_equal(new_node%slots(idx)%bucket_keys(j), key)) then
             removed = .true.
             exit
          end if
       end do
       if (removed) then
          if (n_old == 1) then
             new_node%slots(idx)%kind = HAMT_EMPTY
             deallocate(new_node%slots(idx)%bucket_keys, new_node%slots(idx)%bucket_vals)
          else
             allocate(new_keys(n_old - 1), new_vals(n_old - 1))
             new_keys(1:j-1) = new_node%slots(idx)%bucket_keys(1:j-1)
             new_vals(1:j-1) = new_node%slots(idx)%bucket_vals(1:j-1)
             new_keys(j:) = new_node%slots(idx)%bucket_keys(j+1:n_old)
             new_vals(j:) = new_node%slots(idx)%bucket_vals(j+1:n_old)
             call move_alloc(new_keys, new_node%slots(idx)%bucket_keys)
             call move_alloc(new_vals, new_node%slots(idx)%bucket_vals)
          end if
       end if
    end select

    if (.not. removed) then
       ! Nothing changed -- discard the copy, hand back the original
       ! (still correct either way; just avoids an unnecessary path
       ! copy sitting unused).
       deallocate(new_node)
       hamt_node_total_allocated = hamt_node_total_allocated - 1
       new_ref = node_in
       return
    end if

    ! Collapse: if this whole node is now empty, hand back an empty ref
    ! instead of an empty node, so a parent's collapse check (above)
    ! and hamt_entries (which skips HAMT_EMPTY) both see it.
    do idx = 1, BRANCH
       if (new_node%slots(idx)%kind /= HAMT_EMPTY) then
          new_ref%ptr => new_node
          return
       end if
    end do
    deallocate(new_node)
    hamt_node_total_allocated = hamt_node_total_allocated - 1
  end function node_dissoc


  ! ---- public API: root is a hamt_ref, count is tracked by the caller
  ! (PersistentArrayMap.f90 already tracks it across the promotion) ----

  function hamt_get(root, key) result(val)
    type(hamt_ref), intent(in) :: root
    type(cons_value), intent(in) :: key
    type(cons_value) :: val
    logical :: found
    val = node_get(root, 0, hash_of(key), key, found)
  end function hamt_get

  function hamt_contains(root, key) result(bool)
    type(hamt_ref), intent(in) :: root
    type(cons_value), intent(in) :: key
    logical :: bool
    type(cons_value) :: val
    val = node_get(root, 0, hash_of(key), key, bool)
  end function hamt_contains

  function hamt_assoc(root, key, val, is_new) result(new_root)
    type(hamt_ref), intent(in) :: root
    type(cons_value), intent(in) :: key, val
    logical, intent(out) :: is_new
    type(hamt_ref) :: new_root
    new_root = node_assoc(root, 0, hash_of(key), key, val, is_new)
  end function hamt_assoc

  function hamt_dissoc(root, key, removed) result(new_root)
    type(hamt_ref), intent(in) :: root
    type(cons_value), intent(in) :: key
    logical, intent(out) :: removed
    type(hamt_ref) :: new_root
    new_root = node_dissoc(root, 0, hash_of(key), key, removed)
  end function hamt_dissoc

  ! Builds a fresh trie from n existing (key, val) pairs -- used once,
  ! at promotion time, to seed the hash tier from an array-map's
  ! entries plus the one new pair that pushed it over the threshold.
  ! Alternates between two distinct accumulators rather than
  ! self-assigning one (root = hamt_assoc(root, ...)) -- see
  ! node_assoc's own header comment for why.
  function hamt_from_pairs(keys, vals) result(root)
    type(cons_value), intent(in) :: keys(:), vals(:)
    type(hamt_ref) :: root
    type(hamt_ref) :: next
    logical :: is_new
    integer :: i
    do i = 1, size(keys)
       next = hamt_assoc(root, keys(i), vals(i), is_new)
       root = next
    end do
  end function hamt_from_pairs


  subroutine hamt_keys_vals(root, keys, vals, n)
    type(hamt_ref), intent(in) :: root
    type(cons_value), allocatable, intent(out) :: keys(:), vals(:)
    integer, intent(out) :: n
    integer :: cap
    ! Upper bound: BRANCH**7 covers a full 32-bit hash depth, but the
    ! real bound needed is just "however many entries exist" -- grow
    ! geometrically rather than guess, same fix as the reader's own
    ! read_items over-allocation bug (see NOTES.md).
    cap = 8
    allocate(keys(cap), vals(cap))
    n = 0
    call node_walk_counted(root, keys, vals, n, cap)
  end subroutine hamt_keys_vals

  ! node_walk needs its target arrays pre-sized to the final count,
  ! which isn't known up front for a trie (unlike array_map's flat
  ! array) -- so walk into growable ones instead, doubling on demand.
  recursive subroutine node_walk_counted(node, keys, vals, n, cap)
    type(hamt_ref), intent(in) :: node
    type(cons_value), allocatable, intent(inout) :: keys(:), vals(:)
    integer, intent(inout) :: n, cap
    integer :: i, j
    if (.not. associated(node%ptr)) return
    do i = 1, BRANCH
       select case (node%ptr%slots(i)%kind)
       case (HAMT_LEAF)
          call grow_if_needed(keys, vals, n, cap)
          n = n + 1
          keys(n) = node%ptr%slots(i)%key
          vals(n) = node%ptr%slots(i)%val
       case (HAMT_CHILD)
          call node_walk_counted(node%ptr%slots(i)%child, keys, vals, n, cap)
       case (HAMT_BUCKET)
          do j = 1, size(node%ptr%slots(i)%bucket_keys)
             call grow_if_needed(keys, vals, n, cap)
             n = n + 1
             keys(n) = node%ptr%slots(i)%bucket_keys(j)
             vals(n) = node%ptr%slots(i)%bucket_vals(j)
          end do
       end select
    end do
  end subroutine node_walk_counted

  subroutine grow_if_needed(keys, vals, n, cap)
    type(cons_value), allocatable, intent(inout) :: keys(:), vals(:)
    integer, intent(in) :: n
    integer, intent(inout) :: cap
    type(cons_value), allocatable :: gk(:), gv(:)
    if (n < cap) return
    cap = cap * 2
    allocate(gk(cap), gv(cap))
    gk(1:n) = keys(1:n)
    gv(1:n) = vals(1:n)
    call move_alloc(gk, keys)
    call move_alloc(gv, vals)
  end subroutine grow_if_needed

  ! A function returning an allocatable array (hamt_keys/hamt_vals used
  ! to be exactly that) is unreliable here: `x = f(...)` for a type
  ! with defined assignment (cons_value) does not reliably (re)allocate
  ! x to the real result size on flang -- confirmed via an isolated
  ! repro outside this codebase, independent of self-referencing or
  ! pointer-derefencing concerns already documented elsewhere (this hit
  ! even a fresh, distinct target variable). A subroutine with
  ! intent(out) allocatable arguments sidesteps it entirely: the
  ! standard argument-association mechanism (not assignment(=)) is what
  ! hands the array back, the same reliable pattern read_items already
  ! uses in LispReader.f90. One combined subroutine, not two functions,
  ! also avoids walking the whole trie twice for keys and vals.
  subroutine hamt_entries(root, keys, vals)
    type(hamt_ref), intent(in) :: root
    type(cons_value), allocatable, intent(out) :: keys(:), vals(:)
    type(cons_value), allocatable :: raw_keys(:), raw_vals(:)
    integer :: n
    call hamt_keys_vals(root, raw_keys, raw_vals, n)
    allocate(keys(n), vals(n))
    keys(:) = raw_keys(1:n)
    vals(:) = raw_vals(1:n)
  end subroutine hamt_entries

end module PersistentHashMap

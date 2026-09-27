! PersistentVector: the persistent vector, over the GC heap.
!
! Clojure's 32-way branching trie, with every reference a GC handle.
! Built and tested on its own first, the way GC.f90 and the value
! stack were, so the data layer could be proven before the evaluator
! was switched onto it.
!
! Why this one first: the trie is the most intricate structure in the
! layer, and it is where the refcounted evaluator's use-after-free
! lived -- a node released while a live reference still pointed at it.
! Under a tracing collector that bug cannot be expressed. Nothing decrements, so nothing can
! decrement too often; a node is reachable or it is not.
!
! Shape, matching GC.f90's own comment on OBJ_VECTOR:
!
!   vector   an object: slot 1 = root node, i1 = count, i2 = shift
!   node     a vec-pool run of BRANCH values -- child nodes at any
!            shift above 0, elements at shift 0
!
! Path copying is unchanged from the refcounted version: assoc rebuilds
! the nodes along one path and SHARES every untouched child. That is
! what makes a persistent vector cheap, and sharing is exactly what a
! tracing collector handles without any bookkeeping at the call site.
module PersistentVector
  use GC
  implicit none
  private

  integer, parameter :: VBITS = 5
  integer, parameter :: VBRANCH = 32
  integer, parameter :: VMASK = 31

  public :: gcv_empty, gcv_count, gcv_nth, gcv_conj, gcv_assoc, gcv_is, gcv_build, gcv_put
  public :: gcv_transient, gcv_tcount, gcv_tnth, gcv_tconj, gcv_tassoc, gcv_tdrop, gcv_persistent

contains

  function gcv_empty(roots) result(v)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    type(gc_value) :: none(0)
    v = gc_obj(OBJ_VECTOR, none, roots)
    call gc_set_i1(v, 0)
    call gc_set_i2(v, 0)
  end function gcv_empty

  function gcv_is(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = (gc_kind(v) == OBJ_VECTOR)
  end function gcv_is

  function gcv_count(v) result(n)
    type(gc_value), intent(in) :: v
    integer :: n
    n = 0
    if (gcv_is(v)) n = gc_i1(v)
  end function gcv_count

  ! 0-based, to match Clojure's nth and the refcounted implementation.
  ! Out of range gives nil rather than an error; callers that care test
  ! the count first, exactly as they do today.
  function gcv_nth(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out, node
    integer :: shift, idx
    out = gc_nil()
    if (.not. gcv_is(v)) return
    if (i < 0 .or. i >= gc_i1(v)) return
    node = gc_slot(v, 1)
    shift = gc_i2(v)
    do while (shift > 0)
       idx = iand(ishft(i, -shift), VMASK) + 1
       node = gc_vec_get(node, idx)
       shift = shift - VBITS
    end do
    out = gc_vec_get(node, iand(i, VMASK) + 1)
  end function gcv_nth

  ! Rebuilds the nodes along the path to i and shares everything else.
  ! An unset (nil) child becomes a fresh subtree, which is what lets
  ! conj grow into a level that does not exist yet.
  recursive function node_assoc(node, shift, i, x, roots) result(out)
    type(gc_value), intent(in) :: node, x
    integer, intent(in) :: shift, i
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, child, sub
    type(gc_value), allocatable :: r2(:)
    integer :: idx, k

    ! Root the caller's roots plus the node and value we are handed:
    ! a freshly built node is live but cannot be in the caller's list,
    ! which is the same hazard gc_obj's own argument rooting covers.
    allocate(r2(size(roots) + 2))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = node
    r2(size(roots) + 2) = x

    out = gc_vec(VBRANCH, r2)
    do k = 1, VBRANCH
       call gc_vec_set(out, k, gc_vec_get(node, k))
    end do

    if (shift == 0) then
       call gc_vec_set(out, iand(i, VMASK) + 1, x)
    else
       idx = iand(ishft(i, -shift), VMASK) + 1
       child = gc_vec_get(out, idx)
       block
         type(gc_value), allocatable :: r3(:)
         allocate(r3(size(r2) + 1))
         r3(1:size(r2)) = r2
         r3(size(r2) + 1) = out
         sub = node_assoc(child, shift - VBITS, i, x, r3)
       end block
       call gc_vec_set(out, idx, sub)
    end if
  end function node_assoc

  ! Appends x, growing the trie by a level once the current one fills.
  ! A vector of n slots, n <= VBRANCH, as ONE node and one object: the
  ! executor fills it with gcv_put as a call's arguments arrive, where
  ! n conj calls copied n nodes. Beyond VBRANCH it is the empty vector
  ! and gcv_put falls back to conj.
  ! ---- transient vectors (DEVIATIONS.md 11) ---------------------------
  !
  ! OBJ_TVECTOR: slot 1 the vector it was made from, never changed;
  ! slot 2 a buffer of what was conj'd since, a run grown by doubling;
  ! i1 how many are buffered; i2 1 while it may be edited, 0 once
  ! persistent! has made its vector. Making one is O(1) and shares the
  ! whole vector, as Clojure's does; conj! is an append into the buffer,
  ! with an allocation only when it doubles; persistent! builds the new
  ! vector's tree bottom-up, one node per 32 elements, unless what was
  ! added is small beside what was there, when it conjs the few onto
  ! the old tree and shares the rest. It replaces conj per element, which
  ! copied a path from the root (a 32-slot node per level) every time.

  function gcv_transient(v, roots) result(t)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: t
    t = gc_obj(OBJ_TVECTOR, [v, gc_nil()], [roots, v])
    call gc_set_i1(t, 0)
    call gc_set_i2(t, 1)
  end function gcv_transient

  integer function gcv_tcount(t)
    type(gc_value), intent(in) :: t
    gcv_tcount = gcv_count(gc_slot(t, 1)) + gc_i1(t)
  end function gcv_tcount

  ! Element i, 0-based; the caller checks the range.
  function gcv_tnth(t, i) result(x)
    type(gc_value), intent(in) :: t
    integer, intent(in) :: i
    type(gc_value) :: x
    integer :: cb
    cb = gcv_count(gc_slot(t, 1))
    if (i < cb) then
       x = gcv_nth(gc_slot(t, 1), i)
    else
       x = gc_vec_get(gc_slot(t, 2), i - cb + 1)
    end if
  end function gcv_tnth

  subroutine gcv_tconj(t, x, roots)
    type(gc_value), intent(in) :: t, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: buf, nb
    integer :: k, j
    k = gc_i1(t)
    buf = gc_slot(t, 2)
    if (buf%tag /= GCT_VEC) then
       nb = gc_vec(32, [roots, t, x])
       call gc_set_slot(t, 2, nb)
    else if (k >= gc_vec_len(buf)) then
       nb = gc_vec(2 * gc_vec_len(buf), [roots, t, x])
       buf = gc_slot(t, 2)
       do j = 1, k
          call gc_vec_set(nb, j, gc_vec_get(buf, j))
       end do
       call gc_set_slot(t, 2, nb)
    end if
    call gc_vec_set(gc_slot(t, 2), k + 1, x)
    call gc_set_i1(t, k + 1)
  end subroutine gcv_tconj

  ! assoc! at index i, 0-based, where 0 <= i <= count (count appends).
  subroutine gcv_tassoc(t, i, x, roots)
    type(gc_value), intent(in) :: t, x
    integer, intent(in) :: i
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nv
    integer :: cb
    cb = gcv_count(gc_slot(t, 1))
    if (i < cb) then
       nv = gcv_assoc(gc_slot(t, 1), i, x, [roots, t, x])
       call gc_set_slot(t, 1, nv)
    else if (i < cb + gc_i1(t)) then
       call gc_vec_set(gc_slot(t, 2), i - cb + 1, x)
    else
       call gcv_tconj(t, x, roots)
    end if
  end subroutine gcv_tassoc

  ! pop! of a buffered element; the caller pops the vector itself when
  ! nothing is buffered. False when nothing was buffered.
  logical function gcv_tdrop(t)
    type(gc_value), intent(in) :: t
    integer :: k
    k = gc_i1(t)
    gcv_tdrop = k > 0
    if (.not. gcv_tdrop) return
    call gc_vec_set(gc_slot(t, 2), k, gc_nil())
    call gc_set_i1(t, k - 1)
  end function gcv_tdrop

  ! persistent!: the vector, and the transient is spent.
  function gcv_persistent(t, roots) result(v)
    type(gc_value), intent(in) :: t
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, leaf, node, up
    integer :: cb, k, n, nl, m, nm, l, j, p, shift, bs
    call gc_set_i2(t, 0)
    v = gc_slot(t, 1)
    cb = gcv_count(v)
    k = gc_i1(t)
    if (k == 0) return
    n = cb + k
    bs = vs_enter(3)
    call vs_set(bs + 1, t)
    if (cb > 4 * k) then
       ! a few onto many: conj them, sharing the tree that was there
       call vs_set(bs + 2, v)
       do j = 1, k
          v = gcv_conj(vs_get(bs + 2), gc_vec_get(gc_slot(vs_get(bs + 1), 2), j), [roots, vs_get(bs + 1)])
          call vs_set(bs + 2, v)
       end do
       v = vs_get(bs + 2)
       call vs_leave(bs)
       return
    end if
    ! the leaves, then each level up, until one node is left
    nl = (n + VBRANCH - 1) / VBRANCH
    up = gc_vec(nl, [roots, vs_get(bs + 1)])
    call vs_set(bs + 2, up)
    do l = 0, nl - 1
       leaf = gc_vec(VBRANCH, [roots, vs_get(bs + 1), vs_get(bs + 2)])
       do j = 0, min(VBRANCH, n - l * VBRANCH) - 1
          call gc_vec_set(leaf, j + 1, gcv_tnth(vs_get(bs + 1), l * VBRANCH + j))
       end do
       call gc_vec_set(vs_get(bs + 2), l + 1, leaf)
    end do
    shift = 0
    m = nl
    do while (m > 1)
       nm = (m + VBRANCH - 1) / VBRANCH
       up = gc_vec(nm, [roots, vs_get(bs + 1), vs_get(bs + 2)])
       call vs_set(bs + 3, up)
       do p = 0, nm - 1
          node = gc_vec(VBRANCH, [roots, vs_get(bs + 1), vs_get(bs + 2), vs_get(bs + 3)])
          do j = 0, min(VBRANCH, m - p * VBRANCH) - 1
             call gc_vec_set(node, j + 1, gc_vec_get(vs_get(bs + 2), p * VBRANCH + j + 1))
          end do
          call gc_vec_set(vs_get(bs + 3), p + 1, node)
       end do
       call vs_set(bs + 2, vs_get(bs + 3))
       m = nm
       shift = shift + VBITS
    end do
    v = gc_obj(OBJ_VECTOR, [gc_vec_get(vs_get(bs + 2), 1)], [roots, vs_get(bs + 1), vs_get(bs + 2)])
    call gc_set_i1(v, n)
    call gc_set_i2(v, shift)
    call vs_leave(bs)
  end function gcv_persistent

  function gcv_build(n, roots) result(v)
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, node
    integer :: base
    if (n <= 0 .or. n > VBRANCH) then
       v = gcv_empty(roots)
       return
    end if
    base = vs_enter(1)
    node = gc_vec(VBRANCH, roots)
    call vs_set(base + 1, node)
    v = gc_obj(OBJ_VECTOR, [vs_get(base + 1)], [roots, vs_get(base + 1)])
    call gc_set_i1(v, n)
    call gc_set_i2(v, 0)
    call vs_leave(base)
  end function gcv_build

  ! Slot i (0-based) of a vector gcv_build made; conj when it was too
  ! big for one node (then i must be the next slot, as it is).
  function gcv_put(v, i, x, roots) result(out)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    if (i < gc_i1(v)) then
       call gc_vec_set(gc_slot(v, 1), i + 1, x)
       out = v
    else
       out = gcv_conj(v, x, roots)
    end if
  end function gcv_put

  function gcv_conj(v, x, roots) result(out)
    type(gc_value), intent(in) :: v, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, new_root, old_root
    type(gc_value), allocatable :: r2(:)
    integer :: n, shift, capacity

    if (.not. gcv_is(v)) then
       out = gc_nil()
       return
    end if

    n = gc_i1(v)
    shift = gc_i2(v)

    allocate(r2(size(roots) + 2))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = v
    r2(size(roots) + 2) = x

    capacity = ishft(1, shift + VBITS)
    if (n >= capacity) then
       ! Full: push a new level whose first child is the old root.
       old_root = gc_slot(v, 1)
       new_root = gc_vec(VBRANCH, r2)
       call gc_vec_set(new_root, 1, old_root)
       shift = shift + VBITS
       block
         type(gc_value), allocatable :: r3(:)
         allocate(r3(size(r2) + 1))
         r3(1:size(r2)) = r2
         r3(size(r2) + 1) = new_root
         new_root = node_assoc(new_root, shift, n, x, r3)
       end block
    else
       new_root = node_assoc(gc_slot(v, 1), shift, n, x, r2)
    end if

    block
      type(gc_value), allocatable :: r4(:)
      allocate(r4(size(r2) + 1))
      r4(1:size(r2)) = r2
      r4(size(r2) + 1) = new_root
      out = gc_obj(OBJ_VECTOR, [new_root], r4)
    end block
    call gc_set_i1(out, n + 1)
    call gc_set_i2(out, shift)
  end function gcv_conj

  ! Replaces element i. Out of range returns the vector unchanged,
  ! matching what the refcounted version does rather than erroring.
  function gcv_assoc(v, i, x, roots) result(out)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, new_root
    type(gc_value), allocatable :: r2(:)

    out = v
    if (.not. gcv_is(v)) return
    if (i < 0 .or. i >= gc_i1(v)) return

    allocate(r2(size(roots) + 2))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = v
    r2(size(roots) + 2) = x

    new_root = node_assoc(gc_slot(v, 1), gc_i2(v), i, x, r2)
    block
      type(gc_value), allocatable :: r3(:)
      allocate(r3(size(r2) + 1))
      r3(1:size(r2)) = r2
      r3(size(r2) + 1) = new_root
      out = gc_obj(OBJ_VECTOR, [new_root], r3)
    end block
    call gc_set_i1(out, gc_i1(v))
    call gc_set_i2(out, gc_i2(v))
  end function gcv_assoc

end module PersistentVector

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

  public :: gcv_empty, gcv_count, gcv_nth, gcv_conj, gcv_assoc, gcv_is

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

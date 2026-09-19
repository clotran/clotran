! PersistentArrayMap: the array map, over the GC heap.
!
! Shape, matching GC.f90's comment on OBJ_MAP:
!
!   map   an object: slot 1 = keys run, slot 2 = vals run, i1 = count
!
! A flat, linear-scan key/value pair, which is what real Clojure uses
! up to 8 entries before promoting to a hash trie. The promotion is
! Assoc's job, over this module and PersistentHashMap; on its own this stays
! linear at any size, which is correctness-preserving: a linear map
! answers exactly the same questions,
! just more slowly past 8 entries.
!
! Every operation is persistent: assoc and dissoc build new runs and
! leave the original untouched. Unlike the refcounted version there is
! no per-entry bookkeeping to get right -- the old runs simply become
! unreachable when nothing refers to them.
module PersistentArrayMap
  use GC
  implicit none
  private

  public :: gcm_empty, gcm_count, gcm_is, gcm_get, gcm_contains, &
       gcm_assoc, gcm_dissoc, gcm_key_at, gcm_val_at

contains

  function gcm_empty(roots) result(m)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m, keys, vals
    type(gc_value), allocatable :: r2(:)
    keys = gc_vec(0, roots)
    allocate(r2(size(roots) + 1))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = keys
    vals = gc_vec(0, r2)
    block
      type(gc_value), allocatable :: r3(:)
      allocate(r3(size(r2) + 1))
      r3(1:size(r2)) = r2
      r3(size(r2) + 1) = vals
      m = gc_obj(OBJ_MAP, [keys, vals], r3)
    end block
    call gc_set_i1(m, 0)
  end function gcm_empty

  function gcm_is(m) result(yes)
    type(gc_value), intent(in) :: m
    logical :: yes
    yes = (gc_kind(m) == OBJ_MAP)
  end function gcm_is

  function gcm_count(m) result(n)
    type(gc_value), intent(in) :: m
    integer :: n
    n = 0
    if (gcm_is(m)) n = gc_i1(m)
  end function gcm_count

  ! 1-based positional access, for callers that want to walk entries
  ! without materialising a seq (the printer and `into` both do).
  function gcm_key_at(m, i) result(k)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: k
    k = gc_nil()
    if (.not. gcm_is(m)) return
    if (i < 1 .or. i > gc_i1(m)) return
    k = gc_vec_get(gc_slot(m, 1), i)
  end function gcm_key_at

  function gcm_val_at(m, i) result(v)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: v
    v = gc_nil()
    if (.not. gcm_is(m)) return
    if (i < 1 .or. i > gc_i1(m)) return
    v = gc_vec_get(gc_slot(m, 2), i)
  end function gcm_val_at

  ! The index of k, or 0. The linear scan the type is named for.
  function index_of(m, k) result(at)
    type(gc_value), intent(in) :: m, k
    integer :: at, i
    type(gc_value) :: keys
    at = 0
    if (.not. gcm_is(m)) return
    keys = gc_slot(m, 1)
    do i = 1, gc_i1(m)
       if (gc_equal(gc_vec_get(keys, i), k)) then
          at = i
          return
       end if
    end do
  end function index_of

  function gcm_contains(m, k) result(yes)
    type(gc_value), intent(in) :: m, k
    logical :: yes
    yes = (index_of(m, k) /= 0)
  end function gcm_contains

  ! nil when absent, which is what Clojure's own (get m k) does. A
  ! caller that must tell "absent" from "present and nil" uses
  ! gcm_contains, exactly as `find` exists for that reason in Clojure.
  function gcm_get(m, k) result(v)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: v
    integer :: at
    v = gc_nil()
    at = index_of(m, k)
    if (at /= 0) v = gc_vec_get(gc_slot(m, 2), at)
  end function gcm_get

  ! Replaces in place when the key is present (same size), appends
  ! otherwise. Both build fresh runs: the original map is untouched.
  function gcm_assoc(m, k, v, roots) result(out)
    type(gc_value), intent(in) :: m, k, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys, vals, ok_, ov
    type(gc_value), allocatable :: r2(:)
    integer :: n, at

    out = gc_nil()
    if (.not. gcm_is(m)) return
    n = gc_i1(m)
    at = index_of(m, k)

    allocate(r2(size(roots) + 3))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = m
    r2(size(roots) + 2) = k
    r2(size(roots) + 3) = v

    ok_ = gc_slot(m, 1)
    ov = gc_slot(m, 2)

    if (at /= 0) then
       keys = copy_run(ok_, n, n, r2)
       vals = copy_run(ov, n, n, append_root(r2, keys))
       call gc_vec_set(vals, at, v)
    else
       keys = copy_run(ok_, n, n + 1, r2)
       call gc_vec_set(keys, n + 1, k)
       vals = copy_run(ov, n, n + 1, append_root(r2, keys))
       call gc_vec_set(vals, n + 1, v)
       n = n + 1
    end if

    block
      type(gc_value), allocatable :: r3(:)
      r3 = append_root(append_root(r2, keys), vals)
      out = gc_obj(OBJ_MAP, [keys, vals], r3)
    end block
    call gc_set_i1(out, n)
  end function gcm_assoc

  ! Removing the LAST entry into the hole left by the removed one,
  ! rather than shifting the tail down: a map is unordered, so the
  ! cheap move is the correct one. Clojure's own array map does this.
  function gcm_dissoc(m, k, roots) result(out)
    type(gc_value), intent(in) :: m, k
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys, vals
    type(gc_value), allocatable :: r2(:)
    integer :: n, at

    out = m
    if (.not. gcm_is(m)) return
    at = index_of(m, k)
    if (at == 0) return
    n = gc_i1(m)

    allocate(r2(size(roots) + 2))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = m
    r2(size(roots) + 2) = k

    keys = copy_run(gc_slot(m, 1), n, n - 1, r2)
    vals = copy_run(gc_slot(m, 2), n, n - 1, append_root(r2, keys))
    if (at /= n) then
       call gc_vec_set(keys, at, gc_vec_get(gc_slot(m, 1), n))
       call gc_vec_set(vals, at, gc_vec_get(gc_slot(m, 2), n))
    end if

    block
      type(gc_value), allocatable :: r3(:)
      r3 = append_root(append_root(r2, keys), vals)
      out = gc_obj(OBJ_MAP, [keys, vals], r3)
    end block
    call gc_set_i1(out, n - 1)
  end function gcm_dissoc

  ! --- helpers ---

  ! A fresh run of `newn`, holding the first min(oldn, newn) values of
  ! src. Allocating first and copying after is deliberate: the new run
  ! is what may trigger a collection, and src has to be rooted across
  ! it, which is why it is in the caller's root list.
  function copy_run(src, oldn, newn, roots) result(out)
    type(gc_value), intent(in) :: src
    integer, intent(in) :: oldn, newn
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: i
    out = gc_vec(newn, roots)
    do i = 1, min(oldn, newn)
       call gc_vec_set(out, i, gc_vec_get(src, i))
    end do
  end function copy_run

  function append_root(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function append_root

end module PersistentArrayMap

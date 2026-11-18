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
!
! Formally: model/arraymap.lisp -- get, assoc, dissoc either way and the
! positional edits, as the loops below run them, and their step counts.
module PersistentArrayMap
  use GC
  use iso_fortran_env, only: int64
  implicit none
  private

  ! the reads (index_of, gcm_get, gcm_key_at, gcm_val_at) and assoc's and
  ! dissoc's writes into their new runs are GENERATED:
  ! src/f/gen/arraymap_gen.inc, from model/arraymapg.lisp, included below. Its
  ! stobj is GC's pools, read through GC's hp_* accessors; this is its handle.
  type :: amg_heap
  end type amg_heap
  type(amg_heap) :: hs

  public :: gcm_empty, gcm_count, gcm_is, gcm_get, gcm_contains, &
       gcm_assoc, gcm_dissoc, gcm_key_at, gcm_val_at, &
       gcm_insert_at, gcm_replace_at, gcm_remove_at

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
  ! GENERATED: amg_at answers the place (arraymapg's amg-at-refines).
  function gcm_key_at(m, i) result(k)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: k
    k = amg_value(amg_at(hs, int(m%tag, int64), int(m%ref, int64), 0_int64, int(i, int64)))
  end function gcm_key_at

  function gcm_val_at(m, i) result(v)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: i
    type(gc_value) :: v
    v = amg_value(amg_at(hs, int(m%tag, int64), int(m%ref, int64), 1_int64, int(i, int64)))
  end function gcm_val_at

  ! the generational barrier the generated writes leave out: a new run the
  ! collector has marked old (it survived a collection the second gc_vec ran)
  ! is remembered if any word written into it is young -- gc_vec_set's
  ! per-word check, made once the words are in
  subroutine amg_barrier(r)
    type(gc_value), intent(in) :: r
    integer :: i
    do i = 1, gc_vec_len(r)
       if (.not. vec_mark(r%ref) .or. vec_rem(r%ref)) return
       call gc_reg_barrier(r, gc_vec_get(r, i))
    end do
  end subroutine amg_barrier

  ! what a generated read's place holds: 0 nil, else the arena word -p-1
  function amg_value(p) result(v)
    integer(int64), intent(in) :: p
    type(gc_value) :: v
    v = gc_nil()
    if (p /= 0) v = gc_word_at(p)
  end function amg_value

  ! the generated scan's host read (arraymapg's amg-keq): gc_equal on the run's
  ! key and k, given as their words, in index_of's order
  logical function am_keq(kt, kr, kv, wt, wr, wv)
    integer(int64), intent(in) :: kt, kr, kv, wt, wr, wv
    am_keq = gc_equal(gc_value(int(wt), int(wr), wv), gc_value(int(kt), int(kr), kv))
  end function am_keq

  ! The index of k, or 0. The linear scan the type is named for.
  ! GENERATED: amg_index (arraymapg's amg-index-refines: arraymap's am-index).
  function index_of(m, k) result(at)
    type(gc_value), intent(in) :: m, k
    integer :: at
    at = int(amg_index(hs, int(m%tag, int64), int(m%ref, int64), int(k%tag, int64), int(k%ref, int64), k%ival))
  end function index_of

  function gcm_contains(m, k) result(yes)
    type(gc_value), intent(in) :: m, k
    logical :: yes
    yes = (index_of(m, k) /= 0)
  end function gcm_contains

  ! nil when absent, which is what Clojure's own (get m k) does. A
  ! caller that must tell "absent" from "present and nil" uses
  ! gcm_contains, exactly as `find` exists for that reason in Clojure.
  ! GENERATED: amg_get (arraymapg's amg-get-refines: arraymap's am-get).
  function gcm_get(m, k) result(v)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: v
    v = amg_value(amg_get(hs, int(m%tag, int64), int(m%ref, int64), int(k%tag, int64), int(k%ref, int64), k%ival))
  end function gcm_get

  ! Replaces in place when the key is present (same size), appends
  ! otherwise. Both build fresh runs: the original map is untouched.
  ! GENERATED: the writes, amg_assoc_fill (arraymapg's amg-assoc-fill-refines:
  ! arraymap's am-assoc); the two runs allocated first, here (amg-fresh).
  function gcm_assoc(m, k, v, roots) result(out)
    type(gc_value), intent(in) :: m, k, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys, vals
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

    if (at == 0) n = n + 1
    keys = gc_vec(n, r2)
    vals = gc_vec(n, append_root(r2, keys))
    call amg_assoc_fill(hs, int(m%ref, int64), int(at, int64), int(k%tag, int64), int(k%ref, int64), k%ival, &
         int(v%tag, int64), int(v%ref, int64), v%ival, int(keys%ref, int64), int(vals%ref, int64))
    call amg_barrier(keys)
    call amg_barrier(vals)

    block
      type(gc_value), allocatable :: r3(:)
      r3 = append_root(append_root(r2, keys), vals)
      out = gc_obj(OBJ_MAP, [keys, vals], r3)
    end block
    call gc_set_i1(out, n)
  end function gcm_assoc

  ! swap: the last entry fills the hole, as a TRANSIENT's dissoc! does
  ! (TransientArrayMap.doWithout); without it the entries after the hole
  ! close it up in order, as PersistentArrayMap.without does
  function gcm_dissoc(m, k, roots, swap) result(out)
    type(gc_value), intent(in) :: m, k
    type(gc_value), intent(in) :: roots(:)
    logical, intent(in), optional :: swap
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

    keys = gc_vec(n - 1, r2)
    vals = gc_vec(n - 1, append_root(r2, keys))
    ! GENERATED: the writes, amg_dissoc_fill (arraymapg's amg-dissoc-fill-refines:
    ! arraymap's am-dissoc). Without swap the entries after the hole close it
    ! up, in order, as PersistentArrayMap.without's arraycopy does: moving the
    ! last entry into the hole changed the map's seq order (scripts/fuzz found it)
    block
      integer(int64) :: sw
      sw = 0
      if (present(swap)) then
         if (swap) sw = 1
      end if
      call amg_dissoc_fill(hs, int(m%ref, int64), int(at, int64), sw, int(keys%ref, int64), int(vals%ref, int64))
    end block
    call amg_barrier(keys)
    call amg_barrier(vals)

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
  ! The three POSITIONAL edits a sorted map needs (Assoc.f90): the
  ! order of the entries is kept, where assoc appends and dissoc moves
  ! the last entry into the hole.
  function gcm_insert_at(m, at, k, v, roots) result(out)
    type(gc_value), intent(in) :: m, k, v
    integer, intent(in) :: at
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys, vals
    type(gc_value), allocatable :: r2(:)
    integer :: n, i
    out = gc_nil()
    if (.not. gcm_is(m)) return
    n = gc_i1(m)
    r2 = append_root(append_root(append_root(roots, m), k), v)
    keys = gc_vec(n + 1, r2)
    r2 = append_root(r2, keys)
    vals = gc_vec(n + 1, r2)
    r2 = append_root(r2, vals)
    do i = 1, at - 1
       call gc_vec_set(keys, i, gc_vec_get(gc_slot(m, 1), i))
       call gc_vec_set(vals, i, gc_vec_get(gc_slot(m, 2), i))
    end do
    call gc_vec_set(keys, at, k)
    call gc_vec_set(vals, at, v)
    do i = at, n
       call gc_vec_set(keys, i + 1, gc_vec_get(gc_slot(m, 1), i))
       call gc_vec_set(vals, i + 1, gc_vec_get(gc_slot(m, 2), i))
    end do
    out = gc_obj(OBJ_MAP, [keys, vals], r2)
    call gc_set_i1(out, n + 1)
  end function gcm_insert_at

  function gcm_replace_at(m, at, v, roots) result(out)
    type(gc_value), intent(in) :: m, v
    integer, intent(in) :: at
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys, vals
    type(gc_value), allocatable :: r2(:)
    integer :: n
    out = gc_nil()
    if (.not. gcm_is(m)) return
    n = gc_i1(m)
    r2 = append_root(append_root(roots, m), v)
    keys = copy_run(gc_slot(m, 1), n, n, r2)
    r2 = append_root(r2, keys)
    vals = copy_run(gc_slot(m, 2), n, n, r2)
    r2 = append_root(r2, vals)
    call gc_vec_set(vals, at, v)
    out = gc_obj(OBJ_MAP, [keys, vals], r2)
    call gc_set_i1(out, n)
  end function gcm_replace_at

  function gcm_remove_at(m, at, roots) result(out)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: at
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys, vals
    type(gc_value), allocatable :: r2(:)
    integer :: n, i, j
    out = gc_nil()
    if (.not. gcm_is(m)) return
    n = gc_i1(m)
    r2 = append_root(roots, m)
    keys = gc_vec(n - 1, r2)
    r2 = append_root(r2, keys)
    vals = gc_vec(n - 1, r2)
    r2 = append_root(r2, vals)
    j = 0
    do i = 1, n
       if (i == at) cycle
       j = j + 1
       call gc_vec_set(keys, j, gc_vec_get(gc_slot(m, 1), i))
       call gc_vec_set(vals, j, gc_vec_get(gc_slot(m, 2), i))
    end do
    out = gc_obj(OBJ_MAP, [keys, vals], r2)
    call gc_set_i1(out, n - 1)
  end function gcm_remove_at

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

  include "gen/arraymap_gen.inc"

end module PersistentArrayMap

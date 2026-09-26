! CompiledFn: the registry of procedures a compiled namespace installs,
! and the one signature they all have.
!
! WHY A REGISTRY AND NOT A POINTER IN THE VALUE. A `gc_value` is four
! scalars and deliberately has no pointer component -- that is what
! makes copying one cost 4 ns instead of 497 (PLAN, "the value type has
! no FINAL"). So a compiled function object keeps an INDEX here in its
! i1, exactly as a native array keeps a handle, and the procedure
! pointer lives in this table. The collector never sees a pointer and
! nothing about the heap changes.
!
! WHY THIS MODULE SITS SO LOW. `apply` in Eval has to reach a compiled
! procedure, and ClotranABI has to put one in the table -- but
! ClotranABI already uses Eval, so the table cannot live there without a
! cycle. It has no dependency of its own beyond iso_c_binding.
!
! THE CALLING CONVENTION, and it is the whole interface between
! generated code and the runtime:
!
!   subroutine f(argbase, nargs, dst) bind(C)
!
! The caller has already written the arguments into CONSECUTIVE shadow
! stack slots argbase+1 .. argbase+nargs, and the procedure writes its
! answer into slot dst. Nothing is passed by value, so nothing can be
! held in a register across an allocation, and a call costs no vector
! allocation -- which is the whole point of not passing an args vector.
!
! An entry is never removed. A recompiled namespace registers a NEW
! procedure and the Var is repointed at it; the old library stays open
! and its table entry stays valid, because a value somewhere may still
! name it and closing it would crash (PLAN step 10, "a recompile LEAKS
! the old shared library, on purpose").
module CompiledFn
  use iso_c_binding
  use GC
  use PersistentVector
  implicit none
  private
  public :: compiled_i, cf_register, cf_call, cf_count, cf_name, cf_valid
  public :: cf_pool_add, cf_pool_get

  abstract interface
     subroutine compiled_i(argbase, nargs, dst) bind(C)
       import :: c_int
       integer(c_int), value :: argbase, nargs, dst
     end subroutine compiled_i
  end interface

  ! A c_funptr rather than a procedure pointer, and c_f_procpointer at
  ! the call, which is what DynLoad does for a package's shims. It is
  ! the shape that works the same whether the procedure came from a
  ! dlopened library or was linked in.
  type :: cf_entry
     type(c_funptr) :: fp = c_null_funptr
     character(len=:), allocatable :: name
  end type cf_entry

  type(cf_entry), allocatable, save :: tbl(:)
  integer, save :: used = 0

  ! THE CONSTANT POOLS, one vector per compiled namespace, held in a
  ! global root because nothing else refers to them. A generated
  ! procedure cannot spell a map, a Var or a folded function in
  ! Fortran, so the driver puts them here and the procedure indexes
  ! by a handle it is told at install time.
  type(gc_root), save :: pool_root

  ! Each pool as a flat array, filled at its first read: a compiled
  ! procedure reads its constants on every call, and two persistent-
  ! vector walks an entry was half the cost of its prologue. The values
  ! stay alive through the pool vector (a global root) and never move,
  ! so a copy stays good -- for this heap: gc_init starts another.
  type :: flat_pool
     type(gc_value), allocatable :: e(:)
     integer :: gen = -1
  end type flat_pool
  type(flat_pool), allocatable, save :: flat(:)

contains

  ! Adds a procedure and answers its handle, 1-based. The name is for
  ! printing and for a stack trace; nothing dispatches on it.
  function cf_register(fp, name) result(h)
    type(c_funptr), intent(in) :: fp
    character(len=*), intent(in) :: name
    integer :: h
    type(cf_entry), allocatable :: bigger(:)
    ! every compiled call reads tbl without a lock: it grows with the
    ! world stopped, and an entry is claimed under the state lock
    do
       call gc_state_lock()
       if (.not. allocated(tbl)) then
          allocate(tbl(16))
          used = 0
       end if
       if (used < size(tbl)) exit
       call gc_state_unlock()
       call gc_grow_begin()
       if (used >= size(tbl)) then
          allocate(bigger(2 * size(tbl)))
          bigger(1:used) = tbl(1:used)
          call move_alloc(bigger, tbl)
       end if
       call gc_grow_end()
    end do
    used = used + 1
    tbl(used)%fp = fp
    tbl(used)%name = name
    h = used
    call gc_state_unlock()
  end function cf_register

  logical function cf_valid(h)
    integer, intent(in) :: h
    cf_valid = .false.
    if (.not. allocated(tbl)) return
    if (h < 1 .or. h > used) return
    cf_valid = c_associated(tbl(h)%fp)
  end function cf_valid

  subroutine cf_call(h, argbase, nargs, dst)
    integer, intent(in) :: h, argbase, nargs, dst
    procedure(compiled_i), pointer :: f
    if (.not. cf_valid(h)) return
    call c_f_procpointer(tbl(h)%fp, f)
    call f(int(argbase, c_int), int(nargs, c_int), int(dst, c_int))
  end subroutine cf_call

  ! Adds a pool and answers its handle, 1-based.
  function cf_pool_add(v) result(h)
    type(gc_value), intent(in) :: v
    integer :: h, base
    type(gc_value) :: pools
    base = vs_enter(2)
    call vs_set(base + 1, v)
    pools = gc_root_get(pool_root)
    if (.not. gcv_is(pools)) pools = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 2, pools)
    pools = gcv_conj(vs_get(base + 2), vs_get(base + 1), &
         [vs_get(base + 1), vs_get(base + 2)])
    call gc_global_keep(pool_root, pools)
    h = gcv_count(pools)
    call vs_leave(base)
    ! flatten it now, at install, not at a first read racing another
    block
      type(gc_value) :: first
      first = cf_pool_get(h, 0)
    end block
  end function cf_pool_add

  ! Entry i of pool h, both counted the way their callers count:
  ! the handle from one, the index from zero.
  function cf_pool_get(h, i) result(v)
    integer, intent(in) :: h, i
    type(gc_value) :: v, pools, p
    type(flat_pool), allocatable :: bigger(:)
    integer :: k, n
    v = gc_nil()
    if (h < 1) return
    if (allocated(flat)) then
       if (h <= size(flat)) then
          if (flat(h)%gen == gc_generation()) then
             if (i >= 0 .and. i < size(flat(h)%e)) v = flat(h)%e(i + 1)
             return
          end if
       end if
    end if
    ! the first read of pool h in this heap: flatten it. Readers index
    ! flat without a lock, so every write to it -- the table growing, a
    ! pool filled -- is made with the world stopped; a second thread that
    ! wanted the same pool finds it done.
    pools = gc_root_get(pool_root)
    if (.not. gcv_is(pools)) return
    if (h > gcv_count(pools)) return
    call gc_grow_begin()
    if (.not. allocated(flat)) allocate(flat(max(16, h)))
    if (h > size(flat)) then
       allocate(bigger(max(2 * size(flat), h)))
       do k = 1, size(flat)
          if (allocated(flat(k)%e)) call move_alloc(flat(k)%e, bigger(k)%e)
          bigger(k)%gen = flat(k)%gen
       end do
       call move_alloc(bigger, flat)
    end if
    if (flat(h)%gen /= gc_generation()) then
       p = gcv_nth(pools, h - 1)
       n = gcv_count(p)
       if (allocated(flat(h)%e)) deallocate(flat(h)%e)
       allocate(flat(h)%e(n))
       do k = 1, n
          flat(h)%e(k) = gcv_nth(p, k - 1)
       end do
       flat(h)%gen = gc_generation()
    end if
    if (i >= 0 .and. i < size(flat(h)%e)) v = flat(h)%e(i + 1)
    call gc_grow_end()
  end function cf_pool_get

  subroutine cf_name(h, s)
    integer, intent(in) :: h
    character(len=:), allocatable, intent(out) :: s
    s = ""
    if (.not. allocated(tbl)) return
    if (h < 1 .or. h > used) return
    if (allocated(tbl(h)%name)) s = tbl(h)%name
  end subroutine cf_name

  function cf_count() result(k)
    integer :: k
    k = used
  end function cf_count

end module CompiledFn

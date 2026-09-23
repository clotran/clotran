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
  implicit none
  private
  public :: compiled_i, cf_register, cf_call, cf_count, cf_name, cf_valid

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

contains

  ! Adds a procedure and answers its handle, 1-based. The name is for
  ! printing and for a stack trace; nothing dispatches on it.
  function cf_register(fp, name) result(h)
    type(c_funptr), intent(in) :: fp
    character(len=*), intent(in) :: name
    integer :: h
    type(cf_entry), allocatable :: bigger(:)
    if (.not. allocated(tbl)) then
       allocate(tbl(16))
       used = 0
    end if
    if (used >= size(tbl)) then
       allocate(bigger(2 * size(tbl)))
       bigger(1:used) = tbl(1:used)
       call move_alloc(bigger, tbl)
    end if
    used = used + 1
    tbl(used)%fp = fp
    tbl(used)%name = name
    h = used
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

  function cf_name(h) result(s)
    integer, intent(in) :: h
    character(len=:), allocatable :: s
    s = ""
    if (.not. allocated(tbl)) return
    if (h < 1 .or. h > used) return
    if (allocated(tbl(h)%name)) s = tbl(h)%name
  end function cf_name

  function cf_count() result(k)
    integer :: k
    k = used
  end function cf_count

end module CompiledFn

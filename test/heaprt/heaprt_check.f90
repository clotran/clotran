! The GENERATED value stack and global roots (src/f/gen/heaprt_gen.inc, written by
! scripts/acl2-fortran -b heaprtg from model/heaprtg.lisp) run on
! scripts/fuzz-heaprt-gen's cases: GC.f90's gc_value and gc_stack, cut to
! what the operations read, around the included file.
!
!   heaprt_check CASE-FILE [broken]
!
! A case: "L n" (the stack's slots, the operations), then n lines "op a b c":
! 0 enter a, 1 leave to a, 2 set slot a to b (0 is nil), 3 get slot a,
! 4 reset; on the global roots 5 claim one holding a, 6 keep handle (a . b)
! holding c, 7 get (a . b), 8 live (a . b), 9 set root a to b, 10 root a,
! 11 a new heap. After each: "r r2 top hi", every slot (0 nil, else its
! integer), the generation, the count, the table's size and every root.
! broken is the negative control: a leave below the top leaves one slot
! too many on the stack, and a set by index writes the root after.
module hrt
  use iso_fortran_env, only: int64
  implicit none
  integer, parameter :: GCT_NIL = 0, GCT_INT = 2
  type :: gc_value
     integer :: tag = GCT_NIL
     integer :: ref = 0
     integer(int64) :: ival = 0
  end type gc_value
  type(gc_value), parameter :: nilv = gc_value()
  type :: gc_stack
     integer :: vs_hi = 0
     integer :: vs_top = 0
     type(gc_value), pointer, contiguous :: slots0(:) => null()
  end type gc_stack
  type :: gc_globals
     integer(int64) :: gen = 0, count = 0
     type(gc_value), allocatable :: tbl(:)
  end type gc_globals
contains
  subroutine rt_resize_val(a, n)
    type(gc_value), allocatable, intent(inout) :: a(:)
    integer(int64), intent(in) :: n
    type(gc_value), allocatable :: b(:)
    integer(int64) :: k
    allocate(b(0:n - 1))
    b = nilv
    k = 0
    if (allocated(a)) k = min(n, size(a, kind=int64))
    if (k > 0) b(0:k - 1) = a(0:k - 1)
    call move_alloc(b, a)
  end subroutine rt_resize_val

  integer(int64) function vint(v)
    type(gc_value), intent(in) :: v
    vint = merge(v%ival, 0_int64, v%tag /= GCT_NIL)
  end function vint

  type(gc_value) function ival(b)
    integer(int64), intent(in) :: b
    ival = nilv
    if (b /= 0) ival = gc_value(GCT_INT, 0, b)
  end function ival

  pure function rt_nil() result(v)
    type(gc_value) :: v
    v = nilv
  end function rt_nil

  include "heaprt_gen.inc"
end module hrt

program heaprt_check
  use hrt
  implicit none
  type(gc_stack), target :: st
  type(gc_globals) :: gr
  character(len=512) :: path, mode
  integer :: u, l, n, i, j, op
  integer(int64) :: a, b, c, r, r2
  call get_command_argument(1, path)
  call get_command_argument(2, mode)
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) l, n
  allocate(st%slots0(0:l - 1))
  st%slots0 = nilv
  allocate(gr%tbl(0:-1))
  do i = 1, n
     read(u, *) op, a, b, c
     r = 0
     r2 = 0
     select case (op)
     case (0)
        call vsg_enter(st, a, r)
     case (1)
        if (mode == "broken" .and. a >= 0 .and. a < st%vs_top) a = a + 1
        call vsg_leave(st, a)
     case (2)
        call vsg_set(st, a, ival(b))
     case (3)
        r = vint(vsg_get(st, a))
     case (4)
        call vsg_reset(st)
     case (5)
        call glg_new(gr, ival(a), r)
     case (6)
        call glg_keep(gr, a, b, ival(c), r, r2)
     case (7)
        r = vint(glg_get(gr, a, b))
     case (8)
        r = merge(1, 0, glg_live(gr, a, b))
     case (9)
        if (mode == "broken") a = a + 1
        call glg_set(gr, a, ival(b))
     case (10)
        r = vint(glg_at(gr, a))
     case default
        call glg_init(gr)
     end select
     write(*, '(i0, 3(1x, i0))', advance="no") r, r2, st%vs_top, st%vs_hi
     do j = 0, l - 1
        write(*, '(1x, i0)', advance="no") vint(st%slots0(j))
     end do
     write(*, '(3(1x, i0))', advance="no") gr%gen, gr%count, size(gr%tbl)
     do j = 0, size(gr%tbl) - 1
        write(*, '(1x, i0)', advance="no") vint(gr%tbl(j))
     end do
     write(*, *)
  end do
end program heaprt_check

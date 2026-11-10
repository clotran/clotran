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
! 11 a new heap; 12 push the stack, 13 push the global roots (r the
! pushes, r2 the checksum sum of k (1000 tag + ref) over the k-th).
! After each: "r r2 top hi", every slot (0 nil, else its integer), the generation, the count, the table's size and every root.
! broken is the negative control: a leave below the top leaves one slot
! too many on the stack, a set by index writes the root after, and a
! stack's push starts at its second slot.
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
     type(gc_value) :: spare0(0:255)
     integer :: nspare0(0:31) = 0
  end type gc_stack
  type :: gc_globals
     integer(int64) :: gen = 0, count = 0
     type(gc_value), allocatable :: tbl(:)
  end type gc_globals
  ! the marker, cut to a record of what was pushed
  type :: heap_state
     integer(int64) :: n = 0, sum = 0
  end type heap_state
  ! the pools, cut to six runs and an arena of 40 words, for the spare frames
  integer(int64) :: vlen(0:6) = 0, voff(0:6) = 0
  integer(int64) :: atag(0:39), aref(0:39), aival(0:39)
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
    if (b /= 0) ival = gc_value(GCT_INT, int(b), b)
  end function ival

  pure function rt_nil() result(v)
    type(gc_value) :: v
    v = nilv
  end function rt_nil

  subroutine hpg_push(hs, tag, ref)
    type(heap_state), intent(inout) :: hs
    integer(int64), value :: tag, ref
    hs%n = hs%n + 1
    hs%sum = hs%sum + hs%n * (1000 * tag + ref)
  end subroutine hpg_push

  pure integer(int64) function gv_tag(v)
    type(gc_value), intent(in) :: v
    gv_tag = int(v%tag, int64)
  end function gv_tag
  pure integer(int64) function gv_ref(v)
    type(gc_value), intent(in) :: v
    gv_ref = int(v%ref, int64)
  end function gv_ref

  integer(int64) function hp_vlen(i)
    integer(int64), intent(in) :: i
    hp_vlen = vlen(i)
  end function hp_vlen
  integer(int64) function hp_voff(i)
    integer(int64), intent(in) :: i
    hp_voff = voff(i)
  end function hp_voff
  subroutine hp_set_atag(j, x)
    integer(int64), intent(in) :: j, x
    atag(j) = x
  end subroutine hp_set_atag
  subroutine hp_set_aref(j, x)
    integer(int64), intent(in) :: j, x
    aref(j) = x
  end subroutine hp_set_aref
  subroutine hp_set_aival(j, x)
    integer(int64), intent(in) :: j, x
    aival(j) = x
  end subroutine hp_set_aival

  include "heaprt_gen.inc"

  ! a spare-frame case: "-1 n", the six runs' "off len", then n lines
  ! "op a 0 0": 14 give run a (0: an integer), 15 take size a, 16 reset.
  ! After each: "r r2" (a take's value and tag), the 32 counts, a checksum
  ! of the spares, the arena's 40 tags and a checksum of its refs and ivals.
  ! broken: a give leaves its run's last word as it was.
  subroutine spare_case(u, n, broken)
    integer, intent(in) :: u, n
    logical, intent(in) :: broken
    type(gc_stack) :: st
    type(heap_state) :: hs
    type(gc_value) :: v
    integer :: i, op
    integer(int64) :: a, b, c, r, r2, j, k, last
    read(u, *) (voff(j), vlen(j), j = 1, 6)
    do j = 0, 39
       atag(j) = j + 1; aref(j) = 100 + j; aival(j) = 200 + j
    end do
    do i = 1, n
       read(u, *) op, a, b, c
       r = 0; r2 = 0
       select case (op)
       case (14)
          v = gc_value(2, 7, 7)
          if (a > 0) v = gc_value(9, int(a), a)
          last = -1
          if (a > 0 .and. vlen(a) > 0) last = voff(a) + vlen(a) - 1
          call spg_give(st, hs, v)
          if (broken .and. last >= 0) then
             if (atag(last) == 0) atag(last) = last + 1
          end if
       case (15)
          call spg_take(st, a, v)
          r = vint(v); r2 = v%tag
       case default
          call spg_reset(st, 0_int64)
       end select
       k = 0
       do j = 0, 255
          k = k + (j + 1) * vint(st%spare0(j))
       end do
       write(*, '(i0, 1x, i0)', advance="no") r, r2
       do j = 0, 31
          write(*, '(1x, i0)', advance="no") st%nspare0(j)
       end do
       write(*, '(1x, i0)', advance="no") k
       do j = 0, 39
          write(*, '(1x, i0)', advance="no") atag(j)
       end do
       k = 0
       do j = 0, 39
          k = k + (j + 1) * (aref(j) + 1000 * aival(j))
       end do
       write(*, '(1x, i0)') k
    end do
  end subroutine spare_case
end module hrt

program heaprt_check
  use hrt
  implicit none
  type(gc_stack), target :: st
  type(gc_globals) :: gr
  type(heap_state) :: hs
  character(len=512) :: path, mode
  integer :: u, l, n, i, j, op
  integer(int64) :: a, b, c, r, r2
  call get_command_argument(1, path)
  call get_command_argument(2, mode)
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) l, n
  if (l == -1) then
     call spare_case(u, n, mode == "broken")
     stop
  end if
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
     case (11)
        call glg_init(gr)
     case (12)
        hs = heap_state()
        call vsg_push(st, hs, merge(1_int64, 0_int64, mode == "broken"))
        r = hs%n
        r2 = hs%sum
     case default
        hs = heap_state()
        call glg_push(gr, hs, 0_int64)
        r = hs%n
        r2 = hs%sum
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

! The generated collector's marking (src/f/gen/heap_gen.inc, from
! model/heapg.lisp) on a heap read from a file: scripts/fuzz-heap-gen's
! case, the same one ACL2's hpg-drain marks. Prints the marks and counts.
! With a second argument "broken", the negative control: an object's last
! slot reads as no reference.
module heap_check_m
  use iso_fortran_env, only: int64
  implicit none
  type :: heap_state
     integer(int64) :: err = 0, msp = 0, nobj = 0, nvec = 0, nstr = 0, alive = 0
     integer(int64), allocatable :: mtag(:), mref(:)
  end type heap_state
  integer(int64), allocatable :: otag(:), oref(:), omark(:), voff(:), vlen(:), vmark(:), atag(:), aref(:), smark(:)
  logical :: broken = .false.
contains
  integer(int64) function hp_otag(j)
    integer(int64), intent(in) :: j
    hp_otag = otag(j)
  end function hp_otag
  integer(int64) function hp_oref(j)
    integer(int64), intent(in) :: j
    hp_oref = oref(j)
    if (broken .and. mod(j, 5_int64) == 4) hp_oref = 0
  end function hp_oref
  integer(int64) function hp_n_oslot()
    hp_n_oslot = size(otag, kind=int64)
  end function hp_n_oslot
  integer(int64) function hp_omark(i)
    integer(int64), intent(in) :: i
    hp_omark = omark(i)
  end function hp_omark
  subroutine hp_set_omark(i, x)
    integer(int64), intent(in) :: i, x
    omark(i) = x
  end subroutine hp_set_omark
  integer(int64) function hp_n_obj()
    hp_n_obj = size(omark, kind=int64)
  end function hp_n_obj
  integer(int64) function hp_voff(i)
    integer(int64), intent(in) :: i
    hp_voff = voff(i)
  end function hp_voff
  integer(int64) function hp_vlen(i)
    integer(int64), intent(in) :: i
    hp_vlen = vlen(i)
  end function hp_vlen
  integer(int64) function hp_vmark(i)
    integer(int64), intent(in) :: i
    hp_vmark = vmark(i)
  end function hp_vmark
  subroutine hp_set_vmark(i, x)
    integer(int64), intent(in) :: i, x
    vmark(i) = x
  end subroutine hp_set_vmark
  integer(int64) function hp_n_vec()
    hp_n_vec = min(size(voff, kind=int64), size(vlen, kind=int64), size(vmark, kind=int64))
  end function hp_n_vec
  integer(int64) function hp_atag(j)
    integer(int64), intent(in) :: j
    hp_atag = atag(j)
  end function hp_atag
  integer(int64) function hp_aref(j)
    integer(int64), intent(in) :: j
    hp_aref = aref(j)
  end function hp_aref
  integer(int64) function hp_n_arena()
    hp_n_arena = size(atag, kind=int64)
  end function hp_n_arena
  integer(int64) function hp_smark(i)
    integer(int64), intent(in) :: i
    hp_smark = smark(i)
  end function hp_smark
  subroutine hp_set_smark(i, x)
    integer(int64), intent(in) :: i, x
    smark(i) = x
  end subroutine hp_set_smark
  integer(int64) function hp_n_str()
    hp_n_str = size(smark, kind=int64)
  end function hp_n_str

  include "heap_gen.inc"
end module heap_check_m

program heap_check
  use heap_check_m
  implicit none
  type(heap_state) :: hs
  integer :: u, i, nr
  integer(int64) :: no, nv, na, ns, cap, t, r
  character(len=256) :: path, arg2
  call get_command_argument(1, path)
  call get_command_argument(2, arg2)
  broken = trim(arg2) == "broken"
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) no, nv, na, ns, cap
  allocate(otag(0:5 * no - 1), oref(0:5 * no - 1), omark(0:no - 1))
  allocate(voff(0:nv - 1), vlen(0:nv - 1), vmark(0:nv - 1), atag(0:na - 1), aref(0:na - 1), smark(0:ns - 1))
  allocate(hs%mtag(0:cap - 1), hs%mref(0:cap - 1))
  read(u, *) otag
  read(u, *) oref
  read(u, *) omark
  if (nv > 0) read(u, *) voff
  if (nv > 0) read(u, *) vlen
  if (nv > 0) read(u, *) vmark
  if (na > 0) read(u, *) atag
  if (na > 0) read(u, *) aref
  if (ns > 0) read(u, *) smark
  read(u, *) nr
  do i = 1, nr
     read(u, *) t, r
     call hpg_push(hs, t, r)
  end do
  close(u)
  call hpg_drain(hs, 1000000_int64)
  write(*, '(a, *(1x, i0))') 'omark', omark
  write(*, '(a, *(1x, i0))') 'vmark', vmark
  write(*, '(a, *(1x, i0))') 'smark', smark
  write(*, '(a, 6(1x, i0))') 'regs', hs%err, hs%msp, hs%nobj, hs%nvec, hs%nstr, hs%alive
end program heap_check

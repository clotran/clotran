! The generated VM runtime reads (src/f/gen/vmrt_gen.inc, from
! model/vmrt.lisp) on a heap read from a file: scripts/fuzz-vmrt-gen's case,
! the same one ACL2 answers. Prints, a line a query, every read's answer.
! With a second argument "broken", the negative control: a closure's kind
! reads as a builtin's and a list's count one more.
module vmrt_check_m
  use iso_fortran_env, only: int64
  implicit none
  type :: vrt_heap
  end type vrt_heap
  type :: vrt_aux
  end type vrt_aux
  type(vrt_heap) :: hs
  type(vrt_aux) :: vx
  integer(int64), allocatable :: otag(:), oref(:), oival(:), okind(:), oi1(:), oi2(:)
  integer(int64), allocatable :: voff(:), vlen(:), atag(:), aref(:), aival(:)
  logical :: broken = .false.
contains
  pure integer(int64) function hp_otag(j)
    integer(int64), intent(in) :: j
    hp_otag = otag(j)
  end function hp_otag
  pure integer(int64) function hp_oref(j)
    integer(int64), intent(in) :: j
    hp_oref = oref(j)
  end function hp_oref
  pure integer(int64) function hp_oival(j)
    integer(int64), intent(in) :: j
    hp_oival = oival(j)
  end function hp_oival
  pure integer(int64) function hp_n_oslot()
    hp_n_oslot = size(otag, kind=int64)
  end function hp_n_oslot
  pure integer(int64) function hp_okind(i)
    integer(int64), intent(in) :: i
    hp_okind = okind(i)
    if (broken .and. hp_okind == 4) hp_okind = 13
  end function hp_okind
  pure integer(int64) function hp_oi1(i)
    integer(int64), intent(in) :: i
    hp_oi1 = oi1(i)
    if (broken) hp_oi1 = hp_oi1 + 1
  end function hp_oi1
  pure integer(int64) function hp_oi2(i)
    integer(int64), intent(in) :: i
    hp_oi2 = oi2(i)
  end function hp_oi2
  pure integer(int64) function hp_n_obj()
    hp_n_obj = size(okind, kind=int64)
  end function hp_n_obj
  pure integer(int64) function hp_voff(i)
    integer(int64), intent(in) :: i
    hp_voff = voff(i)
  end function hp_voff
  pure integer(int64) function hp_vlen(i)
    integer(int64), intent(in) :: i
    hp_vlen = vlen(i)
  end function hp_vlen
  pure integer(int64) function hp_n_vec()
    hp_n_vec = size(voff, kind=int64)
  end function hp_n_vec
  pure integer(int64) function hp_atag(j)
    integer(int64), intent(in) :: j
    hp_atag = atag(j)
  end function hp_atag
  pure integer(int64) function hp_aival(j)
    integer(int64), intent(in) :: j
    hp_aival = aival(j)
  end function hp_aival
  pure integer(int64) function hp_n_arena()
    hp_n_arena = size(atag, kind=int64)
  end function hp_n_arena

  include "vmrt_gen.inc"
end module vmrt_check_m

program vmrt_check
  use iso_fortran_env, only: int64
  use vmrt_check_m
  implicit none
  character(len=4096) :: path, flag
  integer :: u, no, nv, na, nq, k
  integer(int64) :: hd(4), q(9), t, r, iv, tb, ib, i, rb, nn, ln
  call get_command_argument(1, path)
  call get_command_argument(2, flag)
  broken = (trim(flag) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) no, nv, na
  allocate(otag(0:5*no-1), oref(0:5*no-1), oival(0:5*no-1), okind(0:no-1), oi1(0:no-1), oi2(0:no-1))
  allocate(voff(0:nv-1), vlen(0:nv-1), atag(0:na-1), aref(0:na-1), aival(0:na-1))
  read(u, *) otag
  read(u, *) oref
  read(u, *) oival
  read(u, *) okind
  read(u, *) oi1
  read(u, *) oi2
  read(u, *) voff
  read(u, *) vlen
  read(u, *) atag
  read(u, *) aref
  read(u, *) aival
  read(u, *) hd
  read(u, *) nq
  do k = 1, nq
     read(u, *) q
     t = q(1); r = q(2); iv = q(3); tb = q(4); ib = q(5); i = q(6); rb = q(7); nn = q(8); ln = q(9)
     print '(*(i0,1x))', b(vrt_truthy(t, iv)), vrt_nat(t, iv), b(vrt_lt(t, iv, tb, ib)), vrt_add(t, iv, tb, ib), &
          vrt_len(hs, t, r), b(vrt_consp(hs, t, r)), vrt_car_place(hs, t, r), vrt_cdr_place(hs, t, r), &
          b(vrt_throwp(hs, t, r, hd(1), hd(2))), vrt_thrown_place(hs, t, r), &
          b(vrt_clop(hs, vx, t, r, hd(3), hd(4))), vrt_clo_f(hs, vx, t, r), &
          vrt_capt_place(hs, vx, i, t, r), vrt_cfid(hs, vx, t, r), vrt_cncap(hs, vx, t, r), &
          vrt_prim_kind(hs, t, r, 1_int64, 2_int64, 3_int64, 4_int64, 5_int64, 6_int64), &
          vrt_arg_slot(nn, t, iv, rb, ln)
  end do
contains
  integer function b(x)
    logical, intent(in) :: x
    b = merge(1, 0, x)
  end function b
end program vmrt_check

! anpass_check: runs the GENERATED analyzer passes (anpass_gen.inc, from
! model/anpass.lisp) on trees read from a file, through mock ast_* reads
! that answer what model/anpass.lisp's ast-* answer of the same tree.
! scripts/fuzz-anpass-gen writes the trees and compares the answers with
! ACL2's. With the argument `broken`, the reads are wrong on purpose (a
! local's slot one more, a recur's target flipped): the negative control.
!
!   anpass_check CASEFILE [broken]
!
! CASEFILE: n lvlen mklen nnodes root, then a line a node, 1..nnodes:
!   kind i2 rfn s3 nk kid.. nc cap.. na alt..
! (0 is nil). Out: "err nmk id..." then "tc0 tc1 tc2 tc3 hfr".
module anpass_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
  end type gc_value
  type :: anp_state
     integer(int64), allocatable :: lv(:)
     type(gc_value), allocatable :: mk(:)
     integer(int64) :: nmk = 0, err = 0
  end type anp_state
  integer, allocatable :: nkind(:), ni2(:), nrfn(:), ns3(:), kidoff(:), nk(:), capoff(:), nc(:), altoff(:), na(:)
  integer, allocatable :: kids(:), caps(:), alts(:)
  logical :: broken = .false.
contains
  logical function ok(nd)
    type(gc_value), intent(in) :: nd
    ok = nd%id >= 1 .and. nd%id <= size(nkind)
  end function ok

  integer(int64) function ast_kind(nd)
    type(gc_value), intent(in) :: nd
    ast_kind = 0
    if (ok(nd)) ast_kind = nkind(nd%id)
  end function ast_kind

  integer(int64) function ast_i2(nd)
    type(gc_value), intent(in) :: nd
    ast_i2 = 0
    if (ok(nd)) ast_i2 = ni2(nd%id)
    if (broken .and. ok(nd)) then
       if (nkind(nd%id) == 2) ast_i2 = ast_i2 + 1
    end if
  end function ast_i2

  integer(int64) function ast_rfn(nd)
    type(gc_value), intent(in) :: nd
    ast_rfn = 0
    if (ok(nd)) ast_rfn = nrfn(nd%id)
    if (broken .and. ok(nd)) ast_rfn = 1 - min(1_int64, abs(ast_rfn))
  end function ast_rfn

  integer(int64) function ast_nkids(nd)
    type(gc_value), intent(in) :: nd
    ast_nkids = 0
    if (ok(nd)) ast_nkids = nk(nd%id)
  end function ast_nkids

  function ast_kid(nd, i) result(k)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    type(gc_value) :: k
    k%id = 0
    if (ok(nd)) then
       if (i >= 0 .and. i < nk(nd%id)) k%id = kids(kidoff(nd%id) + i)
    end if
  end function ast_kid

  function ast_s3(nd) result(k)
    type(gc_value), intent(in) :: nd
    type(gc_value) :: k
    k%id = 0
    if (ok(nd)) k%id = ns3(nd%id)
  end function ast_s3

  integer(int64) function ast_ncaps(nd)
    type(gc_value), intent(in) :: nd
    ast_ncaps = 0
    if (ok(nd)) ast_ncaps = nc(nd%id)
  end function ast_ncaps

  integer(int64) function ast_cap(nd, i)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    ast_cap = 0
    if (ok(nd)) then
       if (i >= 0 .and. i < nc(nd%id)) ast_cap = caps(capoff(nd%id) + i)
    end if
  end function ast_cap

  integer(int64) function ast_nalts(nd)
    type(gc_value), intent(in) :: nd
    ast_nalts = 0
    if (ok(nd)) ast_nalts = na(nd%id)
  end function ast_nalts

  function ast_alt(nd, i) result(k)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    type(gc_value) :: k
    k%id = 0
    if (ok(nd)) then
       if (i >= 0 .and. i < na(nd%id)) k%id = alts(altoff(nd%id) + i)
    end if
  end function ast_alt

  include "anpass_gen.inc"
end module anpass_mock

program anpass_check
  use iso_fortran_env, only: int64
  use anpass_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, n, lvlen, mklen, nn, root, i, j, kd, a, b, c, s3, cnt, vals(4096)
  integer :: tk, tc, ta
  type(anp_state) :: ps
  type(gc_value) :: r
  integer(int64) :: t(0:3)
  logical :: h
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) n, lvlen, mklen, nn, root
  allocate(nkind(nn), ni2(nn), nrfn(nn), ns3(nn), kidoff(nn), nk(nn), capoff(nn), nc(nn), altoff(nn), na(nn))
  allocate(kids(nn * 64 + 1), caps(nn * 64 + 1), alts(nn * 64 + 1))
  tk = 1
  tc = 1
  ta = 1
  do i = 1, nn
     read(u, *) cnt, vals(1:cnt)
     nkind(i) = vals(1)
     ni2(i) = vals(2)
     nrfn(i) = vals(3)
     ns3(i) = vals(4)
     j = 5
     a = vals(j)
     nk(i) = a
     kidoff(i) = tk
     kids(tk:tk + a - 1) = vals(j + 1:j + a)
     tk = tk + a
     j = j + a + 1
     b = vals(j)
     nc(i) = b
     capoff(i) = tc
     caps(tc:tc + b - 1) = vals(j + 1:j + b)
     tc = tc + b
     j = j + b + 1
     c = vals(j)
     na(i) = c
     altoff(i) = ta
     alts(ta:ta + c - 1) = vals(j + 1:j + c)
     ta = ta + c
  end do
  close(u)
  allocate(ps%lv(0:lvlen - 1), ps%mk(0:mklen - 1))
  ps%lv = 7
  r%id = root
  call anp_clears(ps, r, int(n, int64))
  write(*, '(i0, 1x, i0)', advance="no") ps%err, ps%nmk
  if (ps%err == 0) then
     do i = 0, int(ps%nmk) - 1
        write(*, '(1x, i0)', advance="no") ps%mk(i)%id
     end do
  end if
  write(*, *)
  do kd = 0, 3
     t(kd) = anp_tc(0_int64, r, 0_int64, 0_int64, int(kd, int64))
  end do
  h = anp_hfr(0_int64, r, 0_int64, 0_int64)
  write(*, '(4(i0, 1x), i0)') t, merge(1, 0, h)
end program anpass_check

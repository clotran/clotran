! aot_check: runs the GENERATED eligibility scan (aot_gen.inc, from
! model/aot.lisp) on trees read from a file, through mock reads that answer
! what model/aot.lisp's ast-* and aot-nbods/aot-bod answer of the same tree.
! scripts/fuzz-aot-gen writes the trees and compares the answers with ACL2's.
! With the argument `broken`, a case node reads as a do (a kind the compiler
! emits): the negative control.
!
!   aot_check CASEFILE [broken]
!
! CASEFILE: nnodes root, then a line a node, 1..nnodes:
!   kind s3 nk kid.. na alt.. nb bod..
! (0 is nil). Out: "sc" then aot_fr of each node 1..nnodes.
module aot_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
  end type gc_value
  integer, allocatable :: nkind(:), ns3(:), kidoff(:), nk(:), altoff(:), na(:), bodoff(:), nb(:)
  integer, allocatable :: kids(:), alts(:), bods(:)
  logical :: broken = .false., typed = .false.
  ! slice 2: i2 s2 rs rn cty hop kw per node
  integer(int64), allocatable :: xf(:, :)
  type :: aot_state
     integer(int64), allocatable :: tv(:), rc(:), lo(:)
     integer(int64) :: cb = 0, cn = 0, a0 = 1, a1 = 1, a2 = 1, ad = 0, ns = 0
  end type aot_state
contains
  logical function ok(nd)
    type(gc_value), intent(in) :: nd
    ok = nd%id >= 1 .and. nd%id <= size(nkind)
  end function ok

  integer(int64) function ast_kind(nd)
    type(gc_value), intent(in) :: nd
    ast_kind = 0
    if (ok(nd)) ast_kind = nkind(nd%id)
    if (broken .and. ast_kind == 19 .and. .not. typed) ast_kind = 5
  end function ast_kind

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

  integer(int64) function aot_nbods(nd)
    type(gc_value), intent(in) :: nd
    aot_nbods = 0
    if (ok(nd)) aot_nbods = nb(nd%id)
  end function aot_nbods

  function aot_bod(nd, i) result(k)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    type(gc_value) :: k
    k%id = 0
    if (ok(nd)) then
       if (i >= 0 .and. i < nb(nd%id)) k%id = bods(bodoff(nd%id) + i)
    end if
  end function aot_bod

  ! slice 2's reads: the fields the case file gives each node
  integer(int64) function aot_i2(nd)
    type(gc_value), intent(in) :: nd
    aot_i2 = 0
    if (ok(nd)) aot_i2 = xf(1, nd%id)
  end function aot_i2

  integer(int64) function aot_s2(nd)
    type(gc_value), intent(in) :: nd
    aot_s2 = 0
    if (ok(nd)) aot_s2 = xf(2, nd%id)
  end function aot_s2

  integer(int64) function aot_rs(nd)
    type(gc_value), intent(in) :: nd
    aot_rs = 0
    if (ok(nd)) aot_rs = xf(3, nd%id)
  end function aot_rs

  integer(int64) function aot_rn(nd)
    type(gc_value), intent(in) :: nd
    aot_rn = 0
    if (ok(nd)) aot_rn = xf(4, nd%id)
  end function aot_rn

  integer(int64) function aot_cty(nd)
    type(gc_value), intent(in) :: nd
    aot_cty = 1
    if (ok(nd)) aot_cty = xf(5, nd%id)
    if (broken .and. aot_cty == 3) aot_cty = 2
  end function aot_cty

  integer(int64) function aot_hop(nd)
    type(gc_value), intent(in) :: nd
    aot_hop = 0
    if (ok(nd)) aot_hop = xf(6, nd%id)
  end function aot_hop

  integer(int64) function aot_kw(nd)
    type(gc_value), intent(in) :: nd
    aot_kw = 0
    if (ok(nd)) aot_kw = xf(7, nd%id)
  end function aot_kw

  include "aot_gen.inc"
end module aot_mock

program aot_check
  use iso_fortran_env, only: int64
  use aot_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, nn, root, i, j, a, cnt, vals(4096), tk, ta, tb, ne
  integer(int64) :: env(0:63), ty, okf
  type(aot_state) :: as
  type(gc_value) :: r
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  read(u, *) nn, root
  allocate(nkind(nn), ns3(nn), kidoff(nn), nk(nn), altoff(nn), na(nn), bodoff(nn), nb(nn))
  allocate(kids(nn * 64 + 1), alts(nn * 64 + 1), bods(nn * 64 + 1), xf(7, nn))
  tk = 1
  ta = 1
  tb = 1
  do i = 1, nn
     read(u, *) cnt, vals(1:cnt)
     nkind(i) = vals(1)
     ns3(i) = vals(2)
     j = 3
     a = vals(j)
     nk(i) = a
     kidoff(i) = tk
     kids(tk:tk + a - 1) = vals(j + 1:j + a)
     tk = tk + a
     j = j + a + 1
     a = vals(j)
     na(i) = a
     altoff(i) = ta
     alts(ta:ta + a - 1) = vals(j + 1:j + a)
     ta = ta + a
     j = j + a + 1
     a = vals(j)
     nb(i) = a
     bodoff(i) = tb
     bods(tb:tb + a - 1) = vals(j + 1:j + a)
     tb = tb + a
     j = j + a + 1
     xf(:, i) = 0
     xf(5, i) = 1
     if (cnt >= j + 6) xf(:, i) = vals(j:j + 6)
  end do
  env = 1
  read(u, *, end=9) ne, env(0:ne - 1)
9 close(u)
  r%id = root
  write(*, '(i0)') merge(1, 0, aot_sc(0_int64, r, 0_int64, 0_int64))
  do i = 1, nn
     r%id = i
     write(*, '(i0, 1x)', advance="no") merge(1, 0, aot_fr(0_int64, r, 0_int64, 0_int64))
  end do
  write(*, *)
  ! slice 2: each node typed in the environment the case gives
  allocate(as%tv(0:63), as%rc(0:63), as%lo(0:63))
  typed = .true.
  do i = 1, nn
     as%tv = env
     as%rc = 0
     as%lo = 1
     as%cb = 0
     as%cn = 0
     r%id = i
     call aot_ty(as, 0_int64, r, 0_int64, 0_int64, 0_int64, ty, okf)
     write(*, '(i0, 1x, i0, 1x)', advance="no") ty, okf
  end do
  write(*, *)
end program aot_check

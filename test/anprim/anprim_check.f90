! anprim_check: runs the GENERATED primitive kinds (anprim_gen.inc, from
! model/anprim.lisp) on cases read from a file, a node's kind read through
! a mock apk_kid that answers the case's operand kinds, as the attachment
! scripts/fuzz-anprim-gen gives apk-kid does. With the argument `broken`,
! operand i answers operand i+1's kind: the negative control.
!
!   anprim_check CASEFILE [broken]
!
! CASEFILE: a line a case: how n k1 .. k(n-1) pk hinted loopp rk ret bk p k e.
! Out: a line a case, the answers apk_arith, apk_loop, apk_let, apk_ret,
! apk_recur_ok, apk_elem, apk_num, apk_int_p, apk_float_p.
module anprim_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
  end type gc_value
  integer(int64) :: kk(0:63)
  integer :: nk = 0
  logical :: broken = .false.
contains
  integer(int64) function apk_kid(kids, sc, i) result(k)
    type(gc_value), intent(in) :: kids, sc
    integer(int64), intent(in) :: i
    integer(int64) :: j
    j = i
    if (broken) j = i + 1
    k = 0
    if (j >= 0 .and. j < nk) k = kk(j)
  end function apk_kid

  include "anprim_gen.inc"
end module anprim_mock

program anprim_check
  use iso_fortran_env, only: int64
  use anprim_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, ios, i
  integer(int64) :: how, n, v(0:63), a(9)
  type(gc_value) :: x
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  do
     read(u, *, iostat=ios) how, n
     if (ios /= 0) exit
     backspace(u)
     read(u, *) how, n, v(1:n - 1), a(1:9)
     nk = int(n)
     kk = 0
     kk(1:n - 1) = v(1:n - 1)
     write(*, '(i0,8(1x,i0))') apk_arith(x, x, how, n), apk_loop(a(1)), apk_let(a(1), a(2), a(3), a(4)), &
          apk_ret(a(5), a(6)), apk_recur_ok(a(7), a(8)), apk_elem(a(9)), apk_num(a(8)), &
          merge(1_int64, 0_int64, apk_int_p(a(8))), merge(1_int64, 0_int64, apk_float_p(a(8)))
  end do
  close(u)
  i = 0
end program anprim_check

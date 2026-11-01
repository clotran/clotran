! exec_check: runs the GENERATED tree evaluator's decisions (exec_gen.inc,
! from model/exec.lisp) on cases read from a file. With the argument
! `broken`, the value in flight's truthiness is read the wrong way round
! and the restart decision's flag ignored: the negative control.
!
!   exec_check CASEFILE [broken]
!
! CASEFILE: a line a case: k pc i nk n2 tv rf mk.
! Out: a line a case, the answers ex_act, ex_kid, ex_pc, ex_i, ex_fin.
module exec_mock
  use iso_fortran_env, only: int64
  implicit none
  type :: gc_value
     integer :: id = 0
  end type gc_value
contains
  include "exec_gen.inc"
end module exec_mock

program exec_check
  use iso_fortran_env, only: int64
  use exec_mock
  implicit none
  character(len=4096) :: path, arg
  integer :: u, ios
  integer(int64) :: a(8), tv, rf
  logical :: broken
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  do
     read(u, *, iostat=ios) a
     if (ios /= 0) exit
     tv = a(6)
     rf = a(7)
     if (broken) then
        tv = 1 - a(6)
        rf = 1
     end if
     write(*, '(i0,4(1x,i0))') ex_act(a(1), a(2), a(3), a(4), a(5), tv), ex_kid(a(1), a(2), a(3), a(4), a(5), tv), &
          ex_pc(a(1), a(2), a(3), a(4), a(5), tv), ex_i(a(1), a(2), a(3), a(4), a(5), tv), ex_fin(rf, a(8))
  end do
  close(u)
end program exec_check

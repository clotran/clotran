! exec_check: runs the GENERATED tree evaluator's decisions (exec_gen.inc,
! from model/exec.lisp) on cases read from a file. With the argument
! `broken`, the value in flight's truthiness is read the wrong way round,
! the restart decision's flag ignored and every arity's variadic flag
! reversed: the negative control.
!
!   exec_check CASEFILE [broken]
!
! CASEFILE: a line a case: k pc i nk n2 tv rf mk, then a call's arities
! na nf0 vr0 .. nf3 vr3 (the first na of them), its count m and cl (1 when
! the callee is one of the machine's closures); an apply: ap an fk sq (ex_apentry's),
! and its walk: req, the leading arguments k and the seq's length.
! Out: a line a case, the answers ex_act, ex_kid, ex_pc, ex_i, ex_fin, the
! arity the count picks (exec.inc pick_arity's walk over ex_arfit: the
! fixed pass, then the variadic one; -1 for none), ex_entry, ex_apentry and
! the walk B_APPLY takes over ex_apstep: its way, its fixed arguments' count
! and its rest's length.
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
  integer :: u, ios, p, j, pick
  integer(int64) :: a(26), tv, rf, vr(0:3), fit, ap, more, step, k, left, nfx, nrest
  logical :: broken
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  broken = (trim(arg) == "broken")
  open(newunit=u, file=trim(path), status="old", action="read")
  do
     read(u, *, iostat=ios) a
     if (ios /= 0) exit
     tv = a(6)
     ap = a(20)
     rf = a(7)
     do j = 0, 3
        vr(j) = a(11 + 2 * j)
     end do
     if (broken) then
        tv = 1 - a(6)
        rf = 1
        vr = 1 - vr
        ap = 1 - a(20)
     end if
     pick = -1
     do p = 0, 1
        do j = 0, int(a(9)) - 1
           if (ex_arfit(int(p, int64), a(10 + 2 * j), vr(j), a(18)) == 1) then
              pick = j
              exit
           end if
        end do
        if (pick >= 0) exit
     end do
     fit = 0
     if (pick >= 0) fit = 1
     ! B_APPLY's walk: elements off the seq while ex_apstep says so
     k = a(25)
     left = a(26)
     do
        more = 0
        if (left > 0) more = 1
        if (broken) more = 1 - more
        step = ex_apstep(a(24), k, more)
        if (step /= 1 .or. left <= 0) exit
        k = k + 1
        left = left - 1
     end do
     if (step == 2) then
        nfx = a(24)
        nrest = k - a(24) + left
     else
        step = 3
        nfx = k + left
        nrest = 0
     end if
     write(*, '(i0,10(1x,i0))') ex_act(a(1), a(2), a(3), a(4), a(5), tv), ex_kid(a(1), a(2), a(3), a(4), a(5), tv), &
          ex_pc(a(1), a(2), a(3), a(4), a(5), tv), ex_i(a(1), a(2), a(3), a(4), a(5), tv), ex_fin(rf, a(8)), &
          pick, ex_entry(a(19), fit), ex_apentry(ap, a(21), a(22), a(23)), step, nfx, nrest
  end do
  close(u)
end program exec_check

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
! and its walk: req, the leading arguments k, the seq's length, its kind
! (1 a list, 2 a vector, 3 a lazy seq of that many cells), its tail's kind and length.
! Out: a line a case, the answers ex_act, ex_kid, ex_pc, ex_i, ex_fin, the
! arity the count picks (exec.inc pick_arity's walk over ex_arfit: the
! fixed pass, then the variadic one; -1 for none), ex_entry, ex_apentry and
! the walk B_APPLY takes over ex_apstep: its way, its fixed arguments' count
! its rest's length and the realisations it makes.
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
  integer(int64) :: a(29), tv, rf, vr(0:3), fit, ap, more, step, k, left, nfx, nrest, d, dd, nr
  integer(int64) :: md, rem, ix, cnt, lc, smd, srem, six, scnt, slc
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
     ! B_APPLY's walk: each position read while ex_aplook says, by its
     ! kind (sk_step), realising a lazy seq there; elements off the seq
     ! while ex_apstep says so; the peek past position req
     select case (a(27))
     case (1)
        md = 1
     case (2)
        md = 2
     case default
        md = 3
     end select
     rem = a(26)
     ix = 0
     cnt = a(26)
     lc = a(26)
     k = a(25)
     nr = 0
     do
        d = 1
        if (ex_aplook(a(24), k) == 1) then
           do
              d = sk_step(kind(), ix, cnt)
              if (d /= 3) exit
              call realise()
              nr = nr + 1
           end do
        end if
        more = 0
        if (d == 1 .or. d == 2 .or. d == 5) more = 1
        if (broken) more = 1 - more
        step = ex_apstep(a(24), k, more)
        if (step /= 1 .or. .not. (d == 1 .or. d == 2 .or. d == 5)) exit
        k = k + 1
        call advance(d)
     end do
     if (step == 2 .and. ex_aplook(a(24), k + 1) == 1 .and. .not. broken) then
        smd = md; srem = rem; six = ix; scnt = cnt; slc = lc
        call advance(d)
        if (kind() == 3) nr = nr + 1
        md = smd; rem = srem; ix = six; cnt = scnt; lc = slc
     end if
     left = 0
     do
        dd = sk_step(kind(), ix, cnt)
        if (dd == 3) then
           call realise()
        else if (dd == 1 .or. dd == 2 .or. dd == 5) then
           left = left + 1
           call advance(dd)
        else
           exit
        end if
     end do
     if (step == 2) then
        nfx = a(24)
        nrest = k - a(24) + left
     else
        step = 3
        nfx = k + left
        nrest = 0
     end if
     write(*, '(i0,11(1x,i0))') ex_act(a(1), a(2), a(3), a(4), a(5), tv), ex_kid(a(1), a(2), a(3), a(4), a(5), tv), &
          ex_pc(a(1), a(2), a(3), a(4), a(5), tv), ex_i(a(1), a(2), a(3), a(4), a(5), tv), ex_fin(rf, a(8)), &
          pick, ex_entry(a(19), fit), ex_apentry(ap, a(21), a(22), a(23)), step, nfx, nrest, nr
  end do
  close(u)
contains
  ! the seq, as B_APPLY's shims read it (exec.inc ap_kind): md 0 the end,
  ! 1 a list of rem, 2 a vector's view at ix of cnt, 3 a lazy seq of lc
  ! cells still to realise, 5 a realised cell; a(28) its tail's kind
  ! (0 none, 1 a list, 2 a vector), a(29) the tail's length
  integer(int64) function kind()
    select case (md)
    case (1)
       kind = 0
       if (rem > 0) kind = 1
    case (2)
       kind = 2
    case (3)
       kind = 3
    case (5)
       kind = 5
    case default
       kind = 0
    end select
  end function kind
  subroutine realise()
    if (lc > 0) then
       md = 5
    else if (a(28) == 1) then
       md = 1
       rem = a(29)
    else if (a(28) == 2) then
       md = 2
       ix = 0
       cnt = a(29)
    else
       md = 0
    end if
  end subroutine realise
  subroutine advance(dk)
    integer(int64), intent(in) :: dk
    select case (dk)
    case (1)
       rem = rem - 1
    case (2)
       ix = ix + 1
    case (5)
       md = 3
       lc = lc - 1
    end select
  end subroutine advance
end program exec_check

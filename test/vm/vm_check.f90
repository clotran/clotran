! Runs an encoded program on the GENERATED VM (src/f/gen/vm_gen.f90) and
! prints the machine after every step, in the form ACL2 prints vmi's
! (scripts/fuzz-vmx2 -g compares the two, line for line).
!
!   vm_check FILE
!
! FILE: "ncode npool nfn ncl nstk nctl", the code words, the pool (one
! per line: "I n", "T", "N", "K name" or "C" and a cons in prefix
! tokens, each "C car cdr" -- a seq constant apply spreads), each function's first clause
! and count, each clause's arity, entry and rest flag.
program vm_check
  use iso_fortran_env, only: int64
  use vm_runtime
  use vm_gen
  implicit none
  type(vm_state) :: st
  character(len=4096) :: path, line, mode
  character(len=64) :: toks(512)
  integer :: ntok, tp
  integer :: u, k
  integer(int64) :: ncode, npool, nfn, ncl, nstk, nctl, i, n
  logical :: last, fused

  call get_command_argument(1, path)
  call get_command_argument(2, mode)
  fused = (trim(mode) == 'fused')
  open(newunit=u, file=trim(path), status='old', action='read')
  read(u, *) ncode, npool, nfn, ncl, nstk, nctl
  allocate(st%code(0:ncode-1), st%pool(0:npool-1), st%stk(0:nstk-1), st%tmp(0:nstk-1))
  allocate(st%ckind(0:nctl-1), st%ca(0:nctl-1), st%cb(0:nctl-1), st%cc(0:nctl-1), st%cprev(0:nctl-1))
  allocate(st%fnfirst(0:nfn-1), st%fncount(0:nfn-1), st%cln(0:ncl-1), st%clent(0:ncl-1), st%clrest(0:ncl-1))
  st%ckind = 0; st%ca = 0; st%cb = 0; st%cc = 0; st%cprev = 0
  do i = 0, ncode - 1
     read(u, *) st%code(i)
  end do
  do i = 0, npool - 1
     read(u, '(a)') line
     select case (line(1:1))
     case ('I')
        read(line(2:), *) n
        st%pool(i) = vint(n)
     case ('T')
        st%pool(i) = value(VT_T, 0)
     case ('K')
        st%pool(i) = rt_keyword(trim(adjustl(line(2:))))
     case ('C')
        call tokenize(line(2:))
        tp = 1
        st%pool(i) = parse_val()
     case default
        st%pool(i) = value(VT_NIL, 0)
     end select
  end do
  do i = 0, nfn - 1
     read(u, *) st%fnfirst(i), st%fncount(i)
  end do
  do i = 0, ncl - 1
     read(u, *) st%cln(i), st%clent(i), st%clrest(i)
  end do
  close(u)

  ! the bounds vmg_run's guard asks for, which the generated vmg_good
  ! checks (with fused, after the generated pass tags the program, which
  ! then runs by the fused step); then as ACL2's trace: the state, a step, ..., until the
  ! machine stops or has run the main code's return
  if (fused) call vmg_fuse_prog(st)
  write(*, '(a)') merge('good t  ', 'good nil', vmg_good(st))
  if (fused) then
     write(*, '(a)', advance='no') 'tags'
     do i = 0, ncode / 4 - 1
        write(*, '(1x, i0)', advance='no') st%code(4 * i + 3)
     end do
     write(*, '(a)') ''
  end if
  call show()
  do k = 1, 400000
     last = (vmg_w(st, st%pc, 0_int64) == 11 .and. st%ctop == 0 .and. st%status == 0)
     if (fused) then
        call vmg_xstep(st)
     else
        call vmg_step(st)
     end if
     call show()
     if (st%status /= 0 .or. last) exit
  end do

contains

  subroutine tokenize(s)
    character(len=*), intent(in) :: s
    integer :: a, b
    ntok = 0
    a = 1
    do
       do while (a <= len_trim(s) .and. s(a:a) == ' ')
          a = a + 1
       end do
       if (a > len_trim(s)) exit
       b = a
       do while (b <= len_trim(s) .and. s(b:b) /= ' ')
          b = b + 1
       end do
       ntok = ntok + 1
       toks(ntok) = s(a:b-1)
       a = b
    end do
  end subroutine tokenize

  ! a value in prefix tokens: I n, T, N, K name, C car cdr
  recursive function parse_val() result(v)
    type(value) :: v, a, d
    integer(int64) :: n
    select case (trim(toks(tp)))
    case ('I')
       read(toks(tp + 1), *) n
       v = vint(n)
       tp = tp + 2
    case ('T')
       v = value(VT_T, 0)
       tp = tp + 1
    case ('K')
       v = rt_keyword(trim(toks(tp + 1)))
       tp = tp + 2
    case ('C')
       tp = tp + 1
       a = parse_val()
       d = parse_val()
       v = cons(a, d)
    case default
       v = value(VT_NIL, 0)
       tp = tp + 1
    end select
  end function parse_val

  subroutine show()
    integer(int64) :: j
    write(*, '(6(i0, 1x), a)', advance='no') st%pc, st%fb, st%sp, st%status, st%ctop, st%hidx, '|'
    do j = 0, min(st%sp, size(st%stk, kind=int64)) - 1
       write(*, '(a)', advance='no') ' '
       call write_value(6, st%stk(j))
    end do
    write(*, '(a)', advance='no') ' |'
    do j = 0, st%ctop - 1
       write(*, '(1x, 5(i0, 1x))', advance='no') st%ckind(j), st%ca(j), st%cb(j), st%cc(j), st%cprev(j)
    end do
    write(*, '(a)') ''
  end subroutine show

end program vm_check

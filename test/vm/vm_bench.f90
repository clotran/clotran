! Times a program on the generated VM with no trace: vm_bench FILE STEPS [fused]
! -- fused: the generated pass tags the superinstructions first
! (vmg_fuse_prog) and the generated fused step runs it (vmg_xstep).
program vm_bench
  use iso_fortran_env, only: int64
  use vm_runtime
  use vm_gen
  implicit none
  type(vm_state) :: st
  character(len=512) :: path, line, arg, mode
  logical :: fused
  integer :: u
  integer(int64) :: ncode, npool, nfn, ncl, nstk, nctl, i, n, steps, t0, t1, rate
  call get_command_argument(1, path)
  call get_command_argument(2, arg)
  read(arg, *) steps
  call get_command_argument(3, mode)
  fused = (trim(mode) == 'fused')
  open(newunit=u, file=trim(path), status='old', action='read')
  read(u, *) ncode, npool, nfn, ncl, nstk, nctl
  allocate(st%code(0:ncode-1), st%pool(0:npool-1), st%stk(0:nstk-1))
  allocate(st%ckind(0:nctl-1), st%ca(0:nctl-1), st%cb(0:nctl-1), st%cc(0:nctl-1), st%cprev(0:nctl-1))
  allocate(st%fnfirst(0:max(nfn,1_int64)-1), st%fncount(0:max(nfn,1_int64)-1))
  allocate(st%cln(0:max(ncl,1_int64)-1), st%clent(0:max(ncl,1_int64)-1), st%clrest(0:max(ncl,1_int64)-1))
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
  ! step until the main code returns, as vm_check stops
  call system_clock(t0, rate)
  if (fused) call vmg_fuse_prog(st)
  do i = 1, steps
     if (st%code(4 * st%pc) == 11 .and. st%ctop == 0) exit
     if (fused) then
        call vmg_xstep(st)
     else
        call vmg_step(st)
     end if
     if (st%status /= 0) exit
  end do
  call system_clock(t1)
  write(*, '(a, i0, a)', advance='no') 'steps ', i, '  '
  write(*, '(a, f10.2, a)', advance='no') 'ms ', 1000.0d0 * (t1 - t0) / rate, '  answer '
  call write_value(6, st%stk(0))
  write(*, '(a, i0, a, i0)') '  status ', st%status, ' pc ', st%pc
end program vm_bench

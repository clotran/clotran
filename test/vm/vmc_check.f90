! The GENERATED compiler (src/f/gen/vmc_gen.f90) on one program, for
! scripts/fuzz-vmc-gen: reads the expression and the function table as
! ACL2 prints them, compiles them with vmicg_program, and prints the
! error flag, the status and every array, as the fuzzer's ACL2 driver
! prints vmicg-program's.
program vmc_check
  use iso_fortran_env, only: int64
  use vm_runtime
  use vmc_gen
  implicit none
  type(vm_state) :: st
  type(vc_state) :: ce
  type(value) :: e, defs
  character(len=:), allocatable :: buf
  character(len=4096) :: path
  integer :: u, sz, p
  integer(int64) :: j

  call get_command_argument(1, path)
  open(newunit=u, file=trim(path), access='stream', form='unformatted', action='read')
  inquire(unit=u, size=sz)
  allocate(character(len=sz) :: buf)
  read(u) buf
  close(u)
  p = 1
  e = read_sexp()
  defs = read_sexp()

  allocate(st%code(0:-1), st%pool(0:-1), st%stk(0:-1), st%ckind(0:-1), st%ca(0:-1), st%cb(0:-1), st%cc(0:-1))
  allocate(st%cprev(0:-1), st%fnfirst(0:-1), st%fncount(0:-1), st%cln(0:-1), st%clent(0:-1), st%clrest(0:-1))
  allocate(ce%env(0:-1))
  call vmicg_program(st, ce, e, defs, 1024_int64, 256_int64)

  write(6, '(i0, 1x, i0)') ce%err, st%status
  write(6, '(6(i0, 1x))') size(st%code), size(st%pool), size(st%fnfirst), size(st%cln), size(st%stk), size(st%ckind)
  do j = 0, size(st%code, kind=int64) - 1
     write(6, '(i0)') st%code(j)
  end do
  do j = 0, size(st%pool, kind=int64) - 1
     call write_value(6, st%pool(j))
     write(6, '(a)') ''
  end do
  do j = 0, size(st%fnfirst, kind=int64) - 1
     write(6, '(i0, 1x, i0)') st%fnfirst(j), st%fncount(j)
  end do
  do j = 0, size(st%cln, kind=int64) - 1
     write(6, '(i0, 1x, i0, 1x, i0)') st%cln(j), st%clent(j), st%clrest(j)
  end do
  write(6, '(5(i0, 1x))') st%pc, st%fb, st%sp, st%ctop, st%hidx

contains

  subroutine skip_space()
    do while (p <= len(buf))
       if (index(' ' // achar(9) // achar(10) // achar(13), buf(p:p)) == 0) exit
       p = p + 1
    end do
  end subroutine skip_space

  ! nil, t, integers, keywords and lists, as ACL2 prints them downcased
  recursive function read_sexp() result(v)
    type(value) :: v
    type(value) :: items(0:1023), tail
    integer :: k, q, n
    integer(int64) :: i
    call skip_space()
    if (p > len(buf)) error stop 'vmc_check: the input ends early'
    if (buf(p:p) == '(') then
       p = p + 1
       n = 0
       tail = rt_nil()
       do
          call skip_space()
          if (buf(p:p) == ')') exit
          if (buf(p:p) == '.' .and. index(' ()', buf(p+1:p+1)) > 0) then
             p = p + 1
             tail = read_sexp()
             call skip_space()
             exit
          end if
          if (n > ubound(items, 1)) error stop 'vmc_check: a list too long'
          items(n) = read_sexp()
          n = n + 1
       end do
       p = p + 1
       v = tail
       do k = n - 1, 0, -1
          v = cons(items(k), v)
       end do
       return
    end if
    q = p
    do while (p <= len(buf))
       if (index(' ()' // achar(9) // achar(10) // achar(13), buf(p:p)) > 0) exit
       p = p + 1
    end do
    if (buf(q:q) == ':') then
       v = rt_keyword(buf(q+1:p-1))
    else if (buf(q:p-1) == 'nil') then
       v = rt_nil()
    else if (buf(q:p-1) == 't') then
       v = rt_t()
    else
       read(buf(q:p-1), *) i
       v = vint(i)
    end if
  end function read_sexp

end program vmc_check

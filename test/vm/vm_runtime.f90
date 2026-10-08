! The runtime the generated VM (src/f/gen/vm_gen.f90) runs on, FOR THE
! CHECK against ACL2 (scripts/check-vm-gen): a small value heap that
! mirrors model/vmx2.lisp's values exactly -- nil, t, integers, keywords
! (:false among them) and conses, a closure being the list (:clo f caps)
! as it is there -- and the operations on values the model leaves to the
! runtime, written as vmx2.lisp and vmg.lisp write them, with prim as
! vmx2.lisp's prim-impl. clotran's own runtime, gc_value and the
! builtins, takes its place when the VM is wired in. The compiler's
! operations (rt_car .. rt_len, the resizes) serve src/f/gen/vmc_gen.f90.
module vm_runtime
  use iso_fortran_env, only: int64
  implicit none

  integer, parameter :: VT_NIL = 0, VT_T = 1, VT_INT = 2, VT_KW = 3, VT_CONS = 4

  type value
     integer :: tag = VT_NIL
     integer(int64) :: i = 0
  end type value

  type vm_state
     integer(int64) :: pc = 0, fb = 0, sp = 0, status = 0, ctop = 0, hidx = -1
     integer(int64), allocatable :: code(:)
     type(value), allocatable :: pool(:), stk(:)
     integer(int64), allocatable :: ckind(:), ca(:), cb(:), cc(:), cprev(:)
     integer(int64), allocatable :: fnfirst(:), fncount(:), cln(:), clent(:), clrest(:)
  end type vm_state

  ! the compile environment (model/vmic.lisp's stobj vce)
  type vc_state
     integer(int64), allocatable :: env(:)
     integer(int64) :: err = 0
  end type vc_state

  ! the conses, and the keywords by name
  type(value), allocatable :: hcar(:), hcdr(:)
  integer(int64) :: nheap = 0
  character(len=32) :: kwname(256)
  integer :: nkw = 0

contains

  function rt_keyword(name) result(v)
    character(len=*), intent(in) :: name
    type(value) :: v
    integer :: k
    do k = 1, nkw
       if (trim(kwname(k)) == name) then
          v = value(VT_KW, int(k, int64))
          return
       end if
    end do
    nkw = nkw + 1
    kwname(nkw) = name
    v = value(VT_KW, int(nkw, int64))
  end function rt_keyword

  function vint(i) result(v)
    integer(int64), intent(in) :: i
    type(value) :: v
    v = value(VT_INT, i)
  end function vint

  function cons(a, d) result(v)
    type(value), intent(in) :: a, d
    type(value) :: v
    type(value), allocatable :: t1(:), t2(:)
    if (.not. allocated(hcar)) then
       allocate(hcar(0:1023), hcdr(0:1023))
    end if
    if (nheap > ubound(hcar, 1)) then
       allocate(t1(0:2*size(hcar)-1), t2(0:2*size(hcar)-1))
       t1(0:nheap-1) = hcar(0:nheap-1)
       t2(0:nheap-1) = hcdr(0:nheap-1)
       call move_alloc(t1, hcar)
       call move_alloc(t2, hcdr)
    end if
    hcar(nheap) = a
    hcdr(nheap) = d
    v = value(VT_CONS, nheap)
    nheap = nheap + 1
  end function cons

  logical function consp(v)
    type(value), intent(in) :: v
    consp = (v%tag == VT_CONS)
  end function consp

  function car(v) result(r)
    type(value), intent(in) :: v
    type(value) :: r
    if (v%tag == VT_CONS) then
       r = hcar(v%i)
    else
       r = value(VT_NIL, 0)
    end if
  end function car

  function cdr(v) result(r)
    type(value), intent(in) :: v
    type(value) :: r
    if (v%tag == VT_CONS) then
       r = hcdr(v%i)
    else
       r = value(VT_NIL, 0)
    end if
  end function cdr

  logical function is_kw(v, name)
    type(value), intent(in) :: v
    character(len=*), intent(in) :: name
    is_kw = .false.
    if (v%tag == VT_KW) is_kw = (trim(kwname(v%i)) == name)
  end function is_kw

  ! the keywords the operations test, looked up once
  integer(int64) function kw_id(name)
    character(len=*), intent(in) :: name
    type(value) :: v
    v = rt_keyword(name)
    kw_id = v%i
  end function kw_id

  function rt_nil() result(v)
    type(value) :: v
    v = value(VT_NIL, 0)
  end function rt_nil

  function rt_t() result(v)
    type(value) :: v
    v = value(VT_T, 0)
  end function rt_t

  ! ---- vmx2.lisp's value functions ---------------------------------------

  logical function rt_truthy(x)
    type(value), intent(in) :: x
    integer(int64), save :: kfalse = -1
    if (kfalse < 0) kfalse = kw_id("false")
    rt_truthy = .not. (x%tag == VT_NIL .or. (x%tag == VT_KW .and. x%i == kfalse))
  end function rt_truthy

  function fixv(x) result(i)
    type(value), intent(in) :: x
    integer(int64) :: i
    i = 0
    if (x%tag == VT_INT) i = x%i
  end function fixv

  function rt_add(a, b) result(r)
    type(value), intent(in) :: a, b
    type(value) :: r
    r = vint(fixv(a) + fixv(b))
  end function rt_add

  function rt_lt(a, b) result(r)
    type(value), intent(in) :: a, b
    type(value) :: r
    integer(int64), save :: kfalse = -1
    if (kfalse < 0) kfalse = kw_id("false")
    if (fixv(a) < fixv(b)) then
       r = value(VT_T, 0)
    else
       r = value(VT_KW, kfalse)
    end if
  end function rt_lt

  ! (clo f caps) = (list :clo f caps)
  function rt_clo(f, caps) result(r)
    integer(int64), intent(in) :: f
    type(value), intent(in) :: caps
    type(value) :: r
    r = cons(rt_keyword("clo"), cons(vint(f), cons(caps, value(VT_NIL, 0))))
  end function rt_clo

  logical function rt_clop(c)
    type(value), intent(in) :: c
    rt_clop = consp(c)
    if (rt_clop) rt_clop = is_kw(car(c), "clo") .and. consp(cdr(c))
    if (rt_clop) rt_clop = consp(cdr(cdr(c)))
  end function rt_clop

  ! clo-f, as the integer vmg-pick takes; anything else picks no function
  function rt_clo_f(c) result(f)
    type(value), intent(in) :: c
    integer(int64) :: f
    type(value) :: x
    x = car(cdr(c))
    f = -1
    if (x%tag == VT_INT) f = x%i
  end function rt_clo_f

  ! (nth i (clo-caps c))
  function rt_capt(i, c) result(r)
    integer(int64), intent(in) :: i
    type(value), intent(in) :: c
    type(value) :: r
    integer(int64) :: k
    r = car(cdr(cdr(c)))
    do k = 1, i
       r = cdr(r)
    end do
    r = car(r)
  end function rt_capt

  function len_of(l) result(n)
    type(value), intent(in) :: l
    integer(int64) :: n
    type(value) :: x
    n = 0
    x = l
    do while (consp(x))
       n = n + 1
       x = cdr(x)
    end do
  end function len_of

  ! vmx2.lisp's prim-impl
  function rt_prim(op, vals) result(r)
    type(value), intent(in) :: op, vals
    type(value) :: r
    type(value) :: a, b
    integer(int64) :: q
    r = value(VT_NIL, 0)
    if (is_kw(op, "first")) then
       if (consp(vals)) then
          if (consp(car(vals))) r = car(car(vals))
       end if
    else if (is_kw(op, "rest")) then
       if (consp(vals)) then
          if (consp(car(vals))) r = cdr(car(vals))
       end if
    else if (is_kw(op, "empty")) then
       r = value(VT_T, 0)
       if (consp(vals)) then
          if (consp(car(vals))) r = value(VT_NIL, 0)
       end if
    else if (is_kw(op, "count")) then
       r = vint(0_int64)
       if (consp(vals)) r = vint(len_of(car(vals)))
    else if (is_kw(op, "div")) then
       a = car(vals)
       b = car(cdr(vals))
       if (consp(vals) .and. consp(cdr(vals)) .and. a%tag == VT_INT .and. b%tag == VT_INT .and. b%i /= 0) then
          q = a%i / b%i
          if (mod(a%i, b%i) /= 0 .and. ((a%i < 0) .neqv. (b%i < 0))) q = q - 1
          r = vint(q)
       else
          r = cons(rt_keyword("throw"), rt_keyword("arith"))
       end if
    end if
  end function rt_prim

  ! rt_prim on the list (a) and (a b), as the generated superinstructions
  ! call it; clotran's runtime answers these without building the list
  function rt_prim1(op, a) result(r)
    type(value), intent(in) :: op, a
    type(value) :: r
    r = rt_prim(op, cons(a, value(VT_NIL, 0)))
  end function rt_prim1

  function rt_prim2(op, a, b) result(r)
    type(value), intent(in) :: op, a, b
    type(value) :: r
    r = rt_prim(op, cons(a, cons(b, value(VT_NIL, 0))))
  end function rt_prim2

  logical function rt_throwp(a)
    type(value), intent(in) :: a
    rt_throwp = consp(a)
    if (rt_throwp) rt_throwp = is_kw(car(a), "throw")
  end function rt_throwp

  function rt_thrown(a) result(r)
    type(value), intent(in) :: a
    type(value) :: r
    r = cdr(a)
  end function rt_thrown

  ! the slots a..a+k-1 as a list, nil past the stack (vmg-stk-from)
  function rt_list_from(st, a, k) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), intent(in) :: a, k
    type(value) :: r
    integer(int64) :: j
    type(value) :: x
    r = value(VT_NIL, 0)
    do j = a + k - 1, a, -1
       x = value(VT_NIL, 0)
       if (j >= 0 .and. j < size(st%stk, kind=int64)) x = st%stk(j)
       r = cons(x, r)
    end do
  end function rt_list_from

  ! ---- the compiler's (model/vmicg.lisp): the expression read as a list ---

  function rt_car(x) result(r)
    type(value), intent(in) :: x
    type(value) :: r
    r = car(x)
  end function rt_car

  function rt_cdr(x) result(r)
    type(value), intent(in) :: x
    type(value) :: r
    r = cdr(x)
  end function rt_cdr

  logical function rt_consp(x)
    type(value), intent(in) :: x
    rt_consp = consp(x)
  end function rt_consp

  ! (equal x k), k a keyword: every rt-is in the model tests one
  logical function rt_is(x, k)
    type(value), intent(in) :: x, k
    rt_is = (x%tag == k%tag .and. x%i == k%i)
  end function rt_is

  ! a natural below 2^31, else -1
  function rt_nat(x) result(n)
    type(value), intent(in) :: x
    integer(int64) :: n
    n = -1
    if (x%tag == VT_INT) then
       if (x%i >= 0 .and. x%i < 2147483648_int64) n = x%i
    end if
  end function rt_nat

  function rt_len(x) result(n)
    type(value), intent(in) :: x
    integer(int64) :: n
    n = len_of(x)
  end function rt_len

  ! a stobj array resized as ACL2 resizes it: the elements kept, the new
  ! ones the initial value
  subroutine rt_resize_int(a, n)
    integer(int64), allocatable, intent(inout) :: a(:)
    integer(int64), intent(in) :: n
    integer(int64), allocatable :: t(:)
    integer(int64) :: m
    allocate(t(0:n-1))
    t = 0
    m = 0
    if (allocated(a)) m = min(n, size(a, kind=int64))
    if (m > 0) t(0:m-1) = a(0:m-1)
    call move_alloc(t, a)
  end subroutine rt_resize_int

  subroutine rt_resize_val(a, n)
    type(value), allocatable, intent(inout) :: a(:)
    integer(int64), intent(in) :: n
    type(value), allocatable :: t(:)
    integer(int64) :: m
    allocate(t(0:n-1))
    m = 0
    if (allocated(a)) m = min(n, size(a, kind=int64))
    if (m > 0) t(0:m-1) = a(0:m-1)
    call move_alloc(t, a)
  end subroutine rt_resize_val

  ! ---- printing, as ACL2 prints with print-case downcase -----------------

  recursive subroutine write_value(u, v)
    integer, intent(in) :: u
    type(value), intent(in) :: v
    type(value) :: x
    select case (v%tag)
    case (VT_NIL)
       write(u, '(a)', advance='no') 'nil'
    case (VT_T)
       write(u, '(a)', advance='no') 't'
    case (VT_INT)
       write(u, '(i0)', advance='no') v%i
    case (VT_KW)
       write(u, '(a)', advance='no') ':' // trim(kwname(v%i))
    case (VT_CONS)
       write(u, '(a)', advance='no') '('
       x = v
       call write_value(u, car(x))
       x = cdr(x)
       do while (consp(x))
          write(u, '(a)', advance='no') ' '
          call write_value(u, car(x))
          x = cdr(x)
       end do
       if (x%tag /= VT_NIL) then
          write(u, '(a)', advance='no') ' . '
          call write_value(u, x)
       end if
       write(u, '(a)', advance='no') ')'
    end select
  end subroutine write_value

end module vm_runtime

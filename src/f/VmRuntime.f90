! VmRuntime: the runtime the GENERATED VM and compiler run on inside
! clotran (src/f/gen/vm_gen.f90, vmc_gen.f90, written from model/vmfg.lisp
! and vmicg.lisp). test/vm/vm_runtime.f90 is the same interface over a
! toy heap, for the check against ACL2; this one is over clotran's values.
!
! THE VALUES. The model's values are opaque to its proofs except where a
! function says otherwise, and the correspondence is:
!
!   model           clotran
!   nil             nil
!   t               true
!   :false          false        (so rt_truthy is Clojure's truthiness)
!   (:throw . v)    a list (THROWN v), THROWN a private object
!   (:clo f caps)   a clotran closure whose fn the program compiled --
!                   f its template's function id (index 9), caps its
!                   captures and, after them, the fn itself; or, made by
!                   the machine's own mkclo, a list (CLO f caps), CLO a
!                   private object
!   prim            a call: see rt_prim
!
! The private heads are objects no Clojure code can reach, so no value a
! program builds is ever taken for a throw or a closure.
!
! THE STACK is a window onto the thread's value stack (the glue in
! vm.inc points st%stk at it), so the collector, which is non-moving and
! scans that stack, sees every slot. Every other array is the program's,
! read-only while it runs; the compiler's arrays are owned and resized
! here (rt_resize_int, rt_resize_val).
!
! THE CALLS go up through two hooks Eval sets at start-up (vm_init in
! vm.inc): this module sits below Eval, which calls the generated VM, so
! it cannot call Eval directly -- the cycle CompiledFn avoids the same way.
module vm_runtime
  use iso_fortran_env, only: int64
  use GC
  use GC, only: value => gc_value
  use PersistentList, only: gcl_cons, gcl_empty, gcl_is, gcl_count
  use PersistentVector, only: gcv_nth, gcv_count, gcv_is
  implicit none
  private

  ! the generated code names the value type `value`
  public :: value
  type, public :: vm_state
     integer(int64) :: pc = 0, fb = 0, sp = 0, status = 0, ctop = 0, hidx = -1
     integer(int64), pointer, contiguous :: code(:) => null()
     type(value), pointer, contiguous :: pool(:) => null(), stk(:) => null()
     integer(int64), pointer, contiguous :: ckind(:) => null(), ca(:) => null(), cb(:) => null(), cc(:) => null()
     integer(int64), pointer, contiguous :: cprev(:) => null(), fnfirst(:) => null(), fncount(:) => null()
     integer(int64), pointer, contiguous :: cln(:) => null(), clent(:) => null(), clrest(:) => null()
  end type vm_state
  type, public :: vc_state
     integer(int64), pointer, contiguous :: env(:) => null()
     integer(int64) :: err = 0
  end type vc_state

  public :: rt_add, rt_capt, rt_car, rt_cdr, rt_clo, rt_clo_f, rt_clop, rt_consp, rt_is, rt_keyword, rt_len
  public :: rt_list_from, rt_lt, rt_nat, rt_nil, rt_t, rt_prim, rt_prim1, rt_prim2, rt_prim3, rt_resize_int, rt_resize_val
  public :: rt_thrown, rt_throwp, rt_truthy, rt_cons
  public :: vmrt_throw_of, vmrt_init

  ! THE HOOKS. call: fn applied to the nargs values in value-stack slots
  ! argbase+1 .., answering out and ok -- or, when it throws, the thrown
  ! value in out, ok false and the error cleared. deref: a Var's value.
  abstract interface
     subroutine vmrt_call_i(fn, argbase, nargs, out, ok)
       import :: value
       type(value), intent(in) :: fn
       integer, intent(in) :: argbase, nargs
       type(value), intent(out) :: out
       logical, intent(out) :: ok
     end subroutine vmrt_call_i
     function vmrt_deref_i(var) result(v)
       import :: value
       type(value), intent(in) :: var
       type(value) :: v
     end function vmrt_deref_i
  end interface
  procedure(vmrt_call_i), pointer, public :: vmrt_call => null()
  procedure(vmrt_deref_i), pointer, public :: vmrt_deref => null()
  ! a node of the program's own (an OBJ_AST constant) run on values: what
  ! flat does for a collection literal, new, a dot call, fn, lazy-seq
  procedure(vmrt_call_i), pointer, public :: vmrt_node => null()
  ! a call of no arity a compiled fn has: clj's ArityException
  procedure(vmrt_call_i), pointer, public :: vmrt_arity => null()
  ! the running body's entry values (the arguments, the captures, the fn
  ! itself) are vstack(vm_args_rb + i + 1), vm_args_rb the thread's own
  ! (gc_stack, set by vm.inc around each run)

  ! the keywords the generated code tests, made once and kept
  integer, parameter :: MAXKW = 64
  character(len=48) :: kw_name(MAXKW)
  type(gc_root) :: kw_root(MAXKW)
  ! the values themselves, read without the state lock a root takes: the
  ! collector does not move objects, and the roots keep these alive
  type(value) :: kw_val(MAXKW)
  integer :: nkw = 0
  ! filled once by vmrt_init, then only read: threads look keywords up at once
  logical :: kw_frozen = .false.
  ! the private heads
  type(gc_root) :: thrown_head, clo_head
  type(value) :: thrown_v, clo_v
  ! the primitives' own keywords, looked up once
  type(value) :: kw_arg, kw_deref, kw_invoke, kw_invoke_m, kw_arity, kw_callw
  ! (CLO f nil) for the first few f, made once: a closure of nothing is
  ! a value no one can tell from another made the same, and main's
  ! mkclo of the arity's own function would otherwise allocate per call
  integer, parameter :: NCLO0 = 16
  type(gc_root) :: clo0_root(0:NCLO0 - 1)
  type(value) :: clo0(0:NCLO0 - 1)
  logical :: heads_made = .false.

contains

  function rt_nil() result(v)
    type(value) :: v
    v = gc_nil()
  end function rt_nil

  function rt_t() result(v)
    type(value) :: v
    v = gc_bool(.true.)
  end function rt_t

  function rt_keyword(name) result(v)
    character(len=*), intent(in) :: name
    type(value) :: v
    integer :: k
    do k = 1, nkw
       if (kw_name(k) == name) then
          v = kw_val(k)
          if (kw_frozen) return
          v = gc_root_get(kw_root(k))
          if (v%tag == GCT_KEY) return
       end if
    end do
    v = gc_key(name, [value ::])
    if (nkw < MAXKW .and. .not. kw_frozen) then
       nkw = nkw + 1
       kw_name(nkw) = name
       call gc_global_keep(kw_root(nkw), v)
       kw_val(nkw) = v
    end if
  end function rt_keyword

  ! every keyword the generated code and the primitives test, made once
  ! before any thread runs VM code; and the private heads
  subroutine vmrt_init()
    character(len=17), parameter :: names(20) = [character(len=17) :: "const", "local", "capt", "if", &
         "let", "add", "lt", "mkclo", "callv", "loop", "recur", "prim", "throw", "try", "rest", &
         "clotran.vm/arg", "clotran.vm/deref", "clotran.vm/invoke", "invoke", "clotran.vm/arity"]
    type(value) :: k
    integer :: i
    kw_frozen = .false.
    nkw = 0
    do i = 1, size(names)
       k = rt_keyword(trim(names(i)))
    end do
    heads_made = .false.
    call make_heads()
    kw_arg = rt_keyword("clotran.vm/arg")
    kw_deref = rt_keyword("clotran.vm/deref")
    kw_invoke = rt_keyword("clotran.vm/invoke")
    kw_invoke_m = rt_keyword("invoke")
    kw_arity = rt_keyword("clotran.vm/arity")
    kw_callw = rt_keyword("clotran.vm/callw")
    kw_frozen = .true.
    do i = 0, NCLO0 - 1
       clo0(i) = gc_nil()
       clo0(i) = rt_clo(int(i, int64), gc_nil())
       call gc_global_keep(clo0_root(i), clo0(i))
    end do
  end subroutine vmrt_init

  subroutine make_heads()
    if (heads_made) return
    call gc_global_keep(thrown_head, gc_str("clotran.vm/thrown", [value ::]))
    call gc_global_keep(clo_head, gc_str("clotran.vm/closure", [value ::]))
    thrown_v = gc_root_get(thrown_head)
    clo_v = gc_root_get(clo_head)
    heads_made = .true.
  end subroutine make_heads

  logical function same(a, b)
    type(value), intent(in) :: a, b
    same = (a%tag == b%tag .and. a%ref == b%ref)
  end function same

  ! ---- lists, as the compiler reads its expression ---------------------------------

  logical function rt_consp(x)
    type(value), intent(in) :: x
    rt_consp = gcl_is(x)
    if (rt_consp) rt_consp = gcl_count(x) > 0
  end function rt_consp

  function rt_car(x) result(r)
    type(value), intent(in) :: x
    type(value) :: r
    r = gc_nil()
    if (rt_consp(x)) r = gc_slot(x, 1)
  end function rt_car

  ! the rest of a list, nil after its last element, as ACL2's cdr
  function rt_cdr(x) result(r)
    type(value), intent(in) :: x
    type(value) :: r
    r = gc_nil()
    if (rt_consp(x)) then
       if (gcl_count(x) > 1) r = gc_slot(x, 2)
    end if
  end function rt_cdr

  function rt_len(x) result(n)
    type(value), intent(in) :: x
    integer(int64) :: n
    n = 0
    if (rt_consp(x)) n = gcl_count(x)
  end function rt_len

  ! (equal x k), k a keyword: every rt-is in the model tests one
  logical function rt_is(x, k)
    type(value), intent(in) :: x, k
    character(len=:), allocatable :: a, b
    rt_is = .false.
    if (x%tag /= GCT_KEY .or. k%tag /= GCT_KEY) return
    if (x%ref == k%ref) then
       rt_is = .true.
       return
    end if
    call gc_text(x, a)
    call gc_text(k, b)
    rt_is = (a == b)
  end function rt_is

  ! a natural below 2^31, else -1
  function rt_nat(x) result(n)
    type(value), intent(in) :: x
    integer(int64) :: n
    n = -1
    if (x%tag == GCT_INT) then
       if (x%ival >= 0 .and. x%ival < 2147483648_int64) n = x%ival
    end if
  end function rt_nat

  ! ---- values ------------------------------------------------------------------

  logical function rt_truthy(x)
    type(value), intent(in) :: x
    rt_truthy = .not. (x%tag == GCT_NIL .or. (x%tag == GCT_BOOL .and. x%ival == 0))
  end function rt_truthy

  ! the model's :add and :lt, on integers (fix); clotran compiles Clojure's
  ! + and < to prims, so these run only if a program says :add or :lt
  function rt_add(a, b) result(r)
    type(value), intent(in) :: a, b
    type(value) :: r
    r = gc_int(fixv(a) + fixv(b))
  end function rt_add

  function rt_lt(a, b) result(r)
    type(value), intent(in) :: a, b
    type(value) :: r
    r = gc_bool(fixv(a) < fixv(b))
  end function rt_lt

  function fixv(x) result(i)
    type(value), intent(in) :: x
    integer(int64) :: i
    i = 0
    if (x%tag == GCT_INT) i = x%ival
  end function fixv

  ! ---- closures: (CLO f caps) ------------------------------------------------------

  function rt_clo(f, caps) result(r)
    integer(int64), intent(in) :: f
    type(value), intent(in) :: caps
    type(value) :: r
    type(gc_stack), pointer :: vst
    integer :: base
    if (caps%tag == GCT_NIL .and. f >= 0 .and. f < NCLO0) then
       if (clo0(f)%tag /= GCT_NIL) then
          r = clo0(f)
          return
       end if
    end if
    call make_heads()
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, caps)
    r = gcl_cons(vs_get(vst, base + 1), gc_nil(), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, r)
    r = gcl_cons(gc_int(f), vs_get(vst, base + 2), [vs_get(vst, base + 2)])
    call vs_set(vst, base + 2, r)
    r = gcl_cons(clo_v, vs_get(vst, base + 2), [vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function rt_clo

  ! a clotran closure, its metadata taken off, whose fn the program compiled:
  ! f the closure (nil when it is not one), fid its function in the program,
  ! ncap its captures -- read from its call table (flat.inc call_table: the
  ! captures in place 3, K in 4, the function id last), one raw vector the
  ! closure notes at birth, not the template's persistent vectors
  subroutine compiled_fn(c, f, fid, ncap)
    type(value), intent(in) :: c
    type(value), intent(out) :: f
    integer(int64), intent(out) :: fid
    integer, intent(out) :: ncap
    type(value) :: ct, x
    f = c
    fid = -1
    ncap = 0
    do while (gc_kind(f) == OBJ_META)
       f = gc_slot(f, 1)
    end do
    if (gc_kind(f) == OBJ_CLOSURE) then
       if (gc_i2(f) > 0) then
          if (gc_kind(gc_slot(f, 3)) /= OBJ_ENV) then
             ct = value(GCT_VEC, gc_i2(f), 0_gc_ip)
             x = gc_reg(ct, 3)
             ncap = int(x%ival)
             x = gc_reg(ct, 4)
             x = gc_reg(ct, 4 + 4 * (int(x%ival) + 1) + ncap + 1)
             if (x%tag == GCT_INT) fid = x%ival
          end if
       end if
    end if
    if (fid < 0) f = gc_nil()
  end subroutine compiled_fn

  logical function rt_clop(c)
    type(value), intent(in) :: c
    type(value) :: f
    integer(int64) :: fid
    integer :: ncap
    call compiled_fn(c, f, fid, ncap)
    if (fid >= 0) then
       rt_clop = .true.
       return
    end if
    rt_clop = rt_consp(c)
    if (rt_clop) rt_clop = same(gc_slot(c, 1), clo_v) .and. gcl_count(c) == 3
  end function rt_clop

  function rt_clo_f(c) result(f)
    type(value), intent(in) :: c
    integer(int64) :: f
    type(value) :: x
    integer :: ncap
    call compiled_fn(c, x, f, ncap)
    if (f >= 0) return
    x = rt_car(rt_cdr(c))
    f = -1
    if (x%tag == GCT_INT) f = x%ival
  end function rt_clo_f

  ! (nth i (clo-caps c)): a clotran closure's capture i, as cap_of reads it
  ! (two in the closure's slots 2 and 4, more in a vector in slot 2), and
  ! past them the fn itself
  function rt_capt(i, c) result(r)
    integer(int64), intent(in) :: i
    type(value), intent(in) :: c
    type(value) :: r
    integer(int64) :: k, fid
    type(value) :: f
    integer :: ncap
    call compiled_fn(c, f, fid, ncap)
    if (fid >= 0) then
       if (i >= ncap) then
          r = c
       else if (ncap > 2) then
          r = gc_vec_get(gc_slot(f, 2), int(i) + 1)
       else if (i == 0) then
          r = gc_slot(f, 2)
       else
          r = gc_slot(f, 4)
       end if
       return
    end if
    r = rt_car(rt_cdr(rt_cdr(c)))
    do k = 1, i
       r = rt_cdr(r)
    end do
    r = rt_car(r)
  end function rt_capt

  ! the slots a..a+k-1 as a list, nil past the stack (vmg-stk-from)
  function rt_list_from(st, a, k) result(r)
    type(vm_state), intent(in) :: st
    integer(int64), intent(in) :: a, k
    type(value) :: r, x
    type(gc_stack), pointer :: vst
    integer(int64) :: j
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, gc_nil())
    do j = a + k - 1, a, -1
       x = gc_nil()
       if (j >= 0 .and. j < size(st%stk, kind=int64)) x = st%stk(j)
       r = gcl_cons(x, vs_get(vst, base + 1), [vs_get(vst, base + 1), x])
       call vs_set(vst, base + 1, r)
    end do
    r = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function rt_list_from

  ! ---- throws: (THROWN v) ------------------------------------------------------------

  function vmrt_throw_of(v) result(r)
    type(value), intent(in) :: v
    type(value) :: r
    type(gc_stack), pointer :: vst
    integer :: base
    call make_heads()
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, v)
    r = gcl_cons(vs_get(vst, base + 1), gc_nil(), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 1, r)
    r = gcl_cons(thrown_v, vs_get(vst, base + 1), [vs_get(vst, base + 1)])
    call vs_leave(vst, base)
  end function vmrt_throw_of

  logical function rt_throwp(a)
    type(value), intent(in) :: a
    rt_throwp = rt_consp(a)
    if (rt_throwp) rt_throwp = same(gc_slot(a, 1), thrown_v) .and. gcl_count(a) == 2
  end function rt_throwp

  function rt_thrown(a) result(r)
    type(value), intent(in) :: a
    type(value) :: r
    r = rt_car(rt_cdr(a))
  end function rt_thrown

  ! ---- THE PRIMITIVES: what clotran's compiled code asks the runtime ----------------
  !
  !   (:prim :clotran.vm/arg (:const i))      the body's entry value i
  !   (:prim :clotran.vm/deref (:const var))  a Var's value
  !   (:prim :clotran.vm/invoke f args..)     f called with args
  !   (:prim f args..)                        f -- a builtin, a Var, a fn
  !                                           written as a constant -- called
  !
  ! A call that throws answers (THROWN v), and the VM unwinds.

  function rt_prim(op, vals) result(r)
    type(value), intent(in) :: op, vals
    type(value) :: r
    type(gc_stack), pointer :: vst
    type(value) :: x
    integer :: base, n, i
    vst => gc_my_stack()
    n = int(rt_len(vals))
    base = vs_enter(vst, n + 1)
    call vs_set(vst, base + 1, vals)
    x = vals
    do i = 1, n
       call vs_set(vst, base + 1 + i, rt_car(x))
       x = rt_cdr(x)
    end do
    r = dispatch(op, base + 1, n)
    call vs_leave(vst, base)
  end function rt_prim

  function rt_prim1(op, a) result(r)
    type(value), intent(in) :: op, a
    type(value) :: r
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, a)
    r = dispatch(op, base, 1)
    call vs_leave(vst, base)
  end function rt_prim1

  function rt_prim2(op, a, b) result(r)
    type(value), intent(in) :: op, a, b
    type(value) :: r
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, a)
    call vs_set(vst, base + 2, b)
    r = dispatch(op, base, 2)
    call vs_leave(vst, base)
  end function rt_prim2

  ! (cons a l), as the generated code builds a call's list
  function rt_cons(a, l) result(r)
    type(value), intent(in) :: a, l
    type(value) :: r
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, a)
    call vs_set(vst, base + 2, l)
    r = gcl_cons(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function rt_cons

  function rt_prim3(op, a, b, c) result(r)
    type(value), intent(in) :: op, a, b, c
    type(value) :: r
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, a)
    call vs_set(vst, base + 2, b)
    call vs_set(vst, base + 3, c)
    r = dispatch(op, base, 3)
    call vs_leave(vst, base)
  end function rt_prim3

  ! op on the n values in slots argbase+1 ..
  function dispatch(op, argbase, n) result(r)
    type(value), intent(in) :: op
    integer, intent(in) :: argbase, n
    type(value) :: r, a
    type(gc_stack), pointer :: vst
    logical :: ok
    vst => gc_my_stack()
    r = gc_nil()
    if (gc_kind(op) == OBJ_AST) then
       call vmrt_node(op, argbase, n, r, ok)
       if (.not. ok) r = vmrt_throw_of(r)
       return
    end if
    ! an op keyword is the translator's or the generated code's, made by
    ! rt_keyword from its cache: the same object, so identity is the test
    if (op%tag == GCT_KEY) then
       if (op%ref == kw_arg%ref) then
          a = vs_get(vst, argbase + 1)
          if (n == 1 .and. a%tag == GCT_INT) r = vst%vstack(vst%vm_args_rb + int(a%ival) + 1)
          return
       else if (op%ref == kw_arity%ref) then
          call vmrt_arity(op, argbase, n, r, ok)
          if (.not. ok) r = vmrt_throw_of(r)
          return
       else if (op%ref == kw_deref%ref) then
          if (n == 1) r = vmrt_deref(vs_get(vst, argbase + 1))
          return
       else if (op%ref == kw_callw%ref) then
          ! (callw var args ..): the var's value called on the args
          if (n >= 1) then
             call vs_set(vst, argbase + 1, vmrt_deref(vs_get(vst, argbase + 1)))
             call vmrt_call(vs_get(vst, argbase + 1), argbase + 1, n - 1, r, ok)
             if (.not. ok) r = vmrt_throw_of(r)
          end if
          return
       else if (op%ref == kw_invoke%ref .or. op%ref == kw_invoke_m%ref) then
          if (n >= 1) then
             call vmrt_call(vs_get(vst, argbase + 1), argbase + 1, n - 1, r, ok)
             if (.not. ok) r = vmrt_throw_of(r)
          end if
          return
       end if
    end if
    call vmrt_call(op, argbase, n, r, ok)
    if (.not. ok) r = vmrt_throw_of(r)
  end function dispatch

  ! ---- the compiler's arrays, resized as ACL2 resizes them: the elements
  ! kept, the new ones the initial value ----------------------------------------------

  subroutine rt_resize_int(a, n)
    integer(int64), pointer, contiguous, intent(inout) :: a(:)
    integer(int64), intent(in) :: n
    integer(int64), pointer, contiguous :: t(:)
    integer(int64) :: m
    allocate(t(0:n-1))
    t = 0
    m = 0
    if (associated(a)) then
       m = min(n, size(a, kind=int64))
       if (m > 0) t(0:m-1) = a(0:m-1)
       deallocate(a)
    end if
    a => t
  end subroutine rt_resize_int

  subroutine rt_resize_val(a, n)
    type(value), pointer, contiguous, intent(inout) :: a(:)
    integer(int64), intent(in) :: n
    type(value), pointer, contiguous :: t(:)
    integer(int64) :: m
    allocate(t(0:n-1))
    t = gc_nil()
    m = 0
    if (associated(a)) then
       m = min(n, size(a, kind=int64))
       if (m > 0) t(0:m-1) = a(0:m-1)
       deallocate(a)
    end if
    a => t
  end subroutine rt_resize_val

end module vm_runtime

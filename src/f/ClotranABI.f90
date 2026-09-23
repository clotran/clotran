! ClotranABI: the runtime, reachable through the C calling convention.
!
! WHY THIS EXISTS. Two things need to call clotran's runtime from code
! that was not compiled with clotran's own compiler:
!
!   - a COMPILED NAMESPACE, generated as Fortran from a .cljf file and
!     built into a package (PLAN step 10);
!   - an EMBEDDER -- a Fortran or C program that owns `main` and wants
!     to call Clojure functions, which is how a callback handed to an
!     ODE solver gets back here.
!
! Neither can `use GC`. A Fortran module file is a private format, tied
! to one compiler and one version of it, so a library built with
! gfortran 13 cannot `use` a module built by gfortran 14, let alone by
! flang -- and `make crosscheck` builds with both. The C calling
! convention is the one thing every compiler agrees on, which is why
! the package door (DynLoad.f90) already speaks it. There is no C
! source here: `bind(C)` and `iso_c_binding` are Fortran.
!
! A statically linked build does not need this and could `use GC`
! directly. It goes through here anyway, so that one surface is
! exercised by every path and the generator emits one kind of call.
!
! THE MODEL IS JNI'S, AND FOR JNI'S REASON. Values are not passed
! across this boundary. They live in SLOTS on the shadow stack, and
! every entry point names a slot by its integer index. The collector
! already scans the shadow stack, so anything reachable from outside is
! rooted by construction, and no caller can hold a value in a register
! across an allocation -- which is the bug this codebase has paid for
! twice (NOTES.md, "Rooting: two allocations in one argument list").
!
! The cost is a slot write per intermediate. That is the "root
! everything, stupidly" position PLAN calls for; a value-passing fast
! path is a later optimisation with a measurement behind it, not a
! starting point.
!
! CONVENTIONS.
!   - every name is `clotran_*`, and that prefix is reserved for it
!   - a slot argument is `integer(c_int)`, by value
!   - a function that can fail returns `integer(c_int)`: 0 is success
!   - nothing here throws; errors are read with clotran_has_error
!   - the caller opens a frame, uses slots base+1 .. base+n, and leaves
module ClotranABI
  use iso_c_binding
  use GC
  use PersistentVector
  use LispReader
  use Namespace
  use Eval
  implicit none
  private

  ! Everything public here is public BECAUSE it is bind(C); the module
  ! is never `use`d by generated code, only linked against.
  public :: clotran_init, clotran_boot, clotran_eval, clotran_frame_enter, clotran_frame_leave, clotran_frame_depth
  public :: clotran_set_nil, clotran_set_int, clotran_set_real, clotran_set_bool
  public :: clotran_set_str, clotran_copy
  public :: clotran_tag, clotran_int, clotran_real, clotran_bool
  public :: clotran_str_len, clotran_str_copy
  public :: clotran_vec_empty, clotran_vec_conj, clotran_vec_count, clotran_vec_nth
  public :: clotran_var, clotran_deref, clotran_call
  public :: clotran_has_error, clotran_error_len, clotran_error_copy, clotran_clear_error
  public :: clotran_collect, clotran_live_count, clotran_set_torture

contains

  ! --- lifetime ----------------------------------------------------

  ! Brings the heap up if it is not already. Safe to call more than
  ! once, and an embedder must call it before anything else. A compiled
  ! namespace loaded into a running clotran does not need it, but
  ! calling it costs a comparison.
  subroutine clotran_init() bind(C, name="clotran_init")
    call gc_ensure_init()
  end subroutine clotran_init

  ! Builds the global environment: the namespaces, the builtins bound
  ! into clojure.core, the printer and reader hooks. An EMBEDDER must
  ! call this once, after clotran_init and before anything else. Code
  ! loaded into a running clotran must NOT: the environment is already
  ! there and a second one would orphan every namespace in the first.
  !
  ! `home` is the directory holding src/clj, for the files core.clj
  ! loads. Nothing is read here -- the builtins alone are enough for
  ! arithmetic -- so a caller that wants the language says so by
  ! evaluating (load-file ...) afterwards.
  function clotran_boot(home, n) bind(C, name="clotran_boot") result(st)
    character(kind=c_char), intent(in) :: home(*)
    integer(c_int), value :: n
    integer(c_int) :: st
    type(gc_value) :: none(0), env
    call gc_ensure_init()
    call gce_set_home(c_text(home, n))
    env = gce_base_env(none)
    st = 0
    if (gce_has_error()) st = 1
  end function clotran_boot

  ! Reads ONE form from the text, analyses it and evaluates it into
  ! the slot. 0 when it answered, 1 when it raised. This is `eval` for
  ! an embedder; generated code does not use it, since its forms were
  ! analysed at compile time.
  function clotran_eval(src, n, dst) bind(C, name="clotran_eval") result(st)
    character(kind=c_char), intent(in) :: src(*)
    integer(c_int), value :: n, dst
    integer(c_int) :: st
    type(gc_value) :: form, node, env, none(0)
    integer :: base
    st = 1
    call vs_set(int(dst), gc_nil())
    env = gce_env()
    base = vs_enter(3)
    call vs_set(base + 1, env)
    form = gcr_read(c_text(src, n), [vs_get(base + 1)])
    if (gcr_has_error()) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 2, form)
    node = gce_analyze(vs_get(base + 2), vs_get(base + 1))
    if (gce_has_error()) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, node)
    form = gce_eval(vs_get(base + 3), vs_get(base + 1), none)
    if (.not. gce_has_error()) then
       call vs_set(int(dst), form)
       st = 0
    end if
    call vs_leave(base)
  end function clotran_eval

  ! --- frames ------------------------------------------------------

  ! Reserves n slots and answers the base. Slots are base+1 .. base+n,
  ! each starting nil. Pass the base back to clotran_frame_leave.
  function clotran_frame_enter(n) bind(C, name="clotran_frame_enter") result(base)
    integer(c_int), value :: n
    integer(c_int) :: base
    base = int(vs_enter(int(n)), c_int)
  end function clotran_frame_enter

  subroutine clotran_frame_leave(base) bind(C, name="clotran_frame_leave")
    integer(c_int), value :: base
    call vs_leave(int(base))
  end subroutine clotran_frame_leave

  function clotran_frame_depth() bind(C, name="clotran_frame_depth") result(n)
    integer(c_int) :: n
    n = int(vs_depth(), c_int)
  end function clotran_frame_depth

  ! --- writing values into slots -----------------------------------

  subroutine clotran_set_nil(slot) bind(C, name="clotran_set_nil")
    integer(c_int), value :: slot
    call vs_set(int(slot), gc_nil())
  end subroutine clotran_set_nil

  subroutine clotran_set_int(slot, n) bind(C, name="clotran_set_int")
    integer(c_int), value :: slot
    integer(c_int64_t), value :: n
    call vs_set(int(slot), gc_int(int(n, gc_ip)))
  end subroutine clotran_set_int

  subroutine clotran_set_real(slot, x) bind(C, name="clotran_set_real")
    integer(c_int), value :: slot
    real(c_double), value :: x
    call vs_set(int(slot), gc_real(real(x, gc_dp)))
  end subroutine clotran_set_real

  subroutine clotran_set_bool(slot, b) bind(C, name="clotran_set_bool")
    integer(c_int), value :: slot, b
    call vs_set(int(slot), gc_bool(b /= 0))
  end subroutine clotran_set_bool

  ! The bytes are UTF-8 and are COPIED into the string pool, so the
  ! caller's buffer is its own business afterwards. n is a byte count,
  ! not a character count (DEVIATIONS 41: a string is code points).
  subroutine clotran_set_str(slot, chars, n) bind(C, name="clotran_set_str")
    integer(c_int), value :: slot
    character(kind=c_char), intent(in) :: chars(*)
    integer(c_int), value :: n
    character(len=:), allocatable :: s
    type(gc_value) :: none(0)
    integer :: i
    allocate(character(len=max(0, int(n))) :: s)
    do i = 1, int(n)
       s(i:i) = chars(i)
    end do
    ! The shadow stack IS the root set, so an allocation here needs no
    ! roots argument: everything the caller holds is already in a slot.
    call vs_set(int(slot), gc_str(s, none))
  end subroutine clotran_set_str

  subroutine clotran_copy(dst, src) bind(C, name="clotran_copy")
    integer(c_int), value :: dst, src
    call vs_set(int(dst), vs_get(int(src)))
  end subroutine clotran_copy

  ! --- reading values out of slots ---------------------------------

  ! The GCT_* constant. Generated code switches on it the way exec.inc
  ! switches on a node kind.
  function clotran_tag(slot) bind(C, name="clotran_tag") result(t)
    integer(c_int), value :: slot
    integer(c_int) :: t
    type(gc_value) :: v
    v = vs_get(int(slot))
    t = int(v%tag, c_int)
  end function clotran_tag

  function clotran_int(slot) bind(C, name="clotran_int") result(n)
    integer(c_int), value :: slot
    integer(c_int64_t) :: n
    type(gc_value) :: v
    v = vs_get(int(slot))
    n = int(v%ival, c_int64_t)
  end function clotran_int

  function clotran_real(slot) bind(C, name="clotran_real") result(x)
    integer(c_int), value :: slot
    real(c_double) :: x
    type(gc_value) :: v
    v = vs_get(int(slot))
    x = real(v%rval, c_double)
  end function clotran_real

  ! Clojure truthiness, not a tag test: everything but nil and false.
  function clotran_bool(slot) bind(C, name="clotran_bool") result(b)
    integer(c_int), value :: slot
    integer(c_int) :: b
    type(gc_value) :: v
    v = vs_get(int(slot))
    b = 1
    if (v%tag == GCT_NIL) b = 0
    if (v%tag == GCT_BOOL .and. v%ival == 0) b = 0
  end function clotran_bool

  ! Bytes, so that a caller can size its buffer before copying.
  function clotran_str_len(slot) bind(C, name="clotran_str_len") result(n)
    integer(c_int), value :: slot
    integer(c_int) :: n
    type(gc_value) :: v
    v = vs_get(int(slot))
    n = 0
    if (v%tag == GCT_STR) n = int(len(gc_ref_text(v%ref)), c_int)
  end function clotran_str_len

  ! Copies at most n bytes and answers how many were written.
  function clotran_str_copy(slot, buf, n) bind(C, name="clotran_str_copy") result(w)
    integer(c_int), value :: slot
    character(kind=c_char), intent(out) :: buf(*)
    integer(c_int), value :: n
    integer(c_int) :: w
    type(gc_value) :: v
    character(len=:), allocatable :: s
    integer :: i
    w = 0
    v = vs_get(int(slot))
    if (v%tag /= GCT_STR) return
    s = gc_ref_text(v%ref)
    w = int(min(len(s), int(n)), c_int)
    do i = 1, int(w)
       buf(i) = s(i:i)
    end do
  end function clotran_str_copy

  ! --- vectors -----------------------------------------------------
  !
  ! A vector is how arguments reach `apply`, so these four are the
  ! minimum a call needs. Maps and the rest follow the same shape.

  subroutine clotran_vec_empty(slot) bind(C, name="clotran_vec_empty")
    integer(c_int), value :: slot
    type(gc_value) :: none(0)
    call vs_set(int(slot), gcv_empty(none))
  end subroutine clotran_vec_empty

  ! dst may be the same slot as vec; the result is written last.
  subroutine clotran_vec_conj(dst, vec, x) bind(C, name="clotran_vec_conj")
    integer(c_int), value :: dst, vec, x
    type(gc_value) :: out
    type(gc_value) :: none(0)
    out = gcv_conj(vs_get(int(vec)), vs_get(int(x)), none)
    call vs_set(int(dst), out)
  end subroutine clotran_vec_conj

  function clotran_vec_count(slot) bind(C, name="clotran_vec_count") result(n)
    integer(c_int), value :: slot
    integer(c_int) :: n
    n = int(gcv_count(vs_get(int(slot))), c_int)
  end function clotran_vec_count

  ! Zero-based, as gcv_nth is; out of range gives nil.
  subroutine clotran_vec_nth(dst, vec, i) bind(C, name="clotran_vec_nth")
    integer(c_int), value :: dst, vec, i
    call vs_set(int(dst), gcv_nth(vs_get(int(vec)), int(i)))
  end subroutine clotran_vec_nth

  ! --- vars and calling --------------------------------------------

  ! Resolves ns/name to its Var and writes it to the slot. 1 when it
  ! was found, 0 when it was not. A compiled call site looks a Var up
  ! ONCE and keeps the handle, which is what makes redefinition at the
  ! REPL still visible to compiled code.
  function clotran_var(slot, ns, nsn, name, namen) bind(C, name="clotran_var") result(ok)
    integer(c_int), value :: slot
    character(kind=c_char), intent(in) :: ns(*), name(*)
    integer(c_int), value :: nsn, namen
    integer(c_int) :: ok
    type(gc_value) :: nsv, sym, var
    integer :: base
    ok = 0
    call vs_set(int(slot), gc_nil())
    nsv = gcn_find(c_text(ns, nsn))
    if (gc_kind(nsv) /= OBJ_NS) return
    base = vs_enter(1)
    call vs_set(base + 1, nsv)
    sym = gc_sym(c_text(name, namen), [vs_get(base + 1)])
    var = gcn_lookup(vs_get(base + 1), sym)
    call vs_leave(base)
    if (.not. gcn_is_var(var)) return
    call vs_set(int(slot), var)
    ok = 1
  end function clotran_var

  subroutine clotran_deref(dst, var) bind(C, name="clotran_deref")
    integer(c_int), value :: dst, var
    call vs_set(int(dst), gcn_var_value(vs_get(int(var))))
  end subroutine clotran_deref

  ! (apply fn args), with args a vector. 0 when it returned, 1 when it
  ! raised -- and on 1 the destination slot is nil and the error is
  ! readable with clotran_error_copy. An error CANNOT be allowed to
  ! unwind through a caller's frames, which is why this reports rather
  ! than throws; the same reason JNI makes you check.
  function clotran_call(dst, fn, args) bind(C, name="clotran_call") result(st)
    integer(c_int), value :: dst, fn, args
    integer(c_int) :: st
    type(gc_value) :: out
    out = gce_apply(vs_get(int(fn)), vs_get(int(args)))
    if (gce_has_error()) then
       call vs_set(int(dst), gc_nil())
       st = 1
    else
       call vs_set(int(dst), out)
       st = 0
    end if
  end function clotran_call

  ! --- errors ------------------------------------------------------

  function clotran_has_error() bind(C, name="clotran_has_error") result(b)
    integer(c_int) :: b
    b = 0
    if (gce_has_error()) b = 1
  end function clotran_has_error

  function clotran_error_len() bind(C, name="clotran_error_len") result(n)
    integer(c_int) :: n
    n = int(len(gce_error()), c_int)
  end function clotran_error_len

  function clotran_error_copy(buf, n) bind(C, name="clotran_error_copy") result(w)
    character(kind=c_char), intent(out) :: buf(*)
    integer(c_int), value :: n
    integer(c_int) :: w
    character(len=:), allocatable :: s
    integer :: i
    s = gce_error()
    w = int(min(len(s), int(n)), c_int)
    do i = 1, int(w)
       buf(i) = s(i:i)
    end do
  end function clotran_error_copy

  subroutine clotran_clear_error() bind(C, name="clotran_clear_error")
    call gce_clear_error()
  end subroutine clotran_clear_error

  ! --- the collector -----------------------------------------------

  ! Forces a collection. Not something generated code calls in anger;
  ! it is here so a test can prove that a value held only in a slot
  ! SURVIVES one, which is the whole claim this module makes.
  subroutine clotran_collect() bind(C, name="clotran_collect")
    type(gc_value) :: none(0)
    call gc_collect(none)
  end subroutine clotran_collect

  ! Collect at EVERY allocation. The only way a rooting mistake in
  ! foreign code shows up reliably: a value the caller failed to put
  ! in a slot is then freed before the next line rather than in an
  ! hour. Ruinously slow, and exactly what a test wants.
  subroutine clotran_set_torture(on) bind(C, name="clotran_set_torture")
    integer(c_int), value :: on
    gc_torture = (on /= 0)
  end subroutine clotran_set_torture

  function clotran_live_count() bind(C, name="clotran_live_count") result(n)
    integer(c_int) :: n
    n = int(gc_live_count(), c_int)
  end function clotran_live_count

  ! --- helpers, not exported ---------------------------------------

  ! A C character array and a length as a Fortran string.
  function c_text(chars, n) result(s)
    character(kind=c_char), intent(in) :: chars(*)
    integer(c_int), intent(in) :: n
    character(len=:), allocatable :: s
    integer :: i
    allocate(character(len=max(0, int(n))) :: s)
    do i = 1, int(n)
       s(i:i) = chars(i)
    end do
  end function c_text

  ! NOTE on roots: every allocation here passes an EMPTY roots array,
  ! on purpose. The shadow stack is the root set, and a caller that did
  ! not put its value in a slot has already lost it.

end module ClotranABI

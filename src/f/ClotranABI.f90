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
  use PersistentList
  use LispReader
  use CompiledFn
  use DynLoad
  use NativeArray
  use Namespace
  use Eval
  implicit none
  private

  ! Everything public here is public BECAUSE it is bind(C); the module
  ! is never `use`d by generated code, only linked against.
  public :: clotran_stack, clotran_slots
  public :: clotran_init, clotran_boot, clotran_eval, clotran_analyze, clotran_frame_enter, clotran_frame_leave, clotran_frame_depth
  public :: clotran_set_nil, clotran_set_int, clotran_set_real, clotran_set_bool
  public :: clotran_set_str, clotran_copy
  public :: clotran_tag, clotran_int, clotran_real, clotran_bool
  public :: clotran_str_len, clotran_str_copy
  public :: clotran_vec_empty, clotran_vec_conj, clotran_vec_count, clotran_vec_nth
  public :: clotran_var, clotran_deref, clotran_call, clotran_call_slots, clotran_def_fn
  public :: clotran_has_error, clotran_error_len, clotran_error_copy, clotran_clear_error
  public :: clotran_collect, clotran_live_count, clotran_set_torture
  public :: clotran_frame_new, clotran_frame_get, clotran_frame_put
  public :: clotran_eval_node, clotran_pool_register, clotran_pool_get
  public :: clotran_load_compiled, clotran_array_view
  public :: clotran_rest_args, clotran_arity_error
  public :: clotran_native_begin, clotran_reacquire
  public :: clotran_register_proc, clotran_make_closure, clotran_captures, clotran_new, clotran_dot, clotran_arith, clotran_frame_done, clotran_poll

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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call gc_ensure_init()
    block
       call c_text(home, n, s=dlt_1)
       call gce_set_home(dlt_1)
    end block
    env = gce_base_env(none)
    st = 0
    if (gce_has_error()) st = 1
  end function clotran_boot

  ! Reads ONE form from the text, analyses it and evaluates it into
  ! the slot. 0 when it answered, 1 when it raised. This is `eval` for
  ! an embedder; generated code does not use it, since its forms were
  ! analysed at compile time.
  function clotran_eval(src, n, dst) bind(C, name="clotran_eval") result(st)
    type(gc_stack), pointer :: vst
    character(kind=c_char), intent(in) :: src(*)
    integer(c_int), value :: n, dst
    integer(c_int) :: st
    type(gc_value) :: form, node, env, none(0)
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    st = 1
    call vs_set(vst, int(dst), gc_nil())
    env = gce_env()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, env)
    block
       call c_text(src, n, s=dlt_1)
       form = gcr_read(dlt_1, [vs_get(vst, base + 1)])
    end block
    if (gcr_has_error()) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 2, form)
    node = gce_analyze(vs_get(vst, base + 2), vs_get(vst, base + 1))
    if (gce_has_error()) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, node)
    form = gce_eval(vs_get(vst, base + 3), vs_get(vst, base + 1), none)
    if (.not. gce_has_error()) then
       call vs_set(vst, int(dst), form)
       st = 0
    end if
    call vs_leave(vst, base)
  end function clotran_eval

  ! Reads and ANALYSES one form, leaving the node in the slot without
  ! running it. This is what a compiler driver calls: the nodes it
  ! puts in a namespace's constant pool, for the escape hatch to run,
  ! come from here. Analysis is the same pass the executor uses, so
  ! there is no second front end to disagree with the first.
  function clotran_analyze(src, n, dst) bind(C, name="clotran_analyze") result(st)
    type(gc_stack), pointer :: vst
    character(kind=c_char), intent(in) :: src(*)
    integer(c_int), value :: n, dst
    integer(c_int) :: st
    type(gc_value) :: form, node, env
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    st = 1
    call vs_set(vst, int(dst), gc_nil())
    env = gce_env()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, env)
    block
       call c_text(src, n, s=dlt_1)
       form = gcr_read(dlt_1, [vs_get(vst, base + 1)])
    end block
    if (gcr_has_error()) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 2, form)
    node = gce_analyze(vs_get(vst, base + 2), vs_get(vst, base + 1))
    if (.not. gce_has_error()) then
       call vs_set(vst, int(dst), node)
       st = 0
    end if
    call vs_leave(vst, base)
  end function clotran_analyze

  ! --- frames ------------------------------------------------------

  ! This thread's value stack, for the entries below that take it as
  ! their first argument. A generated procedure fetches it ONCE: each
  ! fetch is a thread-key lookup, and an entry that made its own was
  ! ~20 lookups per compiled (+ a b), 29% of a reduce's time (dtrace).
  function clotran_stack() bind(C, name="clotran_stack") result(cs)
    type(c_ptr) :: cs
    type(gc_stack), pointer :: vst
    vst => gc_my_stack()
    cs = c_loc(vst)
  end function clotran_stack

  ! The stack's slots themselves, for generated code to read and write
  ! directly as clotran_val (compiler.cljf): the address of slot 1 and
  ! how many there are. The stack never moves (GC.f90, vstack_make), so
  ! the view holds for the thread's life. The layout is checked once:
  ! a 32-bit tag, a 32-bit pool index, a 64-bit payload.
  function clotran_slots(cs, n) bind(C, name="clotran_slots") result(p)
    type(c_ptr), value :: cs
    integer(c_int), intent(out) :: n
    type(c_ptr) :: p
    type(gc_stack), pointer :: vst
    logical, save :: checked = .false.
    integer(c_int64_t) :: w(2)
    if (.not. checked) then
       w = transfer(gc_value(tag=7, ref=9, ival=-5_gc_ip), w)
       if (storage_size(gc_value()) /= 128 .or. w(1) /= 7 + 9 * 4294967296_c_int64_t .or. w(2) /= -5) &
            error stop "clotran: a value is not laid out as compiled code reads it"
       checked = .true.
    end if
    call c_f_pointer(cs, vst)
    n = int(size(vst%vstack), c_int)
    p = c_loc(vst%vstack(1))
  end function clotran_slots

  ! Reserves n slots and answers the base. Slots are base+1 .. base+n,
  ! each starting nil. Pass the base back to clotran_frame_leave.
  function clotran_frame_enter(cs, n) bind(C, name="clotran_frame_enter") result(base)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: n
    integer(c_int) :: base
    call c_f_pointer(cs, vst)
    base = int(vs_enter(vst, int(n)), c_int)
  end function clotran_frame_enter

  subroutine clotran_frame_leave(cs, base) bind(C, name="clotran_frame_leave")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: base
    call c_f_pointer(cs, vst)
    call vs_leave(vst, int(base))
  end subroutine clotran_frame_leave

  ! The end of a GENERATED procedure: its frame (slot base+1, where
  ! clotran_frame_new put it) is kept for reuse, then the slots go.
  ! Only generated code calls this -- another caller of frame_enter may
  ! keep its own vector at base+1 -- and nothing holds a compiled frame
  ! once its call returns: a break copies locals out, an interpreted
  ! subtree runs inside the call, a closure copies its captures.
  subroutine clotran_frame_done(cs, base) bind(C, name="clotran_frame_done")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: base
    call c_f_pointer(cs, vst)
    call gc_frame_give(vst, vs_get(vst, int(base) + 1))
    call vs_leave(vst, int(base))
  end subroutine clotran_frame_done

  function clotran_frame_depth() bind(C, name="clotran_frame_depth") result(n)
    type(gc_stack), pointer :: vst
    integer(c_int) :: n
    vst => gc_my_stack()
    n = int(vs_depth(vst), c_int)
  end function clotran_frame_depth

  ! --- writing values into slots -----------------------------------

  subroutine clotran_set_nil(cs, slot) bind(C, name="clotran_set_nil")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(slot), gc_nil())
  end subroutine clotran_set_nil

  subroutine clotran_set_int(cs, slot, n) bind(C, name="clotran_set_int")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int64_t), value :: n
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(slot), gc_int(int(n, gc_ip)))
  end subroutine clotran_set_int

  subroutine clotran_set_real(cs, slot, x) bind(C, name="clotran_set_real")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    real(c_double), value :: x
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(slot), gc_real(real(x, gc_dp)))
  end subroutine clotran_set_real

  subroutine clotran_set_bool(cs, slot, b) bind(C, name="clotran_set_bool")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot, b
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(slot), gc_bool(b /= 0))
  end subroutine clotran_set_bool

  ! The bytes are UTF-8 and are COPIED into the string pool, so the
  ! caller's buffer is its own business afterwards. n is a byte count,
  ! not a character count (DEVIATIONS 41: a string is code points).
  subroutine clotran_set_str(cs, slot, chars, n) bind(C, name="clotran_set_str")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    character(kind=c_char), intent(in) :: chars(*)
    integer(c_int), value :: n
    character(len=:), allocatable :: s
    type(gc_value) :: none(0)
    integer :: i
    call c_f_pointer(cs, vst)
    allocate(character(len=max(0, int(n))) :: s)
    do i = 1, int(n)
       s(i:i) = chars(i)
    end do
    ! The shadow stack IS the root set, so an allocation here needs no
    ! roots argument: everything the caller holds is already in a slot.
    call vs_set(vst, int(slot), gc_str(s, none))
  end subroutine clotran_set_str

  subroutine clotran_copy(cs, dst, src) bind(C, name="clotran_copy")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, src
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(dst), vs_get(vst, int(src)))
  end subroutine clotran_copy

  ! --- reading values out of slots ---------------------------------

  ! The GCT_* constant. Generated code switches on it the way exec.inc
  ! switches on a node kind.
  function clotran_tag(cs, slot) bind(C, name="clotran_tag") result(t)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int) :: t
    type(gc_value) :: v
    call c_f_pointer(cs, vst)
    v = vs_get(vst, int(slot))
    t = int(v%tag, c_int)
  end function clotran_tag

  function clotran_int(cs, slot) bind(C, name="clotran_int") result(n)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int64_t) :: n
    type(gc_value) :: v
    call c_f_pointer(cs, vst)
    v = vs_get(vst, int(slot))
    n = int(v%ival, c_int64_t)
  end function clotran_int

  function clotran_real(cs, slot) bind(C, name="clotran_real") result(x)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    real(c_double) :: x
    type(gc_value) :: v
    call c_f_pointer(cs, vst)
    v = vs_get(vst, int(slot))
    x = real(gc_rval(v), c_double)
  end function clotran_real

  ! Clojure truthiness, not a tag test: everything but nil and false.
  function clotran_bool(cs, slot) bind(C, name="clotran_bool") result(b)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int) :: b
    type(gc_value) :: v
    call c_f_pointer(cs, vst)
    v = vs_get(vst, int(slot))
    b = 1
    if (v%tag == GCT_NIL) b = 0
    if (v%tag == GCT_BOOL .and. v%ival == 0) b = 0
  end function clotran_bool

  ! Bytes, so that a caller can size its buffer before copying.
  function clotran_str_len(slot) bind(C, name="clotran_str_len") result(n)
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int) :: n
    type(gc_value) :: v
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    v = vs_get(vst, int(slot))
    n = 0
    if (v%tag == GCT_STR) then
       block
          call gc_ref_text(v%ref, s=dlt_1)
          n = int(len(dlt_1), c_int)
       end block
    end if
  end function clotran_str_len

  ! Copies at most n bytes and answers how many were written.
  function clotran_str_copy(slot, buf, n) bind(C, name="clotran_str_copy") result(w)
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    character(kind=c_char), intent(out) :: buf(*)
    integer(c_int), value :: n
    integer(c_int) :: w
    type(gc_value) :: v
    character(len=:), allocatable :: s
    integer :: i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    w = 0
    v = vs_get(vst, int(slot))
    if (v%tag /= GCT_STR) return
    block
       call gc_ref_text(v%ref, s=dlt_1)
       s = dlt_1
    end block
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
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    type(gc_value) :: none(0)
    vst => gc_my_stack()
    call vs_set(vst, int(slot), gcv_empty(none))
  end subroutine clotran_vec_empty

  ! dst may be the same slot as vec; the result is written last.
  subroutine clotran_vec_conj(dst, vec, x) bind(C, name="clotran_vec_conj")
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, vec, x
    type(gc_value) :: out
    type(gc_value) :: none(0)
    vst => gc_my_stack()
    out = gcv_conj(vs_get(vst, int(vec)), vs_get(vst, int(x)), none)
    call vs_set(vst, int(dst), out)
  end subroutine clotran_vec_conj

  function clotran_vec_count(slot) bind(C, name="clotran_vec_count") result(n)
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int) :: n
    vst => gc_my_stack()
    n = int(gcv_count(vs_get(vst, int(slot))), c_int)
  end function clotran_vec_count

  ! Zero-based, as gcv_nth is; out of range gives nil.
  subroutine clotran_vec_nth(dst, vec, i) bind(C, name="clotran_vec_nth")
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, vec, i
    vst => gc_my_stack()
    call vs_set(vst, int(dst), gcv_nth(vs_get(vst, int(vec)), int(i)))
  end subroutine clotran_vec_nth

  ! --- vars and calling --------------------------------------------

  ! Resolves ns/name to its Var and writes it to the slot. 1 when it
  ! was found, 0 when it was not. A compiled call site looks a Var up
  ! ONCE and keeps the handle, which is what makes redefinition at the
  ! REPL still visible to compiled code.
  function clotran_var(slot, ns, nsn, name, namen) bind(C, name="clotran_var") result(ok)
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    character(kind=c_char), intent(in) :: ns(*), name(*)
    integer(c_int), value :: nsn, namen
    integer(c_int) :: ok
    type(gc_value) :: nsv, sym, var
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    ok = 0
    call vs_set(vst, int(slot), gc_nil())
    block
       call c_text(ns, nsn, s=dlt_1)
       nsv = gcn_find(dlt_1)
    end block
    if (gc_kind(nsv) /= OBJ_NS) return
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, nsv)
    block
       call c_text(name, namen, s=dlt_1)
       sym = gc_sym(dlt_1, [vs_get(vst, base + 1)])
    end block
    var = gcn_lookup(vs_get(vst, base + 1), sym)
    call vs_leave(vst, base)
    if (.not. gcn_is_var(var)) return
    call vs_set(vst, int(slot), var)
    ok = 1
  end function clotran_var

  subroutine clotran_deref(cs, dst, var) bind(C, name="clotran_deref")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, var
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(dst), gcn_var_value(vs_get(vst, int(var))))
  end subroutine clotran_deref

  ! (apply fn args), with args a vector. 0 when it returned, 1 when it
  ! raised -- and on 1 the destination slot is nil and the error is
  ! readable with clotran_error_copy. An error CANNOT be allowed to
  ! unwind through a caller's frames, which is why this reports rather
  ! than throws; the same reason JNI makes you check.
  function clotran_call(dst, fn, args) bind(C, name="clotran_call") result(st)
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, fn, args
    integer(c_int) :: st
    type(gc_value) :: out
    vst => gc_my_stack()
    out = gce_apply(vs_get(vst, int(fn)), vs_get(vst, int(args)))
    if (gce_has_error()) then
       call vs_set(vst, int(dst), gc_nil())
       st = 1
    else
       call vs_set(vst, int(dst), out)
       st = 0
    end if
  end function clotran_call

  ! Installs a COMPILED PROCEDURE as ns/name. This is what a compiled
  ! namespace calls once per function when its library is loaded: the
  ! procedure goes in CompiledFn's table, an OBJ_COMPILED value names
  ! its handle, and the Var is interned to hold it. Everything that
  ! already refers to that Var -- interpreted code, other compiled
  ! code -- reaches the new procedure on its next call, because a call
  ! goes through the Var. That is the whole interactive story.
  !
  ! arity is the fixed argument count, or -1 to accept any and let the
  ! procedure check for itself.
  function clotran_def_fn(ns, nsn, name, namen, fp, arity) &
       bind(C, name="clotran_def_fn") result(st)
    type(gc_stack), pointer :: vst
    character(kind=c_char), intent(in) :: ns(*), name(*)
    integer(c_int), value :: nsn, namen, arity
    type(c_funptr), value :: fp
    integer(c_int) :: st
    type(gc_value) :: nsv, sym, fnv, var, none(0)
    character(len=:), allocatable :: nsname, fname
    integer :: base, h
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    st = 1
    if (.not. c_associated(fp)) return
    block
       call c_text(ns, nsn, s=dlt_1)
       nsname = dlt_1
    end block
    block
       call c_text(name, namen, s=dlt_1)
       fname = dlt_1
    end block
    nsv = gcn_find_or_create(nsname, none)
    if (gc_kind(nsv) /= OBJ_NS) return
    h = cf_register(fp, nsname // "/" // fname)
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, nsv)
    fnv = gc_str(nsname // "/" // fname, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, fnv)
    fnv = gc_obj(OBJ_COMPILED, [vs_get(vst, base + 2)], &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_i1(fnv, h)
    call gc_set_i2(fnv, int(arity))
    call vs_set(vst, base + 2, fnv)
    sym = gc_sym(fname, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, sym)
    var = gcn_intern(vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_leave(vst, base)
    if (gcn_is_var(var)) st = 0
  end function clotran_def_fn

  ! --- frames, constants, and the way back into the interpreter ------
  !
  ! A generated procedure keeps its locals in an interpreter FRAME, not
  ! in raw shadow-stack slots, and that is a deliberate choice for the
  ! first version. A frame is a gc_vec: one heap allocation per call,
  ! O(1) indexed, already traced. What it buys is that an interpreted
  ! subtree inside compiled code sees the same locals, so the escape
  ! hatch below is one call rather than a bridge -- and the debugger
  ! sees a real frame, which is what makes the debug build cheap.
  ! Raw-slot locals for leaf procedures that never fall back are a
  ! later optimisation, with a measurement behind it.

  ! --- compiled closures (PLAN.md step 10, a) ------------------------
  !
  ! An fn written inside a compiled fn is a procedure of its own in the
  ! same file, registered at install with no Var: its handle is what a
  ! closure made from it carries. The closure is an OBJ_COMPILED like a
  ! defn's, plus what it captured: slot 2 the values (read from the
  ! outer frame when it is made, flat, as the interpreter's closures
  ! are), slot 3 the inner frame slots they go to, slot 4 its self
  ! slot or -1. call_compiled records the fn it enters, and the
  ! procedure's prologue copies these into its new frame first thing.

  function clotran_register_proc(name, namen, fp) bind(C, name="clotran_register_proc") result(h)
    character(kind=c_char), intent(in) :: name(*)
    integer(c_int), value :: namen
    type(c_funptr), value :: fp
    integer(c_int) :: h
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call c_text(name, namen, s=dlt_1)
       h = cf_register(fp, dlt_1)
    end block
  end function clotran_register_proc

  ! pairs(1:2*npairs): (outer slot, inner slot), 0-based, as the
  ! analyser's template lists them
  subroutine clotran_make_closure(cs, dst, h, arity, name, namen, fr, pairs, npairs, selfslot) &
       bind(C, name="clotran_make_closure")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, h, arity, namen, fr, npairs, selfslot
    character(kind=c_char), intent(in) :: name(*)
    integer(c_int), intent(in) :: pairs(*)
    type(gc_value) :: v, none(0)
    integer :: base, k
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call c_f_pointer(cs, vst)
    base = vs_enter(vst, 3)
    v = gc_vec(int(npairs), none)
    call vs_set(vst, base + 1, v)
    do k = 1, npairs
       call gc_vec_set(vs_get(vst, base + 1), k, gc_vec_get(vs_get(vst, int(fr)), int(pairs(2 * k - 1)) + 1))
    end do
    v = gc_vec(int(npairs), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, v)
    do k = 1, npairs
       call gc_vec_set(vs_get(vst, base + 2), k, gc_int(int(pairs(2 * k), gc_ip)))
    end do
    block
       call c_text(name, namen, s=dlt_1)
       v = gc_str(dlt_1, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    end block
    call vs_set(vst, base + 3, v)
    v = gc_obj(OBJ_COMPILED, [vs_get(vst, base + 3), vs_get(vst, base + 1), vs_get(vst, base + 2), &
         gc_int(int(selfslot, gc_ip))], [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call gc_set_i1(v, int(h))
    call gc_set_i2(v, int(arity))
    call vs_set(vst, int(dst), v)
    call vs_leave(vst, base)
  end subroutine clotran_make_closure

  ! The prologue of a closure's procedure: its captures, and itself if
  ! it is named, into its frame. A defn's own fn has none of either.
  subroutine clotran_captures(cs, fr) bind(C, name="clotran_captures")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: fr
    type(gc_value) :: fn, vals, inner, self
    integer :: k
    call c_f_pointer(cs, vst)
    fn = gce_current_fn()
    if (gc_kind(fn) /= OBJ_COMPILED) return
    vals = gc_slot(fn, 2)
    inner = gc_slot(fn, 3)
    if (vals%tag == GCT_VEC) then
       do k = 1, gc_vec_len(vals)
          self = gc_vec_get(inner, k)
          call gc_vec_set(vs_get(vst, int(fr)), int(self%ival) + 1, gc_vec_get(vals, k))
       end do
    end if
    self = gc_slot(fn, 4)
    if (self%tag == GCT_INT) then
       if (self%ival >= 0) call gc_vec_set(vs_get(vst, int(fr)), int(self%ival) + 1, fn)
    end if
  end subroutine clotran_captures

  ! (new Class args...): the arguments in slots argbase+1.., the answer
  ! in dst; 1 if it raised, as clotran_call_slots answers.
  function clotran_new(cs, dst, name, namen, argbase, nargs) bind(C, name="clotran_new") result(st)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, namen, argbase, nargs
    character(kind=c_char), intent(in) :: name(*)
    integer(c_int) :: st
    type(gc_value) :: out
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call c_f_pointer(cs, vst)
    block
       call c_text(name, namen, s=dlt_1)
       out = gce_new_slots(dlt_1, int(argbase), int(nargs))
    end block
    if (gce_has_error()) then
       call vs_set(vst, int(dst), gc_nil())
       st = 1
    else
       call vs_set(vst, int(dst), out)
       st = 0
    end if
  end function clotran_new

  ! (. target member args...): the node in slot `node`, the target in
  ! slot `tv` (unused when from is 0: the node names a class), the
  ! arguments in slots argbase+1..; 1 if it raised.
  function clotran_dot(cs, dst, node, tv, argbase, nargs, from) bind(C, name="clotran_dot") result(st)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, node, tv, argbase, nargs, from
    integer(c_int) :: st
    type(gc_value) :: out
    call c_f_pointer(cs, vst)
    out = gce_dot_slots(vs_get(vst, int(node)), vs_get(vst, int(tv)), int(argbase), int(nargs), int(from))
    if (gce_has_error()) then
       call vs_set(vst, int(dst), gc_nil())
       st = 1
    else
       call vs_set(vst, int(dst), out)
       st = 0
    end if
  end function clotran_dot

  ! A NUMERIC OP ON BOXED OPERANDS -- compiled code whose operands are not
  ! proven primitive: `x` an unhinted parameter, say. Two longs (the sum
  ! still a long) or two doubles are answered here, as Numbers does for
  ! them; anything else -- a ratio, a BigInt, one of each, an overflow,
  ! nil -- goes to the builtin in slot fn exactly as the call would have,
  ! so the answer and the error are the interpreter's. op: 1 + 2 - 3 *
  ! 4 inc 5 dec 6 < 7 > 8 <= 9 >= 10 = 11 == 12 zero? 13 pos? 14 neg?
  function clotran_arith(cs, dst, op, fn, a, b, n) bind(C, name="clotran_arith") result(st)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, op, fn, a, b, n
    integer(c_int) :: st
    integer, parameter :: i16 = selected_int_kind(30)
    integer(i16) :: w
    type(gc_value) :: x, y, out
    logical :: ints, reals
    integer :: base
    call c_f_pointer(cs, vst)
    st = 0
    x = vs_get(vst, int(a))
    y = x
    if (n == 2) y = vs_get(vst, int(b))
    ints = x%tag == GCT_INT .and. y%tag == GCT_INT
    reals = x%tag == GCT_REAL .and. y%tag == GCT_REAL
    select case (op)
    case (1, 2, 3)
       if (n == 2 .and. ints) then
          select case (op)
          case (1); w = int(x%ival, i16) + int(y%ival, i16)
          case (2); w = int(x%ival, i16) - int(y%ival, i16)
          case default; w = int(x%ival, i16) * int(y%ival, i16)
          end select
          if (w >= -huge(x%ival) - 1 .and. w <= huge(x%ival)) then
             call vs_set(vst, int(dst), gc_int(int(w, gc_ip)))
             return
          end if
       else if (n == 2 .and. reals) then
          select case (op)
          case (1); call vs_set(vst, int(dst), gc_real(gc_rval(x) + gc_rval(y)))
          case (2); call vs_set(vst, int(dst), gc_real(gc_rval(x) - gc_rval(y)))
          case default; call vs_set(vst, int(dst), gc_real(gc_rval(x) * gc_rval(y)))
          end select
          return
       end if
    case (4, 5)
       if (x%tag == GCT_INT) then
          if ((op == 4 .and. x%ival < huge(x%ival)) .or. (op == 5 .and. x%ival > -huge(x%ival) - 1)) then
             call vs_set(vst, int(dst), gc_int(x%ival + merge(1_gc_ip, -1_gc_ip, op == 4)))
             return
          end if
       else if (x%tag == GCT_REAL) then
          call vs_set(vst, int(dst), gc_real(gc_rval(x) + merge(1.0_gc_dp, -1.0_gc_dp, op == 4)))
          return
       end if
    case (6, 7, 8, 9, 11)
       if (n == 2 .and. ints) then
          select case (op)
          case (6); call vs_set(vst, int(dst), gc_bool(x%ival < y%ival))
          case (7); call vs_set(vst, int(dst), gc_bool(x%ival > y%ival))
          case (8); call vs_set(vst, int(dst), gc_bool(x%ival <= y%ival))
          case (9); call vs_set(vst, int(dst), gc_bool(x%ival >= y%ival))
          case default; call vs_set(vst, int(dst), gc_bool(x%ival == y%ival))
          end select
          return
       else if (n == 2 .and. reals) then
          select case (op)
          case (6); call vs_set(vst, int(dst), gc_bool(gc_rval(x) < gc_rval(y)))
          case (7); call vs_set(vst, int(dst), gc_bool(gc_rval(x) > gc_rval(y)))
          case (8); call vs_set(vst, int(dst), gc_bool(gc_rval(x) <= gc_rval(y)))
          case (9); call vs_set(vst, int(dst), gc_bool(gc_rval(x) >= gc_rval(y)))
          case default; call vs_set(vst, int(dst), gc_bool(gc_rval(x) == gc_rval(y)))
          end select
          return
       end if
    case (10)
       if (n == 2 .and. ints) then
          call vs_set(vst, int(dst), gc_bool(x%ival == y%ival))
          return
       end if
    case (12, 13, 14)
       if (x%tag == GCT_INT) then
          select case (op)
          case (12); call vs_set(vst, int(dst), gc_bool(x%ival == 0))
          case (13); call vs_set(vst, int(dst), gc_bool(x%ival > 0))
          case default; call vs_set(vst, int(dst), gc_bool(x%ival < 0))
          end select
          return
       end if
    end select
    ! the general path: the builtin, with the operands in consecutive slots
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, x)
    call vs_set(vst, base + 2, y)
    out = gce_apply_slots(vst, vs_get(vst, int(fn)), base, int(n))
    call vs_leave(vst, base)
    if (gce_has_error()) then
       call vs_set(vst, int(dst), gc_nil())
       st = 1
    else
       call vs_set(vst, int(dst), out)
    end if
  end function clotran_arith

  ! A SAFEPOINT at a compiled loop's back-edge (PLAN.md step 14f): a loop
  ! that allocates nothing still stops for a collection elsewhere.
  subroutine clotran_poll() bind(C, name="clotran_poll")
    call gc_poll()
  end subroutine clotran_poll

  subroutine clotran_frame_new(cs, dst, n) bind(C, name="clotran_frame_new")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, n
    type(gc_value) :: none(0)
    type(gc_value) :: v
    call c_f_pointer(cs, vst)
    v = gc_frame_take(vst, int(n))
    if (v%tag /= GCT_VEC) v = gc_vec(max(int(n), 0), none)
    call vs_set(vst, int(dst), v)
  end subroutine clotran_frame_new

  subroutine clotran_frame_get(cs, dst, fr, i) bind(C, name="clotran_frame_get")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, fr, i
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(dst), gc_vec_get(vs_get(vst, int(fr)), int(i) + 1))
  end subroutine clotran_frame_get

  subroutine clotran_frame_put(cs, fr, i, src) bind(C, name="clotran_frame_put")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: fr, i, src
    call c_f_pointer(cs, vst)
    call gc_vec_set(vs_get(vst, int(fr)), int(i) + 1, vs_get(vst, int(src)))
  end subroutine clotran_frame_put

  ! THE ESCAPE HATCH. Runs an already-analysed node in a frame, which is
  ! what a generated procedure does for every node kind the generator
  ! has not learned. It is why the generator is correct from the first
  ! kind it handles: an unhandled construct is slow, not broken.
  function clotran_eval_node(cs, dst, node, fr) bind(C, name="clotran_eval_node") result(st)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, node, fr
    integer(c_int) :: st
    type(gc_value) :: out
    call c_f_pointer(cs, vst)
    out = gce_exec_node(vs_get(vst, int(node)), vs_get(vst, int(fr)))
    if (gce_has_error()) then
       call vs_set(vst, int(dst), gc_nil())
       st = 1
    else
       call vs_set(vst, int(dst), out)
       st = 0
    end if
  end function clotran_eval_node

  ! --- off the baton -------------------------------------------------
  !
  ! Compiled code gives the baton up around a loop that works only on
  ! Fortran numbers and array buffers (clotran.compiler, release-around),
  ! so a task's numeric loop runs while clotran code goes on elsewhere
  ! (PLAN.md step 11, stage 2). Every runtime call inside such a loop is
  ! preceded by clotran_reacquire, so none reaches the heap without it.
  ! An EMBEDDER brackets its own long computation the same way
  ! (examples/embed/heat.f90), so a thread serving a REPL into it is
  ! never held up by a collection waiting on the solver.
  subroutine clotran_native_begin(me, rel) bind(C, name="clotran_native_begin")
    integer(c_int), intent(out) :: me, rel
    integer :: m
    logical :: r
    call gce_native_begin(m, r)
    me = int(m, c_int)
    rel = 0
    if (r) rel = 1
  end subroutine clotran_native_begin

  subroutine clotran_reacquire(me, rel) bind(C, name="clotran_reacquire")
    integer(c_int), value :: me
    integer(c_int), intent(inout) :: rel
    if (rel /= 0) call gce_native_end(int(me))
    rel = 0
  end subroutine clotran_reacquire

  ! --- arities -------------------------------------------------------
  !
  ! A compiled function with several arities, or a variadic one, is ONE
  ! procedure that picks by `nargs` itself, as bind_closure does for an
  ! interpreted one: an exact fixed arity first, then the variadic.

  ! The REST argument of a variadic arity: the arguments in slots
  ! argbase+from+1 .. argbase+nargs as a list, or nil when there are
  ! none -- nil, not the empty list, as bind_closure binds it.
  subroutine clotran_rest_args(cs, dst, argbase, from, nargs) bind(C, name="clotran_rest_args")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, argbase, from, nargs
    type(gc_value) :: rest
    integer :: i
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(dst), gc_nil())
    if (nargs <= from) return
    rest = gcl_empty([vs_get(vst, int(dst))])
    call vs_set(vst, int(dst), rest)
    do i = int(nargs), int(from) + 1, -1
       rest = gcl_cons(vs_get(vst, int(argbase) + i), vs_get(vst, int(dst)), [vs_get(vst, int(dst))])
       call vs_set(vst, int(dst), rest)
    end do
  end subroutine clotran_rest_args

  ! No arity takes `nargs`: Clojure's ArityException, naming the
  ! function as clj does, ns/name.
  subroutine clotran_arity_error(nargs, name, n) bind(C, name="clotran_arity_error")
    integer(c_int), value :: nargs, n
    character(kind=c_char), intent(in) :: name(*)
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call c_text(name, n, s=dlt_1)
       call gce_raise_arity_named(int(nargs), dlt_1)
    end block
  end subroutine clotran_arity_error

  ! A CONSTANT POOL, registered for one compiled namespace. The table
  ! is CompiledFn's, so the Clojure builtin and this entry cannot
  ! drift apart. A generated procedure cannot spell a map, a Var or a
  ! folded function in Fortran, so those live here and it indexes.
  function clotran_pool_register(slot) bind(C, name="clotran_pool_register") result(h)
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot
    integer(c_int) :: h
    vst => gc_my_stack()
    h = int(cf_pool_add(vs_get(vst, int(slot))), c_int)
  end function clotran_pool_register

  subroutine clotran_pool_get(cs, dst, h, i) bind(C, name="clotran_pool_get")
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, h, i
    call c_f_pointer(cs, vst)
    call vs_set(vst, int(dst), cf_pool_get(int(h), int(i)))
  end subroutine clotran_pool_get

  ! A call with the arguments already in consecutive slots
  ! argbase+1 .. argbase+nargs. This is the call a compiled site makes;
  ! clotran_call, which takes a vector, is the general one.
  function clotran_call_slots(cs, dst, fn, argbase, nargs) &
       bind(C, name="clotran_call_slots") result(st)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: dst, fn, argbase, nargs
    integer(c_int) :: st
    type(gc_value) :: out
    call c_f_pointer(cs, vst)
    out = gce_apply_slots(vst, vs_get(vst, int(fn)), int(argbase), int(nargs))
    if (gce_has_error()) then
       call vs_set(vst, int(dst), gc_nil())
       st = 1
    else
       call vs_set(vst, int(dst), out)
       st = 0
    end if
  end function clotran_call_slots

  ! The loader, for an embedder. The logic is DynLoad's, so that the
  ! Clojure builtin and this entry cannot drift apart.
  function clotran_load_compiled(path, n, pool) bind(C, name="clotran_load_compiled") result(st)
    character(kind=c_char), intent(in) :: path(*)
    integer(c_int), value :: n, pool
    integer(c_int) :: st
    character(len=:), allocatable :: err
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    st = 1
    block
       call c_text(path, n, s=dlt_1)
       if (dl_install(dlt_1, int(pool), err)) st = 0
    end block
  end function clotran_load_compiled

  ! A VIEW of a one-dimensional array: the address of its first element
  ! and its length, for compiled code to index directly. kind is 1 for
  ! a double array and 2 for a long array. Answers 1, or 0 when the
  ! value is not an array of that kind, not rank 1, or a slice -- and
  ! then the caller takes its generic path, which is the interpreter's.
  !
  ! The address is good for as long as the array lives: the collector
  ! does not move objects, and the registry keeps each buffer where it
  ! is when it grows.
  function clotran_array_view(cs, slot, kind, ptr, n) bind(C, name="clotran_array_view") result(ok)
    type(c_ptr), value :: cs
    type(gc_stack), pointer :: vst
    integer(c_int), value :: slot, kind
    type(c_ptr), intent(out) :: ptr
    integer(c_int64_t), intent(out) :: n
    integer(c_int) :: ok
    type(gc_value) :: v
    real(c_double), pointer, contiguous :: rp(:)
    integer(8), pointer, contiguous :: ip(:)
    logical :: good
    integer :: h
    call c_f_pointer(cs, vst)
    ok = 0
    ptr = c_null_ptr
    n = 0
    v = vs_get(vst, int(slot))
    if (gc_kind(v) /= OBJ_ARRAY) return
    ! a slice shares its base's buffer at an offset; only an array that
    ! owns its buffer is viewed
    if (gc_i2(v) /= -1) return
    h = gc_i1(v)
    if (gcna_rank(h) /= 1) return
    select case (kind)
    case (1)
       call gcna_real8_ptr(h, rp, good)
       if (.not. good) return
       n = int(size(rp), c_int64_t)
       if (n > 0) ptr = c_loc(rp(1))
    case (2)
       call gcna_int8_ptr(h, ip, good)
       if (.not. good) return
       n = int(size(ip), c_int64_t)
       if (n > 0) ptr = c_loc(ip(1))
    case default
       return
    end select
    ok = 1
  end function clotran_array_view

  ! --- errors ------------------------------------------------------

  function clotran_has_error() bind(C, name="clotran_has_error") result(b)
    integer(c_int) :: b
    b = 0
    if (gce_has_error()) b = 1
  end function clotran_has_error

  function clotran_error_len() bind(C, name="clotran_error_len") result(n)
    integer(c_int) :: n
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call gce_error(s=dlt_1)
       n = int(len(dlt_1), c_int)
    end block
  end function clotran_error_len

  function clotran_error_copy(buf, n) bind(C, name="clotran_error_copy") result(w)
    character(kind=c_char), intent(out) :: buf(*)
    integer(c_int), value :: n
    integer(c_int) :: w
    character(len=:), allocatable :: s
    integer :: i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call gce_error(s=dlt_1)
       s = dlt_1
    end block
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
  subroutine c_text(chars, n, s)
    character(kind=c_char), intent(in) :: chars(*)
    integer(c_int), intent(in) :: n
    character(len=:), allocatable, intent(out) :: s
    integer :: i
    allocate(character(len=max(0, int(n))) :: s)
    do i = 1, int(n)
       s(i:i) = chars(i)
    end do
  end subroutine c_text

  ! NOTE on roots: every allocation here passes an EMPTY roots array,
  ! on purpose. The shadow stack is the root set, and a caller that did
  ! not put its value in a slot has already lost it.

end module ClotranABI

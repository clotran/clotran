! Eval: a core evaluator over the GC heap.
!
! The last of the standalone modules, and the one that answers the
! question the whole port rests on: does rooting BY CONSTRUCTION
! actually hold up under real evaluation? Everything before this was
! data structures, where the roots are obvious. An evaluator is where
! they are not -- intermediate values live across recursive calls,
! each of which can allocate and therefore collect.
!
! It began as the core of an evaluator -- enough special forms and
! primitives to run real programs and prove the mechanism -- and grew
! into the whole thing as core.clj was loaded form by form. What it
! started with:
!
!   special forms   quote, if, do, def, let*, fn*, loop*, recur
!   primitives      + - * = < list vector count first rest
!   closures        with lexical capture and recursion
!
! RECUR, AND WHY THERE IS NO GENERAL TRAMPOLINE. Clojure does not
! promise tail-call elimination; it promises `recur`, which is an
! explicit jump to the nearest enclosing loop* or fn*. So iteration
! lives in exactly those two places: each evaluates its body and, if
! the result is an OBJ_RECUR, rebinds its parameters from the recur's
! arguments and goes round again. Recursion depth is then bounded by
! the program's NESTING rather than by its iteration count, which is
! the guarantee Clojure actually makes. A general trampoline would be
! more machinery for a promise the language never made.
!
! What it does NOT have, listed rather than silently missing: macros,
! general tail calls (see recur below), try/catch, destructuring, varargs,
! namespaces, laziness. Each is a feature of the full evaluator, not
! of the representation being proved here.
!
! THE ROOTING RULE, which is the whole point:
!
!   Every value that must survive an allocation lives in a value-stack
!   slot. Not in a Fortran local -- the collector cannot see those.
!   Each routine opens a frame with vs_enter, works in its slots, and
!   closes it with vs_leave. Returning a value means reading it out of
!   a slot BEFORE leaving the frame.
!
! That is rooting by construction rather than discipline, and the
! torture tests are what prove it: with a collection at every single
! allocation, the evaluator still computes the right answers.
module Eval
  use, intrinsic :: ieee_arithmetic, only: ieee_value, ieee_copy_sign, &
       ieee_positive_inf, ieee_negative_inf, ieee_quiet_nan
  use GC
  use PersistentList
  use PersistentVector
  use Assoc
  use Env
  use Namespace
  use Printer
  use NativeArray
  use ChemSolBind
  use Regex
  use LispReader
  implicit none
  private

  ! Primitive ids. Order is arbitrary; only the mapping matters.
  integer, parameter :: B_ADD = 1, B_SUB = 2, B_MUL = 3, B_EQ = 4, B_LT = 5
  integer, parameter :: B_LIST = 6, B_VECTOR = 7, B_COUNT = 8
  integer, parameter :: B_FIRST = 9, B_REST = 10
  integer, parameter :: B_CONS = 11, B_CONCAT = 12
  integer, parameter :: B_STR = 13, B_NOT = 14, B_NTH = 15, B_GET = 16
  integer, parameter :: B_CONJ = 17, B_EMPTY = 18, B_NILP = 19, B_APPLY = 20
  integer, parameter :: B_ASSOC = 21, B_KEYS = 22, B_VALS = 23, B_PRN = 24
  integer, parameter :: B_QUOT = 25, B_REM = 26, B_SEQ = 27, B_DISSOC = 28
  integer, parameter :: B_NAME = 29, B_KEYWORD = 30, B_SYMBOL = 31
  integer, parameter :: B_SUBS = 32, B_TYPE = 33, B_SECOND = 34
  integer, parameter :: B_META = 35, B_WITHMETA = 36
  integer, parameter :: B_NS = 37, B_INNS = 38
  integer, parameter :: B_NEXT = 39, B_INSTANCE = 40
  integer, parameter :: B_VEC = 41, B_HMAP = 42, B_HSET = 43
  integer, parameter :: B_DISJ = 44
  integer, parameter :: B_GT = 45, B_LTE = 46, B_GTE = 47, B_DIV = 48
  integer, parameter :: B_INC = 49, B_DEC = 50, B_COMPARE = 51
  integer, parameter :: B_IDENTITY = 52
  integer, parameter :: B_DEREF = 53, B_HASROOT = 54, B_ADDMETHOD = 55
  integer, parameter :: B_GETPROP = 56
  integer, parameter :: B_APPEND = 57, B_TOSTRING = 58
  integer, parameter :: B_ZERO = 59, B_POS = 60, B_NEG = 61
  integer, parameter :: B_MAX = 62, B_MIN = 63
  integer, parameter :: B_EXMSG = 64, B_EXDATA = 65
  integer, parameter :: B_NEXTID = 76, B_SUBVEC = 77, B_INDEXOF = 78, B_ALWAYS_NIL = 79
  integer, parameter :: B_EVAL = 80, B_ALTERMETA = 81, B_RESETMETA = 82
  integer, parameter :: B_SETVAL = 83, B_ALTERVAL = 84, B_CONTAINS = 85, B_FIND = 86
  integer, parameter :: B_KEY = 87, B_VAL = 88, B_NAMESPACE = 89
  integer, parameter :: B_STARTSWITH = 90, B_STRLEN = 91, B_SUBSTRING = 92
  integer, parameter :: B_ENDSWITH = 93, B_REPLACE = 94, B_LOADFILE = 95
  integer, parameter :: B_FINDNS = 96, B_LASTINDEXOF = 97, B_RTLOAD = 98
  integer, parameter :: B_PUSHTB = 99, B_POPTB = 100, B_FINDVAR = 101
  integer, parameter :: B_GETNAME = 102, B_POP = 103, B_PEEK = 104
  integer, parameter :: B_MAYBERESOLVE = 105
  integer, parameter :: B_NSMAP = 106, B_NSREFER = 107, B_NSALIASES = 108
  integer, parameter :: B_VARNS = 109, B_ISPUBLIC = 110
  integer, parameter :: B_ISMACRO = 111, B_SETMACRO = 112
  integer, parameter :: B_RUNTX = 113, B_DOTGET = 114
  integer, parameter :: B_REPEAT = 115, B_RANGE = 116, B_GENIFACE = 117
  integer, parameter :: B_ALWAYS_FALSE = 118, B_FORNAME = 119
  integer, parameter :: B_VARINTERN = 120
  ! One id per named field: call_builtin sees only the arguments,
  ! never which native was called, so the field has to be in the id.
  integer, parameter :: B_FLD_SYM = 121, B_FLD_PROTOCOL = 122
  integer, parameter :: B_FLD_METHODK = 123, B_FLD_MAP = 124
  integer, parameter :: B_VARSYM = 125, B_FLD_CACHE = 126, B_EMPTYVEC = 127
  integer, parameter :: B_ISREDUCED = 128, B_ITERATE = 129, B_CYCLE = 130
  integer, parameter :: B_TOARRAY = 131
  integer, parameter :: B_RE_COMPILE = 132, B_RE_MATCHER = 133, B_RE_FIND = 134
  integer, parameter :: B_RE_MATCHES = 135, B_RE_GROUPCOUNT = 136, B_RE_GROUP = 137
  integer, parameter :: B_HASH = 138, B_BASELOADER = 139, B_RESOURCE = 140
  integer, parameter :: B_PROPLOAD = 141, B_PROPGET = 142, B_CLOSE = 143
  integer, parameter :: B_INTVALUE = 144, B_STRCONTAINS = 145
  integer, parameter :: B_WRITE = 146, B_FLUSH = 147, B_CHARAT = 148
  integer, parameter :: B_NSADDALIAS = 149, B_SWAPVAL = 150
  integer, parameter :: B_ISWS = 151, B_ISLOWER = 153
  integer, parameter :: B_ISDIGIT = 154, B_ISLETTER = 155, B_ISALNUM = 156
  integer, parameter :: B_UPCASE = 157, B_DOWNCASE = 158
  integer, parameter :: B_SYMBOL2 = B_SYMBOL
  integer, parameter :: B_LONGCAST = 66, B_DBLCAST = 67, B_BOOLCAST = 68, B_CHARCAST = 69
  integer, parameter :: B_BITAND = 70, B_BITOR = 71, B_BITXOR = 72, B_BITNOT = 73
  integer, parameter :: B_SHL = 74, B_SHR = 75
  integer, parameter :: B_IDENTICAL = 159
  integer, parameter :: B_DBLVALUE = 160, B_ISNAN = 161, B_ISINF = 162
  integer, parameter :: B_ISREALIZED = 163
  integer, parameter :: B_MAKE_ARRAY = 164, B_AGET = 165, B_ASET = 166
  integer, parameter :: B_ALENGTH = 167, B_ARRAY_KIND = 168, B_ARRAY_SHAPE = 169
  integer, parameter :: B_ANEWINST = 170, B_ACLONE = 171, B_PREPRET = 172
  integer, parameter :: B_NUMCAST = 173, B_NUMEQ = 174, B_ABS = 175
  integer, parameter :: B_NUMER = 176, B_DENOM = 177
  integer, parameter :: B_SBASIS = 180, B_SCREATE = 181
  integer, parameter :: B_SCONSTRUCT = 182, B_SACCESSOR = 183
  integer, parameter :: B_ASIFASSOC = 184
  integer, parameter :: B_MACROEXP1 = 185
  integer, parameter :: B_COLLEMPTY = 186
  integer, parameter :: B_SWAPVALS = 187, B_RESETVALS = 188
  integer, parameter :: B_METHODTABLE = 189, B_GETMETHOD = 190
  integer, parameter :: B_EMPTYMAP = 191, B_REMOVEMETHOD = 192
  ! java.lang.Math occupies a BLOCK: B_MATH0 + k, k from hosttable.inc.
  integer, parameter :: B_MATH0 = 200, B_MATHN = 45
  integer, parameter :: B_FORMAT = 193, B_NUMCOMPARE = 194
  integer, parameter :: B_READSTRING = 195, B_RE_SPLIT = 196
  integer, parameter :: B_QUOTEREPL = 197, B_SBREVERSE = 198
  ! Past the Math block, which occupies B_MATH0+1 .. B_MATH0+45.
  integer, parameter :: B_RE_REPLACEALL = 250, B_RE_REPLACEFIRST = 251
  integer, parameter :: B_RE_APPENDREPL = 252, B_RE_APPENDTAIL = 253
  integer, parameter :: B_RE_START = 254, B_RE_END = 255
  integer, parameter :: B_INTOARRAY = 256, B_EMPTYARRAY = 257
  integer, parameter :: B_GETIFACES = 258
  ! An agent's error bookkeeping. The agent IS an atom here, and
  ! these live in the atom's spare slots: 3 the error mode, 4 the
  ! handler, 5 the error itself.
  integer, parameter :: B_SETERRMODE = 259, B_GETERRMODE = 260
  integer, parameter :: B_SETERRHANDLER = 261, B_GETERRHANDLER = 262
  integer, parameter :: B_AGENTERROR = 263, B_AGENTRESTART = 264
  integer, parameter :: B_AGENTDISPATCH = 265
  integer, parameter :: B_LATCHDOWN = 266, B_LATCHCOUNT = 267
  integer, parameter :: B_SETVALIDATOR = 268, B_GETVALIDATOR = 269
  integer, parameter :: B_RTPRINT = 270
  integer, parameter :: B_NANOTIME = 271, B_MILLIS = 272
  integer, parameter :: B_DGEMM = 273
  integer, parameter :: B_STACKTRACE = 274, B_STE_CLASS = 275, B_STE_METHOD = 276, &
       B_STE_FILE = 277, B_STE_LINE = 278
  integer, parameter :: B_SLURP = 279, B_CS_ENTROPY = 280, B_CS_READOPT = 281, B_CS_DGLD = 282, B_CS_SOLVOUT = 283
  integer, parameter :: B_CLASSOF = 284, B_IDHASH = 285, B_REDUCEINIT = 286
  integer, parameter :: B_CHUNK_ADD = 287, B_CHUNK_OF = 288, B_CHUNK_FIRST = 289, &
       B_CHUNK_MORE = 290, B_CHUNK_NEXT = 291, B_CHUNK_DROP = 292
  integer, parameter :: B_BREAK = 293, B_LASTBREAK = 294, B_BREAKON = 295
  integer, parameter :: B_RESUME = 296, B_REPL = 297
  integer, parameter :: B_ARRSORT = 178, B_CMPCALL = 179
  integer, parameter :: B_COMPTYPE = 173

  ! The auto-gensym map for the syntax-quote currently being expanded,
  ! and the counter that makes each name unique. GENSYM_ENV in
  ! LispReader is a dynamic Var bound around one syntax-quote; a
  ! module variable plus a depth count is the same scoping here.
  type(gc_root), save :: gensym_root
  integer, save :: gensym_id = 0
  integer, save :: qq_depth = 0
  ! Every type `deftype*` has created, keyed by the class keyword a
  ! class literal evaluates to. Clojure puts the class in a
  ! classloader and imports the short name into the namespace;
  ! clotran's `import` is a no-op (classes are recognised by the
  ! SHAPE of their name), so there is nowhere namespace-local to put
  ! it and one global table is what `new` and `instance?` both read.
  !
  ! Global, and therefore on the list in PLAN.md of what has to move
  ! into a per-thread context before threads exist.
  type(gc_root), save :: types_root
  integer, save :: reify_id = 0
  integer, save :: proxy_id = 0
  ! EVALUATION DEPTH, and the limit that turns a stack overflow into a
  ! reportable error instead of a segfault. The JVM does the same thing
  ! -- StackOverflowError -- and Clojure inherits it.
  !
  ! There is no depth to copy from Clojure, because the JVM's limit is a
  ! BYTE BUDGET, not a frame count: -XX:ThreadStackSize (2048 KB by
  ! default on this platform, per -XX:+PrintFlagsFinal) divided by
  ! whatever each frame happens to need. Measured on real Clojure, a
  ! non-tail-recursive function reaches ~11,200 frames at that default,
  ! and the depth scales linearly with -Xss: 1,635 at 512k, 5,528 at 1m,
  ! 11,211 at 2m, 24,731 at 4m.
  !
  ! So the faithful thing to match is the budget, and ours is measured
  ! the same way. On macOS's 8 MB default stack clotran segfaults
  ! somewhere between 700 and 800 Clojure-level calls; 2200 gce_eval
  ! entries is the highest limit that still reports rather than crashes,
  ! and it leaves roughly 600 usable frames.
  !
  ! That is about twenty times shallower than Clojure per megabyte, and
  ! the reason is structural: one Clojure call costs a chain of
  ! interpreter frames -- eval, eval_call, apply, eval_body, eval back
  ! into the arguments -- where the JVM has one JIT-compiled frame.
  ! Recorded in DEVIATIONS.md; the real fix is an explicit continuation
  ! rather than a bigger number.
  !
  ! CLOTRAN_MAX_DEPTH overrides it, which is what -Xss is for.
  ! The environment `eval` uses. Clojure's eval has no lexical
  ! environment either -- Compiler.eval analyses against an empty local
  ! env -- so this is the bottom frame and nothing else.
  ! The stack of dynamic binding frames. Each frame is a map from Var
  ! to the value that Var held before the frame was pushed, so popping
  ! restores it.
  !
  ! Clojure's is THREAD-LOCAL -- Var.dvals is a ThreadLocal, which is
  ! the whole point of a dynamic Var -- and this one is global. With one
  ! thread the two are indistinguishable; with more they are not.
  ! DEVIATIONS.md 10.
  type(gc_root), save :: binding_stack_root
  ! import* records these; see record_import.
  character(len=64), allocatable, save :: import_full(:), import_short(:)
  integer, save :: n_imports = 0
  type(gc_root), save :: global_env_root
  integer, save :: ev_depth = 0
  integer, save :: ev_limit = 0

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  ! The value a `throw` is carrying, as a GC GLOBAL ROOT rather than a
  ! plain module variable. It has to be: between the throw and the
  ! catch, nothing else refers to it -- the stack frames that held it
  ! are unwinding -- so an ordinary variable would be a value the
  ! collector cannot see, and a collection in that window would free
  ! the exception before its handler ever ran.
  type(gc_root), save :: thrown_root
  ! Reused argument vectors for the numeric builtins (exec.inc, N_CALL
  ! mode 3), and the one recur marker: none of those allocate per call.
  type(gc_root), save :: scratch1_root, scratch2_root, recur_root
  ! The last paused state, as data; see the break protocol in exec.inc.
  type(gc_root), save :: break_root
  integer, save :: break_mode = 0   ! 0 unread, 1 off, 2 capturing
  logical, save :: break_stderr = .false.
  character(len=:), allocatable, save :: break_path
  ! The resuming half (exec.inc, take_break): the handler Var, the fn it
  ! held when the break was taken, the command that came back, the REPL
  ! as a fn value, and the context the handler runs in. step_at is a
  ! step still to be taken: stop at the next call no deeper than it.
  type(gc_root), save :: handler_var_root, handler_fn_root, resume_root, repl_fn_root
  logical, save :: in_handler = .false., resume_pending = .false.
  integer, save :: handler_ctx = 0, step_at = 0, repl_depth = 0

  public :: gce_eval, gce_base_env, gce_has_error, gce_error, gce_clear_error
  public :: gce_analyze, gce_trace
  public :: gce_ctx_new, gce_ctx_switch, gce_ctx_current
  public :: gce_repl
  public :: gce_set_home, gce_home

  ! THE CALL STACK. One entry per closure invocation in progress: the
  ! closure and the position of the call that entered it (set by the
  ! executor just before apply, read by invoke_closure). Nothing here
  ! is a root: a closure on this stack is also in a value-stack slot of
  ! the caller for as long as the call lasts. When an error is raised
  ! the stack is rendered into `last_trace` at once, before it unwinds,
  ! so the message can say where it came from. A `recur` does not push;
  ! a deep loop is one frame, which a trace does not pretend otherwise.
  type(gc_value), allocatable, save :: fstack_fn(:)
  integer, allocatable, save :: fstack_site(:)
  integer, save :: fstack_top = 0
  integer, save :: pending_site = 0
  character(len=:), allocatable, save :: last_trace
  ! Forms evaluated since startup. CLOTRAN_STATS=1 prints it at exit
  ! next to the collector's counters (main.f90), so a cost can be
  ! split into "more work" and "more collector" before theorising.
  integer(8), public :: gce_evals = 0

  ! Node kinds (analyze.inc / exec.inc). K_* are the analyser's own
  ! scope objects, which share OBJ_AST.
  integer, parameter :: N_CONST = 1, N_LOCAL = 2, N_VAR = 3, N_IF = 4, N_DO = 5, &
       N_CALL = 6, N_VECTOR = 7, N_MAP = 8, N_SET = 9, N_DEF = 10, N_LET = 11, &
       N_LOOP = 12, N_LETFN = 13, N_FN = 14, N_LAZY = 15, N_RECUR = 16, N_THROW = 17, &
       N_TRY = 18, N_CASE = 19, N_DEFTYPE = 20, N_DOT = 21, N_NEW = 22, N_NEWTYPE = 23, &
       N_SETBANG = 24, N_FAIL = 25, N_TOP = 26, N_TOPDO = 27, N_LATEVAR = 28
  integer, parameter :: K_SCOPE = 100, K_FNINFO = 101
  integer, save :: trace_macros = 0   ! 0 unread, 1 on, 2 off
  integer, save :: keep_locals_mode = 0   ! 0 unread, 1 clear, 2 keep

  ! The executor's continuation stack (exec.inc, `run`): one entry per
  ! node being evaluated. Its values live in a K_SLOTS-wide region of
  ! the value stack at `base` -- node, frame, aux, argv, restart -- so
  ! the collector sees them; pc and i are its progress; flags say what
  ! happens when it finishes (a fn body pops the call stack, a restart
  ! point runs again on recur); nfr is how many call-stack entries it
  ! pops when it finishes -- one per call it stands for, since a call in
  ! tail position reuses the frame but keeps the caller on the call
  ! stack, as the JVM does; msg is a try's saved error.
  type kframe
     integer :: base = 0, pc = 0, i = 0, flags = 0, nfr = 0
     integer :: mode = 0, aux = 0, aux2 = 0   ! a call's argument mode, first slot, arity
     character(len=:), allocatable :: msg
  end type kframe
  type(kframe), allocatable, save :: kst(:)
  integer, save :: ksp = 0
  integer, parameter :: KF_FNBODY = 1, KF_RESTART = 2, K_SLOTS = 7   ! slot 6: a scalar call's first argument; slot 7: the closure whose body this is
  integer, save :: k_limit = 0

  ! --- evaluation contexts ---------------------------------------------
  !
  ! Everything the evaluator keeps between two steps of `run`: the
  ! continuation stack, the call stack, the error state, the thrown
  ! value, the dynamic bindings. One context is live in the module
  ! variables above; the others are parked here, arrays moved in and
  ! out with move_alloc so a switch costs nothing per frame. The value
  ! stack is parked beside it in GC (gc_stack_save). A green thread is
  ! a context; so is the paused frame a debugger inspects while the
  ! REPL runs in another (PLAN stage 2).
  type eval_ctx
     type(kframe), allocatable :: kst(:)
     integer :: ksp = 0
     type(gc_value), allocatable :: fstack_fn(:)
     integer, allocatable :: fstack_site(:)
     integer :: fstack_top = 0, pending_site = 0, ev_depth = 0
     logical :: has_error = .false.
     character(len=:), allocatable :: last_error, last_trace
     type(gc_root) :: thrown_root, binding_stack_root
  end type eval_ctx
  type(eval_ctx), allocatable, save :: ctxs(:)
  integer, save :: cur_ctx = 0, n_ctx = 0

  ! The directory the binary lives in: a classpath root, so `clotran`
  ! run from anywhere finds src/clj. main.f90 sets it from argv(0).
  character(len=:), allocatable, save :: clotran_home

  include "hosttable.inc"

contains

  ! Cleared by the CALLER before a top-level evaluation, not by
  ! gce_eval itself: gce_eval is recursive, so clearing on entry would
  ! wipe an error raised deeper in the same evaluation. A REPL clears,
  ! evaluates, then checks -- which is exactly this shape.
  subroutine gce_clear_error()
    has_error = .false.
    last_error = ""
    call set_thrown(gc_nil())
    if (allocated(last_trace)) last_trace = ""
  end subroutine gce_clear_error

  ! Re-checks the slot rather than trusting the index, for the same
  ! reason PersistentList's empty-list singleton does: gc_init clears the
  ! global-root registry but this module variable survives it.
  ! The thrown value. A Throwable that has no stack trace yet gets
  ! the current one -- Java fills it in at construction; here that
  ! happens in eval_new for a (new SomeException ...) and, failing
  ! that, now, at the throw.
  subroutine set_thrown(v)
    type(gc_value), intent(in) :: v
    type(gc_value) :: fr
    integer :: base
    call gc_global_keep(thrown_root, v)
    if (gc_kind(v) == OBJ_ERR) then
       if (tag_of(gc_slot(v, 4)) == GCT_NIL) then
          base = vs_enter(1)
          fr = frames_vec([v])
          call vs_set(base + 1, fr)
          call gc_set_slot(v, 4, vs_get(base + 1))
          call vs_leave(base)
       end if
    end if
  end subroutine set_thrown

  ! The call stack as data, innermost first: one map per frame with
  ! the four things a StackTraceElement answers. `:class` is the
  ! function's qualified name, `:method` is always "invoke" -- there
  ! is one way to call a function here -- `:file` and `:line` are the
  ! call site's.
  function frames_vec(roots) result(out)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, nm
    character(len=:), allocatable :: who, fname
    integer :: i, base, line, col
    base = vs_enter(2)
    out = gcv_empty(roots)
    call vs_set(base + 1, out)
    do i = fstack_top, 1, -1
       who = "fn"
       if (gc_kind(fstack_fn(i)) == OBJ_CLOSURE) then
          nm = gc_slot(fstack_fn(i), 5)
          if (nm%tag == GCT_SYM) who = gc_ref_text(nm%ref)
       end if
       fname = ""
       line = 0
       if (fstack_site(i) /= 0) call gcr_position_parts(fstack_site(i), fname, line, col)
       m = gca_empty([roots, vs_get(base + 1)])
       call vs_set(base + 2, m)
       m = gca_assoc(vs_get(base + 2), gc_key("class", [vs_get(base + 1), vs_get(base + 2)]), &
            gc_str(who, [vs_get(base + 1), vs_get(base + 2)]), [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, m)
       m = gca_assoc(vs_get(base + 2), gc_key("method", [vs_get(base + 1), vs_get(base + 2)]), &
            gc_str("invoke", [vs_get(base + 1), vs_get(base + 2)]), [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, m)
       m = gca_assoc(vs_get(base + 2), gc_key("file", [vs_get(base + 1), vs_get(base + 2)]), &
            gc_str(fname, [vs_get(base + 1), vs_get(base + 2)]), [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, m)
       m = gca_assoc(vs_get(base + 2), gc_key("line", [vs_get(base + 1), vs_get(base + 2)]), &
            gc_int(line), [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, m)
       out = gcv_conj(vs_get(base + 1), vs_get(base + 2), [roots])
       call vs_set(base + 1, out)
    end do
    out = vs_get(base + 1)
    call vs_leave(base)
  end function frames_vec

  function thrown_value() result(v)
    type(gc_value) :: v
    v = gc_root_get(thrown_root)
  end function thrown_value

  function gce_has_error() result(yes)
    logical :: yes
    yes = has_error
  end function gce_has_error

  function gce_error() result(s)
    character(len=:), allocatable :: s
    s = ""
    if (allocated(last_error)) s = last_error
  end function gce_error

  subroutine fail(msg)
    character(len=*), intent(in) :: msg
    has_error = .true.
    last_error = msg
    call capture_trace()
  end subroutine fail

  ! The call stack as text, innermost first, taken when an error is
  ! raised. Each line names the function entered and where it was
  ! called from.
  ! The rendered trace stops at 128 frames, as the JVM's stops at
  ! MaxJavaStackTraceDepth: a stack overflow 200000 deep is not 200000
  ! lines, and building them by concatenation was quadratic. The
  ! element array .getStackTrace answers is still the whole stack.
  subroutine capture_trace()
    integer :: i
    type(gc_value) :: bm
    type(gc_value) :: nm
    character(len=:), allocatable :: who
    character(len=16) :: more
    last_trace = ""
    if (fstack_top > 128) write(more, '(I0)') fstack_top - 128
    do i = fstack_top, max(1, fstack_top - 127), -1
       who = "fn"
       if (gc_kind(fstack_fn(i)) == OBJ_CLOSURE) then
          nm = gc_slot(fstack_fn(i), 5)
          if (nm%tag == GCT_SYM) who = gc_ref_text(nm%ref)
       end if
       if (fstack_site(i) /= 0) then
          last_trace = last_trace // "  at " // who // " (" // gcr_position(fstack_site(i)) // ")" // achar(10)
       else
          last_trace = last_trace // "  at " // who // achar(10)
       end if
    end do
    if (fstack_top > 128) last_trace = last_trace // "  ... " // trim(more) // " more" // achar(10)
    ! and the paused state as data, while the frames are still pending,
    ! to the handler if one is bound
    if (break_mode == 0) call read_break_mode()
    if (break_mode == 2) bm = take_break("error")
  end subroutine capture_trace

  ! The trace of the last error, one line per frame, or empty.
  function gce_trace() result(s)
    character(len=:), allocatable :: s
    s = ""
    if (allocated(last_trace)) s = last_trace
  end function gce_trace

  subroutine push_frame(fn, site)
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: site
    type(gc_value), allocatable :: bf(:)
    integer, allocatable :: bs(:)
    integer :: n
    if (.not. allocated(fstack_fn)) then
       allocate(fstack_fn(256), fstack_site(256))
       fstack_top = 0
    end if
    if (fstack_top >= size(fstack_fn)) then
       n = size(fstack_fn)
       allocate(bf(2 * n), bs(2 * n))
       bf(1:n) = fstack_fn(1:n)
       bs(1:n) = fstack_site(1:n)
       call move_alloc(bf, fstack_fn)
       call move_alloc(bs, fstack_site)
    end if
    if (k_limit == 0) call read_frame_limit()
    if (fstack_top >= k_limit) then
       call fail("stack overflow")
       return
    end if
    fstack_top = fstack_top + 1
    fstack_fn(fstack_top) = fn
    fstack_site(fstack_top) = site
  end subroutine push_frame

  subroutine pop_frame()
    if (fstack_top > 0) fstack_top = fstack_top - 1
  end subroutine pop_frame

  ! An environment with the primitives bound. Built fresh rather than
  ! cached in a module variable: a cached handle would go stale across
  ! gc_init, which is exactly the singleton bug PersistentList's check 4c
  ! caught.
  function gce_base_env(roots) result(env)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: env, core, var
    integer :: base

    ! A fresh heap means every array handle from a previous one is
    ! orphaned; this is the one place that always follows gc_init.
    call gcna_reset()
    call gcp_set_forcer(gce_force)
    ! The sweep tells us when an object owning out-of-heap storage
    ! dies, so a native array's buffer is freed exactly once rather
    ! than leaking for the life of the process.
    call gc_set_finalizer(gce_finalize_obj)
    call gc_set_coll_ops(gce_coll_hash, gce_coll_equal)
    call gcn_reset(roots)
    call ctx_reset()
    ! Three slots: env, clojure.core, and the fortran namespace. The
    ! third is NOT optional -- core lives in slot 2 for the whole of
    ! this routine.
    base = vs_enter(3)
    env = gce_new(gc_nil(), roots)
    call vs_set(base + 1, env)
    call gc_global_keep(global_env_root, vs_get(base + 1))
    core = gcn_find_or_create("clojure.core", [vs_get(base + 1)])
    call vs_set(base + 2, core)
    call bind_builtin(core, "+", B_ADD)
    call bind_builtin(core, "-", B_SUB)
    call bind_builtin(core, "*", B_MUL)
    call bind_builtin(core, "=", B_EQ)
    call bind_builtin(core, "<", B_LT)
    call bind_builtin(core, "list", B_LIST)
    call bind_builtin(core, "vector", B_VECTOR)
    ! The debugger's two entry points; PLAN.md's break protocol.
    call bind_builtin(core, "clotran-break", B_BREAK)
    call bind_builtin(core, "clotran-last-break", B_LASTBREAK)
    call bind_builtin(core, "clotran-break-on!", B_BREAKON)
    ! and the resuming half: the handler Var a break calls, the command
    ! a nested REPL answers with, and the REPL itself as the default
    ! handler (gce_repl binds it when a REPL starts).
    call bind_builtin(core, "clotran-resume", B_RESUME)
    call bind_builtin(core, "clotran-repl", B_REPL, var_out=var)
    call gc_global_keep(repl_fn_root, gcn_var_value(var))
    call bind_var(core, "*clotran-break-handler*", gc_nil(), var_out=var)
    call gc_global_keep(handler_var_root, var)
    ! Native arrays go in a `fortran` NAMESPACE, not in clojure.core.
    !
    ! Two reasons, and the first is practical: core.clj defines its
    ! own make-array, aget, aset and alength, so anything bound under
    ! those names here is shadowed the moment core.clj loads. The
    ! second is the one that matters -- these are not Clojure's array
    ! functions wearing a different implementation. They take a
    ! Fortran KIND NAME rather than a class, they are column-major,
    ! and the buffer they make can be handed to dgemm. That is a
    ! different thing and it should not borrow the name.
    !
    ! SEAMS.md asks for exactly this: `fortran.*` for a real Fortran
    ! object crossing a real boundary. This is the first thing in it.
    block
      type(gc_value) :: fns
      ! base + 3, NOT base + 2: that slot holds clojure.core for the
      ! whole of this routine, and clobbering it sent every builtin bound
      ! after this block into the wrong namespace.
      fns = gcn_find_or_create("fortran", [core])
      call vs_set(base + 3, fns)
      call bind_builtin(vs_get(base + 3), "make-array", B_MAKE_ARRAY)
      call bind_builtin(vs_get(base + 3), "aget", B_AGET)
      call bind_builtin(vs_get(base + 3), "aset", B_ASET)
      call bind_builtin(vs_get(base + 3), "alength", B_ALENGTH)
      call bind_builtin(vs_get(base + 3), "array-kind", B_ARRAY_KIND)
      call bind_builtin(vs_get(base + 3), "array-shape", B_ARRAY_SHAPE)
      call bind_builtin(vs_get(base + 3), "dgemm", B_DGEMM)
      ! ChemSol (src/f/chemsol, src/f/ChemSolBind.f90): the routines
      ! main.f90 calls, each taking and answering a map.
      call bind_builtin(vs_get(base + 3), "chemsol-entropy", B_CS_ENTROPY)
      call bind_builtin(vs_get(base + 3), "chemsol-readopt", B_CS_READOPT)
      call bind_builtin(vs_get(base + 3), "chemsol-dg-ld", B_CS_DGLD)
      call bind_builtin(vs_get(base + 3), "chemsol-solvout", B_CS_SOLVOUT)
    end block
    ! A whole file as a string. core.clj's slurp is written over
    ! java.io, which is not here; this is the host's reader for it.
    call bind_builtin(core, "clotran-slurp", B_SLURP)
    call bind_builtin(core, "count", B_COUNT)
    call bind_builtin(core, "first", B_FIRST)
    call bind_builtin(core, "rest", B_REST)
    call bind_builtin(core, "next", B_NEXT)
    call bind_builtin(core, "cons", B_CONS)
    call bind_builtin(core, "concat", B_CONCAT)
    call bind_builtin(core, "str", B_STR)
    call bind_builtin(core, "not", B_NOT)
    call bind_builtin(core, "nth", B_NTH)
    call bind_builtin(core, "get", B_GET)
    call bind_builtin(core, "conj", B_CONJ)
    call bind_builtin(core, "empty?", B_EMPTY)
    call bind_builtin(core, "nil?", B_NILP)
    call bind_builtin(core, "apply", B_APPLY)
    call bind_builtin(core, "assoc", B_ASSOC)
    call bind_builtin(core, "keys", B_KEYS)
    call bind_builtin(core, "vals", B_VALS)
    call bind_builtin(core, "prn", B_PRN)
    call bind_builtin(core, "quot", B_QUOT)
    call bind_builtin(core, "rem", B_REM)
    call bind_builtin(core, "seq", B_SEQ)
    call bind_builtin(core, "dissoc", B_DISSOC)
    call bind_builtin(core, "name", B_NAME)
    call bind_builtin(core, "keyword", B_KEYWORD)
    call bind_builtin(core, "symbol", B_SYMBOL)
    call bind_builtin(core, "subs", B_SUBS)
    call bind_builtin(core, "clotran-type", B_TYPE)
    call bind_builtin(core, "instance?", B_INSTANCE)
    ! Bound as names too, not only as host members: syntax-quote emits
    ! (vec ...) for a vector template, so it has to resolve before
    ! core.clj gets around to defining its own.
    call bind_builtin(core, "vec", B_VEC)
    call bind_builtin(core, "hash-set", B_HSET)
    ! Bound for the same reason vec is: syntax-quote emits (hash-map ...)
    ! for a map template, so it has to resolve before core.clj defines
    ! its own. core.clj's hash-map is variadic over key/value pairs and
    ! this one takes a single flat seq, which is what the template
    ! produces -- the two agree wherever both are reachable.
    call bind_builtin(core, "hash-map", B_HMAP)
    call bind_builtin(core, "disj", B_DISJ)
    ! The rest of the arithmetic primitives. core.clj defines >, <=,
    ! inc and the others in terms of clojure.lang.Numbers, so the
    ! natives have to exist whether or not anything names them yet.
    call bind_builtin(core, ">", B_GT)
    call bind_builtin(core, "<=", B_LTE)
    call bind_builtin(core, ">=", B_GTE)
    call bind_builtin(core, "/", B_DIV)
    call bind_builtin(core, "inc", B_INC)
    call bind_builtin(core, "dec", B_DEC)
    call bind_builtin(core, "compare", B_COMPARE)
    call bind_builtin(core, "deref", B_DEREF)
    call bind_builtin(core, "subvec", B_SUBVEC)
    call bind_builtin(core, "contains?", B_CONTAINS)
    call bind_builtin(core, "find", B_FIND)
    call bind_builtin(core, "key", B_KEY)
    call bind_builtin(core, "val", B_VAL)
    call bind_builtin(core, "namespace", B_NAMESPACE)
    call bind_builtin(core, "pop", B_POP)
    ! gen-interface lives in genclass.clj, which is skipped: it
    ! declares a JVM interface, and there are none here. A macro
    ! evaluating to nil, so definterface is a no-op rather than an
    ! error -- core/protocols opens with one. DEVIATIONS.md 12.
    call bind_builtin(core, "gen-interface", B_GENIFACE, .true.)
    call bind_builtin(core, "definterface", B_GENIFACE, .true.)
    call bind_builtin(core, "peek", B_PEEK)
    ! load-file is a Java-side Var in Clojure -- core.clj only decorates
    ! it with (alter-meta! #'load-file assoc :added "1.0") -- so it has
    ! to exist before core.clj loads, like *ns* and *out*.
    call bind_builtin(core, "load-file", B_LOADFILE)
    call bind_builtin(core, "zero?", B_ZERO)
    call bind_builtin(core, "pos?", B_POS)
    call bind_builtin(core, "neg?", B_NEG)
    call bind_builtin(core, "ex-message", B_EXMSG)
    call bind_builtin(core, "ex-data", B_EXDATA)
    ! The dynamic Vars RT.doInit interns before load("clojure/core").
    ! core.clj reads several of them in code that runs while it is still
    ! loading -- assert-args puts *ns* in its message -- so they cannot
    ! wait for core.clj to define them.
    !
    ! *out* and *err* ARE writers -- core.clj's pr, prn, print and
    ! println all end in (.write *out* s) or (.append *out* c), and a nil
    ! there is what made every one of them fail on nil.write. *in* stays
    ! nil: nothing reads through it yet.
    call bind_var(core, "*out*", make_writer(6, core))
    call bind_var(core, "*in*", gc_nil())
    call bind_var(core, "*err*", make_writer(0, core))
    call bind_var(core, "*agent*", gc_nil())
    call bind_var(core, "*read-eval*", gc_bool(.true.))
    call bind_var(core, "*data-readers*", gca_empty([vs_get(base + 1)]))
    call bind_var(core, "*default-data-reader-fn*", gc_nil())
    call bind_var(core, "*assert*", gc_bool(.true.))
    call bind_var(core, "*math-context*", gc_nil())
    call bind_var(core, "*command-line-args*", gc_nil())
    call bind_var(core, "*flush-on-newline*", gc_bool(.true.))
    call bind_var(core, "*print-meta*", gc_bool(.false.))
    call bind_var(core, "*print-readably*", gc_bool(.true.))
    call bind_var(core, "*print-dup*", gc_bool(.false.))
    call bind_var(core, "*print-length*", gc_nil())
    call bind_var(core, "*print-level*", gc_nil())
    call bind_var(core, "*warn-on-reflection*", gc_bool(.false.))
    call bind_var(core, "*allow-unresolved-vars*", gc_bool(.false.))
    call bind_var(core, "*reader-resolver*", gc_nil())
    call bind_var(core, "*unchecked-math*", gc_bool(.false.))
    call bind_var(core, "*compile-files*", gc_bool(.false.))
    call bind_var(core, "*file*", gc_nil())
    call bind_var(core, "*source-path*", gc_nil())
    call bind_var(core, "*compile-path*", gc_str("classes", [vs_get(base + 1)]))
    call bind_var(core, "*warn-on-reflection*", gc_bool(.false.))
    call bind_var(core, "*clojure-version*", gca_empty([vs_get(base + 1)]))
    call bind_var(core, "*fn-loader*", gc_nil())
    call bind_var(core, "*verbose-defrecords*", gc_bool(.false.))
    call bind_var(core, "*print-namespace-maps*", gc_bool(.false.))
    call bind_var(core, "*repl*", gc_bool(.false.))
    call bind_var(core, "*compiler-options*", gca_empty([vs_get(base + 1)]))
    call bind_var(core, "*suppress-read*", gc_nil())
    call bind_var(core, "*use-context-classloader*", gc_bool(.true.))
    call bind_builtin(core, "second", B_SECOND)
    call bind_builtin(core, "meta", B_META)
    call bind_builtin(core, "with-meta", B_WITHMETA)
    call bind_builtin(core, "ns", B_NS, .true.)
    call bind_builtin(core, "in-ns", B_INNS)
    env = vs_get(base + 1)
    call vs_leave(base)
  end function gce_base_env

  ! Interns a native as a VAR IN clojure.core -- not as a binding in
  ! the environment. That is where RT.doInit puts them, and the
  ! difference is not cosmetic: a Var is what lets core.clj REDEFINE a
  ! primitive, because gcn_intern mutates the Var already there rather
  ! than adding a second binding that the first would shadow forever.
  !
  ! `is_macro` is Var.setMacro, which RT.java calls on exactly one of
  ! these -- `ns` -- before load("clojure/core").
  ! A native as a VALUE. Host members need this rather than a Var
  ! lookup: core.clj is in the middle of REDEFINING first, next, rest,
  ! seq and cons in terms of the host when it asks for them, so
  ! resolving .RT/first through the Var `first` would be a loop.
  function native(id, name, roots) result(fn)
    integer, intent(in) :: id
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fn, sym
    integer :: base
    base = vs_enter(1)
    sym = gc_sym(name, roots)
    call vs_set(base + 1, sym)
    fn = gc_obj(OBJ_BUILTIN, [vs_get(base + 1)], roots)
    call gc_set_i1(fn, id)
    call vs_leave(base)
  end function native

  ! Interns a plain value as a Var in clojure.core. Same shape as
  ! bind_builtin, for the things RT interns that are not functions.
  subroutine bind_var(ns, name, val, var_out)
    type(gc_value), intent(in) :: ns, val
    character(len=*), intent(in) :: name
    type(gc_value), intent(out), optional :: var_out
    type(gc_value) :: sym, var
    integer :: base
    base = vs_enter(2)
    call vs_set(base + 1, ns)
    call vs_set(base + 2, val)
    sym = gc_sym(name, [vs_get(base + 1), vs_get(base + 2)])
    var = gcn_intern(vs_get(base + 1), sym, vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 2), sym])
    call gc_set_i1(var, 1)
    if (present(var_out)) var_out = var
    call vs_leave(base)
  end subroutine bind_var

  subroutine bind_builtin(ns, name, id, is_macro, var_out)
    type(gc_value), intent(in) :: ns
    character(len=*), intent(in) :: name
    integer, intent(in) :: id
    logical, intent(in), optional :: is_macro
    type(gc_value), intent(out), optional :: var_out
    type(gc_value) :: sym, fn, var
    type(gc_value) :: r(2)
    integer :: base

    base = vs_enter(3)
    call vs_set(base + 1, ns)
    sym = gc_sym(name, [vs_get(base + 1)])
    call vs_set(base + 2, sym)
    r(1) = vs_get(base + 1)
    r(2) = vs_get(base + 2)
    fn = gc_obj(OBJ_BUILTIN, [sym], r)
    call gc_set_i1(fn, id)
    call vs_set(base + 3, fn)
    var = gcn_intern(vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), r)
    if (present(is_macro)) then
       if (is_macro) call var_set_macro(var)
    end if
    if (present(var_out)) var_out = var
    call vs_leave(base)
  end subroutine bind_builtin

  ! ---- evaluation ----

  ! A DEPTH GUARD on evaluation. Clojure gets a StackOverflowError it
  ! can report; a Fortran stack overflow is a bare segfault with the
  ! output buffer unflushed, so runaway recursion has to be caught
  ! before the stack goes rather than after.
  ! Evaluation is analysis followed by execution: a caller hands over
  ! a node from gce_analyze. A raw form is analysed here first.
  ! `env` and `roots` are unused and kept for the callers' sake.
  recursive function gce_eval(form, env, roots) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, nd
    integer :: base

    out = gc_nil()
    if (has_error) return
    if (gc_kind(form) == OBJ_AST) then
       out = exec(form, gc_nil())
       return
    end if
    base = vs_enter(2)
    call vs_set(base + 1, form)
    nd = analyze_top(vs_get(base + 1))
    if (.not. has_error) then
       call vs_set(base + 2, nd)
       out = exec(vs_get(base + 2), gc_nil())
    end if
    call vs_leave(base)
  end function gce_eval

  ! `ns` and `in-ns` are macros in real Clojure, defined in core.clj
  ! -- `ns` at line 5976. But core.clj's OWN first form, at line 9,
  ! is (ns clojure.core): the file needs the thing it has not
  ! defined yet. Clojure resolves that outside the .clj entirely --
  ! the namespace exists Java-side before the file loads, and the
  ! shipped core is AOT-compiled. clotran has no Java side, so
  ! something must bridge that window.
  !
  ! It bridges it as a FALLBACK, not a special form. A definition
  ! in the namespace always wins, so the moment core.clj defines
  ! its own `ns` macro, that is what runs -- which is the rule
  ! everywhere here: do what Clojure does unless the bootstrap
  ! makes it impossible, and hand control back as soon as it does
  ! not.
  function is_special(sym) result(yes)
    type(gc_value), intent(in) :: sym
    logical :: yes
    yes = gc_ref_is(sym%ref, "quote") .or. gc_ref_is(sym%ref, "if") .or. &
          gc_ref_is(sym%ref, "do") .or. gc_ref_is(sym%ref, "def") .or. &
          gc_ref_is(sym%ref, "let*") .or. gc_ref_is(sym%ref, "fn*") .or. &
          gc_ref_is(sym%ref, "letfn*") .or. &
          gc_ref_is(sym%ref, "loop*") .or. gc_ref_is(sym%ref, "recur") .or. &
          gc_ref_is(sym%ref, "defmacro*") .or. gc_ref_is(sym%ref, "quasiquote") .or. &
          gc_ref_is(sym%ref, "try") .or. gc_ref_is(sym%ref, "throw") .or. &
          gc_ref_is(sym%ref, "lazy-seq*") .or. gc_ref_is(sym%ref, ".") .or. &
          gc_ref_is(sym%ref, "new") .or. gc_ref_is(sym%ref, "clojure.core/import*") .or. &
          gc_ref_is(sym%ref, "set!") .or. &
          gc_ref_is(sym%ref, "case*") .or. &
          gc_ref_is(sym%ref, "deftype*") .or. gc_ref_is(sym%ref, "reify*") .or. &
          gc_ref_is(sym%ref, "proxy") .or. &
          gc_ref_is(sym%ref, "monitor-enter") .or. gc_ref_is(sym%ref, "monitor-exit") .or. &
          gc_ref_is(sym%ref, "var")
  end function is_special



  ! (deftype* user/Name user.Name [fields]
  !    :implements [ifaces] opt val ...
  !    (methodName [this args*] body)*)
  !
  ! The shape emit-deftype* builds. Nothing here generates a class --
  ! there is no classloader to put one in, and clotran recognises a
  ! class by the SHAPE of its name rather than by looking one up. So
  ! the type is an object in a global table, keyed by the same keyword
  ! a class literal evaluates to, which is what makes `new`,
  ! `instance?` and a protocol's :impls lookup all agree about what
  ! user.Name means without a hierarchy to walk.


  ! (reify* [ifaces] (methodName [this args*] body)*)
  !
  ! The same machinery with no fields and no name anyone can write, so
  ! the type is built and instantiated in one step and never
  ! registered -- nothing can ask for it by name, and registering one
  ! per evaluation would be a leak. The method bodies ARE closures
  ! over the surrounding scope, which reify's docstring requires and
  ! deftype's forbids; here they are closures either way, and the
  ! difference is invisible because a deftype method body is written
  ! at the top level.


  ! (proxy [supers] [ctor-args] (name [args*] body*)*)
  !
  ! REIFY WITH TWO DIFFERENCES, which is why it is built on the same
  ! machinery rather than beside it:
  !
  !   - `this` is IMPLICIT. A reify method names it as its first
  !     parameter; a proxy method does not, and the body says `this`
  !     anyway. So each parameter vector gets one prepended.
  !
  !   - arities nest. reify writes one form per arity and lets
  !     build_type group them by name; proxy writes
  !     (write ([x] ...) ([b o l] ...)) as ONE form. That is flattened
  !     back into build_type's shape here.
  !
  ! The CONSTRUCTOR ARGUMENTS are read and discarded. There is no
  ! superclass to construct -- clotran's classes are its type tags and
  ! form no hierarchy (DEVIATIONS.md 4) -- so a proxy overrides
  ! everything it answers to or answers to nothing, and proxy-super has
  ! nothing to call. Recorded in DEVIATIONS.md.
  !
  ! `proxy` is a MACRO in Clojure, in core_proxy.clj, which is not
  ! vendored (src/clj/clojure/PROVENANCE.md) because it is written
  ! against the class loader. clojure.pprint's writers are proxies, so
  ! without this the pretty printer cannot exist at all.


  ! Proxy method forms, rewritten into the one-arity-per-form shape
  ! build_type reads, with `this` prepended to every parameter vector.
  recursive function proxy_methods(forms, roots) result(out)
    type(gc_value), intent(in) :: forms
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, mname, second, acc, w, clauses
    integer :: base, i

    base = vs_enter(6)
    call vs_set(base + 1, forms)
    acc = gcv_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, acc)
    call vs_set(base + 3, vs_get(base + 1))

    do while (gcl_count(vs_get(base + 3)) > 0)
       m = strip_meta(gcl_first(vs_get(base + 3)))
       call vs_set(base + 4, m)
       mname = strip_meta(gcl_first(vs_get(base + 4)))
       if (mname%tag /= GCT_SYM) then
          call fail("proxy: a method needs a name")
          call vs_leave(base)
          return
       end if
       call vs_set(base + 5, mname)
       second = strip_meta(gcl_first(gcl_rest(vs_get(base + 4), [vs_get(base + 4)])))
       call vs_set(base + 6, second)
       if (gcv_is(vs_get(base + 6))) then
          ! One arity, written flat.
          acc = gcv_conj(vs_get(base + 2), &
               proxy_clause(vs_get(base + 5), vs_get(base + 6), &
                    gcl_rest(gcl_rest(vs_get(base + 4), [vs_get(base + 4)]), &
                         [vs_get(base + 4)]), [roots, vs_get(base + 2)]), &
               [roots, vs_get(base + 2)])
          call vs_set(base + 2, acc)
       else
          ! Several arities, each its own list.
          clauses = gcl_rest(vs_get(base + 4), [vs_get(base + 4)])
          call vs_set(base + 6, clauses)
          do i = 1, gcl_count(vs_get(base + 6))
             w = strip_meta(nth_of(vs_get(base + 6), i - 1))
             acc = gcv_conj(vs_get(base + 2), &
                  proxy_clause(vs_get(base + 5), strip_meta(gcl_first(w)), &
                       gcl_rest(w, [vs_get(base + 2)]), [roots, vs_get(base + 2)]), &
                  [roots, vs_get(base + 2)])
             call vs_set(base + 2, acc)
          end do
       end if
       call vs_set(base + 3, gcl_rest(vs_get(base + 3), [roots, vs_get(base + 2)]))
    end do

    out = seq_to_list(vs_get(base + 2), [roots, vs_get(base + 2)])
    call vs_leave(base)
  end function proxy_methods

  ! (name [this params*] body*) -- one method form in build_type's shape.
  recursive function proxy_clause(mname, params, body, roots) result(out)
    type(gc_value), intent(in) :: mname, params, body
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, ps
    integer :: base, i

    base = vs_enter(4)
    call vs_set(base + 1, mname)
    call vs_set(base + 2, params)
    call vs_set(base + 3, body)
    ! [this ~@params]
    ps = gcv_empty([roots, vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 4, ps)
    call vs_set(base + 4, gcv_conj(vs_get(base + 4), &
         gc_sym("this", [roots, vs_get(base + 4)]), [roots, vs_get(base + 4)]))
    do i = 0, gcv_count(vs_get(base + 2)) - 1
       call vs_set(base + 4, gcv_conj(vs_get(base + 4), gcv_nth(vs_get(base + 2), i), &
            [roots, vs_get(base + 2), vs_get(base + 4)]))
    end do
    out = gcl_cons(vs_get(base + 4), vs_get(base + 3), &
         [roots, vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 4, out)
    out = gcl_cons(vs_get(base + 1), vs_get(base + 4), &
         [roots, vs_get(base + 1), vs_get(base + 4)])
    call vs_leave(base)
  end function proxy_clause

  ! A type object from its parts, with each method form compiled to a
  ! closure. Methods sharing a NAME become clauses of ONE closure: an
  ! interface method overloaded by arity arrives as several forms, and
  ! select_clause is already how a multi-arity fn picks between them.
  !
  ! Grouped by re-scanning the method list once per distinct name,
  ! which is quadratic in the number of methods. A type has a handful,
  ! and this runs once per deftype rather than once per call.


  ! Each interface symbol as its class keyword. java.lang is
  ! implicitly imported, so short_class_name is what makes Object and
  ! java.lang.Object the same entry -- the same rule a class literal
  ! in value position follows.
  recursive function iface_keys(ifaces) result(out)
    type(gc_value), intent(in) :: ifaces
    type(gc_value) :: out, s, tmp
    integer :: base, i

    base = vs_enter(2)
    call vs_set(base + 1, ifaces)
    tmp = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 2, tmp)
    if (gcv_is(vs_get(base + 1))) then
       do i = 0, gcv_count(vs_get(base + 1)) - 1
          s = strip_meta(gcv_nth(vs_get(base + 1), i))
          if (s%tag /= GCT_SYM) cycle
          tmp = gc_key(class_key(gc_ref_text(s%ref)), &
               [vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 2, gcv_conj(vs_get(base + 2), tmp, &
               [vs_get(base + 1), vs_get(base + 2), tmp]))
       end do
    end if
    out = vs_get(base + 2)
    call vs_leave(base)
  end function iface_keys

  ! Every clause for one method name, in order, each with the type's
  ! fields bound around its body.
  recursive function method_clauses(name, methods, fields) result(out)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: methods, fields
    type(gc_value) :: out, m, mname, tmp
    integer :: base

    base = vs_enter(5)
    call vs_set(base + 1, methods)
    call vs_set(base + 2, fields)
    tmp = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, tmp)
    call vs_set(base + 4, vs_get(base + 1))

    do while (gcl_count(vs_get(base + 4)) > 0)
       m = strip_meta(gcl_first(vs_get(base + 4)))
       mname = strip_meta(gcl_first(m))
       if (mname%tag == GCT_SYM) then
          if (bare_name(mname) == name) then
             tmp = bind_fields(gcl_rest(m, [vs_get(base + 2), vs_get(base + 3)]), &
                  vs_get(base + 2))
             call vs_set(base + 5, tmp)
             tmp = gcv_conj(vs_get(base + 3), vs_get(base + 5), &
                  [vs_get(base + 3), vs_get(base + 5)])
             call vs_set(base + 3, tmp)
          end if
       end if
       tmp = gcl_rest(vs_get(base + 4), [vs_get(base + 3), vs_get(base + 4)])
       call vs_set(base + 4, tmp)
    end do

    out = seq_to_list(vs_get(base + 3), [vs_get(base + 3)])
    call vs_leave(base)
  end function method_clauses

  ! One clause -- (params body...) -- with the type's fields bound
  ! around the body, because a method body sees its fields as PLAIN
  ! NAMES and not through `this`. On the JVM they are real fields on a
  ! real class; here the body is wrapped in a let* that reads each one
  ! off the instance.
  !
  ! A field whose name a PARAMETER also uses is left out: the
  ! parameter is bound outside this let*, so binding the field too
  ! would shadow the argument the caller passed. Clojure resolves that
  ! the other way round, the parameter winning, and skipping is how
  ! this gets the same answer.
  recursive function bind_fields(clause, fields) result(out)
    type(gc_value), intent(in) :: clause, fields
    type(gc_value) :: out, params, this, f, tmp
    integer :: base, i

    out = clause
    if (.not. gcv_is(fields)) return
    if (gcv_count(fields) == 0) return
    params = strip_meta(gcl_first(clause))
    if (.not. gcv_is(params)) return
    if (gcv_count(params) == 0) return
    this = strip_meta(gcv_nth(params, 0))
    if (this%tag /= GCT_SYM) return

    base = vs_enter(6)
    call vs_set(base + 1, clause)
    call vs_set(base + 2, fields)
    call vs_set(base + 3, params)
    call vs_set(base + 4, this)
    tmp = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 5, tmp)

    do i = 0, gcv_count(vs_get(base + 2)) - 1
       f = strip_meta(gcv_nth(vs_get(base + 2), i))
       if (f%tag /= GCT_SYM) cycle
       if (params_bind(vs_get(base + 3), gc_ref_text(f%ref))) cycle
       tmp = gcv_conj(vs_get(base + 5), f, [vs_get(base + 5), f])
       call vs_set(base + 5, tmp)
       tmp = field_read(vs_get(base + 4), gc_ref_text(f%ref), &
            [vs_get(base + 4), vs_get(base + 5)])
       call vs_set(base + 6, tmp)
       tmp = gcv_conj(vs_get(base + 5), vs_get(base + 6), &
            [vs_get(base + 5), vs_get(base + 6)])
       call vs_set(base + 5, tmp)
    end do

    if (gcv_count(vs_get(base + 5)) > 0) then
       ! (params (let* [f (. this -f) ...] body...))
       tmp = gcl_cons(vs_get(base + 5), &
            gcl_rest(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 5)]), &
            [vs_get(base + 1), vs_get(base + 5)])
       call vs_set(base + 6, tmp)
       tmp = gcl_cons(gc_sym("let*", [vs_get(base + 6)]), vs_get(base + 6), &
            [vs_get(base + 1), vs_get(base + 6)])
       call vs_set(base + 6, tmp)
       tmp = gcl_cons(vs_get(base + 6), gcl_empty([vs_get(base + 6)]), &
            [vs_get(base + 6)])
       call vs_set(base + 6, tmp)
       out = gcl_cons(vs_get(base + 3), vs_get(base + 6), &
            [vs_get(base + 3), vs_get(base + 6)])
    end if
    call vs_leave(base)
  end function bind_fields

  ! Whether a parameter vector already binds this name. Destructuring
  ! forms are not looked inside: maybe-destructured has already turned
  ! those into gensyms plus a let, so what arrives here is a flat
  ! vector of plain names.
  logical function params_bind(params, name)
    type(gc_value), intent(in) :: params
    character(len=*), intent(in) :: name
    type(gc_value) :: p
    integer :: i
    params_bind = .false.
    do i = 0, gcv_count(params) - 1
       p = strip_meta(gcv_nth(params, i))
       if (p%tag /= GCT_SYM) cycle
       if (gc_ref_is(p%ref, name)) then
          params_bind = .true.
          return
       end if
    end do
  end function params_bind

  ! The form (. this -name) -- a field read, spelled the way eval_dot
  ! reads one.
  function field_read(this, name, roots) result(out)
    type(gc_value), intent(in) :: this
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, tmp
    integer :: base

    base = vs_enter(2)
    call vs_set(base + 1, this)
    tmp = gcl_empty(roots)
    call vs_set(base + 2, tmp)
    tmp = gc_sym("-" // name, [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 2, gcl_cons(tmp, vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 2), tmp]))
    call vs_set(base + 2, gcl_cons(vs_get(base + 1), vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 2)]))
    tmp = gc_sym(".", [vs_get(base + 1), vs_get(base + 2)])
    out = gcl_cons(tmp, vs_get(base + 2), [vs_get(base + 2), tmp])
    call vs_leave(base)
  end function field_read

  ! The type table. Keyed by the class keyword rather than the raw
  ! name so that a lookup here and an instance? test cannot disagree
  ! about java.lang.
  subroutine register_type(ty)
    type(gc_value), intent(in) :: ty
    type(gc_value) :: tbl, k
    integer :: base

    base = vs_enter(3)
    call vs_set(base + 1, ty)
    if (gc_root_live(types_root)) then
       call vs_set(base + 2, gc_root_get(types_root))
    else
       call vs_set(base + 2, gca_empty([vs_get(base + 1)]))
    end if
    k = gc_key(short_class_name(class_text(vs_get(base + 1))), &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, k)
    tbl = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 1), &
         [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 2, tbl)
    ! Under the BARE name too, which is the (import clojure.core.Point)
    ! that deftype emits and that clotran has nowhere to record. It is
    ! what makes (Point. 3 4) and (new Point 3 4) find the type; see
    ! class_matches for what it costs.
    block
      character(len=:), allocatable :: full
      integer :: i, last_dot
      full = class_text(vs_get(base + 1))
      last_dot = 0
      do i = 1, len(full)
         if (full(i:i) == ".") last_dot = i
      end do
      if (last_dot > 0 .and. last_dot < len(full)) then
         k = gc_key(full(last_dot+1:), [vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, k)
         tbl = gca_assoc(vs_get(base + 2), vs_get(base + 3), vs_get(base + 1), &
              [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
         call vs_set(base + 2, tbl)
      end if
    end block
    call gc_global_keep(types_root, vs_get(base + 2))
    call vs_leave(base)
  end subroutine register_type

  ! The type registered under a class name, or nil.
  function find_type(cname) result(out)
    character(len=*), intent(in) :: cname
    type(gc_value) :: out, tbl
    integer :: base

    out = gc_nil()
    if (.not. gc_root_live(types_root)) return
    base = vs_enter(1)
    tbl = gc_root_get(types_root)
    call vs_set(base + 1, tbl)
    out = gca_get(vs_get(base + 1), &
         gc_key(class_key(cname), [vs_get(base + 1)]))
    call vs_leave(base)
  end function find_type

  ! (new user.Name f1 f2) for a type deftype* created: the fields in
  ! declaration order, which is the one constructor deftype defines.


  ! How many TRAILING fields are defrecord's bookkeeping, counted by
  ! name exactly as Compiler.java counts altCtorDrops. Zero for a plain
  ! deftype, which is what keeps its arity check exact.
  integer function alt_ctor_drops(fields)
    type(gc_value), intent(in) :: fields
    type(gc_value) :: f
    integer :: i
    alt_ctor_drops = 0
    do i = gcv_count(fields) - 1, 0, -1
       f = strip_meta(gcv_nth(fields, i))
       if (f%tag /= GCT_SYM) exit
       if (.not. (gc_ref_is(f%ref, "__meta") .or. gc_ref_is(f%ref, "__extmap") &
            .or. gc_ref_is(f%ref, "__hash") .or. gc_ref_is(f%ref, "__hasheq"))) exit
       alt_ctor_drops = alt_ctor_drops + 1
    end do
  end function alt_ctor_drops

  ! The values a record's short constructors supply for the fields the
  ! caller left off: nil for __meta and __extmap, 0 for the two hash
  ! caches. By NAME rather than by position, so dropping four and
  ! dropping two both land the right value in the right field.
  function pad_record_fields(given, fields) result(out)
    type(gc_value), intent(in) :: given, fields
    type(gc_value) :: out, f, fill, tmp
    integer :: base, i

    base = vs_enter(3)
    call vs_set(base + 1, given)
    call vs_set(base + 2, fields)
    call vs_set(base + 3, vs_get(base + 1))
    do i = gcv_count(vs_get(base + 1)), gcv_count(vs_get(base + 2)) - 1
       f = strip_meta(gcv_nth(vs_get(base + 2), i))
       fill = gc_nil()
       if (f%tag == GCT_SYM) then
          if (gc_ref_is(f%ref, "__hash") .or. gc_ref_is(f%ref, "__hasheq")) &
               fill = gc_int(0)
       end if
       tmp = gcv_conj(vs_get(base + 3), fill, [vs_get(base + 2), vs_get(base + 3)])
       call vs_set(base + 3, tmp)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function pad_record_fields

  ! --- deftype instances in the generic operations -----------------
  !
  ! A record defines valAt, assoc, count, seq, cons, equiv and the rest
  ! as ordinary methods, in vendored core_deftype.clj, and they are
  ! correct -- (.valAt p :a) answered 1 before any of this existed. What
  ! was missing was that `get`, `count`, `seq`, `assoc` and `=` never
  ! asked. They went straight to the map layer, which does not know what
  ! an instance is, and every one of them answered nil, 0 or false
  ! instead of failing: (:a p) was nil, (count p) was 0,
  ! (= (->P 1 2) (->P 1 2)) was false.
  !
  ! So each of those builtins now offers the instance its own method
  ! first. That is what an interface IS here -- clotran has no class to
  ! check, so "implements ILookup" means "declares valAt" -- and it
  ! means records work through Clojure's own code rather than through a
  ! second implementation of records written in Fortran.
  !
  ! `found` is reported rather than guessed at, so a caller falls back
  ! to the map layer only when the type really declares nothing. A
  ! plain deftype declares none of these, so (count some-point) still
  ! reaches the old path and is still wrong in the old way -- it is not
  ! a collection, and making it answer 0 quietly is the bug this
  ! comment is about.

  ! The closure an instance's type declares under a method name, or nil.
  function inst_method(inst, name) result(out)
    type(gc_value), intent(in) :: inst
    character(len=*), intent(in) :: name
    type(gc_value) :: out, tbl
    out = gc_nil()
    if (gc_kind(inst) /= OBJ_INST) return
    tbl = gc_slot(gc_slot(inst, 1), 3)
    out = gca_get(tbl, gc_key(name, [inst, tbl]))
  end function inst_method

  ! Applies one, with `this` as the first argument -- a method's own
  ! parameter list names it, exactly as eval_dot passes it.
  recursive function inst_invoke(inst, name, rest_args, found) result(out)
    type(gc_value), intent(in) :: inst, rest_args
    character(len=*), intent(in) :: name
    logical, intent(out) :: found
    type(gc_value) :: out, m, tmp
    integer :: base, i

    out = gc_nil()
    found = .false.
    m = inst_method(inst, name)
    if (gc_kind(m) /= OBJ_CLOSURE) return
    found = .true.

    base = vs_enter(4)
    call vs_set(base + 1, inst)
    call vs_set(base + 2, m)
    call vs_set(base + 3, rest_args)
    tmp = gcv_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 4, tmp)
    tmp = gcv_conj(vs_get(base + 4), vs_get(base + 1), &
         [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 4, tmp)
    do i = 0, gcv_count(vs_get(base + 3)) - 1
       tmp = gcv_conj(vs_get(base + 4), gcv_nth(vs_get(base + 3), i), &
            [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), vs_get(base + 4)])
       call vs_set(base + 4, tmp)
    end do
    out = apply(vs_get(base + 2), vs_get(base + 4))
    call vs_leave(base)
  end function inst_invoke

  ! The same, for the common no-extra-argument case.
  recursive function inst_invoke0(inst, name, found) result(out)
    type(gc_value), intent(in) :: inst
    character(len=*), intent(in) :: name
    logical, intent(out) :: found
    type(gc_value) :: out, empty
    integer :: base
    base = vs_enter(1)
    call vs_set(base + 1, inst)
    empty = gcv_empty([vs_get(base + 1)])
    out = inst_invoke(vs_get(base + 1), name, empty, found)
    call vs_leave(base)
  end function inst_invoke0

  ! The arguments from `from` onward, as a vector -- what a builtin
  ! has to hand inst_invoke once it has peeled off the target.
  function rest_args(args, from) result(out)
    type(gc_value), intent(in) :: args
    integer, intent(in) :: from
    type(gc_value) :: out, tmp
    integer :: base, i
    base = vs_enter(2)
    call vs_set(base + 1, args)
    tmp = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 2, tmp)
    do i = from, gcv_count(vs_get(base + 1)) - 1
       tmp = gcv_conj(vs_get(base + 2), gcv_nth(vs_get(base + 1), i), &
            [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, tmp)
    end do
    out = vs_get(base + 2)
    call vs_leave(base)
  end function rest_args

  ! (get inst k) and (get inst k not-found) through the instance's own
  ! valAt. Both arities are real -- core_deftype defines valAt for each
  ! -- and the three-argument one is what makes a record distinguish a
  ! key bound to nil from a key that is absent.
  recursive function inst_lookup(inst, k, has_default, dflt, found) result(out)
    type(gc_value), intent(in) :: inst, k, dflt
    logical, intent(in) :: has_default
    logical, intent(out) :: found
    type(gc_value) :: out, argv, tmp
    integer :: base

    base = vs_enter(4)
    call vs_set(base + 1, inst)
    call vs_set(base + 2, k)
    call vs_set(base + 3, dflt)
    tmp = gcv_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 4, tmp)
    tmp = gcv_conj(vs_get(base + 4), vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 4, tmp)
    if (has_default) then
       tmp = gcv_conj(vs_get(base + 4), vs_get(base + 3), &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       call vs_set(base + 4, tmp)
    end if
    argv = vs_get(base + 4)
    out = inst_invoke(vs_get(base + 1), "valAt", argv, found)
    call vs_leave(base)
  end function inst_lookup

  ! (= inst other) through the instance's own equiv.
  recursive function inst_equiv(inst, other, found) result(out)
    type(gc_value), intent(in) :: inst, other
    logical, intent(out) :: found
    type(gc_value) :: out, tmp
    integer :: base
    base = vs_enter(3)
    call vs_set(base + 1, inst)
    call vs_set(base + 2, other)
    tmp = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, tmp)
    tmp = gcv_conj(vs_get(base + 3), vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 3, tmp)
    out = inst_invoke(vs_get(base + 1), "equiv", vs_get(base + 3), found)
    call vs_leave(base)
  end function inst_equiv

  ! (keys inst) / (vals inst), built from the instance's own seq --
  ! which hands back map entries, so the key is each entry's first and
  ! the value its second. Going through seq rather than reading the
  ! field vector directly is what makes a record's __extmap show up:
  ! an assoc'd key is not a field, but it IS in the seq.
  recursive function inst_entries(inst, want_keys, found) result(out)
    type(gc_value), intent(in) :: inst
    logical, intent(in) :: want_keys
    logical, intent(out) :: found
    type(gc_value) :: out, sq, items, e
    integer :: base, i

    out = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, inst)
    sq = inst_invoke0(vs_get(base + 1), "seq", found)
    if (.not. found) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 2, sq)
    items = coll_to_vector(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 2, items)
    out = gcl_empty([vs_get(base + 2)])
    call vs_set(base + 3, out)
    do i = gcv_count(vs_get(base + 2)) - 1, 0, -1
       e = gcv_nth(vs_get(base + 2), i)
       if (want_keys) then
          e = sq_first(e, [vs_get(base + 2), vs_get(base + 3)])
       else
          e = sq_first(sq_rest(e, [vs_get(base + 2), vs_get(base + 3)]), &
               [vs_get(base + 2), vs_get(base + 3)])
       end if
       out = gcl_cons(e, vs_get(base + 3), [vs_get(base + 2), vs_get(base + 3), e])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function inst_entries

  ! The static `create` every record class gets: (Person/create m),
  ! which is all map->Person is. Compiler.java emits it exactly when
  ! there are bookkeeping fields (`fields.count() > hintedFields.count()`,
  ! the same condition as altCtorDrops), so a plain deftype has none and
  ! asking for one still fails.
  !
  ! It reads each declared field out of the map by keyword and hands
  ! whatever is LEFT to __extmap -- that is what lets a record carry
  ! keys it never declared -- with nil for an empty remainder, as the
  ! emitted bytecode does.
  recursive function record_create(ty, m, roots) result(out)
    type(gc_value), intent(in) :: ty, m
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, fields, f, k, rest, vals, tmp
    integer :: base, i, declared

    base = vs_enter(5)
    call vs_set(base + 1, ty)
    call vs_set(base + 2, m)
    fields = gc_slot(vs_get(base + 1), 2)
    call vs_set(base + 3, fields)
    declared = gcv_count(vs_get(base + 3)) - alt_ctor_drops(vs_get(base + 3))

    vals = gcv_empty(roots)
    call vs_set(base + 4, vals)
    call vs_set(base + 5, vs_get(base + 2))
    do i = 0, declared - 1
       f = strip_meta(gcv_nth(vs_get(base + 3), i))
       k = gc_key(gc_ref_text(f%ref), [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5)])
       tmp = gcv_conj(vs_get(base + 4), gca_get(vs_get(base + 2), k), &
            [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5), k])
       call vs_set(base + 4, tmp)
       rest = gca_dissoc(vs_get(base + 5), k, &
            [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5), k])
       call vs_set(base + 5, rest)
    end do

    ! __meta, then __extmap -- nil when nothing is left over, which is
    ! what (not-empty ...) gives everywhere else a record builds one.
    tmp = gcv_conj(vs_get(base + 4), gc_nil(), [vs_get(base + 4), vs_get(base + 5)])
    call vs_set(base + 4, tmp)
    rest = vs_get(base + 5)
    if (gca_count(rest) == 0) rest = gc_nil()
    tmp = gcv_conj(vs_get(base + 4), rest, [vs_get(base + 4), vs_get(base + 5)])
    call vs_set(base + 4, tmp)

    tmp = pad_record_fields(vs_get(base + 4), vs_get(base + 3))
    call vs_set(base + 4, tmp)
    out = gc_obj(OBJ_INST, [vs_get(base + 1), vs_get(base + 4), gc_nil()], &
         [vs_get(base + 1), vs_get(base + 4)])
    call vs_leave(base)
  end function record_create

  ! A field of an instance by name, and whether there was one.
  function inst_field(inst, name, found) result(out)
    type(gc_value), intent(in) :: inst
    character(len=*), intent(in) :: name
    logical, intent(out) :: found
    type(gc_value) :: out, fields, f
    integer :: i

    out = gc_nil()
    found = .false.
    fields = gc_slot(gc_slot(inst, 1), 2)
    do i = 0, gcv_count(fields) - 1
       f = strip_meta(gcv_nth(fields, i))
       if (f%tag /= GCT_SYM) cycle
       if (gc_ref_is(f%ref, name)) then
          out = gcv_nth(gc_slot(inst, 2), i)
          found = .true.
          return
       end if
    end do
  end function inst_field

  ! Called by the collector for every object it is about to reuse.
  ! A MODULE procedure, not an internal one: flang segfaults passing
  ! a host-associated internal procedure as a callback on
  ! macOS/ARM64 (NOTES.md), the same rule gce_force follows.
  !
  ! Only kinds that own something outside the heap need a case here.
  ! Everything else is pure gc_value and the sweep has already done
  ! the whole job by returning the slot.
  subroutine gce_finalize_obj(kind, handle, extra)
    integer, intent(in) :: kind, handle, extra
    select case (kind)
    case (OBJ_ARRAY)
       ! extra is i2, the base_offset -- and -1 is the sentinel a
       ! SLICE can never carry, since its own base_offset is always
       ! >= 0. Only the array that set i2=-1 at construction owns the
       ! handle; a slice shares it and must not release what it does
       ! not own, or a still-live parent's buffer is freed out from
       ! under it.
       if (extra < 0) call gcna_release(handle)
    case (OBJ_REGEX, OBJ_MATCHER)
       ! Both hold an ICU object, and a Matcher holds a subject-text
       ! buffer as well -- ICU keeps only a shallow reference to that,
       ! so nothing else can free it. cre_close was declared and never
       ! called, so every compiled pattern and every matcher leaked its
       ! whole ICU handle. DEVIATIONS 14.
       call regex_release(handle)
    end select
  end subroutine gce_finalize_obj

  ! let* binds sequentially in a fresh child frame, so later bindings
  ! can see earlier ones -- which is what Clojure's let does.


  ! (letfn* [name (fn ...) name (fn ...)] body...)
  !
  ! let* with one difference, and it is the whole point: EVERY name is
  ! in scope in EVERY init, so the functions can call each other.
  ! Compiler.java's LetFnExpr calls that "pre-seed env (like Lisp
  ! labels)" -- it registers all the locals before analysing any init.
  !
  ! Here that is one frame, seeded with every name bound to nil before
  ! the first init runs. Each init is then evaluated in that same frame
  ! and overwrites its own seed, so a closure built by an earlier init
  ! captures the frame a later init is about to fill in. Nothing can
  ! observe the nil unless an init CALLS a later name while defining
  ! itself rather than closing over it -- which is why Clojure's letfn
  ! only ever emits (fn ...) inits.
  !
  ! The frame is mutated rather than rebuilt per binding, unlike loop*,
  ! which rebinds into a fresh frame each iteration so a closure keeps
  ! what it captured. Here sharing one frame IS the requirement.


  ! loop* binds like let*, then iterates: evaluate the body, and if it
  ! hands back a recur, rebind the same names from the recur's
  ! arguments and go again. The bindings are rebound in a FRESH frame
  ! each time rather than mutated, so a closure made during one
  ! iteration keeps the values it captured.


  ! (recur a b) evaluates its arguments and hands back a marker. The
  ! nearest loop* or fn* catches it; anywhere else it simply escapes,
  ! which is a recur outside a recur point and would be a compile
  ! error in real Clojure. Left as a value here rather than diagnosed,
  ! since this evaluator has no compile pass to diagnose it in.


  ! Binds a parameter vector to arguments in a fresh frame, handling
  ! `&`: (fn* [a & more] ...) binds `more` to a LIST of whatever is
  ! left, empty rather than nil when nothing is -- which is what lets
  ! (apply f args) and variadic core functions work at all.
  !
  ! One routine for both fn* application and recur, so a variadic
  ! function can recur without the two disagreeing about arity.
  ! A value with any metadata wrapper taken off. core.clj hints
  ! constantly -- (fn instance? [^Class c x] ...), (list* ^{:once true}
  ! fn* ...) -- and everything that has to RECOGNISE a form has to see
  ! past the wrapper: a hinted parameter name, a hinted parameter
  ! vector, a hinted head symbol. Only `meta` looks at the wrapper
  ! itself.
  function strip_meta(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    out = v
    do while (gc_kind(out) == OBJ_META)
       out = gc_slot(out, 1)
    end do
  end function strip_meta

  ! `recur_mode` changes ONE thing, and it is a real Clojure rule:
  ! recur into a variadic arity binds the rest parameter DIRECTLY to
  ! the value given, instead of collecting the remaining arguments into
  ! a fresh seq. (recur ret (first ks) (next ks)) has to be able to
  ! hand ks a nil; re-collecting turns that nil into (nil), which is
  ! truthy, and (if ks ...) then never ends. core.clj's own disj is
  ! written exactly that way.


  ! A fresh frame binding names(i) to vals(i), for a recur.


  ! Every form in a body, last value wins.


  ! Two shapes, the same two real Clojure has:
  !
  !   (fn* [a b] body...)              one arity
  !   (fn* ([a] body) ([a b] body))    several
  !
  ! They are told apart by whether the first thing after fn* is a
  ! vector or a list, which is exactly how the reader leaves them.
  ! Multi-arity keeps its clauses in slot 4 -- the slot GC.f90's
  ! OBJ_CLOSURE comment already reserved for them -- and leaves slot 1
  ! nil, so "is this multi-arity" is one test rather than a flag.


  ! Picks the clause matching argc: an exact arity wins, otherwise the
  ! first variadic one that can take this many. Real Clojure resolves
  ! this at compile time; here it is a short linear scan, which is
  ! fine for the handful of clauses a fn ever has.




  ! (. target member) and (. target (member args...)) -- host interop.
  !
  ! Clojure's host is the JVM, so `.` there reaches arbitrary Java.
  ! Ours is Fortran, and the only classes that exist are clotran's own
  ! runtime types -- so this is not a subset of Java interop, it is the
  ! same door onto a different house. Anything unknown fails by MEMBER
  ! NAME, so a load report says what is missing rather than blaming
  ! `.` for all of it.
  !
  ! The executor has evaluated the target and the arguments. `class_target` says the target is a
  ! class NAME, a symbol never evaluated: a deftype's `create` or a
  ! static member.
  recursive function eval_dot(target0, mname, is_call, argv, class_target) result(out)
    type(gc_value), intent(in) :: target0, argv
    character(len=*), intent(in) :: mname
    logical, intent(in) :: is_call, class_target
    type(gc_value) :: out, dty, tv
    logical :: found
    integer :: base

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, target0)
    call vs_set(base + 2, argv)

    if (class_target) then
       ! A DEFTYPE CLASS in member position. The only static one has
       ! is a record's `create`, which is what map->Name calls.
       dty = find_type(gc_ref_text(target0%ref))
       if (gc_kind(dty) == OBJ_TYPE .and. mname == "create") then
          call vs_set(base + 3, dty)
          out = record_create(vs_get(base + 3), nth_or_nil(vs_get(base + 2), 0), &
               [vs_get(base + 3), vs_get(base + 2)])
          call vs_leave(base)
          return
       end if
       if (is_host_class(target0)) then
          out = static_member(gc_ref_text(target0%ref), mname, vs_get(base + 2))
          if (.not. has_error .and. is_call) out = apply(out, vs_get(base + 2))
          call vs_leave(base)
          return
       end if
       ! A class literal is_host_class does not know evaluates to the
       ! keyword naming its type tag; the retry below sees it as one.
       call vs_set(base + 1, gc_key(class_key(gc_ref_text(target0%ref)), [vs_get(base + 2)]))
    end if

    ! A deftype/reify instance answers its own methods and fields
    ! FIRST. They are what the type declares, and a host member of the
    ! same name would otherwise shadow the implementation the program
    ! actually wrote.
    tv = strip_meta(vs_get(base + 1))
    if (gc_kind(tv) == OBJ_INST .and. len(mname) > 0) then
       call vs_set(base + 3, tv)
       ! (.-name x) is a field read and never a call; a bare name is
       ! a method if the type has one and a field otherwise, which
       ! is the order Compiler's HostExpr resolves them in.
       if (mname(1:1) == "-") then
          out = inst_field(vs_get(base + 3), mname(2:), found)
          if (.not. found) call fail("no such field: " // &
               class_text(vs_get(base + 3)) // "." // mname(2:))
          call vs_leave(base)
          return
       end if
       call vs_set(base + 4, gca_get(gc_slot(gc_slot(vs_get(base + 3), 1), 3), &
            gc_key(mname, [vs_get(base + 3)])))
       ! Writer.append is a concrete method of the superclass that calls
       ! the write the proxy defined: (newline) is (.append *out* ...),
       ! and a proxy over Writer that only wrote `write` inherits it.
       if (gc_kind(vs_get(base + 4)) /= OBJ_CLOSURE .and. mname == "append") then
          call vs_set(base + 4, gca_get(gc_slot(gc_slot(vs_get(base + 3), 1), 3), &
               gc_key("write", [vs_get(base + 3)])))
          ! append(char) reaches write(int): the code point, not the char.
          if (gcv_count(vs_get(base + 2)) == 1) then
             if (tag_of(gcv_nth(vs_get(base + 2), 0)) == GCT_CHAR) then
                call vs_set(base + 2, gcv_conj(gcv_empty([vs_get(base + 3)]), &
                     gc_int(int_of(gcv_nth(vs_get(base + 2), 0))), [vs_get(base + 3)]))
             end if
          end if
       end if
       if (gc_kind(vs_get(base + 4)) == OBJ_CLOSURE) then
          ! `this` is an explicit first parameter of the method, so
          ! the target is prepended exactly as for a host member.
          call vs_set(base + 2, cons_vec(vs_get(base + 3), vs_get(base + 2), [vs_get(base + 4)]))
          out = apply(vs_get(base + 4), vs_get(base + 2))
          call vs_leave(base)
          return
       end if
       out = inst_field(vs_get(base + 3), mname, found)
       if (found) then
          call vs_leave(base)
          return
       end if
    end if

    out = instance_member(mname, vs_get(base + 1))
    if (.not. has_error) then
       ! The target is the first argument, which is all an instance
       ! method is: (.withMeta x m) calls with-meta on x and m.
       call vs_set(base + 4, out)
       call vs_set(base + 2, cons_vec(vs_get(base + 1), vs_get(base + 2), [vs_get(base + 4)]))
       out = apply(vs_get(base + 4), vs_get(base + 2))
       call vs_leave(base)
       return
    end if
    call gce_clear_error()

    if (mname == "setMacro" .and. gcn_is_var(vs_get(base + 1))) then
       ! Var.setMacro is alterMeta(assoc, {:macro true}) -- macro-ness
       ! is METADATA ON THE VAR, not a flag on the function. That is
       ! what makes (:macro (meta (var when))) true, and what makes
       ! (def foo some-macro) bind a plain function rather than a macro.
       call var_set_macro(vs_get(base + 1))
       out = gc_nil()
    else if (tv%tag == GCT_KEY) then
       ! A class reached through a VARIABLE, not written as a
       ! literal. core.clj's `cast` is (. c (cast x)) with c a
       ! parameter, so the analysis -- which tests the symbol --
       ! cannot see it; by here the target has been evaluated and IS
       ! the class. Retrying it as a static member is what makes
       ! (cast Number 1.5) work, and any other class held in a
       ! variable with it.
       out = static_member(gc_ref_text(tv%ref), mname, vs_get(base + 2))
       if (.not. has_error .and. is_call) out = apply(out, vs_get(base + 2))
    else
       ! Name the TARGET as well as the member: "no such member:
       ! create" alone does not say which create.
       call fail("no such member: " // class_name_of(tv) // "." // mname)
    end if
    call vs_leave(base)
  end function eval_dot

  ! [x, v...]
  function cons_vec(x, v, roots) result(out)
    type(gc_value), intent(in) :: x, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base
    base = vs_enter(3)
    call vs_set(base + 1, x)
    call vs_set(base + 2, v)
    out = gcv_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    out = gcv_conj(vs_get(base + 3), vs_get(base + 1), [roots, vs_get(base + 2)])
    call vs_set(base + 3, out)
    out = concat_vecs(vs_get(base + 3), vs_get(base + 2), [roots, vs_get(base + 1)])
    call vs_leave(base)
  end function cons_vec



  ! (.member target args...) is (. target member args...), which is
  ! where macroexpand1 turns it into too -- the sugar is a rewrite, not
  ! a second kind of call.
  ! Whether a set! target is (.__methodImplCache f).
  logical function is_cache_field(form)
    type(gc_value), intent(in) :: form
    type(gc_value) :: f2, h2
    is_cache_field = .false.
    f2 = strip_meta(form)
    if (.not. gcl_is(f2)) return
    if (gcl_count(f2) < 2) return
    h2 = strip_meta(gcl_first(f2))
    if (h2%tag /= GCT_SYM) return
    is_cache_field = gc_ref_is(h2%ref, ".__methodImplCache")
  end function is_cache_field

  logical function is_member_sym(sym)
    type(gc_value), intent(in) :: sym
    character(len=:), allocatable :: t
    is_member_sym = .false.
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    if (len(t) < 2) return
    ! `..` IS NOT A MEMBER ACCESS, it is core.clj's threading
    ! macro. Clojure never has to say so: Compiler.macroexpand1
    ! asks isMacro BEFORE it reaches the dot sugar, and `..` is
    ! a macro. clotran asks the other way round, which is
    ! equivalent for every other name -- .foo is never a macro --
    ! and wrong for exactly this one, where (.. a getClass
    ! isArray) read as the member "." on a.
    if (t(2:2) == ".") return
    is_member_sym = (t(1:1) == ".")
  end function is_member_sym




  ! Whether a symbol names a host class. Compiler.maybeClass asks the
  ! classloader; there is nothing to ask here, so the shape of the name
  ! has to answer: a dotted name, or a bare capitalised one, which is
  ! what java.lang.* being imported into every namespace amounts to.
  !
  ! Only ever reached once a symbol has failed to resolve as a local
  ! and as a Var, so it shadows nothing.
  ! A class name with an implicit java.lang qualifier removed.
  function short_class_name(t) result(s)
    character(len=*), intent(in) :: t
    character(len=:), allocatable :: s
    s = t
    if (len(t) > 10) then
       if (t(1:10) == "java.lang.") then
          if (index(t(11:), ".") == 0) s = t(11:)
       end if
    end if
  end function short_class_name

  logical function is_class_name(sym)
    type(gc_value), intent(in) :: sym
    character(len=:), allocatable :: t
    integer :: i, last_dot
    is_class_name = .false.
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    if (len(t) < 1) return
    if (index(t, "/") > 0) return
    last_dot = 0
    do i = 1, len(t)
       if (t(i:i) == ".") last_dot = i
    end do
    if (last_dot == len(t)) return
    is_class_name = (t(last_dot+1:last_dot+1) >= "A" .and. &
         t(last_dot+1:last_dot+1) <= "Z")
  end function is_class_name

  ! (Classname/member args) -- namesStaticMember, which Clojure decides
  ! by the qualifier not being a known namespace. Same rule here.
  ! (Classname. args) is (new Classname args) -- macroexpand1 rewrites
  ! a symbol whose name ENDS in a dot, the mirror of the one that starts
  ! with one.
  logical function is_ctor_sym(sym)
    type(gc_value), intent(in) :: sym
    character(len=:), allocatable :: t
    is_ctor_sym = .false.
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    if (len(t) < 2) return
    if (t(len(t):len(t)) /= ".") return
    is_ctor_sym = (t(1:1) /= ".")
  end function is_ctor_sym



  logical function is_static_call(sym)
    type(gc_value), intent(in) :: sym
    character(len=:), allocatable :: t
    integer :: slash
    type(gc_value) :: qual
    is_static_call = .false.
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    slash = index(t, "/")
    if (slash <= 1 .or. slash >= len(t)) return
    qual = gc_sym(t(1:slash-1), [sym])
    is_static_call = is_class_name(qual)
  end function is_static_call



  ! (new cname args...) once the executor has evaluated the arguments.
  recursive function eval_new(cname, argv) result(out)
    character(len=*), intent(in) :: cname
    type(gc_value), intent(in) :: argv
    type(gc_value) :: out, thunk
    integer :: base

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, argv)

    if (cname == "clojure.lang.Reduced") then
       ! (reduced x) wraps a value to say "stop reducing". A
       ! one-key map is enough to carry the mark and the value,
       ! and the key is one no Clojure program can write.
       call vs_set(base + 3, nth_or_nil(vs_get(base + 1), 0))
       ! Two allocations in one argument list -- see range_cell.
       call vs_set(base + 4, gca_empty([vs_get(base + 3)]))
       call vs_set(base + 5, gc_key("clotran/reduced", &
            [vs_get(base + 3), vs_get(base + 4)]))
       out = gca_assoc(vs_get(base + 4), vs_get(base + 5), &
            vs_get(base + 3), [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5)])
    else if (cname == "clojure.lang.MethodImplCache" .or. &
         cname == "clojure.lang.MethodImplCache$Entry") then
       ! The protocol dispatch cache, as a MAP with named fields:
       ! (MethodImplCache. sym protocol methodk) and its 4-argument
       ! form, read back through .sym .protocol .methodk .map.
       !
       ! .fnFor always answers nil -- a permanently cold cache --
       ! which sends every protocol call down -cache-protocol-fn and
       ! find-protocol-method. That is the CORRECT path, just not
       ! the fast one, and it is what makes protocol dispatch work
       ! at all without a class to key on. DEVIATIONS.md 13.
       block
         type(gc_value) :: mp
         integer :: fi
         character(len=12) :: fname
         mp = gca_empty([vs_get(base + 1)])
         call vs_set(base + 3, mp)
         do fi = 0, gcv_count(vs_get(base + 1)) - 1
            select case (fi)
            case (0); fname = "sym"
            case (1); fname = "protocol"
            case (2); fname = "methodk"
            case default; fname = "map"
            end select
            mp = gca_assoc(vs_get(base + 3), &
                 gc_key(trim(fname), [vs_get(base + 3)]), gcv_nth(vs_get(base + 1), fi), &
                 [vs_get(base + 1), vs_get(base + 3)])
            call vs_set(base + 3, mp)
         end do
         if (gcv_count(vs_get(base + 1)) < 4) then
            ! Two allocations in one argument list -- see range_cell.
            call vs_set(base + 4, gc_key("map", [vs_get(base + 3)]))
            call vs_set(base + 5, gca_empty([vs_get(base + 3), vs_get(base + 4)]))
            mp = gca_assoc(vs_get(base + 3), vs_get(base + 4), vs_get(base + 5), &
                 [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5)])
            call vs_set(base + 3, mp)
         end if
         out = vs_get(base + 3)
       end block
    else if (cname == "CountDownLatch" .or. &
         cname == "java.util.concurrent.CountDownLatch") then
       ! A LATCH IS A COUNTER when there is one thread. `await`
       ! sends a count-down action to each agent and then waits
       ! on the latch -- and since dispatch here runs the action
       ! before it returns, the count is already zero by the time
       ! anything waits. So: an atom holding the count, .countDown
       ! decrements it, and .await has nothing to wait for.
       call vs_set(base + 3, nth_or_nil(vs_get(base + 1), 0))
       out = gc_obj(OBJ_ATOM, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
    else if (cname == "clojure.lang.Ref" .or. cname == "clojure.lang.Atom" .or. &
         cname == "clojure.lang.Agent") then
       ! A Ref IS an atom here: a mutable box, with no transaction
       ! around it. Single-threaded that is indistinguishable; the
       ! moment threads arrive it is not. DEVIATIONS.md 9.
       call vs_set(base + 3, nth_or_nil(vs_get(base + 1), 0))
       out = gc_obj(OBJ_ATOM, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
    else if (cname == "java.util.Properties" .or. cname == "Properties") then
       thunk = gca_empty([vs_get(base + 1)])
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_ATOM, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
    else if (is_box_class(cname)) then
       ! THE BOXING CONSTRUCTORS. (Long. 1) is 1, (String. "x") is
       ! "x" -- on the JVM they wrap a primitive in an object, and
       ! there is no unboxed number here to wrap. What they do have
       ! to do is CONVERT, because (Long. "12") parses and
       ! (Double. 1) widens, so each runs the same cast its
       ! valueOf does.
       if (gcv_count(vs_get(base + 1)) < 1) then
          call fail("no matching constructor: " // cname)
          call vs_leave(base)
          return
       end if
       call vs_set(base + 3, gcv_nth(vs_get(base + 1), 0))
       out = box_convert(cname, vs_get(base + 3), [vs_get(base + 1), vs_get(base + 3)])
    else if (cname == "PrintWriter" .or. cname == "java.io.PrintWriter" .or. &
         cname == "BufferedWriter" .or. cname == "java.io.BufferedWriter") then
       ! A PrintWriter over a writer IS that writer here. Java's
       ! wraps to add buffering and the print methods; clotran's
       ! writers already take text and hold it, so wrapping would
       ! only add a layer that forwards. What matters is that
       ! (let [s (StringWriter.) p (PrintWriter. s)] ... (str s))
       ! sees what was written to p, which sharing gives directly.
       if (gcv_count(vs_get(base + 1)) > 0) then
          thunk = strip_meta(gcv_nth(vs_get(base + 1), 0))
          if (gc_kind(thunk) == OBJ_SB .or. gc_kind(thunk) == OBJ_WRITER) then
             out = thunk
             call vs_leave(base)
             return
          end if
       end if
       thunk = gc_str("", [vs_get(base + 1)])
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_SB, [vs_get(base + 3)], [vs_get(base + 3)])
    else if (cname == "StringBuilder" .or. cname == "java.lang.StringBuilder" .or. &
         cname == "StringBuffer" .or. cname == "java.lang.StringBuffer" .or. &
         cname == "java.io.StringWriter" .or. cname == "StringWriter") then
       ! (StringBuffer. n) is a CAPACITY, not content -- the buffer
       ! starts empty. clojure.string/replace writes
       ! (StringBuffer. (.length s)) and every replacement it built
       ! came out with the length stuck on the front.
       thunk = gc_str("", [vs_get(base + 1)])
       if (gcv_count(vs_get(base + 1)) > 0) then
          thunk = strip_meta(gcv_nth(vs_get(base + 1), 0))
          if (thunk%tag == GCT_INT) thunk = gc_str("", [vs_get(base + 1)])
       end if
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_SB, [vs_get(base + 3)], [vs_get(base + 3)])
    else if (cname == "clojure.lang.ChunkBuffer") then
       ! (ChunkBuffer. capacity): a run to fill, count in i1
       thunk = gc_vec(max(int_of(nth_or_nil(vs_get(base + 1), 0)), 1), [vs_get(base + 1)])
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_CHUNKBUF, [vs_get(base + 3)], [vs_get(base + 3)])
       call gc_set_i1(out, 0)
    else if (cname == "clojure.lang.ChunkedCons") then
       ! (ChunkedCons. chunk more)
       out = gc_obj(OBJ_CHUNKSEQ, [nth_or_nil(vs_get(base + 1), 0), nth_or_nil(vs_get(base + 1), 1), gc_nil()], &
            [vs_get(base + 1)])
    else if (cname == "clojure.lang.MultiFn") then
       ! (new MultiFn name dispatch-fn default hierarchy). The
       ! hierarchy is accepted and ignored -- see DEVIATIONS.md 7.
       out = gc_obj(OBJ_MULTIFN, &
            [nth_or_nil(vs_get(base + 1), 0), nth_or_nil(vs_get(base + 1), 1), &
             nth_or_nil(vs_get(base + 1), 2), gca_empty([vs_get(base + 1)])], &
            [vs_get(base + 1)])
    else if (cname == "clojure.lang.Delay") then
       ! (delay body) is (new clojure.lang.Delay (fn [] body)) in
       ! core.clj, so the argument is already a no-argument closure and
       ! nothing here needs to know about the body.
       call vs_set(base + 3, nth_or_nil(vs_get(base + 1), 0))
       out = gc_obj(OBJ_DELAY, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
       call gc_set_i1(out, 0)
    else if (cname == "java.util.concurrent.ArrayBlockingQueue" .or. &
         cname == "java.util.concurrent.LinkedBlockingQueue" .or. &
         cname == "ArrayBlockingQueue") then
       ! A MUTABLE BOX HOLDING A VECTOR, which is what a queue is once
       ! the blocking is gone -- and with one thread there is nothing to
       ! block on. The capacity argument is accepted and ignored: a
       ! bound exists to make a producer wait, and nothing here waits.
       !
       ! core.clj builds exactly one, for tap>, and its consumer is a
       ! Thread that clotran never starts. So .offer accumulates and
       ! .take is the operation that cannot be honoured -- see
       ! instance_member, where it fails rather than inventing a value.
       thunk = gcv_empty([vs_get(base + 1)])
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_ATOM, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
    else if (cname == "clojure.lang.LazySeq") then
       call vs_set(base + 3, nth_or_nil(vs_get(base + 1), 0))
       out = gc_obj(OBJ_LAZY, [vs_get(base + 3), gc_nil(), gc_nil()], &
            [vs_get(base + 3)])
       call gc_set_i1(out, LAZY_PENDING)
    else if (is_throwable_class(cname)) then
       ! Every exception class core.clj names takes a message, and
       ! ex-info adds a data map. Anything else about a Java exception
       ! -- its hierarchy, its stack trace -- has nothing to correspond
       ! to here, so the class name is kept as written and nothing is
       ! invented around it.
       out = gc_obj(OBJ_ERR, &
            [gc_sym(cname, [vs_get(base + 1)]), &
             nth_or_nil(vs_get(base + 1), 0), &
             nth_or_nil(vs_get(base + 1), 1)], &
            [vs_get(base + 1)])
       ! filled in at construction, as Throwable's constructor does
       call vs_set(base + 3, out)
       call gc_set_slot(vs_get(base + 3), 4, frames_vec([vs_get(base + 3)]))
       out = vs_get(base + 3)
    else
       ! A type deftype* created. Last, so nothing above is shadowed
       ! by a deftype that happens to pick one of those names.
       thunk = find_type(cname)
       if (gc_kind(thunk) == OBJ_TYPE) then
          call vs_set(base + 3, thunk)
          out = construct_type_vals(vs_get(base + 3), vs_get(base + 1))
       else
          call fail("no such class: " // cname)
       end if
    end if
    call vs_leave(base)
  end function eval_new

  ! Whether a class name is one of the throwables. By SHAPE, because
  ! there is no class hierarchy to consult -- the same bargain
  ! is_class_name makes.
  logical function is_throwable_class(cname)
    character(len=*), intent(in) :: cname
    integer :: n
    n = len(cname)
    is_throwable_class = .false.
    if (n >= 9) then
       if (cname(n-8:n) == "Exception") is_throwable_class = .true.
    end if
    if (n >= 5) then
       if (cname(n-4:n) == "Error") is_throwable_class = .true.
    end if
    if (cname == "Throwable" .or. cname == "java.lang.Throwable") &
         is_throwable_class = .true.
    ! ExceptionInfo does not end in "Exception", and core.clj
    ! constructs one directly -- ex-info is
    ! (ExceptionInfo. msg map cause), imported under its short
    ! name. Both spellings, for the same reason Pattern needs
    ! both.
    if (cname == "ExceptionInfo" .or. &
         cname == "clojure.lang.ExceptionInfo") is_throwable_class = .true.
  end function is_throwable_class

  ! The java.lang boxes, whose constructors core.clj and
  ! Clojure's suite both write.
  logical function is_box_class(cname)
    character(len=*), intent(in) :: cname
    select case (cname)
    case ("Long", "java.lang.Long", "Integer", "java.lang.Integer", &
         "Short", "java.lang.Short", "Byte", "java.lang.Byte", &
         "Double", "java.lang.Double", "Float", "java.lang.Float", &
         "Boolean", "java.lang.Boolean", "String", "java.lang.String", &
         "Character", "java.lang.Character")
       is_box_class = .true.
    case default
       is_box_class = .false.
    end select
  end function is_box_class

  ! What a box constructor answers: the value, converted the way
  ! that box's valueOf would convert it.
  function box_convert(cname, v0, roots) result(out)
    character(len=*), intent(in) :: cname
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, v
    character(len=:), allocatable :: t
    integer(gc_ip) :: iv
    real(gc_dp) :: dv
    integer :: st
    v = strip_meta(v0)
    out = v
    select case (cname)
    case ("String", "java.lang.String")
       out = gc_str(text_of(v), roots)
    case ("Boolean", "java.lang.Boolean")
       if (v%tag == GCT_STR) then
          out = gc_bool(gc_ref_is(v%ref, "true"))
       else
          out = gc_bool(truthy(v))
       end if
    case ("Character", "java.lang.Character")
       if (v%tag == GCT_INT) out = gc_char(achar(int(v%ival, kind=4)))
    case ("Double", "java.lang.Double", "Float", "java.lang.Float")
       if (v%tag == GCT_STR) then
          t = gc_ref_text(v%ref)
          read(t, *, iostat=st) dv
          if (st == 0) then
             out = gc_real(dv)
          else
             call fail("For input string: " // t)
          end if
       else if (is_number(v)) then
          out = gc_real(num_dbl(v))
       end if
    case default
       ! The integer boxes.
       if (v%tag == GCT_STR) then
          t = gc_ref_text(v%ref)
          read(t, *, iostat=st) iv
          if (st == 0) then
             out = gc_int(iv)
          else
             call fail("For input string: " // t)
          end if
       else if (v%tag == GCT_REAL) then
          out = gc_int(int(v%rval, gc_ip))
       end if
    end select
  end function box_convert

  function nth_or_nil(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    out = gc_nil()
    if (i < gcv_count(v)) out = gcv_nth(v, i)
  end function nth_or_nil


  ! --- host members --------------------------------------------------
  !
  ! (. target member) and Class/member -- host interop. Clojure's host
  ! is the JVM, so `.` there reaches arbitrary Java. Ours is Fortran,
  ! and the only classes that exist are clotran's own runtime types --
  ! so this is not a subset of Java interop, it is the same door onto a
  ! different house. What is behind the door is DATA: hosttable.inc
  ! lists every class and member the loaded Clojure reaches for, and
  ! these three lookups read it. A member that is not a row does not
  ! exist, and fails by NAME so a load report says what is missing.

  ! --- imports ---------------------------------------------------------
  !
  ! (import* "java.util.regex.Pattern") records Pattern -> that name, so
  ! a class written by its short name afterwards means the imported one.
  ! One list for the whole process, not one per namespace, the same
  ! choice DEVIATIONS 17 makes for deftype names. java.lang needs no
  ! entry: it is implicitly imported, as on the JVM.
  subroutine record_import(full)
    character(len=*), intent(in) :: full
    character(len=64), allocatable :: nf(:), ns(:)
    integer :: i, last_dot
    last_dot = 0
    do i = 1, len(full)
       if (full(i:i) == ".") last_dot = i
    end do
    if (last_dot == 0) return
    do i = 1, n_imports
       if (import_short(i) == full(last_dot + 1:)) then
          import_full(i) = full
          return
       end if
    end do
    if (.not. allocated(import_full)) then
       allocate(import_full(32), import_short(32))
    else if (n_imports == size(import_full)) then
       allocate(nf(2 * n_imports), ns(2 * n_imports))
       nf(1:n_imports) = import_full
       ns(1:n_imports) = import_short
       call move_alloc(nf, import_full)
       call move_alloc(ns, import_short)
    end if
    n_imports = n_imports + 1
    import_full(n_imports) = full
    import_short(n_imports) = full(last_dot + 1:)
  end subroutine record_import

  ! A class name in full: a dotted name is already one, a bare name is
  ! the import it names, or java.lang's.
  function canon_class(name) result(c)
    character(len=*), intent(in) :: name
    character(len=:), allocatable :: c
    integer :: i
    c = name
    if (index(name, ".") > 0) return
    do i = 1, n_imports
       if (import_short(i) == name) then
          c = trim(import_full(i))
          return
       end if
    end do
    c = "java.lang." // name
  end function canon_class

  ! The ONE spelling a class keyword has, wherever it is built: the
  ! canonical name with java.lang stripped, so String and
  ! java.lang.String are :String, and IDeref after (import
  ! clojure.lang.IDeref) is :clojure.lang.IDeref like the literal
  ! written in full. A bare name nothing imported stays bare.
  function class_key(name) result(k)
    character(len=*), intent(in) :: name
    character(len=:), allocatable :: k
    k = short_class_name(canon_class(name))
  end function class_key


  ! Whether a symbol names a host class: one with a row in the table.
  ! Compiler.maybeClass asks the class loader; this asks the data.
  logical function is_host_class(sym)
    type(gc_value), intent(in) :: sym
    character(len=:), allocatable :: c
    is_host_class = .false.
    if (sym%tag /= GCT_SYM) return
    c = canon_class(gc_ref_text(sym%ref))
    is_host_class = any(HOST_STATICS(:)%cls == c)
  end function is_host_class

  ! A row's value: the native it names, or the constant it holds.
  function host_value(row, roots) result(out)
    type(hm), intent(in) :: row
    type(gc_value), intent(in) :: roots
    type(gc_value) :: out
    out = gc_nil()
    select case (row%id)
    case (1:);          out = native(row%id, trim(row%name), [roots])
    case (HK_INT);      out = gc_int(row%ival)
    case (HK_REAL);     out = gc_real(row%rval)
    case (HK_PINF);     out = gc_real(ieee_value(1.0_gc_dp, ieee_positive_inf))
    case (HK_NINF);     out = gc_real(ieee_value(1.0_gc_dp, ieee_negative_inf))
    case (HK_NAN);      out = gc_real(ieee_value(1.0_gc_dp, ieee_quiet_nan))
    case (HK_NIL);      out = gc_nil()
    case (HK_EMPTYMAP); out = gca_empty([roots])
    case (HK_SPECIALS); out = specials_map([roots])
    case (HK_TYPE);     out = gc_key(short_class_name(trim(row%cls)) // "/TYPE", [roots])
    end select
  end function host_value

  ! Class/member: a static member, or a class constant.
  function static_member(cls, mname, roots) result(out)
    character(len=*), intent(in) :: cls, mname
    type(gc_value), intent(in) :: roots
    type(gc_value) :: out
    character(len=:), allocatable :: c
    integer :: i
    out = gc_nil()
    c = canon_class(cls)
    ! ponytail: a linear scan of ~300 rows, at analysis time; sort and
    ! bisect if it ever shows in a profile.
    do i = 1, size(HOST_STATICS)
       if (HOST_STATICS(i)%cls == c .and. HOST_STATICS(i)%mem == mname) then
          out = host_value(HOST_STATICS(i), roots)
          return
       end if
    end do
    call fail("no such member: " // cls // "/" // mname)
  end function static_member

  ! .member: an instance member, by name alone -- the target's kind is
  ! the native's business.
  function instance_member(mname, roots) result(out)
    character(len=*), intent(in) :: mname
    type(gc_value), intent(in) :: roots
    type(gc_value) :: out
    integer :: i
    out = gc_nil()
    do i = 1, size(HOST_METHODS)
       if (HOST_METHODS(i)%mem == mname) then
          out = native(HOST_METHODS(i)%id, trim(HOST_METHODS(i)%name), [roots])
          return
       end if
    end do
    call fail("no such member: " // mname)
  end function instance_member

  ! Sets :macro true in the Var's metadata, creating the map if the Var
  ! has none. Var metadata is slot 2.
  subroutine var_set_macro(var)
    type(gc_value), intent(in) :: var
    type(gc_value) :: md
    integer :: base
    base = vs_enter(2)
    call vs_set(base + 1, var)
    md = gc_slot(vs_get(base + 1), 2)
    if (.not. gca_is(md)) md = gca_empty([vs_get(base + 1)])
    call vs_set(base + 2, md)
    md = gca_assoc(vs_get(base + 2), gc_key("macro", [vs_get(base + 1)]), &
         gc_bool(.true.), [vs_get(base + 1), vs_get(base + 2)])
    call gc_set_slot(vs_get(base + 1), 2, md)
    call vs_leave(base)
  end subroutine var_set_macro

  ! The Var a macro call's head names, or nil. This is Compiler.isMacro:
  ! the head is looked at UNEVALUATED, a local binding shadows it
  ! ("no local macros for now"), and macro-ness is read from the Var's
  ! metadata rather than from whatever the Var happens to hold.
  function macro_var(head, env) result(var)
    type(gc_value), intent(in) :: head, env
    type(gc_value) :: var, md
    var = gc_nil()
    if (head%tag /= GCT_SYM) return
    var = resolve_var(head, env)
    if (.not. gcn_is_var(var)) then
       var = gc_nil()
       return
    end if
    md = gc_slot(var, 2)
    if (.not. truthy(gca_get(md, gc_key("macro", [env])))) var = gc_nil()
  end function macro_var

  ! The Var a symbol names: the current namespace first, then
  ! clojure.core.
  !
  ! DEVIATION, recorded as #4. Clojure has no such fallback -- every
  ! namespace gets clojure.core through refer, which (ns ...) performs
  ! via refer-clojure. This is that referral hard-wired, and it differs
  ! wherever refer is selective: (refer-clojure :exclude [map]) cannot
  ! be honoured by a rule that has no map of what was referred.
  ! The Var a symbol names, in the namespace being analysed. Analysis
  ! runs in the writing namespace, so "current" is the right one; the
  ! executor never resolves a name (a deferred qualified symbol,
  ! DEVIATIONS 32, is the one exception and it comes back here).
  !
  ! A qualified symbol names its namespace, through an alias if there
  ! is one. An unqualified symbol not in the current namespace falls
  ! back to clojure.core -- DEVIATIONS 3, standing in for refer.
  function resolve_var(sym, roots) result(var)
    type(gc_value), intent(in) :: sym, roots
    type(gc_value) :: var, bare, ans
    character(len=:), allocatable :: t
    integer :: slash

    var = gc_nil()
    if (sym%tag /= GCT_SYM) return
    var = gcn_lookup(gcn_current([roots]), sym)
    if (gcn_is_var(var)) return

    t = gc_ref_text(sym%ref)
    slash = index(t, "/")
    if (slash > 1 .and. slash < len(t)) then
       bare = gc_sym(t(slash+1:), [roots])
       ans = alias_target(t(1:slash-1), [roots, bare])
       if (gc_kind(ans) == OBJ_NS) then
          var = gcn_lookup(ans, bare)
          if (gcn_is_var(var)) return
       end if
       var = gcn_lookup(gcn_find_or_create(t(1:slash-1), [roots, bare]), bare)
       if (.not. gcn_is_var(var)) var = gc_nil()
       return
    end if

    var = gcn_lookup(gcn_find_or_create("clojure.core", [roots]), sym)
  end function resolve_var

  ! Vectors already did this; maps and sets did not, and the cost was
  ! not cosmetic. #{'&} held the form (quote &) rather than the symbol,
  ! so destructure's (some #{'&} b) never found the rest marker and
  ! every (let [[a & b] ...]) produced a binding for b with nothing
  ! bound to it.




  ! Evaluates the head and every argument, then applies. Arguments
  ! accumulate in a GC vector rather than a Fortran array for the same
  ! reason the reader does it: the collector cannot see a local array.


  ! (try* body (catch* e handler)). The catch clause is optional; with
  ! none, an error simply propagates.
  !
  ! `e` is bound to the THROWN VALUE for a throw. For an internal
  ! error it is bound to a MAP, {:error "message"}, not to a bare
  ! string -- because a bare string is indistinguishable from
  ! (throw "x"), and a handler that wants to re-raise anything it does
  ! not recognise has no way to tell them apart. Clotran's older
  ! evaluator uses a string here; this is a deliberate improvement on
  ! it, not an accident of the port.
  ! (try body* (catch Class name body*)* (finally body*)?)
  !
  ! The real shape, not the two-form try*/catch* this used to be:
  ! several body forms, several catch clauses each naming a class to
  ! match, and an optional finally that runs either way.


  ! (case* expr shift mask default map<case-int [test then]> table-type
  !  test-type skip-check?)
  !
  ! On the JVM this compiles to a tableswitch, which is the whole point
  ! of the shift/mask apparatus core.clj builds around it. Here it is a
  ! lookup in that same map, keyed on the case-int recomputed from the
  ! runtime value -- so clojure.lang.Util/hash MUST be gc_hash, because
  ! these keys were built with it at macroexpansion time. Constant time
  ! either way; only the constant differs.


  ! Whether a case-int is in case*'s skip-check set.
  logical function in_skip(s, h)
    type(gc_value), intent(in) :: s
    integer, intent(in) :: h
    type(gc_value) :: st
    in_skip = .false.
    st = strip_meta(s)
    if (gc_kind(st) /= OBJ_SET) return
    in_skip = gca_contains(gc_slot(st, 1), gc_int(h))
  end function in_skip

  ! An integer out of a possibly metadata-wrapped value.
  integer function ival_of(v)
    type(gc_value), intent(in) :: v
    type(gc_value) :: t
    t = strip_meta(v)
    ival_of = t%ival
  end function ival_of

  ! Whether a form is a (catch ...) or (finally ...) clause.
  logical function is_clause(v, want)
    type(gc_value), intent(in) :: v
    character(len=*), intent(in) :: want
    type(gc_value) :: h
    is_clause = .false.
    if (.not. gcl_is(v)) return
    if (gcl_count(v) == 0) return
    h = strip_meta(gcl_first(v))
    if (h%tag /= GCT_SYM) return
    is_clause = gc_ref_is(h%ref, want)
  end function is_clause

  ! Whether a catch clause's class matches the thrown value. Throwable
  ! and Exception catch everything, which is what core.clj relies on;
  ! a named class matches what the value was constructed with.
  ! Throw a value a NAMED catch clause can match.
  !
  ! `fail` produces {:error "..."}, which is an ordinary map, and
  ! catch_matches only lets Throwable and Exception catch one of those.
  ! That is right for an internal failure nobody declared -- but some of
  ! core.clj's own functions are written AROUND a specific exception and
  ! read its absence as an answer:
  !
  !   (defn parse-long [s]
  !     (if (string? s)
  !       (try (Long/valueOf s) (catch NumberFormatException _ nil))
  !       ...))
  !
  ! so (parse-long "x") is nil in Clojure and was an ERROR here -- the
  ! catch could not match, and the failure escaped the function that
  ! existed to contain it.
  subroutine fail_as(class_name, msg, roots)
    character(len=*), intent(in) :: class_name, msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: e, cls, txt
    integer :: base

    base = vs_enter(2)
    cls = gc_sym(class_name, roots)
    call vs_set(base + 1, cls)
    txt = gc_str(msg, [vs_get(base + 1)])
    call vs_set(base + 2, txt)
    e = gc_obj(OBJ_ERR, [vs_get(base + 1), vs_get(base + 2), gc_nil()], &
         [vs_get(base + 1), vs_get(base + 2)])
    call set_thrown(e)
    has_error = .true.
    last_error = gcp_str(e, .true.)
    call vs_leave(base)
  end subroutine fail_as

  recursive function catch_matches(cls, exc, env) result(yes)
    type(gc_value), intent(in) :: cls, exc, env
    logical :: yes
    character(len=:), allocatable :: want
    type(gc_value) :: got

    yes = .true.
    if (cls%tag /= GCT_SYM) return
    want = gc_ref_text(cls%ref)
    if (want == "Throwable" .or. want == "java.lang.Throwable" .or. &
         want == "Exception" .or. want == "java.lang.Exception") return
    if (gc_kind(exc) /= OBJ_ERR) then
       yes = .false.
       return
    end if
    got = gc_slot(exc, 1)
    if (got%tag /= GCT_SYM) then
       yes = .false.
       return
    end if
    ! Either spelling. The class name is kept as the THROWING
    ! code wrote it, and the catch names it however the catching
    ! code wrote it -- ex-info constructs an ExceptionInfo under
    ! its short imported name, and Clojure's own suite catches
    ! clojure.lang.ExceptionInfo. class_matches knows the rule
    ! but only in one direction, so it is asked both ways.
    yes = class_matches(gc_ref_text(got%ref), want) .or. &
         class_matches(want, gc_ref_text(got%ref))
    ! ONE FACT OF HIERARCHY, because Clojure's own suite relies
    ! on it: ArityException extends IllegalArgumentException, so
    ! (thrown? IllegalArgumentException (f)) catches a bad-arity
    ! call. clotran's classes form no hierarchy (DEVIATIONS 4);
    ! this is the single edge that matters.
    if (.not. yes) then
       if (gc_ref_is(got%ref, "ArityException")) &
            yes = class_matches("IllegalArgumentException", want)
    end if
  end function catch_matches

  ! {:error "message"} -- an internal failure as an ordinary clotran
  ! map, so it prints, can be destructured, and is distinguishable
  ! from any value a program might itself throw.
  function error_value(msg, roots) result(v)
    character(len=*), intent(in) :: msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, k, text
    integer :: base

    base = vs_enter(3)
    v = gca_empty(roots)
    call vs_set(base + 1, v)
    k = gc_key("error", [vs_get(base + 1)])
    call vs_set(base + 2, k)
    text = gc_str(msg, [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, text)
    v = gca_assoc(vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), &
         [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_leave(base)
  end function error_value

  ! Raise a CLASSED exception, the way a (throw (Foo. msg)) in
  ! Clojure source would. `fail` alone produces clotran's
  ! internal {:error "..."} map, which no (catch SomeClass e)
  ! can match -- so an error clotran raises itself was
  ! uncatchable by name however well the message read.
  subroutine raise_class(cls, msg, roots)
    character(len=*), intent(in) :: cls, msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: e
    integer :: base

    base = vs_enter(2)
    call vs_set(base + 1, gc_sym(cls, roots))
    call vs_set(base + 2, gc_str(msg, [roots, vs_get(base + 1)]))
    e = gc_obj(OBJ_ERR, [vs_get(base + 1), vs_get(base + 2), gc_nil()], &
         [roots, vs_get(base + 1), vs_get(base + 2)])
    call set_thrown(e)
    has_error = .true.
    last_error = msg
    call vs_leave(base)
  end subroutine raise_class

  ! Clojure's own wording, from ArityException: "Wrong number of
  ! args (2) passed to: user/f". The count is what a reader of
  ! the message needs and "no matching arity" did not carry it.
  subroutine raise_arity(got, fn, roots)
    integer, intent(in) :: got
    type(gc_value), intent(in) :: fn
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nm
    character(len=16) :: buf
    character(len=:), allocatable :: who
    write(buf, '(I0)') got
    who = "fn"
    if (gc_kind(fn) == OBJ_CLOSURE) then
       nm = gc_slot(fn, 5)
       if (nm%tag == GCT_SYM) who = gc_ref_text(nm%ref)
    end if
    call raise_class("ArityException", &
         "Wrong number of args (" // trim(buf) // ") passed to: " // who, roots)
  end subroutine raise_arity

  ! A reference's functions -- its validator and its error
  ! handler -- as a small map in slot 4. An object has five
  ! slots; the value, the metadata, the error mode and the error
  ! itself take the others.
  function ref_fn_get(r, name, roots) result(out)
    type(gc_value), intent(in) :: r
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    out = gc_nil()
    if (r%tag /= GCT_OBJ) return
    out = gca_get(gc_slot(r, 4), gc_key(name, roots))
  end function ref_fn_get

  subroutine ref_fn_put(r, name, v, roots)
    type(gc_value), intent(in) :: r, v
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    integer :: base
    if (r%tag /= GCT_OBJ) return
    base = vs_enter(3)
    call vs_set(base + 1, r)
    call vs_set(base + 2, v)
    m = gc_slot(vs_get(base + 1), 4)
    if (.not. gca_is(m)) m = gca_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, m)
    call vs_set(base + 3, gca_assoc(vs_get(base + 3), &
         gc_key(name, [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)]), &
         vs_get(base + 2), [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)]))
    call gc_set_slot(vs_get(base + 1), 4, vs_get(base + 3))
    call vs_leave(base)
  end subroutine ref_fn_put

  ! Whether `v` passes `f`. A nil validator passes everything;
  ! anything else must answer truthy, and a false answer is an
  ! IllegalStateException with Clojure's own wording.
  function validate_ref(r, f, v, roots) result(ok)
    type(gc_value), intent(in) :: r, f, v
    type(gc_value), intent(in) :: roots(:)
    logical :: ok
    type(gc_value) :: fargs, res
    integer :: base
    ok = .true.
    if (f%tag == GCT_NIL) return
    base = vs_enter(2)
    call vs_set(base + 1, f)
    call vs_set(base + 2, v)
    fargs = gcv_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    fargs = gcv_conj(fargs, vs_get(base + 2), &
         [roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 2, fargs)
    res = apply(vs_get(base + 1), vs_get(base + 2))
    if (has_error) then
       ok = .false.
    else if (.not. truthy(res)) then
       ok = .false.
       call raise_class("IllegalStateException", "Invalid reference state", roots)
    end if
    call vs_leave(base)
    if (r%tag == GCT_NIL) return
  end function validate_ref

  ! Realises ONE cell of a lazy seq, memoised on the node so walking
  ! costs O(1) per element rather than re-running the thunk each time.
  ! A MODULE procedure, so it can be handed to the printer as a
  ! callback (flang will not take an internal one -- NOTES.md).
  !
  ! The thunk may itself hand back another lazy seq -- (lazy-seq
  ! (lazy-seq ...)), and more usefully whatever a `when` returned --
  ! so walk down to something concrete, realising as it goes. Each is
  ! memoised in its own node, so this never repeats work.
  recursive subroutine gce_force(v)
    type(gc_value), intent(in) :: v
    type(gc_value) :: r, args
    integer :: base

    if (gc_kind(v) /= OBJ_LAZY) return
    if (gc_i1(v) /= LAZY_PENDING) return

    base = vs_enter(2)
    call vs_set(base + 1, v)
    select case (gc_i2(vs_get(base + 1)))
    case (1)
       ! a native range tail: slot 1 = [lo hi step]
       args = gc_slot(vs_get(base + 1), 1)
       r = range_cell(gcv_nth(args, 0), gcv_nth(args, 1), gcv_nth(args, 2), [vs_get(base + 1)])
    case (2)
       ! a native iterate tail: slot 1 = [f x]; the next head is (f x)
       args = gc_slot(vs_get(base + 1), 1)
       call vs_set(base + 2, gcv_conj(gcv_empty([vs_get(base + 1)]), gcv_nth(args, 1), [vs_get(base + 1)]))
       r = apply(gcv_nth(gc_slot(vs_get(base + 1), 1), 0), vs_get(base + 2))
       if (.not. has_error) then
          call vs_set(base + 2, r)
          r = iterate_cell(gcv_nth(gc_slot(vs_get(base + 1), 1), 0), vs_get(base + 2), [vs_get(base + 1)])
       end if
    case default
       args = gcv_empty([vs_get(base + 1)])
       r = apply(gc_slot(vs_get(base + 1), 1), args)
    end select
    call vs_set(base + 2, r)
    if (has_error) then
       call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
       call vs_leave(base)
       return
    end if

    do while (gc_kind(vs_get(base + 2)) == OBJ_LAZY)
       call gce_force(vs_get(base + 2))
       if (gc_i1(vs_get(base + 2)) == LAZY_DELEG) then
          call gc_set_slot(vs_get(base + 1), 2, gc_slot(vs_get(base + 2), 2))
          call gc_set_i1(vs_get(base + 1), LAZY_DELEG)
          call vs_leave(base)
          return
       end if
       if (gc_i1(vs_get(base + 2)) == LAZY_CONS) then
          call gc_set_slot(vs_get(base + 1), 2, gc_slot(vs_get(base + 2), 2))
          call gc_set_slot(vs_get(base + 1), 3, gc_slot(vs_get(base + 2), 3))
          call gc_set_i1(vs_get(base + 1), LAZY_CONS)
          call vs_leave(base)
          return
       end if
       call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
       call vs_leave(base)
       return
    end do

    r = vs_get(base + 2)
    if (gc_kind(r) == OBJ_CHUNKSEQ) then
       ! A CHUNK SURVIVES THE LAZY SEQ. map, filter, keep and for all
       ! return (lazy-seq ... (chunk-cons (chunk b) ...)), and splitting
       ! that into a head and a tail here is what made every one of them
       ! answer a plain lazy seq: chunked-seq? was then false on it, so
       ! the next map down the pipeline took the one-at-a-time branch and
       ! the chunking never propagated past the first collection.
       call gc_set_slot(vs_get(base + 1), 2, r)
       call gc_set_i1(vs_get(base + 1), LAZY_DELEG)
       call vs_leave(base)
       return
    end if
    if (gcl_is(r)) then
       if (gcl_count(r) == 0) then
          call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
       else
          call gc_set_slot(vs_get(base + 1), 2, gcl_first(r))
          call gc_set_slot(vs_get(base + 1), 3, gcl_rest(r, [vs_get(base + 1)]))
          call gc_set_i1(vs_get(base + 1), LAZY_CONS)
       end if
    else if (gcv_is(r)) then
       if (gcv_count(r) == 0) then
          call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
       else
          call gc_set_slot(vs_get(base + 1), 2, gcv_nth(r, 0))
          call gc_set_slot(vs_get(base + 1), 3, &
               as_list_rest(r, [vs_get(base + 1)]))
          call gc_set_i1(vs_get(base + 1), LAZY_CONS)
       end if
    else
       ! ANYTHING ELSE SEQABLE, through seq. A thunk may return a view
       ! over a vector, a set, a map or a string -- (drop 2 [1 2 3 4])
       ! returns a view -- and treating those as EMPTY was silent: drop
       ! worked on a list and gave () on a vector, and take-nth built on
       ! drop then truncated every destructuring loop binding.
       block
         type(gc_value) :: sv
         sv = to_seq(vs_get(base + 2), [vs_get(base + 1)])
         if (sv%tag == GCT_NIL) then
            call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
         else
            call vs_set(base + 2, sv)
            call gc_set_slot(vs_get(base + 1), 2, &
                 sq_first(vs_get(base + 2), [vs_get(base + 1)]))
            call gc_set_slot(vs_get(base + 1), 3, &
                 sq_rest(vs_get(base + 2), [vs_get(base + 1)]))
            call gc_set_i1(vs_get(base + 1), LAZY_CONS)
         end if
       end block
    end if
    call vs_leave(base)
  end subroutine gce_force

  ! Everything but the first element of a vector, as a list.
  function as_list_rest(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    base = vs_enter(2)
    call vs_set(base + 1, v)
    out = gcl_empty(roots)
    call vs_set(base + 2, out)
    do i = gcv_count(vs_get(base + 1)) - 1, 1, -1
       out = gcl_cons(gcv_nth(vs_get(base + 1), i), vs_get(base + 2), &
            [vs_get(base + 1)])
       call vs_set(base + 2, out)
    end do
    out = vs_get(base + 2)
    call vs_leave(base)
  end function as_list_rest

  ! Applies a macro to the unevaluated argument forms.
  recursive function expand_macro(fn, form, env) result(out)
    type(gc_value), intent(in) :: fn, form, env
    type(gc_value) :: out, args, walk
    integer :: base

    base = vs_enter(5)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, form)
    call vs_set(base + 5, env)
    ! CLOTRAN_TRACE_MACRO=1 names every expansion on stderr. An
    ! expansion that shows up per ITERATION of a loop escaped analysis
    ! and is being paid for at call time; this is how the first one
    ! was found.
    if (trace_macros == 0) call read_trace_macros()
    if (trace_macros == 1) write(0, '(A,A)') "macro: ", first_form_name(form)
    ! The two HIDDEN PARAMETERS every macro takes: the whole form and
    ! the local environment. macroexpand1 builds the same call --
    ! RT.cons(form, RT.cons(LOCAL_ENV.get(), form.next())) -- and
    ! core.clj's macros name them &form and &env.
    args = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    args = gcv_conj(args, vs_get(base + 2), [vs_get(base + 1), vs_get(base + 2)])
    args = gcv_conj(args, vs_get(base + 5), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, args)
    walk = gcl_rest(vs_get(base + 2), [vs_get(base + 2)])
    call vs_set(base + 4, walk)
    do while (gcl_count(vs_get(base + 4)) > 0)
       args = gcv_conj(vs_get(base + 3), gcl_first(vs_get(base + 4)), &
            [vs_get(base + 1), vs_get(base + 2), vs_get(base + 4)])
       call vs_set(base + 3, args)
       walk = gcl_rest(vs_get(base + 4), [vs_get(base + 2)])
       call vs_set(base + 4, walk)
    end do
    out = apply(vs_get(base + 1), vs_get(base + 3))
    call vs_leave(base)
  end function expand_macro

  ! Syntax-quote, expanded into cons/concat calls exactly as mal and
  ! clotran's own qq_expand do:
  !
  !   (unquote x)              -> x
  !   ((splice-unquote x) ...) -> (concat x <rest>)
  !   (a ...)                  -> (cons <qq a> <rest>)
  !   a symbol                 -> (quote a)
  !   anything else            -> itself
  !
  ! Built right to left so the result comes out in order.
  recursive function qq_expand(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, elt, inner, sym
    integer :: base, i, n
    logical :: spliced

    ! Six slots, and every intermediate goes into one BEFORE anything
    ! that can allocate runs. The first version computed `sym` into a
    ! Fortran local and then called nth_of/qq_expand, both of which
    ! allocate -- so under torture the symbol was collected before it
    ! was ever stored, and the accumulated tail went with it. Only the
    ! torture pass showed it; the plain pass was perfectly green.
    base = vs_enter(6)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)

    if (gcv_is(form)) then
       ! `[a ~b] -- a vector inside syntax-quote. Expanded as a seq and
       ! rebuilt, which is what LispReader does: (apply vector (seq
       ! (concat ...))). Without this a vector passed straight through
       ! and every unquote inside it stayed literal, which is most of
       ! what a (let [...]) template is.
       out = qq_rebuild(form, "vec", vs_get(base + 2))
       call vs_leave(base)
       return
    end if

    if (gca_is(form)) then
       ! `{k ~v} -- flattened to k v k v, expanded as a seq, rebuilt as
       ! a map. syntaxQuote does the same through flattenMap. Missing
       ! this let a whole subtree through as literal data: every (ns ...)
       ! expands into a with-loading-context whose body is a MAP, and
       ! the gensym inside it was never renamed.
       out = qq_rebuild(flatten_map(form, vs_get(base + 2)), "hash-map", &
            vs_get(base + 2), .true.)
       call vs_leave(base)
       return
    end if

    if (gc_kind(form) == OBJ_SET) then
       out = qq_rebuild(set_elems(form, vs_get(base + 2)), "set", &
            vs_get(base + 2))
       call vs_leave(base)
       return
    end if

    if (gc_kind(form) == OBJ_META) then
       ! A HINTED form inside a template is still that form. (.getClass
       ! ^Object loading#) hides its gensym behind a wrapper, and
       ! treating the wrapper as an opaque leaf renamed the other
       ! occurrence of loading# and not this one -- which is worse than
       ! renaming neither.
       out = qq_expand(gc_slot(vs_get(base + 1), 1), vs_get(base + 2))
       call vs_leave(base)
       return
    end if

    if (.not. gcl_is(form)) then
       if (form%tag == GCT_SYM) then
          call vs_set(base + 1, auto_gensym(vs_get(base + 1)))
          call vs_set(base + 1, qq_alias(vs_get(base + 1), vs_get(base + 2)))
          sym = gc_sym("quote", [vs_get(base + 1)])
          call vs_set(base + 3, sym)
          out = gcl_empty([vs_get(base + 1), vs_get(base + 3)])
          out = gcl_cons(vs_get(base + 1), out, [vs_get(base + 3), out])
          out = gcl_cons(vs_get(base + 3), out, [vs_get(base + 1), out])
       else
          out = form
       end if
       call vs_leave(base)
       return
    end if

    ! (unquote x) -> x
    if (gcl_count(form) == 2) then
       head = gcl_first(form)
       if (head%tag == GCT_SYM) then
          if (gc_ref_is(head%ref, "unquote")) then
             out = nth_of(vs_get(base + 1), 1)
             call vs_leave(base)
             return
          end if
       end if
    end if

    n = gcl_count(vs_get(base + 1))
    out = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 4, out)
    do i = n - 1, 0, -1
       elt = nth_of(vs_get(base + 1), i)
       call vs_set(base + 5, elt)
       spliced = .false.
       if (gcl_is(elt)) then
          if (gcl_count(elt) == 2) then
             head = gcl_first(elt)
             if (head%tag == GCT_SYM) spliced = gc_ref_is(head%ref, "splice-unquote")
          end if
       end if
       if (spliced) then
          sym = gc_sym("concat", [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5)])
          call vs_set(base + 3, sym)
          inner = nth_of(vs_get(base + 5), 1)
       else
          sym = gc_sym("cons", [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5)])
          call vs_set(base + 3, sym)
          inner = qq_expand(vs_get(base + 5), vs_get(base + 2))
          if (has_error) then
             call vs_leave(base); return
          end if
       end if
       call vs_set(base + 6, inner)
       ! (sym inner <acc>), built back to front.
       out = gcl_empty([vs_get(base + 3), vs_get(base + 4), vs_get(base + 6)])
       out = gcl_cons(vs_get(base + 4), out, &
            [vs_get(base + 3), vs_get(base + 6), out])
       out = gcl_cons(vs_get(base + 6), out, [vs_get(base + 3), out])
       out = gcl_cons(vs_get(base + 3), out, [out])
       call vs_set(base + 4, out)
    end do
    out = vs_get(base + 4)
    call vs_leave(base)
  end function qq_expand

  ! x# inside a syntax-quote becomes one fresh name, the SAME fresh
  ! name everywhere it appears in that syntax-quote and a different one
  ! in the next. That is what makes a template able to bind a local
  ! without capturing the caller's -- (or x y) expands to a let over
  ! or__17__auto__, which no caller can have written.
  function auto_gensym(sym) result(out)
    type(gc_value), intent(in) :: sym
    type(gc_value) :: out, gmap, hit
    character(len=:), allocatable :: t
    character(len=24) :: buf
    integer :: base

    out = sym
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    if (len(t) < 2) return
    if (t(len(t):len(t)) /= "#") return
    if (index(t, "/") > 0) return
    if (.not. gc_root_live(gensym_root)) return

    base = vs_enter(3)
    call vs_set(base + 1, sym)
    gmap = gc_root_get(gensym_root)
    call vs_set(base + 2, gmap)
    hit = gca_get(vs_get(base + 2), vs_get(base + 1))
    if (hit%tag == GCT_SYM) then
       out = hit
       call vs_leave(base)
       return
    end if
    gensym_id = gensym_id + 1
    write(buf, '(I0)') gensym_id
    out = gc_sym(t(1:len(t)-1) // "__" // trim(buf) // "__auto__", &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    gmap = gca_assoc(vs_get(base + 2), vs_get(base + 1), vs_get(base + 3), &
         [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call gc_global_keep(gensym_root, gmap)
    out = vs_get(base + 3)
    call vs_leave(base)
  end function auto_gensym

  ! Compiler.resolveSymbol, as syntaxQuote calls it: an unqualified
  ! symbol in a template becomes ns/name -- the Var's own namespace if
  ! it resolves to one, the WRITING namespace otherwise -- unless it is
  ! a special form, a class name, an auto-gensym, `&`, or host sugar
  ! (.member, Ctor.), which are left as they are. A qualified symbol has
  ! its alias expanded. Unconditional, as Clojure's is: qualifying only
  ! what already resolved meant a macro defined BEFORE the function its
  ! template names (clojure.test's run-test names test-var, defined
  ! later in the file) expanded to a bare symbol that then resolved in
  ! the caller's namespace, or not at all. Now that syntax-quote is
  ! expanded at analysis time that ordering is real, and the only
  ! correct answer is Clojure's.
  function qq_alias(sym, env) result(out)
    type(gc_value), intent(in) :: sym, env
    type(gc_value) :: out, nsv, tgt, var
    character(len=:), allocatable :: t
    integer :: slash, n

    out = sym
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    n = len(t)
    if (n == 0) return
    nsv = gcn_current([sym])

    slash = index(t, "/")
    if (slash > 1 .and. slash < n) then
       tgt = alias_in(nsv, t(1:slash-1), [sym])
       if (gc_kind(tgt) /= OBJ_NS) return
       out = gc_sym(gcn_name(tgt) // "/" // t(slash+1:), [sym])
       return
    end if
    if (t == "&" .or. t == "/") return
    if (t(1:1) == ".") return
    if (t(n:n) == ".") return
    if (n > 8) then
       if (t(n-7:n) == "__auto__") return
    end if
    if (is_special(sym)) return
    if (gc_ref_is(sym%ref, "catch") .or. gc_ref_is(sym%ref, "finally") .or. &
         gc_ref_is(sym%ref, "unquote") .or. gc_ref_is(sym%ref, "splice-unquote")) return
    if (is_class_name(sym)) return
    var = resolve_var(sym, gc_nil())
    if (gcn_is_var(var)) then
       if (gc_kind(gc_slot(var, 3)) == OBJ_NS) then
          out = gc_sym(gcn_name(gc_slot(var, 3)) // "/" // t, [sym])
          return
       end if
    end if
    out = gc_sym(gcn_name(nsv) // "/" // t, [sym])
  end function qq_alias

  ! A map as a vector of k v k v ..., the shape flattenMap produces.
  function flatten_map(m, roots) result(out)
    type(gc_value), intent(in) :: m, roots
    type(gc_value) :: out
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    base = vs_enter(1)
    call gca_entries(m, ks, vls)
    out = gcv_empty([roots])
    call vs_set(base + 1, out)
    do i = 1, size(ks)
       out = gcv_conj(vs_get(base + 1), ks(i), [roots])
       call vs_set(base + 1, out)
       out = gcv_conj(vs_get(base + 1), vls(i), [roots])
       call vs_set(base + 1, out)
    end do
    out = vs_get(base + 1)
    call vs_leave(base)
  end function flatten_map

  function set_elems(st, roots) result(out)
    type(gc_value), intent(in) :: st, roots
    type(gc_value) :: out
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    base = vs_enter(1)
    call gca_entries(gc_slot(st, 1), ks, vls)
    out = gcv_empty([roots])
    call vs_set(base + 1, out)
    do i = 1, size(ks)
       out = gcv_conj(vs_get(base + 1), ks(i), [roots])
       call vs_set(base + 1, out)
    end do
    out = vs_get(base + 1)
    call vs_leave(base)
  end function set_elems

  ! A collection inside syntax-quote: expand its elements as a seq,
  ! then rebuild the collection from them with `ctor`.
  ! Rebuilds a vector, map or set literal from the expanded seq of
  ! its elements.
  !
  ! use_apply matters and is not cosmetic. hash-map takes k v k v as
  ! SEPARATE arguments, so handing it one seq gave (hash-map '(:a 1))
  ! -- which answered {} rather than erroring, so every syntax-quoted
  ! map literal in the tree silently became empty. clojure.test builds
  ! every assertion result that way, which is why 156 tests reported
  ! zero passes. Clojure emits (apply hash-map (seq (concat ...))).
  !
  ! `vec` and `set` both take a collection, so only the map needs it.
  recursive function qq_rebuild(form, ctor, env, use_apply) result(out)
    type(gc_value), intent(in) :: form, env
    character(len=*), intent(in) :: ctor
    logical, intent(in), optional :: use_apply
    type(gc_value) :: out, lst, inner
    logical :: ap
    integer :: base, i

    ap = .false.
    if (present(use_apply)) ap = use_apply

    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    ! The elements as a list, so the existing list path expands them.
    lst = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 3, lst)
    do i = gcv_count(vs_get(base + 1)) - 1, 0, -1
       lst = gcl_cons(gcv_nth(vs_get(base + 1), i), vs_get(base + 3), &
            [vs_get(base + 1), vs_get(base + 3)])
       call vs_set(base + 3, lst)
    end do
    inner = qq_expand(vs_get(base + 3), vs_get(base + 2))
    if (has_error) then
       out = gc_nil()
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, inner)
    out = gcl_empty([vs_get(base + 3)])
    out = gcl_cons(vs_get(base + 3), out, [vs_get(base + 3), out])
    out = gcl_cons(gc_sym(ctor, [vs_get(base + 3), out]), out, [out])
    if (ap) out = gcl_cons(gc_sym("apply", [out]), out, [out])
    call vs_leave(base)
  end function qq_rebuild

  ! Each clause of a multi-arity fn, body expanded, params untouched.




  ! Compiler.macroexpand, then the same walk over the subforms.
  !
  ! It does NOT track local shadowing, which Compiler.isMacro does
  ! through LOCAL_ENV: (let [when 1] (when ...)) expands here where
  ! Clojure would not. Recorded in DEVIATIONS.md.
  ! A DEPTH GUARD around the pass. Clojure has none -- a macro that
  ! expands to itself loops forever there too -- but on a fixed Fortran
  ! stack that is a segfault with no output at all, and a named error is
  ! the difference between a bug report and a mystery.
  ! What Clojure'\''s analyze does to a form before evaluating it, minus
  ! everything except the macroexpansion.
  !
  ! ONCE PER TOP-LEVEL FORM, which is the part that matters. Clojure
  ! macroexpands inside analyze; the Expr tree it leaves behind has no
  ! macros in it, so calling the function again -- or creating a closure
  ! inside it again -- runs code, not macros.
  !
  ! Doing it per closure instead looks equivalent until two definitions
  ! cross, and core.clj writes exactly that crossing:
  !
  !   (defn destructure [bindings] (let [...] (fn pb [...] (let [...] ...))))
  !   (defmacro let [...] `(let* ~(destructure bindings) ...))
  !
  ! destructure is written with the old let; the new let is written with
  ! destructure. Expanding at closure creation meant every CALL to
  ! destructure rebuilt its inner fns, re-expanded their `let`s, and
  ! called destructure again -- until the stack went. Expanding the
  ! top-level form once pins those inner bodies to the `let` that
  ! existed when destructure was defined, which is what compiling them
  ! would have done.
  ! Analysis: a form to a node tree, symbols resolved, macros expanded,
  ! locals as slots. `env` is unused and kept for the callers' sake.
  recursive function gce_analyze(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out
    ev_depth = 0
    out = analyze_top(form)
  end function gce_analyze

  ! No depth limit of its own: Clojure has none, and the runaway
  ! expansions this used to catch were bugs in the walk, not depth --
  ! it treated a metadata wrapper and a lazy seq as leaves, so whole
  ! function bodies escaped analysis and were re-expanded at call time.
  ! Both are fixed. Genuine runaway expansion now surfaces as the
  ! evaluation depth limit, which is where the JVM would report it too.


  subroutine read_trace_macros()
    character(len=8) :: buf
    call get_environment_variable("CLOTRAN_TRACE_MACRO", buf)
    trace_macros = 2
    if (trim(buf) == "1") trace_macros = 1
  end subroutine read_trace_macros

  subroutine read_depth_limit()
    character(len=16) :: buf
    integer :: st, n
    ev_limit = 2200
    call get_environment_variable("CLOTRAN_MAX_DEPTH", buf)
    if (len_trim(buf) > 0) then
       read(buf, *, iostat=st) n
       if (st == 0 .and. n > 0) ev_limit = n
    end if
  end subroutine read_depth_limit

  ! Enough of a form to name it in an error.
  function first_form_name(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    type(gc_value) :: h
    s = "?"
    h = strip_meta(v)
    if (h%tag == GCT_SYM) then
       s = gc_ref_text(h%ref)
       return
    end if
    if (.not. gcl_is(h)) return
    if (gcl_count(h) == 0) return
    h = strip_meta(gcl_first(h))
    if (h%tag == GCT_SYM) s = gc_ref_text(h%ref)
  end function first_form_name



  ! Compiler.macroexpand1 -- ONE step, and no walk into subforms.
  ! core.clj's macroexpand-1 is this and nothing else; macroexpand is
  ! the loop around it, written in Clojure. So the only piece that has
  ! to be native is the single step, and mx_walk -- which expands to a
  ! fixed point AND descends -- is the wrong thing to reuse.
  !
  ! The local environment is empty. Compiler.macroexpand1 reads
  ! LOCAL_ENV, which is bound only while the compiler is analysing a
  ! body, and a call from user code is not inside that.
  recursive function macroexpand_1step(form0) result(out)
    type(gc_value), intent(in) :: form0
    type(gc_value) :: out, form, head, mvar, item
    character(len=:), allocatable :: t
    integer :: base, i, n

    base = vs_enter(3)
    call vs_set(base + 1, form0)
    out = vs_get(base + 1)

    form = strip_meta(vs_get(base + 1))
    if (gc_kind(form) == OBJ_LAZY .or. gc_kind(form) == OBJ_SEQ .or. gc_kind(form) == OBJ_CHUNKSEQ) &
         form = seq_to_list(form, [vs_get(base + 1)])
    call vs_set(base + 2, form)
    if (.not. gcl_is(vs_get(base + 2))) then
       call vs_leave(base); return
    end if
    n = gcl_count(vs_get(base + 2))
    if (n == 0) then
       call vs_leave(base); return
    end if

    head = strip_meta(gcl_first(vs_get(base + 2)))
    if (head%tag /= GCT_SYM) then
       call vs_leave(base); return
    end if

    mvar = macro_var(head, gc_nil())
    if (gcn_is_var(mvar)) then
       out = expand_macro(gcn_var_value(mvar), vs_get(base + 2), gc_nil())
       call vs_leave(base); return
    end if

    ! The two SUGARS macroexpand1 rewrites before it gives up. clotran
    ! evaluates both shapes directly, so this is not how they run -- it
    ! is so that macroexpand-1 REPORTS the rewrite, which is what a
    ! code walker like pprint's is looking at.
    t = gc_ref_text(head%ref)
    if (is_member_sym(head) .and. n >= 2) then
       ! (.foo target args...) -> (. target foo args...)
       out = gcl_empty([vs_get(base + 2)])
       call vs_set(base + 3, out)
       do i = n - 1, 2, -1
          item = nth_of(vs_get(base + 2), i)
          out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
          call vs_set(base + 3, out)
       end do
       item = gc_sym(t(2:), [vs_get(base + 2), vs_get(base + 3)])
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
       call vs_set(base + 3, out)
       item = nth_of(vs_get(base + 2), 1)
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
       call vs_set(base + 3, out)
       item = gc_sym(".", [vs_get(base + 2), vs_get(base + 3)])
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
    else if (is_ctor_sym(head)) then
       ! (Classname. args...) -> (new Classname args...)
       out = gcl_empty([vs_get(base + 2)])
       call vs_set(base + 3, out)
       do i = n - 1, 1, -1
          item = nth_of(vs_get(base + 2), i)
          out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
          call vs_set(base + 3, out)
       end do
       item = gc_sym(t(:len(t) - 1), [vs_get(base + 2), vs_get(base + 3)])
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
       call vs_set(base + 3, out)
       item = gc_sym("new", [vs_get(base + 2), vs_get(base + 3)])
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 2), item])
    end if
    call vs_leave(base)
  end function macroexpand_1step

  ! IPersistentCollection.empty -- what core.clj's `empty` is, in full:
  ! (when (instance? IPersistentCollection coll) (.empty coll)). The
  ! answer keeps the CATEGORY, so a vector empties to [] and a map to
  ! {}; anything that is not a collection answers nil, which is the
  ! `when`'s else branch rather than an error.
  function coll_empty(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, inner
    integer :: base

    out = gc_nil()
    base = vs_enter(2)
    call vs_set(base + 1, v)
    select case (gc_kind(vs_get(base + 1)))
    case (OBJ_VECTOR)
       out = gcv_empty([roots, vs_get(base + 1)])
    case (OBJ_MAP)
       out = gca_empty([roots, vs_get(base + 1)])
    case (OBJ_SET)
       inner = gca_empty([roots, vs_get(base + 1)])
       call vs_set(base + 2, inner)
       out = gc_obj(OBJ_SET, [vs_get(base + 2)], [roots, vs_get(base + 2)])
    case (OBJ_CONS, OBJ_SEQ, OBJ_LAZY, OBJ_CHUNKSEQ)
       ! Every seq empties to (), the way PersistentList.EMPTY is what
       ! ASeq.empty answers.
       out = gcl_empty([roots, vs_get(base + 1)])
    end select
    if (gcl_is(vs_get(base + 1))) out = gcl_empty([roots, vs_get(base + 1)])
    call vs_leave(base)
  end function coll_empty

  ! ---- java.lang.Math ---------------------------------------------
  !
  ! clojure/math.clj is a THIN WRAPPER: every one of its functions is
  ! (Math/foo (double x)) and nothing else, so the whole namespace
  ! lands here. It is vendored and unmodified like the rest, which
  ! makes these the host members it needs.
  !
  ! No libm binding. Fortran's own intrinsics cover the awkward ones
  ! exactly -- nearest() is nextafter, spacing() is ulp, scale() is
  ! scalb, exponent() is ilogb+1, ieee_rem() is IEEEremainder -- so
  ! this stays inside the premise that src/c holds only the regex
  ! shim.


  ! Round half to EVEN, which is what Math.rint does and what neither
  ! anint (half away from zero) nor int truncation gives.
  real(gc_dp) function math_rint(x) result(r)
    real(gc_dp), intent(in) :: x
    real(gc_dp) :: f, lo
    lo = aint(x)
    f = x - lo
    if (abs(f) < 0.5_gc_dp) then
       r = lo
    else if (abs(f) > 0.5_gc_dp) then
       r = lo + sign(1.0_gc_dp, x)
    else
       ! Exactly halfway: take the neighbour that is even.
       if (mod(lo, 2.0_gc_dp) == 0.0_gc_dp) then
          r = lo
       else
          r = lo + sign(1.0_gc_dp, x)
       end if
    end if
  end function math_rint

  ! The *Exact family throws where ordinary arithmetic wraps. Detected
  ! by dividing back out rather than by the wrapped sign, which is
  ! undefined behaviour to rely on.
  ! Decided BEFORE multiplying, by range: signed overflow is undefined
  ! in Fortran as in C, and at -O2 a check that multiplies first and
  ! divides back is folded away -- (multiply-exact Long/MAX_VALUE 2)
  ! stopped throwing the day optimisation was turned on.
  logical function mul_overflows(a, b) result(bad)
    integer(gc_ip), intent(in) :: a, b
    integer(gc_ip), parameter :: big = huge(0_gc_ip), small = -huge(0_gc_ip) - 1_gc_ip
    bad = .false.
    if (a == 0_gc_ip .or. b == 0_gc_ip) return
    if (a > 0_gc_ip .and. b > 0_gc_ip) then
       bad = a > big / b
    else if (a > 0_gc_ip) then
       bad = b < small / a
    else if (b > 0_gc_ip) then
       bad = a < small / b
    else
       bad = (a == small .or. b == small)
       if (.not. bad) bad = (-a) > big / (-b)
    end if
  end function mul_overflows

  ! One Math call. `k` is the Math row's index in hosttable.inc.
  function math_call(k, args, roots) result(out)
    integer, intent(in) :: k
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    real(gc_dp) :: x, y, r
    integer(gc_ip) :: ia, ib, ir
    integer :: n
    type(gc_value) :: a0, a1

    out = gc_nil()
    n = gcv_count(args)

    ! random takes nothing.
    if (k == 36) then
       call random_number(r)
       out = gc_real(r)
       return
    end if

    if (n < 1) then
       call fail("Math: no argument")
       return
    end if
    a0 = strip_meta(gcv_nth(args, 0))
    if (.not. is_number(a0)) then
       call fail("Math: not a number")
       return
    end if
    x = num_dbl(a0)
    ia = 0_gc_ip
    if (a0%tag == GCT_INT) ia = a0%ival
    y = 0.0_gc_dp
    ib = 0_gc_ip
    if (n >= 2) then
       a1 = strip_meta(gcv_nth(args, 1))
       if (.not. is_number(a1)) then
          call fail("Math: not a number")
          return
       end if
       y = num_dbl(a1)
       if (a1%tag == GCT_INT) ib = a1%ival
    end if

    select case (k)
    case (1);  out = gc_real(sin(x))
    case (2);  out = gc_real(cos(x))
    case (3);  out = gc_real(tan(x))
    case (4);  out = gc_real(asin(x))
    case (5);  out = gc_real(acos(x))
    case (6);  out = gc_real(atan(x))
    case (7);  out = gc_real(x * (acos(-1.0_gc_dp) / 180.0_gc_dp))
    case (8);  out = gc_real(x * (180.0_gc_dp / acos(-1.0_gc_dp)))
    case (9);  out = gc_real(exp(x))
    case (10); out = gc_real(log(x))
    case (11); out = gc_real(log10(x))
    case (12); out = gc_real(sqrt(x))
    case (13)
       ! No cbrt intrinsic; the sign has to come back out by hand so
       ! that (cbrt -8.0) is -2.0 rather than NaN.
       if (x == 0.0_gc_dp) then
          out = gc_real(x)
       else
          out = gc_real(sign(abs(x) ** (1.0_gc_dp / 3.0_gc_dp), x))
       end if
    case (14); out = gc_real(ceiling_dbl(x))
    case (15); out = gc_real(floor_dbl(x))
    case (16); out = gc_real(math_rint(x))
    case (17)
       if (x /= x) then
          out = gc_real(x)
       else if (x == 0.0_gc_dp) then
          out = gc_real(x)
       else
          out = gc_real(sign(1.0_gc_dp, x))
       end if
    case (18); out = gc_real(sinh(x))
    case (19); out = gc_real(cosh(x))
    case (20); out = gc_real(tanh(x))
    case (21)
       ! exp(x)-1 loses every significant digit near zero, so the
       ! series takes over where it would.
       if (abs(x) < 1.0e-5_gc_dp) then
          out = gc_real(x * (1.0_gc_dp + x * (0.5_gc_dp + x / 6.0_gc_dp)))
       else
          out = gc_real(exp(x) - 1.0_gc_dp)
       end if
    case (22)
       if (abs(x) < 1.0e-5_gc_dp) then
          out = gc_real(x * (1.0_gc_dp - x * (0.5_gc_dp - x / 3.0_gc_dp)))
       else
          out = gc_real(log(1.0_gc_dp + x))
       end if
    case (23); out = gc_real(spacing(x))
    case (24); out = gc_real(nearest(x, 1.0_gc_dp))
    case (25); out = gc_real(nearest(x, -1.0_gc_dp))
    case (26)
       ! Math.abs is overloaded: a long stays a long.
       if (a0%tag == GCT_INT) then
          out = gc_int(abs(ia))
       else
          out = gc_real(abs(x))
       end if
    case (27)
       ! IEEE remainder: x - y*rint(x/y), which is what ieee_rem is.
       if (y == 0.0_gc_dp) then
          out = gc_real(x / y)
       else
          out = gc_real(x - y * math_rint(x / y))
       end if
    case (28); out = gc_real(atan2(x, y))
    case (29); out = gc_real(x ** y)
    case (30); out = gc_real(hypot(x, y))
    case (31); out = gc_real(sign(abs(x), y))
    case (32)
       if (x == y) then
          out = gc_real(y)
       else
          out = gc_real(nearest(x, y - x))
       end if
    case (33)
       ! Math.round(double) is floor(x + 0.5) and answers a long.
       out = gc_int(int(floor_dbl(x + 0.5_gc_dp), gc_ip))
    case (34)
       ! Java's unbiased exponent has the mantissa in [1,2);
       ! Fortran's has it in [0.5,1).
       out = gc_int(int(exponent(x) - 1, 8))
    case (35); out = gc_real(scale(x, int(y)))
    case (37)
       ! by range, before the add (see mul_overflows)
       if ((ib > 0 .and. ia > huge(ia) - ib) .or. &
            (ib < 0 .and. ia < -huge(ia) - 1_gc_ip - ib)) then
          call fail("integer overflow")
       else
          out = gc_int(ia + ib)
       end if
    case (38)
       if ((ib < 0 .and. ia > huge(ia) + ib) .or. &
            (ib > 0 .and. ia < -huge(ia) - 1_gc_ip + ib)) then
          call fail("integer overflow")
       else
          out = gc_int(ia - ib)
       end if
    case (39)
       if (mul_overflows(ia, ib)) then
          call fail("integer overflow")
       else
          out = gc_int(ia * ib)
       end if
    case (40)
       if (ia == huge(ia)) then
          call fail("integer overflow")
       else
          out = gc_int(ia + 1_gc_ip)
       end if
    case (41)
       if (ia == -huge(ia) - 1_gc_ip) then
          call fail("integer overflow")
       else
          out = gc_int(ia - 1_gc_ip)
       end if
    case (42)
       if (ia == -huge(ia) - 1_gc_ip) then
          call fail("integer overflow")
       else
          out = gc_int(-ia)
       end if
    case (43)
       ! Floor division, not truncation: (floorDiv -7 2) is -4.
       if (ib == 0_gc_ip) then
          call fail("Divide by zero")
       else
          out = gc_int(int(floor(real(ia, gc_dp) / real(ib, gc_dp)), gc_ip))
       end if
    case (44)
       if (ib == 0_gc_ip) then
          call fail("Divide by zero")
       else
          out = gc_int(modulo(ia, ib))
       end if
    case (45)
       out = gc_int(ia)
    case default
       call fail("Math: no such member")
    end select
  end function math_call

  ! Whether a double is NEGATIVE zero. (x < 0.0) is false for it
  ! and (x == 0.0) is true, so the sign bit is the only witness;
  ! ieee_copy_sign carries it onto a value that can be compared.
  logical function is_neg_zero(x)
    real(gc_dp), intent(in) :: x
    is_neg_zero = (x == 0.0_gc_dp .and. &
         ieee_copy_sign(1.0_gc_dp, x) < 0.0_gc_dp)
  end function is_neg_zero

  ! ---- String.format ----------------------------------------------
  !
  ! core.clj's `format` is (String/format fmt (to-array args)) and
  ! nothing more, so this is the whole of it. A SUBSET of
  ! java.util.Formatter: the conversions that appear in Clojure's own
  ! source and suite -- s S d x X o f e E g b B c n %% -- with the
  ! '-', '0' and '+' flags, a width and a precision. Argument-index
  ! syntax (%1$s) is not here; nothing in the tree writes it.
  !
  ! An unknown conversion is an ERROR rather than a passthrough: a
  ! format string that silently keeps its own text is the kind of
  ! plausible wrong answer that survives for a long time.
  function java_format(fmt, argv) result(s)
    character(len=*), intent(in) :: fmt
    type(gc_value), intent(in) :: argv
    character(len=:), allocatable :: s, flags, conv, piece
    integer :: i, w, prec, ai, nargs
    logical :: has_w, has_prec
    type(gc_value) :: a

    s = ""
    i = 1
    ai = 0
    nargs = gcv_count(argv)
    do while (i <= len(fmt))
       if (fmt(i:i) /= "%") then
          s = s // fmt(i:i)
          i = i + 1
          cycle
       end if
       i = i + 1
       if (i > len(fmt)) then
          call fail("format: trailing %")
          return
       end if
       flags = ""
       do while (i <= len(fmt))
          if (index("-+ 0,#", fmt(i:i)) == 0) exit
          flags = flags // fmt(i:i)
          i = i + 1
       end do
       w = 0
       has_w = .false.
       do while (i <= len(fmt))
          if (fmt(i:i) < "0" .or. fmt(i:i) > "9") exit
          w = w * 10 + (iachar(fmt(i:i)) - iachar("0"))
          has_w = .true.
          i = i + 1
       end do
       prec = 0
       has_prec = .false.
       if (i <= len(fmt)) then
          if (fmt(i:i) == ".") then
             i = i + 1
             has_prec = .true.
             do while (i <= len(fmt))
                if (fmt(i:i) < "0" .or. fmt(i:i) > "9") exit
                prec = prec * 10 + (iachar(fmt(i:i)) - iachar("0"))
                i = i + 1
             end do
          end if
       end if
       if (i > len(fmt)) then
          call fail("format: unterminated conversion")
          return
       end if
       conv = fmt(i:i)
       i = i + 1

       if (conv == "%") then
          s = s // "%"
          cycle
       end if
       if (conv == "n") then
          s = s // achar(10)
          cycle
       end if
       if (ai >= nargs) then
          call fail("format: not enough arguments")
          return
       end if
       a = gcv_nth(argv, ai)
       ai = ai + 1
       piece = format_one(conv, a, prec, has_prec)
       if (has_error) return
       s = s // pad(piece, w, has_w, index(flags, "-") > 0, &
            index(flags, "0") > 0)
    end do
  end function java_format

  ! Pattern.split -- what clojure.string/split is, and the one regex
  ! operation the matcher API cannot already express: it walks the
  ! subject finding matches and returns the text BETWEEN them.
  !
  ! Java's limit rule, which is not obvious: a positive limit caps the
  ! number of parts and the last part keeps the rest of the string
  ! unsplit; zero or absent means no cap AND trailing empty parts are
  ! dropped; a negative limit means no cap and keep them.
  function regex_split(pat, subj, limit, roots) result(out)
    type(gc_value), intent(in) :: pat, subj
    integer, intent(in) :: limit
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, piece
    character(len=:), allocatable :: s
    integer :: mh, base, from, gs, ge, nparts, last
    logical :: ok

    out = gc_nil()
    s = text_of(subj)
    mh = regex_clone(gc_i1(pat))
    if (mh == 0) then
       call fail("regex: " // regex_last_error())
       return
    end if
    if (.not. regex_set_text(mh, s)) then
       call fail("regex: " // regex_last_error())
       call regex_release(mh)
       return
    end if

    base = vs_enter(2)
    out = gcv_empty(roots)
    call vs_set(base + 1, out)
    from = 0
    nparts = 0
    do
       if (limit > 0 .and. nparts == limit - 1) exit
       if (regex_find_next(mh) /= 1) exit
       ok = regex_group_span(mh, 0, gs, ge)
       if (.not. ok) exit
       ! A zero-width match at the position we are already at would
       ! loop forever and produce nothing; Java skips it too.
       if (ge == gs .and. gs == from .and. from == 0) cycle
       piece = gc_str(s(from+1:gs), [roots, vs_get(base + 1)])
       call vs_set(base + 2, piece)
       out = gcv_conj(vs_get(base + 1), vs_get(base + 2), &
            [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 1, out)
       nparts = nparts + 1
       from = ge
       if (ge == gs) from = ge
    end do
    call regex_release(mh)

    piece = gc_str(s(from+1:), [roots, vs_get(base + 1)])
    call vs_set(base + 2, piece)
    out = gcv_conj(vs_get(base + 1), vs_get(base + 2), &
         [roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 1, out)

    if (limit == 0) then
       ! Drop trailing empties.
       last = gcv_count(vs_get(base + 1))
       do while (last > 0)
          if (len(text_of(gcv_nth(vs_get(base + 1), last - 1))) > 0) exit
          last = last - 1
       end do
       out = gcv_empty([roots, vs_get(base + 1)])
       call vs_set(base + 2, out)
       do nparts = 0, last - 1
          out = gcv_conj(vs_get(base + 2), gcv_nth(vs_get(base + 1), nparts), &
               [roots, vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 2, out)
       end do
       out = vs_get(base + 2)
    else
       out = vs_get(base + 1)
    end if
    call vs_leave(base)
  end function regex_split

  ! A `value` array holding the elements of a collection, which is what
  ! into-array is: (RT/seqToTypedArray (seq aseq)), optionally with a
  ! component type first. There are no primitive component types here
  ! -- every array of objects is a `value` array -- so the type is read
  ! and discarded, which is DEVIATIONS.md 24's territory rather than a
  ! new one.
  function value_array(items, roots) result(out)
    type(gc_value), intent(in) :: items
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, vec, run
    character(len=:), allocatable :: err
    integer :: base, h, k, cnt

    out = gc_nil()
    base = vs_enter(3)
    vec = coll_to_vector(items, roots)
    call vs_set(base + 1, vec)
    cnt = gcv_count(vs_get(base + 1))
    h = gcna_new("value", [cnt], [0], err)
    if (h == 0) then
       call fail(err)
       call vs_leave(base)
       return
    end if
    run = gc_vec(max(1, cnt), [roots, vs_get(base + 1)])
    call vs_set(base + 2, run)
    out = gc_obj(OBJ_ARRAY, [vs_get(base + 2)], [roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    call gc_set_i1(vs_get(base + 3), h)
    call gc_set_i2(vs_get(base + 3), -1) ! owns the handle
    do k = 0, cnt - 1
       call gc_vec_set(gc_slot(vs_get(base + 3), 1), k + 1, &
            gcv_nth(vs_get(base + 1), k))
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function value_array

  ! Matcher.quoteReplacement: \ and $ are the only two characters a
  ! replacement string treats specially, so escaping those makes it
  ! literal.
  function quote_replacement(t) result(s)
    character(len=*), intent(in) :: t
    character(len=:), allocatable :: s
    integer :: i
    s = ""
    do i = 1, len(t)
       if (t(i:i) == achar(92) .or. t(i:i) == "$") s = s // achar(92)
       s = s // t(i:i)
    end do
  end function quote_replacement

  ! Matcher's replacement half: appendReplacement, appendTail,
  ! replaceAll and replaceFirst. clojure.string/replace is written
  ! entirely in terms of these, so `replace` and `replace-first` do not
  ! work without them however good the matching is.
  !
  ! The APPEND POSITION lives in the Matcher's i2 -- where the last
  ! appendReplacement left off, which is what makes a sequence of them
  ! stitch a string together. i1 is the ICU handle; i2 was free.

  ! $1..$9 name groups; a backslash escapes the next character. This is
  ! the one place a replacement string is not literal, which is why
  ! Matcher/quoteReplacement exists at all.
  function expand_replacement(repl, mh, subj) result(s)
    character(len=*), intent(in) :: repl, subj
    integer, intent(in) :: mh
    character(len=:), allocatable :: s
    integer :: i, gnum, gs, ge

    s = ""
    i = 1
    do while (i <= len(repl))
       if (repl(i:i) == achar(92) .and. i < len(repl)) then
          s = s // repl(i+1:i+1)
          i = i + 2
       else if (repl(i:i) == "$" .and. i < len(repl) .and. &
            repl(min(i+1, len(repl)):min(i+1, len(repl))) >= "0" .and. &
            repl(min(i+1, len(repl)):min(i+1, len(repl))) <= "9") then
          gnum = iachar(repl(i+1:i+1)) - iachar("0")
          if (regex_group_span(mh, gnum, gs, ge)) s = s // subj(gs+1:ge)
          i = i + 2
       else
          s = s // repl(i:i)
          i = i + 1
       end if
    end do
  end function expand_replacement

  ! Every match replaced, or just the first. Same walk either way.
  function regex_replace(mv, repl, only_first, roots) result(out)
    type(gc_value), intent(in) :: mv
    character(len=*), intent(in) :: repl
    logical, intent(in) :: only_first
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    character(len=:), allocatable :: subj, acc
    integer :: mh, from, gs, ge

    subj = text_of(gc_slot(mv, 2))
    mh = gc_i1(mv)
    acc = ""
    from = 0
    do
       if (regex_find_next(mh) /= 1) exit
       if (.not. regex_group_span(mh, 0, gs, ge)) exit
       acc = acc // subj(from+1:gs) // expand_replacement(repl, mh, subj)
       from = ge
       if (only_first) exit
       ! A zero-width match cannot advance on its own.
       if (ge == gs) then
          if (ge >= len(subj)) exit
          acc = acc // subj(ge+1:ge+1)
          from = ge + 1
       end if
    end do
    out = gc_str(acc // subj(from+1:), roots)
  end function regex_replace

  ! One conversion, before padding.
  function format_one(conv, a0, prec, has_prec) result(p)
    character(len=*), intent(in) :: conv
    type(gc_value), intent(in) :: a0
    integer, intent(in) :: prec
    logical, intent(in) :: has_prec
    character(len=:), allocatable :: p
    character(len=64) :: buf
    type(gc_value) :: a

    a = strip_meta(a0)
    p = ""
    select case (conv)
    case ("s")
       ! String.valueOf(null) is "null", not "nil" -- Formatter
       ! never sees Clojure's printer for a bare nil argument.
       if (a%tag == GCT_NIL) then
          p = "null"
       else
          p = gcp_str(a, .false.)
       end if
       if (has_prec) then
          if (prec < len(p)) p = p(1:prec)
       end if
    case ("S")
       if (a%tag == GCT_NIL) then
          p = "null"
       else
          p = gcp_str(a, .false.)
       end if
       call upcase_in_place(p)
    case ("b", "B")
       ! Java's %b is false for nil and false, true for EVERYTHING
       ! else -- including 0 and "".
       if (truthy(a)) then
          p = "true"
       else
          p = "false"
       end if
       if (conv == "B") call upcase_in_place(p)
    case ("c")
       if (a%tag == GCT_CHAR) then
          p = achar(int(a%ival, kind=4))
       else if (a%tag == GCT_INT) then
          p = achar(int(a%ival, kind=4))
       else
          call fail("format: %c wants a character")
       end if
    case ("d")
       if (a%tag /= GCT_INT) then
          call fail("format: %d wants an integer")
          return
       end if
       write(buf, '(I0)') a%ival
       p = trim(buf)
    case ("x", "X", "o")
       if (a%tag /= GCT_INT) then
          call fail("format: " // conv // " wants an integer")
          return
       end if
       if (conv == "o") then
          write(buf, '(O0)') a%ival
       else
          write(buf, '(Z0)') a%ival
       end if
       p = trim(buf)
       if (conv == "x") call downcase_in_place(p)
    case ("f", "e", "E", "g")
       if (.not. is_number(a)) then
          call fail("format: " // conv // " wants a number")
          return
       end if
       block
         integer :: dp
         character(len=16) :: spec
         dp = 6
         if (has_prec) dp = prec
         select case (conv)
         case ("f"); write(spec, '(A,I0,A)') "(F0.", dp, ")"
         case ("g"); write(spec, '(A,I0,A)') "(G0.", dp, ")"
         case default; write(spec, '(A,I0,A,I0,A)') "(ES", dp + 8, ".", dp, "E2)"
         end select
         write(buf, spec) num_dbl(a)
         p = trim(adjustl(buf))
         ! Fortran writes .5 where Java writes 0.5.
         if (len(p) > 0) then
            if (p(1:1) == ".") p = "0" // p
            if (len(p) > 1) then
               if (p(1:2) == "-.") p = "-0" // p(2:)
            end if
         end if
         if (conv == "e") call downcase_in_place(p)
       end block
    case default
       call fail("format: no conversion %" // conv)
    end select
  end function format_one

  ! Width padding. '-' left-justifies, '0' pads a number on the left
  ! with zeros; neither ever TRUNCATES, which is Formatter's rule.
  function pad(p0, w, has_w, left, zero) result(p)
    character(len=*), intent(in) :: p0
    integer, intent(in) :: w
    logical, intent(in) :: has_w, left, zero
    character(len=:), allocatable :: p
    integer :: k

    p = p0
    if (.not. has_w) return
    k = w - len(p)
    if (k <= 0) return
    if (left) then
       p = p // repeat(" ", k)
    else if (zero) then
       if (len(p) > 0) then
          if (p(1:1) == "-") then
             p = "-" // repeat("0", k) // p(2:)
             return
          end if
       end if
       p = repeat("0", k) // p
    else
       p = repeat(" ", k) // p
    end if
  end function pad

  subroutine upcase_in_place(s)
    character(len=:), allocatable, intent(inout) :: s
    integer :: j
    do j = 1, len(s)
       if (s(j:j) >= "a" .and. s(j:j) <= "z") &
            s(j:j) = achar(iachar(s(j:j)) - 32)
    end do
  end subroutine upcase_in_place

  subroutine downcase_in_place(s)
    character(len=:), allocatable, intent(inout) :: s
    integer :: j
    do j = 1, len(s)
       if (s(j:j) >= "A" .and. s(j:j) <= "Z") &
            s(j:j) = achar(iachar(s(j:j)) + 32)
    end do
  end subroutine downcase_in_place

  ! ceiling/floor as DOUBLES. The intrinsics answer integers, which
  ! would cap a big double at huge(int) and lose the infinities.
  real(gc_dp) function ceiling_dbl(x) result(r)
    real(gc_dp), intent(in) :: x
    r = aint(x)
    if (r < x) r = r + 1.0_gc_dp
  end function ceiling_dbl

  real(gc_dp) function floor_dbl(x) result(r)
    real(gc_dp), intent(in) :: x
    r = aint(x)
    if (r > x) r = r - 1.0_gc_dp
  end function floor_dbl

  ! [old new], the vector swap-vals! and reset-vals! answer.
  function value_pair(a0, b0, roots) result(out)
    type(gc_value), intent(in) :: a0, b0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base

    base = vs_enter(3)
    call vs_set(base + 1, a0)
    call vs_set(base + 2, b0)
    out = gcv_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    out = gcv_conj(vs_get(base + 3), vs_get(base + 1), &
         [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 3, out)
    out = gcv_conj(vs_get(base + 3), vs_get(base + 2), &
         [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_leave(base)
  end function value_pair

  ! Compiler.specials -- the map special-symbol? asks. Its VALUES are
  ! parser objects on the JVM and nothing reads them through this Var,
  ! so nil will do; the KEYS are the answer.
  !
  ! Clojure's list, not is_special's. The two differ: clotran has
  ! quasiquote, defmacro* and lazy-seq* as special forms where Clojure
  ! reaches them another way (DEVIATIONS.md 6), and answering true for
  ! those would make special-symbol? report on our host rather than on
  ! the language.
  function specials_map(roots) result(out)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, k
    integer :: base, i
    character(len=24), parameter :: names(24) = [character(len=24) :: &
         "def", "loop*", "recur", "if", "case*", "let*", "letfn*", "do", &
         "fn*", "quote", "var", "clojure.core/import*", ".", "set!", &
         "deftype*", "reify*", "try", "throw", "monitor-enter", &
         "monitor-exit", "catch", "finally", "new", "&"]

    base = vs_enter(1)
    out = gca_empty([roots])
    call vs_set(base + 1, out)
    do i = 1, size(names)
       k = gc_sym(trim(names(i)), [roots, vs_get(base + 1)])
       out = gca_assoc(vs_get(base + 1), k, gc_nil(), [roots, vs_get(base + 1), k])
       call vs_set(base + 1, out)
    end do
    out = vs_get(base + 1)
    call vs_leave(base)
  end function specials_map

  ! One cell of (iterate f x): a realised head and an unrealised
  ! tail. The tail'"s thunk is an ordinary closure over a frame
  ! binding f and x, whose body is the form
  ! (clojure.lang.Iterate/create __f (__f __x)) -- so the next cell
  ! is built by the evaluator, the same way a lazy-seq body is,
  ! rather than by anything special-cased in the collector.
  ! (range start end step) as a LAZY cell: realised head, unrealised
  ! tail, exactly the shape iterate_cell builds.
  !
  ! It used to realise the whole range into a vector, which is fine
  ! right up until someone writes (take 100 (range 100000000)) -- which
  ! clojure.test-clojure.for does, copied straight out of for's own
  ! docstring, and which hung the entire test suite. Laziness here is
  ! not an optimisation, it is the difference between terminating and
  ! not, and everything downstream (take, map, drop) was only eager
  ! because range handed it a realised vector to be eager about.
  !
  ! A zero step is deliberately not special-cased: neither guard fires,
  ! so it yields its start forever, which is what Clojure does.
  ! lo, hi and stp are VALUES, not Fortran integers. Clojure has
  ! two range classes -- LongRange and Range -- and core.clj picks
  ! between them on (int? x); reading %ival regardless meant
  ! (range 0.0 360.0 5.0) read every bound as 0 and yielded zeros
  ! forever. Carrying the values through means the arithmetic
  ! decides the type, so a double range counts in doubles and a
  ! ratio step stays exact.
  ! One cell of (range lo hi step): head lo, and a NATIVE pending tail
  ! (OBJ_LAZY, i2 = 1) holding [lo+step hi step], which gce_force turns
  ! into the next cell. No closure, no environment, no form.
  ! --- chunks --------------------------------------------------------
  !
  ! core.clj's map, filter, keep, for and doseq process a chunked seq
  ! 32 elements at a time through a chunk buffer, and reduce over one
  ! reduces each chunk with the host's loop. That is where the JVM's
  ! seq speed comes from, and the code is core.clj's; what it needs
  ! from the host is IChunk, ChunkBuffer, ChunkedCons and chunkedFirst/
  ! chunkedMore on the seqs that are chunked: a vector's seq and a
  ! range, exactly as on the JVM.
  !
  ! A chunk (OBJ_CHUNK) is a window [i1, i2) onto a backing: a raw run
  ! (from a chunk buffer or a materialised range) or a vector (a
  ! vector's seq chunks in place, no copy).

  function make_chunk(backing, off, fin, roots) result(c)
    type(gc_value), intent(in) :: backing
    integer, intent(in) :: off, fin
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: c
    c = gc_obj(OBJ_CHUNK, [backing], [roots, backing])
    call gc_set_i1(c, off)
    call gc_set_i2(c, fin)
  end function make_chunk

  integer function chunk_count(c)
    type(gc_value), intent(in) :: c
    chunk_count = max(0, gc_i2(c) - gc_i1(c))
  end function chunk_count

  function chunk_nth(c, i) result(x)
    type(gc_value), intent(in) :: c
    integer, intent(in) :: i
    type(gc_value) :: x, b
    x = gc_nil()
    if (i < 0 .or. i >= chunk_count(c)) return
    b = gc_slot(c, 1)
    if (b%tag == GCT_VEC) then
       x = gc_vec_get(b, gc_i1(c) + i + 1)
    else
       x = gcv_nth(b, gc_i1(c) + i)
    end if
  end function chunk_nth

  ! Whether `v` is a seq that hands out chunks: a ChunkedCons, a
  ! vector's seq view, a realised range cell.
  logical function is_chunked_seq(v)
    type(gc_value), intent(in) :: v
    is_chunked_seq = .false.
    select case (gc_kind(v))
    case (OBJ_CHUNKSEQ)
       is_chunked_seq = .true.
    case (OBJ_SEQ)
       is_chunked_seq = gcv_is(gc_slot(v, 1))
    case (OBJ_LAZY)
       is_chunked_seq = (gc_i2(v) == 1 .and. gc_i1(v) == LAZY_CONS)
    end select
  end function is_chunked_seq

  ! IChunkedSeq.chunkedFirst and chunkedMore of a chunked seq, both at
  ! once since a range decides them together. `more` is nil when
  ! nothing follows.
  recursive subroutine chunked_parts(s0, chunk, more, roots)
    type(gc_value), intent(in) :: s0
    type(gc_value), intent(out) :: chunk, more
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: s, src, cell, nxt, spec, buf
    integer :: base, at, total, fin, cnt
    real(gc_dp) :: sd

    chunk = gc_nil()
    more = gc_nil()
    s = strip_meta(s0)
    base = vs_enter(6)
    call vs_set(base + 1, s)
    select case (gc_kind(s))
    case (OBJ_CHUNKSEQ)
       chunk = gc_slot(s, 1)
       more = gc_slot(s, 2)
    case (OBJ_SEQ)
       src = gc_slot(s, 1)
       at = gc_i1(s)
       total = gcv_count(src)
       fin = min(total, at + 32)
       chunk = make_chunk(src, at, fin, [roots, vs_get(base + 1)])
       call vs_set(base + 2, chunk)
       if (fin < total) then
          more = gc_obj(OBJ_SEQ, [src], [roots, vs_get(base + 1), vs_get(base + 2)])
          call gc_set_i1(more, fin)
       end if
       chunk = vs_get(base + 2)
    case (OBJ_LAZY)
       ! up to 32 values into one run: realised cells first, then the
       ! pending tail's arithmetic, then whatever is left is `more`
       buf = gc_vec(32, [roots, vs_get(base + 1)])
       call vs_set(base + 2, buf)
       cnt = 0
       call vs_set(base + 3, vs_get(base + 1))      ! the cell being read
       do
          cell = vs_get(base + 3)
          if (gc_kind(cell) /= OBJ_LAZY) exit
          if (gc_i1(cell) == LAZY_CONS) then
             if (cnt >= 32) exit
             call gc_vec_set(vs_get(base + 2), cnt + 1, gc_slot(cell, 2))
             cnt = cnt + 1
             call vs_set(base + 3, gc_slot(cell, 3))
             cycle
          end if
          if (gc_i1(cell) == LAZY_PENDING .and. gc_i2(cell) == 1) then
             spec = gc_slot(cell, 1)
             call vs_set(base + 4, gcv_nth(spec, 0))   ! cursor
             call vs_set(base + 5, gcv_nth(spec, 1))   ! hi
             call vs_set(base + 6, gcv_nth(spec, 2))   ! step
             sd = num_dbl(vs_get(base + 6))
             do while (cnt < 32)
                if (sd > 0.0_gc_dp .and. .not. num_lt(vs_get(base + 4), vs_get(base + 5))) exit
                if (sd < 0.0_gc_dp .and. .not. num_lt(vs_get(base + 5), vs_get(base + 4))) exit
                call gc_vec_set(vs_get(base + 2), cnt + 1, vs_get(base + 4))
                cnt = cnt + 1
                call vs_set(base + 4, num_add2(vs_get(base + 4), vs_get(base + 6), [vs_get(base + 2)]))
             end do
             ! what is left of the range, as a fresh pending tail
             if ((sd > 0.0_gc_dp .and. num_lt(vs_get(base + 4), vs_get(base + 5))) .or. &
                  (sd < 0.0_gc_dp .and. num_lt(vs_get(base + 5), vs_get(base + 4))) .or. sd == 0.0_gc_dp) then
                spec = gcv_build(3, [vs_get(base + 2)])
                call vs_set(base + 3, spec)
                call gc_vec_set(gc_slot(spec, 1), 1, vs_get(base + 4))
                call gc_vec_set(gc_slot(spec, 1), 2, vs_get(base + 5))
                call gc_vec_set(gc_slot(spec, 1), 3, vs_get(base + 6))
                nxt = gc_obj(OBJ_LAZY, [vs_get(base + 3), gc_nil(), gc_nil()], [vs_get(base + 2), vs_get(base + 3)])
                call gc_set_i1(nxt, LAZY_PENDING)
                call gc_set_i2(nxt, 1)
                call vs_set(base + 3, nxt)
             else
                call vs_set(base + 3, gc_nil())
             end if
          end if
          exit
       end do
       chunk = make_chunk(vs_get(base + 2), 0, cnt, [vs_get(base + 3)])
       more = vs_get(base + 3)
       if (gc_kind(more) == OBJ_LAZY) then
          if (gc_i1(more) == LAZY_EMPTY) more = gc_nil()
       end if
    end select
    call vs_leave(base)
  end subroutine chunked_parts

  ! Whether every cell of a seq is already realised, so that folding it
  ! reads the whole sequence rather than a prefix. gc_hash may not force
  ! -- it runs inside a map insert and has no roots to hand an allocation
  ! -- so a seq that is not realised keeps identity hashing instead.
  recursive logical function seq_realised_p(v) result(yes)
    type(gc_value), intent(in) :: v
    type(gc_value) :: cur
    yes = .true.
    cur = v
    do
       select case (gc_kind(cur))
       case (OBJ_CHUNKSEQ)
          cur = gc_slot(cur, 2)
       case (OBJ_LAZY)
          select case (gc_i1(cur))
          case (LAZY_EMPTY)
             return
          case (LAZY_DELEG)
             cur = gc_slot(cur, 2)
          case (LAZY_CONS)
             cur = gc_slot(cur, 3)
          case default
             yes = .false.
             return
          end select
       case default
          return
       end select
       if (cur%tag == GCT_NIL) return
    end do
  end function seq_realised_p

  ! The unmixed fold of a seq's elements into h, for the hash of a
  ! ChunkedCons: it must equal a list's. No allocation. An unrealised
  ! tail stops the fold, as an unrealised lazy seq is not hashable here.
  recursive subroutine fold_seq(v, h)
    type(gc_value), intent(in) :: v
    integer, intent(inout) :: h
    type(gc_value) :: cur
    integer :: i
    cur = v
    do
       select case (gc_kind(cur))
       case (OBJ_CHUNKSEQ)
          do i = 0, chunk_count(gc_slot(cur, 1)) - 1
             h = 31 * h + gc_hash(chunk_nth(gc_slot(cur, 1), i))
          end do
          cur = gc_slot(cur, 2)
       case (OBJ_CONS)
          do while (gcl_is(cur) .and. gcl_count(cur) > 0)
             h = 31 * h + gc_hash(gc_slot(cur, 1))
             cur = gc_slot(cur, 2)
          end do
          return
       case (OBJ_SEQ)
          do i = gc_i1(cur), seq_len(gc_slot(cur, 1)) - 1
             h = 31 * h + gc_hash(seq_elem(gc_slot(cur, 1), i, [cur]))
          end do
          return
       case (OBJ_LAZY)
          if (gc_i1(cur) == LAZY_DELEG) then
             cur = gc_slot(cur, 2)
             cycle
          end if
          if (gc_i1(cur) /= LAZY_CONS) return
          h = 31 * h + gc_hash(gc_slot(cur, 2))
          cur = gc_slot(cur, 3)
       case default
          return
       end select
    end do
  end subroutine fold_seq

  recursive function reduce_native(coll, f, has_init, init) result(out)
    type(gc_value), intent(in) :: coll, f, init
    logical, intent(in) :: has_init
    type(gc_value) :: out, x, cell, spec
    integer :: base, i
    logical :: have, done
    real(gc_dp) :: sd
    ! slots: 1 coll/cell 2 f 3 acc 4 cursor (a range's next value) 5 hi 6 step
    base = vs_enter(6)
    call vs_set(base + 1, coll)
    call vs_set(base + 2, f)
    have = has_init
    if (has_init) call vs_set(base + 3, init)
    done = .false.
    select case (gc_kind(coll))
    case (OBJ_VECTOR)
       do i = 0, gcv_count(vs_get(base + 1)) - 1
          call step(gcv_nth(vs_get(base + 1), i))
          if (done) exit
       end do
    case (OBJ_CONS)
       do while (gcl_count(vs_get(base + 1)) > 0)
          call step(gcl_first(vs_get(base + 1)))
          if (done) exit
          call vs_set(base + 1, gcl_rest(vs_get(base + 1), [vs_get(base + 3)]))
       end do
    case (OBJ_LAZY)
       do
          cell = vs_get(base + 1)
          if (gc_i1(cell) == LAZY_PENDING .and. gc_i2(cell) == 1) then
             ! the rest of a range: walk the arithmetic, no cells
             spec = gc_slot(cell, 1)
             call vs_set(base + 4, gcv_nth(spec, 0))
             call vs_set(base + 5, gcv_nth(spec, 1))
             call vs_set(base + 6, gcv_nth(spec, 2))
             sd = num_dbl(vs_get(base + 6))
             do
                if (sd > 0.0_gc_dp .and. .not. num_lt(vs_get(base + 4), vs_get(base + 5))) exit
                if (sd < 0.0_gc_dp .and. .not. num_lt(vs_get(base + 5), vs_get(base + 4))) exit
                if (sd == 0.0_gc_dp .and. .not. num_lt(vs_get(base + 4), vs_get(base + 5))) exit
                call step(vs_get(base + 4))
                if (done) exit
                call vs_set(base + 4, num_add2(vs_get(base + 4), vs_get(base + 6), [vs_get(base + 3)]))
             end do
             exit
          end if
          call gce_force(cell)
          if (has_error) exit
          cell = vs_get(base + 1)
          if (gc_i1(cell) /= LAZY_CONS) exit
          call step(gc_slot(cell, 2))
          if (done) exit
          call vs_set(base + 1, gc_slot(vs_get(base + 1), 3))
       end do
    case (OBJ_CHUNK)
       do i = 0, chunk_count(vs_get(base + 1)) - 1
          call step(chunk_nth(vs_get(base + 1), i))
          if (done) exit
       end do
    case default
       ! a ChunkedCons, or anything else seqable: walked as a seq
       call vs_set(base + 1, to_seq(vs_get(base + 1), [vs_get(base + 2)]))
       do
          cell = vs_get(base + 1)
          if (cell%tag == GCT_NIL) exit
          call step(sq_first(vs_get(base + 1), [vs_get(base + 2)]))
          if (done) exit
          call vs_set(base + 1, to_seq(sq_rest(vs_get(base + 1), [vs_get(base + 2)]), [vs_get(base + 2)]))
       end do
    end select
    if (.not. has_error .and. .not. done) then
       if (have) then
          out = vs_get(base + 3)
       else
          out = apply(vs_get(base + 2), gcv_empty([vs_get(base + 2)]))
       end if
    else if (done) then
       out = vs_get(base + 3)
    else
       out = gc_nil()
    end if
    call vs_leave(base)
  contains
    ! One element: the first is the accumulator when there was no init;
    ! otherwise (f acc x), and a reduced result unwraps and stops.
    subroutine step(x0)
      type(gc_value), intent(in) :: x0
      type(gc_value) :: argv, r
      if (.not. have) then
         call vs_set(base + 3, x0)
         have = .true.
         return
      end if
      x = x0
      argv = gcv_build(2, [vs_get(base + 3), x])
      call gc_vec_set(gc_slot(argv, 1), 1, vs_get(base + 3))
      call gc_vec_set(gc_slot(argv, 1), 2, x)
      r = apply(vs_get(base + 2), argv)
      if (has_error) then
         done = .true.
         return
      end if
      call vs_set(base + 3, r)
      if (gca_contains(strip_meta(r), gc_key("clotran/reduced", [vs_get(base + 3)]))) then
         call vs_set(base + 3, gca_get(strip_meta(vs_get(base + 3)), gc_key("clotran/reduced", [vs_get(base + 3)])))
         done = .true.
      end if
    end subroutine step
  end function reduce_native

  recursive function range_cell(lo, hi, stp, roots) result(out)
    type(gc_value), intent(in) :: lo, hi, stp
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, spec, tail, nxt
    integer :: base
    real(gc_dp) :: sd

    out = gcl_empty(roots)
    sd = num_dbl(stp)
    if (sd > 0.0_gc_dp .and. .not. num_lt(lo, hi)) return
    if (sd < 0.0_gc_dp .and. .not. num_lt(hi, lo)) return

    base = vs_enter(4)
    call vs_set(base + 1, lo)
    call vs_set(base + 2, hi)
    call vs_set(base + 3, stp)
    nxt = num_add2(vs_get(base + 1), vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 4, nxt)
    spec = gcv_empty([roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), vs_get(base + 4)])
    spec = gcv_conj(spec, vs_get(base + 4), [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), spec])
    spec = gcv_conj(spec, vs_get(base + 2), [roots, vs_get(base + 1), vs_get(base + 3), spec])
    spec = gcv_conj(spec, vs_get(base + 3), [roots, vs_get(base + 1), spec])
    call vs_set(base + 4, spec)
    tail = gc_obj(OBJ_LAZY, [vs_get(base + 4), gc_nil(), gc_nil()], [roots, vs_get(base + 1), vs_get(base + 4)])
    call gc_set_i1(tail, LAZY_PENDING)
    call gc_set_i2(tail, 1)
    call vs_set(base + 4, tail)
    out = gc_obj(OBJ_LAZY, [gc_nil(), vs_get(base + 1), vs_get(base + 4)], [roots, vs_get(base + 1), vs_get(base + 4)])
    call gc_set_i1(out, LAZY_CONS)
    ! i2 = 1 on the realised cell as well: it says "this is a range", which
    ! is what makes it a LongRange to `class` and an IReduceInit to reduce.
    call gc_set_i2(out, 1)
    call vs_leave(base)
  end function range_cell

  ! a + b with Clojure's contagion: double beats ratio beats
  ! integer. `range` is the only caller; everything else adds
  ! through B_ADD.
  function num_add2(a, b, roots) result(out)
    type(gc_value), intent(in) :: a, b
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out

    if (a%tag == GCT_REAL .or. b%tag == GCT_REAL) then
       out = gc_real(num_dbl(a) + num_dbl(b))
    else if (a%tag == GCT_RATIO .or. b%tag == GCT_RATIO) then
       out = gc_ratio(gc_numerator(a) * gc_denominator(b) + &
            gc_numerator(b) * gc_denominator(a), &
            gc_denominator(a) * gc_denominator(b))
    else
       out = gc_int(a%ival + b%ival)
    end if
  end function num_add2

  ! One cell of (iterate f x): head x, and a native pending tail
  ! (OBJ_LAZY, i2 = 2) holding [f x]; gce_force applies f and builds the
  ! next cell.
  recursive function iterate_cell(f, x, roots) result(out)
    type(gc_value), intent(in) :: f, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, spec, tail
    integer :: base

    base = vs_enter(3)
    call vs_set(base + 1, f)
    call vs_set(base + 2, x)
    spec = gcv_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    spec = gcv_conj(spec, vs_get(base + 1), [roots, vs_get(base + 2), spec])
    spec = gcv_conj(spec, vs_get(base + 2), [roots, vs_get(base + 1), spec])
    call vs_set(base + 3, spec)
    tail = gc_obj(OBJ_LAZY, [vs_get(base + 3), gc_nil(), gc_nil()], [roots, vs_get(base + 2), vs_get(base + 3)])
    call gc_set_i1(tail, LAZY_PENDING)
    call gc_set_i2(tail, 2)
    call vs_set(base + 3, tail)
    out = gc_obj(OBJ_LAZY, [gc_nil(), vs_get(base + 2), vs_get(base + 3)], [roots, vs_get(base + 2), vs_get(base + 3)])
    call gc_set_i1(out, LAZY_CONS)
    call vs_leave(base)
  end function iterate_cell

  recursive function apply(fn0, args) result(out)
    type(gc_value), intent(in) :: fn0, args
    type(gc_value) :: out, child, body, params, fn
    integer :: base, i, n

    ! A function can arrive wrapped: core.clj's fn macro returns
    ! (with-meta (cons (quote fn*) decl) (meta &form)), so the value a
    ! caller holds is an OBJ_META around the closure. Metadata never
    ! changes what a value IS.
    fn = strip_meta(fn0)
    ! A VAR IS CALLABLE. (#'f x) derefs and applies -- core.clj calls
    ! its own private helpers that way, (#'assert-same-protocol ...), so
    ! that a redefinition is picked up.
    if (gcn_is_var(fn)) fn = gcn_var_value(fn)
    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, args)

    select case (gc_kind(fn))
    case (OBJ_BUILTIN)
       out = call_builtin(gc_i1(fn), args)
    case (OBJ_CLOSURE)
       ! handed over, not kept (see exec's N_CALL): the callee roots
       ! args itself, immediately, and nothing allocates in between
       block
         type(gc_value) :: argl
         argl = vs_get(base + 2)
         call vs_set(base + 2, gc_nil())
         out = invoke_closure(vs_get(base + 1), argl)
       end block
    case (OBJ_MULTIFN)
       ! getFn(dispatchFn.invoke(args)).invoke(args) -- MultiFn.invoke,
       ! exactly. The dispatch function sees the same arguments the
       ! method will.
       block
         type(gc_value) :: dv, meth
         dv = apply(gc_slot(fn, 2), args)
         if (has_error) then
            call vs_leave(base)
            return
         end if
         call vs_set(base + 3, dv)
         meth = gca_get(gc_slot(vs_get(base + 1), 4), vs_get(base + 3))
         ! Then the host supertypes, then :default. See host_super.
         if (meth%tag == GCT_NIL) then
            block
              integer :: si
              type(gc_value) :: sk
              ! A built-in type declares at most a handful of
              ! supertypes; a RECORD declares a dozen -- IRecord,
              ! IHashEq, IObj, ILookup, IPersistentMap, java.util.Map
              ! and more -- so the walk has to be long enough to
              ! reach the one a method was registered on. It stops at
              ! the first nil, so this costs nothing for the others.
              do si = 1, 24
                 sk = host_super(vs_get(base + 3), si, vs_get(base + 1))
                 if (sk%tag == GCT_NIL) exit
                 meth = gca_get(gc_slot(vs_get(base + 1), 4), sk)
                 if (meth%tag /= GCT_NIL) exit
              end do
            end block
         end if
         if (meth%tag == GCT_NIL) &
              meth = gca_get(gc_slot(vs_get(base + 1), 4), &
                             gc_slot(vs_get(base + 1), 3))
         if (meth%tag == GCT_NIL) then
            call fail("No method in multimethod '" // &
                 gcp_str(gc_slot(vs_get(base + 1), 1), .false.) // &
                 "' for dispatch value: " // gcp_str(vs_get(base + 3), .true.))
         else
            out = apply(meth, args)
         end if
       end block
    case default
       ! A keyword and a map are both callable in Clojure, and neither
       ! is a closure: (:k m) looks itself up IN m, and (m :k) looks up
       ! its argument. Same lookup from opposite sides, which is why
       ! both live here rather than as builtins.
       if (fn%tag == GCT_KEY) then
          ! (:a record) is the same lookup `get` does, so it has to
          ! ask the instance the same way -- this is the form people
          ! actually write to read a record field.
          if (gcv_count(args) >= 1) then
             block
               type(gc_value) :: tgt
               logical :: khit
               tgt = strip_meta(gcv_nth(args, 0))
               if (gc_kind(tgt) == OBJ_INST) then
                  out = inst_lookup(tgt, fn, .false., gc_nil(), khit)
                  if (khit) then
                     call vs_leave(base)
                     return
                  end if
               end if
             end block
             ! strip_meta on the ARGUMENT. `fn` is stripped at the
             ! top of apply, so a metadata-carrying map works when
             ! it is the thing being CALLED -- ((with-meta {:a 1} m)
             ! :a) is 1 -- but (:a (with-meta {:a 1} m)) looked the
             ! keyword up in the WRAPPER and answered nil.
             !
             ! That is how `require` lost its :refer. select-keys
             ! ends (with-meta ret (meta map)), so load-lib asks
             ! (:refer filter-opts) of a wrapped map, got nil, and
             ! never called refer at all -- which is why
             ! (:require [clojure.test :refer [deftest]]) interned
             ! nothing and whole test files died on (deftest ...).
             out = coll_get(gcv_nth(args, 0), fn)
          end if
       else if (gca_is(fn)) then
          if (gcv_count(args) >= 1) out = gca_get(fn, gcv_nth(args, 0))
       else if (gc_kind(fn) == OBJ_SET) then
          ! A SET IS CALLABLE, on membership: (#{1 2} 1) is 1 and
          ! (#{1 2} 9) is nil. core.clj leans on it -- destructure asks
          ! (some #{'&} b) whether a binding form has a rest arg -- and
          ! without it that call returned no value at all.
          if (gcv_count(args) >= 1) out = gca_get(gc_slot(fn, 1), gcv_nth(args, 0))
       else if (gcv_is(fn)) then
          ! A vector is callable on an index, as in ([:a :b] 1).
          if (gcv_count(args) >= 1) then
             block
               type(gc_value) :: ix
               ix = gcv_nth(args, 0)
               ! A vector index, narrow by nature.
               if (ix%tag == GCT_INT) out = gcv_nth(fn, int(ix%ival, kind=4))
             end block
          end if
       else
          call fail("not a function: " // gcp_str(fn, .true.))
       end if
    end select

    call vs_leave(base)
  end function apply

  function call_builtin(id, args) result(out)
    integer, intent(in) :: id
    type(gc_value), intent(in) :: args
    type(gc_value) :: out, a, b
    integer :: base, i, n
    ! 64-bit, or every sum would truncate on the way out of %ival.
    integer(gc_ip) :: acc
    logical :: hit

    out = gc_nil()
    hit = .false.
    n = gcv_count(args)
    ! Four slots: args, plus three scratch for the builtins that
    ! accumulate a collection (conj onto a map, the host create
    ! statics, an agent dispatch splicing its extra arguments).
    ! Writing past the frame is a write past the stack top, which
    ! reads back as NIL rather than failing -- so an agent send
    ! with arguments silently dropped them and (send a + 10) left
    ! the agent alone. Widen this before using another slot.
    base = vs_enter(4)
    call vs_set(base + 1, args)

    select case (id)
    case (B_ADD, B_SUB, B_MUL)
       ! Reals used to be IGNORED here. The accumulator read %ival,
       ! which is 0 for a GCT_REAL, so (+ 1.5 2) answered 2 and
       ! (* 2.0 3) answered 0 -- a wrong answer with no error, in the
       ! three most-used functions in the language. `/` and inc/dec
       ! were already right, via num_dbl; these three never were.
       !
       ! Clojure's rule is CONTAGION: a double anywhere in the
       ! expression makes the whole result a double, and otherwise it
       ! stays integral. That needs knowing before accumulating, not
       ! during, so this looks once and then picks an accumulator --
       ! which is also where a Ratio would slot in, as a third case
       ! between the two.
       if (n == 0) then
          if (id == B_MUL) then
             out = gc_int(1)
          else
             out = gc_int(0)
          end if
       else
          block
            logical :: any_real, any_ratio
            real(gc_dp) :: racc
            integer(gc_ip) :: qn, qd, bn, bd, g
            any_real = .false.
            any_ratio = .false.
            do i = 0, n - 1
               b = strip_meta(gcv_nth(args, i))
               if (b%tag == GCT_REAL) any_real = .true.
               if (b%tag == GCT_RATIO) any_ratio = .true.
            end do
            a = gcv_nth(args, 0)
            if (any_ratio .and. .not. any_real) then
               ! Exact rational arithmetic, kept exact. The
               ! contagion order is double > ratio > integer, so
               ! this arm runs only when no double is present --
               ! (+ 1/2 1) is 3/2 but (+ 1/2 0.5) is 1.0.
               !
               ! Reducing at every step, rather than once at the
               ! end, is what keeps the intermediate numerator from
               ! overflowing a 32-bit integer sooner than it must:
               ! summing halves would otherwise square the
               ! denominator on each term.
               b = strip_meta(a)
               qn = gc_numerator(b)
               qd = gc_denominator(b)
               if (n == 1 .and. id == B_SUB) qn = -qn
               do i = 1, n - 1
                  b = strip_meta(gcv_nth(args, i))
                  bn = gc_numerator(b)
                  bd = gc_denominator(b)
                  select case (id)
                  case (B_ADD)
                     qn = qn * bd + bn * qd
                     qd = qd * bd
                  case (B_SUB)
                     qn = qn * bd - bn * qd
                     qd = qd * bd
                  case (B_MUL)
                     qn = qn * bn
                     qd = qd * bd
                  end select
                  g = gc_gcd(qn, qd)
                  qn = qn / g
                  qd = qd / g
               end do
               out = gc_ratio(qn, qd)
            else if (any_real) then
               racc = num_dbl(a)
               if (n == 1 .and. id == B_SUB) racc = -racc
               do i = 1, n - 1
                  b = gcv_nth(args, i)
                  select case (id)
                  case (B_ADD); racc = racc + num_dbl(b)
                  case (B_SUB); racc = racc - num_dbl(b)
                  case (B_MUL); racc = racc * num_dbl(b)
                  end select
               end do
               out = gc_real(racc)
            else
               acc = a%ival
               if (n == 1 .and. id == B_SUB) acc = -acc
               do i = 1, n - 1
                  b = strip_meta(gcv_nth(args, i))
                  select case (id)
                  case (B_ADD); acc = acc + b%ival
                  case (B_SUB); acc = acc - b%ival
                  case (B_MUL); acc = acc * b%ival
                  end select
               end do
               out = gc_int(acc)
            end if
          end block
       end if
    case (B_IDENTICAL)
       ! Same tag and the same thing: one heap slot for a reference,
       ! one value for an immediate. Text is interned here, so two
       ! spellings of :a really are one slot -- which is what makes
       ! (identical? :a :a) true in Clojure too.
       !
       ! The metadata wrapper is NOT seen through: it is a distinct
       ! object, and Clojure agrees that (identical? (with-meta v m) v)
       ! is false.
       a = gcv_nth(args, 0)
       b = gcv_nth(args, 1)
       if (a%tag /= b%tag) then
          out = gc_bool(.false.)
       else
          select case (a%tag)
          case (GCT_NIL); out = gc_bool(.true.)
          case (GCT_BOOL, GCT_INT, GCT_CHAR); out = gc_bool(a%ival == b%ival)
          case (GCT_REAL); out = gc_bool(a%rval == b%rval)
          case (GCT_STR, GCT_SYM, GCT_KEY)
             ! By TEXT, not by pool slot. clotran does not intern
             ! text -- gc_equal says so: the same text allocated
             ! twice is two slots but one value -- while the JVM
             ! interns keywords, symbols and literal strings, so
             ! (identical? :a :a) is true there. Comparing slots
             ! here would answer false, and a record's equiv opens
             ! with (identical? (class this) (class other)), which
             ! is exactly two keywords of the same name.
             out = gc_bool(gc_ref_len(a%ref) == gc_ref_len(b%ref))
             if (truthy(out)) out = gc_bool(gc_ref_is(a%ref, gc_ref_text(b%ref)))
          case default; out = gc_bool(a%ref == b%ref)
          end select
       end if
    case (B_EQ)
       out = gc_bool(.true.)
       do i = 1, n - 1
          if (.not. deep_equal(gcv_nth(args, i - 1), gcv_nth(args, i), &
               [vs_get(base + 1)])) then
             out = gc_bool(.false.)
             exit
          end if
       end do
    case (B_LT)
       out = gc_bool(.true.)
       do i = 1, n - 1
          a = gcv_nth(args, i - 1)
          b = gcv_nth(args, i)
          if (.not. num_lt(a, b)) then
             out = gc_bool(.false.)
             exit
          end if
       end do
    case (B_LIST)
       out = gcl_empty([vs_get(base + 1)])
       do i = n - 1, 0, -1
          out = gcl_cons(gcv_nth(vs_get(base + 1), i), out, [vs_get(base + 1)])
       end do
    case (B_VECTOR)
       out = vs_get(base + 1)
    case (B_COUNT)
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke0(a, "count", hit)
          if (hit) then
             call vs_leave(base)
             return
          end if
       end if
       out = gc_int(sq_count(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)]))
    case (B_FIRST)
       out = sq_first(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)])
    case (B_REST)
       out = sq_rest(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)])
    case (B_NEXT)
       ! RT.next is RT.more put through seq: the two differ only in
       ! what an exhausted sequence gives back, nil versus (). Every
       ! `if (next x)` in core.clj rests on that difference.
       out = to_seq(sq_rest(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)]), &
            [vs_get(base + 1)])
    case (B_CONS)
       ! (cons x anything-seqable) is a SEQ, so the tail is seq'd
       ! rather than type-tested: (cons 1 "ab") is (1 \a \b).
       !
       ! A list tail stays a list, which keeps count O(1) on the common
       ! case. Anything else becomes an already-realised lazy cell --
       ! head and tail in place, nothing forced -- because a plain cons
       ! cell cannot hold an unrealised or viewed rest, and forcing
       ! here would defeat (cons n (from (+ n 1))).
       block
         type(gc_value) :: tl
         ! A LAZY tail is taken as-is and never seq'd: to_seq
         ! forces, and forcing here is not a slowdown but an
         ! infinite loop -- (cons n (from (+ n 1))) would realise
         ! the whole infinite seq to build one cell.
         tl = gcv_nth(vs_get(base + 1), 1)
         if (gc_kind(tl) /= OBJ_LAZY) &
              tl = to_seq(tl, [vs_get(base + 1)])
         ! An EMPTY tail seq's is to nil, and (cons 1 ()) must still be
         ! the LIST (1), not a lazy cell. Macro expansions are lists,
         ! and the evaluator only recognises a list as a form -- get
         ! this wrong and a macro returns its own expansion unevaluated.
         if (tl%tag == GCT_NIL) tl = gcl_empty([vs_get(base + 1)])
         if (gcl_is(tl)) then
            out = gcl_cons(gcv_nth(vs_get(base + 1), 0), tl, [vs_get(base + 1), tl])
         else
            out = gc_obj(OBJ_LAZY, &
                 [gc_nil(), gcv_nth(vs_get(base + 1), 0), tl], &
                 [vs_get(base + 1), tl])
            call gc_set_i1(out, LAZY_CONS)
         end if
       end block
    case (B_STR)
       block
         character(len=:), allocatable :: acc2
         acc2 = ""
         do i = 0, n - 1
            acc2 = acc2 // to_string_text(gcv_nth(vs_get(base + 1), i))
         end do
         out = gc_str(acc2, [vs_get(base + 1)])
       end block
    case (B_NOT)
       out = gc_bool(.not. truthy(gcv_nth(args, 0)))
    case (B_NILP)
       a = gcv_nth(args, 0)
       out = gc_bool(a%tag == GCT_NIL)
    case (B_NTH)
       ! Indexed where the collection is indexable, a seq walk where it
       ! is not -- (nth (range 5) 2) has to work, and a range has no
       ! index. Same fallback Clojure has.
       block
         type(gc_value) :: coll, idx, walk
         integer :: want, k
         coll = gcv_nth(vs_get(base + 1), 0)
         idx = gcv_nth(vs_get(base + 1), 1)
         want = idx%ival
         out = gc_nil()
         if (gc_kind(coll) == OBJ_CHUNK) then
            out = chunk_nth(coll, want)
         else if (gcv_is(coll) .or. coll%tag == GCT_STR) then
            if (want >= 0 .and. want < seq_len(coll)) &
                 out = seq_elem(coll, want, [vs_get(base + 1)])
         else if (want >= 0) then
            walk = to_seq(coll, [vs_get(base + 1)])
            do k = 1, want
               walk = sq_rest(walk, [vs_get(base + 1)])
               walk = to_seq(walk, [vs_get(base + 1)])
            end do
            if (walk%tag /= GCT_NIL) out = sq_first(walk, [vs_get(base + 1)])
         end if
         if (out%tag == GCT_NIL .and. n >= 3) out = gcv_nth(vs_get(base + 1), 2)
       end block
    case (B_GET)
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_lookup(a, gcv_nth(args, 1), n >= 3, gcv_nth(args, 2), hit)
          if (hit) then
             call vs_leave(base)
             return
          end if
       end if
       out = coll_get(a, gcv_nth(args, 1))
       if (out%tag == GCT_NIL .and. n >= 3) then
          if (.not. coll_has(a, gcv_nth(args, 1))) out = gcv_nth(args, 2)
       end if
    case (B_ASSOC)
       ! (assoc nil k v) CREATES a map -- which is what makes assoc-in
       ! able to build a path that does not exist yet. Returning nil
       ! made (assoc-in {} [:impls t] m) produce {:impls nil}, so every
       ! protocol extension was silently discarded.
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke(a, "assoc", rest_args(vs_get(base + 1), 1), hit)
          if (hit) then
             call vs_leave(base)
             return
          end if
       end if
       if (a%tag == GCT_NIL) a = gca_empty([vs_get(base + 1)])
       if (gcv_is(a)) then
          ! A VECTOR IS ASSOCIATIVE BY INDEX, and assoc on one
          ! answered nil -- gca_assoc only knows maps. An index
          ! equal to the count APPENDS, which is the one place
          ! assoc grows a vector; past that it throws, as
          ! PersistentVector.assocN does. clojure.data/vectorize
          ! is built entirely out of this.
          block
            type(gc_value) :: ix
            ix = strip_meta(gcv_nth(vs_get(base + 1), 1))
            if (ix%tag /= GCT_INT) then
               call fail("assoc: a vector takes an integer key")
            else if (ix%ival == int(gcv_count(a), gc_ip)) then
               out = gcv_conj(a, gcv_nth(vs_get(base + 1), 2), [vs_get(base + 1)])
            else if (ix%ival >= 0 .and. ix%ival < int(gcv_count(a), gc_ip)) then
               out = gcv_assoc(a, int(ix%ival), &
                    gcv_nth(vs_get(base + 1), 2), [vs_get(base + 1)])
            else
               call fail("Index out of bounds")
            end if
          end block
       else
          out = gca_assoc(a, &
               gcv_nth(vs_get(base + 1), 1), &
               gcv_nth(vs_get(base + 1), 2), [vs_get(base + 1)])
       end if
    case (B_KEYS, B_VALS)
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_entries(a, id == B_KEYS, hit)
          if (hit) then
             call vs_leave(base)
             return
          end if
       end if
       block
         type(gc_value), allocatable :: ks(:), vls(:)
         call gca_entries(strip_meta(gcv_nth(vs_get(base + 1), 0)), ks, vls)
         out = gcl_empty([vs_get(base + 1)])
         do i = size(ks), 1, -1
            if (id == B_KEYS) then
               out = gcl_cons(ks(i), out, [vs_get(base + 1), out])
            else
               out = gcl_cons(vls(i), out, [vs_get(base + 1), out])
            end if
         end do
       end block
    case (B_CONJ)
       ! Collection-polymorphic ON PURPOSE, and the one place that
       ! should NOT go through seq: (conj [1] 2) appends, (conj (list 1)
       ! 2) prepends, (conj {:a 1} [:b 2]) assocs. That difference is
       ! the feature, not an inconsistency.
       ! VARIADIC: (conj [] 1 2) is [1 2]. Taking only the first item
       ! silently dropped the rest, which is how maybe-destructured
       ! built a one-element parameter vector.
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       do i = 1, n - 1
          a = conj1(a, gcv_nth(vs_get(base + 1), i), [vs_get(base + 1)])
          call vs_set(base + 2, a)
       end do
       out = a
    case (B_EMPTY)
       block
         type(gc_value) :: sv
         sv = to_seq(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)])
         out = gc_bool(sv%tag == GCT_NIL)
       end block
    case (B_APPLY)
       ! (apply f a b args) -- the last argument is a SEQUENCE spread
       ! into the call, which is what makes variadic forwarding work.
       block
         type(gc_value) :: fargs, last
         integer :: j
         fargs = gcv_empty([vs_get(base + 1)])
         do j = 1, n - 2
            fargs = gcv_conj(fargs, gcv_nth(vs_get(base + 1), j), [vs_get(base + 1), fargs])
         end do
         ! Through coll_to_vector, not a two-case count: the last
         ! argument is whatever `seq` produced, which is a VIEW over a
         ! vector as often as it is a list, and counting only lists and
         ! vectors made (apply f (seq xs)) call f with no arguments at
         ! all.
         call vs_set(base + 2, fargs)
         last = coll_to_vector(gcv_nth(vs_get(base + 1), n - 1), &
              [vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, last)
         fargs = vs_get(base + 2)
         do j = 0, gcv_count(vs_get(base + 3)) - 1
            fargs = gcv_conj(fargs, gcv_nth(vs_get(base + 3), j), &
                 [vs_get(base + 1), vs_get(base + 3)])
            call vs_set(base + 2, fargs)
         end do
         fargs = vs_get(base + 2)
         out = apply(gcv_nth(vs_get(base + 1), 0), fargs)
       end block
    case (B_PRN)
       do i = 0, n - 1
          if (i > 0) write(*, '(A)', advance='no') " "
          write(*, '(A)', advance='no') gcp_str(gcv_nth(vs_get(base + 1), i), .true.)
       end do
       write(*, '(A)') ""
       out = gc_nil()
    case (B_NS)
       ! The bootstrap ns, and a deliberate near-copy of RT.java's
       ! bootNamespace: find-or-create the namespace and switch to it,
       ! nothing else. core.clj's own ns macro (its line 5976) replaces
       ! this by ordinary definition once it exists.
       !
       ! A macro, so the name arrives UNEVALUATED, at index 2 -- every
       ! macro is called with &form and &env ahead of its own
       ! arguments. RT.java writes the same signature out longhand:
       ! invoke(Object __form, Object __env, Object arg1).
       !
       ! It also arrives WRAPPED, since core.clj's own first form is
       ! (ns ^{:doc ...} clojure.core).
       a = strip_meta(gcv_nth(vs_get(base + 1), 2))
       if (a%tag /= GCT_SYM) then
          call fail("ns needs a symbol name")
       else
          out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(base + 1)])
          call gcn_set_current(out)
       end if
    case (B_INNS)
       ! A FUNCTION, not a macro -- RT.java interns inNamespace without
       ! setMacro, so (in-ns 'user) evaluates its argument.
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       if (a%tag /= GCT_SYM) then
          call fail("in-ns needs a symbol")
       else
          out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(base + 1)])
          call gcn_set_current(out)
       end if
    case (B_META)
       ! A Var keeps its metadata in slot 2; anything else carries it
       ! in a wrapper. nil when there is none, as Clojure's meta does.
       a = gcv_nth(vs_get(base + 1), 0)
       out = gc_nil()
       if (gcn_is_var(a) .or. gc_kind(a) == OBJ_NS) then
          out = gc_slot(a, meta_slot(a))
       else if (gc_kind(a) == OBJ_META) then
          out = gc_slot(a, 2)
       end if
    case (B_WITHMETA)
       ! REPLACES metadata, never nests it. IObj.withMeta returns a new
       ! object carrying the new map, not an object wrapping the old
       ! one -- and defn calls (with-meta name m) on a name the reader
       ! already wrapped, so nesting buried the symbol two deep and the
       ! Var got interned under a wrapper nobody could name.
       out = gc_obj(OBJ_META, &
            [strip_meta(gcv_nth(vs_get(base + 1), 0)), gcv_nth(vs_get(base + 1), 1)], &
            [vs_get(base + 1)])
    case (B_QUOT, B_REM)
       ! Both used to read %ival only, so (quot 7.0 2) answered 0
       ! rather than 3.0 -- the same silent discard that + - * had.
       ! A zero divisor was not checked either: Clojure raises
       ! "Divide by zero" here for doubles as well as integers,
       ! unlike `/`, where (/ 1.0 0) is ##Inf.
       a = strip_meta(gcv_nth(args, 0)); b = strip_meta(gcv_nth(args, 1))
       if (is_ratio(a) .or. is_ratio(b)) then
          ! Exact, and the integer arm below would have read a ratio
          ! as its numerator: (quot 7/2 1) would answer 7, not 3.
          ! a/b is (an*bd)/(ad*bn), and quot truncates that toward
          ! zero -- which is what Fortran's integer division does.
          block
            integer(gc_ip) :: an, ad, bn, bd, qi
            an = gc_numerator(a); ad = gc_denominator(a)
            bn = gc_numerator(b); bd = gc_denominator(b)
            if (bn == 0) then
               call fail("Divide by zero")
            else
               qi = (an * bd) / (ad * bn)
               if (id == B_QUOT) then
                  out = gc_int(qi)
               else
                  ! rem is a - b*quot, kept exact.
                  out = gc_ratio(an * bd - qi * bn * ad, ad * bd)
               end if
            end if
          end block
       else if (a%tag == GCT_REAL .or. b%tag == GCT_REAL) then
          if (num_dbl(b) == 0.0_gc_dp) then
             call fail("Divide by zero")
          else if (id == B_QUOT) then
             out = gc_real(aint(num_dbl(a) / num_dbl(b)))
          else
             out = gc_real(mod(num_dbl(a), num_dbl(b)))
          end if
       else if (b%ival == 0) then
          call fail("Divide by zero")
       else if (id == B_QUOT) then
          out = gc_int(a%ival / b%ival)
       else
          out = gc_int(mod(a%ival, b%ival))
       end if
    case (B_SECOND)
       out = sq_first(sq_rest(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)]), &
            [vs_get(base + 1)])
    case (B_SEQ)
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke0(a, "seq", hit)
          if (hit) then
             call vs_leave(base)
             return
          end if
       end if
       out = to_seq(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)])
    case (B_DISSOC)
       a = strip_meta(gcv_nth(vs_get(base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke(a, "without", rest_args(vs_get(base + 1), 1), hit)
          if (hit) then
             call vs_leave(base)
             return
          end if
       end if
       out = gca_dissoc(gcv_nth(vs_get(base + 1), 0), gcv_nth(vs_get(base + 1), 1), &
            [vs_get(base + 1)])
    case (B_NAME)
       ! The NAME PART, without the namespace: (name (quote a/b)) is
       ! "b". Returning the whole text made every qualified symbol
       ! answer with its qualifier still attached.
       out = gc_str(name_part(gcv_nth(args, 0)), [vs_get(base + 1)])
    case (B_GETNAME)
       ! .getName answers in the type the host uses: a Namespace gives
       ! back a SYMBOL (which is what ns-name returns), everything else
       ! a string.
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_NS) then
          out = gc_sym(gcn_name(a), [vs_get(base + 1)])
       else
          out = gc_str(name_part(a), [vs_get(base + 1)])
       end if
    case (B_KEYWORD, B_SYMBOL2)
       ! Two arguments make a QUALIFIED name: (symbol "clojure.core"
       ! "require") is clojure.core/require. Ignoring the first argument
       ! returned the NAMESPACE as the symbol, and (ns ... (:require))
       ! then evaluated clojure.core in head position.
       block
         character(len=:), allocatable :: t
         type(gc_value) :: q
         if (n >= 2) then
            ! A NIL namespace means unqualified: core.clj calls
            ! (symbol (namespace b) (name b)) on names that have no
            ! namespace, and gluing an empty qualifier on produced /x.
            q = strip_meta(gcv_nth(args, 0))
            if (q%tag == GCT_NIL) then
               t = name_part(gcv_nth(args, 1))
            else
               t = name_part(q) // "/" // name_part(gcv_nth(args, 1))
            end if
         else
            ! ONE argument keeps the WHOLE name, qualifier and all:
            ! Symbol.intern(String) splits on the slash and sets both
            ! halves, so (symbol "a.b.C/create") is a.b.C/create and
            ! its namespace is "a.b.C". name_part STRIPS the
            ! qualifier, which is right for `name` and wrong here: it
            ! made that symbol just `create`, so every form built as
            ! (~(symbol (str classname "/create")) ...) lost the
            ! class it was calling -- which is how defrecord's
            ! map->Name factory came out as (create m).
            block
              type(gc_value) :: a0
              a0 = strip_meta(gcv_nth(args, 0))
              if (a0%tag == GCT_STR .or. a0%tag == GCT_SYM .or. &
                   a0%tag == GCT_KEY) then
                 t = class_of_text(a0)
              else
                 t = name_part(a0)
              end if
            end block
         end if
         if (id == B_KEYWORD) then
            out = gc_key(t, [vs_get(base + 1)])
         else
            out = gc_sym(t, [vs_get(base + 1)])
         end if
       end block

    case (B_SUBS)
       block
         character(len=:), allocatable :: t
         integer :: lo, hi
         a = gcv_nth(args, 0)
         t = gc_ref_text(a%ref)
         b = gcv_nth(args, 1)
         lo = b%ival + 1
         hi = len(t)
         if (n >= 3) then
            b = gcv_nth(args, 2)
            hi = b%ival
         end if
         if (lo < 1 .or. hi > len(t) .or. lo > hi + 1) then
            call fail("subs: index out of range")
         else
            out = gc_str(t(lo:hi), [vs_get(base + 1)])
         end if
       end block
    case (B_VEC)
       out = coll_to_vector(gcv_nth(args, 0), [vs_get(base + 1)])
    case (B_HMAP)
       ! A flat seq of alternating keys and values, which is the shape
       ! PersistentHashMap.create takes.
       block
         type(gc_value) :: items, mp
         integer :: i2
         items = coll_to_vector(gcv_nth(args, 0), [vs_get(base + 1)])
         call vs_set(base + 2, items)
         mp = gca_empty([vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, mp)
         do i2 = 0, gcv_count(vs_get(base + 2)) - 2, 2
            mp = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 2), i2), &
                 gcv_nth(vs_get(base + 2), i2 + 1), &
                 [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
            call vs_set(base + 3, mp)
         end do
         out = vs_get(base + 3)
       end block
    case (B_HSET)
       block
         type(gc_value) :: items, mp
         integer :: i2
         items = coll_to_vector(gcv_nth(args, 0), [vs_get(base + 1)])
         call vs_set(base + 2, items)
         mp = gca_empty([vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, mp)
         do i2 = 0, gcv_count(vs_get(base + 2)) - 1
            mp = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 2), i2), &
                 gcv_nth(vs_get(base + 2), i2), &
                 [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
            call vs_set(base + 3, mp)
         end do
         out = gc_obj(OBJ_SET, [vs_get(base + 3)], [vs_get(base + 3)])
       end block
    case (B_BITAND, B_BITOR, B_BITXOR, B_SHL, B_SHR)
       a = gcv_nth(args, 0); b = gcv_nth(args, 1)
       select case (id)
       case (B_BITAND); out = gc_int(iand(a%ival, b%ival))
       case (B_BITOR);  out = gc_int(ior(a%ival, b%ival))
       case (B_BITXOR); out = gc_int(ieor(a%ival, b%ival))
       case (B_SHL);    out = gc_int(shiftl(a%ival, int(b%ival)))
       case (B_SHR);    out = gc_int(shifta(a%ival, int(b%ival)))
       end select
    case (B_BITNOT)
       a = gcv_nth(args, 0)
       out = gc_int(not(a%ival))
    case (B_LONGCAST)
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_REAL) then
          out = gc_int(int(a%rval))
       else if (is_ratio(a)) then
          ! (int 1/2) is 0 -- truncation toward zero, the same as for
          ! a double. The else branch would have handed the ratio
          ! straight back, unconverted.
          out = gc_int(gc_numerator(a) / gc_denominator(a))
       else if (a%tag == GCT_CHAR) then
          out = gc_int(a%ival)
       else
          out = a
       end if
    case (B_ANEWINST)
       out = array_new_instance(vs_get(base + 1), [vs_get(base + 1)])

    case (B_NUMCAST)
       ! Class.cast: the value unchanged, or a ClassCastException.
       ! The check is the whole point -- Clojure's `cast` exists to
       ! THROW on the wrong type, so returning x regardless would
       ! make (cast Number "a") answer "a" instead of failing.
       block
         type(gc_value) :: v
         v = strip_meta(gcv_nth(args, 0))
         if (is_number(v)) then
            out = gcv_nth(args, 0)
         else
            call fail("Cannot cast " // type_name(v) // " to java.lang.Number")
         end if
       end block

    case (B_NUMEQ)
       ! == : equal as NUMBERS, across int and real. Non-numeric
       ! arguments are an error in Clojure rather than false, which
       ! is the difference from =.
       block
         integer :: k
         logical :: same
         type(gc_value) :: x, y
         same = .true.
         x = strip_meta(gcv_nth(args, 0))
         if (.not. is_number(x)) then
            call fail("== : not a number")
         else
            do k = 1, n - 1
               y = strip_meta(gcv_nth(args, k))
               if (.not. is_number(y)) then
                  call fail("== : not a number")
                  same = .false.
                  exit
               end if
               if (num_dbl(x) /= num_dbl(y)) same = .false.
            end do
            if (.not. has_error) out = gc_bool(same)
         end if
       end block

    case (B_ABS)
       block
         type(gc_value) :: x
         x = strip_meta(gcv_nth(args, 0))
         if (x%tag == GCT_REAL) then
            out = gc_real(abs(x%rval))
         else if (is_ratio(x)) then
            out = gc_ratio(abs(gc_numerator(x)), gc_denominator(x))
         else
            out = gc_int(abs(x%ival))
         end if
       end block

    case (B_NUMER, B_DENOM)
       ! core.clj reads these as INSTANCE members -- (.numerator r) --
       ! so they arrive with the ratio as the first argument. An
       ! integer answers itself over 1, which is what Clojure does for
       ! a value that normalized out of ratio form.
       block
         type(gc_value) :: x
         x = strip_meta(gcv_nth(args, 0))
         if (.not. is_number(x)) then
            call fail("numerator/denominator: not a number")
         else if (id == B_NUMER) then
            out = gc_int(gc_numerator(x))
         else
            out = gc_int(gc_denominator(x))
         end if
       end block

    case (B_ARRSORT)
       ! (. java.util.Arrays (sort a cmp)) -- in place, and the
       ! return value is ignored by core.clj's sort, which reads the
       ! array back with (seq a).
       block
         type(gc_value) :: arr0
         arr0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(arr0) /= OBJ_ARRAY) then
            call fail("Arrays/sort: not an array")
         else
            call array_sort(arr0, gcv_nth(args, 1))
            out = gc_nil()
         end if
       end block

    case (B_CMPCALL)
       ! Arrives as (comparator x y): an instance member prepends its
       ! target. Same AFunction.compare rule the sort uses, so a
       ! predicate like > works here too.
       out = gc_int(comparator_call(gcv_nth(args, 0), gcv_nth(args, 1), gcv_nth(args, 2)))

    case (B_SBASIS)
       out = struct_basis(args, [vs_get(base + 1)])
    case (B_SCREATE)
       out = struct_create(args, [vs_get(base + 1)])
    case (B_SCONSTRUCT)
       out = struct_construct(args, [vs_get(base + 1)])
    case (B_SACCESSOR)
       out = struct_accessor(args, [vs_get(base + 1)])

    case (B_COLLEMPTY)
       out = coll_empty(gcv_nth(args, 0), [vs_get(base + 1)])

    case (B_MACROEXP1)
       out = macroexpand_1step(gcv_nth(args, 0))

    case (B_ASIFASSOC)
       ! One collection, alternating k v, as if by repeated assoc.
       block
         type(gc_value) :: kvv, acc
         integer :: i, n2
         kvv = coll_to_vector(gcv_nth(args, 0), [vs_get(base + 1)])
         call vs_set(base + 2, kvv)
         n2 = gcv_count(vs_get(base + 2))
         acc = gca_empty([vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, acc)
         do i = 0, n2 - 2, 2
            acc = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 2), i), &
                 gcv_nth(vs_get(base + 2), i + 1), &
                 [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
            call vs_set(base + 3, acc)
         end do
         out = vs_get(base + 3)
       end block

    case (B_PREPRET)
       ! (prepRet component-type value) -- the value, unchanged.
       out = gcv_nth(args, 1)

    case (B_ACLONE)
       ! A COPY, sharing nothing. Clojure's aclone is shallow, which
       ! for a value array means the elements are shared and the
       ! storage is not -- the same thing this does.
       block
         type(gc_value) :: a0, run, e
         character(len=:), allocatable :: kn, err
         integer, allocatable :: ext(:), lows(:)
         integer :: h, h2, k, n2
         a0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(a0) /= OBJ_ARRAY) then
            call fail("aclone: not an array")
            call vs_leave(base)
            return
         end if
         call vs_set(base + 2, a0)
         h = gc_i1(vs_get(base + 2))
         kn = gcna_kind(h)
         ! The clone has the shape of the VIEW, not of the buffer
         ! behind it: (aclone (aget m 0)) on a 2x3 is a fresh length-3
         ! array, the way Java's aclone of one row of a [[I is. Taking
         ! gcna_extents(h) here cloned the whole 2x3 instead. Every
         ! dimension of a fresh array is 0-based, so lows is zeros
         ! rather than the source's.
         ext = array_own_extents(vs_get(base + 2))
         allocate(lows(size(ext)))
         lows = 0
         h2 = gcna_new(kn, ext, lows, err)
         if (h2 == 0) then
            call fail(err)
            call vs_leave(base)
            return
         end if
         n2 = gcna_total(h2)
         run = gc_nil()
         if (kn == "value") run = gc_vec(max(1, n2), [vs_get(base + 2)])
         call vs_set(base + 3, run)
         out = gc_obj(OBJ_ARRAY, [vs_get(base + 3)], &
              [vs_get(base + 2), vs_get(base + 3)])
         call gc_set_i1(out, h2)
         call gc_set_i2(out, -1) ! owns the handle -- not a slice
         do k = 1, n2
            e = array_elem(vs_get(base + 2), k)
            call array_put(out, k, e)
         end do
       end block

    case (B_MAKE_ARRAY)
       ! (make-array kind extent ...) -- (make-array "real8" 3 4) is a
       ! 3x4 real(8), zero-filled, lower bound 0 on every dimension.
       ! Clojure's own make-array takes a class; clotran takes a kind
       ! NAME, because a Fortran kind is what the buffer actually is
       ! and there is no class to name.
       block
         character(len=:), allocatable :: kname, err
         integer, allocatable :: ext(:), lows(:)
         integer :: k, h, nd
         type(gc_value) :: a0, run, tmp
         a0 = strip_meta(gcv_nth(args, 0))
         nd = n - 1
         if (nd < 1) then
            call fail("make-array: needs a kind and at least one extent")
            call vs_leave(base)
            return
         end if
         kname = text_of(a0)
         allocate(ext(nd), lows(nd))
         do k = 1, nd
            tmp = gcv_nth(args, k)
            ext(k) = tmp%ival
            lows(k) = 0
         end do
         h = gcna_new(kname, ext, lows, err)
         if (h == 0) then
            call fail(err)
            call vs_leave(base)
            return
         end if
         ! A `value` array keeps its elements in a GC RUN so the
         ! collector traces them; every numeric kind has its buffer in
         ! the registry and leaves slot 1 nil.
         run = gc_nil()
         if (kname == "value") run = gc_vec(max(1, gcna_total(h)), [vs_get(base + 1)])
         out = gc_obj(OBJ_ARRAY, [run], [vs_get(base + 1), run])
         call gc_set_i1(out, h)
         call gc_set_i2(out, -1) ! owns the handle -- not a slice
       end block

    case (B_DGEMM)
       ! (fortran/dgemm a b) -- a new real8 array, a times b. The first
       ! Fortran library routine called from clotran (PLAN.md step 6):
       ! the buffers of a and b go to the reference DGEMM exactly as
       ! Fortran declares them, and the product comes back in a buffer
       ! this side allocated. Whole arrays only -- a slice is strided
       ! and would be copied, which is the one thing this must not do.
       block
         type(gc_value) :: a0, b0
         integer, allocatable :: ea(:), eb(:)
         integer :: h, m, n, k
         logical :: ok
         character(len=:), allocatable :: err
         a0 = strip_meta(gcv_nth(args, 0))
         b0 = strip_meta(gcv_nth(args, 1))
         if (gc_kind(a0) /= OBJ_ARRAY .or. gc_kind(b0) /= OBJ_ARRAY) then
            call fail("dgemm: needs two arrays")
         else if (gc_i2(a0) /= -1 .or. gc_i2(b0) /= -1) then
            call fail("dgemm: a slice is not contiguous; pass whole arrays")
         else if (gcna_kind(gc_i1(a0)) /= "real8" .or. gcna_kind(gc_i1(b0)) /= "real8") then
            call fail("dgemm: needs real8 arrays")
         else
            ea = gcna_extents(gc_i1(a0))
            eb = gcna_extents(gc_i1(b0))
            if (size(ea) /= 2 .or. size(eb) /= 2) then
               call fail("dgemm: needs rank-2 arrays")
            else if (ea(2) /= eb(1)) then
               call fail("dgemm: inner dimensions differ")
            else
               m = ea(1); k = ea(2); n = eb(2)
               h = gcna_new("real8", [m, n], [0, 0], err)
               if (h == 0) then
                  call fail(err)
               else
                  call gcna_dgemm(gc_i1(a0), gc_i1(b0), h, m, n, k, ok)
                  if (.not. ok) then
                     call gcna_release(h)
                     call fail("dgemm: refused")
                  else
                     out = gc_obj(OBJ_ARRAY, [gc_nil()], [vs_get(base + 1)])
                     call gc_set_i1(out, h)
                     call gc_set_i2(out, -1)
                  end if
               end if
            end if
         end if
       end block

    case (B_SLURP)
       block
         character(len=:), allocatable :: path, text
         integer :: u, st, fsize
         path = text_of(gcv_nth(args, 0))
         open(newunit=u, file=path, access="stream", form="unformatted", &
              status="old", action="read", iostat=st)
         if (st /= 0) then
            call fail_as("java.io.FileNotFoundException", path // " (No such file or directory)", [vs_get(base + 1)])
         else
            inquire(unit=u, size=fsize)
            allocate(character(len=fsize) :: text)
            if (fsize > 0) read(u, iostat=st) text
            close(u)
            out = gc_str(text, [vs_get(base + 1)])
         end if
       end block

    case (B_CS_ENTROPY)
       out = gc_real(csb_entropy(num_dbl(strip_meta(gcv_nth(args, 0)))))

    case (B_CS_READOPT, B_CS_DGLD, B_CS_SOLVOUT)
       out = chemsol_call(id, gcv_nth(args, 0), gcv_nth(args, 1), vs_get(base + 1))

    case (B_ALENGTH)
       ! Clojure's alength on a multi-dimensional array is the
       ! OUTER length -- (alength (make-array Integer/TYPE 2 3)) is
       ! 2, not 6, verified against clj. That is the array's own
       ! FIRST extent, which for rank 1 is also the total -- the
       ! two only look like the same rule by coincidence at rank 1.
       block
         type(gc_value) :: a0
         integer, allocatable :: ext(:)
         a0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(a0) /= OBJ_ARRAY) then
            call fail("alength: not an array")
         else
            ext = array_own_extents(a0)
            out = gc_int(ext(1))
         end if
       end block

    case (B_ARRAY_KIND)
       block
         type(gc_value) :: a0
         a0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(a0) /= OBJ_ARRAY) then
            call fail("array-kind: not an array")
         else
            out = gc_str(gcna_kind(gc_i1(a0)), [vs_get(base + 1)])
         end if
       end block

    case (B_ARRAY_SHAPE)
       block
         type(gc_value) :: a0, acc
         integer, allocatable :: ext(:)
         integer :: k
         a0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(a0) /= OBJ_ARRAY) then
            call fail("array-shape: not an array")
         else
            ext = array_own_extents(a0)
            acc = gcv_empty([vs_get(base + 1)])
            call vs_set(base + 2, acc)
            do k = 1, size(ext)
               acc = gcv_conj(vs_get(base + 2), gc_int(ext(k)), [vs_get(base + 2)])
               call vs_set(base + 2, acc)
            end do
            out = vs_get(base + 2)
         end if
       end block

    case (B_AGET, B_ASET)
       ! (aget a i j ...) and (aset a i j ... v). FEWER subscripts than
       ! the array's own rank is not an error: Clojure's own aget/aset
       ! always pass exactly one index and recur --
       !   ([array idx & idxs] (apply aget (aget array idx) idxs))
       ! -- so (aget m 1) on a rank-2 array must hand back something
       ! that is ITSELF an array. That is array_make_slice: a VIEW
       ! sharing the same buffer, not a copy. See its header comment
       ! for the column-major arithmetic.
       block
         type(gc_value) :: a0, val, tmp2
         integer, allocatable :: subs(:)
         integer :: k, h, at, nsub, own_rank, foff, fstr
         integer(8) :: iv   ! an element of an int8 array is 64-bit
         real(gc_dp) :: rv
         logical :: ok
         character(len=:), allocatable :: kn
         a0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(a0) /= OBJ_ARRAY) then
            call fail("aget/aset: not an array")
            call vs_leave(base)
            return
         end if
         h = gc_i1(a0)
         nsub = n - 1
         if (id == B_ASET) nsub = n - 2
         if (nsub < 1) then
            call fail("aget/aset: needs at least one index")
            call vs_leave(base)
            return
         end if
         allocate(subs(nsub))
         do k = 1, nsub
            tmp2 = gcv_nth(args, k)
            subs(k) = tmp2%ival
         end do

         own_rank = array_own_rank(a0)
         if (nsub > own_rank) then
            call fail("aget/aset: too many indices")
            call vs_leave(base)
            return
         end if

         if (nsub < own_rank) then
            ! A SLICE over the remaining dimensions. aset never
            ! assigns a whole sub-array at once -- core.clj's own
            ! multi-arg aset always slices down to a full index before
            ! writing -- so this path is aget-only.
            if (id == B_ASET) then
               call fail("aset: not enough indices")
               call vs_leave(base)
               return
            end if
            out = array_make_slice(a0, subs, [vs_get(base + 1)])
            call vs_leave(base)
            return
         end if

         ! Every own dimension is specified: fold to the REAL buffer
         ! position, whether a0 is a base array or already a slice.
         call array_fold(a0, subs, foff, fstr, ok)
         if (.not. ok) then
            call fail("aget/aset: index out of bounds")
            call vs_leave(base)
            return
         end if
         at = foff + 1

         kn = gcna_kind(h)
         if (kn == "value") then
            ! The run is the storage. gc_vec_set is O(1) and the
            ! collector already traces what goes in.
            if (id == B_AGET) then
               out = gc_vec_get(gc_slot(a0, 1), at)
            else
               val = gcv_nth(args, n - 1)
               call gc_vec_set(gc_slot(a0, 1), at, val)
               out = val
            end if
         else if (id == B_AGET) then
            if (kn == "logical") then
               block
                 logical :: lv
                 call gcna_get_logical(h, at, lv, ok)
                 out = gc_bool(lv)
               end block
            else if (kn == "int4" .or. kn == "int8") then
               call gcna_get_int(h, at, iv, ok)
               out = gc_int(iv)
            else
               call gcna_get_real(h, at, rv, ok)
               out = gc_real(rv)
            end if
            if (.not. ok) call fail("aget: unreadable element kind '" // kn // "'")
         else
            val = strip_meta(gcv_nth(args, n - 1))
            if (kn == "logical") then
               call gcna_set_logical(h, at, truthy(val), ok)
            else if (val%tag == GCT_INT) then
               call gcna_set_int(h, at, val%ival, ok)
            else
               call gcna_set_real(h, at, num_dbl(val), ok)
            end if
            if (.not. ok) then
               call fail("aset: cannot store that in a '" // kn // "' array")
            else
               out = val
            end if
         end if
       end block
    case (B_ISREALIZED)
       ! realized? is (.isRealized x) on an IPending. The two pending
       ! things here are a delay and a lazy seq; anything else has
       ! nothing left to do and is realized by definition.
       block
         type(gc_value) :: a0
         a0 = strip_meta(gcv_nth(args, 0))
         if (gc_kind(a0) == OBJ_DELAY) then
            out = gc_bool(gc_i1(a0) /= 0)
         else if (gc_kind(a0) == OBJ_LAZY) then
            out = gc_bool(gc_i1(a0) /= LAZY_PENDING)
         else
            out = gc_bool(.true.)
         end if
       end block
    case (B_DBLVALUE)
       ! Double/valueOf PARSES, it does not cast. Pointing it at the
       ! `double` cast made (parse-double "1.5") answer 0.0 -- a silent
       ! wrong answer, and worse than the missing member it replaced,
       ! because num_dbl of a string is zero rather than an error.
       !
       ! core.clj has already matched the string against its own regex
       ! by the time parse-double gets here, so a failure to read it is
       ! a real error rather than a "not a number, return nil".
       block
         type(gc_value) :: a0
         character(len=:), allocatable :: t
         real(gc_dp) :: dv
         integer :: st
         a0 = strip_meta(gcv_nth(args, 0))
         if (a0%tag == GCT_REAL) then
            out = a0
         else if (a0%tag == GCT_INT) then
            out = gc_real(real(a0%ival, gc_dp))
         else
            t = trim(adjustl(text_of(a0)))
            read(t, *, iostat=st) dv
            if (st /= 0) then
               call fail_as("NumberFormatException", "valueOf: not a number: " // t, &
                    [vs_get(base + 1)])
            else
               out = gc_real(dv)
            end if
         end if
       end block
    case (B_ISNAN)
       ! NaN is the one value not equal to itself, which is the test
       ! that needs no ieee_arithmetic import to be right.
       block
         type(gc_value) :: a0
         real(gc_dp) :: dv
         a0 = strip_meta(gcv_nth(args, 0))
         dv = num_dbl(a0)
         out = gc_bool(a0%tag == GCT_REAL .and. dv /= dv)
       end block
    case (B_ISINF)
       block
         type(gc_value) :: a0
         real(gc_dp) :: dv
         a0 = strip_meta(gcv_nth(args, 0))
         dv = num_dbl(a0)
         ! Ordered comparison excludes NaN, which is neither infinite
         ! nor finite and must answer false here.
         out = gc_bool(a0%tag == GCT_REAL .and. dv == dv .and. &
              abs(dv) > huge(1.0_gc_dp))
       end block
    case (B_DBLCAST)
       out = gc_real(num_dbl(gcv_nth(args, 0)))
    case (B_BOOLCAST)
       out = gc_bool(truthy(gcv_nth(args, 0)))
    case (B_CHARCAST)
       a = gcv_nth(args, 0)
       if (a%tag == GCT_CHAR) then
          out = a
       else
          out = gc_char(achar(a%ival))
       end if
    case (B_ALTERMETA)
       block
         type(gc_value) :: ref, fargs, extra
         integer :: j
         ref = gcv_nth(args, 0)
         call vs_set(base + 2, ref)
         fargs = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
         fargs = gcv_conj(fargs, gc_slot(vs_get(base + 2), meta_slot(vs_get(base + 2))), &
              [vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, fargs)
         extra = coll_to_vector(gcv_nth(args, 2), [vs_get(base + 1), vs_get(base + 3)])
         fargs = vs_get(base + 3)
         do j = 0, gcv_count(extra) - 1
            fargs = gcv_conj(fargs, gcv_nth(extra, j), [vs_get(base + 1), extra])
            call vs_set(base + 3, fargs)
         end do
         out = apply(gcv_nth(args, 1), vs_get(base + 3))
         if (.not. has_error) then
            call gc_set_slot(vs_get(base + 2), meta_slot(vs_get(base + 2)), out)
         end if
       end block
    case (B_FINDNS)
       a = strip_meta(gcv_nth(args, 0))
       out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(base + 1)])
    case (B_LOADFILE)
       ! Read the whole file, then analyse and evaluate each form. The
       ! first error ends it, as Compiler.load does.
       block
         character(len=:), allocatable :: path, text
         type(gc_value) :: forms, genv, f
         integer :: u, st, fsize, j, fid
         logical :: eof
         out = gc_nil()
         path = text_of(gcv_nth(args, 0))
         open(newunit=u, file=path, access="stream", form="unformatted", &
              status="old", action="read", iostat=st)
         if (st /= 0) then
            call fail("load-file: cannot open " // path)
         else
            inquire(unit=u, size=fsize)
            allocate(character(len=fsize) :: text)
            read(u, iostat=st) text
            close(u)
            if (gc_root_live(global_env_root)) then
               genv = gc_root_get(global_env_root)
            else
               genv = gc_nil()
            end if
            call vs_set(base + 2, genv)
            ! one form at a time, as main.f90's load_file and Compiler.load
            fid = gcr_begin_file(text, path)
            j = 1
            do
               forms = gcr_read_next(text, j, [vs_get(base + 1), vs_get(base + 2)], eof, fid)
               if (gcr_has_error()) then
                  call fail("load-file " // path // ": " // gcr_error())
                  exit
               end if
               if (eof) exit
               call vs_set(base + 3, forms)
               f = gce_analyze(vs_get(base + 3), vs_get(base + 2))
               if (has_error) exit
               out = gce_eval(f, vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3)])
               if (has_error) exit
            end do
         end if
       end block
    case (B_ENDSWITH)
       block
         character(len=:), allocatable :: hay, ned
         hay = text_of(gcv_nth(args, 0))
         ned = text_of(gcv_nth(args, 1))
         if (len(ned) > len(hay)) then
            out = gc_bool(.false.)
         else
            out = gc_bool(hay(len(hay)-len(ned)+1:) == ned)
         end if
       end block
    case (B_REPLACE)
       ! String.replace with char or string arguments, every occurrence.
       block
         character(len=:), allocatable :: t, frm, too, acc
         integer :: at
         t = text_of(gcv_nth(args, 0))
         frm = text_of(gcv_nth(args, 1))
         too = text_of(gcv_nth(args, 2))
         acc = ""
         do
            if (len(frm) == 0) exit
            at = index(t, frm)
            if (at == 0) exit
            acc = acc // t(1:at-1) // too
            t = t(at+len(frm):)
         end do
         out = gc_str(acc // t, [vs_get(base + 1)])
       end block
    case (B_STARTSWITH)
       block
         character(len=:), allocatable :: hay, ned
         hay = text_of(gcv_nth(args, 0))
         ned = text_of(gcv_nth(args, 1))
         if (len(ned) > len(hay)) then
            out = gc_bool(.false.)
         else
            out = gc_bool(hay(1:len(ned)) == ned)
         end if
       end block
    case (B_STRLEN)
       block
         type(gc_value) :: cv
         cv = strip_meta(gcv_nth(args, 0))
         if (cv%tag == GCT_STR) then
            out = gc_int(len(gc_ref_text(cv%ref)))
         else
            out = gc_int(sq_count(cv, [vs_get(base + 1)]))
         end if
       end block
    case (B_SUBSTRING)
       block
         character(len=:), allocatable :: t
         type(gc_value) :: iv
         integer :: lo, hi
         t = text_of(gcv_nth(args, 0))
         iv = gcv_nth(args, 1)
         lo = int(iv%ival)
         hi = len(t)
         if (n >= 3) then
            iv = gcv_nth(args, 2)
            hi = int(iv%ival)
         end if
         out = gc_str(t(lo+1:hi), [vs_get(base + 1)])
       end block
    case (B_ISPUBLIC, B_ISMACRO)
       ! Both read the Var's metadata, which is where Clojure keeps
       ! them: :private and :macro.
       block
         type(gc_value) :: md2
         a = strip_meta(gcv_nth(args, 0))
         md2 = gc_nil()
         if (gcn_is_var(a)) md2 = gc_slot(a, 2)
         if (id == B_ISMACRO) then
            out = gc_bool(truthy(gca_get(md2, gc_key("macro", [vs_get(base + 1)]))))
         else
            out = gc_bool(.not. truthy(gca_get(md2, &
                 gc_key("private", [vs_get(base + 1)]))))
         end if
       end block
    case (B_SETMACRO)
       a = strip_meta(gcv_nth(args, 0))
       call var_set_macro(a)
       out = gc_nil()
    case (B_DOTGET)
       if (n >= 2) then
          out = gca_get(strip_meta(gcv_nth(args, 0)), gcv_nth(args, 1))
       else
          a = strip_meta(gcv_nth(args, 0))
          if (gcn_is_var(a) .or. gc_kind(a) == OBJ_ATOM) then
             out = gc_slot(a, 1)
          else
             out = a
          end if
       end if
    case (B_GENIFACE)
       out = gc_nil()
    case (B_ALWAYS_FALSE)
       out = gc_bool(.false.)
    case (B_EMPTYVEC)
       out = gcv_empty([vs_get(base + 1)])
    case (B_RE_COMPILE)
       ! re-pattern's own definition already guards against re-compiling
       ! a Pattern (instance? checks first), so by the time this runs
       ! args(0) is always a plain string.
       block
         type(gc_value) :: src, pv
         character(len=:), allocatable :: ptext
         integer :: h
         src = strip_meta(gcv_nth(args, 0))
         ptext = text_of(src)
         h = regex_compile(ptext)
         if (h == 0) then
            call fail("regex: " // regex_last_error())
         else
            pv = gc_obj(OBJ_REGEX, [gc_str(ptext, [vs_get(base + 1)])], [vs_get(base + 1)])
            call gc_set_i1(pv, h)
            out = pv
         end if
       end block
    case (B_RE_MATCHER)
       ! Pattern.matcher(s) -- an INDEPENDENT clone of the pattern's own
       ! handle, so this matcher's search position never collides with
       ! another matcher built from the same Pattern. See Regex.f90.
       block
         type(gc_value) :: pat, subj, mv
         character(len=:), allocatable :: stext
         integer :: ph, mh
         pat = strip_meta(gcv_nth(args, 0))
         subj = strip_meta(gcv_nth(args, 1))
         out = gc_nil()
         if (gc_kind(pat) /= OBJ_REGEX) then
            call fail("matcher needs a Pattern")
         else
            ph = gc_i1(pat)
            mh = regex_clone(ph)
            if (mh == 0) then
               call fail("regex: " // regex_last_error())
            else
               stext = text_of(subj)
               if (.not. regex_set_text(mh, stext)) then
                  call fail("regex: " // regex_last_error())
               else
                  mv = gc_obj(OBJ_MATCHER, [pat, gc_str(stext, [vs_get(base + 1), pat])], &
                       [vs_get(base + 1), pat])
                  call gc_set_i1(mv, mh)
                  out = mv
               end if
            end if
         end if
       end block
    case (B_RE_FIND, B_RE_MATCHES)
       ! Matcher.find() / Matcher.matches() -- both boolean, both
       ! advancing/consulting the SAME ICU handle's internal state,
       ! which is exactly what uregex_findNext and uregex_matches
       ! already track (see regex_shim.h). Neither takes an argument.
       block
         type(gc_value) :: mt
         integer :: mh, r
         mt = strip_meta(gcv_nth(args, 0))
         out = gc_bool(.false.)
         if (gc_kind(mt) == OBJ_MATCHER) then
            mh = gc_i1(mt)
            if (id == B_RE_FIND) then
               r = regex_find_next(mh)
            else
               r = regex_matches(mh)
            end if
            out = gc_bool(r == 1)
         end if
       end block
    case (B_ISWS, B_ISLOWER, B_ISDIGIT, B_ISLETTER, B_ISALNUM)
       block
         type(gc_value) :: cv
         character :: c
         cv = strip_meta(gcv_nth(args, 0))
         c = achar(max(0, min(255, cv%ival)))
         select case (id)
         case (B_ISWS)
            out = gc_bool(c == " " .or. c == achar(9) .or. c == achar(10) &
                 .or. c == achar(13) .or. c == achar(12))
         case (B_ISLOWER); out = gc_bool(c >= "a" .and. c <= "z")
         case (B_ISDIGIT); out = gc_bool(c >= "0" .and. c <= "9")
         case (B_ISLETTER)
            out = gc_bool((c >= "A" .and. c <= "Z") .or. (c >= "a" .and. c <= "z"))
         case (B_ISALNUM)
            out = gc_bool((c >= "A" .and. c <= "Z") .or. (c >= "a" .and. c <= "z") &
                 .or. (c >= "0" .and. c <= "9"))
         end select
       end block
    case (B_UPCASE, B_DOWNCASE)
       ! A character or a whole string: Character/toUpperCase and
       ! String.toUpperCase are the same fold either way. ASCII only,
       ! as everything else here is -- DEVIATIONS 14.
       block
         type(gc_value) :: v
         character(len=:), allocatable :: t
         integer :: j, d
         logical :: up
         up = (id == B_UPCASE)
         v = strip_meta(gcv_nth(args, 0))
         if (v%tag == GCT_CHAR) then
            t = achar(max(0, min(255, v%ival)))
         else
            t = text_of(v)
         end if
         do j = 1, len(t)
            d = iachar(t(j:j))
            if (up .and. d >= 97 .and. d <= 122) t(j:j) = achar(d - 32)
            if (.not. up .and. d >= 65 .and. d <= 90) t(j:j) = achar(d + 32)
         end do
         if (v%tag == GCT_CHAR) then
            out = gc_char(t(1:1))
         else
            out = gc_str(t, [vs_get(base + 1)])
         end if
       end block
    case (B_CHARAT)
       ! core_print escapes a string one character at a time, which is
       ! the only reason pr quotes anything.
       block
         type(gc_value) :: sv, iv
         character(len=:), allocatable :: t
         sv = strip_meta(gcv_nth(args, 0))
         iv = strip_meta(gcv_nth(args, 1))
         out = gc_nil()
         t = text_of(sv)
         if (iv%tag == GCT_INT) then
            if (iv%ival >= 0 .and. iv%ival < len(t)) out = gc_char(t(iv%ival + 1:iv%ival + 1))
         end if
       end block
    case (B_WRITE)
       ! (.write w s). A char writes as itself, and so does an INTEGER:
       ! Writer.write(int) takes a code point, which is how the column
       ! writer under pprint hands a newline down. (StringBuilder.append
       ! of an int is its digits; that is B_APPEND, not this.)
       block
         type(gc_value) :: w, x
         character(len=:), allocatable :: piece
         w = strip_meta(gcv_nth(args, 0))
         x = strip_meta(gcv_nth(args, 1))
         if (x%tag == GCT_INT .and. x%ival >= 0 .and. x%ival < 128) then
            ! ponytail: ASCII only; a code point past 127 still prints as digits.
            piece = achar(int(x%ival))
         else
            piece = text_of(x)
         end if
         if (gc_kind(w) == OBJ_WRITER) then
            write(gc_i1(w), '(A)', advance='no') piece
         else if (gc_kind(w) == OBJ_SB) then
            call gc_set_slot(w, 1, gc_str(text_of(gc_slot(w, 1)) // piece, [vs_get(base + 1)]))
         end if
         out = gc_nil()
       end block
    case (B_FLUSH)
       block
         type(gc_value) :: w
         w = strip_meta(gcv_nth(args, 0))
         if (gc_kind(w) == OBJ_WRITER) flush(gc_i1(w))
         out = gc_nil()
       end block
    case (B_BASELOADER)
       ! the classpath root beside the binary, so getResourceAsStream
       ! finds clojure/version.properties from any directory
       out = gc_str(gce_home() // "/src/clj", [vs_get(base + 1)])
    case (B_RESOURCE)
       ! Java answers null for a resource that is not there, and
       ! with-open then fails on the nil -- same shape either way.
       block
         character(len=:), allocatable :: path, text
         integer :: u, st, fsize
         out = gc_nil()
         path = text_of(gcv_nth(args, 0)) // "/" // text_of(gcv_nth(args, 1))
         open(newunit=u, file=path, access="stream", form="unformatted", &
              status="old", action="read", iostat=st)
         if (st == 0) then
            inquire(unit=u, size=fsize)
            allocate(character(len=fsize) :: text)
            read(u, iostat=st) text
            close(u)
            out = gc_str(text, [vs_get(base + 1)])
         end if
       end block
    case (B_PROPLOAD)
       ! java.util.Properties.load: key=value a line, # and ! comment.
       !
       ! Its own frame, because the key and the value are two separate
       ! allocations and BOTH must be on the shadow stack before the
       ! assoc: passing them straight as arguments lets the second
       ! allocation collect the first. Torture mode caught exactly that.
       block
         character(len=:), allocatable :: txt, ln
         type(gc_value) :: m, kk, vv
         integer :: lb, p0, p1, eq
         lb = vs_enter(4)
         call vs_set(lb + 1, strip_meta(gcv_nth(args, 0)))
         txt = text_of(gcv_nth(args, 1))
         m = gca_empty([vs_get(lb + 1)])
         call vs_set(lb + 2, m)
         p0 = 1
         do while (p0 <= len(txt))
            p1 = index(txt(p0:), new_line('a'))
            if (p1 == 0) then
               p1 = len(txt) + 1
            else
               p1 = p0 + p1 - 1
            end if
            ln = trim(adjustl(txt(p0:p1 - 1)))
            if (len(ln) > 0) then
               if (ln(1:1) /= "#" .and. ln(1:1) /= "!") then
                  eq = index(ln, "=")
                  if (eq > 1) then
                     kk = gc_str(trim(ln(1:eq - 1)), &
                          [vs_get(lb + 1), vs_get(lb + 2)])
                     call vs_set(lb + 3, kk)
                     vv = gc_str(trim(adjustl(ln(eq + 1:))), &
                          [vs_get(lb + 1), vs_get(lb + 2), vs_get(lb + 3)])
                     call vs_set(lb + 4, vv)
                     m = gca_assoc(vs_get(lb + 2), vs_get(lb + 3), vs_get(lb + 4), &
                          [vs_get(lb + 1), vs_get(lb + 2), vs_get(lb + 3), vs_get(lb + 4)])
                     call vs_set(lb + 2, m)
                  end if
               end if
            end if
            p0 = p1 + 1
         end do
         call gc_set_slot(vs_get(lb + 1), 1, vs_get(lb + 2))
         call vs_leave(lb)
         out = gc_nil()
       end block
    case (B_PROPGET)
       block
         type(gc_value) :: props
         props = strip_meta(gcv_nth(args, 0))
         out = gca_get(gc_slot(props, 1), gcv_nth(args, 1))
       end block
    case (B_CLOSE)
       out = gc_nil()
    case (B_INTVALUE)
       block
         type(gc_value) :: a0
         character(len=:), allocatable :: t
         integer :: iv, st
         a0 = strip_meta(gcv_nth(args, 0))
         if (a0%tag == GCT_INT) then
            out = a0
         else
            t = trim(adjustl(text_of(a0)))
            read(t, *, iostat=st) iv
            if (st /= 0) then
               call fail_as("NumberFormatException", "valueOf: not a number: " // t, &
                    [vs_get(base + 1)])
            else
               out = gc_int(iv)
            end if
         end if
       end block
    case (B_STRCONTAINS)
       block
         type(gc_value) :: coll, ckey
         coll = strip_meta(gcv_nth(args, 0))
         ! TWO METHODS SHARE THIS NAME and they ask different
         ! questions. String.contains(s) is substring containment;
         ! RT.contains(coll, key) is whether the KEY is present,
         ! which for a string means the index is in range. The
         ! argument tells them apart -- a string key is the
         ! substring question, an integer key the index one --
         ! and conflating them made (contains? "ab" 0) false.
         ckey = strip_meta(gcv_nth(args, 1))
         if (coll%tag == GCT_STR .and. ckey%tag /= GCT_INT) then
            out = gc_bool(index(text_of(coll), text_of(gcv_nth(args, 1))) > 0)
         else if (gc_kind(coll) == OBJ_INST) then
            ! THE path contains? takes: core.clj's contains? is
            ! (. clojure.lang.RT (contains coll key)), which lands
            ! here rather than on the contains? builtin.
            out = inst_invoke(coll, "containsKey", rest_args(args, 1), hit)
            if (.not. hit) out = gc_bool(coll_has(coll, gcv_nth(args, 1)))
         else
            out = gc_bool(coll_has(coll, gcv_nth(args, 1)))
         end if
       end block
    case (B_HASH)
       out = gc_int(gc_hash(gcv_nth(args, 0)))
    case (B_RE_GROUPCOUNT)
       block
         type(gc_value) :: mt
         mt = strip_meta(gcv_nth(args, 0))
         out = gc_int(0)
         if (gc_kind(mt) == OBJ_MATCHER) out = gc_int(max(0, regex_group_count(gc_i1(mt))))
       end block
    case (B_RE_GROUP)
       ! (.group) is group 0 (the whole match); (.group n) is group n.
       ! A group that exists but did not participate answers nil, same
       ! as Java's Matcher.group(n) returning null -- an optional group
       ! inside an alternation that did not fire.
       block
         type(gc_value) :: mt, iv, subj
         character(len=:), allocatable :: stext
         integer :: mh, gnum, gstart, gend
         logical :: participated
         mt = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gc_kind(mt) == OBJ_MATCHER) then
            mh = gc_i1(mt)
            gnum = 0
            if (n >= 2) then
               iv = gcv_nth(args, 1)
               gnum = int(iv%ival)
            end if
            participated = regex_group_span(mh, gnum, gstart, gend)
            if (participated) then
               subj = gc_slot(mt, 2)
               stext = text_of(subj)
               out = gc_str(stext(gstart+1:gend), [vs_get(base + 1)])
            end if
         end if
       end block
    case (B_ISREDUCED)
       out = gc_bool(gca_contains(strip_meta(gcv_nth(args, 0)), &
            gc_key("clotran/reduced", [vs_get(base + 1)])))
    case (B_FLD_SYM, B_FLD_PROTOCOL, B_FLD_METHODK, B_FLD_MAP)
       ! (.field x) on a map-shaped host object: the field name IS
       ! a keyword in the map.
       block
         character(len=10) :: fk
         select case (id)
         case (B_FLD_SYM)
            ! .sym on a VAR is its name, not a map field -- and that is
            ! how a protocol names its method: (keyword (.sym v)).
            block
              type(gc_value) :: tv2
              tv2 = strip_meta(gcv_nth(args, 0))
              if (gcn_is_var(tv2)) then
                 out = gc_slot(tv2, 4)
                 call vs_leave(base)
                 return
              end if
            end block
            fk = "sym"
         case (B_FLD_PROTOCOL); fk = "protocol"
         case (B_FLD_METHODK);  fk = "methodk"
         case default;          fk = "map"
         end select
         out = gca_get(strip_meta(gcv_nth(args, 0)), &
              gc_key(trim(fk), [vs_get(base + 1)]))
       end block
    case (B_FLD_CACHE)
       ! A protocol function carries its dispatch cache on ITSELF --
       ! (set! (.__methodImplCache f) cache) in emit-method-builder --
       ! and slot 5 is where it goes. See OBJ_SLOTS in GC.f90.
       block
         type(gc_value) :: fv
         fv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gc_kind(fv) == OBJ_CLOSURE) out = gc_slot(fv, 5)
       end block
    case (B_VARSYM)
       block
         type(gc_value) :: vv, nm2
         vv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gcn_is_var(vv)) then
            nm2 = gc_slot(vv, 4)
            out = gc_sym(gcn_name(gc_slot(vv, 3)) // "/" // name_part(nm2), &
                 [vs_get(base + 1)])
         end if
       end block
    case (B_VARINTERN)
       ! (Var/intern ns sym) leaves the Var unbound; with a third
       ! argument it binds the root, which is the hasRoot flag too.
       block
         type(gc_value) :: nsv, sym2, val2, var2
         nsv = strip_meta(gcv_nth(args, 0))
         sym2 = strip_meta(gcv_nth(args, 1))
         val2 = gc_nil()
         if (n >= 3) val2 = gcv_nth(args, 2)
         call vs_set(base + 2, nsv)
         call vs_set(base + 3, sym2)
         var2 = gcn_intern(vs_get(base + 2), vs_get(base + 3), val2, &
              [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
         if (n >= 3) call gc_set_i1(var2, 1)
         out = var2
       end block
    case (B_FORNAME)
       ! There are no Java classes, so Class/forName THROWS -- which
       ! is the honest answer and also the useful one: core.clj's
       ! when-class catches ClassNotFoundException and skips the
       ! body, so (when-class "java.sql.Timestamp" (load "instant"))
       ! skips itself without clotran naming instant at all.
       block
         type(gc_value) :: exc
         exc = gc_obj(OBJ_ERR, &
              [gc_sym("ClassNotFoundException", [vs_get(base + 1)]), &
               gcv_nth(args, 0), gc_nil()], [vs_get(base + 1)])
         call vs_set(base + 2, exc)
         call set_thrown(vs_get(base + 2))
         has_error = .true.
         last_error = gcp_str(vs_get(base + 2), .true.)
         out = gc_nil()
       end block
    case (B_TOARRAY)
       ! A REAL array, not a vector. That comment used to say every
       ! use fed straight back into a seq, which was true until
       ! `sort`: it is (let [a (to-array coll)] (. Arrays (sort a cmp))
       ! (seq a)) -- the array is sorted IN PLACE and then read back,
       ! and a persistent vector cannot be mutated.
       out = value_array_of(gcv_nth(args, 0), [vs_get(base + 1)])
    case (B_ITERATE)
       ! (iterate f x) -- x, (f x), (f (f x)) ... unbounded, so a
       ! LAZY cell whose thunk is built by the evaluator. Realised
       ! head, unrealised tail: exactly what lazy-seq produces.
       out = iterate_cell(gcv_nth(args, 0), gcv_nth(args, 1), &
            [vs_get(base + 1)])
    case (B_CYCLE)
       ! (cycle coll) repeats it forever. Built by hand as a ring:
       ! the last cell'"s tail is the first cell, so the whole thing
       ! is O(n) in the collection and infinite to walk.
       block
         type(gc_value) :: items, cell, prev, firstc
         integer :: j, cn
         items = coll_to_vector(gcv_nth(args, 0), [vs_get(base + 1)])
         call vs_set(base + 2, items)
         cn = gcv_count(vs_get(base + 2))
         out = gc_nil()
         if (cn > 0) then
            firstc = gc_nil()
            prev = gc_nil()
            do j = 0, cn - 1
               cell = gc_obj(OBJ_LAZY, [gc_nil(), &
                    gcv_nth(vs_get(base + 2), j), gc_nil()], &
                    [vs_get(base + 1), vs_get(base + 2)])
               call gc_set_i1(cell, LAZY_CONS)
               if (j == 0) then
                  firstc = cell
                  call vs_set(base + 3, firstc)
               else
                  call gc_set_slot(prev, 3, cell)
               end if
               prev = cell
            end do
            call gc_set_slot(prev, 3, vs_get(base + 3))
            out = vs_get(base + 3)
         end if
       end block
    case (B_REPEAT)
       ! (repeat x) is INFINITE, and here that is a single realised cons
       ! cell whose tail is itself -- O(1) space, and every `first` and
       ! `rest` of it answers correctly forever. (repeat n x) is finite
       ! and ordinary.
       if (n >= 2) then
          block
            type(gc_value) :: acc, iv
            integer :: j, cnt
            iv = gcv_nth(args, 0)
            cnt = int(iv%ival)
            acc = gcl_empty([vs_get(base + 1)])
            call vs_set(base + 2, acc)
            do j = 1, cnt
               acc = gcl_cons(gcv_nth(args, 1), vs_get(base + 2), [vs_get(base + 1)])
               call vs_set(base + 2, acc)
            end do
            out = vs_get(base + 2)
          end block
       else
          out = gc_obj(OBJ_LAZY, [gc_nil(), gcv_nth(args, 0), gc_nil()], &
               [vs_get(base + 1)])
          call gc_set_i1(out, LAZY_CONS)
          call gc_set_slot(out, 3, out)
       end if
    case (B_RANGE)
       ! (range end), (range start end) and (range start end step), the
       ! three arities Range/create has. LAZY -- see range_cell.
       block
         type(gc_value) :: lo, hi, stp
         lo = gc_int(0)
         stp = gc_int(1)
         hi = strip_meta(gcv_nth(args, 0))
         if (n >= 2) then
            lo = hi
            hi = strip_meta(gcv_nth(args, 1))
         end if
         if (n >= 3) stp = strip_meta(gcv_nth(args, 2))
         if (.not. (is_number(lo) .and. is_number(hi) .and. is_number(stp))) then
                 call fail("range: not a number")
         else
            out = range_cell(lo, hi, stp, [vs_get(base + 1)])
         end if
       end block
    case (B_RUNTX)
       out = apply(gcv_nth(args, 0), gcv_empty([vs_get(base + 1)]))
    case (B_VARNS)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gcn_is_var(a)) out = gc_slot(a, 3)
    case (B_NSMAP, B_NSALIASES)
       block
         type(gc_value) :: nsv
         integer :: slot
         nsv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gc_kind(nsv) == OBJ_NS) then
            if (id == B_NSMAP) then
               slot = 2
            else
               slot = 3
            end if
            out = gc_slot(nsv, slot)
            if (.not. gca_is(out)) out = gca_empty([vs_get(base + 1)])
         end if
       end block
    case (B_NSADDALIAS)
       ! (.addAlias ns sym other-ns) -- slot 3, the alias map, which
       ! resolve_var consults before treating a prefix as a namespace
       ! name of its own. refer, which shared this case, writes slot 2:
       ! a Var under a name, not a NAMESPACE under a name. Sharing them
       ! put every :as alias into the bindings map, where nothing looks.
       block
         type(gc_value) :: nsv, m
         nsv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gc_kind(nsv) == OBJ_NS) then
            call vs_set(base + 2, nsv)
            m = gc_slot(vs_get(base + 2), 3)
            if (.not. gca_is(m)) m = gca_empty([vs_get(base + 1)])
            call vs_set(base + 3, m)
            m = gca_assoc(vs_get(base + 3), strip_meta(gcv_nth(args, 1)), &
                 gcv_nth(args, 2), &
                 [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
            call gc_set_slot(vs_get(base + 2), 3, m)
         end if
       end block
    case (B_NSREFER)
       ! (.refer ns sym var) puts an existing Var under a name in
       ! another namespace -- which is all refer is. addAlias is the
       ! same operation on slot 3.
       block
         type(gc_value) :: nsv, m
         nsv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gc_kind(nsv) == OBJ_NS) then
            call vs_set(base + 2, nsv)
            m = gc_slot(vs_get(base + 2), 2)
            if (.not. gca_is(m)) m = gca_empty([vs_get(base + 1)])
            m = gca_assoc(m, strip_meta(gcv_nth(args, 1)), gcv_nth(args, 2), &
                 [vs_get(base + 1), vs_get(base + 2)])
            call gc_set_slot(vs_get(base + 2), 2, m)
            out = vs_get(base + 2)
         end if
       end block
    case (B_MAYBERESOLVE)
       block
         type(gc_value) :: sym2
         sym2 = strip_meta(gcv_nth(args, n - 1))
         out = gc_nil()
         if (sym2%tag == GCT_SYM) out = resolve_var(sym2, vs_get(base + 1))
       end block
    case (B_POP, B_PEEK)
       ! Both work at the END of a vector and the FRONT of a list --
       ! the end a conj would touch, which is what makes a vector a
       ! stack and a list a stack too, at opposite ends.
       block
         type(gc_value) :: coll, acc
         integer :: j, cn
         coll = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gcv_is(coll)) then
            cn = gcv_count(coll)
            if (id == B_PEEK) then
               if (cn > 0) out = gcv_nth(coll, cn - 1)
            else
               acc = gcv_empty([vs_get(base + 1)])
               call vs_set(base + 2, acc)
               do j = 0, cn - 2
                  acc = gcv_conj(vs_get(base + 2), gcv_nth(coll, j), &
                       [vs_get(base + 1), vs_get(base + 2)])
                  call vs_set(base + 2, acc)
               end do
               out = vs_get(base + 2)
            end if
         else if (coll%tag /= GCT_NIL) then
            if (id == B_PEEK) then
               out = sq_first(coll, [vs_get(base + 1)])
            else
               out = sq_rest(coll, [vs_get(base + 1)])
            end if
         end if
       end block
    case (B_NAMESPACE)
       ! The qualifier of a qualified symbol or keyword, nil otherwise.
       block
         character(len=:), allocatable :: t
         integer :: sl
         out = gc_nil()
         a = strip_meta(gcv_nth(args, 0))
         if (a%tag == GCT_SYM .or. a%tag == GCT_KEY) then
            t = gc_ref_text(a%ref)
            sl = index(t, "/")
            if (sl > 1) out = gc_str(t(1:sl-1), [vs_get(base + 1)])
         end if
       end block
    case (B_KEY, B_VAL)
       block
         type(gc_value) :: e
         e = strip_meta(gcv_nth(args, 0))
         if (id == B_KEY) then
            out = seq_elem(e, 0, [vs_get(base + 1)])
         else
            out = seq_elem(e, 1, [vs_get(base + 1)])
         end if
       end block
    case (B_CONTAINS)
       block
         type(gc_value) :: coll
         coll = strip_meta(gcv_nth(args, 0))
         if (gc_kind(coll) == OBJ_INST) then
            out = inst_invoke(coll, "containsKey", rest_args(args, 1), hit)
            if (hit) then
             call vs_leave(base)
             return
          end if
         end if
         out = gc_bool(coll_has(coll, gcv_nth(args, 1)))
       end block
    case (B_FIND)
       ! A map entry is a two-element vector, which is what makes
       ! (key e) and (val e) plain nth calls.
       block
         type(gc_value) :: coll, pair
         coll = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gca_contains(coll, gcv_nth(args, 1))) then
            pair = gcv_empty([vs_get(base + 1)])
            pair = gcv_conj(pair, gcv_nth(args, 1), [vs_get(base + 1)])
            call vs_set(base + 2, pair)
            pair = gcv_conj(vs_get(base + 2), gca_get(coll, gcv_nth(args, 1)), &
                 [vs_get(base + 1), vs_get(base + 2)])
            out = pair
         end if
       end block
    case (B_SETVAL, B_RESETVALS)
       a = gcv_nth(args, 0)
       out = gcv_nth(args, 1)
       block
         type(gc_value) :: prev
         ! THE VALIDATOR RUNS BEFORE THE WRITE, and a refusal
         ! leaves the reference alone -- which is the whole point
         ! of set-validator!.
         if (.not. validate_ref(a, ref_fn_get(a, "validator", [vs_get(base + 1)]), &
              out, [vs_get(base + 1)])) then
            call vs_leave(base)
            return
         end if
         prev = gc_slot(a, 1)
         call gc_set_slot(a, 1, out)
         if (id == B_RESETVALS) out = value_pair(prev, out, [a, args])
       end block
    case (B_SWAPVAL, B_SWAPVALS)
       ! IAtom has FOUR swap arities: (f), (f x), (f x y) and
       ! (f x y argseq). Only the last passes a seq; the middle two pass
       ! plain values. This used to share alter's builtin, whose shape is
       ! (.alter ref f argseq) with the seq at index 2 -- so
       ! (swap! a conj 1) called (conj @a) with no 1 at all, and
       ! answered the unchanged value instead of erroring. Every
       ! (swap! acc conj x) in the tree silently did nothing.
       block
         type(gc_value) :: fargs
         integer :: lb, j
         lb = vs_enter(3)
         call vs_set(lb + 1, strip_meta(gcv_nth(args, 0)))
         fargs = gcv_empty([vs_get(lb + 1)])
         fargs = gcv_conj(fargs, gc_slot(vs_get(lb + 1), 1), [vs_get(lb + 1)])
         call vs_set(lb + 2, fargs)
         ! indices 2 and 3 are values
         do j = 2, min(n, 4) - 1
            fargs = gcv_conj(vs_get(lb + 2), gcv_nth(args, j), &
                 [vs_get(lb + 1), vs_get(lb + 2)])
            call vs_set(lb + 2, fargs)
         end do
         ! index 4, when present, is a seq to splice
         if (n >= 5) then
            call vs_set(lb + 3, coll_to_vector(gcv_nth(args, 4), &
                 [vs_get(lb + 1), vs_get(lb + 2)]))
            do j = 0, gcv_count(vs_get(lb + 3)) - 1
               fargs = gcv_conj(vs_get(lb + 2), gcv_nth(vs_get(lb + 3), j), &
                    [vs_get(lb + 1), vs_get(lb + 2), vs_get(lb + 3)])
               call vs_set(lb + 2, fargs)
            end do
         end if
         out = apply(gcv_nth(args, 1), vs_get(lb + 2))
         if (.not. has_error) then
            if (.not. validate_ref(vs_get(lb + 1), &
                 ref_fn_get(vs_get(lb + 1), "validator", [vs_get(lb + 1)]), &
                 out, [vs_get(lb + 1)])) then
               call vs_leave(lb)
               call vs_leave(base)
               return
            end if
            if (id == B_SWAPVALS) then
               out = value_pair(gc_slot(vs_get(lb + 1), 1), out, &
                    [vs_get(lb + 1), vs_get(lb + 2)])
               call gc_set_slot(vs_get(lb + 1), 1, gcv_nth(out, 1))
            else
               call gc_set_slot(vs_get(lb + 1), 1, out)
            end if
         end if
         call vs_leave(lb)
       end block
    case (B_ALTERVAL)
       ! (.alter ref f args) is (apply f @ref args), stored back.
       block
         type(gc_value) :: ref, fargs, extra
         integer :: j
         ref = gcv_nth(args, 0)
         call vs_set(base + 2, ref)
         fargs = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
         fargs = gcv_conj(fargs, gc_slot(vs_get(base + 2), 1), &
              [vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, fargs)
         if (n >= 3) then
            extra = coll_to_vector(gcv_nth(args, 2), [vs_get(base + 1), vs_get(base + 3)])
            fargs = vs_get(base + 3)
            do j = 0, gcv_count(extra) - 1
               fargs = gcv_conj(fargs, gcv_nth(extra, j), [vs_get(base + 1), extra])
               call vs_set(base + 3, fargs)
            end do
         end if
         out = apply(gcv_nth(args, 1), vs_get(base + 3))
         if (.not. has_error) call gc_set_slot(vs_get(base + 2), 1, out)
       end block
    case (B_RESETMETA)
       a = gcv_nth(args, 0)
       out = gcv_nth(args, 1)
       call gc_set_slot(a, meta_slot(a), out)
    case (B_EVAL)
       ! Analyse then evaluate, the same two halves load does. definline
       ! calls this at macroexpansion time to fold its body.
       block
         type(gc_value) :: genv, form
         if (gc_root_live(global_env_root)) then
            genv = gc_root_get(global_env_root)
         else
            genv = gc_nil()
         end if
         call vs_set(base + 2, genv)
         form = gce_analyze(gcv_nth(args, 0), vs_get(base + 2))
         call vs_set(base + 3, form)
         if (.not. has_error) &
              out = gce_eval(vs_get(base + 3), vs_get(base + 2), [vs_get(base + 1)])
       end block
    case (B_ALWAYS_NIL)
       out = gc_nil()
    case (B_PUSHTB)
       ! Save each Var's current root, then install the new value. The
       ! saved map goes on the stack for popThreadBindings.
       block
         type(gc_value) :: m, saved, stack
         type(gc_value), allocatable :: kk(:), vv(:)
         integer :: j
         m = strip_meta(gcv_nth(args, 0))
         call vs_set(base + 2, m)
         call gca_entries(vs_get(base + 2), kk, vv)
         saved = gca_empty([vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, saved)
         do j = 1, size(kk)
            if (gcn_is_var(kk(j))) then
               saved = gca_assoc(vs_get(base + 3), kk(j), gc_slot(kk(j), 1), &
                    [vs_get(base + 1), vs_get(base + 3)])
               call vs_set(base + 3, saved)
               call gc_set_slot(kk(j), 1, vv(j))
            end if
         end do
         if (gc_root_live(binding_stack_root)) then
            stack = gc_root_get(binding_stack_root)
         else
            stack = gcl_empty([vs_get(base + 3)])
         end if
         stack = gcl_cons(vs_get(base + 3), stack, [vs_get(base + 3), stack])
         call gc_global_keep(binding_stack_root, stack)
         out = gc_nil()
       end block
    case (B_POPTB)
       block
         type(gc_value) :: stack, frame
         type(gc_value), allocatable :: kk(:), vv(:)
         integer :: j
         out = gc_nil()
         if (gc_root_live(binding_stack_root)) then
            stack = gc_root_get(binding_stack_root)
            call vs_set(base + 2, stack)
            if (gcl_count(vs_get(base + 2)) > 0) then
               frame = gcl_first(vs_get(base + 2))
               call vs_set(base + 3, frame)
               call gca_entries(vs_get(base + 3), kk, vv)
               do j = 1, size(kk)
                  if (gcn_is_var(kk(j))) call gc_set_slot(kk(j), 1, vv(j))
               end do
               call gc_global_keep(binding_stack_root, &
                    gcl_rest(vs_get(base + 2), [vs_get(base + 2)]))
            end if
         end if
       end block
    case (B_FINDVAR)
       block
         type(gc_value) :: sym2
         sym2 = strip_meta(gcv_nth(args, 0))
         out = resolve_var(sym2, vs_get(base + 1))
       end block
    case (B_LASTINDEXOF)
       block
         character(len=:), allocatable :: hay, ned
         integer :: j, hit
         hay = text_of(gcv_nth(args, 0))
         ned = needle_text(gcv_nth(args, 1))
         hit = 0
         if (len(ned) > 0 .and. len(ned) <= len(hay)) then
            do j = 1, len(hay) - len(ned) + 1
               if (hay(j:j+len(ned)-1) == ned) then
                  if (n >= 3) then
                     if (j - 1 > int(strip_int(gcv_nth(args, 2)))) exit
                  end if
                  hit = j
               end if
            end do
         end if
         out = gc_int(hit - 1)
       end block
    case (B_RTLOAD)
       ! RT.load takes a CLASSPATH-relative name without its extension:
       ! (load "core_proxy") reaches here as "clojure/core_proxy",
       ! and classpath_find turns that into a file.
       block
         character(len=:), allocatable :: rel
         type(gc_value) :: fargs
         rel = text_of(gcv_nth(args, 0))
         ! The two libs that ARE the JVM are skipped BY NAME, and
         ! loudly. core_proxy and genclass emit bytecode through
         ! clojure.asm and DynamicClassLoader; there is nothing here
         ! for them to emit. Naming the two, rather than tolerating
         ! any missing file, keeps a real typo in a load path an
         ! error.
         !
         ! Skipping matters more than it looks: the (load ...) block
         ! sits at core.clj line 6983 and `reduce` is at 7076, so
         ! stopping at the first of them costs the whole second half
         ! of the seq library. DEVIATIONS.md 12.
         ! CLOJURE.CORE IS ALREADY LOADED, and loading it again is
         ! not merely wasteful -- it re-evaluates every definition
         ! in the file against a namespace that already has them.
         ! (require 'clojure.core) and (use 'clojure.core) both
         ! reach here, and Clojure's own test helper opens every
         ! temporary namespace with (clojure.core/use 'clojure.core)
         ! -- which died on an arity error halfway through the
         ! reload. Clojure answers nil and changes nothing;
         ! so does this. Quietly, because it is not a gap.
         if (rel == "clojure/core") then
            out = gc_nil()
            call vs_leave(base)
            return
         end if
         if (rel == "clojure/core_proxy" .or. &
              rel == "clojure/genclass" .or. &
              rel == "clojure/gvec" .or. &
              rel == "clojure/uuid" .or. &
              rel == "clojure/java/io") then
            print '(A,A,A)', "note: skipping ", rel, &
                 " (JVM-only)"
            out = gc_nil()
            call vs_leave(base)
            return
         end if
         fargs = gcv_empty([vs_get(base + 1)])
         fargs = gcv_conj(fargs, gc_str(classpath_find(rel), &
              [vs_get(base + 1)]), [vs_get(base + 1)])
         call vs_set(base + 2, fargs)
         ! *ns* is SAVED AND RESTORED around the load, as RT.load
         ! does by pushing CURRENT_NS. Without it a loaded file's
         ! own (ns ...) leaks into whatever loaded it, and the next
         ! (load "x") resolves x relative to the wrong namespace.
         call vs_set(base + 3, gcn_current([vs_get(base + 1)]))
         out = call_builtin(B_LOADFILE, vs_get(base + 2))
         call gcn_set_current(vs_get(base + 3))
       end block
    case (B_INDEXOF)
       ! String.indexOf is overloaded on (int ch) as well as
       ! (String). An INTEGER is a character CODE, not the text
       ! of that integer -- cl_format.clj writes
       ! (.indexOf s (int \~)) to find its directives, and
       ! searching for "126" never found one, so every format
       ! string compiled to itself as literal text and cl-format
       ! returned the format unchanged.
       block
         character(len=:), allocatable :: hay, ned
         integer :: from1, hit1
         hay = text_of(gcv_nth(args, 0))
         ned = needle_text(gcv_nth(args, 1))
         from1 = 0
         if (n >= 3) from1 = max(0, int(strip_int(gcv_nth(args, 2))))
         hit1 = 0
         if (from1 < len(hay) .or. len(ned) == 0) &
              hit1 = index(hay(from1+1:), ned)
         if (hit1 > 0) then
            out = gc_int(hit1 + from1 - 1)
         else
            out = gc_int(-1)
         end if
       end block
    case (B_SUBVEC)
       ! (subvec v start) and (subvec v start end). A copy rather than a
       ! view: Clojure's APersistentVector$SubVector shares the source,
       ! which matters for a big vector and not at all yet.
       block
         type(gc_value) :: src, acc, ix
         integer :: lo, hi, j
         src = strip_meta(gcv_nth(args, 0))
         ix = gcv_nth(args, 1)
         lo = int(ix%ival)
         hi = gcv_count(src)
         if (n >= 3) then
            ix = gcv_nth(args, 2)
            hi = int(ix%ival)
         end if
         acc = gcv_empty([vs_get(base + 1)])
         call vs_set(base + 2, acc)
         do j = lo, hi - 1
            acc = gcv_conj(vs_get(base + 2), gcv_nth(src, j), [vs_get(base + 1), vs_get(base + 2)])
            call vs_set(base + 2, acc)
         end do
         out = vs_get(base + 2)
       end block
    case (B_NEXTID)
       gensym_id = gensym_id + 1
       out = gc_int(gensym_id)
    case (B_EXMSG, B_EXDATA)
       a = gcv_nth(args, 0)
       out = gc_nil()
       if (gc_kind(a) == OBJ_ERR) then
          if (id == B_EXMSG) then
             out = gc_slot(a, 2)
          else
             out = gc_slot(a, 3)
          end if
       end if
    case (B_ZERO, B_POS, B_NEG)
       block
         type(gc_value) :: z
         z = gc_int(0)
         a = gcv_nth(args, 0)
         select case (id)
         case (B_ZERO); out = gc_bool(.not. (num_lt(a, z) .or. num_lt(z, a)))
         case (B_POS);  out = gc_bool(num_lt(z, a))
         case (B_NEG);  out = gc_bool(num_lt(a, z))
         end select
       end block
    case (B_MAX, B_MIN)
       out = gcv_nth(args, 0)
       do i = 1, n - 1
          b = gcv_nth(args, i)
          if (id == B_MAX) then
             if (num_lt(out, b)) out = b
          else
             if (num_lt(b, out)) out = b
          end if
       end do
    case (B_APPEND)
       ! MUTATES and returns the builder, as StringBuilder.append does:
       ! (recur (. sb (append ...)) ...) in core.clj's str relies on
       ! getting the same object back.
       a = gcv_nth(args, 0)
       out = a
       if (gc_kind(a) == OBJ_SB) then
          call gc_set_slot(a, 1, gc_str( &
               text_of(gc_slot(a, 1)) // text_of(gcv_nth(args, 1)), &
               [vs_get(base + 1)]))
       else if (gc_kind(a) == OBJ_WRITER) then
          write(gc_i1(a), '(A)', advance='no') text_of(gcv_nth(args, 1))
       end if
    case (B_TOSTRING)
       out = gc_str(to_string_text(gcv_nth(args, 0)), [vs_get(base + 1)])
    case (B_NANOTIME, B_MILLIS)
       block
         integer(8) :: c, r
         real(gc_dp) :: secs
         call system_clock(c, r)
         secs = real(c, gc_dp) / real(r, gc_dp)
         if (id == B_NANOTIME) then
            out = gc_int(int(secs * 1.0d9, 8))
         else
            out = gc_int(int(secs * 1.0d3, 8))
         end if
       end block
    case (B_GETPROP)
       ! The host describing itself. Only the properties core.clj
       ! actually reads; anything else is nil, which is what
       ! System.getProperty gives for a property that is not set.
       a = gcv_nth(args, 0)
       out = gc_nil()
       if (a%tag == GCT_STR) then
          if (gc_ref_is(a%ref, "line.separator")) out = gc_str(achar(10), [vs_get(base + 1)])
       end if
    case (B_DEREF)
       ! A Var, an atom and a delay all deref the same way here: the
       ! thing in slot 1.
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_DELAY) then
          ! ONCE. The thunk runs on the first deref and the answer is
          ! cached in slot 2; i1 says which state it is in. Running it
          ! again would be observable whenever the body has an effect.
          if (gc_i1(a) == 0) then
             call vs_set(base + 2, a)
             b = apply(gc_slot(vs_get(base + 2), 1), &
                  gcv_empty([vs_get(base + 1), vs_get(base + 2)]))
             if (has_error) then
                ! A DELAY THAT THREW STAYS THROWN, with the SAME
                ! exception object every time -- Delay.deref
                ! catches the throwable, drops the thunk and
                ! rethrows what it caught on every later deref.
                ! Letting the error escape without recording it
                ! meant the body RAN AGAIN, which is observable
                ! whenever it has an effect, and made
                ! (identical? r (deref-again)) false.
                call gc_set_slot(vs_get(base + 2), 2, thrown_value())
                call gc_set_slot(vs_get(base + 2), 3, &
                     gc_str(gce_error(), [vs_get(base + 1), vs_get(base + 2)]))
                call gc_set_i1(vs_get(base + 2), 2)
                call vs_leave(base)
                return
             end if
             call gc_set_slot(vs_get(base + 2), 2, b)
             call gc_set_i1(vs_get(base + 2), 1)
             a = vs_get(base + 2)
          end if
          if (gc_i1(a) == 2) then
             call set_thrown(gc_slot(a, 2))
             call fail(text_of(gc_slot(a, 3)))
             call vs_leave(base)
             return
          end if
          out = gc_slot(a, 2)
       else if (gcn_is_var(a) .or. gc_kind(a) == OBJ_ATOM) then
          out = gc_slot(a, 1)
       else if (gca_contains(a, gc_key("clotran/reduced", &
            [vs_get(base + 1)]))) then
          ! Unwrapping a (reduced x) is a deref in Clojure too.
          out = gca_get(a, gc_key("clotran/reduced", [vs_get(base + 1)]))
       else
          out = a
       end if
    case (B_HASROOT)
       a = gcv_nth(args, 0)
       out = gc_bool(gcn_is_var(a) .and. gc_i1(a) == 1)
    case (B_ADDMETHOD)
       ! MUTATES the multimethod, as MultiFn.addMethod does, and returns
       ! it so (. mf (addMethod v f)) evaluates to the multimethod.
       a = gcv_nth(args, 0)
       out = a
       if (gc_kind(a) == OBJ_MULTIFN) then
          call gc_set_slot(a, 4, gca_assoc(gc_slot(a, 4), gcv_nth(args, 1), &
               gcv_nth(args, 2), [vs_get(base + 1)]))
       end if
    case (B_METHODTABLE)
       a = gcv_nth(args, 0)
       out = gca_empty([vs_get(base + 1)])
       if (gc_kind(a) == OBJ_MULTIFN) out = gc_slot(a, 4)
    case (B_REMOVEMETHOD)
       ! Mutates and answers the multimethod, the mirror of
       ! addMethod.
       a = gcv_nth(args, 0)
       out = a
       if (gc_kind(a) == OBJ_MULTIFN) &
            call gc_set_slot(a, 4, gca_dissoc(gc_slot(a, 4), gcv_nth(args, 1), &
                 [vs_get(base + 1)]))
    case (B_MATH0 + 1 : B_MATH0 + B_MATHN)
       out = math_call(id - B_MATH0, args, [vs_get(base + 1)])
    case (B_FORMAT)
       ! (String/format fmt (to-array args)) -- the arguments
       ! arrive as one ARRAY, not spread.
       block
         type(gc_value) :: fv, av
         fv = strip_meta(gcv_nth(args, 0))
         if (fv%tag /= GCT_STR) then
            call fail("format: first argument must be a string")
         else
            av = gcv_empty([vs_get(base + 1)])
            if (n >= 2) av = coll_to_vector(gcv_nth(args, 1), [vs_get(base + 1)])
            call vs_set(base + 2, av)
            out = gc_str(java_format(gc_ref_text(fv%ref), vs_get(base + 2)), &
                 [vs_get(base + 1), vs_get(base + 2)])
         end if
       end block
    case (B_RTPRINT)
       block
         type(gc_value) :: w
         character(len=:), allocatable :: txt
         txt = gcp_str(gcv_nth(args, 0), .true.)
         out = gc_nil()
         if (n >= 2) then
            w = strip_meta(gcv_nth(args, 1))
            if (gc_kind(w) == OBJ_SB) then
               call gc_set_slot(w, 1, gc_str(text_of(gc_slot(w, 1)) // txt, &
                    [vs_get(base + 1)]))
            else if (gc_kind(w) == OBJ_WRITER) then
               write(gc_i1(w), '(A)', advance='no') txt
            end if
         end if
       end block
    case (B_SETVALIDATOR, B_GETVALIDATOR)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (id == B_GETVALIDATOR) then
          out = ref_fn_get(a, "validator", [vs_get(base + 1)])
       else
          ! Clojure VALIDATES THE CURRENT VALUE on the way in and
          ! refuses a validator the state already fails.
          if (validate_ref(a, gcv_nth(args, 1), gc_slot(a, 1), &
               [vs_get(base + 1)])) call ref_fn_put(a, "validator", &
               gcv_nth(args, 1), [vs_get(base + 1)])
       end if
    case (B_LATCHDOWN, B_LATCHCOUNT)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gc_kind(a) == OBJ_ATOM) then
          if (id == B_LATCHDOWN) then
             block
               type(gc_value) :: cur
               cur = gc_slot(a, 1)
               if (cur%tag == GCT_INT) call gc_set_slot(a, 1, gc_int(max(0_gc_ip, cur%ival - 1)))
             end block
          else
             out = gc_slot(a, 1)
          end if
       end if
    case (B_SETERRMODE, B_SETERRHANDLER)
       ! Both answer the AGENT, since core.clj threads it on.
       a = strip_meta(gcv_nth(args, 0))
       out = a
       if (gc_kind(a) == OBJ_ATOM) then
          if (id == B_SETERRMODE) then
             call gc_set_slot(a, 3, gcv_nth(args, 1))
          else
             call ref_fn_put(a, "error-handler", gcv_nth(args, 1), [vs_get(base + 1)])
          end if
       end if
    case (B_GETERRMODE, B_GETERRHANDLER, B_AGENTERROR)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gc_kind(a) == OBJ_ATOM) then
          select case (id)
          case (B_GETERRMODE);    out = gc_slot(a, 3)
          case (B_GETERRHANDLER); out = ref_fn_get(a, "error-handler", [vs_get(base + 1)])
          case default;           out = gc_slot(a, 5)
          end select
       end if
    case (B_AGENTRESTART)
       ! (restart-agent a new-state) clears the failure and takes
       ! the state given, which is what Agent.restart does.
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gc_kind(a) == OBJ_ATOM) then
          call gc_set_slot(a, 5, gc_nil())
          if (n >= 2) call gc_set_slot(a, 1, gcv_nth(args, 1))
          out = gc_slot(a, 1)
       end if
    case (B_AGENTDISPATCH)
       ! (.dispatch a f args executor) -- SYNCHRONOUS here, so the
       ! action runs before dispatch returns. A failed agent
       ! refuses the action; an action that throws records the
       ! error, calls the handler if there is one, and under
       ! :fail leaves the agent failed with its old value.
       block
         type(gc_value) :: ag, fargs, res, hnd, prior
         integer :: j
         ag = strip_meta(gcv_nth(args, 0))
         out = ag
         prior = gc_slot(ag, 5)
         if (gc_kind(ag) /= OBJ_ATOM) then
            call fail("dispatch: not an agent")
         else if (prior%tag /= GCT_NIL) then
            call raise_class("RuntimeException", &
                 "Agent is failed, needs restart", [vs_get(base + 1)])
         else
            call vs_set(base + 2, ag)
            fargs = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
            fargs = gcv_conj(fargs, gc_slot(vs_get(base + 2), 1), &
                 [vs_get(base + 1), vs_get(base + 2)])
            call vs_set(base + 3, fargs)
            block
              type(gc_value) :: extra
              extra = coll_to_vector(gcv_nth(args, 2), &
                   [vs_get(base + 1), vs_get(base + 3)])
              call vs_set(base + 4, extra)
              do j = 0, gcv_count(vs_get(base + 4)) - 1
                 fargs = gcv_conj(vs_get(base + 3), gcv_nth(vs_get(base + 4), j), &
                      [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
                 call vs_set(base + 3, fargs)
              end do
            end block
            res = apply(gcv_nth(args, 1), vs_get(base + 3))
            if (has_error) then
               call gc_set_slot(vs_get(base + 2), 5, thrown_value())
               hnd = ref_fn_get(vs_get(base + 2), "error-handler", [vs_get(base + 1)])
               call gce_clear_error()
               if (hnd%tag /= GCT_NIL) then
                  fargs = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
                  fargs = gcv_conj(fargs, vs_get(base + 2), &
                       [vs_get(base + 1), vs_get(base + 2)])
                  call vs_set(base + 3, fargs)
                  fargs = gcv_conj(vs_get(base + 3), &
                       gc_slot(vs_get(base + 2), 5), &
                       [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
                  call vs_set(base + 3, fargs)
                  res = apply(hnd, vs_get(base + 3))
                  call gce_clear_error()
               end if
               ! :continue forgets the failure; :fail keeps it.
               if (.not. gc_equal(gc_slot(vs_get(base + 2), 3), &
                    gc_key("fail", [vs_get(base + 1)]))) &
                    call gc_set_slot(vs_get(base + 2), 5, gc_nil())
            else if (.not. validate_ref(vs_get(base + 2), &
                 ref_fn_get(vs_get(base + 2), "validator", [vs_get(base + 1)]), &
                 res, [vs_get(base + 1)])) then
               ! A REJECTED STATE IS AN AGENT ERROR, handled the
               ! same way a thrown action is.
               call gc_set_slot(vs_get(base + 2), 5, thrown_value())
               call gce_clear_error()
               if (.not. gc_equal(gc_slot(vs_get(base + 2), 3), &
                    gc_key("fail", [vs_get(base + 1)]))) &
                    call gc_set_slot(vs_get(base + 2), 5, gc_nil())
            else
               call gc_set_slot(vs_get(base + 2), 1, res)
            end if
            out = vs_get(base + 2)
         end if
       end block
    case (B_GETIFACES)
       block
         type(gc_value) :: cv, acc, sk
         integer :: si2
         cv = strip_meta(gcv_nth(args, 0))
         acc = gcv_empty([vs_get(base + 1)])
         call vs_set(base + 2, acc)
         do si2 = 1, 24
            sk = host_super(cv, si2, vs_get(base + 1))
            if (sk%tag == GCT_NIL) exit
            acc = gcv_conj(vs_get(base + 2), sk, &
                 [vs_get(base + 1), vs_get(base + 2), sk])
            call vs_set(base + 2, acc)
         end do
         out = vs_get(base + 2)
       end block
    case (B_EMPTYARRAY)
       out = value_array(gcv_empty([vs_get(base + 1)]), [vs_get(base + 1)])
    case (B_STACKTRACE)
       ! (.getStackTrace e): the frames e was thrown with; for anything
       ! that is not a Throwable -- (Thread/currentThread) -- the
       ! frames of the call in progress.
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_ERR .and. gcv_is(gc_slot(a, 4))) then
          out = value_array(gc_slot(a, 4), [vs_get(base + 1)])
       else
          call vs_set(base + 2, frames_vec([vs_get(base + 1)]))
          out = value_array(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 2)])
       end if
    case (B_STE_CLASS, B_STE_METHOD, B_STE_FILE, B_STE_LINE)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gca_is(a)) then
          select case (id)
          case (B_STE_CLASS);  out = gca_get(a, gc_key("class", [vs_get(base + 1)]))
          case (B_STE_METHOD); out = gca_get(a, gc_key("method", [vs_get(base + 1)]))
          case (B_STE_FILE);   out = gca_get(a, gc_key("file", [vs_get(base + 1)]))
          case (B_STE_LINE);   out = gca_get(a, gc_key("line", [vs_get(base + 1)]))
          end select
       end if
    case (B_INTOARRAY)
       out = value_array(gcv_nth(args, n - 1), [vs_get(base + 1)])
    case (B_RE_START, B_RE_END)
       block
         type(gc_value) :: mt, iv
         integer :: mh3, gnum3, gs3, ge3
         mt = strip_meta(gcv_nth(args, 0))
         out = gc_int(-1)
         if (gc_kind(mt) == OBJ_MATCHER) then
            mh3 = gc_i1(mt)
            gnum3 = 0
            if (n >= 2) then
               iv = strip_meta(gcv_nth(args, 1))
               gnum3 = int(iv%ival)
            end if
            if (regex_group_span(mh3, gnum3, gs3, ge3)) then
               if (id == B_RE_START) then
                  out = gc_int(gs3)
               else
                  out = gc_int(ge3)
               end if
            end if
         end if
       end block
    case (B_RE_REPLACEALL, B_RE_REPLACEFIRST)
       block
         type(gc_value) :: mt
         mt = strip_meta(gcv_nth(args, 0))
         if (gc_kind(mt) == OBJ_MATCHER) then
            out = regex_replace(mt, text_of(gcv_nth(args, 1)), &
                 id == B_RE_REPLACEFIRST, [vs_get(base + 1)])
         else if (mt%tag == GCT_STR .and. n >= 3) then
            ! String.replaceAll(regex, replacement) and replaceFirst: the
            ! pattern source is compiled here, as Java compiles it on
            ! every call, and matched against the string.
            block
              type(gc_value) :: rx, mv
              integer :: h, mh
              character(len=:), allocatable :: stext
              h = regex_compile(text_of(gcv_nth(args, 1)))
              if (h == 0) then
                 call fail("regex: " // regex_last_error())
              else
                 rx = gc_obj(OBJ_REGEX, [gc_str(text_of(gcv_nth(args, 1)), [vs_get(base + 1)])], [vs_get(base + 1)])
                 call gc_set_i1(rx, h)
                 call vs_set(base + 2, rx)
                 mh = regex_clone(h)
                 stext = text_of(mt)
                 if (mh == 0) then
                    call fail("regex: " // regex_last_error())
                 else if (.not. regex_set_text(mh, stext)) then
                    call fail("regex: " // regex_last_error())
                 else
                    mv = gc_obj(OBJ_MATCHER, [vs_get(base + 2), gc_str(stext, [vs_get(base + 1), vs_get(base + 2)])], &
                         [vs_get(base + 1), vs_get(base + 2)])
                    call gc_set_i1(mv, mh)
                    call vs_set(base + 3, mv)
                    out = regex_replace(vs_get(base + 3), text_of(gcv_nth(args, 2)), &
                         id == B_RE_REPLACEFIRST, [vs_get(base + 1)])
                 end if
              end if
            end block
         else
            call fail("replaceAll needs a Matcher")
         end if
       end block
    case (B_RE_APPENDREPL, B_RE_APPENDTAIL)
       ! (.appendReplacement m buffer repl) and (.appendTail m
       ! buffer): the buffer is the SECOND argument and is
       ! mutated, and the answer is the matcher.
       block
         type(gc_value) :: mt, bufv
         character(len=:), allocatable :: subj, piece
         integer :: mh2, gs2, ge2, apos
         mt = strip_meta(gcv_nth(args, 0))
         bufv = strip_meta(gcv_nth(args, 1))
         out = mt
         if (gc_kind(mt) /= OBJ_MATCHER) then
            call fail("appendReplacement needs a Matcher")
         else
            subj = text_of(gc_slot(mt, 2))
            mh2 = gc_i1(mt)
            apos = gc_i2(mt)
            if (id == B_RE_APPENDTAIL) then
               piece = subj(apos+1:)
            else if (regex_group_span(mh2, 0, gs2, ge2)) then
               piece = subj(apos+1:gs2) // &
                    expand_replacement(text_of(gcv_nth(args, 2)), mh2, subj)
               call gc_set_i2(mt, ge2)
            else
               piece = ""
            end if
            if (gc_kind(bufv) == OBJ_SB) then
               call gc_set_slot(bufv, 1, gc_str( &
                    text_of(gc_slot(bufv, 1)) // piece, [vs_get(base + 1)]))
            end if
         end if
       end block
    case (B_RE_SPLIT)
       block
         type(gc_value) :: pv, sv, lv
         integer :: lim
         pv = strip_meta(gcv_nth(args, 0))
         sv = strip_meta(gcv_nth(args, 1))
         lim = 0
         if (n >= 3) then
            lv = strip_meta(gcv_nth(args, 2))
            lim = int(lv%ival)
         end if
         if (gc_kind(pv) == OBJ_REGEX) then
            out = regex_split(pv, sv, lim, [vs_get(base + 1)])
         else if (pv%tag == GCT_STR .and. sv%tag == GCT_STR) then
            ! String.split(regex[, limit]): the string is the subject and
            ! the second argument is a pattern SOURCE, compiled here as
            ! Java compiles it on every call.
            call vs_set(base + 2, pv)
            block
              type(gc_value) :: rx
              integer :: h
              h = regex_compile(text_of(sv))
              if (h == 0) then
                 call fail("regex: " // regex_last_error())
              else
                 rx = gc_obj(OBJ_REGEX, [gc_str(text_of(sv), [vs_get(base + 1)])], [vs_get(base + 1)])
                 call gc_set_i1(rx, h)
                 call vs_set(base + 3, rx)
                 out = regex_split(vs_get(base + 3), vs_get(base + 2), lim, [vs_get(base + 1)])
              end if
            end block
         else
            call fail("split needs a Pattern")
         end if
       end block
    case (B_QUOTEREPL)
       out = gc_str(quote_replacement(text_of(gcv_nth(args, 0))), &
            [vs_get(base + 1)])
    case (B_SBREVERSE)
       ! Mutates and returns the builder, like append.
       block
         character(len=:), allocatable :: bt, rt
         integer :: bi
         a = gcv_nth(args, 0)
         out = a
         bt = text_of(a)
         rt = bt
         do bi = 1, len(bt)
            rt(bi:bi) = bt(len(bt) - bi + 1:len(bt) - bi + 1)
         end do
         if (gc_kind(a) == OBJ_SB) then
            call gc_set_slot(a, 1, gc_str(rt, [vs_get(base + 1)]))
         else
            out = gc_str(rt, [vs_get(base + 1)])
         end if
       end block
    case (B_READSTRING)
       block
         type(gc_value) :: sv
         sv = strip_meta(gcv_nth(args, 0))
         if (sv%tag /= GCT_STR) then
            call fail("read-string wants a string")
         else
            out = gcr_read(gc_ref_text(sv%ref), [vs_get(base + 1)])
            if (gcr_has_error()) call fail(gcr_error())
         end if
       end block
    case (B_NUMCOMPARE)
       ! Double.compare's total order. -0.0 < 0.0, and NaN is
       ! greater than every other value including +Inf -- neither
       ! of which plain < can say.
       block
         real(gc_dp) :: dx, dy
         type(gc_value) :: cx, cy
         integer :: cres
         cx = strip_meta(gcv_nth(args, 0))
         cy = strip_meta(gcv_nth(args, 1))
         if (cx%tag == GCT_INT .and. cy%tag == GCT_INT) then
            cres = 0
            if (cx%ival < cy%ival) cres = -1
            if (cx%ival > cy%ival) cres = 1
         else
            dx = num_dbl(cx)
            dy = num_dbl(cy)
            if (dx < dy) then
               cres = -1
            else if (dx > dy) then
               cres = 1
            else if (dx /= dx .or. dy /= dy) then
               ! At least one is NaN, and they did not compare
               ! equal: NaN sorts last, and two NaNs are equal.
               cres = 0
               if (dy /= dy .and. dx == dx) cres = -1
               if (dx /= dx .and. dy == dy) cres = 1
            else
               ! Equal as numbers -- so only signed zero is left.
               cres = 0
               if (is_neg_zero(dx) .and. .not. is_neg_zero(dy)) cres = -1
               if (is_neg_zero(dy) .and. .not. is_neg_zero(dx)) cres = 1
            end if
         end if
         out = gc_int(cres)
       end block
    case (B_EMPTYMAP)
       out = gca_empty([vs_get(base + 1)])
    case (B_GETMETHOD)
       ! The method a dispatch value WOULD reach. Same three steps
       ! the multimethod call itself takes -- exact, host
       ! supertypes, then the default dispatch value -- because
       ! get-method is documented as answering what WOULD apply.
       a = gcv_nth(args, 0)
       out = gc_nil()
       if (gc_kind(a) == OBJ_MULTIFN) then
          block
            integer :: si
            type(gc_value) :: sk
            out = gca_get(gc_slot(a, 4), gcv_nth(args, 1))
            if (out%tag == GCT_NIL) then
               do si = 1, 24
                  sk = host_super(gcv_nth(args, 1), si, a)
                  if (sk%tag == GCT_NIL) exit
                  out = gca_get(gc_slot(a, 4), sk)
                  if (out%tag /= GCT_NIL) exit
               end do
            end if
            if (out%tag == GCT_NIL) out = gca_get(gc_slot(a, 4), gc_slot(a, 3))
          end block
       end if
    case (B_IDENTITY)
       out = gcv_nth(args, 0)
    case (B_GT, B_LTE, B_GTE)
       ! Chained, like <: (< 1 2 3) is true, and Clojure'\''s > is the
       ! same shape. Written against num_lt so int/double mixing is
       ! decided in exactly one place.
       block
         logical :: ok
         integer :: j
         ok = .true.
         do j = 0, n - 2
            a = gcv_nth(args, j)
            b = gcv_nth(args, j + 1)
            select case (id)
            case (B_GT);  ok = ok .and. num_lt(b, a)
            case (B_LTE); ok = ok .and. (.not. num_lt(b, a))
            case (B_GTE); ok = ok .and. (.not. num_lt(a, b))
            end select
         end do
         out = gc_bool(ok)
       end block
    case (B_DIV)
       ! There IS a Ratio now, so an inexact integer division is no
       ! longer approximated with a double: (/ 1 3) is 1/3.
       !
       ! Contagion again -- a double anywhere makes the answer a
       ! double, and otherwise the result stays exact. Dividing by a
       ! ratio multiplies by its reciprocal.
       a = strip_meta(gcv_nth(args, 0)); b = strip_meta(gcv_nth(args, 1))
       if (is_ratio(a) .or. is_ratio(b)) then
          ! Exact, and the integer arm below would have read a ratio
          ! as its numerator: (quot 7/2 1) would answer 7, not 3.
          ! a/b is (an*bd)/(ad*bn), and quot truncates that toward
          ! zero -- which is what Fortran's integer division does.
          block
            integer(gc_ip) :: an, ad, bn, bd, qi
            an = gc_numerator(a); ad = gc_denominator(a)
            bn = gc_numerator(b); bd = gc_denominator(b)
            if (bn == 0) then
               call fail("Divide by zero")
            else
               qi = (an * bd) / (ad * bn)
               if (id == B_QUOT) then
                  out = gc_int(qi)
               else
                  ! rem is a - b*quot, kept exact.
                  out = gc_ratio(an * bd - qi * bn * ad, ad * bd)
               end if
            end if
          end block
       else if (a%tag == GCT_REAL .or. b%tag == GCT_REAL) then
          ! (/ 1.0 0) is ##Inf, NOT an error -- only the exact path
          ! raises. Verified against clj.
          out = gc_real(num_dbl(a) / num_dbl(b))
       else if (gc_numerator(b) == 0) then
          call fail("Divide by zero")
       else
          out = gc_ratio(gc_numerator(a) * gc_denominator(b), &
                         gc_denominator(a) * gc_numerator(b))
       end if
    case (B_INC, B_DEC)
       a = strip_meta(gcv_nth(args, 0))
       if (is_ratio(a)) then
          ! (inc 1/2) is 3/2, not 1.5 -- the else branch below sends
          ! everything that is not an integer through num_dbl, which
          ! would silently drop a ratio to a double.
          if (id == B_INC) then
             out = gc_ratio(gc_numerator(a) + gc_denominator(a), gc_denominator(a))
          else
             out = gc_ratio(gc_numerator(a) - gc_denominator(a), gc_denominator(a))
          end if
       else if (a%tag == GCT_INT) then
          if (id == B_INC) then
             out = gc_int(a%ival + 1)
          else
             out = gc_int(a%ival - 1)
          end if
       else
          if (id == B_INC) then
             out = gc_real(num_dbl(a) + 1.0_gc_dp)
          else
             out = gc_real(num_dbl(a) - 1.0_gc_dp)
          end if
       end if
    case (B_COMPARE)
       block
         logical :: cok
         integer :: cv
         cv = compare_values(gcv_nth(args, 0), gcv_nth(args, 1), cok)
         if (cok) then
            out = gc_int(cv)
         else
            call fail("compare: cannot compare " // &
                 type_name(strip_meta(gcv_nth(args, 0))) // " with " // &
                 type_name(strip_meta(gcv_nth(args, 1))))
         end if
       end block
    case (B_DISJ)
       ! A set is a map to itself, so disj is dissoc on the backing map.
       block
         type(gc_value) :: st
         st = gcv_nth(args, 0)
         if (gc_kind(st) == OBJ_SET) then
            out = gc_obj(OBJ_SET, &
                 [gca_dissoc(gc_slot(st, 1), gcv_nth(args, 1), [vs_get(base + 1)])], &
                 [vs_get(base + 1)])
         else
            out = st
         end if
       end block
    case (B_INSTANCE)
       out = gc_bool(is_instance(gcv_nth(args, 0), gcv_nth(args, 1)))
    case (B_REDUCEINIT)
       ! (.reduce coll f) and (.reduce coll f init): IReduceInit.reduce,
       ! the host loop the JVM runs for a LongRange, a vector or a list
       ! instead of walking seqs. A native range is walked by its
       ! arithmetic and allocates no cells; a reduced value ends it
       ! and is unwrapped, as Java's reduce does.
       out = reduce_native(strip_meta(gcv_nth(args, 0)), gcv_nth(args, 1), n >= 3, gcv_nth(args, 2))
    case (B_CHUNK_ADD)
       ! ChunkBuffer.add: the buffer grows if asked past its capacity,
       ! where Java's throws -- nothing in core.clj asks.
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) /= OBJ_CHUNKBUF) then
          call fail("no such member: " // class_name_of(a) // ".add")
       else
          block
            type(gc_value) :: run, bigger
            integer :: cnt, k
            run = gc_slot(a, 1)
            cnt = gc_i1(a)
            if (cnt >= gc_vec_len(run)) then
               call vs_set(base + 2, a)
               bigger = gc_vec(max(2 * cnt, 1), [vs_get(base + 1), vs_get(base + 2)])
               do k = 1, cnt
                  call gc_vec_set(bigger, k, gc_vec_get(gc_slot(vs_get(base + 2), 1), k))
               end do
               call gc_set_slot(vs_get(base + 2), 1, bigger)
               a = vs_get(base + 2)
               run = gc_slot(a, 1)
            end if
            call gc_vec_set(run, cnt + 1, gcv_nth(args, 1))
            call gc_set_i1(a, cnt + 1)
          end block
          out = gc_nil()
       end if
    case (B_CHUNK_OF)
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) /= OBJ_CHUNKBUF) then
          call fail("no such member: " // class_name_of(a) // ".chunk")
       else
          out = make_chunk(gc_slot(a, 1), 0, gc_i1(a), [vs_get(base + 1)])
       end if
    case (B_CHUNK_FIRST, B_CHUNK_MORE, B_CHUNK_NEXT)
       block
         type(gc_value) :: ch, mo
         a = strip_meta(gcv_nth(args, 0))
         if (.not. is_chunked_seq(a)) then
            call fail("no such member: " // class_name_of(a) // ".chunkedFirst")
         else
            call chunked_parts(a, ch, mo, [vs_get(base + 1)])
            if (id == B_CHUNK_FIRST) then
               out = ch
            else if (id == B_CHUNK_MORE) then
               out = mo
               if (out%tag == GCT_NIL) out = gcl_empty([vs_get(base + 1)])
            else
               call vs_set(base + 2, mo)
               out = to_seq(vs_get(base + 2), [vs_get(base + 1)])
            end if
         end if
       end block
    case (B_CHUNK_DROP)
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) /= OBJ_CHUNK) then
          call fail("no such member: " // class_name_of(a) // ".dropFirst")
       else
          out = make_chunk(gc_slot(a, 1), gc_i1(a) + 1, gc_i2(a), [vs_get(base + 1)])
       end if
    case (B_BREAK)
       ! (clotran-break) -- the paused state here, as data, stored, and
       ! handed to the handler; what comes back is the value here.
       out = take_break("break")
    case (B_RESUME)
       ! (clotran-resume cmd) at a nested REPL: the command that REPL
       ! answers with, once the form that called this has returned.
       ! No argument is :continue.
       if (repl_depth < 2) then
          call fail("clotran-resume: not at a break")
       else
          a = gc_key("continue", [gc_nil()])
          if (n > 0) a = gcv_nth(args, 0)
          call gc_global_keep(resume_root, a)
          resume_pending = .true.
       end if
    case (B_REPL)
       ! (clotran-repl state): a nested REPL, the default handler.
       a = gc_nil()
       if (n > 0) a = gcv_nth(args, 0)
       out = repl_loop(a)
    case (B_LASTBREAK)
       out = gc_nil()
       if (gc_root_live(break_root)) out = gc_root_get(break_root)
    case (B_BREAKON)
       ! (clotran-break-on! true) at a REPL, for when the process was not
       ! started under CLOTRAN_BREAK. Capturing is off by default because
       ! it builds a map of every frame at every error, caught ones
       ! included.
       if (break_mode == 0) call read_break_mode()
       if (truthy(gcv_nth(args, 0))) then
          break_mode = 2
       else
          break_mode = 1
       end if
       out = gc_bool(break_mode == 2)
    case (B_IDHASH)
       ! System.identityHashCode: a number that is the same for the same
       ! object and usually differs between objects. The pool index is
       ! exactly that for a heap object (the collector does not move),
       ! and an immediate hashes by value, as a boxed Long would not --
       ! print-object only puts it in #object[... 0x..] anyway.
       a = strip_meta(gcv_nth(args, 0))
       if (a%ref /= 0) then
          out = gc_int(int(a%ref, gc_ip))
       else
          out = gc_int(int(gc_hash(a), gc_ip))
       end if
    case (B_CLASSOF)
       ! (class x): the canonical class keyword, nil for nil.
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_NIL) then
          out = gc_nil()
       else
          out = gc_key(class_name_of(a), [vs_get(base + 1)])
       end if
    case (B_TYPE)
       ! One host primitive instead of a dozen predicates: core is
       ! written in Clojure on top of this, which is how real Clojure
       ! does it too (instance? plus defns).
       a = gcv_nth(args, 0)
       out = gc_key(type_name(a), [vs_get(base + 1)])
    case (B_CONCAT)
       ! Right to left, so the result comes out in order without a
       ! reverse. Every argument is seq'd to a list first, which is
       ! what lets (concat [1 2] (list 3)) work.
       out = gcl_empty([vs_get(base + 1)])
       do i = n - 1, 0, -1
          block
            type(gc_value) :: piece
            integer :: j
            piece = as_list(gcv_nth(vs_get(base + 1), i), [vs_get(base + 1), out])
            do j = gcl_count(piece) - 1, 0, -1
               out = gcl_cons(nth_of(piece, j), out, [vs_get(base + 1), piece])
            end do
          end block
       end do
    end select

    call vs_leave(base)
  end function call_builtin

  ! A list view of a value: lists pass through, vectors are copied
  ! into one, nil is the empty list. Enough for cons/concat and for
  ! quasiquote's splicing; a real seq abstraction is a later feature.
  function as_list(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i

    base = vs_enter(2)
    call vs_set(base + 1, v)
    if (gcl_is(v)) then
       out = v
       call vs_leave(base)
       return
    end if
    out = gcl_empty(roots)
    call vs_set(base + 2, out)
    if (gcv_is(v)) then
       do i = gcv_count(vs_get(base + 1)) - 1, 0, -1
          out = gcl_cons(gcv_nth(vs_get(base + 1), i), vs_get(base + 2), &
               [vs_get(base + 1)])
          call vs_set(base + 2, out)
       end do
    end if
    out = vs_get(base + 2)
    call vs_leave(base)
  end function as_list

  ! The nth element of a list, by walking. Only used where the list is
  ! already in hand and short.
  function nth_of(l, i) result(out)
    type(gc_value), intent(in) :: l
    integer, intent(in) :: i
    type(gc_value) :: out, walk
    integer :: base, k

    base = vs_enter(2)
    call vs_set(base + 1, l)
    walk = l
    call vs_set(base + 2, walk)
    do k = 1, i
       walk = gcl_rest(vs_get(base + 2), [vs_get(base + 1)])
       call vs_set(base + 2, walk)
    end do
    out = gcl_first(vs_get(base + 2))
    call vs_leave(base)
  end function nth_of

  ! Realises a whole lazy seq to count it. Does not terminate on an
  ! infinite one, which is correct: (count (range)) does not either.




  ! Structural equality, which is what `=` means in Clojure: two
  ! vectors of equal elements ARE equal, however they were built.
  !
  ! Deliberately NOT gc_equal, and the split is worth keeping. gc_equal
  ! compares collections by identity and is what map KEYS use -- making
  ! key comparison deep would mean hashing deeply too, and gc_hash
  ! lives in GC.f90 which cannot see the collection modules. The older
  ! evaluator draws the same line ("lists/vectors/maps as keys aren't
  ! compared deeply yet"), so this matches rather than diverges.
  ! `roots` because this now WALKS: forcing a lazy seq allocates,
  ! and so does taking the rest of a vector view, so the two sides
  ! have to be reachable across those allocations. Indexing never
  ! allocated, which is why it used to take none.
  ! --- structural hashing and equality for collections --------------
  !
  ! Installed into GC.f90 through gc_set_coll_ops. Until they were,
  ! a collection hashed and compared by its POOL SLOT, so a map keyed
  ! on one answered nil for an equal key built elsewhere:
  !
  !     (get {[1] 2} [1])   ;=> nil, clj says 2
  !     (= #{[1]} #{[1]})   ;=> false
  !     (case {:a 1 :b 2} {:b 2 :a 1} :map :default)  ;=> :default
  !
  ! The two must agree exactly: equal values have to hash equal, or a
  ! trie stores one key twice and finds whichever arm a lookup walks
  ! into. So both are written here, together, against the same notion
  ! of what equality means -- deep_equal, which is what `=` already
  ! used.

  ! Equality for the kinds is_structural_kind admits.
  !
  ! The kind pairing is checked HERE rather than left to deep_equal,
  ! which ends by delegating to gc_equal for anything it does not
  ! recognise. gc_equal now calls this function, so a pair deep_equal
  ! declined -- a set against a vector, say -- would bounce between
  ! the two forever. Mismatched kinds are simply not equal.
  recursive function gce_coll_equal(a, b) result(eq)
    type(gc_value), intent(in) :: a, b
    logical :: eq
    integer :: ka, kb
    ka = gc_kind(a)
    kb = gc_kind(b)
    eq = .false.
    if (ka == OBJ_SET .and. kb == OBJ_SET) then
       eq = deep_equal(a, b, [a, b])
    else if (ka == OBJ_MAP .and. kb == OBJ_MAP) then
       eq = deep_equal(a, b, [a, b])
    else if (is_seq_kind(ka) .and. is_seq_kind(kb)) then
       ! A list and a vector of the same elements ARE equal in
       ! Clojure, so these share one branch and one hash scheme.
       eq = deep_equal(a, b, [a, b])
    end if
  end function gce_coll_equal

  ! A SEQ VIEW counts too. It is a view over something already
  ! realised -- a vector or an array -- so walking it forces
  ! nothing, which is the reason OBJ_LAZY is still left out (see
  ! is_structural_kind in GC.f90). Without it (hash (seq [1 2]))
  ! was an identity hash while (= (seq [1 2]) [1 2]) was true,
  ! which breaks the guarantee a map relies on.
  pure logical function is_seq_kind(k)
    integer, intent(in) :: k
    is_seq_kind = (k == OBJ_CONS .or. k == OBJ_VECTOR .or. k == OBJ_SEQ .or. k == OBJ_CHUNKSEQ)
  end function is_seq_kind

  ! Hash for the same kinds, and it must NOT allocate: gc_hash runs in
  ! the middle of a map insert, where a collection could take the
  ! half-built structure with it.
  !
  !   sequential  ordered, 31*h + hash(element) -- and the SAME scheme
  !               for a list and a vector, because they can be equal.
  !   map         unordered, a sum of hash(k) xor hash(v)
  !   set         unordered, a sum of hash(element)
  !
  ! Unordered for the last two because two equal maps may hand back
  ! their entries in different orders; a fold that cared about order
  ! would hash them differently and break the invariant. Sums wrap on
  ! overflow, which is fine -- a hash may collide, it may not disagree
  ! with equality.
  recursive function gce_coll_hash(v) result(h)
    type(gc_value), intent(in) :: v
    integer :: h
    integer :: i, n, k
    type(gc_value), allocatable :: ks(:), vs_(:)
    type(gc_value) :: cur, item
    k = gc_kind(v)
    h = 0
    select case (k)
    case (OBJ_VECTOR)
       n = gcv_count(v)
       do i = 0, n - 1
          h = 31 * h + gc_hash(gcv_nth(v, i))
       end do
       h = mix32(h)
    case (OBJ_CONS)
       ! Walked through the slots rather than the seq interface: car
       ! and cdr are already there, and sq_first/sq_rest can allocate.
       !
       ! THE EMPTY TAIL IS ITSELF AN OBJ_CONS, so a walk that stops
       ! only on kind hashes one extra nil and (hash '(1)) came out
       ! equal to (hash [1 2]) rather than to (hash [1]). Clojure
       ! guarantees (= a b) implies (= (hash a) (hash b)), and a
       ! list IS equal to a vector of the same elements -- so this
       ! broke the guarantee for every list. `case` is where it
       ! showed: it dispatches on the hash, so
       ! (case (list 1 2) [1 2] :vec :d) answered :d.
       cur = v
       do while (gcl_is(cur) .and. gcl_count(cur) > 0)
          item = gc_slot(cur, 1)
          h = 31 * h + gc_hash(item)
          cur = gc_slot(cur, 2)
       end do
       h = mix32(h)
    case (OBJ_SEQ)
       ! Same fold as a vector, over the view's own elements.
       ! Read THROUGH the view: seq_elem indexes a source collection,
       ! and a seq is slot 1 plus the offset in i1.
       n = sq_count(v, [v])
       do i = 0, n - 1
          h = 31 * h + gc_hash(seq_elem(gc_slot(v, 1), gc_i1(v) + i, [v]))
       end do
       h = mix32(h)
    case (OBJ_CHUNKSEQ)
       if (seq_realised_p(v)) then
          call fold_seq(v, h)
          h = mix32(h)
       else
          ! not realised to the end: identity, as an unrealised lazy seq
          ! gets (DEVIATIONS 35)
          h = mix32(ieor(mix32(v%ref), OBJ_CHUNKSEQ))
       end if
    case (OBJ_MAP)
       call gca_entries(v, ks, vs_)
       do i = 1, size(ks)
          h = h + ieor(gc_hash(ks(i)), gc_hash(vs_(i)))
       end do
       h = mix32(ieor(h, OBJ_MAP))
    case (OBJ_SET)
       call gca_entries(gc_slot(v, 1), ks, vs_)
       do i = 1, size(ks)
          h = h + gc_hash(ks(i))
       end do
       h = mix32(ieor(h, OBJ_SET))
    case default
       h = mix32(ieor(v%ref, v%tag))
    end select
  end function gce_coll_hash

  ! Clojure's `compare`, which is Comparable and NOT just numbers. It
  ! answered 0 for anything non-numeric, so (compare "a" "b") was 0 and
  ! (sort ["b" "a"]) would have come back in its original order without
  ! erroring -- a wrong answer, not a missing feature. Verified against
  ! clj:
  !
  !   nil is less than everything     (compare nil 1)     => -1
  !   false is less than true         (compare false true)=> -1
  !   text is lexicographic           (compare "a" "b")   => -1
  !   a vector is by COUNT first      (compare [1 2] [1]) =>  1
  !   ...then element by element      (compare [1] [2])   => -1
  !   mixed types throw               (compare 1 "a")     => ClassCastException
  !
  ! Only the sign matters to a caller, but Clojure answers -1/0/1 for
  ! these cases and so does this.
  recursive function compare_values(a0, b0, ok) result(c)
    type(gc_value), intent(in) :: a0, b0
    logical, intent(out) :: ok
    integer :: c
    type(gc_value) :: a, b
    character(len=:), allocatable :: sa, sb
    integer :: i, na, nb
    a = strip_meta(a0)
    b = strip_meta(b0)
    ok = .true.
    c = 0

    ! nil sorts before everything, and is equal only to itself.
    if (a%tag == GCT_NIL .and. b%tag == GCT_NIL) return
    if (a%tag == GCT_NIL) then
       c = -1
       return
    end if
    if (b%tag == GCT_NIL) then
       c = 1
       return
    end if

    if (a%tag == GCT_BOOL .and. b%tag == GCT_BOOL) then
       if (a%ival == b%ival) then
          c = 0
       else if (a%ival == 0) then
          c = -1
       else
          c = 1
       end if
       return
    end if

    if (is_number(a) .and. is_number(b)) then
       if (num_lt(a, b)) then
          c = -1
       else if (num_lt(b, a)) then
          c = 1
       end if
       return
    end if

    if (a%tag == GCT_CHAR .and. b%tag == GCT_CHAR) then
       if (a%ival < b%ival) then
          c = -1
       else if (a%ival > b%ival) then
          c = 1
       end if
       return
    end if

    ! Strings, symbols and keywords compare by their text, and only
    ! against their own kind -- a string is not a keyword.
    if (a%tag == b%tag .and. &
         (a%tag == GCT_STR .or. a%tag == GCT_SYM .or. a%tag == GCT_KEY)) then
       sa = gc_ref_text(a%ref)
       sb = gc_ref_text(b%ref)
       if (sa < sb) then
          c = -1
       else if (sa > sb) then
          c = 1
       end if
       return
    end if

    ! A vector is Comparable; a list is not, and clj throws for one.
    if (gc_kind(a) == OBJ_VECTOR .and. gc_kind(b) == OBJ_VECTOR) then
       na = gcv_count(a)
       nb = gcv_count(b)
       if (na < nb) then
          c = -1
          return
       else if (na > nb) then
          c = 1
          return
       end if
       do i = 0, na - 1
          c = compare_values(gcv_nth(a, i), gcv_nth(b, i), ok)
          if (.not. ok) return
          if (c /= 0) return
       end do
       return
    end if

    ok = .false.
  end function compare_values

  ! A `value`-kind array holding a collection's elements. This is what
  ! to-array answers, because `sort` mutates the array it gets.
  function value_array_of(coll, roots) result(out)
    type(gc_value), intent(in) :: coll
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, vecd, run
    integer, allocatable :: ext(:), lows(:)
    character(len=:), allocatable :: err
    integer :: n, h, i, base
    base = vs_enter(2)
    vecd = coll_to_vector(coll, roots)
    call vs_set(base + 1, vecd)
    n = gcv_count(vs_get(base + 1))
    allocate(ext(1), lows(1))
    ext(1) = n
    lows(1) = 0
    h = gcna_new("value", ext, lows, err)
    if (h == 0) then
       call fail(err)
       call vs_leave(base)
       out = gc_nil()
       return
    end if
    run = gc_vec(max(1, n), [roots, [vs_get(base + 1)]])
    call vs_set(base + 2, run)
    out = gc_obj(OBJ_ARRAY, [vs_get(base + 2)], [roots, [vs_get(base + 1), vs_get(base + 2)]])
    call gc_set_i1(out, h)
    call gc_set_i2(out, -1)   ! owns its handle; not a slice
    do i = 1, n
       call array_put(out, i, gcv_nth(vs_get(base + 1), i - 1))
    end do
    call vs_leave(base)
  end function value_array_of

  ! One comparator call, following AFunction.compare (AFunction.java):
  ! a function that answers a BOOLEAN is a predicate, so (sort > coll)
  ! works -- true means "less", and false asks the reverse question to
  ! tell 0 from 1. Anything else is a number and its sign is the answer.
  recursive function comparator_call(cmp, x, y) result(c)
    type(gc_value), intent(in) :: cmp, x, y
    integer :: c
    type(gc_value) :: r, args2, rev
    integer :: base
    base = vs_enter(4)
    call vs_set(base + 1, cmp)
    ! A VECTOR, not a list: apply counts its arguments with
    ! gcv_count to pick an arity, and a list counts as zero --
    ! which is how a two-argument comparator produced
    ! "no matching arity".
    !
    ! Each conj is rooted before the next allocation: two
    ! allocations as arguments to one call means the second can
    ! collect the first.
    args2 = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 2, args2)
    args2 = gcv_conj(vs_get(base + 2), x, [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 2, args2)
    args2 = gcv_conj(vs_get(base + 2), y, [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 2, args2)
    r = apply(vs_get(base + 1), vs_get(base + 2))
    call vs_set(base + 3, r)
    c = 0
    if (has_error) then
       call vs_leave(base)
       return
    end if
    if (r%tag == GCT_BOOL) then
       if (truthy(r)) then
          c = -1
       else
          rev = gcv_empty([vs_get(base + 1)])
          call vs_set(base + 2, rev)
          rev = gcv_conj(vs_get(base + 2), y, [vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 2, rev)
          rev = gcv_conj(vs_get(base + 2), x, [vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 2, rev)
          r = apply(vs_get(base + 1), vs_get(base + 2))
          if (.not. has_error) then
             if (truthy(r)) c = 1
          end if
       end if
    else if (is_number(r)) then
       if (num_lt(r, gc_int(0))) then
          c = -1
       else if (num_lt(gc_int(0), r)) then
          c = 1
       end if
    end if
    call vs_leave(base)
  end function comparator_call

  ! java.util.Arrays/sort -- IN PLACE, and STABLE, which Clojure's sort
  ! docstring promises: "equal elements will not be reordered". A
  ! merge sort rather than a quicksort for exactly that reason; the
  ! extra array is the price of the guarantee.
  recursive subroutine array_sort(arr, cmp)
    type(gc_value), intent(in) :: arr, cmp
    integer :: n, width, i, lo, mid, hi
    type(gc_value), allocatable :: buf(:), src(:)
    integer :: base
    n = seq_len(arr)
    if (n < 2) return
    base = vs_enter(2)
    call vs_set(base + 1, arr)
    call vs_set(base + 2, cmp)
    allocate(src(n), buf(n))
    do i = 1, n
       src(i) = array_elem(vs_get(base + 1), i)
    end do
    ! Bottom-up: merge runs of 1, then 2, then 4... Taking from the
    ! left run on a tie is what keeps it stable.
    width = 1
    do while (width < n)
       lo = 1
       do while (lo <= n)
          mid = min(lo + width - 1, n)
          hi = min(lo + 2 * width - 1, n)
          call merge_run(src, buf, lo, mid, hi, vs_get(base + 2))
          if (has_error) then
             call vs_leave(base)
             return
          end if
          lo = hi + 1
       end do
       src = buf
       width = 2 * width
    end do
    do i = 1, n
       call array_put(vs_get(base + 1), i, src(i))
    end do
    call vs_leave(base)
  end subroutine array_sort

  recursive subroutine merge_run(src, buf, lo, mid, hi, cmp)
    type(gc_value), intent(in) :: src(:)
    type(gc_value), intent(inout) :: buf(:)
    integer, intent(in) :: lo, mid, hi
    type(gc_value), intent(in) :: cmp
    integer :: i, j, k
    i = lo
    j = mid + 1
    k = lo
    do while (i <= mid .and. j <= hi)
       ! <= 0 keeps the LEFT element first on a tie: stability.
       if (comparator_call(cmp, src(j), src(i)) < 0) then
          buf(k) = src(j)
          j = j + 1
       else
          buf(k) = src(i)
          i = i + 1
       end if
       if (has_error) return
       k = k + 1
    end do
    do while (i <= mid)
       buf(k) = src(i)
       i = i + 1
       k = k + 1
    end do
    do while (j <= hi)
       buf(k) = src(j)
       j = j + 1
       k = k + 1
    end do
  end subroutine merge_run

  ! --- struct maps --------------------------------------------------
  !
  ! A struct map IS a map. PersistentStructMap on the JVM is a storage
  ! optimisation -- a shared key basis plus a flat value array, so N
  ! instances of the same struct do not each carry their keys -- and
  ! nothing about its BEHAVIOUR differs from a map. Verified against
  ! clj:
  !
  !   (defstruct point :x :y)
  !   (struct point 1 2)         => {:x 1, :y 2}
  !   (struct point 1)           => {:x 1, :y nil}  basis keys are
  !   (struct-map point :x 1)    => {:x 1, :y nil}  always present
  !   (struct-map point :x 1 :z 9) => {:x 1, :y nil, :z 9}  extras ok
  !   (map? (struct point 1 2))  => true
  !
  ! So clotran's structs are its maps, and the basis is a VECTOR of the
  ! keys -- which is all createSlotMap's Def is, minus the key->slot
  ! index that only matters when the values live in an array.
  !
  ! This is here because clojure/pprint.clj uses defstruct, so without
  ! it pprint does not load -- and clojure.test-clojure.reflect does
  ! (:use clojure.pprint), so reflect does not load either.

  ! createSlotMap: the basis, as a vector of the keys.
  function struct_basis(args, roots) result(out)
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, keys
    keys = strip_meta(gcv_nth(args, 0))
    if (keys%tag == GCT_NIL) then
       call fail("Must supply keys")
       out = gc_nil()
       return
    end if
    out = coll_to_vector(keys, roots)
  end function struct_basis

  ! A map holding every basis key, each nil. Both constructors start
  ! here, because an unsupplied basis key is PRESENT and nil rather
  ! than absent -- that is what makes (struct point 1) answer
  ! {:x 1, :y nil} rather than {:x 1}.
  function struct_blank(basis, roots) result(out)
    type(gc_value), intent(in) :: basis
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, tmp
    integer :: i, base
    base = vs_enter(2)
    call vs_set(base + 1, basis)
    tmp = gca_empty([roots, [basis]])
    call vs_set(base + 2, tmp)
    do i = 0, gcv_count(vs_get(base + 1)) - 1
       tmp = gca_assoc(vs_get(base + 2), gcv_nth(vs_get(base + 1), i), gc_nil(), &
            [roots, [vs_get(base + 1), vs_get(base + 2)]])
       call vs_set(base + 2, tmp)
    end do
    out = vs_get(base + 2)
    call vs_leave(base)
  end function struct_blank

  ! construct: the values positionally against the basis.
  function struct_construct(args, roots) result(out)
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, basis, vals, tmp
    integer :: i, n, base
    base = vs_enter(3)
    basis = strip_meta(gcv_nth(args, 0))
    call vs_set(base + 1, basis)
    vals = coll_to_vector(gcv_nth(args, 1), [roots, [basis]])
    call vs_set(base + 2, vals)
    n = gcv_count(vs_get(base + 2))
    if (n > gcv_count(vs_get(base + 1))) then
       call fail("Too many arguments to struct constructor")
       call vs_leave(base)
       out = gc_nil()
       return
    end if
    tmp = struct_blank(vs_get(base + 1), [roots, [vs_get(base + 2)]])
    call vs_set(base + 3, tmp)
    do i = 0, n - 1
       tmp = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 1), i), &
            gcv_nth(vs_get(base + 2), i), &
            [roots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)]])
       call vs_set(base + 3, tmp)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function struct_construct

  ! create: key/value pairs, which may name keys outside the basis.
  function struct_create(args, roots) result(out)
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, basis, kvs, tmp
    integer :: i, n, base
    base = vs_enter(3)
    basis = strip_meta(gcv_nth(args, 0))
    call vs_set(base + 1, basis)
    kvs = coll_to_vector(gcv_nth(args, 1), [roots, [basis]])
    call vs_set(base + 2, kvs)
    n = gcv_count(vs_get(base + 2))
    if (mod(n, 2) /= 0) then
       call fail("No value supplied for key: " // &
            gcp_str(gcv_nth(vs_get(base + 2), n - 1), .true.))
       call vs_leave(base)
       out = gc_nil()
       return
    end if
    tmp = struct_blank(vs_get(base + 1), [roots, [vs_get(base + 2)]])
    call vs_set(base + 3, tmp)
    do i = 0, n - 2, 2
       tmp = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 2), i), &
            gcv_nth(vs_get(base + 2), i + 1), &
            [roots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)]])
       call vs_set(base + 3, tmp)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function struct_create

  ! getAccessor: the KEY itself. Clojure returns a closure over the
  ! value slot, which is faster than a lookup on the JVM; here the
  ! values are in a map and a keyword already looks itself up, so
  ! ((accessor point :x) p) is (:x p). What is lost is the
  ! "Accessor/struct mismatch" error for applying one struct's
  ! accessor to another -- see DEVIATIONS.
  function struct_accessor(args, roots) result(out)
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, basis, k
    integer :: i
    basis = strip_meta(gcv_nth(args, 0))
    k = gcv_nth(args, 1)
    out = gc_nil()
    do i = 0, gcv_count(basis) - 1
       if (gc_equal(gcv_nth(basis, i), strip_meta(k))) then
          out = k
          return
       end if
    end do
    call fail("Not a key of struct")
  end function struct_accessor

  recursive function deep_equal(a0, b0, roots) result(eq)
    type(gc_value), intent(in) :: a0, b0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: a, b
    logical :: eq
    type(gc_value), allocatable :: ka(:), va(:), kb(:), vb(:)
    integer :: i
    logical :: hit
    type(gc_value) :: r

    ! METADATA IS INVISIBLE TO EQUALITY, as gc_equal already says
    ! and as Clojure agrees: (= (with-meta [1 2] {:a 1}) [1 2]) is
    ! true. The wrapper used to reach the sequential test, which
    ! answered false for it, so a hinted collection compared by
    ! identity.
    a = strip_meta(a0)
    b = strip_meta(b0)

    ! An INSTANCE decides its own equality, through the equiv its
    ! type declares. Two records with the same fields are equal in
    ! Clojure and two deftypes never are, and that difference is not
    ! something this function can see -- it is written in
    ! core_deftype.clj, per type. Falling through to identity made
    ! (= (->P 1 2) (->P 1 2)) false.
    if (gc_kind(a) == OBJ_INST) then
       r = inst_equiv(a, b, hit)
       if (hit) then
          eq = truthy(r)
          return
       end if
    end if

    ! SEQUENTIAL EQUALITY, element at a time. Both references do it the
    ! same way and neither indexes:
    !
    !   ASeq.equiv          ISeq ms = RT.seq(obj);
    !                       for(ISeq s = seq(); s != null;
    !                           s = s.next(), ms = ms.next())
    !                         if(ms == null || !Util.equiv(...)) false;
    !                       return ms == null;
    !
    !   equiv-sequential    (loop [xs (seq x) ys (seq y)]
    !                         (cond (nil? xs) (nil? ys)
    !                               (nil? ys) false
    !                               (= (first xs) (first ys))
    !                                 (recur (next xs) (next ys))
    !                               :else false))
    !
    ! The count is a SHORTCUT, not the method, and is taken only when
    ! both sides are counted -- see counted_p. Counting first
    ! unconditionally, which is what this did, cannot work for a lazy
    ! seq: it realises the whole thing, and an infinite one never
    ! returns. Walking stops at the first difference or the first end.
    !
    ! ClojureScript writes this in Clojure, so it is not host-bound and
    ! being in Fortran here is a choice, not a seam. SEAMS.md bucket B.
    if (sequential_p(a) .and. sequential_p(b)) then
       if (counted_p(a) .and. counted_p(b)) then
          if (seq_count(a) /= seq_count(b)) then
             eq = .false.
             return
          end if
       end if
       block
         type(gc_value) :: sa, sb, tmp
         integer :: base
         base = vs_enter(6)
         call vs_set(base + 1, a)
         call vs_set(base + 2, b)
         tmp = to_seq(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 2)])
         call vs_set(base + 3, tmp)
         tmp = to_seq(vs_get(base + 2), [vs_get(base + 2), vs_get(base + 3)])
         call vs_set(base + 4, tmp)
         eq = .false.
         do
            sa = vs_get(base + 3)
            sb = vs_get(base + 4)
            ! to_seq answers nil for an exhausted seq, which is
            ! RT.seq returning null and (seq x) returning nil. Both
            ! ending together is the only way to be equal.
            if (sa%tag == GCT_NIL) then
               eq = (sb%tag == GCT_NIL)
               exit
            end if
            if (sb%tag == GCT_NIL) exit

            ! Each element onto the stack BEFORE the other is taken:
            ! two allocations as arguments to one call means the
            ! second can collect the first.
            tmp = sq_first(vs_get(base + 3), [vs_get(base + 3), vs_get(base + 4)])
            call vs_set(base + 5, tmp)
            tmp = sq_first(vs_get(base + 4), &
                 [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5)])
            call vs_set(base + 6, tmp)
            if (.not. deep_equal(vs_get(base + 5), vs_get(base + 6), &
                 [vs_get(base + 3), vs_get(base + 4)])) exit

            tmp = sq_rest(vs_get(base + 3), [vs_get(base + 3), vs_get(base + 4)])
            call vs_set(base + 5, tmp)
            tmp = to_seq(vs_get(base + 5), [vs_get(base + 4), vs_get(base + 5)])
            call vs_set(base + 3, tmp)
            tmp = sq_rest(vs_get(base + 4), [vs_get(base + 3), vs_get(base + 4)])
            call vs_set(base + 6, tmp)
            tmp = to_seq(vs_get(base + 6), [vs_get(base + 3), vs_get(base + 6)])
            call vs_set(base + 4, tmp)
         end do
         call vs_leave(base)
       end block
       return
    end if

    ! A SET equals a set with the same members, and both references say
    ! it the same way: other must be a set, the counts must match, and
    ! every element of one must be in the other.
    !
    !   APersistentSet.equiv   if(!(obj instanceof Set)) return false;
    !                          if(m.size() != size()) return false;
    !                          for(Object aM : m) if(!contains(aM)) false;
    !
    !   PersistentHashSet      (and (set? other)
    !                               (== (count coll) (count other))
    !                               every element contains?)
    !
    ! A set fell past this to gc_equal, which compares references, so
    ! (= #{1 2} #{1 2}) was false -- two literals spelled the same way
    ! were not equal.
    !
    ! Membership goes through gca_contains, so an element that is itself
    ! a COLLECTION is matched by identity rather than by value, which is
    ! the standing decision gc_equal records for map keys. Scalars,
    ! which is what a set almost always holds, are exact.
    if (gc_kind(a) == OBJ_SET .and. gc_kind(b) == OBJ_SET) then
       eq = (gca_count(gc_slot(a, 1)) == gca_count(gc_slot(b, 1)))
       if (.not. eq) return
       call gca_entries(gc_slot(a, 1), ka, va)
       do i = 1, size(ka)
          if (.not. gca_contains(gc_slot(b, 1), ka(i))) then
             eq = .false.
             return
          end if
       end do
       return
    end if

    if (gca_is(a) .and. gca_is(b)) then
       eq = (gca_count(a) == gca_count(b))
       if (.not. eq) return
       call gca_entries(a, ka, va)
       call gca_entries(b, kb, vb)
       do i = 1, size(ka)
          if (.not. gca_contains(b, ka(i))) then
             eq = .false.
             return
          end if
          if (.not. deep_equal(va(i), gca_get(b, ka(i)), roots)) then
             eq = .false.
             return
          end if
       end do
       return
    end if

    eq = gc_equal(a, b)
  end function deep_equal

  ! SEQUENTIAL, which is what decides sequential equality. Clojure asks
  ! `obj instanceof Sequential || obj instanceof List` (ASeq.equiv) and
  ! ClojureScript asks `(sequential? y)` (equiv-sequential) -- the same
  ! question, and neither is asking "is this a list or a vector".
  !
  ! This used to answer list-or-vector ONLY, so a LAZY SEQ was not
  ! sequential: (= (map inc [0 1]) [1 2]) fell through to identity and
  ! came back false. Anything built by map, filter, range or map-indexed
  ! is a lazy seq, so comparing one against a literal vector -- which is
  ! what a test usually does -- was silently wrong.
  !
  ! A SET and a bare STRING are deliberately absent: neither is
  ! Sequential, and clj agrees that (= #{1 2} [1 2]) and
  ! (= "ab" [\a \b]) are both false. (seq "ab") IS sequential, and that
  ! is the OBJ_SEQ case rather than the string case.
  function sequential_p(v0) result(yes)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v
    logical :: yes
    v = strip_meta(v0)
    yes = gcl_is(v) .or. gcv_is(v) .or. &
         gc_kind(v) == OBJ_LAZY .or. gc_kind(v) == OBJ_SEQ .or. gc_kind(v) == OBJ_CHUNKSEQ
  end function sequential_p

  ! COUNTED: the count is known without walking. Both references use a
  ! count as a shortcut and BOTH gate it on the two sides being counted
  ! -- `this instanceof Counted && obj instanceof Counted` in
  ! ASeq.equiv, `(and (counted? x) (counted? y))` in equiv-sequential --
  ! because counting a lazy seq realises it, and an infinite one never
  ! finishes. (= (range) [1 2]) terminates in Clojure precisely because
  ! nothing asks it for a count.
  !
  ! A seq VIEW over a vector could answer its count, but the JVM's
  ! ChunkedSeq is not Counted either, and being conservative here only
  ! ever costs a shortcut.
  function counted_p(v0) result(yes)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v
    logical :: yes
    v = strip_meta(v0)
    yes = gcl_is(v) .or. gcv_is(v)
  end function counted_p

  function seq_count(v) result(n)
    type(gc_value), intent(in) :: v
    integer :: n
    n = 0
    if (gcl_is(v)) then
       n = gcl_count(v)
    else if (gcv_is(v)) then
       n = gcv_count(v)
    end if
  end function seq_count


  ! ---- the seq abstraction -------------------------------------
  !
  ! ONE place knows about concrete collection types: to_seq. Every
  ! other seq operation works on seqs alone, so adding a seqable type
  ! means teaching to_seq about it and nothing else.
  !
  ! This replaces a chain of `if list ... else if vector ... else if
  ! lazy` repeated at every call site, which is not a style point:
  ! each chain was an independent chance to forget a branch, and one
  ! of them did -- rest silently missed vectors, which made reduce
  ! return its first element and last return its first.
  !
  ! nil for an EMPTY collection, which is what makes (if (seq c) ...)
  ! the idiomatic emptiness test rather than a special case.
  ! Metadata is transparent here, as it is everywhere that RECOGNISES
  ! a value. Clojure keeps metadata on the collection, so a vector with
  ! metadata is still a vector; ours wraps it, and a funnel that did not
  ! unwrap made (count (with-meta [1 2] m)) zero and (first ...) nil.
  ! DEVIATIONS.md 5.
  recursive function to_seq(v0, roots) result(out)
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, v
    integer :: base

    v = strip_meta(v0)
    out = gc_nil()
    if (v%tag == GCT_NIL) return

    ! Already a seq: lists and lazy seqs implement it directly.
    if (gcl_is(v)) then
       if (gcl_count(v) > 0) out = v
       return
    end if
    if (gc_kind(v) == OBJ_LAZY) then
       call gce_force(v)
       if (gc_i1(v) == LAZY_CONS) out = v
       if (gc_i1(v) == LAZY_DELEG) out = gc_slot(v, 2)
       return
    end if
    if (gc_kind(v) == OBJ_SEQ) then
       if (seq_len(gc_slot(v, 1)) > gc_i1(v)) out = v
       return
    end if
    if (gc_kind(v) == OBJ_CHUNKSEQ) then
       ! a ChunkedCons is a seq; an empty chunk defers to what follows
       if (chunk_count(gc_slot(v, 1)) > 0) then
          out = v
       else
          out = to_seq(gc_slot(v, 2), roots)
       end if
       return
    end if

    ! Indexable: a VIEW, not a copy. rest is then O(1).
    if (seq_len(v) == 0) return
    base = vs_enter(1)
    call vs_set(base + 1, v)
    out = gc_obj(OBJ_SEQ, [vs_get(base + 1)], roots)
    call gc_set_i1(out, 0)
    call vs_leave(base)
  end function to_seq

  ! How many elements an indexable value has. The only other place
  ! that needs to know concrete types, and deliberately next to
  ! to_seq so the two stay in step.
  function seq_len(v) result(n)
    type(gc_value), intent(in) :: v
    integer :: n
    n = 0
    if (gcv_is(v)) then
       n = gcv_count(v)
    else if (gc_kind(v) == OBJ_SET) then
       ! A set counts and seqs as its ELEMENTS, not as the {k v}
       ! pairs of the map backing it.
       n = gca_count(gc_slot(v, 1))
    else if (gca_is(v)) then
       n = gca_count(v)
    else if (v%tag == GCT_STR) then
       n = gc_ref_len(v%ref)
    else if (gc_kind(v) == OBJ_ARRAY) then
       ! An array seqs as its elements, so `sort` can hand the array
       ! it just sorted back to `seq`. The length is the FIRST extent,
       ! matching alength: a rank-2 array is 2 rows, not 6 numbers.
       block
         integer, allocatable :: ext(:)
         ext = array_own_extents(v)
         if (size(ext) > 0) n = ext(1)
       end block
    end if
  end function seq_len

  ! The i-th element of an indexable value (0-based). A map yields
  ! its entries as two-element vectors, which is what makes
  ! (first {:a 1}) an entry and lets destructuring walk a map.
  function seq_elem(v, i, roots) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base

    out = gc_nil()
    if (gcv_is(v)) then
       out = gcv_nth(v, i)
    else if (gc_kind(v) == OBJ_ARRAY) then
       ! Rank 1 yields an element, deeper yields a row -- the same
       ! split (aget a i) makes. This is what lets `sort` read back
       ! the array it just sorted with (seq a).
       if (array_own_rank(v) <= 1) then
          out = array_elem(v, i + 1)
       else
          out = array_make_slice(v, [i], roots)
       end if
    else if (gc_kind(v) == OBJ_SET) then
       block
         type(gc_value), allocatable :: sks(:), svs(:)
         call gca_entries(gc_slot(v, 1), sks, svs)
         if (i >= 0 .and. i < size(sks)) out = sks(i+1)
       end block
    else if (v%tag == GCT_STR) then
       block
         character(len=:), allocatable :: t
         t = gc_ref_text(v%ref)
         if (i >= 0 .and. i < len(t)) out = gc_char(t(i+1:i+1))
       end block
    else if (gca_is(v)) then
       call gca_entries(v, ks, vls)
       if (i >= 0 .and. i < size(ks)) then
          base = vs_enter(1)
          out = gcv_empty(roots)
          call vs_set(base + 1, out)
          out = gcv_conj(vs_get(base + 1), ks(i+1), roots)
          call vs_set(base + 1, out)
          out = gcv_conj(vs_get(base + 1), vls(i+1), roots)
          call vs_leave(base)
       end if
    end if
  end function seq_elem

  ! first/rest work on SEQS only. Anything else is seq'd first.
  recursive function sq_first(v0, roots) result(out)
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, s, v
    integer :: base

    v = strip_meta(v0)
    out = gc_nil()
    base = vs_enter(1)
    s = to_seq(v, roots)
    call vs_set(base + 1, s)
    if (gcl_is(vs_get(base + 1))) then
       out = gcl_first(vs_get(base + 1))
    else if (gc_kind(vs_get(base + 1)) == OBJ_LAZY) then
       out = gc_slot(vs_get(base + 1), 2)
    else if (gc_kind(vs_get(base + 1)) == OBJ_SEQ) then
       out = seq_elem(gc_slot(vs_get(base + 1), 1), gc_i1(vs_get(base + 1)), roots)
    else if (gc_kind(vs_get(base + 1)) == OBJ_CHUNKSEQ) then
       out = chunk_nth(gc_slot(vs_get(base + 1), 1), 0)
    end if
    call vs_leave(base)
  end function sq_first

  ! Always a seq, never nil -- Clojure's `rest`, as opposed to `next`.
  ! For a view this bumps the index and shares the source, so walking
  ! a vector is O(1) per step rather than copying the tail each time.
  recursive function sq_rest(v0, roots) result(out)
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, s, v
    integer :: base

    v = strip_meta(v0)
    base = vs_enter(2)
    s = to_seq(v, roots)
    call vs_set(base + 1, s)
    out = gcl_empty(roots)
    if (gcl_is(vs_get(base + 1))) then
       out = gcl_rest(vs_get(base + 1), roots)
    else if (gc_kind(vs_get(base + 1)) == OBJ_LAZY) then
       out = gc_slot(vs_get(base + 1), 3)
    else if (gc_kind(vs_get(base + 1)) == OBJ_SEQ) then
       out = gc_obj(OBJ_SEQ, [gc_slot(vs_get(base + 1), 1)], &
            [vs_get(base + 1)])
       call gc_set_i1(out, gc_i1(vs_get(base + 1)) + 1)
    else if (gc_kind(vs_get(base + 1)) == OBJ_CHUNKSEQ) then
       ! ChunkedCons.more: the chunk less its first while that leaves
       ! any, else what follows (or () when nothing does)
       if (chunk_count(gc_slot(vs_get(base + 1), 1)) > 1) then
          call vs_set(base + 2, make_chunk(gc_slot(gc_slot(vs_get(base + 1), 1), 1), &
               gc_i1(gc_slot(vs_get(base + 1), 1)) + 1, gc_i2(gc_slot(vs_get(base + 1), 1)), [vs_get(base + 1)]))
          out = gc_obj(OBJ_CHUNKSEQ, [vs_get(base + 2), gc_slot(vs_get(base + 1), 2), gc_nil()], &
               [vs_get(base + 1), vs_get(base + 2)])
       else
          out = gc_slot(vs_get(base + 1), 2)
          if (out%tag == GCT_NIL) out = gcl_empty(roots)
       end if
    end if
    call vs_leave(base)
  end function sq_rest

  ! How many elements a seq yields. Realises a lazy seq, as (count)
  ! must.
  recursive function sq_count(v0, roots) result(n)
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: s, v
    integer :: base, n

    v = strip_meta(v0)
    n = 0
    if (v%tag == GCT_NIL) return
    if (gcl_is(v)) then
       n = gcl_count(v)
       return
    end if
    if (gc_kind(v) == OBJ_SEQ) then
       n = seq_len(gc_slot(v, 1)) - gc_i1(v)
       return
    end if
    if (gc_kind(v) == OBJ_CHUNK) then
       n = chunk_count(v)
       return
    end if
    if (gc_kind(v) == OBJ_LAZY) then
       if (gc_i1(v) == LAZY_DELEG) then
          n = sq_count(gc_slot(v, 2), roots)
          return
       end if
    end if
    if (gc_kind(v) == OBJ_CHUNKSEQ) then
       n = chunk_count(gc_slot(v, 1)) + sq_count(gc_slot(v, 2), roots)
       return
    end if
    if (gc_kind(v) /= OBJ_LAZY) then
       n = seq_len(v)
       return
    end if
    base = vs_enter(1)
    call vs_set(base + 1, v)
    do
       s = to_seq(vs_get(base + 1), roots)
       call vs_set(base + 1, s)
       ! s, not vs_get(...)%tag: neither compiler will take a
       ! component off a function result (NOTES.md gotcha).
       if (s%tag == GCT_NIL) exit
       n = n + 1
       s = sq_rest(vs_get(base + 1), roots)
       call vs_set(base + 1, s)
    end do
    call vs_leave(base)
  end function sq_count

  ! Clojure's truthiness: everything except nil and false.
  ! The type of a value, as a keyword. Everything else that asks
  ! what a value IS gets written in Clojure on top of this, which
  ! is how real Clojure does it too (instance? plus defns).
  recursive function type_name(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    ! METADATA DOES NOT CHANGE A TYPE. Clojure carries it on the object
    ! -- Symbol implements IObj -- so ^:static x is still a Symbol.
    ! Ours is a wrapper, which would otherwise make every hinted name
    ! in core.clj answer :object and fail (instance? Symbol name).
    ! Transparent here; only `meta` looks at the wrapper.
    if (gc_kind(v) == OBJ_META) then
       s = type_name(gc_slot(v, 1))
       return
    end if
    select case (v%tag)
    case (GCT_NIL);  s = "nil"
    case (GCT_BOOL); s = "boolean"
    case (GCT_INT);  s = "int"
    case (GCT_REAL); s = "double"
    case (GCT_RATIO); s = "ratio"
    case (GCT_CHAR); s = "char"
    case (GCT_STR);  s = "string"
    case (GCT_SYM);  s = "symbol"
    case (GCT_KEY);  s = "keyword"
    case default
       select case (gc_kind(v))
       case (OBJ_CONS);    s = "list"
       case (OBJ_VECTOR);  s = "vector"
       case (OBJ_MAP, OBJ_HAMT); s = "map"
       case (OBJ_SET);     s = "set"
       case (OBJ_CLOSURE, OBJ_BUILTIN); s = "fn"
       case (OBJ_MULTIFN); s = "multifn"
       case (OBJ_REGEX);   s = "regex"
       case (OBJ_MATCHER); s = "matcher"
       case (OBJ_WRITER); s = "writer"
       case (OBJ_SB); s = "string-builder"
       case (OBJ_ERR); s = "error"
       case (OBJ_LAZY);    s = "lazy-seq"
       ! A seq VIEW over an indexable. Without this it fell to
       ! "object", which matched no print-method and no host
       ! supertype, so (prn (seq ["a"])) printed (a) rather than
       ! ("a") -- print-method's :default reaches print-simple,
       ! which does not quote. is_instance already expected the
       ! name "seq" here.
       case (OBJ_SEQ);     s = "seq"
       case (OBJ_CHUNKSEQ); s = "seq"
       case (OBJ_CHUNK);   s = "chunk"
       case (OBJ_CHUNKBUF); s = "chunk-buffer"
       case (OBJ_VAR);     s = "var"
       case (OBJ_NS);      s = "ns"
       ! A deftype instance answers with its OWN class name, so
       ! (class x) is the keyword a protocol's :impls map is keyed by
       ! and extend-type on the type reaches it.
       case (OBJ_DELAY);   s = "delay"
       case (OBJ_ARRAY);   s = "array"
       case (OBJ_INST);    s = class_text(v)
       case (OBJ_TYPE);    s = "class"
       case default;       s = "object"
       end select
    end select
  end function type_name

  ! (instance? Class x). The class arrives as the keyword a class
  ! literal evaluates to, so this is a name-to-type-tag table.
  !
  ! An unlisted class is FALSE, not an error, and that is the honest
  ! answer rather than a shortcut: clotran has no BigInteger, so
  ! nothing is an instance of one. The interfaces are the interesting
  ! entries -- Sequential and Named cover several tags each, which is
  ! exactly what an interface is.
  ! What `.toString` answers, which is what `str` is: core.clj's str is
  ! (. x (toString)), so this is the one path both the builtin str and
  ! the host member take.
  !
  ! For almost everything that IS the print form -- clotran renders a
  ! host object as #<atom 1>, #<multifn f>, and .toString hands back
  ! the same text. Three kinds separate the two, each because the host
  ! object has real text of its own: a StringBuilder and a Pattern hold
  ! theirs in slot 1, and a NAMESPACE'S toString is its NAME.
  !
  ! That last one is not cosmetic. namespace-munge is literally
  ! (.replace (str ns) \- \_), so (str *ns*) is what deftype builds its
  ! class name out of -- printing the wrapper made it
  ! "#<ns clojure.core>.Point". Clojure separates the two the same way:
  ! Namespace.toString is "user", while print-method shows
  ! #object[clojure.lang.Namespace ...]. Doing it in the PRINTER on
  ! *print-readably* instead got (str *ns*) right and (str [*ns*])
  ! wrong, because a collection's toString prints its elements.
  function to_string_text(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    type(gc_value) :: inner
    if (gc_kind(v) == OBJ_SB .or. gc_kind(v) == OBJ_REGEX .or. &
         gc_kind(v) == OBJ_NS) then
       inner = gc_slot(v, 1)
       s = gcp_str(inner, .false.)
    else
       s = gcp_str(v, .false.)
    end if
  end function to_string_text

  ! The Fortran element kind a Clojure type argument asks for.
  !
  ! `make-array` takes a CLASS -- (make-array Integer/TYPE 3) -- and a
  ! class literal evaluates to a keyword here, so this is a keyword to
  ! kind-name table. The primitive types map onto real Fortran kinds,
  ! which is the whole point: an int array IS integer(4), contiguous,
  ! and can be handed to a Fortran routine.
  !
  ! Everything else -- Object, String, a deftype's own class -- becomes
  ! "value", whose storage is a GC run rather than a typed buffer,
  ! because its elements are clotran values holding heap references.
  ! Clojure's Object[] is that case.
  function array_kind_for(tv) result(kind)
    type(gc_value), intent(in) :: tv
    character(len=:), allocatable :: kind
    character(len=:), allocatable :: t
    type(gc_value) :: v
    v = strip_meta(tv)
    kind = "value"
    if (v%tag /= GCT_KEY) return
    t = gc_ref_text(v%ref)
    select case (t)
    case ("Integer/TYPE", "int");      kind = "int4"
    case ("Long/TYPE", "long");        kind = "int8"
    case ("Double/TYPE", "double");    kind = "real8"
    case ("Float/TYPE", "float");      kind = "real4"
    case ("Boolean/TYPE", "boolean");  kind = "logical"
    case ("Short/TYPE", "Byte/TYPE");  kind = "int4"
    end select
  end function array_kind_for

  ! (java.lang.reflect.Array/newInstance type n) and the N-dimensional
  ! form, whose second argument is itself an int ARRAY -- core.clj's own
  ! make-array builds one with aset-int and passes it, so this has to
  ! accept both shapes.
  !
  ! Clojure's N-dimensional array is an array OF ARRAYS; ours is one
  ! rank-N Fortran array. DEVIATIONS 24 is what that costs (no ragged
  ! rows) and PLAN item 9 is what it buys (one contiguous column-major
  ! block, which is what a BLAS routine takes).
  recursive function array_new_instance(args, roots) result(out)
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, dimv, e
    character(len=:), allocatable :: kind, err
    integer, allocatable :: ext(:), lows(:)
    integer :: nd, k, h
    type(gc_value) :: run

    out = gc_nil()
    kind = array_kind_for(gcv_nth(args, 0))
    dimv = strip_meta(gcv_nth(args, 1))

    if (gc_kind(dimv) == OBJ_ARRAY) then
       nd = gcna_total(gc_i1(dimv))
       allocate(ext(nd), lows(nd))
       do k = 1, nd
          e = array_elem(dimv, k)
          ext(k) = e%ival
          lows(k) = 0
       end do
    else
       allocate(ext(1), lows(1))
       ext(1) = dimv%ival
       lows(1) = 0
    end if

    h = gcna_new(kind, ext, lows, err)
    if (h == 0) then
       call fail(err)
       return
    end if
    run = gc_nil()
    if (kind == "value") run = gc_vec(max(1, gcna_total(h)), roots)
    out = gc_obj(OBJ_ARRAY, [run], [roots, [run]])
    call gc_set_i1(out, h)
    call gc_set_i2(out, -1) ! owns the handle -- not a slice
  end function array_new_instance

  ! --- array views: a base array, or a SLICE sharing its buffer -----
  !
  ! Clojure's own aget/aset always pass exactly ONE index per call and
  ! recur: core.clj's aget is
  !   ([array idx & idxs] (apply aget (aget array idx) idxs))
  ! so (aget m 1 2) on a rank-2 array is (aget (aget m 1) 2), and
  ! (aget m 1) has to hand back something that is itself an array --
  ! Clojure's own [[I is exactly that, one real object per row.
  !
  ! Ours is one Fortran buffer, so "the row at index 1" cannot be a
  ! second buffer -- it has to be a VIEW over the same one. In
  ! column-major, fixing the FIRST index of a(d1,d2,...,dR) gives
  ! elements at flat positions {i1 + k*d1 : k=0..(d2*...*dR - 1)} --
  ! a uniformly STRIDED sequence, not a contiguous block. Measured in
  ! NOTES.md's Fortran experiment and folded here in general form:
  ! every array view is (handle, offset, stride, extents), where a
  ! BASE array is the degenerate view (0, 1, its own full extents).
  !
  ! WHO OWNS THE HANDLE. A slice shares its parent's handle rather
  ! than claiming one of its own, so only ONE of them may release it
  ! when collected -- releasing on the wrong one frees a live parent's
  ! buffer or double-frees an already-dead one. i2 is the marker:
  ! -1 means "I own this handle" (a base array's own base_offset would
  ! otherwise be a plain 0, so -1 is never mistaken for one); any
  ! offset >= 0 means "I am a view, I do not own it." See
  ! gce_finalize_obj.

  ! Whether `arr` is a slice (has its own offset/stride/extents in
  ! slot 2) rather than a base array (whose shape lives in the
  ! registry under its handle).
  logical function array_is_slice(arr)
    type(gc_value), intent(in) :: arr
    array_is_slice = gcv_is(gc_slot(arr, 2))
  end function array_is_slice

  integer function array_own_offset(arr)
    type(gc_value), intent(in) :: arr
    if (array_is_slice(arr)) then
       array_own_offset = gc_i2(arr)
    else
       array_own_offset = 0
    end if
  end function array_own_offset

  integer function array_own_stride(arr)
    type(gc_value), intent(in) :: arr
    type(gc_value) :: sl
    type(gc_value) :: elt
    if (array_is_slice(arr)) then
       sl = gc_slot(arr, 2)
       elt = gcv_nth(sl, 0)
       array_own_stride = elt%ival
    else
       array_own_stride = 1
    end if
  end function array_own_stride

  integer function array_own_rank(arr)
    type(gc_value), intent(in) :: arr
    type(gc_value) :: sl
    if (array_is_slice(arr)) then
       sl = gc_slot(arr, 2)
       array_own_rank = gcv_count(sl) - 1
    else
       array_own_rank = gcna_rank(gc_i1(arr))
    end if
  end function array_own_rank

  function array_own_extents(arr) result(e)
    type(gc_value), intent(in) :: arr
    integer, allocatable :: e(:)
    type(gc_value) :: sl, elt
    integer :: i
    if (array_is_slice(arr)) then
       sl = gc_slot(arr, 2)
       allocate(e(gcv_count(sl) - 1))
       do i = 1, size(e)
          elt = gcv_nth(sl, i)
          e(i) = elt%ival
       end do
    else
       e = gcna_extents(gc_i1(arr))
    end if
  end function array_own_extents

  ! Consumes the leading `size(subs)` dimensions of arr's OWN shape,
  ! folding them into a single (offset, stride) pair -- the arithmetic
  ! verified in the Fortran experiment: consuming one more dimension
  ! multiplies the running stride by that dimension's extent and adds
  ! subs(k)*stride to the running offset. `ok` is false on an
  ! out-of-range subscript or a wrong number of them.
  subroutine array_fold(arr, subs, out_offset, out_stride, ok)
    type(gc_value), intent(in) :: arr
    integer, intent(in) :: subs(:)
    integer, intent(out) :: out_offset, out_stride
    logical, intent(out) :: ok
    integer, allocatable :: extents(:)
    integer :: k, own_rank
    ok = .false.
    own_rank = array_own_rank(arr)
    if (size(subs) > own_rank) return
    extents = array_own_extents(arr)
    out_offset = array_own_offset(arr)
    out_stride = array_own_stride(arr)
    do k = 1, size(subs)
       if (subs(k) < 0 .or. subs(k) >= extents(k)) return
       out_offset = out_offset + subs(k) * out_stride
       out_stride = out_stride * extents(k)
    end do
    ok = .true.
  end subroutine array_fold

  ! A SLICE consuming the leading `size(subs)` dimensions of `arr`,
  ! sharing its handle (and its value-run, for a `value` array) rather
  ! than copying anything. `size(subs)` must be less than arr's own
  ! rank -- a full set of subscripts is an ELEMENT, not a slice, and
  ! callers check that first.
  function array_make_slice(arr, subs, roots) result(out)
    type(gc_value), intent(in) :: arr
    integer, intent(in) :: subs(:)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, shapevec, tmp
    integer, allocatable :: extents(:)
    integer :: new_offset, new_stride, k, own_rank
    logical :: ok
    integer :: base

    out = gc_nil()
    call array_fold(arr, subs, new_offset, new_stride, ok)
    if (.not. ok) return

    base = vs_enter(3)
    call vs_set(base + 1, arr)
    own_rank = array_own_rank(vs_get(base + 1))
    extents = array_own_extents(vs_get(base + 1))

    tmp = gcv_empty([vs_get(base + 1), roots])
    call vs_set(base + 2, tmp)
    tmp = gcv_conj(vs_get(base + 2), gc_int(new_stride), &
         [vs_get(base + 1), vs_get(base + 2), roots])
    call vs_set(base + 2, tmp)
    do k = size(subs) + 1, own_rank
       tmp = gcv_conj(vs_get(base + 2), gc_int(extents(k)), &
            [vs_get(base + 1), vs_get(base + 2), roots])
       call vs_set(base + 2, tmp)
    end do
    shapevec = vs_get(base + 2)
    call vs_set(base + 3, shapevec)

    ! Slot 1 (the value-run, for a `value`-kind array) is SHARED with
    ! the parent, unchanged -- the run holds every element of the
    ! whole base array, and this view's offset/stride already say
    ! which of them are ours.
    out = gc_obj(OBJ_ARRAY, [gc_slot(vs_get(base + 1), 1), vs_get(base + 3)], &
         [vs_get(base + 1), vs_get(base + 3), roots])
    call gc_set_i1(out, gc_i1(vs_get(base + 1)))
    call gc_set_i2(out, new_offset)
    call vs_leave(base)
  end function array_make_slice

  ! Writes one element, by a 1-based index into the array's OWN
  ! (possibly sliced) column-major shape. Translated to the real
  ! buffer/run position via array_own_offset/array_own_stride, which
  ! is what makes this correct whether `arr` is a base array or a
  ! view: the array's own elements, in its own column-major order,
  ! sit at real position = own_offset + own_stride*(k-1) + 1 -- a
  ! single linear map, not a per-dimension decomposition, because
  ! that is what folding a column-major layout through a fixed prefix
  ! of indices reduces to. Verified in the Fortran experiment this
  ! module's header cites.
  subroutine array_put(arr, at, val)
    type(gc_value), intent(in) :: arr, val
    integer, intent(in) :: at
    character(len=:), allocatable :: kn
    type(gc_value) :: v
    integer :: h, real_at
    logical :: ok
    if (gc_kind(arr) /= OBJ_ARRAY) return
    h = gc_i1(arr)
    real_at = array_own_offset(arr) + array_own_stride(arr) * (at - 1) + 1
    kn = gcna_kind(h)
    v = strip_meta(val)
    if (kn == "value") then
       call gc_vec_set(gc_slot(arr, 1), real_at, v)
    else if (kn == "logical") then
       call gcna_set_logical(h, real_at, truthy(v), ok)
    else if (v%tag == GCT_INT) then
       call gcna_set_int(h, real_at, v%ival, ok)
    else
       call gcna_set_real(h, real_at, num_dbl(v), ok)
    end if
  end subroutine array_put

  ! One element, by a 1-based index into the array's OWN shape -- see
  ! array_put, its partner.
  function array_elem(arr, at) result(out)
    type(gc_value), intent(in) :: arr
    integer, intent(in) :: at
    type(gc_value) :: out
    character(len=:), allocatable :: kn
    integer :: h, real_at
    integer(8) :: iv
    real(gc_dp) :: rv
    logical :: lv, ok
    out = gc_nil()
    if (gc_kind(arr) /= OBJ_ARRAY) return
    h = gc_i1(arr)
    real_at = array_own_offset(arr) + array_own_stride(arr) * (at - 1) + 1
    kn = gcna_kind(h)
    if (kn == "value") then
       out = gc_vec_get(gc_slot(arr, 1), real_at)
    else if (kn == "logical") then
       call gcna_get_logical(h, real_at, lv, ok)
       if (ok) out = gc_bool(lv)
    else if (kn == "int4" .or. kn == "int8") then
       call gcna_get_int(h, real_at, iv, ok)
       if (ok) out = gc_int(iv)
    else
       call gcna_get_real(h, real_at, rv, ok)
       if (ok) out = gc_real(rv)
    end if
  end function array_elem

  ! The class name of a type object, or of an instance's type.
  ! A function result cannot be the left of a %, so the slot walk
  ! lands in a local first.
  function class_text(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    type(gc_value) :: t
    t = v
    if (gc_kind(t) == OBJ_INST) t = gc_slot(t, 1)
    t = gc_slot(t, 1)
    s = gc_ref_text(t%ref)
  end function class_text

  ! The text of an interned symbol, string or keyword. Same reason.
  function class_of_text(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    type(gc_value) :: t
    t = v
    s = gc_ref_text(t%ref)
  end function class_of_text

  ! Whether a class DECLARED under one name answers to another.
  !
  ! Exact, or the asked-for name is unqualified and matches the last
  ! segment of the declared one. That second case is what `import`
  ! buys in Clojure -- (deftype Point ...) expands to (import
  ! clojure.core.Point), which makes the bare `Point` name the class
  ! in that namespace. clotran's import is a no-op (there is no class
  ! table to bind into; a class is recognised by the shape of its
  ! name), so the short name has to be accepted here instead.
  !
  ! The cost is that it is accepted EVERYWHERE, not only where the
  ! import ran: two namespaces each defining a Point make `Point`
  ! ambiguous, and the last one defined wins. DEVIATIONS.md.
  logical function class_matches(declared, asked)
    character(len=*), intent(in) :: declared, asked
    integer :: i, last_dot
    class_matches = (declared == asked)
    if (class_matches) return
    if (index(asked, ".") > 0) return
    last_dot = 0
    do i = 1, len(declared)
       if (declared(i:i) == ".") last_dot = i
    end do
    if (last_dot == 0) return
    class_matches = (declared(last_dot+1:) == asked)
  end function class_matches

  ! Whether a vector of class keywords names this class.
  logical function key_in_vector(vec, name)
    type(gc_value), intent(in) :: vec
    character(len=*), intent(in) :: name
    type(gc_value) :: k
    integer :: i
    key_in_vector = .false.
    do i = 0, gcv_count(vec) - 1
       k = gcv_nth(vec, i)
       if (k%tag /= GCT_KEY) cycle
       if (class_matches(gc_ref_text(k%ref), name)) then
          key_in_vector = .true.
          return
       end if
    end do
  end function key_in_vector

  function is_instance(cls, v) result(yes)
    type(gc_value), intent(in) :: cls, v
    logical :: yes
    character(len=:), allocatable :: c, t
    yes = .false.
    if (cls%tag /= GCT_KEY) return
    c = gc_ref_text(cls%ref)
    t = type_name(v)
    ! A deftype/reify instance is an instance of its own class and of
    ! everything its :implements list names -- which is the whole
    ! hierarchy there is, and enough for find-protocol-impl, whose
    ! first question is (instance? (:on-interface protocol) x).
    if (gc_kind(strip_meta(v)) == OBJ_INST) then
       yes = class_matches(t, c) .or. (c == "Object") .or. &
            key_in_vector(gc_slot(gc_slot(strip_meta(v), 1), 4), c)
       return
    end if
    select case (c)
    case ("clojure.lang.Symbol");   yes = (t == "symbol")
    case ("clojure.lang.Keyword");  yes = (t == "keyword")
    case ("clojure.lang.Var");      yes = (t == "var")
    case ("clojure.lang.Namespace"); yes = (t == "ns")
    case ("clojure.lang.IFn", "clojure.lang.Fn"); yes = (t == "fn" .or. t == "multifn")
    case ("clojure.lang.MultiFn"); yes = (t == "multifn")
    case ("clojure.lang.IDeref", "clojure.lang.IPending")
       ! core.clj's deref is (if (instance? clojure.lang.IDeref ref)
       ! (.deref ref) (deref-future ref)), so a thing that derefs has
       ! to ANSWER to IDeref or it silently takes the future path --
       ! which is how @(delay 1) came back as the delay itself.
       yes = (t == "atom" .or. t == "delay" .or. t == "var")
    case ("clojure.lang.Delay"); yes = (t == "delay")
    ! The concrete classes `class` answers (class_name_of), so that
    ! (instance? (class x) x) holds and a condp on them can ask.
    case ("clojure.lang.PersistentVector"); yes = (t == "vector")
    case ("clojure.lang.PersistentArrayMap", "clojure.lang.PersistentHashMap"); yes = (t == "map")
    case ("clojure.lang.PersistentHashSet"); yes = (t == "set")
    case ("clojure.lang.PersistentList"); yes = (t == "list")
    case ("clojure.lang.LazySeq"); yes = (t == "lazy-seq" .and. gc_i2(strip_meta(v)) /= 1)
    case ("clojure.lang.LongRange", "clojure.lang.Range"); yes = (t == "lazy-seq" .and. gc_i2(strip_meta(v)) == 1)
    ! What reduce hands to a host .reduce rather than walking as a seq:
    ! the JVM's LongRange, PersistentVector and PersistentList do.
    case ("clojure.lang.IReduceInit", "clojure.lang.IReduce")
       yes = (t == "vector" .or. t == "list" .or. (t == "lazy-seq" .and. gc_i2(strip_meta(v)) == 1))
    case ("clojure.lang.IChunkedSeq"); yes = is_chunked_seq(strip_meta(v))
    case ("clojure.lang.IChunk", "clojure.lang.ArrayChunk"); yes = (gc_kind(strip_meta(v)) == OBJ_CHUNK)
    case ("clojure.lang.ChunkBuffer"); yes = (gc_kind(strip_meta(v)) == OBJ_CHUNKBUF)
    case ("clojure.lang.ChunkedCons"); yes = (gc_kind(strip_meta(v)) == OBJ_CHUNKSEQ)
    case ("clojure.lang.PersistentVector$ChunkedSeq", "clojure.lang.Cons"); yes = (t == "seq")
    case ("clojure.lang.Atom"); yes = (t == "atom")
    case ("clojure.lang.AFunction", "clojure.lang.AFn"); yes = (t == "fn")
    case ("StringBuilder", "java.lang.StringBuilder"); yes = (t == "string-builder")
    case ("java.io.PrintWriter", "java.io.Writer"); yes = (t == "writer")
    ! Everything but nil is an Object.
    case ("Object", "java.lang.Object"); yes = (v%tag /= GCT_NIL)
    ! Both spellings. clojure.string imports these -- (:import
    ! (java.util.regex Pattern Matcher)) -- and then writes the
    ! SHORT name, so (instance? Pattern re) has to answer the same
    ! as the qualified form. Without it clojure.string/replace
    ! fell through every branch of its cond and threw
    ! "Invalid match arg" on a perfectly good pattern.
    case ("java.util.regex.Pattern", "Pattern"); yes = (t == "regex")
    case ("java.util.regex.Matcher", "Matcher"); yes = (t == "matcher")
    case ("clojure.lang.Reduced")
       ! A Reduced is the one-key map (reduced x) builds, so instance?
       ! asks for the key. Without this reduce returned the WRAPPER
       ! instead of unwrapping it on an early exit.
       yes = gca_contains(strip_meta(v), gc_key("clotran/reduced", [v]))
    case ("Throwable", "java.lang.Throwable", "Exception", "java.lang.Exception", &
          "Error", "IExceptionInfo", "clojure.lang.IExceptionInfo", &
          "ExceptionInfo", "clojure.lang.ExceptionInfo")
       yes = (t == "error")
    case ("clojure.lang.ISeq");     yes = (t == "list" .or. t == "lazy-seq" .or. t == "seq")
    case ("clojure.lang.IPersistentList"); yes = (t == "list")
    case ("clojure.lang.IPersistentVector", "clojure.lang.Indexed"); yes = (t == "vector")
    case ("clojure.lang.IPersistentMap", "java.util.Map"); yes = (t == "map")
    case ("clojure.lang.IPersistentSet"); yes = (t == "set")
    case ("clojure.lang.Associative"); yes = (t == "map" .or. t == "vector")
    case ("clojure.lang.Counted"); &
         yes = (t == "list" .or. t == "vector" .or. t == "map" .or. &
                t == "set" .or. t == "string")
    case ("clojure.lang.Sequential"); &
         yes = (t == "list" .or. t == "vector" .or. t == "lazy-seq" .or. t == "seq")
    case ("clojure.lang.IPersistentCollection", "clojure.lang.Seqable"); &
         yes = (t == "list" .or. t == "vector" .or. t == "map" .or. &
                t == "set" .or. t == "lazy-seq" .or. t == "seq")
    case ("clojure.lang.Named"); yes = (t == "symbol" .or. t == "keyword")
    case ("clojure.lang.IMeta")
       ! IMeta is "can report its metadata", and a function can:
       ! core.clj:210 makes `meta` itself
       !   (if (instance? clojure.lang.IMeta x) (.meta x))
       ! so answering false here makes (meta (with-meta (fn [] 1) {:a 1}))
       ! nil. Split from IObj below, which a function must NOT claim.
       yes = (t == "symbol" .or. t == "list" .or. t == "vector" .or. &
              t == "map" .or. t == "set" .or. t == "var" .or. t == "fn")
    case ("clojure.lang.IObj")
       ! NOT "fn", and that is a deviation with a reason. print-method's
       ! :default is
       !   (if (instance? IObj o) (print-method (vary-meta o ...) w)
       !                          (print-simple o w))
       ! so anything answering IObj here must have a print-method that
       ! dispatch can actually REACH, or :default calls itself on the
       ! same object forever. A closure had none: host_super has no
       ! entry for fn, core_print registers nothing on IFn, and
       ! print-method Object is unreachable because print-object needs
       ! String/format. So (prn (fn [x] x)) segfaulted.
       !
       ! Answering false sends a closure to print-simple, which is
       ! (.write w (str o)) -- #<fn>, the shape every other host object
       ! here prints in.
       !
       ! IMeta is answered separately, just above, and a function DOES
       ! claim it: `meta` is (if (instance? clojure.lang.IMeta x) ...)
       ! at core.clj:210, so collapsing the two made
       ! (meta (with-meta (fn [] 1) {:a 1})) nil. They were one case
       ! here and had to stop being one.
       !
       ! The real fix is String/format: it lets print-object run, which
       ! lets every type fall back to Object. DEVIATIONS 18 and 21 want
       ! it too.
       yes = (t == "symbol" .or. t == "list" .or. t == "vector" .or. &
              t == "map" .or. t == "set" .or. t == "var")
    case ("String", "java.lang.String", "CharSequence"); yes = (t == "string")
    case ("Character", "java.lang.Character"); yes = (t == "char")
    case ("Boolean", "java.lang.Boolean"); yes = (t == "boolean")
    case ("Long", "java.lang.Long", "Integer", "java.lang.Integer"); yes = (t == "int")
    case ("Double", "java.lang.Double", "Float"); yes = (t == "double")
    case ("Ratio", "clojure.lang.Ratio"); yes = (t == "ratio")
    case ("Number", "java.lang.Number")
       ! A Ratio is a Number on the JVM too, so (number? 1/2) is true.
       yes = (t == "int" .or. t == "double" .or. t == "ratio")
    end select
  end function is_instance

  ! Every element of a seqable, as a vector. The three host `create`
  ! statics all take a collection, so they all start here.
  recursive function coll_to_vector(coll, roots) result(out)
    type(gc_value), intent(in) :: coll
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, walk, item
    integer :: base

    base = vs_enter(2)
    out = gcv_empty(roots)
    call vs_set(base + 1, out)
    walk = to_seq(coll, roots)
    call vs_set(base + 2, walk)
    do while (walk%tag /= GCT_NIL)
       item = sq_first(vs_get(base + 2), [vs_get(base + 1)])
       out = gcv_conj(vs_get(base + 1), item, [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 1, out)
       walk = to_seq(sq_rest(vs_get(base + 2), [vs_get(base + 1)]), [vs_get(base + 1)])
       call vs_set(base + 2, walk)
    end do
    out = vs_get(base + 1)
    call vs_leave(base)
  end function coll_to_vector

  ! Every element of a seq, as a proper list.
  recursive function seq_to_list(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, items
    integer :: base, i

    base = vs_enter(2)
    items = coll_to_vector(v, roots)
    call vs_set(base + 1, items)
    out = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 2, out)
    do i = gcv_count(vs_get(base + 1)) - 1, 0, -1
       out = gcl_cons(gcv_nth(vs_get(base + 1), i), vs_get(base + 2), &
            [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, out)
    end do
    out = vs_get(base + 2)
    call vs_leave(base)
  end function seq_to_list

  ! Numeric comparison across int and double. Comparing %ival alone
  ! made (< 1.5 2.0) read two garbage integers; one place to decide it
  ! means < > <= >= and compare cannot disagree.
  logical function num_lt(a, b)
    type(gc_value), intent(in) :: a, b
    if (a%tag == GCT_INT .and. b%tag == GCT_INT) then
       num_lt = (a%ival < b%ival)
    else
       num_lt = (num_dbl(a) < num_dbl(b))
    end if
  end function num_lt

  function num_dbl(v) result(d)
    type(gc_value), intent(in) :: v
    real(gc_dp) :: d
    if (v%tag == GCT_REAL) then
       d = v%rval
    else if (v%tag == GCT_RATIO) then
       ! Every comparison goes through here, so without this a ratio
       ! would compare as its NUMERATOR: (< 1/3 1/2) would be 1 < 1.
       d = real(gc_numerator(v), gc_dp) / real(gc_denominator(v), gc_dp)
    else
       d = real(v%ival, gc_dp)
    end if
  end function num_dbl

  logical function is_ratio(v)
    type(gc_value), intent(in) :: v
    is_ratio = (v%tag == GCT_RATIO)
  end function is_ratio

  ! Whether a value is any of clotran's numbers.
  logical function is_number(v)
    type(gc_value), intent(in) :: v
    is_number = (v%tag == GCT_INT .or. v%tag == GCT_REAL .or. v%tag == GCT_RATIO)
  end function is_number

  ! The host supertypes of a class, one per call. `supers` walks them
  ! through .getInterfaces, and multimethod dispatch and
  ! find-protocol-impl walk them the same way. The class is what
  ! `class` answers (class_name_of), so the keys here are CLASS NAMES,
  ! spelt as a class literal evaluates: java.lang stripped, everything
  ! else in full. Order is specific-to-general, because the caller
  ! takes the first match: print-dup has a method on Long and another
  ! on Number, and only the Long one prints 1 rather than
  ! #=(java.lang.Long. "1").
  function host_super(dv, i, roots) result(k)
    type(gc_value), intent(in) :: dv, roots
    integer, intent(in) :: i
    type(gc_value) :: k
    character(len=:), allocatable :: t

    k = gc_nil()
    if (dv%tag /= GCT_KEY) return
    t = gc_ref_text(dv%ref)

    ! A DEFTYPE'S SUPERTYPES ARE THE INTERFACES IT DECLARED. The
    ! table below is fixed because clotran's built-in types are, but
    ! a deftype names its own, so they are read from the type rather
    ! than listed here.
    !
    ! Without this, a multimethod registered on an interface never
    ! fires for a record: print-method has a method on
    ! clojure.lang.IRecord, a record dispatches as :clojure.core.P,
    ! and nothing connected the two -- so dispatch fell to :default,
    ! which asks (instance? clojure.lang.IObj o), which a record IS,
    ! and re-entered print-method on the same object. Printing one
    ! segfaulted on a stack that never unwound.
    block
      type(gc_value) :: ty, ifaces
      ty = find_type(t)
      if (gc_kind(ty) == OBJ_TYPE) then
         ifaces = gc_slot(ty, 4)
         if (i >= 1 .and. i <= gcv_count(ifaces)) k = gcv_nth(ifaces, i - 1)
         return
      end if
    end block

    ! THE CHAIN IS BUILT, THEN INDEXED. Every class this table knows
    ! ends at Object, where core.clj's catch-all print-method is
    ! registered; a class it does not know -- a function, an array --
    ! has no supertypes and falls to :default, which for a function
    ! is DEVIATIONS.md 23's territory and not this function's.
    block
      character(len=36) :: chain(8)
      integer :: cnt
      logical :: known
      cnt = 0
      known = .true.
      select case (t)
      case ("clojure.lang.PersistentVector")
         chain(1:5) = [character(len=36) :: "clojure.lang.IPersistentVector", &
              "java.util.List", "java.util.RandomAccess", &
              "clojure.lang.IPersistentCollection", "java.util.Collection"]
         cnt = 5
      case ("clojure.lang.PersistentArrayMap")
         chain(1:4) = [character(len=36) :: "clojure.lang.IPersistentMap", "java.util.Map", &
              "clojure.lang.IPersistentCollection", "java.util.Collection"]
         cnt = 4
      case ("clojure.lang.PersistentHashSet")
         chain(1:4) = [character(len=36) :: "clojure.lang.IPersistentSet", "java.util.Set", &
              "clojure.lang.IPersistentCollection", "java.util.Collection"]
         cnt = 4
      case ("clojure.lang.PersistentList")
         chain(1:5) = [character(len=36) :: "clojure.lang.IPersistentList", "clojure.lang.ISeq", &
              "java.util.List", "clojure.lang.IPersistentCollection", "java.util.Collection"]
         cnt = 5
      case ("clojure.lang.LazySeq", "clojure.lang.PersistentVector$ChunkedSeq", "clojure.lang.Cons", &
            "clojure.lang.LongRange", "clojure.lang.Range", "clojure.lang.ChunkedCons")
         chain(1:4) = [character(len=36) :: "clojure.lang.ISeq", "java.util.List", &
              "clojure.lang.IPersistentCollection", "java.util.Collection"]
         cnt = 4
      case ("clojure.lang.Var", "clojure.lang.Atom", "clojure.lang.Delay")
         chain(1) = "clojure.lang.IDeref"
         cnt = 1
      case ("String")
         chain(1) = "CharSequence"
         cnt = 1
      case ("Long", "Double", "clojure.lang.Ratio")
         chain(1) = "Number"
         cnt = 1
      case ("clojure.lang.Keyword", "clojure.lang.Symbol", "Character", "Boolean", &
            "java.util.regex.Pattern", "java.util.regex.Matcher", "clojure.lang.Namespace", &
            "clojure.lang.MultiFn", "StringBuilder", "java.io.PrintWriter")
         continue
      case default
         if (is_throwable_class(t)) then
            chain(1) = "Throwable"
            cnt = 1
         else
            known = .false.
         end if
      end select
      if (known) then
         cnt = cnt + 1
         chain(cnt) = "Object"
      end if
      if (i >= 1 .and. i <= cnt) k = gc_key(trim(chain(i)), [roots])
    end block
  end function host_super

  ! What `class` answers: the canonical class of a value, spelt as a
  ! class literal evaluates (java.lang stripped), so (= (class "a")
  ! String) holds, (condp = (class x) String ...) takes its branch,
  ! and a protocol's :impls map keyed by the literal is hit directly.
  ! The type TAG (type_name) stays internal: host.clj's predicates
  ! read it through clotran-type, and messages use it. Where clotran
  ! has one type for several of Clojure's classes -- one map, one
  ! seq view -- the most common class stands for it.
  recursive function class_name_of(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    type(gc_value) :: c
    if (gc_kind(v) == OBJ_META) then
       s = class_name_of(gc_slot(v, 1))
       return
    end if
    select case (v%tag)
    case (GCT_NIL);   s = ""
    case (GCT_BOOL);  s = "Boolean"
    case (GCT_INT);   s = "Long"
    case (GCT_REAL);  s = "Double"
    case (GCT_RATIO); s = "clojure.lang.Ratio"
    case (GCT_CHAR);  s = "Character"
    case (GCT_STR);   s = "String"
    case (GCT_SYM);   s = "clojure.lang.Symbol"
    case (GCT_KEY);   s = "clojure.lang.Keyword"
    case default
       select case (gc_kind(v))
       case (OBJ_CONS);    s = "clojure.lang.PersistentList"
       case (OBJ_VECTOR);  s = "clojure.lang.PersistentVector"
       case (OBJ_MAP, OBJ_HAMT); s = "clojure.lang.PersistentArrayMap"
       case (OBJ_SET);     s = "clojure.lang.PersistentHashSet"
       case (OBJ_CLOSURE, OBJ_BUILTIN); s = "clojure.lang.AFunction"
       case (OBJ_MULTIFN); s = "clojure.lang.MultiFn"
       case (OBJ_REGEX);   s = "java.util.regex.Pattern"
       case (OBJ_MATCHER); s = "java.util.regex.Matcher"
       case (OBJ_WRITER);  s = "java.io.PrintWriter"
       case (OBJ_SB);      s = "StringBuilder"
       case (OBJ_ERR)
          ! Its own class, as constructed, spelt as the literal is:
          ! core.clj writes (ExceptionInfo. ...) under an import.
          c = gc_slot(v, 1)
          s = class_key(gc_ref_text(c%ref))
       case (OBJ_LAZY)
          s = "clojure.lang.LazySeq"
          if (gc_i2(v) == 1) then
             ! Clojure has two range classes and picks between them on
             ! the bounds: LongRange for integers, Range for anything
             ! else. Ours is one cell either way, so the head decides.
             s = "clojure.lang.Range"
             if (gc_i1(v) == LAZY_CONS) then
                if (tag_of(gc_slot(v, 2)) == GCT_INT) s = "clojure.lang.LongRange"
             else if (tag_of(gcv_nth(gc_slot(v, 1), 0)) == GCT_INT) then
                s = "clojure.lang.LongRange"
             end if
          end if
       case (OBJ_SEQ);     s = "clojure.lang.PersistentVector$ChunkedSeq"
       case (OBJ_CHUNKSEQ); s = "clojure.lang.ChunkedCons"
       case (OBJ_CHUNK);   s = "clojure.lang.ArrayChunk"
       case (OBJ_CHUNKBUF); s = "clojure.lang.ChunkBuffer"
       case (OBJ_VAR);     s = "clojure.lang.Var"
       case (OBJ_NS);      s = "clojure.lang.Namespace"
       case (OBJ_DELAY);   s = "clojure.lang.Delay"
       case (OBJ_ATOM);    s = "clojure.lang.Atom"
       case (OBJ_ARRAY);   s = "array"
       case (OBJ_INST);    s = class_text(v)
       case (OBJ_TYPE);    s = "Class"
       case default;       s = "Object"
       end select
    end select
  end function class_name_of

  ! The classpath, and the extensions. One root was enough while only
  ! core.clj was being loaded, but Clojure's own test suite lives under
  ! test/clj and requires clojure.test-helper from there. First root
  ! holding the file wins, which is what a classpath means.
  !
  ! Extensions, in order: .cljf is clotran's own (a file that uses the
  ! fortran namespace, say), .cljc is portable Clojure with reader
  ! conditionals, .clj is JVM Clojure. A library that ships a .cljc
  ! beside a .clj wrote the .cljc for other hosts, so it wins here;
  ! RT.load prefers the .clj, which is right for the host the .clj was
  ! written for. DEVIATIONS 33.
  function classpath_find(rel) result(path)
    character(len=*), intent(in) :: rel
    character(len=:), allocatable :: path, cand
    character(len=1024) :: roots(5)
    character(len=4), parameter :: exts(3) = [character(len=4) :: "cljf", "cljc", "clj"]
    logical :: there
    integer :: i, e

    roots(1) = "src/clj"
    roots(2) = "test/clj"
    roots(3) = "."
    roots(4) = gce_home() // "/src/clj"
    roots(5) = gce_home() // "/test/clj"
    ! The src/clj spelling is the fallback too, so a genuinely missing
    ! file still reports the path a reader would expect to see.
    path = "src/clj/" // rel // ".clj"
    do e = 1, 3
       do i = 1, 5
          cand = trim(roots(i)) // "/" // rel // "." // trim(exts(e))
          inquire(file=cand, exist=there)
          if (there) then
             path = cand
             return
          end if
       end do
    end do
  end function classpath_find

  ! The namespace an alias names in the CURRENT namespace, or nil.
  ! (require '[clojure.template :as temp]) records temp -> that
  ! namespace in slot 3, and this is the lookup that makes
  ! temp/do-template mean something.
  function alias_target(name, roots) result(nsv)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nsv
    nsv = alias_in(gcn_current(roots), name, roots)
  end function alias_target

  ! The same lookup in a NAMED namespace.
  function alias_in(nsv0, name, roots) result(nsv)
    type(gc_value), intent(in) :: nsv0
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nsv, al
    nsv = gc_nil()
    if (gc_kind(nsv0) /= OBJ_NS) return
    al = gc_slot(nsv0, 3)
    if (.not. gca_is(al)) return
    nsv = gca_get(al, gc_sym(name, roots))
  end function alias_in

  function make_writer(unit, roots) result(w)
    integer, intent(in) :: unit
    type(gc_value), intent(in) :: roots
    type(gc_value) :: w
    w = gc_obj(OBJ_WRITER, [gc_nil()], [roots])
    call gc_set_i1(w, unit)
  end function make_writer

  function text_of(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    if (v%tag == GCT_STR) then
       s = gc_ref_text(v%ref)
    else if (v%tag == GCT_NIL) then
       s = ""
    else
       s = gcp_str(v, .false.)
    end if
  end function text_of

  ! A LOOKUP, for the three collections that answer one: a map by
  ! key, an instance by field, and a SET BY MEMBERSHIP. That last
  ! is the one that was missing -- (get #{:at} :at) and
  ! (:at #{:at}) both answered nil, where Clojure answers :at,
  ! because a set's contents live one slot down and nothing
  ! unwrapped them. cl_format.clj asks exactly that of its
  ! allowed-flags set for every directive it compiles, so every
  ! flag looked illegal and clojure.pprint would not load.
  function coll_get(coll0, k) result(out)
    type(gc_value), intent(in) :: coll0, k
    type(gc_value) :: out, coll, kk
    character(len=:), allocatable :: t
    coll = strip_meta(coll0)
    kk = strip_meta(k)
    if (gc_kind(coll) == OBJ_SET) then
       out = gca_get(gc_slot(coll, 1), k)
    else if (gcv_is(coll) .and. kk%tag == GCT_INT) then
       ! A VECTOR IS ASSOCIATIVE BY INDEX. (get v 0) is its first
       ! element, not nil -- Associative is what Indexed answers
       ! to -- and clojure.data's diff-associative walks a vector
       ! with (range (count v)) as its keys, so without this every
       ! sequential diff came back all-nil.
       out = gc_nil()
       if (kk%ival >= 0 .and. kk%ival < int(gcv_count(coll), gc_ip)) &
            out = gcv_nth(coll, int(kk%ival))
    else if (coll%tag == GCT_STR .and. kk%tag == GCT_INT) then
       out = gc_nil()
       t = gc_ref_text(coll%ref)
       if (kk%ival >= 0 .and. kk%ival < int(len(t), gc_ip)) &
            out = gc_char(t(int(kk%ival) + 1:int(kk%ival) + 1))
    else
       out = gca_get(coll, k)
    end if
  end function coll_get

  ! Whether that lookup would find anything.
  function coll_has(coll0, k) result(yes)
    type(gc_value), intent(in) :: coll0, k
    type(gc_value) :: coll, kk
    logical :: yes
    coll = strip_meta(coll0)
    kk = strip_meta(k)
    if (gc_kind(coll) == OBJ_SET) then
       yes = gca_contains(gc_slot(coll, 1), k)
    else if (gcv_is(coll)) then
       ! contains? on a vector asks whether the INDEX is in
       ! range, which is the question its keys answer.
       yes = (kk%tag == GCT_INT)
       if (yes) yes = (kk%ival >= 0 .and. kk%ival < int(gcv_count(coll), gc_ip))
    else if (coll%tag == GCT_STR) then
       yes = (kk%tag == GCT_INT)
       if (yes) yes = (kk%ival >= 0 .and. &
            kk%ival < int(gc_ref_len(coll%ref), gc_ip))
    else
       yes = gca_contains(coll, k)
    end if
  end function coll_has

  ! What a String.indexOf needle MEANS. A string is itself, and a
  ! character -- or an integer, which is how Java spells one
  ! here -- is the single character it names.
  function needle_text(v0) result(s)
    type(gc_value), intent(in) :: v0
    character(len=:), allocatable :: s
    type(gc_value) :: v
    v = strip_meta(v0)
    if (v%tag == GCT_INT .or. v%tag == GCT_CHAR) then
       s = achar(int(max(0_gc_ip, min(255_gc_ip, v%ival)), kind=4))
    else
       s = text_of(v)
    end if
  end function needle_text

  ! The integer a value carries, or zero.
  function strip_int(v0) result(i)
    type(gc_value), intent(in) :: v0
    integer(gc_ip) :: i
    type(gc_value) :: v
    v = strip_meta(v0)
    i = 0
    if (v%tag == GCT_INT .or. v%tag == GCT_CHAR) i = v%ival
  end function strip_int

  ! conj of ONE item. Collection-polymorphic on purpose, and the one
  ! place that should NOT go through seq: (conj [1] 2) appends,
  ! (conj (list 1) 2) prepends, (conj {:a 1} [:b 2]) assocs, and
  ! (conj {:a 1} {:b 2}) merges. That difference is the feature.
  recursive function conj1(coll0, x, roots) result(out)
    type(gc_value), intent(in) :: coll0, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, coll
    integer :: base

    coll = strip_meta(coll0)
    base = vs_enter(2)
    call vs_set(base + 1, coll)
    call vs_set(base + 2, x)

    if (gcv_is(coll)) then
       out = gcv_conj(vs_get(base + 1), vs_get(base + 2), roots)
    else if (gc_kind(coll) == OBJ_SET) then
       out = gc_obj(OBJ_SET, [gca_assoc(gc_slot(vs_get(base + 1), 1), &
            vs_get(base + 2), vs_get(base + 2), roots)], roots)
    else if (gca_is(coll)) then
       if (x%tag == GCT_NIL) then
          ! CONJ OF NIL ONTO A MAP IS A NO-OP. APersistentMap.cons
          ! walks (RT/seq o), and the seq of nil is nil, so the
          ! loop never runs and the map comes back unchanged.
          ! Treating nil as a pair assoc'd nil to nil instead, and
          ! (merge m nil) is (conj m nil) -- so every map that
          ! passed through merge grew a spurious nil entry.
          ! clojure.data/diff folds with merge over [nil nil nil].
          out = vs_get(base + 1)
       else if (gca_is(vs_get(base + 2))) then
          block
            type(gc_value), allocatable :: kk(:), vv(:)
            type(gc_value) :: mm
            integer :: j
            call gca_entries(vs_get(base + 2), kk, vv)
            mm = vs_get(base + 1)
            do j = 1, size(kk)
               mm = gca_assoc(mm, kk(j), vv(j), roots)
            end do
            out = mm
          end block
       else
          out = gca_assoc(vs_get(base + 1), &
               seq_elem(vs_get(base + 2), 0, roots), &
               seq_elem(vs_get(base + 2), 1, roots), roots)
       end if
    else if (coll%tag == GCT_NIL) then
       out = gcl_cons(vs_get(base + 2), gcl_empty(roots), roots)
    else
       out = gcl_cons(vs_get(base + 2), to_seq(vs_get(base + 1), roots), roots)
    end if
    call vs_leave(base)
  end function conj1

  ! Which slot holds metadata. A Var keeps it in slot 2, but a
  ! namespace uses slot 2 for its bindings -- writing metadata there
  ! would empty the namespace -- so OBJ_NS keeps it in slot 4.
  integer function meta_slot(v)
    type(gc_value), intent(in) :: v
    if (gc_kind(v) == OBJ_NS) then
       meta_slot = 4
    else
       meta_slot = 2
    end if
  end function meta_slot

  ! A symbol or keyword's name, with any namespace qualifier removed;
  ! a string is already its own name.
  function name_part(v0) result(s)
    type(gc_value), intent(in) :: v0
    character(len=:), allocatable :: s, t
    type(gc_value) :: v
    integer :: sl
    v = strip_meta(v0)
    if (gc_kind(v) == OBJ_NS) then
       s = gcn_name(v)
       return
    end if
    if (gcn_is_var(v)) then
       s = name_part(gc_slot(v, 4))
       return
    end if
    t = gc_ref_text(v%ref)
    sl = index(t, "/")
    if (sl > 1 .and. sl < len(t)) then
       s = t(sl+1:)
    else
       s = t
    end if
  end function name_part

  function truthy(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = .true.
    if (v%tag == GCT_NIL) yes = .false.
    if (v%tag == GCT_BOOL .and. v%ival == 0) yes = .false.
  end function truthy

  ! A method symbol's name without its namespace. A deftype method
  ! written inside a syntax-quote template -- every one of defrecord's
  ! -- arrives qualified, and NewInstanceMethod.parse reads sym.name.
  function bare_name(sym) result(s)
    type(gc_value), intent(in) :: sym
    character(len=:), allocatable :: s
    integer :: sl
    s = gc_ref_text(sym%ref)
    sl = index(s, "/")
    if (sl > 1 .and. sl < len(s)) s = s(sl+1:)
  end function bare_name

  ! --- ChemSol: a map in, the routine, a map out -------------------------
  !
  ! (fortran/chemsol-readopt m "vdw.par"), (fortran/chemsol-dg-ld m atoms)
  ! and (fortran/chemsol-solvout m). The map's keys are the routines'
  ! own argument names as keywords -- :iterld, :n-reg1, :xw -- with
  ! underscores as hyphens. Scalars are read from the map and, for the
  ! ones a routine writes, assoc'd back; arrays are clotran arrays whose
  ! buffers the routine writes in place, so they need no repacking.
  recursive function chemsol_call(id, m0, extra, roots) result(out)
    integer, intent(in) :: id
    type(gc_value), intent(in) :: m0, extra, roots
    type(gc_value) :: out, m
    type(cs_args) :: a
    character(len=:), allocatable :: err
    character(len=8), allocatable :: atom(:)
    integer :: base, i, n

    out = gc_nil()
    m = strip_meta(m0)
    if (.not. gca_is(m)) then
       call fail("chemsol: needs a map")
       return
    end if
    base = vs_enter(2)
    call vs_set(base + 1, m)
    if (.not. cs_from_map(vs_get(base + 1), a)) then
       call vs_leave(base)
       return
    end if
    err = ""
    select case (id)
    case (B_CS_READOPT)
       call csb_readopt(a, text_of(extra), err)
    case (B_CS_DGLD)
       ! the atom names, as ChemSol's character(8)
       if (.not. gcv_is(strip_meta(extra))) then
          call fail("chemsol-dg-ld: needs a vector of atom names")
          call vs_leave(base)
          return
       end if
       n = gcv_count(strip_meta(extra))
       allocate(atom(max(n, 1)))
       atom = ""
       do i = 1, n
          atom(i) = text_of(gcv_nth(strip_meta(extra), i - 1))
       end do
       call csb_dg_ld(a, atom, err)
    case (B_CS_SOLVOUT)
       call csb_solvout(a)
    end select
    if (len(err) > 0) then
       call fail(err)
       call vs_leave(base)
       return
    end if
    out = cs_to_map(vs_get(base + 1), a, roots)
    call vs_leave(base)
  end function chemsol_call

  ! One scalar or array out of the map, by the routine's name.
  function cs_key(name, roots) result(k)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: k
    character(len=len(name)) :: t
    integer :: i
    t = name
    do i = 1, len(t)
       if (t(i:i) == "_") t(i:i) = "-"
    end do
    k = gc_key(t, roots)
  end function cs_key

  function cs_real(m, name, dflt) result(d)
    type(gc_value), intent(in) :: m
    character(len=*), intent(in) :: name
    real(gc_dp), intent(in) :: dflt
    real(gc_dp) :: d
    type(gc_value) :: v
    v = strip_meta(gca_get(m, cs_key(name, [m])))
    d = dflt
    if (v%tag == GCT_INT .or. v%tag == GCT_REAL .or. v%tag == GCT_RATIO) d = num_dbl(v)
  end function cs_real

  function cs_int(m, name, dflt) result(i)
    type(gc_value), intent(in) :: m
    character(len=*), intent(in) :: name
    integer, intent(in) :: dflt
    integer :: i
    type(gc_value) :: v
    v = strip_meta(gca_get(m, cs_key(name, [m])))
    i = dflt
    if (v%tag == GCT_INT) i = int(v%ival, kind=4)
  end function cs_int

  ! The handle of the array under `name`, checked for kind, or 0 with a
  ! failure raised. A missing key is 0 without failure: the binding
  ! decides which arrays each routine needs.
  function cs_array(m, name, kind_name) result(h)
    type(gc_value), intent(in) :: m
    character(len=*), intent(in) :: name, kind_name
    integer :: h
    type(gc_value) :: v
    h = 0
    v = strip_meta(gca_get(m, cs_key(name, [m])))
    if (v%tag == GCT_NIL) return
    if (gc_kind(v) /= OBJ_ARRAY) then
       call fail("chemsol: :" // name // " is not an array")
       return
    end if
    if (gc_i2(v) /= -1) then
       call fail("chemsol: :" // name // " is a slice; pass a whole array")
       return
    end if
    if (gcna_kind(gc_i1(v)) /= kind_name) then
       call fail("chemsol: :" // name // " must be a " // kind_name // " array")
       return
    end if
    h = gc_i1(v)
  end function cs_array

  logical function cs_from_map(m, a)
    type(gc_value), intent(in) :: m
    type(cs_args), intent(out) :: a
    type(gc_value) :: v
    a%iterld = cs_int(m, "iterld", 0)
    a%ndxp = cs_int(m, "ndxp", 0)
    a%iprint = cs_int(m, "iprint", 0)
    a%n_reg1 = cs_int(m, "n_reg1", 0)
    a%itl = cs_int(m, "itl", 399)
    a%clgvn = cs_real(m, "clgvn", 0.0_gc_dp)
    a%slgvn = cs_real(m, "slgvn", 0.0_gc_dp)
    a%tds0 = cs_real(m, "tds0", 0.0_gc_dp)
    a%vdwsl = cs_real(m, "vdwsl", 0.0_gc_dp)
    a%phobsl = cs_real(m, "phobsl", 0.0_gc_dp)
    a%ephil1 = cs_real(m, "ephil1", 0.0_gc_dp)
    a%ephil2 = cs_real(m, "ephil2", 0.0_gc_dp)
    a%rzcut = cs_real(m, "rzcut", 0.0_gc_dp)
    a%rg_reg1 = cs_real(m, "rg_reg1", 0.0_gc_dp)
    a%rg = cs_real(m, "rg", 0.0_gc_dp)
    a%rg_inner = cs_real(m, "rg_inner", 0.0_gc_dp)
    a%rgim = cs_real(m, "rgim", 0.0_gc_dp)
    a%drg = cs_real(m, "drg", 0.0_gc_dp)
    a%drg_inner = cs_real(m, "drg_inner", 0.0_gc_dp)
    a%rdcutl = cs_real(m, "rdcutl", 0.0_gc_dp)
    a%out_cut = cs_real(m, "out_cut", 0.0_gc_dp)
    a%evqdq = cs_real(m, "evqdq", 0.0_gc_dp)
    a%elgwa = cs_real(m, "elgwa", 0.0_gc_dp)
    a%evdw = cs_real(m, "evdw", 0.0_gc_dp)
    a%elgvn = cs_real(m, "elgvn", 0.0_gc_dp)
    a%ephob = cs_real(m, "ephob", 0.0_gc_dp)
    a%etds = cs_real(m, "etds", 0.0_gc_dp)
    a%ebw = cs_real(m, "ebw", 0.0_gc_dp)
    a%vdwc6 = cs_array(m, "vdwc6", "real8")
    a%dxp0 = cs_array(m, "dxp0", "real8")
    a%rp = cs_array(m, "rp", "real8")
    a%rpi = cs_array(m, "rpi", "real8")
    a%pcenter = cs_array(m, "pcenter", "real8")
    a%xw = cs_array(m, "xw", "real8")
    a%q = cs_array(m, "q", "real8")
    a%q_gas = cs_array(m, "q_gas", "real8")
    a%q_mp2 = cs_array(m, "q_mp2", "real8")
    a%iacw = cs_array(m, "iacw", "int4")
    v = strip_meta(gca_get(m, cs_key("do_gas", [m])))
    a%do_gas = truthy(v)
    v = strip_meta(gca_get(m, cs_key("molname", [m])))
    if (v%tag == GCT_STR) a%molname = gc_ref_text(v%ref)
    v = strip_meta(gca_get(m, cs_key("ssname", [m])))
    if (v%tag == GCT_STR) a%ssname = gc_ref_text(v%ref)
    v = strip_meta(gca_get(m, cs_key("input_file", [m])))
    if (v%tag == GCT_STR) a%input_file = gc_ref_text(v%ref)
    a%input_skip = cs_int(m, "input_skip", 0)
    cs_from_map = .not. has_error
  end function cs_from_map

  ! The scalars a routine may have written, assoc'd back over the map.
  function cs_to_map(m, a, roots) result(out)
    type(gc_value), intent(in) :: m, roots
    type(cs_args), intent(in) :: a
    type(gc_value) :: out
    integer :: base
    base = vs_enter(1)
    call vs_set(base + 1, m)
    call put_int("iterld", a%iterld);   call put_int("ndxp", a%ndxp)
    call put_real("clgvn", a%clgvn);   call put_real("slgvn", a%slgvn);   call put_real("tds0", a%tds0)
    call put_real("vdwsl", a%vdwsl);   call put_real("phobsl", a%phobsl); call put_real("ephil1", a%ephil1)
    call put_real("ephil2", a%ephil2); call put_real("rzcut", a%rzcut);   call put_real("rg_reg1", a%rg_reg1)
    call put_real("rg", a%rg);         call put_real("rg_inner", a%rg_inner); call put_real("rgim", a%rgim)
    call put_real("evqdq", a%evqdq);   call put_real("elgwa", a%elgwa);   call put_real("evdw", a%evdw)
    call put_real("elgvn", a%elgvn);   call put_real("ephob", a%ephob);   call put_real("etds", a%etds)
    call put_real("ebw", a%ebw)
    out = vs_get(base + 1)
    call vs_leave(base)
  contains
    subroutine put_real(name, d)
      character(len=*), intent(in) :: name
      real(gc_dp), intent(in) :: d
      type(gc_value) :: k, nm
      k = cs_key(name, [roots, vs_get(base + 1)])
      nm = gca_assoc(vs_get(base + 1), k, gc_real(d), [roots, vs_get(base + 1), k])
      call vs_set(base + 1, nm)
    end subroutine put_real
    subroutine put_int(name, i)
      character(len=*), intent(in) :: name
      integer, intent(in) :: i
      type(gc_value) :: k, nm
      k = cs_key(name, [roots, vs_get(base + 1)])
      nm = gca_assoc(vs_get(base + 1), k, gc_int(i), [roots, vs_get(base + 1), k])
      call vs_set(base + 1, nm)
    end subroutine put_int
  end function cs_to_map



  ! --- evaluation contexts ---------------------------------------------

  ! Context 1 is the one the program started in; it exists as soon as
  ! anything asks.
  subroutine ctx_ensure_main()
    if (n_ctx > 0) return
    allocate(ctxs(8))
    n_ctx = 1
    cur_ctx = 1
  end subroutine ctx_ensure_main

  ! A fresh context: empty stacks, no error, no bindings, its own root
  ! slots for the thrown value and the binding stack.
  function gce_ctx_new() result(id)
    integer :: id
    type(eval_ctx), allocatable :: bigger(:)
    type(eval_ctx) :: blank   ! default-initialised; flang rejects eval_ctx()
    integer :: n
    call ctx_ensure_main()
    if (n_ctx >= size(ctxs)) then
       n = size(ctxs)
       allocate(bigger(2 * n))
       bigger(1:n) = ctxs(1:n)
       call move_alloc(bigger, ctxs)
    end if
    n_ctx = n_ctx + 1
    id = n_ctx
    ctxs(id) = blank
    ctxs(id)%last_error = ""
    ctxs(id)%last_trace = ""
    call gc_stack_new(id)
  end function gce_ctx_new

  integer function gce_ctx_current()
    call ctx_ensure_main()
    gce_ctx_current = cur_ctx
  end function gce_ctx_current

  ! Parks the live context and brings `id` in. Only between steps: a
  ! run in progress on the Fortran stack (a native calling back into
  ! Clojure) belongs to the context that started it, and switching
  ! under it is the caller's mistake, not this routine's. The one
  ! exception is a switch BRACKETED inside a native call -- out and
  ! back before that call returns, as take_break does -- since the run
  ! in progress never executes under the other context.
  subroutine gce_ctx_switch(id)
    integer, intent(in) :: id
    call ctx_ensure_main()
    if (id == cur_ctx .or. id < 1 .or. id > n_ctx) return
    ! out
    if (allocated(kst)) call move_alloc(kst, ctxs(cur_ctx)%kst)
    ctxs(cur_ctx)%ksp = ksp
    if (allocated(fstack_fn)) then
       call move_alloc(fstack_fn, ctxs(cur_ctx)%fstack_fn)
       call move_alloc(fstack_site, ctxs(cur_ctx)%fstack_site)
    end if
    ctxs(cur_ctx)%fstack_top = fstack_top
    ctxs(cur_ctx)%pending_site = pending_site
    ctxs(cur_ctx)%ev_depth = ev_depth
    ctxs(cur_ctx)%has_error = has_error
    if (allocated(last_error)) then
       ctxs(cur_ctx)%last_error = last_error
    else
       ctxs(cur_ctx)%last_error = ""
    end if
    if (allocated(last_trace)) then
       ctxs(cur_ctx)%last_trace = last_trace
    else
       ctxs(cur_ctx)%last_trace = ""
    end if
    ctxs(cur_ctx)%thrown_root = thrown_root
    ctxs(cur_ctx)%binding_stack_root = binding_stack_root
    call gc_stack_save(cur_ctx)
    ! in
    if (allocated(kst)) deallocate(kst)
    if (allocated(ctxs(id)%kst)) call move_alloc(ctxs(id)%kst, kst)
    ksp = ctxs(id)%ksp
    if (allocated(fstack_fn)) deallocate(fstack_fn, fstack_site)
    if (allocated(ctxs(id)%fstack_fn)) then
       call move_alloc(ctxs(id)%fstack_fn, fstack_fn)
       call move_alloc(ctxs(id)%fstack_site, fstack_site)
    end if
    fstack_top = ctxs(id)%fstack_top
    pending_site = ctxs(id)%pending_site
    ev_depth = ctxs(id)%ev_depth
    has_error = ctxs(id)%has_error
    last_error = ctxs(id)%last_error
    last_trace = ctxs(id)%last_trace
    thrown_root = ctxs(id)%thrown_root
    binding_stack_root = ctxs(id)%binding_stack_root
    call gc_stack_restore(id)
    cur_ctx = id
  end subroutine gce_ctx_switch

  subroutine gce_set_home(dir)
    character(len=*), intent(in) :: dir
    clotran_home = dir
  end subroutine gce_set_home

  function gce_home() result(h)
    character(len=:), allocatable :: h
    h = "."
    if (allocated(clotran_home)) h = clotran_home
  end function gce_home

  subroutine ctx_reset()
    if (allocated(ctxs)) deallocate(ctxs)
    n_ctx = 0
    cur_ctx = 0
    handler_ctx = 0
    in_handler = .false.
    resume_pending = .false.
    step_at = 0
    repl_depth = 0
    call gc_stacks_reset()
  end subroutine ctx_reset

  include "analyze.inc"
  include "exec.inc"
  include "repl.inc"

end module Eval

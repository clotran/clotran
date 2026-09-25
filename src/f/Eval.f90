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
  use BigInt
  use BigDec
  use PersistentList
  use PersistentVector
  use Assoc
  use Env
  use Namespace
  use Printer
  use NativeArray
  use Regex
  use LispReader
  use CompiledFn
  use DynLoad
  use Threads
  use iso_c_binding, only: c_ptr, c_funptr, c_loc, c_f_pointer, c_double, c_int, c_long, c_char, c_null_char, c_associated, c_bool, c_int32_t, &
       c_null_ptr, c_intptr_t, c_funloc, c_size_t
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
  integer, parameter :: B_CAS = 305
  integer, parameter :: B_SETVALIDATOR = 268, B_GETVALIDATOR = 269
  integer, parameter :: B_RTPRINT = 270
  integer, parameter :: B_NANOTIME = 271, B_MILLIS = 272
  integer, parameter :: B_DGEMM = 273
  integer, parameter :: B_STACKTRACE = 274, B_STE_CLASS = 275, B_STE_METHOD = 276, &
       B_STE_FILE = 277, B_STE_LINE = 278
  integer, parameter :: B_SLURP = 279
  integer, parameter :: B_CLASSOF = 284, B_IDHASH = 285, B_REDUCEINIT = 286
  integer, parameter :: B_CHUNK_ADD = 287, B_CHUNK_OF = 288, B_CHUNK_FIRST = 289, &
       B_CHUNK_MORE = 290, B_CHUNK_NEXT = 291, B_CHUNK_DROP = 292
  integer, parameter :: B_BREAK = 293, B_LASTBREAK = 294, B_BREAKON = 295
  integer, parameter :: B_RESUME = 296, B_REPL = 297
  integer, parameter :: B_SUBMIT = 298, B_TASKDONE = 299, B_TASKCANCELLED = 300, B_TASKCANCEL = 301, &
       B_LATCHWAIT = 302, B_SLEEP = 303, B_NPROCS = 304, &
       B_TASKSTATUS = 306, B_MAILBOX = 307, B_CURTASK = 308
  ! A host member that is Clojure on this host: a row with this id names
  ! a var in clotran.rt (src/clj/clotran/rt.cljf), loaded on first use.
  integer, parameter :: B_RTFN = 309
  ! Sorted maps and sets (sorted.inc)
  integer, parameter :: B_SORTEDMAP = 310, B_SORTEDSET = 311, B_SEQFROM = 312, B_ENTRYKEY = 313, &
       B_COMPARATOR = 314, B_RSEQ = 315
  ! The unchecked arithmetic, which wraps where + - * inc dec throw
  integer, parameter :: B_UADD = 316, B_USUB = 317, B_UMUL = 318, B_UINC = 319, B_UDEC = 320
  ! A stand-in for a JVM object clotran has no counterpart to but code
  ! calls methods on -- a class loader, a thread: non-nil, so the call
  ! reaches its row instead of a NullPointerException
  integer, parameter :: B_STUB = 321
  integer, parameter :: B_MAPENTRY = 322, B_ISASSIGN = 323, B_BINDROOT = 324, B_RAWROOT = 325
  integer, parameter :: B_HASHCODE = 326, B_GETCAUSE = 327, B_NSREMOVE = 328, B_NSCREATE = 329, B_CANSEQ = 330
  integer, parameter :: B_PREFERMETHOD = 331, B_PREFERTABLE = 332, B_DISPATCHFN = 333
  integer, parameter :: B_PKGLOAD = 334, B_PKGCALL = 335, B_PKGFN = 336, B_RANDOMUUID = 337
  integer, parameter :: B_GCTORTURE = 338
  ! The PROMOTING operators: +' -' *' inc' dec' (Numbers.addP and
  ! friends). Same arithmetic as + - * inc dec, but an overflow
  ! promotes to a BigInt instead of throwing.
  integer, parameter :: B_PADD = 339, B_PSUB = 340, B_PMUL = 341
  integer, parameter :: B_PINC = 342, B_PDEC = 343, B_TOBIG = 344, B_TODEC = 345
  ! andNot and the UNSIGNED shift. Both used to be pointed at their
  ! nearest neighbour -- bit-and and an arithmetic shift -- which is a
  ! wrong ANSWER rather than a missing one: (bit-and-not 7 2) came
  ! back 2 instead of 5.
  integer, parameter :: B_BITANDNOT = 346, B_USHR = 347
  ! the narrowing casts, which TRUNCATE to their width
  integer, parameter :: B_SHORTCAST = 348, B_BYTECAST = 349, B_INTCAST = 350
  ! and the CHECKED ones, which raise instead of truncating
  integer, parameter :: B_CHKSHORT = 351, B_CHKBYTE = 352, B_CHKINT = 353
  ! Murmur3.hashOrdered/hashUnordered and Util.hashCombine, which are
  ! what hash-ordered-coll, hash-unordered-coll and a defrecord's
  ! generated hasheq are written on.
  integer, parameter :: B_HASHORD = 354, B_HASHUNORD = 355, B_HASHCOMB = 356
  ! IRef.addWatch/removeWatch/getWatches. A watch is a fn of four
  ! arguments -- key, reference, old, new -- run after every change.
  integer, parameter :: B_ADDWATCH = 357, B_REMWATCH = 358, B_GETWATCHES = 359
  ! TaggedLiteral/create and UUID/fromString
  integer, parameter :: B_TAGGEDLIT = 360, B_UUIDOF = 361
  ! The tap queue: java.util.concurrent.ArrayBlockingQueue, which is
  ! a task MAILBOX here (tasks.inc) -- an atom holding a vector,
  ! ready when it holds anything -- and a Thread, which is a task.
  integer, parameter :: B_QOFFER = 362, B_QTAKE = 363, B_THREADSTART = 364
  integer, parameter :: B_THREADDAEMON = 365, B_NSUNMAP = 366
  integer, parameter :: B_MUNGE = 367, B_DEMUNGE = 368
  integer, parameter :: B_ISARRAY = 369, B_EDNREAD = 370, B_ASTDATA = 371
  integer, parameter :: B_LOADCOMPILED = 372, B_ALLNS = 373, B_POOLREG = 374
  integer, parameter :: B_LONGCAST_CHECKED = 375, B_SIMPLENAME = 376
  integer, parameter :: B_NUMLONG = 377, B_ARRAYCAST = 378, B_SPIT = 379
  integer, parameter :: B_ASTPOOL = 380, B_POSITION = 381, B_READFORMS = 382, B_ARRAYTYPESYM = 383

  ! Compiler.CHAR_MAP, verbatim from the pinned clone: the characters
  ! a Clojure name may hold that a JVM member name may not. '.' is
  ! commented out there and so absent here. The two arrays are one
  ! table read in both directions; demunge tries the long escapes
  ! first, so _COLON_ is not read as the _ that stands for a hyphen.
  character(len=1), parameter :: MUNGE_CH(24) = [ &
       "-", ":", "+", ">", "<", "=", "~", "!", "@", "#", "'", '"', "%", &
       "^", "&", "*", "|", "{", "}", "[", "]", "/", "\", "?" ]
  character(len=16), parameter :: MUNGE_ESC(24) = [ character(len=16) :: &
       "_", "_COLON_", "_PLUS_", "_GT_", "_LT_", "_EQ_", "_TILDE_", &
       "_BANG_", "_CIRCA_", "_SHARP_", "_SINGLEQUOTE_", "_DOUBLEQUOTE_", &
       "_PERCENT_", "_CARET_", "_AMPERSAND_", "_STAR_", "_BAR_", &
       "_LBRACE_", "_RBRACE_", "_LBRACK_", "_RBRACK_", "_SLASH_", &
       "_BSLASH_", "_QMARK_" ]
  integer, parameter :: B_ARRSORT = 178, B_CMPCALL = 179
  integer, parameter :: B_COMPTYPE = 173

  ! The auto-gensym map for the syntax-quote currently being expanded,
  ! and the counter that makes each name unique. GENSYM_ENV in
  ! LispReader is a dynamic Var bound around one syntax-quote; a
  ! module variable plus a depth count is the same scoping here.
  type(gc_root), save :: gensym_root
  integer, save :: gensym_id = 0
  ! Every type `deftype*` has created, keyed by the class keyword a
  ! class literal evaluates to. Clojure puts the class in a
  ! classloader and imports the short name into the namespace;
  ! clotran's `import` is a no-op (classes are recognised by the
  ! SHAPE of their name), so there is nowhere namespace-local to put
  ! it and one global table is what `new` and `instance?` both read.
  !
  ! Shared between threads, as the JVM's classes are (src/f/state.edn).
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
  ! import* records these; see record_import.
  character(len=64), allocatable, save :: import_full(:), import_short(:)
  integer, save :: n_imports = 0
  type(gc_root), save :: global_env_root
  integer, save :: ev_limit = 0


  ! The value a `throw` is carrying, as a GC GLOBAL ROOT rather than a
  ! plain module variable. It has to be: between the throw and the
  ! catch, nothing else refers to it -- the stack frames that held it
  ! are unwinding -- so an ordinary variable would be a value the
  ! collector cannot see, and a collection in that window would free
  ! the exception before its handler ever ran.
  ! Reused argument vectors for the numeric builtins (exec.inc, N_CALL
  ! mode 3), and the one recur marker: none of those allocate per call.
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
  ! clojure.core/*math-context*, so the decimal arithmetic can read what
  ! with-precision bound without looking a Var up by name every time
  type(gc_root), save :: math_ctx_root
  logical, save :: in_handler = .false., resume_pending = .false.
  integer, save :: handler_ctx = 0, step_at = 0, repl_depth = 0
  ! Tasks (tasks.inc): every task not yet finished; the one running now,
  ! nil in the main context; the depth of its outermost run, where a
  ! block may yield; a yield in progress; and the context ids finished
  ! tasks gave back, for the next ones.
  type(gc_root), save :: tasks_root, main_mailbox_root
  ! The baton (tasks.inc): one lock and one condition, the context that
  ! may run clotran code, and per context who stepped it, whether it was
  ! cancelled while parked, and its task. A task's thread gets a big
  ! stack: it runs the interpreter, as the main thread does.
  type(th_lock), save :: baton_lock
  type(th_cond), save :: baton_cond
  integer, save :: baton_ctx = 0
  logical, save :: baton_up = .false.
  integer, save :: natives_running = 0, native_gen = 0
  integer(c_size_t), parameter :: TASK_STACK_BYTES = 64_c_size_t * 1024_c_size_t * 1024_c_size_t
  logical, save :: task_trace = .false., task_trace_read = .false.   ! CLOTRAN_TASK_TRACE=1: the scheduler's decisions, on stderr
  logical, save :: rt_loaded = .false.   ! clotran.rt, once (rt_call)
  logical, save :: mf_loaded = .false.   ! clotran.multifn, once (mf_call)
  ! Compiler.checkSpecs: clojure.spec.alpha/macroexpand-check before a
  ! macro expands. RT.CHECK_SPECS comes on once core.clj has loaded
  ! (main.f90); the two spec libs load at the first check, and no check
  ! runs while they load (MACRO_CHECK_LOADING).
  logical, save :: spec_check = .false.
  logical, save :: spec_loaded = .false.
  logical, save :: spec_loading = .false.
  logical, save :: pk_loaded = .false.   ! clotran.package, once (B_PKGFN)
  logical, save :: ld_loaded = .false.   ! clotran.loader, once (gce_install_compiled)
  ! The packages opened (DynLoad.f90), by handle: a package's fns carry
  ! the index, never the pointer.
  type(c_ptr), allocatable, save :: pkg_handles(:)
  integer, save :: pkg_count = 0
  ! the directories of the packages loaded, classpath roots for their Clojure
  character(len=1024), allocatable, save :: pkg_roots(:)
  ! a string argument on its way to a shim, null-terminated
  type :: cbuf
     character(kind=c_char), allocatable :: s(:)
  end type cbuf
  integer, allocatable, save :: free_ctx(:)
  integer, save :: n_free_ctx = 0
  ! A task's states (i1): parked and resumable, on the Fortran stack
  ! now, and the three finished ones.
  integer, parameter :: TASK_NEW = 0, TASK_RUNNABLE = 1, TASK_RUNNING = 2, &
       TASK_DONE = 3, TASK_FAILED = 4, TASK_CANCELLED = 5

  public :: gce_eval, gce_base_env, gce_has_error, gce_error, gce_clear_error, gce_set_spec_check
  public :: gce_main_bindings, gce_install_compiled, gce_raise_arity_named
  public :: gce_native_begin, gce_native_end
  public :: gce_analyze, gce_trace
  public :: gce_ctx_new, gce_ctx_switch, gce_ctx_current
  public :: gce_repl
  public :: gce_set_home, gce_home
  public :: gce_apply, gce_env, gce_exec_node, gce_apply_slots

  ! THE CALL STACK. One entry per closure invocation in progress: the
  ! closure and the position of the call that entered it (set by the
  ! executor just before apply, read by invoke_closure). Nothing here
  ! is a root: a closure on this stack is also in a value-stack slot of
  ! the caller for as long as the call lasts. When an error is raised
  ! the stack is rendered into `last_trace` at once, before it unwinds,
  ! so the message can say where it came from. A `recur` does not push;
  ! a deep loop is one frame, which a trace does not pretend otherwise.
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
  ! Set by deftype* and reify* just before a method's clauses go
  ! through analyze_fn, and read and cleared by it at once: a
  ! method's parameters take their types from the interface, not
  ! from fn's primitive hint rules.
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
  integer, parameter :: KF_FNBODY = 1, KF_RESTART = 2, K_SLOTS = 7   ! slot 6: a scalar call's first argument; slot 7: the closure whose body this is
  integer, save :: k_limit = 0

  ! --- evaluation contexts ---------------------------------------------
  !
  ! Everything the evaluator keeps between two steps of `run`: the
  ! continuation stack, the call stack, the error state, the thrown
  ! value, the dynamic bindings. Each thread runs on its own, the one
  ! ctx_self finds through the thread's key (PLAN.md step 14b); its value
  ! stack is GC's, bound the same way (gc_stack_bind). A task is a
  ! context; so is the paused frame a debugger inspects while the REPL
  ! runs in another, on the same thread.
  type eval_ctx
     type(kframe), allocatable :: kst(:)
     integer :: ksp = 0
     type(gc_value), allocatable :: fstack_fn(:)
     integer, allocatable :: fstack_site(:)
     integer :: fstack_top = 0, pending_site = 0, ev_depth = 0
     logical :: has_error = .false.
     character(len=:), allocatable :: last_error, last_trace
     type(gc_root) :: thrown_root, binding_stack_root
     ! the rest of what was one module variable each, now one per thread
     integer :: id = 0, qq_depth = 0, task_loop_depth = 0
     logical :: analyzing_method = .false., yield_flag = .false.
     type(gc_value) :: cur_task
     type(gc_root) :: scratch1_root, scratch2_root, recur_root
     ! the scheduler's, per context: who stepped it, whether it is to end,
     ! whether it is in a native call, its task; and the condition its
     ! thread waits on for the baton -- a hand-off wakes that thread only
     integer :: came_from = 0
     logical :: dying = .false., native = .false.
     type(gc_value) :: task
     type(th_cond) :: turn
  end type eval_ctx
  ! Each context is allocated on its own and never moves: a thread holds
  ! its context's address (PLAN.md step 14b), so growing the table copies
  ! pointers, not contexts.
  type ctx_ref
     type(eval_ctx), pointer :: c => null()
  end type ctx_ref
  type(ctx_ref), allocatable, save :: ctxs(:)
  integer, save :: n_ctx = 0
  ! Each thread's own context: the one this key names on that thread
  ! (PLAN.md step 14b). A same-thread switch -- the debugger's handler --
  ! re-points it; a hand-off between threads does not touch it.
  type(th_key), save :: ctx_key
  logical, save :: ctx_key_made = .false.

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
    type(eval_ctx), pointer :: tctx
    tctx => ctx_self()
    tctx%has_error = .false.
    tctx%last_error = ""
    call set_thrown(gc_nil())
    if (allocated(tctx%last_trace)) tctx%last_trace = ""
  end subroutine gce_clear_error

  ! Re-checks the slot rather than trusting the index, for the same
  ! reason PersistentList's empty-list singleton does: gc_init clears the
  ! global-root registry but this module variable survives it.
  ! The thrown value. A Throwable that has no stack trace yet gets
  ! the current one -- Java fills it in at construction; here that
  ! happens in eval_new for a (new SomeException ...) and, failing
  ! that, now, at the throw.
  subroutine set_thrown(v)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: v
    type(gc_value) :: fr
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    call gc_global_keep(tctx%thrown_root, v)
    if (gc_kind(v) == OBJ_ERR) then
       if (tag_of(gc_slot(v, 4)) == GCT_NIL) then
          base = vs_enter(vst, 1)
          fr = frames_vec([v])
          call vs_set(vst, base + 1, fr)
          call gc_set_slot(v, 4, vs_get(vst, base + 1))
          call vs_leave(vst, base)
       end if
    end if
  end subroutine set_thrown

  ! The call stack as data, innermost first: one map per frame with
  ! the four things a StackTraceElement answers. `:class` is the
  ! function's qualified name, `:method` is always "invoke" -- there
  ! is one way to call a function here -- `:file` and `:line` are the
  ! call site's.
  ! Each key and each value goes on the shadow stack BEFORE the assoc:
  ! two allocations in one argument list means the second can collect
  ! the first (NOTES, "Rooting"), and the frame map then carried a nil
  ! class -- which Throwable->map turns into (symbol nil), "no
  ! conversion to symbol", but only when the heap happened to fill
  ! between the two. The oracle caught it with spec loaded.
  function frames_vec(roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, nm
    character(len=:), allocatable :: who, fname
    integer :: i, base, line, col
    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 4)
    out = gcv_empty(roots)
    call vs_set(vst, base + 1, out)
    do i = tctx%fstack_top, 1, -1
       who = "fn"
       if (gc_kind(tctx%fstack_fn(i)) == OBJ_CLOSURE) then
          nm = gc_slot(tctx%fstack_fn(i), 5)
          if (nm%tag == GCT_SYM) who = gc_ref_text(nm%ref)
       else if (gc_kind(tctx%fstack_fn(i)) == OBJ_COMPILED) then
          nm = gc_slot(tctx%fstack_fn(i), 1)
          who = gc_ref_text(nm%ref)
       end if
       fname = ""
       line = 0
       if (tctx%fstack_site(i) /= 0) call gcr_position_parts(tctx%fstack_site(i), fname, line, col)
       m = gca_empty([roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, m)
       call frame_put(base, roots, "class", gc_str(who, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       call frame_put(base, roots, "method", gc_str("invoke", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       call frame_put(base, roots, "file", gc_str(fname, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       call frame_put(base, roots, "line", gc_int(line))
       out = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 2), [roots])
       call vs_set(vst, base + 1, out)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function frames_vec

  ! One key/value into the frame map in slot base+2. The VALUE is
  ! already built (and rooted by its own allocation); the key is built
  ! here, with the value on the stack first.
  subroutine frame_put(base, roots, key, val)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: base
    type(gc_value), intent(in) :: roots(:), val
    character(len=*), intent(in) :: key
    type(gc_value) :: k, m
    vst => gc_my_stack()
    call vs_set(vst, base + 4, val)
    k = gc_key(key, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4)])
    call vs_set(vst, base + 3, k)
    m = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 2, m)
  end subroutine frame_put

  function thrown_value() result(v)
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: v
    tctx => ctx_self()
    v = gc_root_get(tctx%thrown_root)
  end function thrown_value

  function gce_has_error() result(yes)
    type(eval_ctx), pointer :: tctx
    logical :: yes
    tctx => ctx_self()
    yes = tctx%has_error
  end function gce_has_error

  function gce_error() result(s)
    type(eval_ctx), pointer :: tctx
    character(len=:), allocatable :: s
    tctx => ctx_self()
    s = ""
    if (allocated(tctx%last_error)) s = tctx%last_error
  end function gce_error

  subroutine fail(msg)
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: msg
    tctx => ctx_self()
    tctx%has_error = .true.
    tctx%last_error = msg
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
    type(eval_ctx), pointer :: tctx
    integer :: i
    type(gc_value) :: bm
    type(gc_value) :: nm
    character(len=:), allocatable :: who
    character(len=16) :: more
    tctx => ctx_self()
    tctx%last_trace = ""
    if (tctx%fstack_top > 128) write(more, '(I0)') tctx%fstack_top - 128
    do i = tctx%fstack_top, max(1, tctx%fstack_top - 127), -1
       who = "fn"
       if (gc_kind(tctx%fstack_fn(i)) == OBJ_CLOSURE) then
          nm = gc_slot(tctx%fstack_fn(i), 5)
          if (nm%tag == GCT_SYM) who = gc_ref_text(nm%ref)
       else if (gc_kind(tctx%fstack_fn(i)) == OBJ_COMPILED) then
          nm = gc_slot(tctx%fstack_fn(i), 1)
          who = gc_ref_text(nm%ref)
       end if
       if (tctx%fstack_site(i) /= 0) then
          tctx%last_trace = tctx%last_trace // "  at " // who // " (" // gcr_position(tctx%fstack_site(i)) // ")" // achar(10)
       else
          tctx%last_trace = tctx%last_trace // "  at " // who // achar(10)
       end if
    end do
    if (tctx%fstack_top > 128) tctx%last_trace = tctx%last_trace // "  ... " // trim(more) // " more" // achar(10)
    ! and the paused state as data, while the frames are still pending,
    ! to the handler if one is bound
    if (break_mode == 0) call read_break_mode()
    if (break_mode == 2) bm = take_break("error")
  end subroutine capture_trace

  ! The trace of the last error, one line per frame, or empty.
  function gce_trace() result(s)
    type(eval_ctx), pointer :: tctx
    character(len=:), allocatable :: s
    tctx => ctx_self()
    s = ""
    if (allocated(tctx%last_trace)) s = tctx%last_trace
  end function gce_trace

  subroutine push_frame(fn, site)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: site
    type(gc_value), allocatable :: bf(:)
    integer, allocatable :: bs(:)
    integer :: n
    tctx => ctx_self()
    if (.not. allocated(tctx%fstack_fn)) then
       allocate(tctx%fstack_fn(256), tctx%fstack_site(256))
       tctx%fstack_top = 0
    end if
    if (tctx%fstack_top >= size(tctx%fstack_fn)) then
       n = size(tctx%fstack_fn)
       allocate(bf(2 * n), bs(2 * n))
       bf(1:n) = tctx%fstack_fn(1:n)
       bs(1:n) = tctx%fstack_site(1:n)
       call move_alloc(bf, tctx%fstack_fn)
       call move_alloc(bs, tctx%fstack_site)
    end if
    if (k_limit == 0) call read_frame_limit()
    if (tctx%fstack_top >= k_limit) then
       call fail("stack overflow")
       return
    end if
    tctx%fstack_top = tctx%fstack_top + 1
    tctx%fstack_fn(tctx%fstack_top) = fn
    tctx%fstack_site(tctx%fstack_top) = site
  end subroutine push_frame

  subroutine pop_frame()
    type(eval_ctx), pointer :: tctx
    tctx => ctx_self()
    if (tctx%fstack_top > 0) tctx%fstack_top = tctx%fstack_top - 1
  end subroutine pop_frame

  ! An environment with the primitives bound. Built fresh rather than
  ! cached in a module variable: a cached handle would go stale across
  ! gc_init, which is exactly the singleton bug PersistentList's check 4c
  ! caught.
  function gce_base_env(roots) result(env)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: env, core, var
    integer :: base

    ! A fresh heap means every array handle from a previous one is
    ! orphaned; this is the one place that always follows gc_init.
    vst => gc_my_stack()
    call gcna_reset()
    call seed_default_imports()
    call gcp_set_forcer(gce_force)
    call gca_set_comparer(compare_via)
    call gcr_set_ns_resolver(kw_ns_of)
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
    base = vs_enter(vst, 3)
    env = gce_new(gc_nil(), roots)
    call vs_set(vst, base + 1, env)
    call gc_global_keep(global_env_root, vs_get(vst, base + 1))
    core = gcn_find_or_create("clojure.core", [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, core)
    call bind_builtin(core, "+", B_ADD)
    call bind_builtin(core, "-", B_SUB)
    call bind_builtin(core, "*", B_MUL)
    call bind_builtin(core, "=", B_EQ)
    call bind_builtin(core, "<", B_LT)
    call bind_builtin(core, "list", B_LIST)
    call bind_builtin(core, "vector", B_VECTOR)
    ! The debugger's two entry points; PLAN.md's break protocol.
    ! The compiler's front door: the resolved tree as DATA, so a code
    ! generator can be written in Clojure over the same tree the
    ! executor runs. PLAN step 10.
    call bind_builtin(core, "clotran-ast", B_ASTDATA)
    call bind_builtin(core, "clotran-ast-pool", B_ASTPOOL)
    call bind_builtin(core, "clotran-position", B_POSITION)
    call bind_builtin(core, "clotran-read-forms", B_READFORMS)
    call bind_builtin(core, "clotran-load-compiled", B_LOADCOMPILED)
    call bind_builtin(core, "clotran-pool-register", B_POOLREG)
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
      call vs_set(vst, base + 3, fns)
      call bind_builtin(vs_get(vst, base + 3), "make-array", B_MAKE_ARRAY)
      call bind_builtin(vs_get(vst, base + 3), "aget", B_AGET)
      call bind_builtin(vs_get(vst, base + 3), "aset", B_ASET)
      call bind_builtin(vs_get(vst, base + 3), "alength", B_ALENGTH)
      call bind_builtin(vs_get(vst, base + 3), "array-kind", B_ARRAY_KIND)
      call bind_builtin(vs_get(vst, base + 3), "array-shape", B_ARRAY_SHAPE)
      ! packages: a shared library opened at run time (DynLoad.f90, clotran.package)
      call bind_builtin(vs_get(vst, base + 3), "load-package*", B_PKGLOAD)
      call bind_builtin(vs_get(vst, base + 3), "call-package*", B_PKGCALL)
      call bind_builtin(vs_get(vst, base + 3), "load-package", B_PKGFN)
      ! The thread primitive's host half, in the namespace the protocol
      ! lives in (src/clj/clotran/thread.cljf; tasks.inc).
      fns = gcn_find_or_create("clotran.thread", [core])
      call vs_set(vst, base + 3, fns)
      call bind_builtin(vs_get(vst, base + 3), "task-spawn", B_SUBMIT)
      call bind_builtin(vs_get(vst, base + 3), "task-status", B_TASKSTATUS)
      call bind_builtin(vs_get(vst, base + 3), "task-mailbox", B_MAILBOX)
      call bind_builtin(vs_get(vst, base + 3), "current-task", B_CURTASK)
      call bind_builtin(vs_get(vst, base + 3), "task-sleep", B_SLEEP)
    end block
    ! A whole file as a string. core.clj's slurp is written over
    ! java.io, which is not here; this is the host's reader for it.
    call bind_builtin(core, "clotran-slurp", B_SLURP)
    call bind_builtin(core, "clotran-spit", B_SPIT)
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
    call bind_builtin(core, "clotran-gc-torture", B_GCTORTURE)
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
    call bind_var(core, "*data-readers*", gca_empty([vs_get(vst, base + 1)]))
    call bind_var(core, "*default-data-reader-fn*", gc_nil())
    call bind_var(core, "*assert*", gc_bool(.true.))
    ! NOT nil, which is Clojure's root and means "exact, or throw".
    ! clotran is a language for people doing arithmetic, and every
    ! other such language answers 1/3 rather than raising: MATLAB and
    ! Octave compute in doubles and never raise, and Julia gives
    ! BigFloat a working precision (256 bits by default, changed with
    ! setprecision) so big(1)/big(3) is a number. So the root here is
    ! Java's own name for that default, MathContext.DECIMAL128 --
    ! 34 significant digits, HALF_EVEN, which is IEEE 754 decimal128 --
    ! and with-precision is setprecision. DEVIATIONS 43.
    !
    ! (binding [*math-context* nil] ...) asks for Clojure's exact
    ! arithmetic back, and then (/ 1M 3) throws as it does there.
    call bind_var(core, "*math-context*", default_math_context([vs_get(vst, base + 1)]), var_out=var)
    call gc_global_keep(math_ctx_root, var)
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
    call bind_var(core, "*compile-path*", gc_str("classes", [vs_get(vst, base + 1)]))
    call bind_var(core, "*warn-on-reflection*", gc_bool(.false.))
    call bind_var(core, "*clojure-version*", gca_empty([vs_get(vst, base + 1)]))
    call bind_var(core, "*fn-loader*", gc_nil())
    call bind_var(core, "*verbose-defrecords*", gc_bool(.false.))
    call bind_var(core, "*print-namespace-maps*", gc_bool(.false.))
    call bind_var(core, "*repl*", gc_bool(.false.))
    call bind_var(core, "*compiler-options*", gca_empty([vs_get(vst, base + 1)]))
    call bind_var(core, "*suppress-read*", gc_nil())
    call bind_var(core, "*use-context-classloader*", gc_bool(.true.))
    call bind_builtin(core, "second", B_SECOND)
    call bind_builtin(core, "meta", B_META)
    call bind_builtin(core, "with-meta", B_WITHMETA)
    call bind_builtin(core, "ns", B_NS, .true.)
    call bind_builtin(core, "in-ns", B_INNS)
    env = vs_get(vst, base + 1)
    call vs_leave(vst, base)
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
  ! (seq inst) for a deftype with a `seq` method; nil for one without.
  recursive function inst_seq(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, argv
    integer :: base
    logical :: via_iter
    vst => gc_my_stack()
    tctx => ctx_self()
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, v)
    via_iter = .false.
    m = gca_get(gc_slot(gc_slot(v, 1), 3), gc_key("seq", [roots, vs_get(vst, base + 1)]))
    if (gc_kind(m) /= OBJ_CLOSURE) then
       ! No seq: an Iterable is seq'd through its iterator, 32 at a
       ! time, as RT.seqFrom does -- and core.clj's own Eduction has
       ! iterator and reduce and no seq, so (seq (eduction ..)) was nil.
       m = gca_get(gc_slot(gc_slot(v, 1), 3), gc_key("iterator", [roots, vs_get(vst, base + 1)]))
       if (gc_kind(m) /= OBJ_CLOSURE) then
          call vs_leave(vst, base)
          return
       end if
       via_iter = .true.
    end if
    call vs_set(vst, base + 2, m)
    argv = gcv_conj(gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]), vs_get(vst, base + 1), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, argv)
    out = apply(vs_get(vst, base + 2), vs_get(vst, base + 3))
    if (.not. tctx%has_error .and. via_iter) then
       call vs_set(vst, base + 3, out)
       argv = gcv_conj(gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 3)]), vs_get(vst, base + 3), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, argv)
       out = rt_call("chunk-iterator-seq", vs_get(vst, base + 3))
    end if
    if (.not. tctx%has_error) then
       call vs_set(vst, base + 3, out)
       out = to_seq(vs_get(vst, base + 3), [roots, vs_get(vst, base + 1)])
    end if
    call vs_leave(vst, base)
  end function inst_seq

  ! The var `name` in clotran.rt, applied to `args`. clotran.rt is the
  ! part of clojure.lang.RT and its neighbours that ClojureScript
  ! writes in Clojure -- iterators, TransformerIterator, ArrayList,
  ! Eduction -- written in Clojure here too (src/clj/clotran/rt.cljf)
  ! and loaded the first time a row with B_RTFN, or a constructor
  ! eval_new sends here, is reached.
  recursive function rt_call(name, args) result(out)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: args
    type(gc_value) :: out
    out = rt_call_in("clotran/rt", "clotran.rt", rt_loaded, name, args)
  end function rt_call

  ! clotran.multifn: the multimethod's method selection, a file of its
  ! own because it is first needed while core.clj is still loading
  recursive function mf_call(name, args) result(out)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: args
    type(gc_value) :: out
    out = rt_call_in("clotran/multifn", "clotran.multifn", mf_loaded, name, args)
  end function mf_call

  ! The libs load when checking is switched on, not at the first
  ! macro: on the JVM clojure.main's own macros pull spec in before any
  ! user code, so spec's (:require [clojure.string]) never lands in the
  ! middle of clojure.string's own load -- which is exactly where the
  ! first user (require 'clojure.string) would otherwise put it.
  subroutine gce_set_spec_check(on)
    logical, intent(in) :: on
    spec_check = on
    if (on) call ensure_specs()
  end subroutine gce_set_spec_check

  ! What clojure.main/with-bindings binds for a script or a REPL, and
  ! `clj` therefore runs with: *print-namespace-maps* true, so a map
  ! whose keys share a namespace prints as #:ns{...}. The Var's ROOT is
  ! false (core_print.cljf, Rich's value); this is the launcher's
  ! binding, set once core.clj has loaded.
  subroutine gce_main_bindings()
    type(gc_value) :: var, none(0)
    var = gcn_lookup(gcn_find_or_create("clojure.core", none), gc_sym("*print-namespace-maps*", none))
    if (gcn_is_var(var)) call gc_set_slot(var, var_root_slot(var), gc_bool(.true.))
  end subroutine gce_main_bindings

  recursive subroutine ensure_specs()
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: fargs, out
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    if (spec_loaded) return
    base = vs_enter(vst, 1)
    spec_loading = .true.
    fargs = gcv_empty([gc_nil()])
    call vs_set(vst, base + 1, fargs)
    fargs = gcv_conj(vs_get(vst, base + 1), gc_str("clojure/spec/alpha", [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 1, fargs)
    out = call_builtin(B_RTLOAD, vs_get(vst, base + 1))
    if (.not. tctx%has_error) then
       fargs = gcv_empty([gc_nil()])
       call vs_set(vst, base + 1, fargs)
       fargs = gcv_conj(vs_get(vst, base + 1), gc_str("clojure/core/specs/alpha", [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, fargs)
       out = call_builtin(B_RTLOAD, vs_get(vst, base + 1))
    end if
    spec_loading = .false.
    spec_loaded = .true.
    call vs_leave(vst, base)
  end subroutine ensure_specs

  ! Compiler.checkSpecs(v, form): (macroexpand-check v (next form)),
  ! and a failure is wrapped as the CompilerException is -- a
  ! RuntimeException whose cause is spec's ex-info, which is what
  ! (thrown-with-cause-msg? Exception #"did not conform to spec" ...)
  ! reads.
  recursive subroutine check_specs(mvar, form)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: mvar, form
    type(gc_value) :: fargs, out, e
    logical :: was_loaded
    character(len=:), allocatable :: vt
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    if (.not. spec_check .or. spec_loading) return
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, mvar)
    call vs_set(vst, base + 2, form)
    if (.not. spec_loaded) then
       call ensure_specs()
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
    end if
    fargs = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, fargs)
    fargs = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, fargs)
    fargs = gcv_conj(vs_get(vst, base + 3), gcl_rest(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, fargs)
    was_loaded = .true.
    out = rt_call_in("clojure/spec/alpha", "clojure.spec.alpha", was_loaded, "macroexpand-check", vs_get(vst, base + 3))
    if (tctx%has_error) then
       vt = to_string_text(vs_get(vst, base + 1))
       if (len(vt) > 2) then
          if (vt(1:2) == "#'") vt = vt(3:)
       end if
       call vs_set(vst, base + 3, thrown_value())
       call vs_set(vst, base + 4, gc_sym("RuntimeException", [vs_get(vst, base + 1), vs_get(vst, base + 3)]))
       e = gc_obj(OBJ_ERR, [vs_get(vst, base + 4), gc_str("Syntax error macroexpanding " // vt // ".", &
            [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)]), gc_nil()], &
            [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call gc_set_slot(e, 5, vs_get(vst, base + 3))
       call set_thrown(e)
       tctx%last_error = "Syntax error macroexpanding " // vt // "."
    end if
    call vs_leave(vst, base)
  end subroutine check_specs

  ! After a source file loads: when a compiled library sits beside it
  ! -- foo.cljf and foo.dylib or foo.so, as a class file sits beside a
  ! .clj for RT.load -- clotran.loader installs it over the functions
  ! the source just defined. A file under src/clj/ may instead have its
  ! library at the same place under build/compiled/: clojure/core.clj
  ! is vendored, and nothing is added to that tree. Nothing beside it, nothing happens, and
  ! clotran.loader is never read. A library that will not install is
  ! REPORTED and the interpreted definitions stand: the source loaded,
  ! so the program is still right, only slower.
  recursive subroutine gce_install_compiled(path)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: path
    character(len=5), parameter :: exts(2) = [character(len=5) :: "dylib", "so"]
    character(len=:), allocatable :: stem, cand
    type(gc_value) :: args, r
    logical :: there
    integer :: dot, i, base, at
    vst => gc_my_stack()
    tctx => ctx_self()
    dot = index(path, ".", back=.true.)
    if (dot <= index(path, "/", back=.true.)) return
    stem = path(1:dot)
    do i = 1, 4
       cand = stem // trim(exts(mod(i - 1, 2) + 1))
       if (i > 2) then
          at = index(stem, "src/clj/", back=.true.)
          if (at == 0) exit
          cand = stem(1:at-1) // "build/compiled/" // stem(at+8:) // trim(exts(i - 2))
       end if
       inquire(file=cand, exist=there)
       if (.not. there) cycle
       base = vs_enter(vst, 1)
       args = gcv_empty([gc_nil()])
       call vs_set(vst, base + 1, args)
       args = gcv_conj(vs_get(vst, base + 1), gc_str(cand, [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, args)
       args = gcv_conj(vs_get(vst, base + 1), gc_str(path, [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, args)
       r = rt_call_in("clotran/loader", "clotran.loader", ld_loaded, "install", vs_get(vst, base + 1))
       if (tctx%has_error) then
          print '(A,A,A,A)', "note: not using ", cand, ": ", gce_error()
          call gce_clear_error()
       end if
       call vs_leave(vst, base)
       return
    end do
  end subroutine gce_install_compiled

  recursive function rt_call_in(lib, nsname, loaded, name, args) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: lib, nsname, name
    logical, intent(inout) :: loaded
    type(gc_value), intent(in) :: args
    type(gc_value) :: out, fargs, ns, var, sym
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, args)
    if (.not. loaded) then
       loaded = .true.   ! before the load: a row reached while loading is an error, not a loop
       fargs = gcv_empty([vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, fargs)
       fargs = gcv_conj(vs_get(vst, base + 2), gc_str(lib, [vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, fargs)
       out = call_builtin(B_RTLOAD, vs_get(vst, base + 2))
       out = gc_nil()
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
    end if
    ns = gcn_find_or_create(nsname, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, ns)
    sym = gc_sym(name, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, sym)
    var = gcn_lookup(vs_get(vst, base + 2), vs_get(vst, base + 3))
    if (.not. gcn_is_var(var)) then
       call fail(nsname // " has no " // name)
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, gcn_var_value(var))
    out = apply(vs_get(vst, base + 3), vs_get(vst, base + 1))
    call vs_leave(vst, base)
  end function rt_call_in

  function native(id, name, roots) result(fn)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: id
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fn, sym
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    sym = gc_sym(name, roots)
    call vs_set(vst, base + 1, sym)
    fn = gc_obj(OBJ_BUILTIN, [vs_get(vst, base + 1)], roots)
    call gc_set_i1(fn, id)
    call vs_leave(vst, base)
  end function native

  ! Interns a plain value as a Var in clojure.core. Same shape as
  ! bind_builtin, for the things RT interns that are not functions.
  subroutine bind_var(ns, name, val, var_out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ns, val
    character(len=*), intent(in) :: name
    type(gc_value), intent(out), optional :: var_out
    type(gc_value) :: sym, var
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, ns)
    call vs_set(vst, base + 2, val)
    sym = gc_sym(name, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    var = gcn_intern(vs_get(vst, base + 1), sym, vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), sym])
    call gc_set_i1(var, 1)
    if (present(var_out)) var_out = var
    call vs_leave(vst, base)
  end subroutine bind_var

  subroutine bind_builtin(ns, name, id, is_macro, var_out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ns
    character(len=*), intent(in) :: name
    integer, intent(in) :: id
    logical, intent(in), optional :: is_macro
    type(gc_value), intent(out), optional :: var_out
    type(gc_value) :: sym, fn, var
    type(gc_value) :: r(2)
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, ns)
    sym = gc_sym(name, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, sym)
    r(1) = vs_get(vst, base + 1)
    r(2) = vs_get(vst, base + 2)
    fn = gc_obj(OBJ_BUILTIN, [sym], r)
    call gc_set_i1(fn, id)
    call vs_set(vst, base + 3, fn)
    var = gcn_intern(vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), r)
    if (present(is_macro)) then
       if (is_macro) call var_set_macro(var)
    end if
    if (present(var_out)) var_out = var
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, env
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, nd
    integer :: base

    vst => gc_my_stack()
    tctx => ctx_self()
    out = gc_nil()
    if (tctx%has_error) return
    if (gc_kind(form) == OBJ_AST) then
       out = exec(form, gc_nil())
       return
    end if
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, form)
    nd = analyze_top(vs_get(vst, base + 1))
    if (.not. tctx%has_error) then
       call vs_set(vst, base + 2, nd)
       out = exec(vs_get(vst, base + 2), gc_nil())
    end if
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: forms
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, mname, second, acc, w, clauses
    integer :: base, i

    vst => gc_my_stack()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, forms)
    acc = gcv_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, acc)
    call vs_set(vst, base + 3, vs_get(vst, base + 1))

    do while (gcl_count(vs_get(vst, base + 3)) > 0)
       m = strip_meta(gcl_first(vs_get(vst, base + 3)))
       call vs_set(vst, base + 4, m)
       mname = strip_meta(gcl_first(vs_get(vst, base + 4)))
       if (mname%tag /= GCT_SYM) then
          call fail("proxy: a method needs a name")
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 5, mname)
       second = strip_meta(gcl_first(gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 4)])))
       call vs_set(vst, base + 6, second)
       if (gcv_is(vs_get(vst, base + 6))) then
          ! One arity, written flat.
          acc = gcv_conj(vs_get(vst, base + 2), &
               proxy_clause(vs_get(vst, base + 5), vs_get(vst, base + 6), &
                    gcl_rest(gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 4)]), &
                         [vs_get(vst, base + 4)]), [roots, vs_get(vst, base + 2)]), &
               [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, acc)
       else
          ! Several arities, each its own list.
          clauses = gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 4)])
          call vs_set(vst, base + 6, clauses)
          do i = 1, gcl_count(vs_get(vst, base + 6))
             w = strip_meta(nth_of(vs_get(vst, base + 6), i - 1))
             acc = gcv_conj(vs_get(vst, base + 2), &
                  proxy_clause(vs_get(vst, base + 5), strip_meta(gcl_first(w)), &
                       gcl_rest(w, [vs_get(vst, base + 2)]), [roots, vs_get(vst, base + 2)]), &
                  [roots, vs_get(vst, base + 2)])
             call vs_set(vst, base + 2, acc)
          end do
       end if
       call vs_set(vst, base + 3, gcl_rest(vs_get(vst, base + 3), [roots, vs_get(vst, base + 2)]))
    end do

    out = seq_to_list(vs_get(vst, base + 2), [roots, vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function proxy_methods

  ! (name [this params*] body*) -- one method form in build_type's shape.
  recursive function proxy_clause(mname, params, body, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: mname, params, body
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, ps
    integer :: base, i

    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, mname)
    call vs_set(vst, base + 2, params)
    call vs_set(vst, base + 3, body)
    ! [this ~@params]
    ps = gcv_empty([roots, vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, ps)
    call vs_set(vst, base + 4, gcv_conj(vs_get(vst, base + 4), &
         gc_sym("this", [roots, vs_get(vst, base + 4)]), [roots, vs_get(vst, base + 4)]))
    do i = 0, gcv_count(vs_get(vst, base + 2)) - 1
       call vs_set(vst, base + 4, gcv_conj(vs_get(vst, base + 4), gcv_nth(vs_get(vst, base + 2), i), &
            [roots, vs_get(vst, base + 2), vs_get(vst, base + 4)]))
    end do
    out = gcl_cons(vs_get(vst, base + 4), vs_get(vst, base + 3), &
         [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 4, out)
    out = gcl_cons(vs_get(vst, base + 1), vs_get(vst, base + 4), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ifaces
    type(gc_value) :: out, s, tmp
    integer :: base, i

    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, ifaces)
    tmp = gcv_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, tmp)
    if (gcv_is(vs_get(vst, base + 1))) then
       do i = 0, gcv_count(vs_get(vst, base + 1)) - 1
          s = strip_meta(gcv_nth(vs_get(vst, base + 1), i))
          if (s%tag /= GCT_SYM) cycle
          tmp = gc_class(class_key(gc_ref_text(s%ref)), &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, gcv_conj(vs_get(vst, base + 2), tmp, &
               [vs_get(vst, base + 1), vs_get(vst, base + 2), tmp]))
       end do
    end if
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function iface_keys

  ! Every clause for one method name, in order, each with the type's
  ! fields bound around its body.
  recursive function method_clauses(name, methods, fields) result(out)
    type(gc_stack), pointer :: vst
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: methods, fields
    type(gc_value) :: out, m, mname, tmp
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, methods)
    call vs_set(vst, base + 2, fields)
    tmp = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, tmp)
    call vs_set(vst, base + 4, vs_get(vst, base + 1))

    do while (gcl_count(vs_get(vst, base + 4)) > 0)
       m = strip_meta(gcl_first(vs_get(vst, base + 4)))
       mname = strip_meta(gcl_first(m))
       if (mname%tag == GCT_SYM) then
          if (bare_name(mname) == name) then
             tmp = bind_fields(gcl_rest(m, [vs_get(vst, base + 2), vs_get(vst, base + 3)]), &
                  vs_get(vst, base + 2))
             call vs_set(vst, base + 5, tmp)
             tmp = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 5), &
                  [vs_get(vst, base + 3), vs_get(vst, base + 5)])
             call vs_set(vst, base + 3, tmp)
          end if
       end if
       tmp = gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, tmp)
    end do

    out = seq_to_list(vs_get(vst, base + 3), [vs_get(vst, base + 3)])
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: clause, fields
    type(gc_value) :: out, params, this, f, tmp
    integer :: base, i

    vst => gc_my_stack()
    out = clause
    if (.not. gcv_is(fields)) return
    if (gcv_count(fields) == 0) return
    params = strip_meta(gcl_first(clause))
    if (.not. gcv_is(params)) return
    if (gcv_count(params) == 0) return
    this = strip_meta(gcv_nth(params, 0))
    if (this%tag /= GCT_SYM) return

    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, clause)
    call vs_set(vst, base + 2, fields)
    call vs_set(vst, base + 3, params)
    call vs_set(vst, base + 4, this)
    tmp = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 5, tmp)

    do i = 0, gcv_count(vs_get(vst, base + 2)) - 1
       f = strip_meta(gcv_nth(vs_get(vst, base + 2), i))
       if (f%tag /= GCT_SYM) cycle
       if (params_bind(vs_get(vst, base + 3), gc_ref_text(f%ref))) cycle
       tmp = gcv_conj(vs_get(vst, base + 5), f, [vs_get(vst, base + 5), f])
       call vs_set(vst, base + 5, tmp)
       tmp = field_read(vs_get(vst, base + 4), gc_ref_text(f%ref), &
            [vs_get(vst, base + 4), vs_get(vst, base + 5)])
       call vs_set(vst, base + 6, tmp)
       tmp = gcv_conj(vs_get(vst, base + 5), vs_get(vst, base + 6), &
            [vs_get(vst, base + 5), vs_get(vst, base + 6)])
       call vs_set(vst, base + 5, tmp)
    end do

    if (gcv_count(vs_get(vst, base + 5)) > 0) then
       ! (params (let* [f (. this -f) ...] body...))
       tmp = gcl_cons(vs_get(vst, base + 5), &
            gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 5)]), &
            [vs_get(vst, base + 1), vs_get(vst, base + 5)])
       call vs_set(vst, base + 6, tmp)
       tmp = gcl_cons(gc_sym("let*", [vs_get(vst, base + 6)]), vs_get(vst, base + 6), &
            [vs_get(vst, base + 1), vs_get(vst, base + 6)])
       call vs_set(vst, base + 6, tmp)
       tmp = gcl_cons(vs_get(vst, base + 6), gcl_empty([vs_get(vst, base + 6)]), &
            [vs_get(vst, base + 6)])
       call vs_set(vst, base + 6, tmp)
       out = gcl_cons(vs_get(vst, base + 3), vs_get(vst, base + 6), &
            [vs_get(vst, base + 3), vs_get(vst, base + 6)])
    end if
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: this
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, tmp
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, this)
    tmp = gcl_empty(roots)
    call vs_set(vst, base + 2, tmp)
    tmp = gc_sym("-" // name, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 2, gcl_cons(tmp, vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), tmp]))
    call vs_set(vst, base + 2, gcl_cons(vs_get(vst, base + 1), vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
    tmp = gc_sym(".", [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    out = gcl_cons(tmp, vs_get(vst, base + 2), [vs_get(vst, base + 2), tmp])
    call vs_leave(vst, base)
  end function field_read

  ! The type table. Keyed by the class keyword rather than the raw
  ! name so that a lookup here and an instance? test cannot disagree
  ! about java.lang.
  subroutine register_type(ty)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ty
    type(gc_value) :: tbl, k
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, ty)
    if (gc_root_live(types_root)) then
       call vs_set(vst, base + 2, gc_root_get(types_root))
    else
       call vs_set(vst, base + 2, gca_empty([vs_get(vst, base + 1)]))
    end if
    k = gc_class(short_class_name(class_text(vs_get(vst, base + 1))), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, k)
    tbl = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 1), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 2, tbl)
    ! Under the BARE name too, which is the (import clojure.core.Point)
    ! that deftype emits and that clotran has nowhere to record. It is
    ! what makes (Point. 3 4) and (new Point 3 4) find the type; see
    ! class_matches for what it costs.
    block
      character(len=:), allocatable :: full
      integer :: i, last_dot
      full = class_text(vs_get(vst, base + 1))
      last_dot = 0
      do i = 1, len(full)
         if (full(i:i) == ".") last_dot = i
      end do
      if (last_dot > 0 .and. last_dot < len(full)) then
         k = gc_class(full(last_dot+1:), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, k)
         tbl = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 1), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
         call vs_set(vst, base + 2, tbl)
      end if
    end block
    call gc_global_keep(types_root, vs_get(vst, base + 2))
    call vs_leave(vst, base)
  end subroutine register_type

  ! The type registered under a class name, or nil.
  function find_type(cname) result(out)
    type(gc_stack), pointer :: vst
    character(len=*), intent(in) :: cname
    type(gc_value) :: out, tbl
    integer :: base

    vst => gc_my_stack()
    out = gc_nil()
    if (.not. gc_root_live(types_root)) return
    base = vs_enter(vst, 1)
    tbl = gc_root_get(types_root)
    call vs_set(vst, base + 1, tbl)
    out = gca_get(vs_get(vst, base + 1), &
         gc_class(class_key(cname), [vs_get(vst, base + 1)]))
    ! A deftype is registered under its own name and under the bare
    ! last segment, and class_key qualifies a bare name with java.lang
    ! (canon_class) -- so (Point. 3 4) looks up java.lang.Point and
    ! must then try Point itself.
    if (gc_kind(out) /= OBJ_TYPE) out = gca_get(vs_get(vst, base + 1), &
         gc_class(cname, [vs_get(vst, base + 1)]))
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: given, fields
    type(gc_value) :: out, f, fill, tmp
    integer :: base, i

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, given)
    call vs_set(vst, base + 2, fields)
    call vs_set(vst, base + 3, vs_get(vst, base + 1))
    do i = gcv_count(vs_get(vst, base + 1)), gcv_count(vs_get(vst, base + 2)) - 1
       f = strip_meta(gcv_nth(vs_get(vst, base + 2), i))
       fill = gc_nil()
       if (f%tag == GCT_SYM) then
          if (gc_ref_is(f%ref, "__hash") .or. gc_ref_is(f%ref, "__hasheq")) &
               fill = gc_int(0)
       end if
       tmp = gcv_conj(vs_get(vst, base + 3), fill, [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, tmp)
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: inst, rest_args
    character(len=*), intent(in) :: name
    logical, intent(out) :: found
    type(gc_value) :: out, m, tmp
    integer :: base, i

    vst => gc_my_stack()
    out = gc_nil()
    found = .false.
    m = inst_method(inst, name)
    if (gc_kind(m) /= OBJ_CLOSURE) return
    found = .true.

    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, inst)
    call vs_set(vst, base + 2, m)
    call vs_set(vst, base + 3, rest_args)
    tmp = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, tmp)
    tmp = gcv_conj(vs_get(vst, base + 4), vs_get(vst, base + 1), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 4, tmp)
    do i = 0, gcv_count(vs_get(vst, base + 3)) - 1
       tmp = gcv_conj(vs_get(vst, base + 4), gcv_nth(vs_get(vst, base + 3), i), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, tmp)
    end do
    out = apply(vs_get(vst, base + 2), vs_get(vst, base + 4))
    call vs_leave(vst, base)
  end function inst_invoke

  ! The same, for the common no-extra-argument case.
  recursive function inst_invoke0(inst, name, found) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: inst
    character(len=*), intent(in) :: name
    logical, intent(out) :: found
    type(gc_value) :: out, empty
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, inst)
    empty = gcv_empty([vs_get(vst, base + 1)])
    out = inst_invoke(vs_get(vst, base + 1), name, empty, found)
    call vs_leave(vst, base)
  end function inst_invoke0

  ! The arguments from `from` onward, as a vector -- what a builtin
  ! has to hand inst_invoke once it has peeled off the target.
  function rest_args(args, from) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: args
    integer, intent(in) :: from
    type(gc_value) :: out, tmp
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, args)
    tmp = gcv_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, tmp)
    do i = from, gcv_count(vs_get(vst, base + 1)) - 1
       tmp = gcv_conj(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, tmp)
    end do
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function rest_args

  ! (get inst k) and (get inst k not-found) through the instance's own
  ! valAt. Both arities are real -- core_deftype defines valAt for each
  ! -- and the three-argument one is what makes a record distinguish a
  ! key bound to nil from a key that is absent.
  recursive function inst_lookup(inst, k, has_default, dflt, found) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: inst, k, dflt
    logical, intent(in) :: has_default
    logical, intent(out) :: found
    type(gc_value) :: out, argv, tmp
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, inst)
    call vs_set(vst, base + 2, k)
    call vs_set(vst, base + 3, dflt)
    tmp = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, tmp)
    tmp = gcv_conj(vs_get(vst, base + 4), vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 4, tmp)
    if (has_default) then
       tmp = gcv_conj(vs_get(vst, base + 4), vs_get(vst, base + 3), &
            [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, tmp)
    end if
    argv = vs_get(vst, base + 4)
    out = inst_invoke(vs_get(vst, base + 1), "valAt", argv, found)
    call vs_leave(vst, base)
  end function inst_lookup

  ! (= inst other) through the instance's own equiv.
  recursive function inst_equiv(inst, other, found) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: inst, other
    logical, intent(out) :: found
    type(gc_value) :: out, tmp
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, inst)
    call vs_set(vst, base + 2, other)
    tmp = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, tmp)
    tmp = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, tmp)
    out = inst_invoke(vs_get(vst, base + 1), "equiv", vs_get(vst, base + 3), found)
    call vs_leave(vst, base)
  end function inst_equiv

  ! (keys inst) / (vals inst), built from the instance's own seq --
  ! which hands back map entries, so the key is each entry's first and
  ! the value its second. Going through seq rather than reading the
  ! field vector directly is what makes a record's __extmap show up:
  ! an assoc'd key is not a field, but it IS in the seq.
  recursive function inst_entries(inst, want_keys, found) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: inst
    logical, intent(in) :: want_keys
    logical, intent(out) :: found
    type(gc_value) :: out, sq, items, e
    integer :: base, i

    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, inst)
    sq = inst_invoke0(vs_get(vst, base + 1), "seq", found)
    if (.not. found) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 2, sq)
    items = coll_to_vector(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 2, items)
    out = gcl_empty([vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    do i = gcv_count(vs_get(vst, base + 2)) - 1, 0, -1
       e = gcv_nth(vs_get(vst, base + 2), i)
       if (want_keys) then
          e = sq_first(e, [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       else
          e = sq_first(sq_rest(e, [vs_get(vst, base + 2), vs_get(vst, base + 3)]), &
               [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       end if
       out = gcl_cons(e, vs_get(vst, base + 3), [vs_get(vst, base + 2), vs_get(vst, base + 3), e])
       call vs_set(vst, base + 3, out)
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ty, m
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, fields, f, k, rest, vals, tmp
    integer :: base, i, declared

    vst => gc_my_stack()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, ty)
    call vs_set(vst, base + 2, m)
    fields = gc_slot(vs_get(vst, base + 1), 2)
    call vs_set(vst, base + 3, fields)
    declared = gcv_count(vs_get(vst, base + 3)) - alt_ctor_drops(vs_get(vst, base + 3))

    vals = gcv_empty(roots)
    call vs_set(vst, base + 4, vals)
    call vs_set(vst, base + 5, vs_get(vst, base + 2))
    do i = 0, declared - 1
       f = strip_meta(gcv_nth(vs_get(vst, base + 3), i))
       k = gc_key(gc_ref_text(f%ref), [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
       tmp = gcv_conj(vs_get(vst, base + 4), gca_get(vs_get(vst, base + 2), k), &
            [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5), k])
       call vs_set(vst, base + 4, tmp)
       rest = gca_dissoc(vs_get(vst, base + 5), k, &
            [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5), k])
       call vs_set(vst, base + 5, rest)
    end do

    ! __meta, then __extmap -- nil when nothing is left over, which is
    ! what (not-empty ...) gives everywhere else a record builds one.
    tmp = gcv_conj(vs_get(vst, base + 4), gc_nil(), [vs_get(vst, base + 4), vs_get(vst, base + 5)])
    call vs_set(vst, base + 4, tmp)
    rest = vs_get(vst, base + 5)
    if (gca_count(rest) == 0) rest = gc_nil()
    tmp = gcv_conj(vs_get(vst, base + 4), rest, [vs_get(vst, base + 4), vs_get(vst, base + 5)])
    call vs_set(vst, base + 4, tmp)

    tmp = pad_record_fields(vs_get(vst, base + 4), vs_get(vst, base + 3))
    call vs_set(vst, base + 4, tmp)
    out = gc_obj(OBJ_INST, [vs_get(vst, base + 1), vs_get(vst, base + 4), gc_nil()], &
         [vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: target0, argv
    character(len=*), intent(in) :: mname
    logical, intent(in) :: is_call, class_target
    type(gc_value) :: out, dty, tv
    logical :: found
    integer :: base

    vst => gc_my_stack()
    tctx => ctx_self()
    out = gc_nil()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, target0)
    call vs_set(vst, base + 2, argv)

    if (class_target) then
       ! A DEFTYPE CLASS in member position. The only static one has
       ! is a record's `create`, which is what map->Name calls.
       dty = find_type(gc_ref_text(target0%ref))
       if (gc_kind(dty) == OBJ_TYPE .and. mname == "create") then
          call vs_set(vst, base + 3, dty)
          out = record_create(vs_get(vst, base + 3), nth_or_nil(vs_get(vst, base + 2), 0), &
               [vs_get(vst, base + 3), vs_get(vst, base + 2)])
          call vs_leave(vst, base)
          return
       end if
       if (is_host_class(target0)) then
          out = static_member(gc_ref_text(target0%ref), mname, vs_get(vst, base + 2))
          if (.not. tctx%has_error) then
             if (is_call) out = apply(out, vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
          ! Not a static of that class: a member of the CLASS OBJECT
          ! -- (.isAssignableFrom String Object), (.getName String) --
          ! is an instance member of the keyword naming it, below.
          call gce_clear_error()
       end if
       ! A class literal is_host_class does not know evaluates to the
       ! keyword naming its type tag; the retry below sees it as one.
       call vs_set(vst, base + 1, gc_class(class_key(gc_ref_text(target0%ref)), [vs_get(vst, base + 2)]))
    end if

    ! A deftype/reify instance answers its own methods and fields
    ! FIRST. They are what the type declares, and a host member of the
    ! same name would otherwise shadow the implementation the program
    ! actually wrote.
    tv = strip_meta(vs_get(vst, base + 1))
    if (gc_kind(tv) == OBJ_INST .and. len(mname) > 0) then
       call vs_set(vst, base + 3, tv)
       ! (.-name x) is a field read and never a call; a bare name is
       ! a method if the type has one and a field otherwise, which
       ! is the order Compiler's HostExpr resolves them in. Written
       ! as a call, (. x (-name)), a leading dash is just part of the
       ! method's name -- protocol methods are often spelt that way,
       ! and a protocol fn reaches its type's method exactly so.
       if (mname(1:1) == "-" .and. .not. is_call) then
          out = inst_field(vs_get(vst, base + 3), mname(2:), found)
          if (.not. found) call fail("no such field: " // &
               class_text(vs_get(vst, base + 3)) // "." // mname(2:))
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 4, gca_get(gc_slot(gc_slot(vs_get(vst, base + 3), 1), 3), &
            gc_key(mname, [vs_get(vst, base + 3)])))
       ! Writer.append is a concrete method of the superclass that calls
       ! the write the proxy defined: (newline) is (.append *out* ...),
       ! and a proxy over Writer that only wrote `write` inherits it.
       if (gc_kind(vs_get(vst, base + 4)) /= OBJ_CLOSURE .and. mname == "append") then
          call vs_set(vst, base + 4, gca_get(gc_slot(gc_slot(vs_get(vst, base + 3), 1), 3), &
               gc_key("write", [vs_get(vst, base + 3)])))
          ! append(char) reaches write(int): the code point, not the char.
          if (gcv_count(vs_get(vst, base + 2)) == 1) then
             if (tag_of(gcv_nth(vs_get(vst, base + 2), 0)) == GCT_CHAR) then
                call vs_set(vst, base + 2, gcv_conj(gcv_empty([vs_get(vst, base + 3)]), &
                     gc_int(int_of(gcv_nth(vs_get(vst, base + 2), 0))), [vs_get(vst, base + 3)]))
             end if
          end if
       end if
       if (gc_kind(vs_get(vst, base + 4)) == OBJ_CLOSURE) then
          ! `this` is an explicit first parameter of the method, so
          ! the target is prepended exactly as for a host member. The
          ! call itself is the loop's to make (exec.inc enter_call),
          ! not a nested run: a method that blocks must be able to yield.
          call vs_set(vst, base + 2, cons_vec(vs_get(vst, base + 3), vs_get(vst, base + 2), [vs_get(vst, base + 4)]))
          out = call_request(vs_get(vst, base + 4), vs_get(vst, base + 2))
          call vs_leave(vst, base)
          return
       end if
       out = inst_field(vs_get(vst, base + 3), mname, found)
       if (found) then
          call vs_leave(vst, base)
          return
       end if
    end if

    ! A method called on nil is a NullPointerException, as on the JVM:
    ! (.toUpperCase nil) is how clojure.string's fns fail on nil there.
    if (.not. class_target) then
       tv = strip_meta(vs_get(vst, base + 1))
       if (tv%tag == GCT_NIL) then
          call raise_class("NullPointerException", "Cannot invoke ." // mname // " on nil", [vs_get(vst, base + 1)])
          call vs_leave(vst, base)
          return
       end if
    end if
    out = instance_member(mname, vs_get(vst, base + 1))
    if (.not. tctx%has_error) then
       ! The target is the first argument, which is all an instance
       ! method is: (.withMeta x m) calls with-meta on x and m.
       call vs_set(vst, base + 4, out)
       call vs_set(vst, base + 2, cons_vec(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 4)]))
       out = apply(vs_get(vst, base + 4), vs_get(vst, base + 2))
       call vs_leave(vst, base)
       return
    end if
    call gce_clear_error()

    if (mname == "setMacro" .and. gcn_is_var(vs_get(vst, base + 1))) then
       ! Var.setMacro is alterMeta(assoc, {:macro true}) -- macro-ness
       ! is METADATA ON THE VAR, not a flag on the function. That is
       ! what makes (:macro (meta (var when))) true, and what makes
       ! (def foo some-macro) bind a plain function rather than a macro.
       call var_set_macro(vs_get(vst, base + 1))
       out = gc_nil()
    else if (tv%tag == GCT_CLASS) then
       ! A class reached through a VARIABLE, not written as a
       ! literal. core.clj's `cast` is (. c (cast x)) with c a
       ! parameter, so the analysis -- which tests the symbol --
       ! cannot see it; by here the target has been evaluated and IS
       ! the class. Retrying it as a static member is what makes
       ! (cast Number 1.5) work, and any other class held in a
       ! variable with it.
       out = static_member(gc_ref_text(tv%ref), mname, vs_get(vst, base + 2))
       if (.not. tctx%has_error .and. is_call) out = apply(out, vs_get(vst, base + 2))
    else
       ! Reflector's words, class and count included: "No matching
       ! method jump found taking 1 args for class java.lang.String"
       block
         character(len=16) :: cbuf
         write(cbuf, '(I0)') gcv_count(vs_get(vst, base + 2))
         call raise_class("IllegalArgumentException", "No matching method " // mname // &
              " found taking " // trim(cbuf) // " args for class " // class_name_of(tv), [vs_get(vst, base + 1)])
       end block
    end if
    call vs_leave(vst, base)
  end function eval_dot

  ! [x, v...]
  function cons_vec(x, v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: x, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, x)
    call vs_set(vst, base + 2, v)
    out = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    out = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 1), [roots, vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    out = concat_vecs(vs_get(vst, base + 3), vs_get(vst, base + 2), [roots, vs_get(vst, base + 1)])
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    character(len=*), intent(in) :: cname
    type(gc_value), intent(in) :: argv
    type(gc_value) :: out, thunk
    integer :: base

    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, argv)

    if (cname == "java.util.concurrent.ArrayBlockingQueue" .or. cname == "ArrayBlockingQueue") then
       ! A queue is a task mailbox: an atom holding a vector. The
       ! capacity argument is read and ignored -- nothing here drops.
       call vs_set(vst, base + 3, gcv_empty([vs_get(vst, base + 1)]))
       out = gc_obj(OBJ_ATOM, [vs_get(vst, base + 3), gc_nil()], [vs_get(vst, base + 3)])
    else if (cname == "Thread" .or. cname == "java.lang.Thread") then
       ! (Thread. f name): the fn, held until .start submits it as a
       ! task. A thread IS a task here (PLAN.md: a thread is an
       ! evaluator context); the name is dropped.
       out = nth_or_nil(vs_get(vst, base + 1), 0)
    else if (cname == "MathContext" .or. cname == "java.math.MathContext") then
       ! (MathContext. precision) and (MathContext. precision mode) --
       ! a MAP with named fields, as MethodImplCache is, because
       ! nothing reads one but the arithmetic below. with-precision
       ! builds it and binds *math-context* to it.
       block
         type(gc_value) :: mc
         mc = gca_empty([vs_get(vst, base + 1)])
         call vs_set(vst, base + 3, mc)
         call vs_set(vst, base + 4, gc_key("precision", [vs_get(vst, base + 1), vs_get(vst, base + 3)]))
         mc = gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 4), nth_or_nil(vs_get(vst, base + 1), 0), &
              [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
         call vs_set(vst, base + 3, mc)
         call vs_set(vst, base + 4, gc_key("rounding", [vs_get(vst, base + 1), vs_get(vst, base + 3)]))
         call vs_set(vst, base + 5, gc_key("HALF_UP", [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)]))
         if (gcv_count(vs_get(vst, base + 1)) >= 2) call vs_set(vst, base + 5, gcv_nth(vs_get(vst, base + 1), 1))
         out = gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5), &
              [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
       end block
    else if (cname == "BigDecimal" .or. cname == "java.math.BigDecimal") then
       ! (BigDecimal. x), which core.cljs bigdec falls back to for a
       ! string and uses for a Ratio numerator.
       out = call_builtin(B_TODEC, vs_get(vst, base + 1))
    else if (cname == "BigInteger" .or. cname == "java.math.BigInteger") then
       ! (BigInteger. "12"), which core.clj's bigint falls back to for
       ! a string. There is one big integer type here, not two.
       out = call_builtin(B_TOBIG, vs_get(vst, base + 1))
    else if (cname == "clojure.lang.MapEntry") then
       ! (MapEntry. k v): a map entry is a two-vector marked as one
       ! (DEVIATIONS 39); clojure.spec.alpha's tagged-ret builds them
       call vs_set(vst, base + 3, gcv_empty([vs_get(vst, base + 1)]))
       out = gcv_conj(vs_get(vst, base + 3), nth_or_nil(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, out)
       out = gcv_conj(vs_get(vst, base + 3), nth_or_nil(vs_get(vst, base + 1), 1), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call mark_entry(out)
    else if (cname == "clojure.lang.Reduced") then
       ! (reduced x) wraps a value to say "stop reducing". A
       ! one-key map is enough to carry the mark and the value,
       ! and the key is one no Clojure program can write.
       call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 0))
       ! Two allocations in one argument list -- see range_cell.
       call vs_set(vst, base + 4, gca_empty([vs_get(vst, base + 3)]))
       call vs_set(vst, base + 5, gc_key("clotran/reduced", &
            [vs_get(vst, base + 3), vs_get(vst, base + 4)]))
       out = gca_assoc(vs_get(vst, base + 4), vs_get(vst, base + 5), &
            vs_get(vst, base + 3), [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
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
         mp = gca_empty([vs_get(vst, base + 1)])
         call vs_set(vst, base + 3, mp)
         do fi = 0, gcv_count(vs_get(vst, base + 1)) - 1
            select case (fi)
            case (0); fname = "sym"
            case (1); fname = "protocol"
            case (2); fname = "methodk"
            case default; fname = "map"
            end select
            mp = gca_assoc(vs_get(vst, base + 3), &
                 gc_key(trim(fname), [vs_get(vst, base + 3)]), gcv_nth(vs_get(vst, base + 1), fi), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, mp)
         end do
         if (gcv_count(vs_get(vst, base + 1)) < 4) then
            ! Two allocations in one argument list -- see range_cell.
            call vs_set(vst, base + 4, gc_key("map", [vs_get(vst, base + 3)]))
            call vs_set(vst, base + 5, gca_empty([vs_get(vst, base + 3), vs_get(vst, base + 4)]))
            mp = gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5), &
                 [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
            call vs_set(vst, base + 3, mp)
         end if
         out = vs_get(vst, base + 3)
       end block
    else if (cname == "CountDownLatch" .or. &
         cname == "java.util.concurrent.CountDownLatch") then
       ! A LATCH IS A COUNTER when there is one thread. `await`
       ! sends a count-down action to each agent and then waits
       ! on the latch -- and since dispatch here runs the action
       ! before it returns, the count is already zero by the time
       ! anything waits. So: an atom holding the count, .countDown
       ! decrements it, and .await has nothing to wait for.
       call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 0))
       out = gc_obj(OBJ_ATOM, [vs_get(vst, base + 3), gc_nil()], [vs_get(vst, base + 3)])
    else if (cname == "clojure.lang.Ref" .or. cname == "clojure.lang.Atom" .or. &
         cname == "clojure.lang.Agent") then
       ! A Ref IS an atom here: a mutable box, with no transaction
       ! around it. Single-threaded that is indistinguishable; the
       ! moment threads arrive it is not. DEVIATIONS.md 9.
       call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 0))
       out = gc_obj(OBJ_ATOM, [vs_get(vst, base + 3), gc_nil()], [vs_get(vst, base + 3)])
    else if (cname == "java.util.Properties" .or. cname == "Properties") then
       thunk = gca_empty([vs_get(vst, base + 1)])
       call vs_set(vst, base + 3, thunk)
       out = gc_obj(OBJ_ATOM, [vs_get(vst, base + 3), gc_nil()], [vs_get(vst, base + 3)])
    else if (is_box_class(cname)) then
       ! THE BOXING CONSTRUCTORS. (Long. 1) is 1, (String. "x") is
       ! "x" -- on the JVM they wrap a primitive in an object, and
       ! there is no unboxed number here to wrap. What they do have
       ! to do is CONVERT, because (Long. "12") parses and
       ! (Double. 1) widens, so each runs the same cast its
       ! valueOf does.
       if (gcv_count(vs_get(vst, base + 1)) < 1) then
          call fail("no matching constructor: " // cname)
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 3, gcv_nth(vs_get(vst, base + 1), 0))
       out = box_convert(cname, vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    else if (cname == "PrintWriter" .or. cname == "java.io.PrintWriter" .or. &
         cname == "BufferedWriter" .or. cname == "java.io.BufferedWriter") then
       ! A PrintWriter over a writer IS that writer here. Java's
       ! wraps to add buffering and the print methods; clotran's
       ! writers already take text and hold it, so wrapping would
       ! only add a layer that forwards. What matters is that
       ! (let [s (StringWriter.) p (PrintWriter. s)] ... (str s))
       ! sees what was written to p, which sharing gives directly.
       if (gcv_count(vs_get(vst, base + 1)) > 0) then
          thunk = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
          if (gc_kind(thunk) == OBJ_SB .or. gc_kind(thunk) == OBJ_WRITER) then
             out = thunk
             call vs_leave(vst, base)
             return
          end if
       end if
       thunk = gc_str("", [vs_get(vst, base + 1)])
       call vs_set(vst, base + 3, thunk)
       out = gc_obj(OBJ_SB, [vs_get(vst, base + 3)], [vs_get(vst, base + 3)])
    else if (cname == "StringBuilder" .or. cname == "java.lang.StringBuilder" .or. &
         cname == "StringBuffer" .or. cname == "java.lang.StringBuffer" .or. &
         cname == "java.io.StringWriter" .or. cname == "StringWriter") then
       ! (StringBuffer. n) is a CAPACITY, not content -- the buffer
       ! starts empty. clojure.string/replace writes
       ! (StringBuffer. (.length s)) and every replacement it built
       ! came out with the length stuck on the front.
       thunk = gc_str("", [vs_get(vst, base + 1)])
       if (gcv_count(vs_get(vst, base + 1)) > 0) then
          thunk = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
          if (thunk%tag == GCT_INT) thunk = gc_str("", [vs_get(vst, base + 1)])
          if (thunk%tag == GCT_NIL) then
             ! (StringBuilder. nil) is a NullPointerException, which is
             ! how clojure.string/reverse fails on nil
             call raise_class("NullPointerException", "StringBuilder of nil", [vs_get(vst, base + 1)])
             call vs_leave(vst, base)
             return
          end if
       end if
       call vs_set(vst, base + 3, thunk)
       out = gc_obj(OBJ_SB, [vs_get(vst, base + 3)], [vs_get(vst, base + 3)])
    else if (cname == "clojure.lang.ChunkBuffer") then
       ! (ChunkBuffer. capacity): a run to fill, count in i1
       thunk = gc_vec(max(int_of(nth_or_nil(vs_get(vst, base + 1), 0)), 1), [vs_get(vst, base + 1)])
       call vs_set(vst, base + 3, thunk)
       out = gc_obj(OBJ_CHUNKBUF, [vs_get(vst, base + 3)], [vs_get(vst, base + 3)])
       call gc_set_i1(out, 0)
    else if (cname == "clojure.lang.ChunkedCons") then
       ! (ChunkedCons. chunk more)
       out = gc_obj(OBJ_CHUNKSEQ, [nth_or_nil(vs_get(vst, base + 1), 0), nth_or_nil(vs_get(vst, base + 1), 1), gc_nil()], &
            [vs_get(vst, base + 1)])
    else if (cname == "clojure.lang.MultiFn") then
       ! (new MultiFn name dispatch-fn default hierarchy): name, the
       ! dispatch fn, the default value and the method table in slots
       ! 1-4, and in slot 5 [hierarchy-ref prefers cache cached-hierarchy]
       ! for mf_lookup
       call vs_set(vst, base + 3, gcv_build(4, [vs_get(vst, base + 1)]))
       thunk = gcv_put(vs_get(vst, base + 3), 0, nth_or_nil(vs_get(vst, base + 1), 3), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, thunk)
       thunk = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 4, thunk)
       thunk = gcv_put(vs_get(vst, base + 3), 1, vs_get(vst, base + 4), [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 3, thunk)
       thunk = gcv_put(vs_get(vst, base + 3), 2, vs_get(vst, base + 4), [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 3, thunk)
       thunk = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 4, thunk)
       out = gc_obj(OBJ_MULTIFN, &
            [nth_or_nil(vs_get(vst, base + 1), 0), nth_or_nil(vs_get(vst, base + 1), 1), &
             nth_or_nil(vs_get(vst, base + 1), 2), vs_get(vst, base + 4), vs_get(vst, base + 3)], &
            [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    else if (cname == "clojure.lang.Delay") then
       ! (delay body) is (new clojure.lang.Delay (fn [] body)) in
       ! core.clj, so the argument is already a no-argument closure and
       ! nothing here needs to know about the body.
       call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 0))
       out = gc_obj(OBJ_DELAY, [vs_get(vst, base + 3), gc_nil()], [vs_get(vst, base + 3)])
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
       thunk = gcv_empty([vs_get(vst, base + 1)])
       call vs_set(vst, base + 3, thunk)
       out = gc_obj(OBJ_ATOM, [vs_get(vst, base + 3), gc_nil()], [vs_get(vst, base + 3)])
    else if (cname == "clojure.lang.LazySeq") then
       call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 0))
       out = gc_obj(OBJ_LAZY, [vs_get(vst, base + 3), gc_nil(), gc_nil()], &
            [vs_get(vst, base + 3)])
       call gc_set_i1(out, LAZY_PENDING)
    else if (is_throwable_class(cname)) then
       ! Every exception class core.clj names takes a message, and
       ! ex-info adds a data map. Anything else about a Java exception
       ! -- its hierarchy, its stack trace -- has nothing to correspond
       ! to here, so the class name is kept as written and nothing is
       ! invented around it.
       block
         logical :: is_info
         type(gc_value) :: cause
         is_info = (cname == "ExceptionInfo" .or. cname == "clojure.lang.ExceptionInfo")
         ! ex-info's data, an empty map when given nil; other classes carry none
         call vs_set(vst, base + 3, gc_nil())
         if (is_info) then
            call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 1))
            thunk = vs_get(vst, base + 3)
            if (thunk%tag == GCT_NIL) call vs_set(vst, base + 3, gca_empty([vs_get(vst, base + 1)]))
         end if
         out = gc_obj(OBJ_ERR, &
              [gc_sym(cname, [vs_get(vst, base + 1), vs_get(vst, base + 3)]), &
               nth_or_nil(vs_get(vst, base + 1), 0), &
               vs_get(vst, base + 3)], &
              [vs_get(vst, base + 1), vs_get(vst, base + 3)])
         ! filled in at construction, as Throwable's constructor does
         call vs_set(vst, base + 3, out)
         call gc_set_slot(vs_get(vst, base + 3), 4, frames_vec([vs_get(vst, base + 3)]))
         ! the cause, in slot 5: ex-info's third argument, any other
         ! class's second -- what getCause, ex-cause and Throwable->map's
         ! :via chain read
         if (is_info) then
            cause = nth_or_nil(vs_get(vst, base + 1), 2)
         else
            ! the LAST argument, when it is one: (Exception. msg cause), and
            ! (CompilerException. file line col cause)
            cause = gc_nil()
            if (gcv_count(vs_get(vst, base + 1)) >= 2) cause = gcv_nth(vs_get(vst, base + 1), gcv_count(vs_get(vst, base + 1)) - 1)
         end if
         if (gc_kind(strip_meta(cause)) == OBJ_ERR) call gc_set_slot(vs_get(vst, base + 3), 5, cause)
         out = vs_get(vst, base + 3)
       end block
    else if (cname == "Volatile" .or. cname == "clojure.lang.Volatile") then
       ! volatile!: a box, deref'd and .reset, with none of an atom's
       ! validators or watches
       call vs_set(vst, base + 3, nth_or_nil(vs_get(vst, base + 1), 0))
       out = gc_obj(OBJ_VOLATILE, [vs_get(vst, base + 3)], [vs_get(vst, base + 3)])
    else if (cname == "ArrayList" .or. cname == "java.util.ArrayList") then
       ! Clojure on this host: clotran.rt's ArrayList (rt_call)
       out = rt_call("array-list", vs_get(vst, base + 1))
    else if (cname == "Eduction" .or. cname == "clojure.lang.Eduction") then
       out = rt_call("->Eduction", vs_get(vst, base + 1))
    else if (cname == "Object" .or. cname == "java.lang.Object") then
       ! (Object.), a sentinel equal only to itself
       out = rt_call("object", vs_get(vst, base + 1))
    else
       ! A type deftype* created. Last, so nothing above is shadowed
       ! by a deftype that happens to pick one of those names.
       thunk = find_type(cname)
       if (gc_kind(thunk) == OBJ_TYPE) then
          call vs_set(vst, base + 3, thunk)
          out = construct_type_vals(vs_get(vst, base + 3), vs_get(vst, base + 1))
       else
          call fail("no such class: " // cname)
       end if
    end if
    call vs_leave(vst, base)
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
       if (v%tag == GCT_INT) out = gc_char_cp(int(v%ival, kind=4))
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
  ! RT.DEFAULT_IMPORTS names java.math.BigDecimal and
  ! java.math.BigInteger in every namespace, which is why core.clj
  ! writes (. BigDecimal valueOf x) with no import of its own. Seeded
  ! here rather than left to canon_class, which would answer
  ! java.lang.BigDecimal and find no row.
  subroutine seed_default_imports()
    if (n_imports > 0) return
    call record_import("java.math.BigDecimal")
    call record_import("java.math.BigInteger")
  end subroutine seed_default_imports

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
  ! The ONE spelling a class has, wherever it is built: the canonical
  ! name IN FULL, so String and java.lang.String are both
  ! java.lang.Class's java.lang.String and (pr-str (class 1)) is
  ! java.lang.Long, as it is on the JVM. A bare name nothing imported
  ! stays bare, which is what a deftype's own name is.
  function class_key(name) result(k)
    character(len=*), intent(in) :: name
    character(len=:), allocatable :: k
    k = canon_class(name)
  end function class_key


  ! Whether a name is a class this runtime KNOWS -- what
  ! Compiler.maybeClass answers by asking the class loader, and what
  ! (resolve (quote NonExistentClass.Name)) must answer nil for. A row
  ! in the host table, a deftype, or a package clotran models: the
  ! last is a compromise, since there is no loader to ask, and it
  ! keeps (resolve (quote clojure.lang.PersistentVector)) answering a
  ! class while a made-up package answers nil.
  logical function known_class_name(t) result(yes)
    character(len=*), intent(in) :: t
    yes = .true.
    ! By TEXT, allocating nothing: this runs inside analysis, where a
    ! fresh symbol would be a value the collector cannot see. The
    ! name is the one WRITTEN, not the canonical one -- canon_class
    ! qualifies every bare name with java.lang, and the prefix rule
    ! below would then accept anything at all.
    if (any(HOST_STATICS(:)%cls == canon_class(t))) return
    if (any(HOST_METHODS(:)%cls == canon_class(t))) return
    if (gc_kind(find_type(t)) == OBJ_TYPE) return
    if (index(t, "clojure.lang.") == 1) return
    if (index(t, "clojure.asm.") == 1) return
    if (index(t, "java.") == 1) return
    yes = .false.
  end function known_class_name

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
    case (HK_TRUE);     out = gc_bool(.true.)
    case (HK_FALSE);    out = gc_bool(.false.)
    case (HK_LINEBOX);  out = gc_obj(OBJ_ATOM, [gc_int(0_gc_ip), gc_nil()], [roots])
    case (HK_NIL);      out = gc_nil()
    case (HK_EMPTYMAP); out = gca_empty([roots])
    case (HK_SPECIALS); out = specials_map([roots])
    case (HK_TYPE);     out = gc_key(short_class_name(trim(row%cls)) // "/TYPE", [roots])
    case (HK_SELFKEY);  out = gc_key(trim(row%mem), [roots])
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: var
    type(gc_value) :: md
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, var)
    md = gc_slot(vs_get(vst, base + 1), 2)
    if (.not. gca_is(md)) md = gca_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, md)
    md = gca_assoc(vs_get(vst, base + 2), gc_key("macro", [vs_get(vst, base + 1)]), &
         gc_bool(.true.), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_slot(vs_get(vst, base + 1), 2, md)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: class_name, msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: e, cls, txt
    integer :: base

    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 2)
    cls = gc_sym(class_name, roots)
    call vs_set(vst, base + 1, cls)
    txt = gc_str(msg, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, txt)
    e = gc_obj(OBJ_ERR, [vs_get(vst, base + 1), vs_get(vst, base + 2), gc_nil()], &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call set_thrown(e)
    tctx%has_error = .true.
    tctx%last_error = gcp_str(e, .true.)
    call vs_leave(vst, base)
  end subroutine fail_as

  function is_runtime_class(cname) result(yes)
    character(len=*), intent(in) :: cname
    logical :: yes
    integer :: dot
    dot = index(cname, ".", back=.true.)
    select case (cname(dot+1:))
    case ("RuntimeException", "ArithmeticException", "ArityException", "ClassCastException", &
          "IllegalArgumentException", "IllegalStateException", "IndexOutOfBoundsException", &
          "NullPointerException", "NumberFormatException", "UnsupportedOperationException", &
          "ExceptionInfo", "NoSuchElementException", "ConcurrentModificationException", &
          "ArrayIndexOutOfBoundsException", "StringIndexOutOfBoundsException", "NegativeArraySizeException")
       yes = .true.
    case default
       yes = .false.
    end select
  end function is_runtime_class

  ! Whether an exception object answers to a class name: its own,
  ! under either spelling, or through the two edges of hierarchy --
  ! and Throwable and Exception take anything. Asked by catch and by
  ! instance?, so an agent's error handler can tell an
  ! ArithmeticException from the rest.
  logical function exc_class_matches(want, exc)
    character(len=*), intent(in) :: want
    type(gc_value), intent(in) :: exc
    type(gc_value) :: got
    exc_class_matches = .true.
    if (want == "Throwable" .or. want == "java.lang.Throwable" .or. &
         want == "Exception" .or. want == "java.lang.Exception") return
    exc_class_matches = .false.
    if (gc_kind(exc) /= OBJ_ERR) return
    got = gc_slot(exc, 1)
    if (got%tag /= GCT_SYM) return
    ! RuntimeException is the parent of every runtime class clotran
    ! throws, a host failure among them; only the checked classes and
    ! the Errors stand outside it.
    if (want == "RuntimeException" .or. want == "java.lang.RuntimeException") then
       exc_class_matches = is_runtime_class(gc_ref_text(got%ref))
       return
    end if
    ! Either spelling. The class name is kept as the THROWING
    ! code wrote it, and the catch names it however the catching
    ! code wrote it -- ex-info constructs an ExceptionInfo under
    ! its short imported name, and Clojure's own suite catches
    ! clojure.lang.ExceptionInfo. class_matches knows the rule
    ! but only in one direction, so it is asked both ways.
    exc_class_matches = class_matches(gc_ref_text(got%ref), want) .or. &
         class_matches(want, gc_ref_text(got%ref))
    ! The other fact of hierarchy, because Clojure's own suite relies
    ! on it: ArityException extends IllegalArgumentException, so
    ! (thrown? IllegalArgumentException (f)) catches a bad-arity
    ! call. Beyond these two edges clotran's classes form no
    ! hierarchy (DEVIATIONS 4).
    if (.not. exc_class_matches) then
       if (gc_ref_is(got%ref, "ArityException")) &
            exc_class_matches = class_matches("IllegalArgumentException", want)
    end if
  end function exc_class_matches

  recursive function catch_matches(cls, exc, env) result(yes)
    type(gc_value), intent(in) :: cls, exc, env
    logical :: yes
    yes = .true.
    if (cls%tag /= GCT_SYM) return
    yes = exc_class_matches(gc_ref_text(cls%ref), exc)
  end function catch_matches

  ! {:error "message"} -- an internal failure as an ordinary clotran
  ! map, so it prints, can be destructured, and is distinguishable
  ! from any value a program might itself throw.
  function error_value(msg, roots) result(v)
    type(gc_stack), pointer :: vst
    character(len=*), intent(in) :: msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, k, text
    integer :: base

    ! An exception object, of class RuntimeException -- what most of
    ! the JVM's own runtime failures are -- so (.getMessage e),
    ! ex-message and (catch RuntimeException e) all work on a host
    ! error. It was {:error msg}, a map, and none of them did.
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    k = gc_sym("RuntimeException", roots)
    call vs_set(vst, base + 2, k)
    text = gc_str(msg, [roots, vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, text)
    v = gc_obj(OBJ_ERR, [vs_get(vst, base + 2), vs_get(vst, base + 3), gc_nil()], &
         [roots, vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_leave(vst, base)
  end function error_value

  ! Raise a CLASSED exception, the way a (throw (Foo. msg)) in
  ! Clojure source would. `fail` alone produces clotran's
  ! internal {:error "..."} map, which no (catch SomeClass e)
  ! can match -- so an error clotran raises itself was
  ! uncatchable by name however well the message read.
  subroutine raise_class(cls, msg, roots)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: cls, msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: e
    integer :: base

    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, gc_sym(cls, roots))
    call vs_set(vst, base + 2, gc_str(msg, [roots, vs_get(vst, base + 1)]))
    e = gc_obj(OBJ_ERR, [vs_get(vst, base + 1), vs_get(vst, base + 2), gc_nil()], &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call set_thrown(e)
    tctx%has_error = .true.
    tctx%last_error = msg
    call vs_leave(vst, base)
  end subroutine raise_class

  ! identical?: the same slot for a reference, the same value for an
  ! immediate.
  function same_object(a, b) result(yes)
    type(gc_value), intent(in) :: a, b
    logical :: yes
    yes = a%tag == b%tag .and. a%ref == b%ref .and. a%ival == b%ival
    if (yes .and. a%rval /= b%rval) yes = (a%rval /= a%rval .and. b%rval /= b%rval)
  end function same_object

  ! raise_arity for a function known by name -- a compiled one, whose
  ! procedure picks its own arity (ClotranABI, clotran_arity_error).
  subroutine gce_raise_arity_named(got, who)
    integer, intent(in) :: got
    character(len=*), intent(in) :: who
    character(len=16) :: buf
    type(gc_value) :: none(0)
    write(buf, '(I0)') got
    call raise_class("ArityException", "Wrong number of args (" // trim(buf) // ") passed to: " // who, none)
  end subroutine gce_raise_arity_named

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

  ! Everything but the first n of a vector, as a vector.
  function gcv_subvec_from(v, n, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, v)
    out = gcv_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, out)
    do i = n, gcv_count(vs_get(vst, base + 1)) - 1
       out = gcv_conj(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, out)
    end do
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function gcv_subvec_from

  ! Step whatever tasks can run right now. tap> needs it: the loop
  ! that drains the tap queue is a task parked on that queue, and
  ! with one OS thread nothing else would ever wake it.
  recursive subroutine run_ready_tasks(target)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: target
    type(gc_value) :: t
    logical :: sleeping
    integer :: guard
    tctx => ctx_self()
    guard = 0
    do
       guard = guard + 1
       if (guard > 64) exit
       t = pick_runnable(gc_nil(), sleeping)
       if (gc_kind(t) /= OBJ_TASK) exit
       call task_step(t)
       if (tctx%has_error) exit
    end do
  end subroutine run_ready_tasks

  ! Every watch on a reference, called with the key, the reference,
  ! the old value and the new one -- IRef.notifyWatches, which runs
  ! AFTER the change is in place, so a watch that reads the reference
  ! sees the new value.
  recursive subroutine notify_watches(r, oldv, newv, roots)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: r, oldv, newv
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: w, fargs, res
    type(gc_value), allocatable :: ks(:), fs(:)
    integer :: base, i
    vst => gc_my_stack()
    tctx => ctx_self()
    if (r%tag /= GCT_OBJ) return
    w = ref_fn_get(r, "watches", roots)
    if (.not. gca_is(w)) return
    if (gca_count(w) == 0) return
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, r)
    call vs_set(vst, base + 2, w)
    call vs_set(vst, base + 3, oldv)
    call vs_set(vst, base + 4, newv)
    call gca_entries(vs_get(vst, base + 2), ks, fs)
    do i = 1, size(ks)
       if (tctx%has_error) exit
       fargs = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       fargs = gcv_conj(fargs, ks(i), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4), fargs])
       fargs = gcv_conj(fargs, vs_get(vst, base + 1), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4), fargs])
       fargs = gcv_conj(fargs, vs_get(vst, base + 3), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4), fargs])
       fargs = gcv_conj(fargs, vs_get(vst, base + 4), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4), fargs])
       res = apply(fs(i), fargs)
    end do
    call vs_leave(vst, base)
  end subroutine notify_watches

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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: r, v
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    integer :: base
    vst => gc_my_stack()
    if (r%tag /= GCT_OBJ) return
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, r)
    call vs_set(vst, base + 2, v)
    m = gc_slot(vs_get(vst, base + 1), 4)
    if (.not. gca_is(m)) m = gca_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, m)
    call vs_set(vst, base + 3, gca_assoc(vs_get(vst, base + 3), &
         gc_key(name, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]), &
         vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]))
    call gc_set_slot(vs_get(vst, base + 1), 4, vs_get(vst, base + 3))
    call vs_leave(vst, base)
  end subroutine ref_fn_put

  ! Whether `v` passes `f`. A nil validator passes everything;
  ! anything else must answer truthy, and a false answer is an
  ! IllegalStateException with Clojure's own wording.
  function validate_ref(r, f, v, roots) result(ok)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: r, f, v
    type(gc_value), intent(in) :: roots(:)
    logical :: ok
    type(gc_value) :: fargs, res
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    ok = .true.
    if (f%tag == GCT_NIL) return
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, f)
    call vs_set(vst, base + 2, v)
    fargs = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    fargs = gcv_conj(fargs, vs_get(vst, base + 2), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 2, fargs)
    res = apply(vs_get(vst, base + 1), vs_get(vst, base + 2))
    if (tctx%has_error) then
       ok = .false.
    else if (.not. truthy(res)) then
       ok = .false.
       call raise_class("IllegalStateException", "Invalid reference state", roots)
    end if
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: v
    type(gc_value) :: r, args
    integer :: base

    vst => gc_my_stack()
    tctx => ctx_self()
    if (gc_kind(v) /= OBJ_LAZY) return
    if (gc_i1(v) /= LAZY_PENDING) return
    ! NOT while an error is in flight. `apply` refuses to run anything
    ! with has_error set, so forcing here would answer nothing and the
    ! cell would be cached as EMPTY -- permanently, for every later
    ! reader. That is how a lazy seq inside an exception's ex-data came
    ! back empty in the catch handler: raising the error printed the
    ! map, printing forced the seq, and the seq was gone. Leave it
    ! pending; whoever forces it after the error is handled gets the
    ! real elements.
    if (tctx%has_error) return

    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, v)
    select case (gc_i2(vs_get(vst, base + 1)))
    case (1)
       ! a native range tail: slot 1 = [lo hi step]
       args = gc_slot(vs_get(vst, base + 1), 1)
       r = range_cell(gcv_nth(args, 0), gcv_nth(args, 1), gcv_nth(args, 2), [vs_get(vst, base + 1)])
    case (2)
       ! a native iterate tail: slot 1 = [f x]; the next head is (f x)
       args = gc_slot(vs_get(vst, base + 1), 1)
       call vs_set(vst, base + 2, gcv_conj(gcv_empty([vs_get(vst, base + 1)]), gcv_nth(args, 1), [vs_get(vst, base + 1)]))
       r = apply(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 0), vs_get(vst, base + 2))
       if (.not. tctx%has_error) then
          call vs_set(vst, base + 2, r)
          r = iterate_cell(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 0), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
       end if
    case default
       args = gcv_empty([vs_get(vst, base + 1)])
       r = apply(gc_slot(vs_get(vst, base + 1), 1), args)
    end select
    call vs_set(vst, base + 2, r)
    if (tctx%has_error) then
       ! The thunk threw. Clojure's LazySeq caches nothing in that case --
       ! it keeps the fn, and the next seq call runs it again and throws
       ! again -- so the cell stays PENDING rather than becoming an
       ! empty seq that silently swallows the failure.
       call vs_leave(vst, base)
       return
    end if

    do while (gc_kind(vs_get(vst, base + 2)) == OBJ_LAZY)
       call gce_force(vs_get(vst, base + 2))
       if (gc_i1(vs_get(vst, base + 2)) == LAZY_DELEG) then
          call gc_set_slot(vs_get(vst, base + 1), 2, gc_slot(vs_get(vst, base + 2), 2))
          call gc_set_i1(vs_get(vst, base + 1), LAZY_DELEG)
          call vs_leave(vst, base)
          return
       end if
       if (gc_i1(vs_get(vst, base + 2)) == LAZY_CONS) then
          call gc_set_slot(vs_get(vst, base + 1), 2, gc_slot(vs_get(vst, base + 2), 2))
          call gc_set_slot(vs_get(vst, base + 1), 3, gc_slot(vs_get(vst, base + 2), 3))
          call gc_set_i1(vs_get(vst, base + 1), LAZY_CONS)
          call vs_leave(vst, base)
          return
       end if
       call gc_set_i1(vs_get(vst, base + 1), LAZY_EMPTY)
       call vs_leave(vst, base)
       return
    end do

    r = vs_get(vst, base + 2)
    if (gc_kind(r) == OBJ_CHUNKSEQ) then
       ! A CHUNK SURVIVES THE LAZY SEQ. map, filter, keep and for all
       ! return (lazy-seq ... (chunk-cons (chunk b) ...)), and splitting
       ! that into a head and a tail here is what made every one of them
       ! answer a plain lazy seq: chunked-seq? was then false on it, so
       ! the next map down the pipeline took the one-at-a-time branch and
       ! the chunking never propagated past the first collection.
       call gc_set_slot(vs_get(vst, base + 1), 2, r)
       call gc_set_i1(vs_get(vst, base + 1), LAZY_DELEG)
       call vs_leave(vst, base)
       return
    end if
    if (gcl_is(r)) then
       if (gcl_count(r) == 0) then
          call gc_set_i1(vs_get(vst, base + 1), LAZY_EMPTY)
       else
          call gc_set_slot(vs_get(vst, base + 1), 2, gcl_first(r))
          call gc_set_slot(vs_get(vst, base + 1), 3, gcl_rest(r, [vs_get(vst, base + 1)]))
          call gc_set_i1(vs_get(vst, base + 1), LAZY_CONS)
       end if
    else if (gcv_is(r)) then
       if (gcv_count(r) == 0) then
          call gc_set_i1(vs_get(vst, base + 1), LAZY_EMPTY)
       else
          call gc_set_slot(vs_get(vst, base + 1), 2, gcv_nth(r, 0))
          call gc_set_slot(vs_get(vst, base + 1), 3, &
               as_list_rest(r, [vs_get(vst, base + 1)]))
          call gc_set_i1(vs_get(vst, base + 1), LAZY_CONS)
       end if
    else
       ! ANYTHING ELSE SEQABLE, through seq. A thunk may return a view
       ! over a vector, a set, a map or a string -- (drop 2 [1 2 3 4])
       ! returns a view -- and treating those as EMPTY was silent: drop
       ! worked on a list and gave () on a vector, and take-nth built on
       ! drop then truncated every destructuring loop binding.
       block
         type(gc_value) :: sv
         sv = to_seq(vs_get(vst, base + 2), [vs_get(vst, base + 1)])
         if (sv%tag == GCT_NIL) then
            call gc_set_i1(vs_get(vst, base + 1), LAZY_EMPTY)
         else
            call vs_set(vst, base + 2, sv)
            call gc_set_slot(vs_get(vst, base + 1), 2, &
                 sq_first(vs_get(vst, base + 2), [vs_get(vst, base + 1)]))
            call gc_set_slot(vs_get(vst, base + 1), 3, &
                 sq_rest(vs_get(vst, base + 2), [vs_get(vst, base + 1)]))
            call gc_set_i1(vs_get(vst, base + 1), LAZY_CONS)
         end if
       end block
    end if
    call vs_leave(vst, base)
  end subroutine gce_force

  ! Everything but the first element of a vector, as a list.
  function as_list_rest(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, v)
    out = gcl_empty(roots)
    call vs_set(vst, base + 2, out)
    do i = gcv_count(vs_get(vst, base + 1)) - 1, 1, -1
       out = gcl_cons(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2), &
            [vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, out)
    end do
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function as_list_rest

  ! Applies a macro to the unevaluated argument forms.
  ! Compiler.macroexpand1: an ArityException thrown by the MACRO ITSELF
  ! is rethrown with &form and &env taken off the count, so the message
  ! says what the caller wrote; one from inside its body is left alone.
  ! The macro is known by the name its exception carries.
  subroutine macro_arity_fixup(mvar)
    type(gc_value), intent(in) :: mvar
    type(gc_value) :: e, cls, ns, sym
    character(len=:), allocatable :: msg, name
    character(len=16) :: cbuf
    integer :: p, q, n, st
    e = thrown_value()
    if (gc_kind(e) /= OBJ_ERR) return
    cls = gc_slot(e, 1)
    if (cls%tag /= GCT_SYM) return
    if (.not. gc_ref_is(cls%ref, "ArityException")) return
    ns = gc_slot(mvar, 3)
    sym = gc_slot(mvar, 4)
    if (gc_kind(ns) /= OBJ_NS .or. sym%tag /= GCT_SYM) return
    name = gcn_name(ns) // "/" // gc_ref_text(sym%ref)
    msg = text_of(gc_slot(e, 2))
    q = index(msg, "passed to: ")
    if (q == 0) return
    if (msg(q+11:) /= name) return
    p = index(msg, "(")
    q = index(msg, ")")
    if (p == 0 .or. q <= p + 1) return
    read(msg(p+1:q-1), *, iostat=st) n
    if (st /= 0) return
    write(cbuf, '(I0)') n - 2
    call gce_clear_error()
    call raise_class("ArityException", "Wrong number of args (" // trim(cbuf) // ") passed to: " // name, [mvar])
  end subroutine macro_arity_fixup

  recursive function expand_macro(fn, form, env, mvar) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: fn, form, env
    type(gc_value), intent(in), optional :: mvar
    type(gc_value) :: out, args, walk
    integer :: base

    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, fn)
    call vs_set(vst, base + 2, form)
    call vs_set(vst, base + 5, env)
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
    args = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
    args = gcv_conj(args, vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    args = gcv_conj(args, vs_get(vst, base + 5), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, args)
    walk = gcl_rest(vs_get(vst, base + 2), [vs_get(vst, base + 2)])
    call vs_set(vst, base + 4, walk)
    do while (gcl_count(vs_get(vst, base + 4)) > 0)
       args = gcv_conj(vs_get(vst, base + 3), gcl_first(vs_get(vst, base + 4)), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4)])
       call vs_set(vst, base + 3, args)
       walk = gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 2)])
       call vs_set(vst, base + 4, walk)
    end do
    out = apply(vs_get(vst, base + 1), vs_get(vst, base + 3))
    if (tctx%has_error .and. present(mvar)) call macro_arity_fixup(mvar)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
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
    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, env)

    if (gcv_is(form)) then
       ! `[a ~b] -- a vector inside syntax-quote. Expanded as a seq and
       ! rebuilt, which is what LispReader does: (apply vector (seq
       ! (concat ...))). Without this a vector passed straight through
       ! and every unquote inside it stayed literal, which is most of
       ! what a (let [...]) template is.
       out = qq_rebuild(form, "vec", vs_get(vst, base + 2))
       call vs_leave(vst, base)
       return
    end if

    if (gca_is(form)) then
       ! `{k ~v} -- flattened to k v k v, expanded as a seq, rebuilt as
       ! a map. syntaxQuote does the same through flattenMap. Missing
       ! this let a whole subtree through as literal data: every (ns ...)
       ! expands into a with-loading-context whose body is a MAP, and
       ! the gensym inside it was never renamed.
       out = qq_rebuild(flatten_map(form, vs_get(vst, base + 2)), "hash-map", &
            vs_get(vst, base + 2), .true.)
       call vs_leave(vst, base)
       return
    end if

    if (gc_kind(form) == OBJ_SET) then
       out = qq_rebuild(set_elems(form, vs_get(vst, base + 2)), "set", &
            vs_get(vst, base + 2))
       call vs_leave(vst, base)
       return
    end if

    if (gc_kind(form) == OBJ_META) then
       ! A HINTED form inside a template is still that form. (.getClass
       ! ^Object loading#) hides its gensym behind a wrapper, and
       ! treating the wrapper as an opaque leaf renamed the other
       ! occurrence of loading# and not this one -- which is worse than
       ! renaming neither.
       out = qq_expand(gc_slot(vs_get(vst, base + 1), 1), vs_get(vst, base + 2))
       call vs_leave(vst, base)
       return
    end if

    if (.not. gcl_is(form)) then
       if (form%tag == GCT_SYM) then
          call vs_set(vst, base + 1, auto_gensym(vs_get(vst, base + 1)))
          call vs_set(vst, base + 1, qq_alias(vs_get(vst, base + 1), vs_get(vst, base + 2)))
          sym = gc_sym("quote", [vs_get(vst, base + 1)])
          call vs_set(vst, base + 3, sym)
          out = gcl_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)])
          out = gcl_cons(vs_get(vst, base + 1), out, [vs_get(vst, base + 3), out])
          out = gcl_cons(vs_get(vst, base + 3), out, [vs_get(vst, base + 1), out])
       else
          out = form
       end if
       call vs_leave(vst, base)
       return
    end if

    ! (unquote x) -> x
    if (gcl_count(form) == 2) then
       head = gcl_first(form)
       if (head%tag == GCT_SYM) then
          if (gc_ref_is(head%ref, "unquote")) then
             out = nth_of(vs_get(vst, base + 1), 1)
             call vs_leave(vst, base)
             return
          end if
       end if
    end if

    n = gcl_count(vs_get(vst, base + 1))
    out = gcl_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 4, out)
    do i = n - 1, 0, -1
       elt = nth_of(vs_get(vst, base + 1), i)
       call vs_set(vst, base + 5, elt)
       spliced = .false.
       if (gcl_is(elt)) then
          if (gcl_count(elt) == 2) then
             head = gcl_first(elt)
             if (head%tag == GCT_SYM) spliced = gc_ref_is(head%ref, "splice-unquote")
          end if
       end if
       if (spliced) then
          sym = gc_sym("concat", [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 5)])
          call vs_set(vst, base + 3, sym)
          inner = nth_of(vs_get(vst, base + 5), 1)
       else
          sym = gc_sym("cons", [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 5)])
          call vs_set(vst, base + 3, sym)
          inner = qq_expand(vs_get(vst, base + 5), vs_get(vst, base + 2))
          if (tctx%has_error) then
             call vs_leave(vst, base); return
          end if
       end if
       call vs_set(vst, base + 6, inner)
       ! (sym inner <acc>), built back to front.
       out = gcl_empty([vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 6)])
       out = gcl_cons(vs_get(vst, base + 4), out, &
            [vs_get(vst, base + 3), vs_get(vst, base + 6), out])
       out = gcl_cons(vs_get(vst, base + 6), out, [vs_get(vst, base + 3), out])
       out = gcl_cons(vs_get(vst, base + 3), out, [out])
       call vs_set(vst, base + 4, out)
    end do
    out = vs_get(vst, base + 4)
    call vs_leave(vst, base)
  end function qq_expand

  ! x# inside a syntax-quote becomes one fresh name, the SAME fresh
  ! name everywhere it appears in that syntax-quote and a different one
  ! in the next. That is what makes a template able to bind a local
  ! without capturing the caller's -- (or x y) expands to a let over
  ! or__17__auto__, which no caller can have written.
  function auto_gensym(sym) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sym
    type(gc_value) :: out, gmap, hit
    character(len=:), allocatable :: t
    character(len=24) :: buf
    integer :: base

    vst => gc_my_stack()
    out = sym
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    if (len(t) < 2) return
    if (t(len(t):len(t)) /= "#") return
    if (index(t, "/") > 0) return
    if (.not. gc_root_live(gensym_root)) return

    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, sym)
    gmap = gc_root_get(gensym_root)
    call vs_set(vst, base + 2, gmap)
    hit = gca_get(vs_get(vst, base + 2), vs_get(vst, base + 1))
    if (hit%tag == GCT_SYM) then
       out = hit
       call vs_leave(vst, base)
       return
    end if
    gensym_id = gensym_id + 1
    write(buf, '(I0)') gensym_id
    out = gc_sym(t(1:len(t)-1) // "__" // trim(buf) // "__auto__", &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    gmap = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 1), vs_get(vst, base + 3), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call gc_global_keep(gensym_root, gmap)
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
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
    ! Compiler.resolveSymbol: a name with a dot in it is a class name
    ! and stays as written -- `clojure.core is clojure.core, not
    ! this-ns/clojure.core, which is what (use 'clojure.core) inside a
    ! syntax-quote was asking to load
    if (index(t, ".") > 0) return
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: m, roots
    type(gc_value) :: out
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call gca_entries(m, ks, vls)
    out = gcv_empty([roots])
    call vs_set(vst, base + 1, out)
    do i = 1, size(ks)
       out = gcv_conj(vs_get(vst, base + 1), ks(i), [roots])
       call vs_set(vst, base + 1, out)
       out = gcv_conj(vs_get(vst, base + 1), vls(i), [roots])
       call vs_set(vst, base + 1, out)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function flatten_map

  function set_elems(st, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: st, roots
    type(gc_value) :: out
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call gca_entries(gc_slot(st, 1), ks, vls)
    out = gcv_empty([roots])
    call vs_set(vst, base + 1, out)
    do i = 1, size(ks)
       out = gcv_conj(vs_get(vst, base + 1), ks(i), [roots])
       call vs_set(vst, base + 1, out)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, env
    character(len=*), intent(in) :: ctor
    logical, intent(in), optional :: use_apply
    type(gc_value) :: out, lst, inner
    logical :: ap
    integer :: base, i

    vst => gc_my_stack()
    tctx => ctx_self()
    ap = .false.
    if (present(use_apply)) ap = use_apply

    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, env)
    ! The elements as a list, so the existing list path expands them.
    lst = gcl_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, lst)
    do i = gcv_count(vs_get(vst, base + 1)) - 1, 0, -1
       lst = gcl_cons(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 3), &
            [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, lst)
    end do
    inner = qq_expand(vs_get(vst, base + 3), vs_get(vst, base + 2))
    if (tctx%has_error) then
       out = gc_nil()
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, inner)
    out = gcl_empty([vs_get(vst, base + 3)])
    out = gcl_cons(vs_get(vst, base + 3), out, [vs_get(vst, base + 3), out])
    out = gcl_cons(gc_sym(ctor, [vs_get(vst, base + 3), out]), out, [out])
    if (ap) out = gcl_cons(gc_sym("apply", [out]), out, [out])
    call vs_leave(vst, base)
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
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out
    tctx => ctx_self()
    tctx%ev_depth = 0
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: form0
    type(gc_value) :: out, form, head, mvar, item
    character(len=:), allocatable :: t
    integer :: base, i, n

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form0)
    out = vs_get(vst, base + 1)

    form = strip_meta(vs_get(vst, base + 1))
    if (gc_kind(form) == OBJ_LAZY .or. gc_kind(form) == OBJ_SEQ .or. gc_kind(form) == OBJ_CHUNKSEQ) &
         form = seq_to_list(form, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, form)
    if (.not. gcl_is(vs_get(vst, base + 2))) then
       call vs_leave(vst, base); return
    end if
    n = gcl_count(vs_get(vst, base + 2))
    if (n == 0) then
       call vs_leave(vst, base); return
    end if

    head = strip_meta(gcl_first(vs_get(vst, base + 2)))
    if (head%tag /= GCT_SYM) then
       call vs_leave(vst, base); return
    end if

    mvar = macro_var(head, gc_nil())
    if (gcn_is_var(mvar)) then
       out = expand_macro(gcn_var_value(mvar), vs_get(vst, base + 2), gc_nil(), mvar)
       call vs_leave(vst, base); return
    end if

    ! The two SUGARS macroexpand1 rewrites before it gives up. clotran
    ! evaluates both shapes directly, so this is not how they run -- it
    ! is so that macroexpand-1 REPORTS the rewrite, which is what a
    ! code walker like pprint's is looking at.
    t = gc_ref_text(head%ref)
    if (is_member_sym(head) .and. n >= 2) then
       ! (.foo target args...) -> (. target foo args...)
       out = gcl_empty([vs_get(vst, base + 2)])
       call vs_set(vst, base + 3, out)
       do i = n - 1, 2, -1
          item = nth_of(vs_get(vst, base + 2), i)
          out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
          call vs_set(vst, base + 3, out)
       end do
       item = gc_sym(t(2:), [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
       call vs_set(vst, base + 3, out)
       item = nth_of(vs_get(vst, base + 2), 1)
       out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
       call vs_set(vst, base + 3, out)
       item = gc_sym(".", [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
    else if (is_ctor_sym(head)) then
       ! (Classname. args...) -> (new Classname args...)
       out = gcl_empty([vs_get(vst, base + 2)])
       call vs_set(vst, base + 3, out)
       do i = n - 1, 1, -1
          item = nth_of(vs_get(vst, base + 2), i)
          out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
          call vs_set(vst, base + 3, out)
       end do
       item = gc_sym(t(:len(t) - 1), [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
       call vs_set(vst, base + 3, out)
       item = gc_sym("new", [vs_get(vst, base + 2), vs_get(vst, base + 3)])
       out = gcl_cons(item, vs_get(vst, base + 3), [vs_get(vst, base + 2), item])
    end if
    call vs_leave(vst, base)
  end function macroexpand_1step

  ! IPersistentCollection.empty -- what core.clj's `empty` is, in full:
  ! (when (instance? IPersistentCollection coll) (.empty coll)). The
  ! answer keeps the CATEGORY, so a vector empties to [] and a map to
  ! {}; anything that is not a collection answers nil, which is the
  ! `when`'s else branch rather than an error.
  function coll_empty(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, inner
    integer :: base

    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, strip_meta(v))
    select case (gc_kind(vs_get(vst, base + 1)))
    case (OBJ_VECTOR)
       out = gcv_empty([roots, vs_get(vst, base + 1)])
    case (OBJ_MAP)
       ! a sorted map's empty keeps its order and comparator
       if (gca_is_sorted(vs_get(vst, base + 1))) then
          out = gca_sorted_empty(gca_comparator(vs_get(vst, base + 1)), [roots, vs_get(vst, base + 1)])
       else
          out = gca_empty([roots, vs_get(vst, base + 1)])
       end if
    case (OBJ_SET)
       if (gca_is_sorted(gc_slot(vs_get(vst, base + 1), 1))) then
          inner = gca_sorted_empty(gca_comparator(gc_slot(vs_get(vst, base + 1), 1)), [roots, vs_get(vst, base + 1)])
       else
          inner = gca_empty([roots, vs_get(vst, base + 1)])
       end if
       call vs_set(vst, base + 2, inner)
       out = gc_obj(OBJ_SET, [vs_get(vst, base + 2)], [roots, vs_get(vst, base + 2)])
    case (OBJ_CONS, OBJ_SEQ, OBJ_LAZY, OBJ_CHUNKSEQ)
       ! Every seq empties to (), the way PersistentList.EMPTY is what
       ! ASeq.empty answers.
       out = gcl_empty([roots, vs_get(vst, base + 1)])
    end select
    if (gcl_is(vs_get(vst, base + 1))) out = gcl_empty([roots, vs_get(vst, base + 1)])
    ! (empty x) keeps x's metadata, as IPersistentCollection.empty does
    out = keep_meta(v, out, [roots, vs_get(vst, base + 1)])
    call vs_leave(vst, base)
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
    case (23)
       ! Math.ulp: infinity's is infinity, zero's the least denormal
       if (abs(x) > huge(x)) then
          out = gc_real(abs(x))
       else if (x == 0.0_gc_dp) then
          out = gc_real(scale(1.0_gc_dp, -1074))
       else
          out = gc_real(spacing(x))
       end if
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
       ! IEEE remainder: x - y*rint(x/y), which is what ieee_rem is;
       ! by zero it is NaN, as Java's
       if (y == 0.0_gc_dp) then
          out = gc_real(ieee_value(1.0_gc_dp, ieee_quiet_nan))
       else
          out = gc_real(x - y * math_rint(x / y))
       end if
    case (28); out = gc_real(atan2(x, y))
    case (29)
       ! Math.pow: 1 or -1 to an infinite power is NaN, where C says 1
       if (abs(x) == 1.0_gc_dp .and. abs(y) > huge(y)) then
          out = gc_real(ieee_value(1.0_gc_dp, ieee_quiet_nan))
       else
          out = gc_real(x ** y)
       end if
    case (30); out = gc_real(hypot(x, y))
    case (31); out = gc_real(sign(abs(x), y))
    case (32)
       if (x /= x .or. y /= y) then
          out = gc_real(ieee_value(1.0_gc_dp, ieee_quiet_nan))
       else if (x == y) then
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
       ! NaN and the infinities answer MAX_EXPONENT + 1, zero and the
       ! subnormals MIN_EXPONENT - 1, as Math.getExponent does
       if (x /= x .or. abs(x) > huge(x)) then
          out = gc_int(1024_gc_ip)
       else if (abs(x) < tiny(x)) then
          out = gc_int(-1023_gc_ip)
       else
          out = gc_int(int(exponent(x) - 1, 8))
       end if
    case (35); out = gc_real(scale(x, int(y)))
    case (37)
       ! by range, before the add (see mul_overflows)
       if ((ib > 0 .and. ia > huge(ia) - ib) .or. &
            (ib < 0 .and. ia < -huge(ia) - 1_gc_ip - ib)) then
          call raise_class("ArithmeticException", "long overflow", [gc_nil()])
       else
          out = gc_int(ia + ib)
       end if
    case (38)
       if ((ib < 0 .and. ia > huge(ia) + ib) .or. &
            (ib > 0 .and. ia < -huge(ia) - 1_gc_ip + ib)) then
          call raise_class("ArithmeticException", "long overflow", [gc_nil()])
       else
          out = gc_int(ia - ib)
       end if
    case (39)
       if (mul_overflows(ia, ib)) then
          call raise_class("ArithmeticException", "long overflow", [gc_nil()])
       else
          out = gc_int(ia * ib)
       end if
    case (40)
       if (ia == huge(ia)) then
          call raise_class("ArithmeticException", "long overflow", [gc_nil()])
       else
          out = gc_int(ia + 1_gc_ip)
       end if
    case (41)
       if (ia == -huge(ia) - 1_gc_ip) then
          call raise_class("ArithmeticException", "long overflow", [gc_nil()])
       else
          out = gc_int(ia - 1_gc_ip)
       end if
    case (42)
       if (ia == -huge(ia) - 1_gc_ip) then
          call raise_class("ArithmeticException", "long overflow", [gc_nil()])
       else
          out = gc_int(-ia)
       end if
    case (43)
       ! Floor division, not truncation: (floorDiv -7 2) is -4. In
       ! integers, so Long/MIN_VALUE by -1 wraps as Java's does rather
       ! than going through a double.
       if (ib == 0_gc_ip) then
          call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
       else if (ib == -1_gc_ip) then
          out = gc_int(-ia)
       else
          block
            integer(gc_ip) :: q
            q = ia / ib
            if (mod(ia, ib) /= 0_gc_ip .and. ((ia < 0_gc_ip) .neqv. (ib < 0_gc_ip))) q = q - 1_gc_ip
            out = gc_int(q)
          end block
       end if
    case (44)
       if (ib == 0_gc_ip) then
          call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
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
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: fmt
    type(gc_value), intent(in) :: argv
    character(len=:), allocatable :: s, flags, conv, piece
    integer :: i, w, prec, ai, nargs
    logical :: has_w, has_prec
    type(gc_value) :: a

    tctx => ctx_self()
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
       if (tctx%has_error) return
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: pat, subj
    integer, intent(in) :: limit
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, piece
    character(len=:), allocatable :: s
    integer :: mh, base, from, gs, ge, nparts, last
    logical :: ok

    vst => gc_my_stack()
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

    base = vs_enter(vst, 2)
    out = gcv_empty(roots)
    call vs_set(vst, base + 1, out)
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
       piece = gc_str(u8_slice(s, from, gs), [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, piece)
       out = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 2), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 1, out)
       nparts = nparts + 1
       from = ge
       if (ge == gs) from = ge
    end do
    call regex_release(mh)

    piece = gc_str(s(u8_off(s, from):), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, piece)
    out = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 2), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 1, out)

    if (limit == 0) then
       ! Drop trailing empties.
       last = gcv_count(vs_get(vst, base + 1))
       do while (last > 0)
          if (len(text_of(gcv_nth(vs_get(vst, base + 1), last - 1))) > 0) exit
          last = last - 1
       end do
       out = gcv_empty([roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, out)
       do nparts = 0, last - 1
          out = gcv_conj(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), nparts), &
               [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, out)
       end do
       out = vs_get(vst, base + 2)
    else
       out = vs_get(vst, base + 1)
    end if
    call vs_leave(vst, base)
  end function regex_split

  ! A `value` array holding the elements of a collection, which is what
  ! into-array is: (RT/seqToTypedArray (seq aseq)), optionally with a
  ! component type first. There are no primitive component types here
  ! -- every array of objects is a `value` array -- so the type is read
  ! and discarded, which is DEVIATIONS.md 24's territory rather than a
  ! new one.
  function value_array(items, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: items
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, vec, run
    character(len=:), allocatable :: err
    integer :: base, h, k, cnt

    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 3)
    vec = coll_to_vector(items, roots)
    call vs_set(vst, base + 1, vec)
    cnt = gcv_count(vs_get(vst, base + 1))
    h = gcna_new("value", [cnt], [0], err)
    if (h == 0) then
       call fail(err)
       call vs_leave(vst, base)
       return
    end if
    run = gc_vec(max(1, cnt), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, run)
    out = gc_obj(OBJ_ARRAY, [vs_get(vst, base + 2)], [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    call gc_set_i1(vs_get(vst, base + 3), h)
    call gc_set_i2(vs_get(vst, base + 3), -1) ! owns the handle
    do k = 0, cnt - 1
       call gc_vec_set(gc_slot(vs_get(vst, base + 3), 1), k + 1, &
            gcv_nth(vs_get(vst, base + 1), k))
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
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
          if (regex_group_span(mh, gnum, gs, ge)) s = s // u8_slice(subj, gs, ge)
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
       acc = acc // u8_slice(subj, from, gs) // expand_replacement(repl, mh, subj)
       from = ge
       if (only_first) exit
       ! A zero-width match cannot advance on its own.
       if (ge == gs) then
          if (ge >= u8_count(subj)) exit
          acc = acc // u8_slice(subj, ge, ge + 1)
          from = ge + 1
       end if
    end do
    out = gc_str(acc // subj(u8_off(subj, from):), roots)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: a0, b0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, a0)
    call vs_set(vst, base + 2, b0)
    out = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    out = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 1), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, out)
    out = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 2), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, k
    integer :: base, i
    character(len=24), parameter :: names(24) = [character(len=24) :: &
         "def", "loop*", "recur", "if", "case*", "let*", "letfn*", "do", &
         "fn*", "quote", "var", "clojure.core/import*", ".", "set!", &
         "deftype*", "reify*", "try", "throw", "monitor-enter", &
         "monitor-exit", "catch", "finally", "new", "&"]

    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    out = gca_empty([roots])
    call vs_set(vst, base + 1, out)
    do i = 1, size(names)
       k = gc_sym(trim(names(i)), [roots, vs_get(vst, base + 1)])
       out = gca_assoc(vs_get(vst, base + 1), k, gc_nil(), [roots, vs_get(vst, base + 1), k])
       call vs_set(vst, base + 1, out)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: s0
    type(gc_value), intent(out) :: chunk, more
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: s, src, cell, nxt, spec, buf
    integer :: base, at, total, fin, cnt
    real(gc_dp) :: sd

    vst => gc_my_stack()
    chunk = gc_nil()
    more = gc_nil()
    s = strip_meta(s0)
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, s)
    select case (gc_kind(s))
    case (OBJ_CHUNKSEQ)
       chunk = gc_slot(s, 1)
       more = gc_slot(s, 2)
    case (OBJ_SEQ)
       src = gc_slot(s, 1)
       at = gc_i1(s)
       total = gcv_count(src)
       fin = min(total, at + 32)
       chunk = make_chunk(src, at, fin, [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, chunk)
       if (fin < total) then
          more = gc_obj(OBJ_SEQ, [src], [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call gc_set_i1(more, fin)
       end if
       chunk = vs_get(vst, base + 2)
    case (OBJ_LAZY)
       ! up to 32 values into one run: realised cells first, then the
       ! pending tail's arithmetic, then whatever is left is `more`
       buf = gc_vec(32, [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, buf)
       cnt = 0
       call vs_set(vst, base + 3, vs_get(vst, base + 1))      ! the cell being read
       do
          cell = vs_get(vst, base + 3)
          if (gc_kind(cell) /= OBJ_LAZY) exit
          if (gc_i1(cell) == LAZY_CONS) then
             if (cnt >= 32) exit
             call gc_vec_set(vs_get(vst, base + 2), cnt + 1, gc_slot(cell, 2))
             cnt = cnt + 1
             call vs_set(vst, base + 3, gc_slot(cell, 3))
             cycle
          end if
          if (gc_i1(cell) == LAZY_PENDING .and. gc_i2(cell) == 1) then
             spec = gc_slot(cell, 1)
             call vs_set(vst, base + 4, gcv_nth(spec, 0))   ! cursor
             call vs_set(vst, base + 5, gcv_nth(spec, 1))   ! hi
             call vs_set(vst, base + 6, gcv_nth(spec, 2))   ! step
             sd = num_dbl(vs_get(vst, base + 6))
             do while (cnt < 32)
                if (sd > 0.0_gc_dp .and. .not. num_lt(vs_get(vst, base + 4), vs_get(vst, base + 5))) exit
                if (sd < 0.0_gc_dp .and. .not. num_lt(vs_get(vst, base + 5), vs_get(vst, base + 4))) exit
                call gc_vec_set(vs_get(vst, base + 2), cnt + 1, vs_get(vst, base + 4))
                cnt = cnt + 1
                call vs_set(vst, base + 4, num_add2(vs_get(vst, base + 4), vs_get(vst, base + 6), [vs_get(vst, base + 2)]))
             end do
             ! what is left of the range, as a fresh pending tail
             if ((sd > 0.0_gc_dp .and. num_lt(vs_get(vst, base + 4), vs_get(vst, base + 5))) .or. &
                  (sd < 0.0_gc_dp .and. num_lt(vs_get(vst, base + 5), vs_get(vst, base + 4))) .or. sd == 0.0_gc_dp) then
                spec = gcv_build(3, [vs_get(vst, base + 2)])
                call vs_set(vst, base + 3, spec)
                call gc_vec_set(gc_slot(spec, 1), 1, vs_get(vst, base + 4))
                call gc_vec_set(gc_slot(spec, 1), 2, vs_get(vst, base + 5))
                call gc_vec_set(gc_slot(spec, 1), 3, vs_get(vst, base + 6))
                nxt = gc_obj(OBJ_LAZY, [vs_get(vst, base + 3), gc_nil(), gc_nil()], [vs_get(vst, base + 2), vs_get(vst, base + 3)])
                call gc_set_i1(nxt, LAZY_PENDING)
                call gc_set_i2(nxt, 1)
                call vs_set(vst, base + 3, nxt)
             else
                call vs_set(vst, base + 3, gc_nil())
             end if
          end if
          exit
       end do
       chunk = make_chunk(vs_get(vst, base + 2), 0, cnt, [vs_get(vst, base + 3)])
       more = vs_get(vst, base + 3)
       if (gc_kind(more) == OBJ_LAZY) then
          if (gc_i1(more) == LAZY_EMPTY) more = gc_nil()
       end if
    end select
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: coll, f, init
    logical, intent(in) :: has_init
    type(gc_value) :: out, x, cell, spec
    integer :: base, i
    logical :: have, done
    real(gc_dp) :: sd
    ! slots: 1 coll/cell 2 f 3 acc 4 cursor (a range's next value) 5 hi 6 step
    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, coll)
    call vs_set(vst, base + 2, f)
    have = has_init
    if (has_init) call vs_set(vst, base + 3, init)
    done = .false.
    select case (gc_kind(coll))
    case (OBJ_VECTOR)
       do i = 0, gcv_count(vs_get(vst, base + 1)) - 1
          call step(gcv_nth(vs_get(vst, base + 1), i))
          if (done) exit
       end do
    case (OBJ_CONS)
       do while (gcl_count(vs_get(vst, base + 1)) > 0)
          call step(gcl_first(vs_get(vst, base + 1)))
          if (done) exit
          call vs_set(vst, base + 1, gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 3)]))
       end do
    case (OBJ_LAZY)
       do
          cell = vs_get(vst, base + 1)
          if (gc_i1(cell) == LAZY_PENDING .and. gc_i2(cell) == 1) then
             ! the rest of a range: walk the arithmetic, no cells
             spec = gc_slot(cell, 1)
             call vs_set(vst, base + 4, gcv_nth(spec, 0))
             call vs_set(vst, base + 5, gcv_nth(spec, 1))
             call vs_set(vst, base + 6, gcv_nth(spec, 2))
             sd = num_dbl(vs_get(vst, base + 6))
             do
                if (sd > 0.0_gc_dp .and. .not. num_lt(vs_get(vst, base + 4), vs_get(vst, base + 5))) exit
                if (sd < 0.0_gc_dp .and. .not. num_lt(vs_get(vst, base + 5), vs_get(vst, base + 4))) exit
                if (sd == 0.0_gc_dp .and. .not. num_lt(vs_get(vst, base + 4), vs_get(vst, base + 5))) exit
                call step(vs_get(vst, base + 4))
                if (done) exit
                call vs_set(vst, base + 4, num_add2(vs_get(vst, base + 4), vs_get(vst, base + 6), [vs_get(vst, base + 3)]))
             end do
             exit
          end if
          call gce_force(cell)
          if (tctx%has_error) exit
          cell = vs_get(vst, base + 1)
          if (gc_i1(cell) /= LAZY_CONS) exit
          call step(gc_slot(cell, 2))
          if (done) exit
          call vs_set(vst, base + 1, gc_slot(vs_get(vst, base + 1), 3))
       end do
    case (OBJ_CHUNK)
       do i = 0, chunk_count(vs_get(vst, base + 1)) - 1
          call step(chunk_nth(vs_get(vst, base + 1), i))
          if (done) exit
       end do
    case default
       ! a ChunkedCons, or anything else seqable: walked as a seq
       call vs_set(vst, base + 1, to_seq(vs_get(vst, base + 1), [vs_get(vst, base + 2)]))
       do
          cell = vs_get(vst, base + 1)
          if (cell%tag == GCT_NIL) exit
          call step(sq_first(vs_get(vst, base + 1), [vs_get(vst, base + 2)]))
          if (done) exit
          call vs_set(vst, base + 1, to_seq(sq_rest(vs_get(vst, base + 1), [vs_get(vst, base + 2)]), [vs_get(vst, base + 2)]))
       end do
    end select
    if (.not. tctx%has_error .and. .not. done) then
       if (have) then
          out = vs_get(vst, base + 3)
       else
          out = apply(vs_get(vst, base + 2), gcv_empty([vs_get(vst, base + 2)]))
       end if
    else if (done) then
       out = vs_get(vst, base + 3)
    else
       out = gc_nil()
    end if
    call vs_leave(vst, base)
  contains
    ! One element: the first is the accumulator when there was no init;
    ! otherwise (f acc x), and a reduced result unwraps and stops.
    subroutine step(x0)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
      type(gc_value), intent(in) :: x0
      type(gc_value) :: argv, r
    vst => gc_my_stack()
    tctx => ctx_self()
      if (.not. have) then
         call vs_set(vst, base + 3, x0)
         have = .true.
         return
      end if
      x = x0
      argv = gcv_build(2, [vs_get(vst, base + 3), x])
      call gc_vec_set(gc_slot(argv, 1), 1, vs_get(vst, base + 3))
      call gc_vec_set(gc_slot(argv, 1), 2, x)
      r = apply(vs_get(vst, base + 2), argv)
      if (tctx%has_error) then
         done = .true.
         return
      end if
      call vs_set(vst, base + 3, r)
      if (is_reduced(r)) then
         call vs_set(vst, base + 3, gca_get(strip_meta(vs_get(vst, base + 3)), gc_key("clotran/reduced", [vs_get(vst, base + 3)])))
         done = .true.
      end if
    end subroutine step
  end function reduce_native

  recursive function range_cell(lo, hi, stp, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: lo, hi, stp
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, spec, tail, nxt
    integer :: base
    real(gc_dp) :: sd

    vst => gc_my_stack()
    out = gcl_empty(roots)
    sd = num_dbl(stp)
    if (sd > 0.0_gc_dp .and. .not. num_lt(lo, hi)) return
    if (sd < 0.0_gc_dp .and. .not. num_lt(hi, lo)) return

    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, lo)
    call vs_set(vst, base + 2, hi)
    call vs_set(vst, base + 3, stp)
    nxt = num_add2(vs_get(vst, base + 1), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, nxt)
    spec = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    spec = gcv_conj(spec, vs_get(vst, base + 4), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 3), [roots, vs_get(vst, base + 1), spec])
    call vs_set(vst, base + 4, spec)
    tail = gc_obj(OBJ_LAZY, [vs_get(vst, base + 4), gc_nil(), gc_nil()], [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call gc_set_i1(tail, LAZY_PENDING)
    call gc_set_i2(tail, 1)
    call vs_set(vst, base + 4, tail)
    out = gc_obj(OBJ_LAZY, [gc_nil(), vs_get(vst, base + 1), vs_get(vst, base + 4)], [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call gc_set_i1(out, LAZY_CONS)
    ! i2 = 1 on the realised cell as well: it says "this is a range", which
    ! is what makes it a LongRange to `class` and an IReduceInit to reduce.
    call gc_set_i2(out, 1)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: f, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, spec, tail
    integer :: base

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, f)
    call vs_set(vst, base + 2, x)
    spec = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    spec = gcv_conj(spec, vs_get(vst, base + 1), [roots, vs_get(vst, base + 2), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), spec])
    call vs_set(vst, base + 3, spec)
    tail = gc_obj(OBJ_LAZY, [vs_get(vst, base + 3), gc_nil(), gc_nil()], [roots, vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call gc_set_i1(tail, LAZY_PENDING)
    call gc_set_i2(tail, 2)
    call vs_set(vst, base + 3, tail)
    out = gc_obj(OBJ_LAZY, [gc_nil(), vs_get(vst, base + 2), vs_get(vst, base + 3)], [roots, vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call gc_set_i1(out, LAZY_CONS)
    call vs_leave(vst, base)
  end function iterate_cell

  ! The global environment gce_base_env built and rooted, or nil.
  ! ClotranABI needs it to analyse and evaluate on an embedder's
  ! behalf; B_EVAL reaches the same root from inside.
  function gce_env() result(env)
    type(gc_value) :: env
    env = gc_nil()
    if (gc_root_live(global_env_root)) env = gc_root_get(global_env_root)
  end function gce_env

  ! A call whose arguments are already in CONSECUTIVE shadow stack
  ! slots. A compiled call site has them there anyway, so calling
  ! another compiled function costs no vector at all; every other
  ! callee gets one built here, which is what the interpreter would
  ! have done.
  ! Every call into a compiled procedure comes through here. It is a
  ! FRAME, as a closure's call is: a stack trace names it (ns/name) and
  ! a runaway recursion is the same "stack overflow" error rather than
  ! a crash of the Fortran stack. And it is a NESTED RUN, as a callback
  ! from a builtin is: a task that blocks below compiled code cannot
  ! yield -- there is Fortran on the stack between it and its context --
  ! so it is pinned (tasks.inc) and the other tasks run right there.
  ! Counted as nothing, a block down there yielded anyway: the builtin
  ! answered nil into compiled code that carried on with it.
  recursive subroutine call_compiled(fn, argbase, nargs, dst)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: argbase, nargs, dst
    tctx => ctx_self()
    if (ev_limit == 0) call read_depth_limit()
    call push_frame(fn, tctx%pending_site)
    tctx%pending_site = 0
    if (tctx%has_error) return
    tctx%ev_depth = tctx%ev_depth + 1
    if (tctx%ev_depth > ev_limit) then
       call fail("stack overflow")
    else
       call cf_call(gc_i1(fn), argbase, nargs, dst)
    end if
    tctx%ev_depth = tctx%ev_depth - 1
    call pop_frame()
  end subroutine call_compiled

  recursive function gce_apply_slots(fn0, argbase, nargs) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: fn0
    integer, intent(in) :: argbase, nargs
    type(gc_value) :: out, fn, av
    integer :: base, j
    vst => gc_my_stack()
    out = gc_nil()
    fn = strip_meta(fn0)
    if (gcn_is_var(fn)) fn = gcn_var_value(fn)
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, fn)
    if (gc_kind(vs_get(vst, base + 1)) == OBJ_COMPILED .and. &
         (gc_i2(vs_get(vst, base + 1)) < 0 .or. gc_i2(vs_get(vst, base + 1)) == nargs)) then
       block
         integer :: rb
         rb = vs_enter(vst, 1)
         call call_compiled(vs_get(vst, base + 1), argbase, nargs, rb + 1)
         out = vs_get(vst, rb + 1)
         call vs_leave(vst, rb)
       end block
       call vs_leave(vst, base)
       return
    end if
    ! A NUMERIC BUILTIN reuses the interpreter's scratch vector and
    ! allocates nothing, by the same rule exec.inc's N_CALL uses
    ! (scalar_builtin: numeric, keeps no argument, never calls back).
    ! Without this a compiled loop built a fresh vector for every +
    ! and <, and a profile had the collector at 58% of its time --
    ! the interpreter, which already took this path, allocated none.
    if (gc_kind(vs_get(vst, base + 1)) == OBJ_BUILTIN .and. (nargs == 1 .or. nargs == 2)) then
       if (scalar_builtin(gc_i1(vs_get(vst, base + 1)))) then
          av = scratch_args(nargs)
          do j = 1, nargs
             call gc_vec_set(gc_slot(av, 1), j, vs_get(vst, argbase + j))
          end do
          out = call_builtin(gc_i1(vs_get(vst, base + 1)), av)
          call vs_leave(vst, base)
          return
       end if
    end if
    ! ONE allocation, not one per argument: gcv_conj would build a
    ! new vector each time round, which for a two-argument call in a
    ! loop is twice the garbage the interpreter makes.
    if (nargs > 0 .and. nargs <= 32) then
       av = gcv_build(nargs, [vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, av)
       do j = 1, nargs
          av = gcv_put(vs_get(vst, base + 2), j - 1, vs_get(vst, argbase + j), &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, av)
       end do
    else
       av = gcv_empty([vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, av)
       do j = 1, nargs
          av = gcv_conj(vs_get(vst, base + 2), vs_get(vst, argbase + j), &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, av)
       end do
    end if
    out = apply(vs_get(vst, base + 1), vs_get(vst, base + 2))
    call vs_leave(vst, base)
  end function gce_apply_slots

  ! `exec` under a public name: an already-analysed node run in a
  ! frame. This is the compiler's escape hatch -- generated code calls
  ! it for every node kind the generator has not learned, so an
  ! unhandled construct is slow rather than broken.
  recursive function gce_exec_node(node, frame) result(out)
    type(gc_value), intent(in) :: node, frame
    type(gc_value) :: out
    out = exec(node, frame)
  end function gce_exec_node

  ! `apply` under a public name, for ClotranABI. The ABI is the
  ! surface compiled code and an embedder call through, and it must
  ! not reach into the module's internals; this is the one call it
  ! needs that GC and Namespace do not already export.
  recursive function gce_apply(fn, args) result(out)
    type(gc_value), intent(in) :: fn, args
    type(gc_value) :: out
    out = apply(fn, args)
  end function gce_apply

  recursive function apply(fn0, args) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: fn0, args
    type(gc_value) :: out, child, body, params, fn
    integer :: base, i, n

    ! A function can arrive wrapped: core.clj's fn macro returns
    ! (with-meta (cons (quote fn*) decl) (meta &form)), so the value a
    ! caller holds is an OBJ_META around the closure. Metadata never
    ! changes what a value IS.
    vst => gc_my_stack()
    tctx => ctx_self()
    fn = strip_meta(fn0)
    ! A VAR IS CALLABLE. (#'f x) derefs and applies -- core.clj calls
    ! its own private helpers that way, (#'assert-same-protocol ...), so
    ! that a redefinition is picked up.
    if (gcn_is_var(fn)) fn = gcn_var_value(fn)
    out = gc_nil()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, fn)
    call vs_set(vst, base + 2, args)

    select case (gc_kind(fn))
    case (OBJ_BUILTIN)
       if (gc_i1(fn) == B_RTFN) then
          ! a host member written in Clojure: its var in clotran.rt
          block
            type(gc_value) :: nm
            nm = gc_slot(fn, 1)
            out = rt_call(gc_ref_text(nm%ref), args)
          end block
       else
          out = call_builtin(gc_i1(fn), args)
       end if
    case (OBJ_CLOSURE)
       ! handed over, not kept (see exec's N_CALL): the callee roots
       ! args itself, immediately, and nothing allocates in between
       block
         type(gc_value) :: argl
         argl = vs_get(vst, base + 2)
         call vs_set(vst, base + 2, gc_nil())
         out = invoke_closure(vs_get(vst, base + 1), argl)
       end block
    case (OBJ_COMPILED)
       ! A compiled procedure. The arguments go into CONSECUTIVE
       ! slots and the answer comes back in one more, so a call costs
       ! no vector -- which is most of the point of compiling. The
       ! args arrive here as a vector because `apply` is the general
       ! path; a compiled CALL SITE will write the slots directly and
       ! never build one.
       block
         type(gc_value) :: av, nmv
         integer :: cb, cn, j
         av = vs_get(vst, base + 2)
         cn = gcv_count(av)
         nmv = gc_slot(vs_get(vst, base + 1), 1)
         if (gc_i2(vs_get(vst, base + 1)) >= 0 .and. gc_i2(vs_get(vst, base + 1)) /= cn) then
            call raise_class("ArityException", &
                 "Wrong number of args (" // itoa(cn) // ") passed to: " // &
                 gc_ref_text(nmv%ref), [vs_get(vst, base + 1)])
         else
            ! slots cb+1 .. cb+cn are the arguments and cb+cn+1 is
            ! where the answer lands, which is the convention every
            ! generated procedure is written to.
            cb = vs_enter(vst, cn + 1)
            do j = 1, cn
               call vs_set(vst, cb + j, gcv_nth(av, j - 1))
            end do
            call call_compiled(vs_get(vst, base + 1), cb, cn, cb + cn + 1)
            out = vs_get(vst, cb + cn + 1)
            call vs_leave(vst, cb)
         end if
       end block
    case (OBJ_INST)
       ! A deftype or reify that implements IFn is callable: (promise x)
       ! is its invoke method, with the instance as `this` in front.
       block
         type(gc_value) :: m
         m = gca_get(gc_slot(gc_slot(fn, 1), 3), gc_key("invoke", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
         if (gc_kind(m) == OBJ_CLOSURE) then
            call vs_set(vst, base + 3, m)
            call vs_set(vst, base + 2, cons_vec(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 3)]))
            out = apply(vs_get(vst, base + 3), vs_get(vst, base + 2))
         else
            call fail("not a function: " // gcp_str(fn, .true.))
         end if
       end block
    case (OBJ_MULTIFN)
       ! getFn(dispatchFn.invoke(args)).invoke(args) -- MultiFn.invoke,
       ! exactly. The dispatch function sees the same arguments the
       ! method will.
       block
         type(gc_value) :: dv, meth
         dv = apply(gc_slot(fn, 2), args)
         if (tctx%has_error) then
            call vs_leave(vst, base)
            return
         end if
         call vs_set(vst, base + 3, dv)
         meth = mf_lookup(vs_get(vst, base + 1), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
         if (tctx%has_error) then
            call vs_leave(vst, base)
            return
         end if
         if (meth%tag == GCT_NIL) then
            call raise_class("IllegalArgumentException", "No method in multimethod '" // &
                 gcp_str(gc_slot(vs_get(vst, base + 1), 1), .false.) // &
                 "' for dispatch value: " // gcp_str(vs_get(vst, base + 3), .true.), [vs_get(vst, base + 1)])
         else
            out = apply(meth, args)
         end if
       end block
    case default
       ! A keyword and a map are both callable in Clojure, and neither
       ! is a closure: (:k m) looks itself up IN m, and (m :k) looks up
       ! its argument. Same lookup from opposite sides, which is why
       ! both live here rather than as builtins.
       if (fn%tag == GCT_KEY .and. (gcv_count(args) == 0 .or. gcv_count(args) > 2)) then
          ! Keyword.invoke has one and two: ArityException otherwise,
          ! with the JVM's own count and its "(> 20)" past twenty
          block
            character(len=16) :: cbuf
            if (gcv_count(args) > 20) then
               cbuf = "> 20"
            else
               write(cbuf, '(I0)') gcv_count(args)
            end if
            call raise_class("ArityException", "Wrong number of args (" // trim(cbuf) // &
                 ") passed to: " // gcp_str(fn, .true.), [vs_get(vst, base + 1)])
          end block
       else if (fn%tag == GCT_SYM) then
          ! A SYMBOL IS CALLABLE too, the same lookup as a keyword's
          if (gcv_count(args) >= 1) then
             block
               type(gc_value) :: tgt
               tgt = strip_meta(gcv_nth(args, 0))
               if (gca_is(tgt)) then
                  out = gca_get(tgt, fn)
                  if (gcv_count(args) >= 2 .and. out%tag == GCT_NIL) then
                     if (.not. gca_contains(tgt, fn)) out = gcv_nth(args, 1)
                  end if
               else if (gc_kind(tgt) == OBJ_SET) then
                  out = gca_get(gc_slot(tgt, 1), fn)
               else if (gcv_count(args) >= 2) then
                  out = gcv_nth(args, 1)
               end if
             end block
          end if
       else if (fn%tag == GCT_KEY) then
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
                     call vs_leave(vst, base)
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
             ! (:k coll not-found): on a set or a transient as on a map
             if (gcv_count(args) >= 2 .and. out%tag == GCT_NIL) then
                if (.not. coll_has(strip_meta(gcv_nth(args, 0)), fn)) out = gcv_nth(args, 1)
             end if
          end if
       else if (gca_is(fn)) then
          ! (m k) and (m k not-found)
          if (gcv_count(args) >= 1) out = gca_get(fn, gcv_nth(args, 0))
          if (gcv_count(args) >= 2 .and. out%tag == GCT_NIL) then
             if (.not. gca_contains(fn, gcv_nth(args, 0))) out = gcv_nth(args, 1)
          end if
       else if (gc_kind(fn) == OBJ_SET) then
          ! A SET IS CALLABLE, on membership: (#{1 2} 1) is 1 and
          ! (#{1 2} 9) is nil. core.clj leans on it -- destructure asks
          ! (some #{'&} b) whether a binding form has a rest arg -- and
          ! without it that call returned no value at all.
          if (gcv_count(args) >= 1) out = gca_get(gc_slot(fn, 1), gcv_nth(args, 0))
          if (gcv_count(args) >= 2 .and. out%tag == GCT_NIL) then
             if (.not. gca_contains(gc_slot(fn, 1), gcv_nth(args, 0))) out = gcv_nth(args, 1)
          end if
       else if (gcv_is(fn)) then
          ! A vector is callable on an index, as in ([:a :b] 1).
          if (gcv_count(args) >= 1) then
             block
               type(gc_value) :: ix
               ix = gcv_nth(args, 0)
               ! A vector index, narrow by nature; out of range throws
               ! as PersistentVector.nth does.
               if (ix%tag /= GCT_INT) then
                  call raise_class("IllegalArgumentException", "Key must be integer", [vs_get(vst, base + 1)])
               else if (ix%ival < 0 .or. ix%ival >= int(gcv_count(fn), gc_ip)) then
                  call raise_class("IndexOutOfBoundsException", "index out of bounds", [vs_get(vst, base + 1)])
               else
                  out = gcv_nth(fn, int(ix%ival, kind=4))
               end if
             end block
          end if
       else
          call fail("not a function: " // gcp_str(fn, .true.))
       end if
    end select

    call vs_leave(vst, base)
  end function apply

  function call_builtin(id, args) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    integer, intent(in) :: id
    type(gc_value), intent(in) :: args
    type(gc_value) :: out, a, b
    integer :: base, i, n
    ! 64-bit, or every sum would truncate on the way out of %ival.
    integer(gc_ip) :: acc
    logical :: hit, checked, promote
    integer :: op

    vst => gc_my_stack()
    tctx => ctx_self()
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
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, args)

    select case (id)
    case (B_ADD, B_SUB, B_MUL, B_UADD, B_USUB, B_UMUL, B_PADD, B_PSUB, B_PMUL)
       ! Long arithmetic THROWS on overflow, as Numbers.add and friends
       ! do; the unchecked- variants wrap, as theirs do.
       checked = (id == B_ADD .or. id == B_SUB .or. id == B_MUL)
       ! +' -' *' promote instead: the whole expression is computed in
       ! arbitrary precision and narrowed back to a long at the end if
       ! it fits and no operand was a BigInt to begin with, which is
       ! what makes (+' 1 1) a Long and (+' Long/MAX_VALUE 1) a BigInt.
       promote = (id == B_PADD .or. id == B_PSUB .or. id == B_PMUL)
       op = id
       if (id == B_UADD .or. id == B_PADD) op = B_ADD
       if (id == B_USUB .or. id == B_PSUB) op = B_SUB
       if (id == B_UMUL .or. id == B_PMUL) op = B_MUL
       if (.not. numbers_ok(args, n, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
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
          if (op == B_MUL) then
             out = gc_int(1)
          else
             out = gc_int(0)
          end if
       else
          block
            logical :: any_real, any_ratio, any_big, any_dec, dok
            character(len=:), allocatable :: dacc, dopn
            integer :: mcp, mcm
            real(gc_dp) :: racc
            integer(gc_ip) :: qn, qd, bn, bd, g
            character(len=:), allocatable :: bacc
            any_real = .false.
            any_ratio = .false.
            any_big = .false.
            any_dec = .false.
            do i = 0, n - 1
               b = strip_meta(gcv_nth(args, i))
               if (b%tag == GCT_REAL) any_real = .true.
               if (b%tag == GCT_RATIO) any_ratio = .true.
               if (b%tag == GCT_BIG) any_big = .true.
               if (b%tag == GCT_DEC) any_dec = .true.
            end do
            a = gcv_nth(args, 0)
            if (any_dec .and. .not. any_real) then
               ! CONTAGION, one step above a ratio and below a double:
               ! (+ 1M 1/2) is 1.5M and (+ 1M 1.0) is 2.0. Every scale
               ! rule is BigDecimal's (BigDec.f90): add and subtract
               ! take the larger scale, multiply adds them.
               dacc = dec_operand(strip_meta(a), dok)
               if (dok .and. n == 1 .and. op == B_SUB) dacc = dec_neg(dacc)
               do i = 1, n - 1
                  if (.not. dok) exit
                  dopn = dec_operand(strip_meta(gcv_nth(args, i)), dok)
                  if (.not. dok) exit
                  select case (op)
                  case (B_ADD); dacc = dec_add(dacc, dopn)
                  case (B_SUB); dacc = dec_sub(dacc, dopn)
                  case (B_MUL); dacc = dec_mul(dacc, dopn)
                  end select
               end do
               ! Under with-precision every operation rounds, as
               ! Numbers.add(x, y, mc) does; with none it is exact.
               if (dok) then
                  call math_context(mcp, mcm)
                  if (mcp > 0) then
                     dopn = dacc
                     call dec_round(dopn, mcp, mcm, dacc, dok)
                  end if
               end if
               if (dok) then
                  out = gc_dec(dacc, [vs_get(vst, base + 1)])
               else
                  call raise_class("ArithmeticException", &
                       "Rounding necessary", [vs_get(vst, base + 1)])
                  call vs_leave(vst, base)
                  return
               end if
            else if (any_ratio .and. .not. any_real) then
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
               ! A BigInt here is exact only while it fits in 64
               ! bits: a Ratio's parts are integers (DEVIATIONS 26).
               b = rat_operand(strip_meta(a), hit)
               if (.not. hit) then
                  call raise_class("ArithmeticException", &
                       "a Ratio of BigInts is not supported (DEVIATIONS 26)", [vs_get(vst, base + 1)])
                  call vs_leave(vst, base)
                  return
               end if
               qn = gc_numerator(b)
               qd = gc_denominator(b)
               if (n == 1 .and. op == B_SUB) qn = -qn
               do i = 1, n - 1
                  b = rat_operand(strip_meta(gcv_nth(args, i)), hit)
                  if (.not. hit) then
                     call raise_class("ArithmeticException", &
                          "a Ratio of BigInts is not supported (DEVIATIONS 26)", [vs_get(vst, base + 1)])
                     call vs_leave(vst, base)
                     return
                  end if
                  bn = gc_numerator(b)
                  bd = gc_denominator(b)
                  select case (op)
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
               ! (* 2N 1/2) is 1N, not 1: a BigInt anywhere keeps the
               ! answer a BigInt when it comes out integral.
               if (any_big .and. out%tag == GCT_INT) out = gc_big(big_from_i64(out%ival), [vs_get(vst, base + 1)])
            else if (any_real) then
               racc = num_dbl(a)
               if (n == 1 .and. op == B_SUB) racc = -racc
               do i = 1, n - 1
                  b = gcv_nth(args, i)
                  select case (op)
                  case (B_ADD); racc = racc + num_dbl(b)
                  case (B_SUB); racc = racc - num_dbl(b)
                  case (B_MUL); racc = racc * num_dbl(b)
                  end select
               end do
               out = gc_real(racc)
            else if (any_big .or. promote) then
               ! Exact, in decimal text (BigInt.f90). A BigInt anywhere
               ! makes the answer a BigInt -- (+ 1N 1) is 2N -- and a
               ! promoting operator narrows back to a long below.
               bacc = big_of(strip_meta(a))
               if (n == 1 .and. op == B_SUB) bacc = big_neg(bacc)
               do i = 1, n - 1
                  b = strip_meta(gcv_nth(args, i))
                  select case (op)
                  case (B_ADD); bacc = big_add(bacc, big_of(b))
                  case (B_SUB); bacc = big_sub(bacc, big_of(b))
                  case (B_MUL); bacc = big_mul(bacc, big_of(b))
                  end select
               end do
               if (.not. any_big .and. big_fits_i64(bacc)) then
                  out = gc_int(big_to_i64(bacc))
               else
                  out = gc_big(bacc, [vs_get(vst, base + 1)])
               end if
            else
               acc = a%ival
               if (n == 1 .and. op == B_SUB) then
                  if (checked .and. acc == -huge(acc) - 1_gc_ip) then
                     call raise_class("ArithmeticException", "long overflow", [vs_get(vst, base + 1)])
                     call vs_leave(vst, base)
                     return
                  end if
                  acc = -acc
               end if
               do i = 1, n - 1
                  b = strip_meta(gcv_nth(args, i))
                  if (checked) then
                     select case (op)
                     case (B_ADD); hit = add_overflows(acc, b%ival)
                     case (B_SUB); hit = add_overflows(acc, -b%ival) .or. b%ival == -huge(acc) - 1_gc_ip
                     case (B_MUL); hit = mul_overflows(acc, b%ival)
                     end select
                     if (hit) then
                        call raise_class("ArithmeticException", "long overflow", [vs_get(vst, base + 1)])
                        call vs_leave(vst, base)
                        return
                     end if
                  end if
                  select case (op)
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
          case (GCT_STR, GCT_SYM, GCT_KEY, GCT_CLASS, GCT_BIG)
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
               [vs_get(vst, base + 1)])) then
             out = gc_bool(.false.)
             exit
          end if
       end do
    case (B_LT)
       if (.not. numbers_ok(args, n, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
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
       out = gcl_empty([vs_get(vst, base + 1)])
       do i = n - 1, 0, -1
          out = gcl_cons(gcv_nth(vs_get(vst, base + 1), i), out, [vs_get(vst, base + 1)])
       end do
    case (B_VECTOR)
       out = vs_get(vst, base + 1)
    case (B_COUNT)
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke0(a, "count", hit)
          if (hit) then
             call vs_leave(vst, base)
             return
          end if
       end if
       out = gc_int(sq_count(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)]))
    case (B_FIRST)
       if (seqable(gcv_nth(vs_get(vst, base + 1), 0))) &
            out = sq_first(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)])
    case (B_REST)
       if (seqable(gcv_nth(vs_get(vst, base + 1), 0))) &
            out = sq_rest(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)])
    case (B_NEXT)
       if (.not. seqable(gcv_nth(vs_get(vst, base + 1), 0))) then
          call vs_leave(vst, base)
          return
       end if
       ! RT.next is RT.more put through seq: the two differ only in
       ! what an exhausted sequence gives back, nil versus (). Every
       ! `if (next x)` in core.clj rests on that difference.
       out = to_seq(sq_rest(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)]), &
            [vs_get(vst, base + 1)])
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
         tl = gcv_nth(vs_get(vst, base + 1), 1)
         if (seqable(tl)) then
         if (gc_kind(tl) /= OBJ_LAZY) &
              tl = to_seq(tl, [vs_get(vst, base + 1)])
         ! An EMPTY tail seq's is to nil, and (cons 1 ()) must still be
         ! the LIST (1), not a lazy cell. Macro expansions are lists,
         ! and the evaluator only recognises a list as a form -- get
         ! this wrong and a macro returns its own expansion unevaluated.
         if (tl%tag == GCT_NIL) tl = gcl_empty([vs_get(vst, base + 1)])
         if (gcl_is(tl)) then
            out = gcl_cons(gcv_nth(vs_get(vst, base + 1), 0), tl, [vs_get(vst, base + 1), tl])
         else
            out = gc_obj(OBJ_LAZY, &
                 [gc_nil(), gcv_nth(vs_get(vst, base + 1), 0), tl], &
                 [vs_get(vst, base + 1), tl])
            call gc_set_i1(out, LAZY_CONS)
         end if
         end if
       end block
    case (B_STR)
       block
         character(len=:), allocatable :: acc2
         acc2 = ""
         do i = 0, n - 1
            acc2 = acc2 // to_string_text(gcv_nth(vs_get(vst, base + 1), i))
         end do
         out = gc_str(acc2, [vs_get(vst, base + 1)])
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
         coll = gcv_nth(vs_get(vst, base + 1), 0)
         idx = as_index(gcv_nth(vs_get(vst, base + 1), 1))
         want = int(idx%ival)
         out = gc_nil()
         if (gc_kind(coll) == OBJ_CHUNK) then
            out = chunk_nth(coll, want)
         else if (gcv_is(coll) .or. coll%tag == GCT_STR) then
            if (want >= 0 .and. want < seq_len(coll)) &
                 out = seq_elem(coll, want, [vs_get(vst, base + 1)])
         else if (want >= 0) then
            walk = to_seq(coll, [vs_get(vst, base + 1)])
            do k = 1, want
               walk = sq_rest(walk, [vs_get(vst, base + 1)])
               walk = to_seq(walk, [vs_get(vst, base + 1)])
            end do
            if (walk%tag /= GCT_NIL) out = sq_first(walk, [vs_get(vst, base + 1)])
         end if
         if (out%tag == GCT_NIL .and. n >= 3) out = gcv_nth(vs_get(vst, base + 1), 2)
       end block
    case (B_GET)
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_lookup(a, gcv_nth(args, 1), n >= 3, gcv_nth(args, 2), hit)
          if (hit) then
             call vs_leave(vst, base)
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
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke(a, "assoc", rest_args(vs_get(vst, base + 1), 1), hit)
          if (hit) then
             call vs_leave(vst, base)
             return
          end if
       end if
       if (a%tag == GCT_NIL) a = gca_empty([vs_get(vst, base + 1)])
       if (gcv_is(a)) then
          ! A VECTOR IS ASSOCIATIVE BY INDEX, and assoc on one
          ! answered nil -- gca_assoc only knows maps. An index
          ! equal to the count APPENDS, which is the one place
          ! assoc grows a vector; past that it throws, as
          ! PersistentVector.assocN does. clojure.data/vectorize
          ! is built entirely out of this.
          block
            type(gc_value) :: ix
            ix = strip_meta(gcv_nth(vs_get(vst, base + 1), 1))
            if (ix%tag /= GCT_INT) then
               call fail("assoc: a vector takes an integer key")
            else if (ix%ival == int(gcv_count(a), gc_ip)) then
               out = gcv_conj(a, gcv_nth(vs_get(vst, base + 1), 2), [vs_get(vst, base + 1)])
            else if (ix%ival >= 0 .and. ix%ival < int(gcv_count(a), gc_ip)) then
               out = gcv_assoc(a, int(ix%ival), &
                    gcv_nth(vs_get(vst, base + 1), 2), [vs_get(vst, base + 1)])
            else
               call fail("Index out of bounds")
            end if
          end block
       else
          out = gca_assoc(a, &
               gcv_nth(vs_get(vst, base + 1), 1), &
               gcv_nth(vs_get(vst, base + 1), 2), [vs_get(vst, base + 1)])
       end if
       out = keep_meta(gcv_nth(vs_get(vst, base + 1), 0), out, [vs_get(vst, base + 1)])
    case (B_KEYS, B_VALS)
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_entries(a, id == B_KEYS, hit)
          if (hit) then
             call vs_leave(vst, base)
             return
          end if
       end if
       block
         type(gc_value), allocatable :: ks(:), vls(:)
         call gca_entries(strip_meta(gcv_nth(vs_get(vst, base + 1), 0)), ks, vls)
         ! nil for an empty map, as RT.keys and RT.vals answer
         out = gc_nil()
         if (size(ks) > 0) out = gcl_empty([vs_get(vst, base + 1)])
         do i = size(ks), 1, -1
            if (id == B_KEYS) then
               out = gcl_cons(ks(i), out, [vs_get(vst, base + 1), out])
            else
               out = gcl_cons(vls(i), out, [vs_get(vst, base + 1), out])
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
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          ! a record's own cons, one argument at a time; it keeps its
          ! metadata itself. conj1 answered a list of the entries.
          block
            type(gc_value) :: one
            do i = 1, n - 1
               call vs_set(vst, base + 2, a)
               one = gcv_conj(gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)]), gcv_nth(vs_get(vst, base + 1), i), &
                    [vs_get(vst, base + 1), vs_get(vst, base + 2)])
               call vs_set(vst, base + 3, one)
               a = inst_invoke(vs_get(vst, base + 2), "cons", vs_get(vst, base + 3), hit)
               if (.not. hit) a = conj1(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), [vs_get(vst, base + 1)])
               if (tctx%has_error) exit
            end do
            out = a
          end block
       else
          do i = 1, n - 1
             a = conj1(a, gcv_nth(vs_get(vst, base + 1), i), [vs_get(vst, base + 1)])
             call vs_set(vst, base + 2, a)
          end do
          out = keep_meta(gcv_nth(vs_get(vst, base + 1), 0), a, [vs_get(vst, base + 1)])
       end if
    case (B_EMPTY)
       block
         type(gc_value) :: sv
         sv = to_seq(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)])
         out = gc_bool(sv%tag == GCT_NIL)
       end block
    case (B_APPLY)
       ! (apply f a b args) -- the last argument is a SEQUENCE spread
       ! into the call, which is what makes variadic forwarding work.
       block
         type(gc_value) :: fargs, last, f, arities, ar, s, v
         integer :: j, req
         fargs = gcv_empty([vs_get(vst, base + 1)])
         do j = 1, n - 2
            fargs = gcv_conj(fargs, gcv_nth(vs_get(vst, base + 1), j), [vs_get(vst, base + 1), fargs])
         end do
         call vs_set(vst, base + 2, fargs)
         ! A variadic closure gets its rest AS IT IS. RestFn.applyTo walks
         ! the seq only as far as the required arity; what follows is the
         ! rest argument, unrealised, so (apply f 1 (range)) hands f an
         ! infinite seq instead of realising a million elements first.
         ! Anything else -- a native, a keyword, a fixed-arity fn -- takes
         ! its arguments spread, as below.
         f = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
         if (gcn_is_var(f)) f = strip_meta(gcn_var_value(f))
         req = -1
         if (gc_kind(f) == OBJ_CLOSURE) then
            arities = gcv_nth(gc_slot(f, 1), 1)
            do j = 0, gcv_count(arities) - 1
               ar = gcv_nth(arities, j)
               if (truthy(gcv_nth(ar, 1))) req = int_of(gcv_nth(ar, 0))
            end do
         end if
         if (req >= 0) then
            s = to_seq(gcv_nth(vs_get(vst, base + 1), n - 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call vs_set(vst, base + 3, s)
            ! the fixed arguments still wanted come off the front of the seq
            do while (gcv_count(vs_get(vst, base + 2)) < req .and. s%tag /= GCT_NIL .and. .not. tctx%has_error)
               v = sq_first(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
               fargs = gcv_conj(vs_get(vst, base + 2), v, [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), v])
               call vs_set(vst, base + 2, fargs)
               s = sq_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
               call vs_set(vst, base + 3, s)
               s = to_seq(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
               call vs_set(vst, base + 3, s)
            end do
            if (tctx%has_error) then
               continue
            else if (gcv_count(vs_get(vst, base + 2)) > req .or. s%tag /= GCT_NIL) then
               ! leading arguments past the fixed ones go onto the seq as it is
               do j = gcv_count(vs_get(vst, base + 2)) - 1, req, -1
                  s = seq_cons(gcv_nth(vs_get(vst, base + 2), j), vs_get(vst, base + 3), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
                  call vs_set(vst, base + 3, s)
               end do
               fargs = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
               call vs_set(vst, base + 4, fargs)
               do j = 0, req - 1
                  fargs = gcv_conj(vs_get(vst, base + 4), gcv_nth(vs_get(vst, base + 2), j), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
                  call vs_set(vst, base + 4, fargs)
               end do
               out = invoke_closure(f, vs_get(vst, base + 4), vs_get(vst, base + 3))
            else
               ! too few for the variadic arity: spread, and a fixed arity may match
               fargs = vs_get(vst, base + 2)
               out = apply(gcv_nth(vs_get(vst, base + 1), 0), fargs)
            end if
         else
         ! Through coll_to_vector, not a two-case count: the last
         ! argument is whatever `seq` produced, which is a VIEW over a
         ! vector as often as it is a list, and counting only lists and
         ! vectors made (apply f (seq xs)) call f with no arguments at
         ! all. Bounded, so (apply + (range)) is an error and not a hang.
         last = coll_to_vector(gcv_nth(vs_get(vst, base + 1), n - 1), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2)], limit=1000000)
         call vs_set(vst, base + 3, last)
         fargs = vs_get(vst, base + 2)
         do j = 0, gcv_count(vs_get(vst, base + 3)) - 1
            fargs = gcv_conj(fargs, gcv_nth(vs_get(vst, base + 3), j), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 2, fargs)
         end do
         fargs = vs_get(vst, base + 2)
         if (.not. tctx%has_error) out = apply(gcv_nth(vs_get(vst, base + 1), 0), fargs)
         end if
       end block
    case (B_PRN)
       do i = 0, n - 1
          if (i > 0) write(*, '(A)', advance='no') " "
          write(*, '(A)', advance='no') gcp_str(gcv_nth(vs_get(vst, base + 1), i), .true.)
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
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 2))
       if (a%tag /= GCT_SYM) then
          call fail("ns needs a symbol name")
       else
          out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(vst, base + 1)])
          call gcn_set_current(out)
       end if
    case (B_INNS)
       ! A FUNCTION, not a macro -- RT.java interns inNamespace without
       ! setMacro, so (in-ns 'user) evaluates its argument.
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (a%tag /= GCT_SYM) then
          call fail("in-ns needs a symbol")
       else
          out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(vst, base + 1)])
          call gcn_set_current(out)
       end if
    case (B_META)
       ! A Var keeps its metadata in slot 2; anything else carries it
       ! in a wrapper. nil when there is none, as Clojure's meta does.
       a = gcv_nth(vs_get(vst, base + 1), 0)
       out = gc_nil()
       if (gcn_is_var(a) .or. gc_kind(a) == OBJ_NS .or. gc_kind(a) == OBJ_ATOM) then
          ! An atom, ref or agent is an IReference: it carries its own
          ! metadata in the box rather than in a wrapper, which is
          ! what reset-meta! and alter-meta! write. Leaving it out
          ! here made both of them answer and then be invisible.
          out = gc_slot(a, meta_slot(a))
       else if (gc_kind(a) == OBJ_META) then
          out = gc_slot(a, 2)
       else if (gc_kind(a) == OBJ_INST) then
          ! a record answers its own meta; a reify keeps it in slot 3
          out = inst_invoke(a, "meta", gcv_empty([vs_get(vst, base + 1)]), hit)
          if (.not. hit) out = gc_slot(a, 3)
       end if
    case (B_WITHMETA)
       ! REPLACES metadata, never nests it. IObj.withMeta returns a new
       ! object carrying the new map, not an object wrapping the old
       ! one -- and defn calls (with-meta name m) on a name the reader
       ! already wrapped, so nesting buried the symbol two deep and the
       ! Var got interned under a wrapper nobody could name.
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          ! a record carries its own metadata: its withMeta, not a wrapper
          out = inst_invoke(a, "withMeta", rest_args(vs_get(vst, base + 1), 1), hit)
          if (.not. hit) then
             ! a reify (or any deftype instance): the same type and
             ! fields under the new metadata, in slot 3
             out = gc_obj(OBJ_INST, [gc_slot(a, 1), gc_slot(a, 2), gcv_nth(vs_get(vst, base + 1), 1)], &
                  [vs_get(vst, base + 1)])
          end if
          call vs_leave(vst, base)
          return
       end if
       out = gc_obj(OBJ_META, &
            [strip_meta(gcv_nth(vs_get(vst, base + 1), 0)), gcv_nth(vs_get(vst, base + 1), 1)], &
            [vs_get(vst, base + 1)])
    case (B_QUOT, B_REM)
       ! Both used to read %ival only, so (quot 7.0 2) answered 0
       ! rather than 3.0 -- the same silent discard that + - * had.
       ! A zero divisor was not checked either: Clojure raises
       ! "Divide by zero" here for doubles as well as integers,
       if (.not. numbers_ok(args, n, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
       ! unlike `/`, where (/ 1.0 0) is ##Inf.
       a = strip_meta(gcv_nth(args, 0)); b = strip_meta(gcv_nth(args, 1))
       ! A decimal quotient keeps the preferred scale, so
       ! (quot 10.5M 3) is 3.0M and (rem 10.5M 3) is 1.5M.
       if ((a%tag == GCT_DEC .or. b%tag == GCT_DEC) .and. exact_num(a) .and. exact_num(b)) then
          if (dec_is_zero(dec_of(b))) then
             call raise_class("ArithmeticException", "Divide by zero", [vs_get(vst, base + 1)])
          else if (id == B_QUOT) then
             out = gc_dec(dec_quot(dec_of(a), dec_of(b)), [vs_get(vst, base + 1)])
          else
             out = gc_dec(dec_rem(dec_of(a), dec_of(b)), [vs_get(vst, base + 1)])
          end if
          call vs_leave(vst, base)
          return
       end if
       ! Exact, truncating toward zero, with the remainder taking the
       ! dividend's sign -- BigInteger.divide and .remainder.
       if ((a%tag == GCT_BIG .or. b%tag == GCT_BIG) .and. &
            (a%tag == GCT_BIG .or. a%tag == GCT_INT) .and. (b%tag == GCT_BIG .or. b%tag == GCT_INT)) then
          block
            character(len=:), allocatable :: bq, br
            if (big_of(b) == "0") then
               call raise_class("ArithmeticException", "Divide by zero", [vs_get(vst, base + 1)])
            else
               call big_divmod(big_of(a), big_of(b), bq, br)
               if (id == B_QUOT) then
                  out = gc_big(bq, [vs_get(vst, base + 1)])
               else
                  out = gc_big(br, [vs_get(vst, base + 1)])
               end if
            end if
          end block
          call vs_leave(vst, base)
          return
       end if
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
               call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
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
             call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
          else if (id == B_QUOT) then
             out = gc_real(aint(num_dbl(a) / num_dbl(b)))
          else
             out = gc_real(mod(num_dbl(a), num_dbl(b)))
          end if
       else if (b%ival == 0) then
          call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
       else if (id == B_QUOT) then
          out = gc_int(a%ival / b%ival)
       else
          out = gc_int(mod(a%ival, b%ival))
       end if
    case (B_SECOND)
       out = sq_first(sq_rest(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)]), &
            [vs_get(vst, base + 1)])
    case (B_SEQ)
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (n >= 2) then
          ! (. sc seq ascending?), which subseq and rsubseq use
          if (.not. truthy(gcv_nth(args, 1))) then
             out = reverse_seq(a, [vs_get(vst, base + 1)])
             call vs_leave(vst, base)
             return
          end if
       end if
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke0(a, "seq", hit)
          if (hit) then
             call vs_leave(vst, base)
             return
          end if
       end if
       if (seqable(gcv_nth(vs_get(vst, base + 1), 0))) &
            out = to_seq(gcv_nth(vs_get(vst, base + 1), 0), [vs_get(vst, base + 1)])
    case (B_DISSOC)
       a = strip_meta(gcv_nth(vs_get(vst, base + 1), 0))
       if (gc_kind(a) == OBJ_INST) then
          out = inst_invoke(a, "without", rest_args(vs_get(vst, base + 1), 1), hit)
          if (hit) then
             call vs_leave(vst, base)
             return
          end if
       end if
       ! on the map UNDER any metadata, which the result keeps -- given
       ! the wrapper, gca_dissoc saw no map and answered it unchanged,
       ! so a record's own field would not dissoc
       out = gca_dissoc(a, gcv_nth(vs_get(vst, base + 1), 1), [vs_get(vst, base + 1)])
       out = keep_meta(gcv_nth(vs_get(vst, base + 1), 0), out, [vs_get(vst, base + 1)])
    case (B_NAME)
       ! The NAME PART, without the namespace: (name (quote a/b)) is
       ! "b". Returning the whole text made every qualified symbol
       ! answer with its qualifier still attached.
       out = gc_str(name_part(gcv_nth(args, 0)), [vs_get(vst, base + 1)])
    case (B_GETNAME)
       ! .getName answers in the type the host uses: a Namespace gives
       ! back a SYMBOL (which is what ns-name returns), everything else
       ! a string. The `name` FIELD of Namespace and Symbol is the same
       ! answer, (.name *ns*) in clojure.spec.alpha's ns-qualify.
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_NS) then
          out = gc_sym(gcn_name(a), [vs_get(vst, base + 1)])
       else
          out = gc_str(name_part(a), [vs_get(vst, base + 1)])
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
                   a0%tag == GCT_KEY .or. a0%tag == GCT_CLASS) then
                 t = class_of_text(a0)
              else
                 t = name_part(a0)
              end if
            end block
         end if
         if (id == B_KEYWORD) then
            out = gc_key(t, [vs_get(vst, base + 1)])
         else
            out = gc_sym(t, [vs_get(vst, base + 1)])
         end if
       end block

    case (B_SUBS)
       block
         character(len=:), allocatable :: t
         integer :: lo, hi
         a = gcv_nth(args, 0)
         if (a%tag == GCT_NIL) then
            call raise_class("NullPointerException", "subs of nil", [vs_get(vst, base + 1)])
            call vs_leave(vst, base)
            return
         end if
         t = gc_ref_text(a%ref)
         b = as_index(gcv_nth(args, 1))
         lo = int(b%ival)
         hi = u8_count(t)
         if (n >= 3) then
            b = as_index(gcv_nth(args, 2))
            hi = int(b%ival)
         end if
         if (lo < 0 .or. hi > u8_count(t) .or. lo > hi) then
            call raise_class("StringIndexOutOfBoundsException", "Range [" // trim(itoa(lo)) // ", " // trim(itoa(hi)) // ") out of bounds for length " // trim(itoa(u8_count(t))), [vs_get(vst, base + 1)])
         else
            out = gc_str(u8_slice(t, lo, hi), [vs_get(vst, base + 1)])
         end if
       end block
    case (B_VEC)
       out = coll_to_vector(gcv_nth(args, 0), [vs_get(vst, base + 1)])
    case (B_HMAP)
       ! A flat seq of alternating keys and values, which is the shape
       ! PersistentHashMap.create takes.
       block
         type(gc_value) :: items, mp
         integer :: i2
         items = coll_to_vector(gcv_nth(args, 0), [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, items)
         mp = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, mp)
         do i2 = 0, gcv_count(vs_get(vst, base + 2)) - 2, 2
            mp = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i2), &
                 gcv_nth(vs_get(vst, base + 2), i2 + 1), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, mp)
         end do
         out = vs_get(vst, base + 3)
       end block
    case (B_HSET)
       block
         type(gc_value) :: items, mp
         integer :: i2
         items = coll_to_vector(gcv_nth(args, 0), [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, items)
         mp = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, mp)
         do i2 = 0, gcv_count(vs_get(vst, base + 2)) - 1
            mp = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i2), &
                 gcv_nth(vs_get(vst, base + 2), i2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, mp)
         end do
         out = gc_obj(OBJ_SET, [vs_get(vst, base + 3)], [vs_get(vst, base + 3)])
       end block
    case (B_BITAND, B_BITOR, B_BITXOR, B_SHL, B_SHR, B_BITANDNOT, B_USHR)
       ! A bit operation is defined on FIXED-WIDTH integers only, and
       ! Clojure says so rather than guessing: "bit operation not
       ! supported for: class clojure.lang.BigInt". Without the check
       ! a BigInt read as its (empty) integer field and answered 0.
       a = strip_meta(gcv_nth(args, 0)); b = strip_meta(gcv_nth(args, 1))
       if (a%tag /= GCT_INT .or. (n >= 2 .and. b%tag /= GCT_INT)) then
          call raise_class("IllegalArgumentException", "bit operation not supported for: " // &
               class_name_of(merge(b, a, a%tag == GCT_INT)), [vs_get(vst, base + 1)])
          call vs_leave(vst, base)
          return
       end if
       select case (id)
       case (B_BITAND); out = gc_int(iand(a%ival, b%ival))
       case (B_BITOR);  out = gc_int(ior(a%ival, b%ival))
       case (B_BITXOR); out = gc_int(ieor(a%ival, b%ival))
       case (B_SHL);    out = gc_int(shiftl(a%ival, int(b%ival)))
       case (B_SHR);    out = gc_int(shifta(a%ival, int(b%ival)))
       ! x AND NOT y, which is what Numbers.andNot is
       case (B_BITANDNOT); out = gc_int(iand(a%ival, not(b%ival)))
       ! LOGICAL, not arithmetic: the sign bit is shifted in as a
       ! zero, so (unsigned-bit-shift-right -1 60) is 15 and not -1.
       case (B_USHR);   out = gc_int(shiftr(a%ival, int(b%ival)))
       end select
    case (B_BITNOT)
       a = gcv_nth(args, 0)
       out = gc_int(not(a%ival))
    case (B_CHKSHORT, B_CHKBYTE, B_CHKINT)
       ! (int 5000000000) is an ERROR in Clojure, not a truncation:
       ! RT.intCast checks the range and throws. The unchecked- ones
       ! below truncate, and pointing both at the same builtin made
       ! the checked ones answer the whole 64 bits.
       block
         integer(gc_ip) :: w, lo, hi
         character(len=32) :: wbuf
         a = strip_meta(gcv_nth(args, 0))
         w = int_of_number(a)
         select case (id)
         case (B_CHKBYTE);  lo = -128_gc_ip;        hi = 127_gc_ip
         case (B_CHKSHORT); lo = -32768_gc_ip;      hi = 32767_gc_ip
         case default;      lo = -2147483648_gc_ip; hi = 2147483647_gc_ip
         end select
         if (w < lo .or. w > hi) then
            write(wbuf, '(I0)') w
            ! RT.intCast(long) is Math.toIntExact, which throws
            ! ArithmeticException; every other checked narrowing --
            ! and intCast of a DOUBLE -- throws IllegalArgumentException
            ! naming the value.
            if (id == B_CHKINT .and. a%tag /= GCT_REAL) then
               call raise_class("ArithmeticException", "integer overflow", [vs_get(vst, base + 1)])
            else
               call raise_class("IllegalArgumentException", &
                    "Value out of range for " // trim(cast_width_name(id)) // ": " // to_string_text(a), &
                    [vs_get(vst, base + 1)])
            end if
         else
            out = gc_int(w)
         end if
       end block
    case (B_SHORTCAST, B_BYTECAST, B_INTCAST)
       ! uncheckedShortCast and friends TRUNCATE to the width, which
       ! is what makes (unchecked-byte 300) 44 and not 300. They went
       ! through longCast, which is the whole 64 bits.
       block
         integer(gc_ip) :: w, m, half
         a = strip_meta(gcv_nth(args, 0))
         w = int_of_number(a)
         select case (id)
         case (B_BYTECAST);  m = 256_gc_ip
         case (B_SHORTCAST); m = 65536_gc_ip
         case default;       m = 4294967296_gc_ip
         end select
         half = m / 2
         w = modulo(w, m)
         if (w >= half) w = w - m
         out = gc_int(w)
       end block
    case (B_LONGCAST)
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_DEC) then
          ! truncating, as BigDecimal.longValue is
          out = gc_int(big_to_i64(dec_to_big(gc_dec_text(a))))
       else if (a%tag == GCT_BIG) then
          ! TRUNCATING, which is uncheckedLongCast's rule and not
          ! longCast's -- the two share this row (DEVIATIONS 26). It is
          ! what (even? n) needs on a number past the 64-bit range,
          ! since core.clj asks for the low bit through a long.
          block
            character(len=:), allocatable :: bq, br
            integer(gc_ip) :: lv
            if (big_fits_i64(gc_big_text(a))) then
               out = gc_int(big_to_i64(gc_big_text(a)))
            else
               call big_divmod(gc_big_text(a), "18446744073709551616", bq, br)
               if (big_cmp(br, "9223372036854775807") > 0) br = big_sub(br, "18446744073709551616")
               if (big_cmp(br, "-9223372036854775808") < 0) br = big_add(br, "18446744073709551616")
               lv = big_to_i64(br)
               out = gc_int(lv)
            end if
          end block
       else if (a%tag == GCT_REAL) then
          ! Java's (long) of a double: truncation, SATURATING at the
          ! ends and 0 for NaN. int() at the default kind gave
          ! 2147483647 for 1e30.
          out = gc_int(long_of_double(a%rval))
       else if (is_ratio(a)) then
          ! (int 1/2) is 0 -- truncation toward zero, the same as for
          ! a double. The else branch would have handed the ratio
          ! straight back, unconverted.
          out = gc_int(gc_numerator(a) / gc_denominator(a))
       else if (a%tag == GCT_CHAR) then
          out = gc_int(a%ival)
       else if (a%tag == GCT_INT) then
          out = a
       else
          ! ((Number) x).longValue(): not a number is not a long
          call raise_number_cast(a, [vs_get(vst, base + 1)])
       end if
    case (B_ANEWINST)
       out = array_new_instance(vs_get(vst, base + 1), [vs_get(vst, base + 1)])

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
       if (.not. numbers_ok(args, n, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
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
            if (.not. tctx%has_error) out = gc_bool(same)
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
         else if (x%tag == GCT_BIG) then
            out = gc_big(big_abs(gc_big_text(x)), [vs_get(vst, base + 1)])
         else if (x%tag == GCT_DEC) then
            out = gc_dec(dec_abs(gc_dec_text(x)), [vs_get(vst, base + 1)])
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
       out = struct_basis(args, [vs_get(vst, base + 1)])
    case (B_SCREATE)
       out = struct_create(args, [vs_get(vst, base + 1)])
    case (B_SCONSTRUCT)
       out = struct_construct(args, [vs_get(vst, base + 1)])
    case (B_SACCESSOR)
       out = struct_accessor(args, [vs_get(vst, base + 1)])

    case (B_COLLEMPTY)
       out = coll_empty(gcv_nth(args, 0), [vs_get(vst, base + 1)])

    case (B_MACROEXP1)
       out = macroexpand_1step(gcv_nth(args, 0))

    case (B_ASIFASSOC)
       ! One collection, alternating k v, as if by repeated assoc.
       block
         type(gc_value) :: kvv, acc
         integer :: i, n2
         kvv = coll_to_vector(gcv_nth(args, 0), [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, kvv)
         n2 = gcv_count(vs_get(vst, base + 2))
         acc = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, acc)
         do i = 0, n2 - 2, 2
            acc = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i), &
                 gcv_nth(vs_get(vst, base + 2), i + 1), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, acc)
         end do
         ! an odd count ends in a map, merged: keyword arguments with a
         ! trailing map, as createAsIfByAssoc takes since 1.11
         if (mod(n2, 2) == 1) then
            block
              type(gc_value) :: last
              type(gc_value), allocatable :: kk(:), vv(:)
              integer :: j
              last = strip_meta(gcv_nth(vs_get(vst, base + 2), n2 - 1))
              if (gca_is(last)) then
                 call gca_entries(last, kk, vv)
                 do j = 1, size(kk)
                    acc = gca_assoc(vs_get(vst, base + 3), kk(j), vv(j), &
                         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
                    call vs_set(vst, base + 3, acc)
                 end do
              else
                 call raise_class("IllegalArgumentException", "No value supplied for key: " // &
                      gcp_str(last, .true.), [vs_get(vst, base + 1)])
              end if
            end block
         end if
         out = vs_get(vst, base + 3)
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
            call vs_leave(vst, base)
            return
         end if
         call vs_set(vst, base + 2, a0)
         h = gc_i1(vs_get(vst, base + 2))
         kn = gcna_kind(h)
         ! The clone has the shape of the VIEW, not of the buffer
         ! behind it: (aclone (aget m 0)) on a 2x3 is a fresh length-3
         ! array, the way Java's aclone of one row of a [[I is. Taking
         ! gcna_extents(h) here cloned the whole 2x3 instead. Every
         ! dimension of a fresh array is 0-based, so lows is zeros
         ! rather than the source's.
         ext = array_own_extents(vs_get(vst, base + 2))
         allocate(lows(size(ext)))
         lows = 0
         h2 = gcna_new(kn, ext, lows, err)
         if (h2 == 0) then
            call fail(err)
            call vs_leave(vst, base)
            return
         end if
         n2 = gcna_total(h2)
         run = gc_nil()
         if (kn == "value") run = gc_vec(max(1, n2), [vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, run)
         out = gc_obj(OBJ_ARRAY, [vs_get(vst, base + 3)], &
              [vs_get(vst, base + 2), vs_get(vst, base + 3)])
         call gc_set_i1(out, h2)
         call gc_set_i2(out, -1) ! owns the handle -- not a slice
         do k = 1, n2
            e = array_elem(vs_get(vst, base + 2), k)
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
            call vs_leave(vst, base)
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
         if (len(err) > 9) then
            if (err(1:9) == "negative:") then
               call raise_class("NegativeArraySizeException", err(10:), [vs_get(vst, base + 1)])
               call vs_leave(vst, base)
               return
            end if
         end if
         if (h == 0) then
            call fail(err)
            call vs_leave(vst, base)
            return
         end if
         ! A `value` array keeps its elements in a GC RUN so the
         ! collector traces them; every numeric kind has its buffer in
         ! the registry and leaves slot 1 nil.
         run = gc_nil()
         if (kname == "value") run = gc_vec(max(1, gcna_total(h)), [vs_get(vst, base + 1)])
         out = gc_obj(OBJ_ARRAY, [run], [vs_get(vst, base + 1), run])
         call gc_set_i1(out, h)
         call gc_set_i2(out, -1) ! owns the handle -- not a slice
       end block

    case (B_SPIT)
       ! (clotran-spit path text): the whole file replaced by the text.
       ! core.clj's spit is written over java.io, which is not here;
       ! this is clotran-slurp's other half.
       block
         character(len=:), allocatable :: path, text
         integer :: u, st
         path = text_of(gcv_nth(args, 0))
         text = text_of(gcv_nth(args, 1))
         open(newunit=u, file=path, access="stream", form="unformatted", &
              status="replace", action="write", iostat=st)
         if (st /= 0) then
            call fail_as("java.io.FileNotFoundException", path // " (cannot open for writing)", [vs_get(vst, base + 1)])
         else
            write(u) text
            close(u)
            out = gc_nil()
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
            call fail_as("java.io.FileNotFoundException", path // " (No such file or directory)", [vs_get(vst, base + 1)])
         else
            inquire(unit=u, size=fsize)
            allocate(character(len=fsize) :: text)
            if (fsize > 0) read(u, iostat=st) text
            close(u)
            out = gc_str(text, [vs_get(vst, base + 1)])
         end if
       end block

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
            out = gc_str(gcna_kind(gc_i1(a0)), [vs_get(vst, base + 1)])
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
            acc = gcv_empty([vs_get(vst, base + 1)])
            call vs_set(vst, base + 2, acc)
            do k = 1, size(ext)
               acc = gcv_conj(vs_get(vst, base + 2), gc_int(ext(k)), [vs_get(vst, base + 2)])
               call vs_set(vst, base + 2, acc)
            end do
            out = vs_get(vst, base + 2)
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
            call vs_leave(vst, base)
            return
         end if
         h = gc_i1(a0)
         nsub = n - 1
         if (id == B_ASET) nsub = n - 2
         if (nsub < 1) then
            call fail("aget/aset: needs at least one index")
            call vs_leave(vst, base)
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
            call vs_leave(vst, base)
            return
         end if

         ! Out of range is ArrayIndexOutOfBoundsException naming the index
         ! and the length, as the JVM says it -- for a slice as for an
         ! element: a bad slice index once answered nil.
         block
           integer, allocatable :: ext(:)
           character(len=24) :: bi, bn
           ext = array_own_extents(a0)
           do k = 1, nsub
              if (subs(k) < 0 .or. subs(k) >= ext(k)) then
                 write(bi, '(I0)') subs(k)
                 write(bn, '(I0)') ext(k)
                 call raise_class("ArrayIndexOutOfBoundsException", "Index " // trim(bi) // &
                      " out of bounds for length " // trim(bn), [vs_get(vst, base + 1)])
                 call vs_leave(vst, base)
                 return
              end if
           end do
         end block

         if (nsub < own_rank) then
            ! A SLICE over the remaining dimensions. aset never
            ! assigns a whole sub-array at once -- core.clj's own
            ! multi-arg aset always slices down to a full index before
            ! writing -- so this path is aget-only.
            if (id == B_ASET) then
               call fail("aset: not enough indices")
               call vs_leave(vst, base)
               return
            end if
            out = array_make_slice(a0, subs, [vs_get(vst, base + 1)])
            call vs_leave(vst, base)
            return
         end if

         ! Every own dimension is specified: fold to the REAL buffer
         ! position, whether a0 is a base array or already a slice.
         call array_fold(a0, subs, foff, fstr, ok)
         if (.not. ok) then
            call fail("aget/aset: index out of bounds")
            call vs_leave(vst, base)
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
                    [vs_get(vst, base + 1)])
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
    case (B_SIMPLENAME)
       ! Class.getSimpleName: the name without its package, so
       ! String's is "String". It shared getName's row and answered
       ! "java.lang.String", which every error report that names an
       ! exception's class then carried.
       block
         character(len=:), allocatable :: nm
         type(gc_value) :: full
         full = call_builtin(B_GETNAME, args)
         if (.not. tctx%has_error) then
            nm = text_of(full)
            out = gc_str(nm(index(nm, ".", back=.true.) + 1:), [vs_get(vst, base + 1)])
         end if
       end block
    case (B_ARRAYCAST)
       ! (clotran-array-cast value :doubles) -- the checkcast Clojure
       ! emits where an array-hinted value is used as an array. The
       ! value comes back unchanged or it throws. nil is the
       ! NullPointerException the array operation would raise on it; the
       ! wrong thing is a ClassCastException naming both types the way
       ! the JVM does, [D for double[] and so on.
       block
         character(len=:), allocatable :: want, desc, have, kind
         type(gc_value) :: hv
         a = strip_meta(gcv_nth(args, 0))
         hv = strip_meta(gcv_nth(args, 1))
         select case (gc_ref_text(hv%ref))
         case ("doubles");  want = "real8";   desc = "[D"
         case ("longs");    want = "int8";    desc = "[J"
         case ("ints");     want = "int4";    desc = "[I"
         case ("shorts");   want = "int4";    desc = "[S"
         case ("bytes");    want = "int4";    desc = "[B"
         case ("floats");   want = "real4";   desc = "[F"
         case ("booleans"); want = "logical"; desc = "[Z"
         case ("chars");    want = "value";   desc = "[C"
         case default;      want = "value";   desc = "[Ljava.lang.Object;"
         end select
         if (a%tag == GCT_NIL) then
            call raise_class("NullPointerException", "Cannot use a null array", [vs_get(vst, base + 1)])
         else if (gc_kind(a) == OBJ_ARRAY) then
            kind = gcna_kind(gc_i1(a))
            if (kind == want .and. gcna_rank(gc_i1(a)) == 1) then
               out = a
            else
               select case (kind)
               case ("real8");   have = "[D"
               case ("int8");    have = "[J"
               case ("int4");    have = "[I"
               case ("real4");   have = "[F"
               case ("logical"); have = "[Z"
               case default;     have = "[Ljava.lang.Object;"
               end select
               if (gcna_rank(gc_i1(a)) > 1) have = repeat("[", gcna_rank(gc_i1(a)) - 1) // have
               call raise_class("ClassCastException", "class " // have // " cannot be cast to class " // desc, &
                    [vs_get(vst, base + 1)])
            end if
         else
            call raise_class("ClassCastException", "class " // class_name_of(a) // &
                 " cannot be cast to class " // desc, [vs_get(vst, base + 1)])
         end if
       end block
    case (B_LONGCAST_CHECKED, B_NUMLONG)
       ! B_NUMLONG is a ^long PARAMETER's conversion: the compiler checks
       ! for a Number first (Compiler.emitUnboxArg), so a character is a
       ! ClassCastException there, though (long \a) is 97.
       a = strip_meta(gcv_nth(args, 0))
       if (id == B_NUMLONG .and. a%tag == GCT_CHAR) then
          call raise_number_cast(a, [vs_get(vst, base + 1)])
          call vs_leave(vst, base)
          return
       end if
       ! RT.longCast, clojure.core/long. Read from RT.java at the pinned
       ! commit: an integer answers itself; a BigInt must fit or it is
       ! "Value out of range for long"; a ratio truncates; a character
       ! is its code; ANY OTHER number goes through its double, with the
       ! same range check. A non-number is a ClassCastException and nil
       ! a NullPointerException, because RT casts to Number. Sharing
       ! uncheckedLongCast's row made (long "a") answer "a" and
       ! (long 1e30) answer 2147483647.
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_INT .or. a%tag == GCT_CHAR) then
          out = gc_int(a%ival)
       else if (a%tag == GCT_BIG) then
          if (big_fits_i64(gc_big_text(a))) then
             out = gc_int(big_to_i64(gc_big_text(a)))
          else
             call raise_class("IllegalArgumentException", "Value out of range for long: " // &
                  gcp_str(a, .false.), [vs_get(vst, base + 1)])
          end if
       else if (is_ratio(a)) then
          out = gc_int(gc_numerator(a) / gc_denominator(a))
       else if (a%tag == GCT_REAL .or. a%tag == GCT_DEC) then
          block
            real(gc_dp) :: d
            d = num_dbl(a)
            ! -2^63 and 2^63 as doubles are what Long.MIN_VALUE and
            ! MAX_VALUE become in RT's comparison
            if (d < -9223372036854775808.0_gc_dp .or. d > 9223372036854775808.0_gc_dp) then
               call raise_class("IllegalArgumentException", "Value out of range for long: " // &
                    gcp_str(gc_real(d), .false.), [vs_get(vst, base + 1)])
            else
               out = gc_int(long_of_double(d))
            end if
          end block
       else
          call raise_number_cast(a, [vs_get(vst, base + 1)])
       end if
    case (B_DBLCAST)
       ! ((Number) x).doubleValue(), checked and unchecked alike: a
       ! number converts, nil and anything else raise. It answered
       ! 0.0 for both.
       a = strip_meta(gcv_nth(args, 0))
       if (is_number(a)) then
          out = gc_real(num_dbl(a))
       else
          call raise_number_cast(a, [vs_get(vst, base + 1)])
       end if
    case (B_BOOLCAST)
       out = gc_bool(truthy(gcv_nth(args, 0)))
    case (B_CHARCAST)
       ! int_of_number, not the integer FIELD, and a code point, not
       ! achar. (char 50.0) read the unset ival of a real and answered
       ! a space, which is how cl-format's base-str turned every digit
       ! of a double or a BigInt into one -- (cl-format nil "~D" 2e6)
       ! was seven blanks. achar also wrapped at 256, so (char 955)
       ! was a guillemet rather than a lambda.
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_CHAR) then
          out = a
       else
          out = gc_char_cp(int(int_of_number(a)))
       end if
    case (B_ALTERMETA)
       block
         type(gc_value) :: ref, fargs, extra
         integer :: j
         ref = gcv_nth(args, 0)
         call vs_set(vst, base + 2, ref)
         fargs = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         fargs = gcv_conj(fargs, gc_slot(vs_get(vst, base + 2), meta_slot(vs_get(vst, base + 2))), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, fargs)
         extra = coll_to_vector(gcv_nth(args, 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
         fargs = vs_get(vst, base + 3)
         do j = 0, gcv_count(extra) - 1
            fargs = gcv_conj(fargs, gcv_nth(extra, j), [vs_get(vst, base + 1), extra])
            call vs_set(vst, base + 3, fargs)
         end do
         out = apply(gcv_nth(args, 1), vs_get(vst, base + 3))
         if (.not. tctx%has_error) then
            call gc_set_slot(vs_get(vst, base + 2), meta_slot(vs_get(vst, base + 2)), out)
         end if
       end block
    case (B_FINDNS)
       ! Namespace.find: nil for a namespace nobody made. Creating one
       ! here made (the-ns 'nope) answer a namespace instead of
       ! throwing, and alias to it succeed.
       a = strip_meta(gcv_nth(args, 0))
       out = gcn_find(gc_ref_text(a%ref))
    case (B_LOADFILE)
       ! Read the whole file, then analyse and evaluate each form. The
       ! first error ends it, as Compiler.load does. *ns* is SAVED AND
       ! RESTORED around it, as Compiler.load pushes a binding for it:
       ! a loaded file's (ns ...) once leaked into its caller, and the
       ! forms after (load-file ...) were analysed in the wrong namespace.
       block
         character(len=:), allocatable :: path, text
         type(gc_value) :: forms, genv, f
         integer :: u, st, fsize, j, fid, nsb
         logical :: eof
         out = gc_nil()
         path = text_of(gcv_nth(args, 0))
         nsb = vs_enter(vst, 1)
         call vs_set(vst, nsb + 1, gcn_current([vs_get(vst, base + 1)]))
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
            call vs_set(vst, base + 2, genv)
            ! one form at a time, as main.f90's load_file and Compiler.load
            fid = gcr_begin_file(text, path)
            j = 1
            do
               forms = gcr_read_next(text, j, [vs_get(vst, base + 1), vs_get(vst, base + 2)], eof, fid)
               if (gcr_has_error()) then
                  call fail("load-file " // path // ": " // gcr_error())
                  exit
               end if
               if (eof) exit
               call vs_set(vst, base + 3, forms)
               f = gce_analyze(vs_get(vst, base + 3), vs_get(vst, base + 2))
               if (tctx%has_error) exit
               out = gce_eval(f, vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
               if (tctx%has_error) exit
            end do
            if (.not. tctx%has_error) call gce_install_compiled(path)
         end if
         call gcn_set_current(vs_get(vst, nsb + 1))
         call vs_leave(vst, nsb)
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
         out = gc_str(acc // t, [vs_get(vst, base + 1)])
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
            out = gc_int(u8_count(gc_ref_text(cv%ref)))
         else if (gc_kind(cv) == OBJ_SB) then
            ! A StringBuilder IS a CharSequence, so .length is its
            ! text's. Answering the seq count (0) made clojure.string's
            ! trim -- which loops down from .length -- answer "".
            out = gc_int(u8_count(text_of(cv)))
         else
            out = gc_int(sq_count(cv, [vs_get(vst, base + 1)]))
         end if
       end block
    case (B_SUBSTRING)
       block
         character(len=:), allocatable :: t
         type(gc_value) :: iv
         integer :: lo, hi
         t = text_of(gcv_nth(args, 0))
         iv = as_index(gcv_nth(args, 1))
         lo = int(iv%ival)
         hi = u8_count(t)
         if (n >= 3) then
            iv = as_index(gcv_nth(args, 2))
            hi = int(iv%ival)
         end if
         if (lo < 0 .or. hi > u8_count(t) .or. lo > hi) then
            call raise_class("StringIndexOutOfBoundsException", "Range [" // trim(itoa(lo)) // ", " // trim(itoa(hi)) // ") out of bounds for length " // trim(itoa(u8_count(t))), [vs_get(vst, base + 1)])
         else
            out = gc_str(u8_slice(t, lo, hi), [vs_get(vst, base + 1)])
         end if
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
            out = gc_bool(truthy(gca_get(md2, gc_key("macro", [vs_get(vst, base + 1)]))))
         else
            out = gc_bool(.not. truthy(gca_get(md2, &
                 gc_key("private", [vs_get(vst, base + 1)]))))
         end if
       end block
    case (B_SETMACRO)
       a = strip_meta(gcv_nth(args, 0))
       call var_set_macro(a)
       out = gc_nil()
    case (B_DOTGET)
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_TASK) then
          ! (.get task), or (.get task timeout unit); tasks.inc
          if (n >= 2) then
             out = task_get(a, now_ms() + int(int_of(gcv_nth(args, 1)), gc_ip))
          else
             out = task_get(a, -1_gc_ip)
          end if
       else if (n >= 2) then
          out = gca_get(a, gcv_nth(args, 1))
       else
          if (gcn_is_var(a) .or. gc_kind(a) == OBJ_ATOM) then
             out = gc_slot(a, 1)
          else if (is_reduced(a)) then
             out = gca_get(a, gc_key("clotran/reduced", [vs_get(vst, base + 1)]))
          else
             out = a
          end if
       end if
    case (B_SUBMIT)
       ! (.submit executor f): the executor is whatever soloExecutor is
       ! -- nil here -- and the task is what matters (tasks.inc).
       out = task_submit(gcv_nth(args, n - 1))
    case (B_TASKDONE, B_TASKCANCELLED)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_bool(.false.)
       if (gc_kind(a) == OBJ_TASK) then
          if (id == B_TASKDONE) then
             out = gc_bool(gc_i1(a) >= TASK_DONE)
          else
             out = gc_bool(gc_i1(a) == TASK_CANCELLED)
          end if
       end if
    case (B_TASKCANCEL)
       out = gc_bool(task_cancel(strip_meta(gcv_nth(args, 0))))
    case (B_LATCHWAIT)
       ! (.await latch), or (.await latch ms unit) answering whether the
       ! count reached zero in time. A latch is an atom holding its count.
       a = strip_meta(gcv_nth(args, 0))
       if (n >= 2) then
          hit = block_on(a, now_ms() + int(int_of(gcv_nth(args, 1)), gc_ip))
          if (.not. tctx%yield_flag .and. .not. tctx%has_error) out = gc_bool(hit)
       else
          hit = block_on(a, -1_gc_ip)
       end if
    case (B_SLEEP)
       ! Thread.sleep: the clock, with the other tasks running meanwhile
       hit = block_on(gc_nil(), now_ms() + int(int_of(gcv_nth(args, 0)), gc_ip))
    case (B_NPROCS)
       ! Runtime.availableProcessors: the processors online (Threads.f90).
       ! pmap keeps this many plus two futures in flight, and futures
       ! whose Fortran runs off the baton use them (tasks.inc).
       out = gc_int(int(th_ncpus(), gc_ip))
    case (B_STUB)
       out = gc_key("clotran/stub", [vs_get(vst, base + 1)])
    case (B_SORTEDMAP, B_SORTEDSET)
       ! PersistentTreeMap/create keyvals, or comparator keyvals, and
       ! PersistentTreeSet/create likewise over keys (sorted.inc)
       out = sorted_create(args, n, id == B_SORTEDSET, [vs_get(vst, base + 1)])
    case (B_SEQFROM)
       ! (. sc seqFrom key ascending?): the entries from the first key
       ! at or past `key`, that way
       a = strip_meta(gcv_nth(args, 0))
       b = sorted_backing(a)
       out = gc_nil()
       if (b%tag /= GCT_NIL) then
          i = gca_sorted_from(b, gcv_nth(args, 1), truthy(gcv_nth(args, 2)))
          if (.not. tctx%has_error) out = sorted_entries(a, i, truthy(gcv_nth(args, 2)), [vs_get(vst, base + 1)])
       end if
    case (B_ENTRYKEY)
       ! (. sc entryKey e): an entry's key -- the element itself, for a set
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_SET) then
          out = gcv_nth(args, 1)
       else
          out = sq_first(gcv_nth(args, 1), [vs_get(vst, base + 1)])
       end if
    case (B_COMPARATOR)
       ! (.comparator sc): its comparator, or compare itself
       out = gca_comparator(sorted_backing(gcv_nth(args, 0)))
       if (out%tag == GCT_NIL) out = native(B_COMPARE, "compare", [vs_get(vst, base + 1)])
    case (B_RSEQ)
       ! (rseq coll): a vector or a sorted collection, last first; nil when empty
       out = reverse_seq(strip_meta(gcv_nth(args, 0)), [vs_get(vst, base + 1)])
    case (B_TASKSTATUS)
       ! (task-status t): the protocol's five words for a task's state
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gc_kind(a) == OBJ_TASK) then
          select case (gc_i1(a))
          case (TASK_NEW, TASK_RUNNABLE)
             out = gc_key("parked", [a])
          case (TASK_RUNNING)
             out = gc_key("running", [a])
          case (TASK_DONE)
             out = gc_key("done", [a])
          case (TASK_FAILED)
             out = gc_key("failed", [a])
          case default
             out = gc_key("cancelled", [a])
          end select
       end if
    case (B_MAILBOX)
       ! (task-mailbox t), or (task-mailbox nil) for the main context
       a = gc_nil()
       if (n > 0) a = strip_meta(gcv_nth(args, 0))
       out = task_mailbox(a)
    case (B_CURTASK)
       ! (current-task): the task running now, or nil in the main context
       out = gc_nil()
       if (gc_kind(tctx%cur_task) == OBJ_TASK) out = tctx%cur_task
    case (B_GENIFACE)
       out = gc_nil()
    case (B_ALWAYS_FALSE)
       out = gc_bool(.false.)
    case (B_EMPTYVEC)
       out = gcv_empty([vs_get(vst, base + 1)])
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
            pv = gc_obj(OBJ_REGEX, [gc_str(ptext, [vs_get(vst, base + 1)])], [vs_get(vst, base + 1)])
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
                  mv = gc_obj(OBJ_MATCHER, [pat, gc_str(stext, [vs_get(vst, base + 1), pat])], &
                       [vs_get(vst, base + 1), pat])
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
    case (B_TOBIG)
       ! (bigint x) and (biginteger x), and the .toBigInteger /
       ! .bigIntegerValue members core.clj reaches them through. A
       ! double and a ratio TRUNCATE toward zero, as BigDecimal's and
       ! Ratio's own conversions do.
       block
         type(gc_value) :: bv
         bv = strip_meta(gcv_nth(args, 0))
         select case (bv%tag)
         case (GCT_BIG)
            out = bv
         case (GCT_INT, GCT_CHAR)
            out = gc_big(big_from_i64(bv%ival), [vs_get(vst, base + 1)])
         case (GCT_RATIO)
            out = gc_big(big_from_i64(gc_numerator(bv) / gc_denominator(bv)), [vs_get(vst, base + 1)])
         case (GCT_REAL)
            out = gc_big(big_from_i64(int(aint(bv%rval), gc_ip)), [vs_get(vst, base + 1)])
         case (GCT_DEC)
            out = gc_big(dec_to_big(gc_dec_text(bv)), [vs_get(vst, base + 1)])
         case (GCT_STR)
            if (big_valid(text_of(bv))) then
               out = gc_big(text_of(bv), [vs_get(vst, base + 1)])
            else
               call raise_class("NumberFormatException", "For input string: " // text_of(bv), [vs_get(vst, base + 1)])
            end if
         case default
            call raise_class("IllegalArgumentException", "cannot convert to a BigInt", [vs_get(vst, base + 1)])
         end select
       end block
    case (B_TODEC)
       ! (bigdec x), and the BigDecimal/valueOf and (BigDecimal. x)
       ! core.clj reaches it through. A double goes by its printed
       ! form, which is what BigDecimal.valueOf(double) does -- and
       ! why (bigdec 1.5) is 1.5M and not the binary approximation.
       block
         type(gc_value) :: dv2
         character(len=:), allocatable :: dt
         logical :: dok2
         dv2 = strip_meta(gcv_nth(args, 0))
         select case (dv2%tag)
         case (GCT_DEC)
            out = dv2
         case (GCT_INT, GCT_CHAR)
            out = gc_dec(dec_from_i64(dv2%ival), [vs_get(vst, base + 1)])
         case (GCT_BIG)
            out = gc_dec(dec_from_big(gc_big_text(dv2)), [vs_get(vst, base + 1)])
         case (GCT_REAL, GCT_STR, GCT_RATIO)
            if (dv2%tag == GCT_RATIO) then
               call dec_div(dec_from_big(big_from_i64(gc_numerator(dv2))), &
                    dec_from_big(big_from_i64(gc_denominator(dv2))), dt, dok2)
            else
               call dec_from_text(to_string_text(dv2), dt, dok2)
            end if
            if (dok2) then
               out = gc_dec(dt, [vs_get(vst, base + 1)])
            else
               call raise_class("NumberFormatException", &
                    "not a decimal: " // to_string_text(dv2), [vs_get(vst, base + 1)])
            end if
         case default
            call raise_class("IllegalArgumentException", "cannot convert to a BigDecimal", [vs_get(vst, base + 1)])
         end select
       end block
    case (B_GCTORTURE)
       ! (clotran-gc-torture true) -- collect at EVERY allocation from
       ! here on. A rooting bug is otherwise a value that is wrong only
       ! when the heap happens to fill at the wrong moment; under
       ! torture it is wrong every time. The env var CLOTRAN_GC_TORTURE
       ! does the same from the second file onwards (main.f90); this is
       ! for turning it on around one form.
       gc_torture = truthy(gcv_nth(args, 0))
       out = gc_bool(gc_torture)
    case (B_RANDOMUUID)
       ! A version-4 UUID's text, from the random generator plus a
       ! counter so two in one process never collide. There is no UUID
       ! class here (uuid.clj is skipped, DEVIATIONS 12); spec.alpha only
       ! compares the ids it makes with these.
       block
         character(len=36) :: u
         character(len=32) :: hx
         real :: r(4)
         integer :: k, w(4)
         integer, save :: uuid_seq = 0
         uuid_seq = uuid_seq + 1
         call random_number(r)
         do k = 1, 4
            w(k) = int(r(k) * 2147483647.0)
         end do
         w(4) = ieor(w(4), uuid_seq)
         write(hx, '(4Z8.8)') w
         u = hx(1:8) // "-" // hx(9:12) // "-4" // hx(14:16) // "-a" // hx(18:20) // "-" // hx(21:32)
         out = gc_str(u, [vs_get(vst, base + 1)])
       end block
    case (B_ISWS, B_ISLOWER, B_ISDIGIT, B_ISLETTER, B_ISALNUM)
       ! Character.isX over the code point, answered by ICU (cu_* in
       ! regex_shim.c); u_isWhitespace is defined as Java's.
       block
         type(gc_value) :: cv
         integer(c_int32_t) :: cp
         cv = strip_meta(gcv_nth(args, 0))
         cp = int(cv%ival, c_int32_t)
         select case (id)
         case (B_ISWS);     out = gc_bool(cu_isws(cp) /= 0)
         case (B_ISLOWER);  out = gc_bool(cu_islower(cp) /= 0)
         case (B_ISDIGIT);  out = gc_bool(cu_isdigit(cp) /= 0)
         case (B_ISLETTER); out = gc_bool(cu_isalpha(cp) /= 0)
         case (B_ISALNUM);  out = gc_bool(cu_isalnum(cp) /= 0)
         end select
       end block
    case (B_UPCASE, B_DOWNCASE)
       ! A character or a whole string: Character/toUpperCase and
       ! String.toUpperCase, one code point at a time through ICU's
       ! SIMPLE case map -- one code point to one, so ß stays ß where
       ! Java's String.toUpperCase writes SS.
       block
         type(gc_value) :: v
         character(len=:), allocatable :: t, r
         integer :: p, cp, nb
         logical :: up
         up = (id == B_UPCASE)
         v = strip_meta(gcv_nth(args, 0))
         if (v%tag == GCT_CHAR) then
            out = gc_char_cp(case_cp(int(v%ival), up))
         else
            t = text_of(v)
            r = ""
            p = 1
            do while (p <= len(t))
               call u8_dec(t, p, cp, nb)
               r = r // u8_enc(case_cp(cp, up))
               p = p + nb
            end do
            out = gc_str(r, [vs_get(vst, base + 1)])
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
            if (iv%ival >= 0 .and. iv%ival < u8_count(t)) out = gc_char_cp(u8_at(t, int(iv%ival)))
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
            call gc_set_slot(w, 1, gc_str(text_of(gc_slot(w, 1)) // piece, [vs_get(vst, base + 1)]))
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
       out = gc_str(gce_home() // "/src/clj", [vs_get(vst, base + 1)])
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
            out = gc_str(text, [vs_get(vst, base + 1)])
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
         lb = vs_enter(vst, 4)
         call vs_set(vst, lb + 1, strip_meta(gcv_nth(args, 0)))
         txt = text_of(gcv_nth(args, 1))
         m = gca_empty([vs_get(vst, lb + 1)])
         call vs_set(vst, lb + 2, m)
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
                          [vs_get(vst, lb + 1), vs_get(vst, lb + 2)])
                     call vs_set(vst, lb + 3, kk)
                     vv = gc_str(trim(adjustl(ln(eq + 1:))), &
                          [vs_get(vst, lb + 1), vs_get(vst, lb + 2), vs_get(vst, lb + 3)])
                     call vs_set(vst, lb + 4, vv)
                     m = gca_assoc(vs_get(vst, lb + 2), vs_get(vst, lb + 3), vs_get(vst, lb + 4), &
                          [vs_get(vst, lb + 1), vs_get(vst, lb + 2), vs_get(vst, lb + 3), vs_get(vst, lb + 4)])
                     call vs_set(vst, lb + 2, m)
                  end if
               end if
            end if
            p0 = p1 + 1
         end do
         call gc_set_slot(vs_get(vst, lb + 1), 1, vs_get(vst, lb + 2))
         call vs_leave(vst, lb)
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
       ! Long.valueOf and parseLong take one argument; any other count
       ! fails in the Reflector's words, as the static call does there
       if (n /= 1) then
          block
            character(len=16) :: cbuf
            write(cbuf, '(I0)') n
            call raise_class("IllegalArgumentException", "No matching method found taking " // &
                 trim(cbuf) // " args for class java.lang.Long", [vs_get(vst, base + 1)])
          end block
          call vs_leave(vst, base)
          return
       end if
       block
         type(gc_value) :: a0
         character(len=:), allocatable :: t
         integer(gc_ip) :: iv
         integer :: st
         a0 = strip_meta(gcv_nth(args, 0))
         if (a0%tag == GCT_INT) then
            out = a0
         else
            t = trim(adjustl(text_of(a0)))
            ! Long.valueOf's grammar, not list-directed input's: an
            ! optional sign and digits and nothing else. "1 2" and
            ! "1,2" read as 1 without a word; and a 64-bit result, or
            ! Long/MAX_VALUE came back truncated.
            st = 1
            if (len(t) > 0 .and. len(t) <= 20) then
               if (verify(t, "+-0123456789") == 0 .and. verify(t(2:), "0123456789") == 0 &
                    .and. scan(t, "0123456789") > 0) read(t, *, iostat=st) iv
            end if
            if (st /= 0) then
               call fail_as("NumberFormatException", "valueOf: not a number: " // t, &
                    [vs_get(vst, base + 1)])
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
    case (B_POOLREG)
       ! (clotran-pool-register v) -- a compiled namespace's constants,
       ! kept alive and answered by handle.
       out = gc_int(int(cf_pool_add(strip_meta(gcv_nth(args, 0))), gc_ip))
    case (B_ALLNS)
       ! Namespace.all: core.clj's all-ns.
       out = gcn_all([vs_get(vst, base + 1)])
    case (B_LOADCOMPILED)
       ! (clotran-load-compiled "path" pool) -- open a compiled
       ! namespace and let it install its functions, handing it the
       ! handle of the constant pool registered for it. True, or an
       ! error naming what the loader could not do.
       block
         character(len=:), allocatable :: lerr
         if (dl_install(text_of(strip_meta(gcv_nth(args, 0))), &
              int(int_of_number(strip_meta(gcv_nth(args, 1)))), lerr)) then
            out = gc_bool(.true.)
         else
            call raise_class("RuntimeException", lerr, [vs_get(vst, base + 1)])
         end if
       end block
    case (B_ASTDATA)
       ! (clotran-ast 'form) -- analyse the form and hand back the
       ! tree as nested maps. Analysis is where every name has already
       ! become a Var handle or a frame slot and every node has a
       ! kind, so a generator reading this never has to resolve
       ! anything. It is the SAME analysis the executor runs; there is
       ! no second front end to disagree with the first.
       block
         type(gc_value) :: genv, node
         genv = gce_env()
         call vs_set(vst, base + 2, genv)
         node = gce_analyze(strip_meta(gcv_nth(args, 0)), vs_get(vst, base + 2))
         if (.not. tctx%has_error) then
            call vs_set(vst, base + 3, node)
            out = ast_data(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            ! and the pool and fingerprint of this same analysis, so the
            ! pool's nodes are the ones the tree's :node keys hold
            block
              integer :: lb
              lb = vs_enter(vst, 3)
              call vs_set(vst, lb + 1, out)
              out = compiled_pool(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, lb + 1)])
              call vs_set(vst, lb + 2, out)
              call vs_set(vst, lb + 3, gc_key("pool", [vs_get(vst, base + 1), vs_get(vst, lb + 1), vs_get(vst, lb + 2)]))
              out = gca_assoc(vs_get(vst, lb + 1), vs_get(vst, lb + 3), gca_get(vs_get(vst, lb + 2), vs_get(vst, lb + 3)), &
                   [vs_get(vst, base + 1), vs_get(vst, lb + 1), vs_get(vst, lb + 2), vs_get(vst, lb + 3)])
              call vs_set(vst, lb + 1, out)
              call vs_set(vst, lb + 3, gc_key("fingerprint", [vs_get(vst, base + 1), vs_get(vst, lb + 1), vs_get(vst, lb + 2)]))
              out = gca_assoc(vs_get(vst, lb + 1), vs_get(vst, lb + 3), gca_get(vs_get(vst, lb + 2), vs_get(vst, lb + 3)), &
                   [vs_get(vst, base + 1), vs_get(vst, lb + 1), vs_get(vst, lb + 2), vs_get(vst, lb + 3)])
              call vs_leave(vst, lb)
            end block
         end if
       end block
    case (B_READFORMS)
       ! (clotran-read-forms path): every top-level form of a file as a
       ! vector, read as load-file reads them -- the file registered with
       ! the reader, so each form's position decodes to its real file,
       ! line and column (clotran-position). Nothing is evaluated, so a
       ! ::keyword resolves against the CURRENT namespace: bind *ns*.
       block
         character(len=:), allocatable :: path, text
         type(gc_value) :: form, acc
         integer :: u, st, fsize, j, fid, lb
         logical :: eof
         path = text_of(gcv_nth(args, 0))
         open(newunit=u, file=path, access="stream", form="unformatted", &
              status="old", action="read", iostat=st)
         if (st /= 0) then
            call fail_as("java.io.FileNotFoundException", path // " (No such file or directory)", [vs_get(vst, base + 1)])
         else
            inquire(unit=u, size=fsize)
            allocate(character(len=fsize) :: text)
            if (fsize > 0) read(u, iostat=st) text
            close(u)
            lb = vs_enter(vst, 1)
            call vs_set(vst, lb + 1, gcv_empty([vs_get(vst, base + 1)]))
            fid = gcr_begin_file(text, path)
            j = 1
            do
               form = gcr_read_next(text, j, [vs_get(vst, base + 1), vs_get(vst, lb + 1)], eof, fid)
               if (gcr_has_error()) then
                  call fail("clotran-read-forms " // path // ": " // gcr_error())
                  exit
               end if
               if (eof) exit
               acc = gcv_conj(vs_get(vst, lb + 1), form, [vs_get(vst, base + 1), vs_get(vst, lb + 1), form])
               call vs_set(vst, lb + 1, acc)
            end do
            if (.not. tctx%has_error) out = vs_get(vst, lb + 1)
            call vs_leave(vst, lb)
         end if
       end block
    case (B_ARRAYTYPESYM)
       ! clojure.lang.Util/arrayTypeToSymbol: an array class as the symbol
       ! Clojure prints it with -- component/dimensions, double/1 for [D.
       block
         character(len=:), allocatable :: cn, comp
         character(len=16) :: db
         integer :: dims
         a = strip_meta(gcv_nth(args, 0))
         cn = gc_ref_text(a%ref)
         dims = verify(cn, "[") - 1
         select case (cn(dims + 1:))
         case ("D"); comp = "double"
         case ("J"); comp = "long"
         case ("I"); comp = "int"
         case ("F"); comp = "float"
         case ("Z"); comp = "boolean"
         case ("C"); comp = "char"
         case ("B"); comp = "byte"
         case ("S"); comp = "short"
         case default
            comp = cn(dims + 2:len(cn) - 1)   ! L<name>;
         end select
         write(db, '(I0)') dims
         out = gc_sym(comp // "/" // trim(db), [vs_get(vst, base + 1)])
       end block
    case (B_POSITION)
       ! (clotran-position pos): a node's packed source position, as the
       ! analyser recorded it (clotran-ast's :pos), decoded to
       ! [file line column]; nil for a node with none. The compiler's
       ! diagnostics point at source with it.
       block
         character(len=:), allocatable :: fname
         integer :: line, col, lb
         type(gc_value) :: pv, v
         pv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (pv%tag == GCT_INT) then
            if (pv%ival > 0) then
               call gcr_position_parts(int(pv%ival), fname, line, col)
               lb = vs_enter(vst, 1)
               v = gcv_empty([vs_get(vst, base + 1)])
               call vs_set(vst, lb + 1, v)
               v = gcv_conj(vs_get(vst, lb + 1), gc_str(fname, [vs_get(vst, base + 1), vs_get(vst, lb + 1)]), &
                    [vs_get(vst, base + 1), vs_get(vst, lb + 1)])
               call vs_set(vst, lb + 1, v)
               v = gcv_conj(vs_get(vst, lb + 1), gc_int(int(line, gc_ip)), [vs_get(vst, base + 1), vs_get(vst, lb + 1)])
               call vs_set(vst, lb + 1, v)
               v = gcv_conj(vs_get(vst, lb + 1), gc_int(int(col, gc_ip)), [vs_get(vst, base + 1), vs_get(vst, lb + 1)])
               out = v
               call vs_leave(vst, lb)
            end if
         end if
       end block
    case (B_ASTPOOL)
       ! (clotran-ast-pool 'form) -- clotran-ast's :pool and :fingerprint
       ! without exporting the tree: what clotran.loader needs to install
       ! a compiled function, at a small part of the cost.
       block
         type(gc_value) :: genv, node
         genv = gce_env()
         call vs_set(vst, base + 2, genv)
         node = gce_analyze(strip_meta(gcv_nth(args, 0)), vs_get(vst, base + 2))
         if (.not. tctx%has_error) then
            call vs_set(vst, base + 3, node)
            out = compiled_pool(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         end if
       end block
    case (B_EDNREAD)
       ! (EdnReader/readString s opts). The EDN grammar is the Clojure
       ! reader's without eval, syntax-quote or the deref and var
       ! shorthands, none of which our reader produces from data
       ! anyway; what IS particular to it is that its data readers
       ! come from the OPTS map rather than from *data-readers*. So
       ! the form is read with #tag left as a marker and the markers
       ! are resolved here, against :readers, then the built-in uuid,
       ! then :default.
       block
         type(gc_value) :: sv, opts, form
         logical :: was
         sv = strip_meta(gcv_nth(args, 0))
         opts = strip_meta(gcv_nth(args, 1))
         call vs_set(vst, base + 2, opts)
         if (sv%tag /= GCT_STR) then
            call fail("edn/read-string wants a string")
         else
            was = gcr_set_tag_markers(.true.)
            form = gcr_read(gc_ref_text(sv%ref), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            was = gcr_set_tag_markers(was)
            if (gcr_has_error()) then
               call fail(gcr_error())
            else
               call vs_set(vst, base + 3, form)
               out = resolve_tags(vs_get(vst, base + 3), vs_get(vst, base + 2), &
                    [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            end if
         end if
       end block
    case (B_ISARRAY)
       ! Class.isArray, which clojure.data reaches as
       ! (.. x getClass isArray) to decide that an array diffs as a
       ! SEQUENCE rather than as an atom. Answering false always made
       ! (diff [1 2] (into-array [1 2])) say they differ.
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_CLASS) then
          out = gc_bool(short_class_name(gc_ref_text(a%ref)) == "array" .or. &
               index(gc_ref_text(a%ref), "[") == 1)
       else
          out = gc_bool(gc_kind(a) == OBJ_ARRAY)
       end if
    case (B_MUNGE, B_DEMUNGE)
       a = strip_meta(gcv_nth(args, 0))
       if (id == B_MUNGE) then
          out = gc_str(munge_text(gc_ref_text(a%ref)), [vs_get(vst, base + 1)])
       else
          out = gc_str(demunge_text(gc_ref_text(a%ref)), [vs_get(vst, base + 1)])
       end if
    case (B_NSUNMAP)
       ! (.unmap ns sym): the mapping goes, the Var itself stays
       ! wherever else it is referred from. Namespace.unmap.
       block
         type(gc_value) :: nsv, m
         nsv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (gc_kind(nsv) == OBJ_NS) then
            call vs_set(vst, base + 2, nsv)
            m = gca_dissoc(gc_slot(vs_get(vst, base + 2), 2), strip_meta(gcv_nth(args, 1)), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call gc_set_slot(vs_get(vst, base + 2), 2, m)
            out = vs_get(vst, base + 2)
         end if
       end block
    case (B_QOFFER, B_QTAKE)
       ! .offer conjes onto the queue and answers true; .take blocks
       ! until there is something and pops the front. The queue is an
       ! atom holding a vector, which is exactly what block_on already
       ! knows how to wait for.
       block
         type(gc_value) :: q, items
         logical :: gotit
         q = strip_meta(gcv_nth(args, 0))
         call vs_set(vst, base + 2, q)
         if (id == B_QOFFER) then
            items = gc_slot(vs_get(vst, base + 2), 1)
            if (.not. gcv_is(items)) items = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call vs_set(vst, base + 3, items)
            items = gcv_conj(vs_get(vst, base + 3), gcv_nth(args, 1), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call gc_set_slot(vs_get(vst, base + 2), 1, items)
            ! Nothing else will run the taps: one OS thread, and the
            ! loop that reads this queue is parked on it. Step it here,
            ! so tap> delivers rather than waiting for the next block.
            call run_ready_tasks(vs_get(vst, base + 2))
            out = gc_bool(.true.)
         else
            gotit = block_on(vs_get(vst, base + 2), -1_gc_ip)
            items = gc_slot(vs_get(vst, base + 2), 1)
            if (gcv_is(items) .and. gcv_count(items) > 0) then
               out = gcv_nth(items, 0)
               call vs_set(vst, base + 3, out)
               call gc_set_slot(vs_get(vst, base + 2), 1, &
                    gcv_subvec_from(items, 1, [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]))
               out = vs_get(vst, base + 3)
            else
               out = gc_nil()
            end if
         end if
       end block
    case (B_THREADSTART)
       ! kept for a thread started by something other than .start
       out = strip_meta(gcv_nth(args, 0))
       if (gc_kind(out) == OBJ_CLOSURE) out = task_submit(out)
    case (B_THREADDAEMON)
       ! (.setDaemon t b): there is one OS thread, so this is a no-op
       ! that answers the thread, which doto threads on.
       out = strip_meta(gcv_nth(args, 0))
    case (B_TAGGEDLIT)
       ! (tagged-literal tag form): {:tag t :form f} under the marker.
       block
         type(gc_value) :: m
         m = gca_empty([vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, m)
         call vs_set(vst, base + 3, gc_key("clotran/tagged-literal", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
         m = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 3), gc_bool(.true.), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
         call vs_set(vst, base + 2, m)
         call vs_set(vst, base + 3, gc_key("tag", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
         m = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 3), gcv_nth(args, 0), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
         call vs_set(vst, base + 2, m)
         call vs_set(vst, base + 3, gc_key("form", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
         out = gca_assoc(vs_get(vst, base + 2), vs_get(vst, base + 3), gcv_nth(args, 1), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       end block
    case (B_UUIDOF)
       ! (parse-uuid s) and UUID/fromString. A UUID is its TEXT here
       ! (DEVIATIONS 12: java.util.UUID is not a type clotran has), so
       ! this checks the shape and answers the string; a string that
       ! is not one raises, which is what parse-uuid catches to nil.
       out = uuid_of(gcv_nth(args, 0), [vs_get(vst, base + 1)])
    case (B_ADDWATCH, B_REMWATCH, B_GETWATCHES)
       ! The watches live beside the validator and the error handler
       ! in slot 4, as a map from key to fn.
       block
         type(gc_value) :: r, w
         r = strip_meta(gcv_nth(args, 0))
         call vs_set(vst, base + 2, r)
         w = ref_fn_get(vs_get(vst, base + 2), "watches", [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         if (.not. gca_is(w)) w = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, w)
         select case (id)
         case (B_GETWATCHES)
            out = vs_get(vst, base + 3)
         case (B_ADDWATCH)
            w = gca_assoc(vs_get(vst, base + 3), gcv_nth(args, 1), gcv_nth(args, 2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, w)
            call ref_fn_put(vs_get(vst, base + 2), "watches", vs_get(vst, base + 3), [vs_get(vst, base + 1)])
            out = vs_get(vst, base + 2)
         case default
            w = gca_dissoc(vs_get(vst, base + 3), gcv_nth(args, 1), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, w)
            call ref_fn_put(vs_get(vst, base + 2), "watches", vs_get(vst, base + 3), [vs_get(vst, base + 1)])
            out = vs_get(vst, base + 2)
         end select
       end block
    case (B_HASHORD, B_HASHUNORD)
       ! The SAME folds gce_coll_hash uses, so a collection and the
       ! hash of its elements agree: ordered multiplies by 31 as a
       ! vector does, unordered sums as a set does. The numbers are
       ! not murmur3's (DEVIATIONS 15); what matters is that equal
       ! collections hash alike and that these agree with `hash`.
       block
         type(gc_value) :: sq, el
         integer :: acc
         acc = 0
         sq = to_seq(gcv_nth(args, 0), [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, sq)
         sq = vs_get(vst, base + 2)
         do while (sq%tag /= GCT_NIL .and. .not. tctx%has_error)
            el = sq_first(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            if (id == B_HASHORD) then
               acc = 31 * acc + gc_hash(el)
            else
               acc = acc + gc_hash(el)
            end if
            sq = sq_rest(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call vs_set(vst, base + 2, sq)
            sq = to_seq(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call vs_set(vst, base + 2, sq)
         end do
         if (id == B_HASHORD) then
            out = gc_int(mix32(acc))
         else
            out = gc_int(mix32(ieor(acc, OBJ_SET)))
         end if
       end block
    case (B_HASHCOMB)
       ! Util.hashCombine: seed ^ (hash + 0x9e3779b9 + (seed<<6) + (seed>>2))
       block
         integer :: sd, hv
         sd = int(strip_int(gcv_nth(args, 0)))
         hv = int(strip_int(gcv_nth(args, 1)))
         out = gc_int(int(ieor(sd, hv + (-1640531527) + shiftl(sd, 6) + shifta(sd, 2)), gc_ip))
       end block
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
               out = gc_str(u8_slice(stext, gstart, gend), [vs_get(vst, base + 1)])
            end if
         end if
       end block
    case (B_ISREDUCED)
       out = gc_bool(is_reduced(gcv_nth(args, 0)))
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
                 call vs_leave(vst, base)
                 return
              end if
            end block
            fk = "sym"
         case (B_FLD_PROTOCOL); fk = "protocol"
         case (B_FLD_METHODK);  fk = "methodk"
         case default;          fk = "map"
         end select
         out = gca_get(strip_meta(gcv_nth(args, 0)), &
              gc_key(trim(fk), [vs_get(vst, base + 1)]))
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
                 [vs_get(vst, base + 1)])
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
         call vs_set(vst, base + 2, nsv)
         call vs_set(vst, base + 3, sym2)
         var2 = gcn_intern(vs_get(vst, base + 2), vs_get(vst, base + 3), val2, &
              [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
         if (n >= 3) call gc_set_i1(var2, 1)
         out = var2
       end block
    case (B_FORNAME)
       ! An ARRAY class is the exception, and core.clj needs it:
       ! to-array-2d is (make-array (Class/forName "[Ljava.lang.Object;")
       ! n), so throwing here made it fail on every collection, ragged
       ! or not. The name answers as a class, make-array reads it as
       ! the "value" kind (array_kind_for's default), and each row is
       ! then an ARRAY STORED AS AN ELEMENT -- which is how a ragged
       ! result is possible here despite DEVIATIONS 24: the rank-2
       ! Fortran buffer is not involved.
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_STR) then
          block
            character(len=:), allocatable :: cn
            cn = gc_ref_text(a%ref)
            if (len(cn) > 0) then
               if (cn(1:1) == "[") then
                  out = gc_class(cn, [vs_get(vst, base + 1)])
                  call vs_leave(vst, base)
                  return
               end if
            end if
          end block
       end if
       ! Otherwise there are no Java classes, so Class/forName THROWS -- which
       ! is the honest answer and also the useful one: core.clj's
       ! when-class catches ClassNotFoundException and skips the
       ! body, so (when-class "java.sql.Timestamp" (load "instant"))
       ! skips itself without clotran naming instant at all.
       block
         type(gc_value) :: exc
         exc = gc_obj(OBJ_ERR, &
              [gc_sym("ClassNotFoundException", [vs_get(vst, base + 1)]), &
               gcv_nth(args, 0), gc_nil()], [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, exc)
         call set_thrown(vs_get(vst, base + 2))
         tctx%has_error = .true.
         tctx%last_error = gcp_str(vs_get(vst, base + 2), .true.)
         out = gc_nil()
       end block
    case (B_TOARRAY)
       ! A REAL array, not a vector. That comment used to say every
       ! use fed straight back into a seq, which was true until
       ! `sort`: it is (let [a (to-array coll)] (. Arrays (sort a cmp))
       ! (seq a)) -- the array is sorted IN PLACE and then read back,
       ! and a persistent vector cannot be mutated.
       out = value_array_of(gcv_nth(args, 0), [vs_get(vst, base + 1)])
    case (B_ITERATE)
       ! (iterate f x) -- x, (f x), (f (f x)) ... unbounded, so a
       ! LAZY cell whose thunk is built by the evaluator. Realised
       ! head, unrealised tail: exactly what lazy-seq produces.
       out = iterate_cell(gcv_nth(args, 0), gcv_nth(args, 1), &
            [vs_get(vst, base + 1)])
    case (B_CYCLE)
       ! (cycle coll) repeats it forever. Built by hand as a ring:
       ! the last cell'"s tail is the first cell, so the whole thing
       ! is O(n) in the collection and infinite to walk.
       block
         type(gc_value) :: items, cell, prev, firstc
         integer :: j, cn
         items = coll_to_vector(gcv_nth(args, 0), [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, items)
         cn = gcv_count(vs_get(vst, base + 2))
         out = gc_nil()
         if (cn > 0) then
            firstc = gc_nil()
            prev = gc_nil()
            do j = 0, cn - 1
               cell = gc_obj(OBJ_LAZY, [gc_nil(), &
                    gcv_nth(vs_get(vst, base + 2), j), gc_nil()], &
                    [vs_get(vst, base + 1), vs_get(vst, base + 2)])
               call gc_set_i1(cell, LAZY_CONS)
               if (j == 0) then
                  firstc = cell
                  call vs_set(vst, base + 3, firstc)
               else
                  call gc_set_slot(prev, 3, cell)
               end if
               prev = cell
            end do
            call gc_set_slot(prev, 3, vs_get(vst, base + 3))
            out = vs_get(vst, base + 3)
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
            iv = as_index(gcv_nth(args, 0))
            cnt = int(iv%ival)
            acc = gcl_empty([vs_get(vst, base + 1)])
            call vs_set(vst, base + 2, acc)
            do j = 1, cnt
               acc = gcl_cons(gcv_nth(args, 1), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
               call vs_set(vst, base + 2, acc)
            end do
            out = vs_get(vst, base + 2)
          end block
       else
          out = gc_obj(OBJ_LAZY, [gc_nil(), gcv_nth(args, 0), gc_nil()], &
               [vs_get(vst, base + 1)])
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
         hi = as_int(gcv_nth(args, 0))
         if (n >= 2) then
            lo = hi
            hi = as_int(gcv_nth(args, 1))
         end if
         if (n >= 3) stp = as_int(gcv_nth(args, 2))
         if (.not. (is_number(lo) .and. is_number(hi) .and. is_number(stp))) then
                 call fail("range: not a number")
         else
            out = range_cell(lo, hi, stp, [vs_get(vst, base + 1)])
         end if
       end block
    case (B_RUNTX)
       out = apply(gcv_nth(args, 0), gcv_empty([vs_get(vst, base + 1)]))
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
            if (.not. gca_is(out)) out = gca_empty([vs_get(vst, base + 1)])
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
            call vs_set(vst, base + 2, nsv)
            m = gc_slot(vs_get(vst, base + 2), 3)
            if (.not. gca_is(m)) m = gca_empty([vs_get(vst, base + 1)])
            call vs_set(vst, base + 3, m)
            m = gca_assoc(vs_get(vst, base + 3), strip_meta(gcv_nth(args, 1)), &
                 gcv_nth(args, 2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
            call gc_set_slot(vs_get(vst, base + 2), 3, m)
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
            call vs_set(vst, base + 2, nsv)
            m = gc_slot(vs_get(vst, base + 2), 2)
            if (.not. gca_is(m)) m = gca_empty([vs_get(vst, base + 1)])
            m = gca_assoc(m, strip_meta(gcv_nth(args, 1)), gcv_nth(args, 2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call gc_set_slot(vs_get(vst, base + 2), 2, m)
            out = vs_get(vst, base + 2)
         end if
       end block
    case (B_MAYBERESOLVE)
       ! Compiler.maybeResolveIn(ns, sym): in THAT namespace -- its
       ! mappings, its aliases -- not the current one. It resolved in
       ! the current namespace, so (ns-resolve 'clojure.core 'num) from
       ! a namespace with its own num answered that one.
       block
         type(gc_value) :: sym2, nsv, tgt
         character(len=:), allocatable :: t
         integer :: slash
         sym2 = strip_meta(gcv_nth(args, n - 1))
         nsv = gc_nil()
         if (n >= 2) nsv = strip_meta(gcv_nth(args, 0))
         out = gc_nil()
         if (sym2%tag /= GCT_SYM) then
            continue
         else if (gc_kind(nsv) /= OBJ_NS) then
            out = resolve_var(sym2, vs_get(vst, base + 1))
         else
            call vs_set(vst, base + 2, nsv)
            t = gc_ref_text(sym2%ref)
            slash = index(t, "/")
            if (slash > 1 .and. slash < len(t)) then
               tgt = alias_in(vs_get(vst, base + 2), t(1:slash-1), [vs_get(vst, base + 1)])
               if (gc_kind(tgt) /= OBJ_NS) tgt = gcn_find(t(1:slash-1))
               if (gc_kind(tgt) == OBJ_NS) then
                  call vs_set(vst, base + 3, tgt)
                  out = gcn_lookup(vs_get(vst, base + 3), gc_sym(t(slash+1:), [vs_get(vst, base + 1), vs_get(vst, base + 3)]))
               end if
               if (.not. gcn_is_var(out)) out = gc_nil()
            else
               out = gcn_lookup(vs_get(vst, base + 2), sym2)
               ! then clojure.core, which every namespace refers -- the
               ! same fallback a bare symbol takes when it is analysed
               ! (DEVIATIONS 3). Without it (resolve 'nil?) was nil in
               ! every namespace but clojure.core, and clojure.spec.alpha
               ! resolves the symbols of a pred form that way.
               if (.not. gcn_is_var(out)) &
                    out = gcn_lookup(gcn_find_or_create("clojure.core", [vs_get(vst, base + 1)]), sym2)
               if (.not. gcn_is_var(out)) then
                  out = gc_nil()
                  ! A class that EXISTS -- a row in the host table or a
                  ! deftype -- and not merely a name shaped like one:
                  ! (resolve 'NonExistentClass.Name) is nil on the JVM.
                  if (is_class_name(sym2) .and. known_class_name(t)) &
                       out = gc_class(class_key(t), [vs_get(vst, base + 1)])
               end if
            end if
         end if
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
            else if (cn == 0) then
               call raise_class("IllegalStateException", "Can't pop empty vector", [vs_get(vst, base + 1)])
            else
               acc = gcv_empty([vs_get(vst, base + 1)])
               call vs_set(vst, base + 2, acc)
               do j = 0, cn - 2
                  acc = gcv_conj(vs_get(vst, base + 2), gcv_nth(coll, j), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                  call vs_set(vst, base + 2, acc)
               end do
               out = keep_meta(gcv_nth(args, 0), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
            end if
         else if (.not. gcl_is(coll) .and. coll%tag /= GCT_NIL) then
            ! not a stack: IPersistentStack is a vector or a list, and a
            ! seq, a set or a map is refused as on the JVM
            call raise_class("ClassCastException", class_name_of(coll) // &
                 " cannot be cast to clojure.lang.IPersistentStack", [vs_get(vst, base + 1)])
         else if (coll%tag /= GCT_NIL) then
            if (id == B_PEEK) then
               out = sq_first(coll, [vs_get(vst, base + 1)])
            else
               acc = to_seq(coll, [vs_get(vst, base + 1)])
               if (acc%tag == GCT_NIL) then
                  call raise_class("IllegalStateException", "Can't pop empty list", [vs_get(vst, base + 1)])
               else
                  out = sq_rest(coll, [vs_get(vst, base + 1)])
               end if
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
            if (sl > 1) out = gc_str(t(1:sl-1), [vs_get(vst, base + 1)])
         end if
       end block
    case (B_KEY, B_VAL)
       block
         type(gc_value) :: e
         e = strip_meta(gcv_nth(args, 0))
         if (id == B_KEY) then
            out = seq_elem(e, 0, [vs_get(vst, base + 1)])
         else
            out = seq_elem(e, 1, [vs_get(vst, base + 1)])
         end if
       end block
    case (B_CONTAINS)
       block
         type(gc_value) :: coll
         coll = strip_meta(gcv_nth(args, 0))
         if (gc_kind(coll) == OBJ_INST) then
            out = inst_invoke(coll, "containsKey", rest_args(args, 1), hit)
            if (hit) then
             call vs_leave(vst, base)
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
         if (gcv_is(coll)) then
            ! a vector is associative by index: (find [1 2] 0) is [0 1]
            if (coll_has(coll, gcv_nth(args, 1))) then
               pair = gcv_empty([vs_get(vst, base + 1)])
               pair = gcv_conj(pair, gcv_nth(args, 1), [vs_get(vst, base + 1)])
               call vs_set(vst, base + 2, pair)
               pair = gcv_conj(vs_get(vst, base + 2), gcv_nth(coll, int_of(gcv_nth(args, 1))), &
                    [vs_get(vst, base + 1), vs_get(vst, base + 2)])
               out = pair
               call mark_entry(out)
            end if
         else if (gca_contains(coll, gcv_nth(args, 1))) then
            pair = gcv_empty([vs_get(vst, base + 1)])
            ! the map's own key, metadata and all, as MapEntry carries it
            pair = gcv_conj(pair, gca_find_key(coll, gcv_nth(args, 1)), [vs_get(vst, base + 1)])
            call vs_set(vst, base + 2, pair)
            pair = gcv_conj(vs_get(vst, base + 2), gca_get(coll, gcv_nth(args, 1)), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            out = pair
            call mark_entry(out)
         end if
       end block
    case (B_SETVAL, B_RESETVALS)
       a = gcv_nth(args, 0)
       if (gc_kind(a) == OBJ_MULTIFN) then
          ! MultiFn.reset, behind remove-all-methods: methods, preferences and cache
          call gc_set_slot(a, 4, gca_empty([vs_get(vst, base + 1)]))
          call mf_aux_set(a, 1, gca_empty([vs_get(vst, base + 1)]))
          call mf_reset_cache(a)
          out = a
          call vs_leave(vst, base)
          return
       end if
       out = gcv_nth(args, 1)
       block
         type(gc_value) :: prev
         ! THE VALIDATOR RUNS BEFORE THE WRITE, and a refusal
         ! leaves the reference alone -- which is the whole point
         ! of set-validator!.
         if (.not. validate_ref(a, ref_fn_get(a, "validator", [vs_get(vst, base + 1)]), &
              out, [vs_get(vst, base + 1)])) then
            call vs_leave(vst, base)
            return
         end if
         prev = gc_slot(a, 1)
         call gc_set_slot(a, 1, out)
         call notify_watches(a, prev, out, [vs_get(vst, base + 1)])
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
         lb = vs_enter(vst, 3)
         call vs_set(vst, lb + 1, strip_meta(gcv_nth(args, 0)))
         fargs = gcv_empty([vs_get(vst, lb + 1)])
         fargs = gcv_conj(fargs, gc_slot(vs_get(vst, lb + 1), 1), [vs_get(vst, lb + 1)])
         call vs_set(vst, lb + 2, fargs)
         ! indices 2 and 3 are values
         do j = 2, min(n, 4) - 1
            fargs = gcv_conj(vs_get(vst, lb + 2), gcv_nth(args, j), &
                 [vs_get(vst, lb + 1), vs_get(vst, lb + 2)])
            call vs_set(vst, lb + 2, fargs)
         end do
         ! index 4, when present, is a seq to splice
         if (n >= 5) then
            call vs_set(vst, lb + 3, coll_to_vector(gcv_nth(args, 4), &
                 [vs_get(vst, lb + 1), vs_get(vst, lb + 2)]))
            do j = 0, gcv_count(vs_get(vst, lb + 3)) - 1
               fargs = gcv_conj(vs_get(vst, lb + 2), gcv_nth(vs_get(vst, lb + 3), j), &
                    [vs_get(vst, lb + 1), vs_get(vst, lb + 2), vs_get(vst, lb + 3)])
               call vs_set(vst, lb + 2, fargs)
            end do
         end if
         out = apply(gcv_nth(args, 1), vs_get(vst, lb + 2))
         if (.not. tctx%has_error) then
            if (.not. validate_ref(vs_get(vst, lb + 1), &
                 ref_fn_get(vs_get(vst, lb + 1), "validator", [vs_get(vst, lb + 1)]), &
                 out, [vs_get(vst, lb + 1)])) then
               call vs_leave(vst, lb)
               call vs_leave(vst, base)
               return
            end if
            if (id == B_SWAPVALS) then
               out = value_pair(gc_slot(vs_get(vst, lb + 1), 1), out, &
                    [vs_get(vst, lb + 1), vs_get(vst, lb + 2)])
               call gc_set_slot(vs_get(vst, lb + 1), 1, gcv_nth(out, 1))
               call notify_watches(vs_get(vst, lb + 1), gcv_nth(out, 0), gcv_nth(out, 1), [vs_get(vst, lb + 2)])
            else
               call vs_set(vst, lb + 3, gc_slot(vs_get(vst, lb + 1), 1))
               call gc_set_slot(vs_get(vst, lb + 1), 1, out)
               call notify_watches(vs_get(vst, lb + 1), vs_get(vst, lb + 3), out, [vs_get(vst, lb + 2)])
            end if
         end if
         call vs_leave(vst, lb)
       end block
    case (B_ALTERVAL)
       ! (.alter ref f args) is (apply f @ref args), stored back.
       block
         type(gc_value) :: ref, fargs, extra
         integer :: j
         ref = gcv_nth(args, 0)
         call vs_set(vst, base + 2, ref)
         fargs = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         fargs = gcv_conj(fargs, gc_slot(vs_get(vst, base + 2), var_root_slot(vs_get(vst, base + 2))), &
              [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, fargs)
         if (n >= 3) then
            extra = coll_to_vector(gcv_nth(args, 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            fargs = vs_get(vst, base + 3)
            do j = 0, gcv_count(extra) - 1
               fargs = gcv_conj(fargs, gcv_nth(extra, j), [vs_get(vst, base + 1), extra])
               call vs_set(vst, base + 3, fargs)
            end do
         end if
         out = apply(gcv_nth(args, 1), vs_get(vst, base + 3))
         if (.not. tctx%has_error) call gc_set_slot(vs_get(vst, base + 2), var_root_slot(vs_get(vst, base + 2)), out)
       end block
    case (B_BINDROOT)
       ! Var.bindRoot: the root, wherever a binding in force has put it
       a = gcv_nth(args, 0)
       out = gcv_nth(args, 1)
       if (.not. validate_ref(a, ref_fn_get(a, "validator", [vs_get(vst, base + 1)]), &
            out, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
       call gc_set_slot(a, var_root_slot(a), out)
       out = gc_nil()
    case (B_RAWROOT)
       a = gcv_nth(args, 0)
       out = gc_slot(a, var_root_slot(a))
    case (B_MAPENTRY)
       ! MapEntry/create
       out = value_pair(gcv_nth(args, 0), gcv_nth(args, 1), [vs_get(vst, base + 1)])
       call mark_entry(out)
    case (B_ISASSIGN)
       out = gc_bool(class_assignable(strip_meta(gcv_nth(args, 0)), strip_meta(gcv_nth(args, 1))))
    case (B_HASHCODE)
       out = gc_int(int(java_hashcode(gcv_nth(args, 0)), gc_ip))
    case (B_CANSEQ)
       ! RT.canSeq, behind seqable?: what seq would take without
       ! complaint -- nil, strings, the collections, and a deftype
       ! that answers seq or iterator
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_NIL) then
          out = gc_bool(.true.)
       else if (gc_kind(a) == OBJ_INST) then
          out = gc_bool(gc_kind(inst_method(a, "seq")) == OBJ_CLOSURE .or. &
               gc_kind(inst_method(a, "iterator")) == OBJ_CLOSURE)
       else
          out = gc_bool(seqable_quiet(a))
       end if
    case (B_NSCREATE)
       ! Namespace.findOrCreate, behind create-ns: the one that makes one
       a = strip_meta(gcv_nth(args, 0))
       out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(vst, base + 1)])
    case (B_NSREMOVE)
       ! Namespace.remove, which refuses clojure.core as it does there
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (a%tag == GCT_SYM) then
          if (gc_ref_is(a%ref, "clojure.core")) then
             call raise_class("IllegalArgumentException", "Cannot remove clojure namespace", [vs_get(vst, base + 1)])
          else
             out = gcn_remove(gc_ref_text(a%ref))
          end if
       end if
    case (B_GETCAUSE)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gc_kind(a) == OBJ_ERR) out = gc_slot(a, 5)
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
         call vs_set(vst, base + 2, genv)
         form = gce_analyze(gcv_nth(args, 0), vs_get(vst, base + 2))
         call vs_set(vst, base + 3, form)
         if (.not. tctx%has_error) &
              out = gce_eval(vs_get(vst, base + 3), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
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
         call vs_set(vst, base + 2, m)
         call gca_entries(vs_get(vst, base + 2), kk, vv)
         saved = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, saved)
         do j = 1, size(kk)
            if (gcn_is_var(kk(j))) then
               saved = gca_assoc(vs_get(vst, base + 3), kk(j), gc_slot(kk(j), 1), &
                    [vs_get(vst, base + 1), vs_get(vst, base + 3)])
               call vs_set(vst, base + 3, saved)
               ! The first binding of a Var parks its ROOT in slot 5,
               ! where bindRoot, alter-var-root and def reach it while
               ! the binding stands; i2 counts the bindings. So
               ! with-redefs inside a binding changes what the binding
               ! restores to and not what it shows, as on the JVM.
               if (gc_i2(kk(j)) == 0) call gc_set_slot(kk(j), 5, gc_slot(kk(j), 1))
               call gc_set_i2(kk(j), gc_i2(kk(j)) + 1)
               call gc_set_slot(kk(j), 1, vv(j))
            end if
         end do
         if (gc_root_live(tctx%binding_stack_root)) then
            stack = gc_root_get(tctx%binding_stack_root)
         else
            stack = gcl_empty([vs_get(vst, base + 3)])
         end if
         stack = gcl_cons(vs_get(vst, base + 3), stack, [vs_get(vst, base + 3), stack])
         call gc_global_keep(tctx%binding_stack_root, stack)
         out = gc_nil()
       end block
    case (B_POPTB)
       block
         type(gc_value) :: stack, frame
         type(gc_value), allocatable :: kk(:), vv(:)
         integer :: j
         out = gc_nil()
         if (gc_root_live(tctx%binding_stack_root)) then
            stack = gc_root_get(tctx%binding_stack_root)
            call vs_set(vst, base + 2, stack)
            if (gcl_count(vs_get(vst, base + 2)) > 0) then
               frame = gcl_first(vs_get(vst, base + 2))
               call vs_set(vst, base + 3, frame)
               call gca_entries(vs_get(vst, base + 3), kk, vv)
               do j = 1, size(kk)
                  if (gcn_is_var(kk(j))) then
                     call gc_set_slot(kk(j), 1, vv(j))
                     call gc_set_i2(kk(j), max(0, gc_i2(kk(j)) - 1))
                     if (gc_i2(kk(j)) == 0) then
                        ! the last binding gone: the root, as bindRoot left it
                        call gc_set_slot(kk(j), 1, gc_slot(kk(j), 5))
                        call gc_set_slot(kk(j), 5, gc_nil())
                     end if
                  end if
               end do
               call gc_global_keep(tctx%binding_stack_root, &
                    gcl_rest(vs_get(vst, base + 2), [vs_get(vst, base + 2)]))
            end if
         end if
       end block
    case (B_FINDVAR)
       block
         type(gc_value) :: sym2
         sym2 = strip_meta(gcv_nth(args, 0))
         out = resolve_var(sym2, vs_get(vst, base + 1))
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
                     if (u8_cpidx(hay, j) > int(strip_int(gcv_nth(args, 2)))) exit
                  end if
                  hit = j
               end if
            end do
         end if
         if (hit > 0) then
            out = gc_int(u8_cpidx(hay, hit))
         else
            out = gc_int(-1)
         end if
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
            call vs_leave(vst, base)
            return
         end if
         if (rel == "clojure/core_proxy" .or. &
              rel == "clojure/genclass" .or. &
              rel == "clojure/gvec" .or. &
              rel == "clojure/uuid" .or. &
              rel == "clojure/java/io") then
            print '(A,A,A)', "note: skipping ", rel, &
                 " (JVM-only)"
            ! The namespace exists, empty: require checks that a lib
            ! defined its namespace after loading, and find-ns no
            ! longer creates one on the way to answering.
            block
              character(len=:), allocatable :: nsname
              integer :: ci
              nsname = rel
              do ci = 1, len(nsname)
                 if (nsname(ci:ci) == "/") nsname(ci:ci) = "."
                 if (nsname(ci:ci) == "_") nsname(ci:ci) = "-"
              end do
              call vs_set(vst, base + 2, gcn_find_or_create(nsname, [vs_get(vst, base + 1)]))
            end block
            out = gc_nil()
            call vs_leave(vst, base)
            return
         end if
         ! Two of Rich's files are Clojure written against java.util --
         ! core_print.clj dispatches print-method on Map, Collection, List,
         ! RandomAccess and Set, data.clj extends its protocols to three
         ! of them -- and ClojureScript's answer to both is a version of
         ! its own. So is clotran's: the same file with the JVM keys taken
         ! out, loaded in its place. The vendored file stays, unread.
         ! DEVIATIONS.md 40.
         if (rel == "clojure/core_print") rel = "clotran/core_print"
         if (rel == "clojure/data") rel = "clotran/data"
         fargs = gcv_empty([vs_get(vst, base + 1)])
         fargs = gcv_conj(fargs, gc_str(classpath_find(rel), &
              [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, fargs)
         ! *ns* is SAVED AND RESTORED around the load, as RT.load
         ! does by pushing CURRENT_NS. Without it a loaded file's
         ! own (ns ...) leaks into whatever loaded it, and the next
         ! (load "x") resolves x relative to the wrong namespace.
         call vs_set(vst, base + 3, gcn_current([vs_get(vst, base + 1)]))
         out = call_builtin(B_LOADFILE, vs_get(vst, base + 2))
         call gcn_set_current(vs_get(vst, base + 3))
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
         integer :: from1, hit1, fb
         hay = text_of(gcv_nth(args, 0))
         ned = needle_text(gcv_nth(args, 1))
         from1 = 0
         if (n >= 3) from1 = max(0, int(strip_int(gcv_nth(args, 2))))
         ! indices are characters; the search is over bytes
         fb = u8_off(hay, from1)
         hit1 = 0
         if (fb <= len(hay) .or. len(ned) == 0) &
              hit1 = index(hay(fb:), ned)
         if (hit1 > 0) then
            out = gc_int(u8_cpidx(hay, hit1 + fb - 1))
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
         acc = gcv_empty([vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, acc)
         do j = lo, hi - 1
            acc = gcv_conj(vs_get(vst, base + 2), gcv_nth(src, j), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call vs_set(vst, base + 2, acc)
         end do
         out = vs_get(vst, base + 2)
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
       if (.not. numbers_ok(args, n, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
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
               [vs_get(vst, base + 1)]))
       else if (gc_kind(a) == OBJ_WRITER) then
          write(gc_i1(a), '(A)', advance='no') text_of(gcv_nth(args, 1))
       end if
    case (B_TOSTRING)
       out = gc_str(to_string_text(gcv_nth(args, 0)), [vs_get(vst, base + 1)])
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
          if (gc_ref_is(a%ref, "line.separator")) out = gc_str(achar(10), [vs_get(vst, base + 1)])
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
             call vs_set(vst, base + 2, a)
             b = apply(gc_slot(vs_get(vst, base + 2), 1), &
                  gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)]))
             if (tctx%has_error) then
                ! A DELAY THAT THREW STAYS THROWN, with the SAME
                ! exception object every time -- Delay.deref
                ! catches the throwable, drops the thunk and
                ! rethrows what it caught on every later deref.
                ! Letting the error escape without recording it
                ! meant the body RAN AGAIN, which is observable
                ! whenever it has an effect, and made
                ! (identical? r (deref-again)) false.
                call gc_set_slot(vs_get(vst, base + 2), 2, thrown_value())
                call gc_set_slot(vs_get(vst, base + 2), 3, &
                     gc_str(gce_error(), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
                call gc_set_i1(vs_get(vst, base + 2), 2)
                call vs_leave(vst, base)
                return
             end if
             call gc_set_slot(vs_get(vst, base + 2), 2, b)
             call gc_set_i1(vs_get(vst, base + 2), 1)
             a = vs_get(vst, base + 2)
          end if
          if (gc_i1(a) == 2) then
             call set_thrown(gc_slot(a, 2))
             call fail(text_of(gc_slot(a, 3)))
             call vs_leave(vst, base)
             return
          end if
          out = gc_slot(a, 2)
       else if (gcn_is_var(a) .or. gc_kind(a) == OBJ_ATOM .or. gc_kind(a) == OBJ_VOLATILE) then
          out = gc_slot(a, 1)
       else if (is_reduced(a)) then
          ! Unwrapping a (reduced x) is a deref in Clojure too.
          out = gca_get(a, gc_key("clotran/reduced", [vs_get(vst, base + 1)]))
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
               gcv_nth(args, 2), [vs_get(vst, base + 1)]))
          call mf_reset_cache(a)
       end if
    case (B_METHODTABLE)
       a = gcv_nth(args, 0)
       out = gca_empty([vs_get(vst, base + 1)])
       if (gc_kind(a) == OBJ_MULTIFN) out = gc_slot(a, 4)
    case (B_REMOVEMETHOD)
       ! Mutates and answers the multimethod, the mirror of
       ! addMethod.
       a = gcv_nth(args, 0)
       out = a
       if (gc_kind(a) == OBJ_MULTIFN) then
          call gc_set_slot(a, 4, gca_dissoc(gc_slot(a, 4), gcv_nth(args, 1), &
               [vs_get(vst, base + 1)]))
          call mf_reset_cache(a)
       end if
    case (B_MATH0 + 1 : B_MATH0 + B_MATHN)
       out = math_call(id - B_MATH0, args, [vs_get(vst, base + 1)])
    case (B_FORMAT)
       ! (String/format fmt (to-array args)) -- the arguments
       ! arrive as one ARRAY, not spread.
       block
         type(gc_value) :: fv, av
         fv = strip_meta(gcv_nth(args, 0))
         if (fv%tag /= GCT_STR) then
            call fail("format: first argument must be a string")
         else
            av = gcv_empty([vs_get(vst, base + 1)])
            if (n >= 2) av = coll_to_vector(gcv_nth(args, 1), [vs_get(vst, base + 1)])
            call vs_set(vst, base + 2, av)
            out = gc_str(java_format(gc_ref_text(fv%ref), vs_get(vst, base + 2)), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2)])
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
                    [vs_get(vst, base + 1)]))
            else if (gc_kind(w) == OBJ_WRITER) then
               write(gc_i1(w), '(A)', advance='no') txt
            end if
         end if
       end block
    case (B_SETVALIDATOR, B_GETVALIDATOR)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (id == B_GETVALIDATOR) then
          out = ref_fn_get(a, "validator", [vs_get(vst, base + 1)])
       else
          ! Clojure VALIDATES THE CURRENT VALUE on the way in and
          ! refuses a validator the state already fails.
          if (validate_ref(a, gcv_nth(args, 1), gc_slot(a, 1), &
               [vs_get(vst, base + 1)])) call ref_fn_put(a, "validator", &
               gcv_nth(args, 1), [vs_get(vst, base + 1)])
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
    case (B_CAS)
       ! Atom.compareAndSet: the new value goes in only if the current
       ! one is IDENTICAL to the old -- the same slot, or the same
       ! immediate -- which is how a promise delivers exactly once.
       a = strip_meta(gcv_nth(args, 0))
       out = gc_bool(.false.)
       if (gc_kind(a) == OBJ_ATOM .and. n >= 3) then
          b = gc_slot(a, 1)
          if (same_object(b, gcv_nth(args, 1))) then
             call gc_set_slot(a, 1, gcv_nth(args, 2))
             call notify_watches(a, b, gcv_nth(args, 2), [vs_get(vst, base + 1)])
             out = gc_bool(.true.)
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
             call ref_fn_put(a, "error-handler", gcv_nth(args, 1), [vs_get(vst, base + 1)])
          end if
       end if
    case (B_GETERRMODE, B_GETERRHANDLER, B_AGENTERROR)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gc_kind(a) == OBJ_ATOM) then
          select case (id)
          case (B_GETERRMODE);    out = gc_slot(a, 3)
          case (B_GETERRHANDLER); out = ref_fn_get(a, "error-handler", [vs_get(vst, base + 1)])
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
                 "Agent is failed, needs restart", [vs_get(vst, base + 1)])
         else
            call vs_set(vst, base + 2, ag)
            fargs = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
            fargs = gcv_conj(fargs, gc_slot(vs_get(vst, base + 2), 1), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2)])
            call vs_set(vst, base + 3, fargs)
            block
              type(gc_value) :: extra
              extra = coll_to_vector(gcv_nth(args, 2), &
                   [vs_get(vst, base + 1), vs_get(vst, base + 3)])
              call vs_set(vst, base + 4, extra)
              do j = 0, gcv_count(vs_get(vst, base + 4)) - 1
                 fargs = gcv_conj(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 4), j), &
                      [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
                 call vs_set(vst, base + 3, fargs)
              end do
            end block
            res = apply(gcv_nth(args, 1), vs_get(vst, base + 3))
            if (tctx%has_error) then
               call gc_set_slot(vs_get(vst, base + 2), 5, thrown_value())
               hnd = ref_fn_get(vs_get(vst, base + 2), "error-handler", [vs_get(vst, base + 1)])
               call gce_clear_error()
               if (hnd%tag /= GCT_NIL) then
                  fargs = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
                  fargs = gcv_conj(fargs, vs_get(vst, base + 2), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                  call vs_set(vst, base + 3, fargs)
                  fargs = gcv_conj(vs_get(vst, base + 3), &
                       gc_slot(vs_get(vst, base + 2), 5), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
                  call vs_set(vst, base + 3, fargs)
                  res = apply(hnd, vs_get(vst, base + 3))
                  call gce_clear_error()
               end if
               ! :continue forgets the failure; :fail keeps it.
               if (.not. gc_equal(gc_slot(vs_get(vst, base + 2), 3), &
                    gc_key("fail", [vs_get(vst, base + 1)]))) &
                    call gc_set_slot(vs_get(vst, base + 2), 5, gc_nil())
            else if (.not. validate_ref(vs_get(vst, base + 2), &
                 ref_fn_get(vs_get(vst, base + 2), "validator", [vs_get(vst, base + 1)]), &
                 res, [vs_get(vst, base + 1)])) then
               ! A REJECTED STATE IS AN AGENT ERROR, handled the
               ! same way a thrown action is.
               call gc_set_slot(vs_get(vst, base + 2), 5, thrown_value())
               call gce_clear_error()
               if (.not. gc_equal(gc_slot(vs_get(vst, base + 2), 3), &
                    gc_key("fail", [vs_get(vst, base + 1)]))) &
                    call gc_set_slot(vs_get(vst, base + 2), 5, gc_nil())
            else
               call gc_set_slot(vs_get(vst, base + 2), 1, res)
            end if
            out = vs_get(vst, base + 2)
         end if
       end block
    case (B_GETIFACES)
       block
         type(gc_value) :: cv, acc, sk
         integer :: si2
         cv = strip_meta(gcv_nth(args, 0))
         acc = gcv_empty([vs_get(vst, base + 1)])
         call vs_set(vst, base + 2, acc)
         do si2 = 1, 24
            sk = host_super(cv, si2, vs_get(vst, base + 1))
            if (sk%tag == GCT_NIL) exit
            acc = gcv_conj(vs_get(vst, base + 2), sk, &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), sk])
            call vs_set(vst, base + 2, acc)
         end do
         ! an INTERFACE: what it extends (iface_supers), so that parents
         ! and bases of one are not empty
         if (gcv_count(vs_get(vst, base + 2)) == 0 .and. cv%tag == GCT_CLASS) then
            block
              character(len=:), allocatable :: list
              integer :: p, q
              list = iface_supers(gc_ref_text(cv%ref))
              p = 2
              do while (p <= len(list))
                 q = index(list(p:), " ")
                 if (q == 0) exit
                 if (q > 1) then
                    sk = gc_class(list(p:p+q-2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                    acc = gcv_conj(vs_get(vst, base + 2), sk, [vs_get(vst, base + 1), vs_get(vst, base + 2), sk])
                    call vs_set(vst, base + 2, acc)
                 end if
                 p = p + q
              end do
            end block
         end if
         out = vs_get(vst, base + 2)
       end block
    case (B_EMPTYARRAY)
       out = value_array(gcv_empty([vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
    case (B_STACKTRACE)
       ! (.getStackTrace e): the frames e was thrown with; for anything
       ! that is not a Throwable -- (Thread/currentThread) -- the
       ! frames of the call in progress.
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) == OBJ_ERR .and. gcv_is(gc_slot(a, 4))) then
          out = value_array(gc_slot(a, 4), [vs_get(vst, base + 1)])
       else
          call vs_set(vst, base + 2, frames_vec([vs_get(vst, base + 1)]))
          out = value_array(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       end if
    case (B_STE_CLASS, B_STE_METHOD, B_STE_FILE, B_STE_LINE)
       a = strip_meta(gcv_nth(args, 0))
       out = gc_nil()
       if (gca_is(a)) then
          select case (id)
          case (B_STE_CLASS);  out = gca_get(a, gc_key("class", [vs_get(vst, base + 1)]))
          case (B_STE_METHOD); out = gca_get(a, gc_key("method", [vs_get(vst, base + 1)]))
          case (B_STE_FILE);   out = gca_get(a, gc_key("file", [vs_get(vst, base + 1)]))
          case (B_STE_LINE);   out = gca_get(a, gc_key("line", [vs_get(vst, base + 1)]))
          end select
       end if
    case (B_INTOARRAY)
       out = value_array(gcv_nth(args, n - 1), [vs_get(vst, base + 1)])
    case (B_RE_START, B_RE_END)
       ! (.start t) on a THREAD is the task starting; the member name
       ! is shared with a Matcher's group start, and the target says
       ! which is meant.
       if (id == B_RE_START .and. gc_kind(strip_meta(gcv_nth(args, 0))) == OBJ_CLOSURE) then
          out = task_submit(strip_meta(gcv_nth(args, 0)))
          call vs_leave(vst, base)
          return
       end if
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
                 id == B_RE_REPLACEFIRST, [vs_get(vst, base + 1)])
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
                 rx = gc_obj(OBJ_REGEX, [gc_str(text_of(gcv_nth(args, 1)), [vs_get(vst, base + 1)])], [vs_get(vst, base + 1)])
                 call gc_set_i1(rx, h)
                 call vs_set(vst, base + 2, rx)
                 mh = regex_clone(h)
                 stext = text_of(mt)
                 if (mh == 0) then
                    call fail("regex: " // regex_last_error())
                 else if (.not. regex_set_text(mh, stext)) then
                    call fail("regex: " // regex_last_error())
                 else
                    mv = gc_obj(OBJ_MATCHER, [vs_get(vst, base + 2), gc_str(stext, [vs_get(vst, base + 1), vs_get(vst, base + 2)])], &
                         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                    call gc_set_i1(mv, mh)
                    call vs_set(vst, base + 3, mv)
                    out = regex_replace(vs_get(vst, base + 3), text_of(gcv_nth(args, 2)), &
                         id == B_RE_REPLACEFIRST, [vs_get(vst, base + 1)])
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
               piece = subj(u8_off(subj, apos):)
            else if (regex_group_span(mh2, 0, gs2, ge2)) then
               piece = u8_slice(subj, apos, gs2) // &
                    expand_replacement(text_of(gcv_nth(args, 2)), mh2, subj)
               call gc_set_i2(mt, ge2)
            else
               piece = ""
            end if
            if (gc_kind(bufv) == OBJ_SB) then
               call gc_set_slot(bufv, 1, gc_str( &
                    text_of(gc_slot(bufv, 1)) // piece, [vs_get(vst, base + 1)]))
            end if
         end if
       end block
    case (B_RE_SPLIT)
       block
         type(gc_value) :: pv, sv, lv
         integer :: lim
         pv = strip_meta(gcv_nth(args, 0))
         sv = strip_meta(gcv_nth(args, 1))
         if (sv%tag == GCT_NIL) then
            call raise_class("NullPointerException", "split of nil", [vs_get(vst, base + 1)])
            call vs_leave(vst, base)
            return
         end if
         lim = 0
         if (n >= 3) then
            lv = strip_meta(gcv_nth(args, 2))
            lim = int(lv%ival)
         end if
         if (gc_kind(pv) == OBJ_REGEX) then
            out = regex_split(pv, sv, lim, [vs_get(vst, base + 1)])
         else if (pv%tag == GCT_STR .and. sv%tag == GCT_STR) then
            ! String.split(regex[, limit]): the string is the subject and
            ! the second argument is a pattern SOURCE, compiled here as
            ! Java compiles it on every call.
            call vs_set(vst, base + 2, pv)
            block
              type(gc_value) :: rx
              integer :: h
              h = regex_compile(text_of(sv))
              if (h == 0) then
                 call fail("regex: " // regex_last_error())
              else
                 rx = gc_obj(OBJ_REGEX, [gc_str(text_of(sv), [vs_get(vst, base + 1)])], [vs_get(vst, base + 1)])
                 call gc_set_i1(rx, h)
                 call vs_set(vst, base + 3, rx)
                 out = regex_split(vs_get(vst, base + 3), vs_get(vst, base + 2), lim, [vs_get(vst, base + 1)])
              end if
            end block
         else
            call fail("split needs a Pattern")
         end if
       end block
    case (B_QUOTEREPL)
       out = gc_str(quote_replacement(text_of(gcv_nth(args, 0))), &
            [vs_get(vst, base + 1)])
    case (B_SBREVERSE)
       ! Mutates and returns the builder, like append.
       block
         character(len=:), allocatable :: bt, rt
         integer :: bi
         a = gcv_nth(args, 0)
         out = a
         bt = text_of(a)
         rt = ""
         do bi = u8_count(bt) - 1, 0, -1
            rt = rt // u8_slice(bt, bi, bi + 1)
         end do
         if (gc_kind(a) == OBJ_SB) then
            call gc_set_slot(a, 1, gc_str(rt, [vs_get(vst, base + 1)]))
         else
            out = gc_str(rt, [vs_get(vst, base + 1)])
         end if
       end block
    case (B_READSTRING)
       block
         type(gc_value) :: sv
         sv = strip_meta(gcv_nth(args, 0))
         if (sv%tag /= GCT_STR) then
            call fail("read-string wants a string")
         else
            out = gcr_read(gc_ref_text(sv%ref), [vs_get(vst, base + 1)])
            if (gcr_has_error()) call fail(gcr_error())
         end if
       end block
    case (B_NUMCOMPARE)
       ! Double.compare's total order, which the host table reaches as
       ! Double/compare (clojure.math's neg-zero? is written on it). -0.0 < 0.0, and NaN is
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
       out = gca_empty([vs_get(vst, base + 1)])
    case (B_GETMETHOD)
       ! what WOULD apply: the same lookup a call makes, default included
       a = gcv_nth(args, 0)
       out = gc_nil()
       if (gc_kind(a) == OBJ_MULTIFN) then
          out = mf_lookup(a, gcv_nth(args, 1), [vs_get(vst, base + 1)])
       end if
    case (B_PREFERMETHOD)
       ! MultiFn.preferMethod, the table update in clotran.rt
       a = gcv_nth(args, 0)
       out = a
       if (gc_kind(a) == OBJ_MULTIFN) then
          block
            type(gc_value) :: fargs, pt
            call vs_set(vst, base + 2, a)
            fargs = gcv_build(5, [vs_get(vst, base + 1)])
            call vs_set(vst, base + 3, fargs)
            fargs = gcv_put(vs_get(vst, base + 3), 0, gc_slot(vs_get(vst, base + 2), 1), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, fargs)
            fargs = gcv_put(vs_get(vst, base + 3), 1, mf_aux(vs_get(vst, base + 2), 1), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, fargs)
            pt = mf_hierarchy(vs_get(vst, base + 2))
            call vs_set(vst, base + 4, pt)
            fargs = gcv_put(vs_get(vst, base + 3), 2, vs_get(vst, base + 4), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, fargs)
            fargs = gcv_put(vs_get(vst, base + 3), 3, gcv_nth(args, 1), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, fargs)
            fargs = gcv_put(vs_get(vst, base + 3), 4, gcv_nth(args, 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, fargs)
            pt = mf_call("prefer", vs_get(vst, base + 3))
            if (.not. tctx%has_error) then
               call mf_aux_set(vs_get(vst, base + 2), 1, pt)
               call mf_reset_cache(vs_get(vst, base + 2))
            end if
            out = vs_get(vst, base + 2)
          end block
       end if
    case (B_PREFERTABLE)
       a = gcv_nth(args, 0)
       out = gca_empty([vs_get(vst, base + 1)])
       if (gc_kind(a) == OBJ_MULTIFN) out = mf_aux(a, 1)
    case (B_DISPATCHFN)
       a = gcv_nth(args, 0)
       out = gc_nil()
       if (gc_kind(a) == OBJ_MULTIFN) out = gc_slot(a, 2)
    case (B_PKGFN)
       ! (fortran/load-package path): clotran.package makes the fns
       out = rt_call_in("clotran/package", "clotran.package", pk_loaded, "load-package", args)
    case (B_PKGLOAD)
       ! (load-package* path): the library opened, its manifest read by
       ! clotran's own reader, {:handle n :manifest m} answered
       block
         character(len=:), allocatable :: path, text
         type(c_ptr) :: h
         type(gc_value) :: m, res, k
         type(c_ptr), allocatable :: grown(:)
         path = pkg_library(text_of(gcv_nth(args, 0)))
         if (tctx%has_error) then
            call vs_leave(vst, base)
            return
         end if
         h = dl_open(path)
         if (.not. c_associated(h)) then
            call fail("load-package: " // path // ": " // dl_error())
         else
            text = dl_manifest(h)
            if (len(text) == 0) then
               call fail("load-package: " // path // " exports no clotran_manifest")
            else
               m = gcr_read(text, [vs_get(vst, base + 1)])
               if (gcr_has_error()) then
                  call fail("load-package: " // path // ": manifest: " // gcr_error())
               else
                  call vs_set(vst, base + 2, m)
                  if (.not. allocated(pkg_handles)) allocate(pkg_handles(8))
                  if (pkg_count >= size(pkg_handles)) then
                     allocate(grown(2 * size(pkg_handles)))
                     grown(1:pkg_count) = pkg_handles(1:pkg_count)
                     call move_alloc(grown, pkg_handles)
                  end if
                  pkg_count = pkg_count + 1
                  pkg_handles(pkg_count) = h
                  res = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
                  call vs_set(vst, base + 3, res)
                  k = gc_key("handle", [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
                  call vs_set(vst, base + 4, k)
                  res = gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 4), gc_int(int(pkg_count, gc_ip)), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
                  call vs_set(vst, base + 3, res)
                  k = gc_key("manifest", [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
                  call vs_set(vst, base + 4, k)
                  res = gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 2), &
                       [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
                  out = res
               end if
            end if
         end if
       end block
    case (B_PKGCALL)
       out = pkg_call(gcv_nth(args, 0), gcv_nth(args, 1), gcv_nth(args, 2), [vs_get(vst, base + 1)])
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
       if (.not. numbers_ok(args, n, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
       ! There IS a Ratio now, so an inexact integer division is no
       ! longer approximated with a double: (/ 1 3) is 1/3.
       !
       ! Contagion again -- a double anywhere makes the answer a
       ! double, and otherwise the result stays exact. Dividing by a
       ! ratio multiplies by its reciprocal.
       a = strip_meta(gcv_nth(args, 0)); b = strip_meta(gcv_nth(args, 1))
       ! A decimal divides EXACTLY or not at all: BigDecimal.divide
       ! with no MathContext throws on a non-terminating expansion
       ! rather than rounding, and there is no with-precision here to
       ! say otherwise (DEVIATIONS 30).
       if ((a%tag == GCT_DEC .or. b%tag == GCT_DEC) .and. &
            exact_num(a) .and. exact_num(b)) then
          block
            character(len=:), allocatable :: dq
            logical :: dok
            integer :: mcp, mcm
            if (dec_is_zero(dec_of(b))) then
               call raise_class("ArithmeticException", "Divide by zero", [vs_get(vst, base + 1)])
            else
               ! With a precision the quotient is rounded to it; with
               ! none it is exact or it throws, which is what Java does
               ! outside with-precision.
               call math_context(mcp, mcm)
               if (mcp > 0) then
                  call dec_div_mc(dec_of(a), dec_of(b), mcp, mcm, dq, dok)
               else
                  call dec_div(dec_of(a), dec_of(b), dq, dok)
               end if
               if (dok) then
                  out = gc_dec(dq, [vs_get(vst, base + 1)])
               else if (mcp > 0) then
                  call raise_class("ArithmeticException", "Rounding necessary", [vs_get(vst, base + 1)])
               else
                  call raise_class("ArithmeticException", &
                       "Non-terminating decimal expansion; no exact representable decimal result.", &
                       [vs_get(vst, base + 1)])
               end if
            end if
          end block
          call vs_leave(vst, base)
          return
       end if
       ! Two integrals, one of them a BigInt: exact. It divides evenly
       ! or it is a Ratio -- (/ 4N 2) is 2N and (/ 10N 4) is 5/2 --
       ! and a Ratio's parts are 64-bit, so a remainder past that
       ! range has nowhere to go (DEVIATIONS 26).
       if ((a%tag == GCT_BIG .or. b%tag == GCT_BIG) .and. &
            (a%tag == GCT_BIG .or. a%tag == GCT_INT) .and. (b%tag == GCT_BIG .or. b%tag == GCT_INT)) then
          block
            character(len=:), allocatable :: bq, br
            if (big_of(b) == "0") then
               call raise_class("ArithmeticException", "Divide by zero", [vs_get(vst, base + 1)])
            else
               call big_divmod(big_of(a), big_of(b), bq, br)
               if (br == "0") then
                  out = gc_big(bq, [vs_get(vst, base + 1)])
               else if (big_fits_i64(big_of(a)) .and. big_fits_i64(big_of(b))) then
                  out = gc_ratio(big_to_i64(big_of(a)), big_to_i64(big_of(b)))
               else
                  call raise_class("ArithmeticException", &
                       "a Ratio of BigInts is not supported (DEVIATIONS 26)", [vs_get(vst, base + 1)])
               end if
            end if
          end block
          call vs_leave(vst, base)
          return
       end if
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
               call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
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
          call raise_class("ArithmeticException", "Divide by zero", [gc_nil()])
       else
          out = gc_ratio(gc_numerator(a) * gc_denominator(b), &
                         gc_denominator(a) * gc_numerator(b))
       end if
    case (B_INC, B_DEC, B_UINC, B_UDEC, B_PINC, B_PDEC)
       checked = (id == B_INC .or. id == B_DEC)
       op = id
       if (id == B_UINC .or. id == B_PINC) op = B_INC
       if (id == B_UDEC .or. id == B_PDEC) op = B_DEC
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_DEC) then
          if (op == B_INC) then
             out = gc_dec(dec_add(gc_dec_text(a), dec_from_big("1")), [vs_get(vst, base + 1)])
          else
             out = gc_dec(dec_sub(gc_dec_text(a), dec_from_big("1")), [vs_get(vst, base + 1)])
          end if
          call vs_leave(vst, base)
          return
       end if
       ! A BigInt counts exactly, and inc'/dec' promote rather than
       ! throw at the edge of the 64-bit range.
       if (a%tag == GCT_BIG .or. ((id == B_PINC .or. id == B_PDEC) .and. a%tag == GCT_INT)) then
          block
            character(len=:), allocatable :: bt
            if (op == B_INC) then
               bt = big_add(big_of(a), "1")
            else
               bt = big_sub(big_of(a), "1")
            end if
            if (a%tag /= GCT_BIG .and. big_fits_i64(bt)) then
               out = gc_int(big_to_i64(bt))
            else
               out = gc_big(bt, [vs_get(vst, base + 1)])
            end if
          end block
          call vs_leave(vst, base)
          return
       end if
       if (.not. numbers_ok(args, 1, [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
       if (a%tag == GCT_INT .and. checked) then
          if ((op == B_INC .and. a%ival == huge(a%ival)) .or. &
               (op == B_DEC .and. a%ival == -huge(a%ival) - 1_gc_ip)) then
             call raise_class("ArithmeticException", "long overflow", [vs_get(vst, base + 1)])
             call vs_leave(vst, base)
             return
          end if
       end if
       if (is_ratio(a)) then
          ! (inc 1/2) is 3/2, not 1.5 -- the else branch below sends
          ! everything that is not an integer through num_dbl, which
          ! would silently drop a ratio to a double.
          if (op == B_INC) then
             out = gc_ratio(gc_numerator(a) + gc_denominator(a), gc_denominator(a))
          else
             out = gc_ratio(gc_numerator(a) - gc_denominator(a), gc_denominator(a))
          end if
       else if (a%tag == GCT_INT) then
          if (op == B_INC) then
             out = gc_int(a%ival + 1)
          else
             out = gc_int(a%ival - 1)
          end if
       else
          if (op == B_INC) then
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
            ! what the JVM throws when neither is Comparable to the other
            call raise_class("ClassCastException", "compare: cannot compare " // &
                 type_name(strip_meta(gcv_nth(args, 0))) // " with " // &
                 type_name(strip_meta(gcv_nth(args, 1))), [vs_get(vst, base + 1)])
         end if
       end block
    case (B_DISJ)
       ! A set is a map to itself, so disj is dissoc on the backing map.
       block
         type(gc_value) :: st
         st = strip_meta(gcv_nth(args, 0))
         if (gc_kind(st) == OBJ_SET) then
            out = gc_obj(OBJ_SET, &
                 [gca_dissoc(gc_slot(st, 1), gcv_nth(args, 1), [vs_get(vst, base + 1)])], &
                 [vs_get(vst, base + 1)])
            out = keep_meta(gcv_nth(args, 0), out, [vs_get(vst, base + 1)])
         else
            out = gcv_nth(args, 0)
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
               call vs_set(vst, base + 2, a)
               bigger = gc_vec(max(2 * cnt, 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
               do k = 1, cnt
                  call gc_vec_set(bigger, k, gc_vec_get(gc_slot(vs_get(vst, base + 2), 1), k))
               end do
               call gc_set_slot(vs_get(vst, base + 2), 1, bigger)
               a = vs_get(vst, base + 2)
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
          out = make_chunk(gc_slot(a, 1), 0, gc_i1(a), [vs_get(vst, base + 1)])
       end if
    case (B_CHUNK_FIRST, B_CHUNK_MORE, B_CHUNK_NEXT)
       block
         type(gc_value) :: ch, mo
         a = strip_meta(gcv_nth(args, 0))
         if (.not. is_chunked_seq(a)) then
            call fail("no such member: " // class_name_of(a) // ".chunkedFirst")
         else
            call chunked_parts(a, ch, mo, [vs_get(vst, base + 1)])
            if (id == B_CHUNK_FIRST) then
               out = ch
            else if (id == B_CHUNK_MORE) then
               out = mo
               if (out%tag == GCT_NIL) out = gcl_empty([vs_get(vst, base + 1)])
            else
               call vs_set(vst, base + 2, mo)
               out = to_seq(vs_get(vst, base + 2), [vs_get(vst, base + 1)])
            end if
         end if
       end block
    case (B_CHUNK_DROP)
       a = strip_meta(gcv_nth(args, 0))
       if (gc_kind(a) /= OBJ_CHUNK) then
          call fail("no such member: " // class_name_of(a) // ".dropFirst")
       else
          out = make_chunk(gc_slot(a, 1), gc_i1(a) + 1, gc_i2(a), [vs_get(vst, base + 1)])
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
       ! (class x): the class, spelt canonically, nil for nil.
       a = strip_meta(gcv_nth(args, 0))
       if (a%tag == GCT_NIL) then
          out = gc_nil()
       else
          out = gc_class(class_name_of(a), [vs_get(vst, base + 1)])
       end if
    case (B_TYPE)
       ! One host primitive instead of a dozen predicates: core is
       ! written in Clojure on top of this, which is how real Clojure
       ! does it too (instance? plus defns).
       a = gcv_nth(args, 0)
       out = gc_key(type_name(a), [vs_get(vst, base + 1)])
    case (B_CONCAT)
       ! Right to left, so the result comes out in order without a
       ! reverse. Every argument is seq'd to a list first, which is
       ! what lets (concat [1 2] (list 3)) work.
       out = gcl_empty([vs_get(vst, base + 1)])
       do i = n - 1, 0, -1
          block
            type(gc_value) :: piece
            integer :: j
            piece = as_list(gcv_nth(vs_get(vst, base + 1), i), [vs_get(vst, base + 1), out])
            do j = gcl_count(piece) - 1, 0, -1
               out = gcl_cons(nth_of(piece, j), out, [vs_get(vst, base + 1), piece])
            end do
          end block
       end do
    end select

    call vs_leave(vst, base)
  end function call_builtin

  ! A list view of a value: lists pass through, vectors are copied
  ! into one, nil is the empty list. Enough for cons/concat and for
  ! quasiquote's splicing; a real seq abstraction is a later feature.
  function as_list(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i

    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, v)
    if (gcl_is(v)) then
       out = v
       call vs_leave(vst, base)
       return
    end if
    out = gcl_empty(roots)
    call vs_set(vst, base + 2, out)
    if (gcv_is(v)) then
       do i = gcv_count(vs_get(vst, base + 1)) - 1, 0, -1
          out = gcl_cons(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2), &
               [vs_get(vst, base + 1)])
          call vs_set(vst, base + 2, out)
       end do
    end if
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function as_list

  ! The nth element of a list, by walking. Only used where the list is
  ! already in hand and short.
  function nth_of(l, i) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: l
    integer, intent(in) :: i
    type(gc_value) :: out, walk
    integer :: base, k

    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, l)
    walk = l
    call vs_set(vst, base + 2, walk)
    do k = 1, i
       walk = gcl_rest(vs_get(vst, base + 2), [vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, walk)
    end do
    out = gcl_first(vs_get(vst, base + 2))
    call vs_leave(vst, base)
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

    ! Util.compare answers 0 for an object against itself, and Clojure's
    ! empty collections are singletons: (compare {} {}) is 0 there, and
    ! (compare {:a 1} {:a 1}) throws.
    if (same_object(a, b)) then
       c = 0
       return
    end if
    if (gc_kind(a) == gc_kind(b) .and. empty_coll(a) .and. empty_coll(b)) then
       c = 0
       return
    end if
    ok = .false.
  end function compare_values

  ! An empty map, set or list.
  function empty_coll(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = .false.
    if (gca_is(v)) then
       yes = gca_count(v) == 0
    else if (gc_kind(v) == OBJ_SET) then
       yes = gca_count(gc_slot(v, 1)) == 0
    else if (gcl_is(v)) then
       yes = gcl_count(v) == 0
    end if
  end function empty_coll

  ! Long addition would overflow: by range, before the add.
  function add_overflows(a, b) result(bad)
    integer(gc_ip), intent(in) :: a, b
    logical :: bad
    bad = (b > 0 .and. a > huge(a) - b) .or. (b < 0 .and. a < -huge(a) - 1_gc_ip - b)
  end function add_overflows

  ! A `value`-kind array holding a collection's elements. This is what
  ! to-array answers, because `sort` mutates the array it gets.
  function value_array_of(coll, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: coll
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, vecd, run
    integer, allocatable :: ext(:), lows(:)
    character(len=:), allocatable :: err
    integer :: n, h, i, base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    vecd = coll_to_vector(coll, roots)
    call vs_set(vst, base + 1, vecd)
    n = gcv_count(vs_get(vst, base + 1))
    allocate(ext(1), lows(1))
    ext(1) = n
    lows(1) = 0
    h = gcna_new("value", ext, lows, err)
    if (h == 0) then
       call fail(err)
       call vs_leave(vst, base)
       out = gc_nil()
       return
    end if
    run = gc_vec(max(1, n), [roots, [vs_get(vst, base + 1)]])
    call vs_set(vst, base + 2, run)
    out = gc_obj(OBJ_ARRAY, [vs_get(vst, base + 2)], [roots, [vs_get(vst, base + 1), vs_get(vst, base + 2)]])
    call gc_set_i1(out, h)
    call gc_set_i2(out, -1)   ! owns its handle; not a slice
    do i = 1, n
       call array_put(out, i, gcv_nth(vs_get(vst, base + 1), i - 1))
    end do
    call vs_leave(vst, base)
  end function value_array_of

  ! One comparator call, following AFunction.compare (AFunction.java):
  ! a function that answers a BOOLEAN is a predicate, so (sort > coll)
  ! works -- true means "less", and false asks the reverse question to
  ! tell 0 from 1. Anything else is a number and its sign is the answer.
  recursive function comparator_call(cmp, x, y) result(c)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: cmp, x, y
    integer :: c
    type(gc_value) :: r, args2, rev
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, cmp)
    ! A VECTOR, not a list: apply counts its arguments with
    ! gcv_count to pick an arity, and a list counts as zero --
    ! which is how a two-argument comparator produced
    ! "no matching arity".
    !
    ! Each conj is rooted before the next allocation: two
    ! allocations as arguments to one call means the second can
    ! collect the first.
    args2 = gcv_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, args2)
    args2 = gcv_conj(vs_get(vst, base + 2), x, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 2, args2)
    args2 = gcv_conj(vs_get(vst, base + 2), y, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 2, args2)
    r = apply(vs_get(vst, base + 1), vs_get(vst, base + 2))
    call vs_set(vst, base + 3, r)
    c = 0
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    if (r%tag == GCT_BOOL) then
       if (truthy(r)) then
          c = -1
       else
          rev = gcv_empty([vs_get(vst, base + 1)])
          call vs_set(vst, base + 2, rev)
          rev = gcv_conj(vs_get(vst, base + 2), y, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, rev)
          rev = gcv_conj(vs_get(vst, base + 2), x, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, rev)
          r = apply(vs_get(vst, base + 1), vs_get(vst, base + 2))
          if (.not. tctx%has_error) then
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
    call vs_leave(vst, base)
  end function comparator_call

  ! java.util.Arrays/sort -- IN PLACE, and STABLE, which Clojure's sort
  ! docstring promises: "equal elements will not be reordered". A
  ! merge sort rather than a quicksort for exactly that reason; the
  ! extra array is the price of the guarantee.
  recursive subroutine array_sort(arr, cmp)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: arr, cmp
    integer :: n, width, i, lo, mid, hi
    type(gc_value), allocatable :: buf(:), src(:)
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    n = seq_len(arr)
    if (n < 2) return
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, arr)
    call vs_set(vst, base + 2, cmp)
    allocate(src(n), buf(n))
    do i = 1, n
       src(i) = array_elem(vs_get(vst, base + 1), i)
    end do
    ! Bottom-up: merge runs of 1, then 2, then 4... Taking from the
    ! left run on a tie is what keeps it stable.
    width = 1
    do while (width < n)
       lo = 1
       do while (lo <= n)
          mid = min(lo + width - 1, n)
          hi = min(lo + 2 * width - 1, n)
          call merge_run(src, buf, lo, mid, hi, vs_get(vst, base + 2))
          if (tctx%has_error) then
             call vs_leave(vst, base)
             return
          end if
          lo = hi + 1
       end do
       src = buf
       width = 2 * width
    end do
    do i = 1, n
       call array_put(vs_get(vst, base + 1), i, src(i))
    end do
    call vs_leave(vst, base)
  end subroutine array_sort

  recursive subroutine merge_run(src, buf, lo, mid, hi, cmp)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: src(:)
    type(gc_value), intent(inout) :: buf(:)
    integer, intent(in) :: lo, mid, hi
    type(gc_value), intent(in) :: cmp
    integer :: i, j, k
    tctx => ctx_self()
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
       if (tctx%has_error) return
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: basis
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, tmp
    integer :: i, base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, basis)
    tmp = gca_empty([roots, [basis]])
    call vs_set(vst, base + 2, tmp)
    do i = 0, gcv_count(vs_get(vst, base + 1)) - 1
       tmp = gca_assoc(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), gc_nil(), &
            [roots, [vs_get(vst, base + 1), vs_get(vst, base + 2)]])
       call vs_set(vst, base + 2, tmp)
    end do
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function struct_blank

  ! construct: the values positionally against the basis.
  function struct_construct(args, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, basis, vals, tmp
    integer :: i, n, base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    basis = strip_meta(gcv_nth(args, 0))
    call vs_set(vst, base + 1, basis)
    vals = coll_to_vector(gcv_nth(args, 1), [roots, [basis]])
    call vs_set(vst, base + 2, vals)
    n = gcv_count(vs_get(vst, base + 2))
    if (n > gcv_count(vs_get(vst, base + 1))) then
       call fail("Too many arguments to struct constructor")
       call vs_leave(vst, base)
       out = gc_nil()
       return
    end if
    tmp = struct_blank(vs_get(vst, base + 1), [roots, [vs_get(vst, base + 2)]])
    call vs_set(vst, base + 3, tmp)
    do i = 0, n - 1
       tmp = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 1), i), &
            gcv_nth(vs_get(vst, base + 2), i), &
            [roots, [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]])
       call vs_set(vst, base + 3, tmp)
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
  end function struct_construct

  ! create: key/value pairs, which may name keys outside the basis.
  function struct_create(args, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: args
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, basis, kvs, tmp
    integer :: i, n, base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    basis = strip_meta(gcv_nth(args, 0))
    call vs_set(vst, base + 1, basis)
    kvs = coll_to_vector(gcv_nth(args, 1), [roots, [basis]])
    call vs_set(vst, base + 2, kvs)
    n = gcv_count(vs_get(vst, base + 2))
    if (mod(n, 2) /= 0) then
       call fail("No value supplied for key: " // &
            gcp_str(gcv_nth(vs_get(vst, base + 2), n - 1), .true.))
       call vs_leave(vst, base)
       out = gc_nil()
       return
    end if
    tmp = struct_blank(vs_get(vst, base + 1), [roots, [vs_get(vst, base + 2)]])
    call vs_set(vst, base + 3, tmp)
    do i = 0, n - 2, 2
       tmp = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i), &
            gcv_nth(vs_get(vst, base + 2), i + 1), &
            [roots, [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]])
       call vs_set(vst, base + 3, tmp)
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
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
    type(gc_stack), pointer :: vst
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
    vst => gc_my_stack()
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
    if ((sequential_p(a) .and. sequential_p(b)) .or. seq_inst_pair(a, b)) then
       if (counted_p(a) .and. counted_p(b)) then
          if (seq_count(a) /= seq_count(b)) then
             eq = .false.
             return
          end if
       end if
       block
         type(gc_value) :: sa, sb, tmp
         integer :: base
         base = vs_enter(vst, 6)
         call vs_set(vst, base + 1, a)
         call vs_set(vst, base + 2, b)
         tmp = to_seq(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, tmp)
         tmp = to_seq(vs_get(vst, base + 2), [vs_get(vst, base + 2), vs_get(vst, base + 3)])
         call vs_set(vst, base + 4, tmp)
         eq = .false.
         do
            sa = vs_get(vst, base + 3)
            sb = vs_get(vst, base + 4)
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
            tmp = sq_first(vs_get(vst, base + 3), [vs_get(vst, base + 3), vs_get(vst, base + 4)])
            call vs_set(vst, base + 5, tmp)
            tmp = sq_first(vs_get(vst, base + 4), &
                 [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
            call vs_set(vst, base + 6, tmp)
            if (.not. deep_equal(vs_get(vst, base + 5), vs_get(vst, base + 6), &
                 [vs_get(vst, base + 3), vs_get(vst, base + 4)])) exit

            tmp = sq_rest(vs_get(vst, base + 3), [vs_get(vst, base + 3), vs_get(vst, base + 4)])
            call vs_set(vst, base + 5, tmp)
            tmp = to_seq(vs_get(vst, base + 5), [vs_get(vst, base + 4), vs_get(vst, base + 5)])
            call vs_set(vst, base + 3, tmp)
            tmp = sq_rest(vs_get(vst, base + 4), [vs_get(vst, base + 3), vs_get(vst, base + 4)])
            call vs_set(vst, base + 6, tmp)
            tmp = to_seq(vs_get(vst, base + 6), [vs_get(vst, base + 3), vs_get(vst, base + 6)])
            call vs_set(vst, base + 4, tmp)
         end do
         call vs_leave(vst, base)
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
  ! A deftype that answers seq -- an Eduction -- is Sequential, and a
  ! vector, list or seq equals it element by element. Two such
  ! instances are NOT equal to each other: Eduction keeps Object's
  ! identity equals, and so the pair is one instance and one sequence.
  function seq_inst_pair(a, b) result(yes)
    type(gc_value), intent(in) :: a, b
    logical :: yes
    yes = .false.
    if (gc_kind(a) == OBJ_INST .and. sequential_p(b)) then
       yes = (gc_kind(inst_method(a, "seq")) == OBJ_CLOSURE) .or. (gc_kind(inst_method(a, "iterator")) == OBJ_CLOSURE)
    else if (gc_kind(b) == OBJ_INST .and. sequential_p(a)) then
       yes = (gc_kind(inst_method(b, "seq")) == OBJ_CLOSURE) .or. (gc_kind(inst_method(b, "iterator")) == OBJ_CLOSURE)
    end if
  end function seq_inst_pair

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
  ! (cons head tl) as B_CONS builds it: a list tail stays a list, any
  ! other tail -- lazy, unrealised -- is kept as it is under a cell.
  recursive function seq_cons(head, tl0, roots) result(out)
    type(gc_value), intent(in) :: head, tl0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, tl
    tl = tl0
    if (gc_kind(tl) /= OBJ_LAZY .and. tl%tag /= GCT_NIL) tl = to_seq(tl, [roots, head])
    if (tl%tag == GCT_NIL) tl = gcl_empty([roots, head])
    if (gcl_is(tl)) then
       out = gcl_cons(head, tl, [roots, head, tl])
    else
       out = gc_obj(OBJ_LAZY, [gc_nil(), head, tl], [roots, head, tl])
       call gc_set_i1(out, LAZY_CONS)
    end if
  end function seq_cons

  recursive function to_seq(v0, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, v
    integer :: base

    vst => gc_my_stack()
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

    ! A deftype that answers seq -- ISeqable, as ClojureScript spells
    ! it; clotran.rt's Eduction does -- is whatever that answers.
    if (gc_kind(v) == OBJ_INST) then
       out = inst_seq(v, roots)
       return
    end if

    ! Indexable: a VIEW, not a copy. rest is then O(1).
    if (seq_len(v) == 0) return
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, v)
    out = gc_obj(OBJ_SEQ, [vs_get(vst, base + 1)], roots)
    call gc_set_i1(out, 0)
    call vs_leave(vst, base)
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
       n = u8_count(gc_ref_text(v%ref))
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base

    vst => gc_my_stack()
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
         if (i >= 0 .and. i < u8_count(t)) out = gc_char_cp(u8_at(t, i))
       end block
    else if (gca_is(v)) then
       call gca_entries(v, ks, vls)
       if (i >= 0 .and. i < size(ks)) then
          base = vs_enter(vst, 1)
          out = gcv_empty(roots)
          call vs_set(vst, base + 1, out)
          out = gcv_conj(vs_get(vst, base + 1), ks(i+1), roots)
          call vs_set(vst, base + 1, out)
          out = gcv_conj(vs_get(vst, base + 1), vls(i+1), roots)
          call mark_entry(out)
          call vs_leave(vst, base)
       end if
    end if
  end function seq_elem

  ! first/rest work on SEQS only. Anything else is seq'd first.
  recursive function sq_first(v0, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, s, v
    integer :: base

    vst => gc_my_stack()
    v = strip_meta(v0)
    out = gc_nil()
    base = vs_enter(vst, 1)
    s = to_seq(v, roots)
    call vs_set(vst, base + 1, s)
    if (gcl_is(vs_get(vst, base + 1))) then
       out = gcl_first(vs_get(vst, base + 1))
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_LAZY) then
       out = gc_slot(vs_get(vst, base + 1), 2)
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_SEQ) then
       out = seq_elem(gc_slot(vs_get(vst, base + 1), 1), gc_i1(vs_get(vst, base + 1)), roots)
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_CHUNKSEQ) then
       out = chunk_nth(gc_slot(vs_get(vst, base + 1), 1), 0)
    end if
    call vs_leave(vst, base)
  end function sq_first

  ! Always a seq, never nil -- Clojure's `rest`, as opposed to `next`.
  ! For a view this bumps the index and shares the source, so walking
  ! a vector is O(1) per step rather than copying the tail each time.
  recursive function sq_rest(v0, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, s, v
    integer :: base

    vst => gc_my_stack()
    v = strip_meta(v0)
    base = vs_enter(vst, 2)
    s = to_seq(v, roots)
    call vs_set(vst, base + 1, s)
    out = gcl_empty(roots)
    if (gcl_is(vs_get(vst, base + 1))) then
       out = gcl_rest(vs_get(vst, base + 1), roots)
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_LAZY) then
       out = gc_slot(vs_get(vst, base + 1), 3)
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_SEQ) then
       out = gc_obj(OBJ_SEQ, [gc_slot(vs_get(vst, base + 1), 1)], &
            [vs_get(vst, base + 1)])
       call gc_set_i1(out, gc_i1(vs_get(vst, base + 1)) + 1)
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_CHUNKSEQ) then
       ! ChunkedCons.more: the chunk less its first while that leaves
       ! any, else what follows (or () when nothing does)
       if (chunk_count(gc_slot(vs_get(vst, base + 1), 1)) > 1) then
          call vs_set(vst, base + 2, make_chunk(gc_slot(gc_slot(vs_get(vst, base + 1), 1), 1), &
               gc_i1(gc_slot(vs_get(vst, base + 1), 1)) + 1, gc_i2(gc_slot(vs_get(vst, base + 1), 1)), [vs_get(vst, base + 1)]))
          out = gc_obj(OBJ_CHUNKSEQ, [vs_get(vst, base + 2), gc_slot(vs_get(vst, base + 1), 2), gc_nil()], &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       else
          out = gc_slot(vs_get(vst, base + 1), 2)
          if (out%tag == GCT_NIL) out = gcl_empty(roots)
       end if
    end if
    call vs_leave(vst, base)
  end function sq_rest

  ! How many elements a seq yields. Realises a lazy seq, as (count)
  ! must.
  recursive function sq_count(v0, roots) result(n)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v0
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: s, v
    integer :: base, n

    vst => gc_my_stack()
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
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, v)
    do
       s = to_seq(vs_get(vst, base + 1), roots)
       call vs_set(vst, base + 1, s)
       ! s, not vs_get(...)%tag: neither compiler will take a
       ! component off a function result (NOTES.md gotcha).
       if (s%tag == GCT_NIL) exit
       n = n + 1
       s = sq_rest(vs_get(vst, base + 1), roots)
       call vs_set(vst, base + 1, s)
    end do
    call vs_leave(vst, base)
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
    case (GCT_CLASS); s = "class"
    case (GCT_DEC);  s = "bigdec"
    case (GCT_BIG);  s = "bigint"
    case (GCT_STR);  s = "string"
    case (GCT_SYM);  s = "symbol"
    case (GCT_KEY);  s = "keyword"
    case default
       select case (gc_kind(v))
       case (OBJ_CONS);    s = "list"
       case (OBJ_VECTOR);  s = "vector"
       case (OBJ_MAP, OBJ_HAMT); s = "map"
       case (OBJ_SET);     s = "set"
       ! A compiled procedure IS a function: fn?, ifn?, the IFn
       ! instance check and everything core does with a callable all
       ! read this name, so leaving it out made a compiled fn an
       ! "object" that map would refuse.
       case (OBJ_CLOSURE, OBJ_BUILTIN, OBJ_COMPILED); s = "fn"
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
       ! An atom names itself here, so the "atom" the IDeref, Atom
       ! and IMeta cases in is_instance already looked for is a name
       ! something actually answers to. Without it an atom was an
       ! "object", which is how (instance? clojure.lang.IMeta (atom 1))
       ! came back false and reset-meta! wrote a slot `meta` never read.
       case (OBJ_ATOM);    s = "atom"
       case (OBJ_DELAY);   s = "delay"
       case (OBJ_VOLATILE); s = "volatile"
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
    ! Class.toString is "class java.lang.Long" while print-method
    ! writes the NAME, so (str Long) and (pr-str Long) differ.
    if (v%tag == GCT_CLASS) then
       s = "class " // gc_class_text(v)
    else if (gc_kind(v) == OBJ_SB .or. gc_kind(v) == OBJ_REGEX .or. &
         gc_kind(v) == OBJ_NS) then
       inner = gc_slot(v, 1)
       s = gcp_str(inner, .false.)
    else if (sequential_p(v) .or. gca_is(strip_meta(v)) .or. gc_kind(strip_meta(v)) == OBJ_SET) then
       ! a collection's toString is its READABLE form -- RT.printString
       ! -- so (str ["a" \b]) is ["a" \b], not [a b]
       s = gcp_str(v, .true.)
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

  ! An array's class, as the JVM names it: [D a double[], [J a long[],
  ! [[I an int[][] -- one [ per dimension -- and [Ljava.lang.Object; an
  ! Object[]. short and byte arrays are int4 here (DEVIATIONS 45), so
  ! they answer [I.
  function array_class_name(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    character(len=:), allocatable :: kind, comp
    kind = gcna_kind(gc_i1(v))
    select case (kind)
    case ("real8");   comp = "D"
    case ("int8");    comp = "J"
    case ("int4");    comp = "I"
    case ("real4");   comp = "F"
    case ("logical"); comp = "Z"
    case default;     comp = "Ljava.lang.Object;"
    end select
    s = repeat("[", max(1, array_own_rank(v))) // comp
  end function array_class_name

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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: arr
    integer, intent(in) :: subs(:)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, shapevec, tmp
    integer, allocatable :: extents(:)
    integer :: new_offset, new_stride, k, own_rank
    logical :: ok
    integer :: base

    vst => gc_my_stack()
    out = gc_nil()
    call array_fold(arr, subs, new_offset, new_stride, ok)
    if (.not. ok) return

    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, arr)
    own_rank = array_own_rank(vs_get(vst, base + 1))
    extents = array_own_extents(vs_get(vst, base + 1))

    tmp = gcv_empty([vs_get(vst, base + 1), roots])
    call vs_set(vst, base + 2, tmp)
    tmp = gcv_conj(vs_get(vst, base + 2), gc_int(new_stride), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), roots])
    call vs_set(vst, base + 2, tmp)
    do k = size(subs) + 1, own_rank
       tmp = gcv_conj(vs_get(vst, base + 2), gc_int(extents(k)), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), roots])
       call vs_set(vst, base + 2, tmp)
    end do
    shapevec = vs_get(vst, base + 2)
    call vs_set(vst, base + 3, shapevec)

    ! Slot 1 (the value-run, for a `value`-kind array) is SHARED with
    ! the parent, unchanged -- the run holds every element of the
    ! whole base array, and this view's offset/stride already say
    ! which of them are ours.
    out = gc_obj(OBJ_ARRAY, [gc_slot(vs_get(vst, base + 1), 1), vs_get(vst, base + 3)], &
         [vs_get(vst, base + 1), vs_get(vst, base + 3), roots])
    call gc_set_i1(out, gc_i1(vs_get(vst, base + 1)))
    call gc_set_i2(out, new_offset)
    call vs_leave(vst, base)
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

  ! A map entry is a two-element vector marked in a slot the vector
  ! never uses. MapEntry is an APersistentVector on the JVM, so every
  ! vector operation works on one, and conj or assoc on it builds a
  ! plain vector, as there. The mark is what map-entry? reads, and
  ! it is how clojure.walk tells an entry from a vector it may rewrite.
  subroutine mark_entry(v)
    type(gc_value), intent(in) :: v
    if (gcv_is(v)) call gc_set_slot(v, 5, gc_int(1))
  end subroutine mark_entry

  logical function is_map_entry(v0)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v, m
    v = strip_meta(v0)
    is_map_entry = .false.
    if (.not. gcv_is(v)) return
    m = gc_slot(v, 5)
    is_map_entry = (m%tag == GCT_INT)
  end function is_map_entry

  ! Where a Var's root lives: slot 1, or slot 5 while a binding stands.
  integer function var_root_slot(v)
    type(gc_value), intent(in) :: v
    var_root_slot = 1
    if (gcn_is_var(v)) then
       if (gc_i2(v) > 0) var_root_slot = 5
    end if
  end function var_root_slot

  ! Class.isAssignableFrom, over what clotran knows of classes: a class
  ! is assignable from itself under either spelling, Object from
  ! anything, and an interface from a deftype that declared it or a
  ! built-in whose supertype chain (host_super) names it. It is what
  ! `extend` asks before refusing a type that implements the protocol
  ! inline, and what extends? and implements? read; it answered false
  ! to everything.
  function class_assignable(av, bv) result(yes)
    type(gc_value), intent(in) :: av, bv
    logical :: yes
    character(len=:), allocatable :: a, b
    type(gc_value) :: k
    integer :: i
    yes = .false.
    if (av%tag /= GCT_CLASS .and. av%tag /= GCT_SYM) return
    if (bv%tag /= GCT_CLASS .and. bv%tag /= GCT_SYM) return
    a = gc_ref_text(av%ref)
    b = gc_ref_text(bv%ref)
    yes = class_matches(a, b) .or. class_matches(b, a) .or. a == "Object" .or. a == "java.lang.Object"
    if (yes) return
    i = 1
    do
       k = host_super(bv, i, av)
       if (k%tag /= GCT_CLASS) exit
       if (class_matches(gc_ref_text(k%ref), a) .or. class_matches(a, gc_ref_text(k%ref))) then
          yes = .true.
          return
       end if
       i = i + 1
    end do
    ! an interface from an interface it extends: IPersistentCollection
    ! from IPersistentMap (iface_supers), which is how isa? orders the
    ! two when both have a print-dup method
    if (.not. yes) yes = iface_extends(b, a)
  end function class_assignable

  ! Object.hashCode as the JVM's classes define it, where clotran can
  ! say: an integer is (int)(v ^ (v >>> 32)), Long.hashCode, since
  ! Clojure's integers are all longs there; a double is that fold over
  ! its bits; a string is Java's 31-polynomial over its chars; true and
  ! false are 1231 and 1237; nil is 0. Everything else is clotran's
  ! own hash. `case` leans on the integer rule: its collision merging
  ! keys the table with Util.hash, which IS hashCode, so 1 and
  ! -9223372034707292159 both hash to 1 here as there (case_branch
  ! has the rest of that story).
  function java_hashcode(v0) result(h)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v
    integer :: h, i, cp, nb
    integer(gc_ip) :: iv, acc
    character(len=:), allocatable :: t
    v = strip_meta(v0)
    select case (v%tag)
    case (GCT_NIL)
       h = 0
    case (GCT_BOOL)
       if (v%ival /= 0) then
          h = 1231
       else
          h = 1237
       end if
    case (GCT_INT)
       h = fold_long(v%ival)
    case (GCT_BIG)
       ! BigInt.hashCode is Long.hashCode while the value fits in a
       ! long, which is what keeps (hash 1N) and (hash 1) equal -- and
       ! they must be, because (= 1N 1).
       if (big_fits_i64(gc_big_text(v))) then
          h = fold_long(big_to_i64(gc_big_text(v)))
       else
          h = gc_hash(v)
       end if
    case (GCT_REAL)
       iv = transfer(v%rval, iv)
       h = fold_long(iv)
    case (GCT_STR)
       t = gc_ref_text(v%ref)
       acc = 0_gc_ip
       i = 1
       do while (i <= len(t))
          call u8_dec(t, i, cp, nb)
          acc = iand(31_gc_ip * acc + int(cp, gc_ip), 4294967295_gc_ip)
          i = i + nb
       end do
       h = fold_long(acc)
    case default
       h = gc_hash(v)
    end select
  contains
    ! Long.hashCode, for every integer: Clojure's are all longs there
    integer function fold_long(x)
      integer(gc_ip), intent(in) :: x
      integer(gc_ip) :: y
      y = ieor(iand(x, 4294967295_gc_ip), ishft(x, -32))
      if (y > 2147483647_gc_ip) y = y - 4294967296_gc_ip
      fold_long = int(y)
    end function fold_long
  end function java_hashcode

  ! Compiler.resolveIn: a qualified symbol may not name another
  ! namespace's private Var.
  logical function var_not_public(var)
    type(gc_value), intent(in) :: var
    type(gc_value) :: md, owner, p
    var_not_public = .false.
    owner = gc_slot(var, 3)
    if (gc_kind(owner) /= OBJ_NS) return
    if (gcn_name(owner) == gcn_name(gcn_current([var]))) return
    md = gc_slot(var, 2)
    if (.not. gca_is(md)) return
    p = gca_get(md, gc_key("private", [var, md]))
    var_not_public = truthy(p)
  end function var_not_public

  ! What the interfaces a deftype declares extend: a record that says
  ! IPersistentMap is an IPersistentCollection, Associative, Counted,
  ! Seqable and a java.util.Map too, which is what coll?, counted? and
  ! clojure.walk ask. The JVM reads this off the interfaces; here it
  ! is a list.
  logical function iface_in_vector(vec, want)
    type(gc_value), intent(in) :: vec
    character(len=*), intent(in) :: want
    type(gc_value) :: k
    integer :: i
    iface_in_vector = .false.
    do i = 0, gcv_count(vec) - 1
       k = gcv_nth(vec, i)
       if (k%tag /= GCT_CLASS) cycle
       if (iface_extends(gc_ref_text(k%ref), want)) then
          iface_in_vector = .true.
          return
       end if
    end do
  end function iface_in_vector

  ! Whether an interface extends another, through any number of steps.
  recursive function iface_extends(iface, want) result(yes)
    character(len=*), intent(in) :: iface, want
    logical :: yes
    character(len=:), allocatable :: supers
    integer :: p, q
    yes = .false.
    supers = iface_supers(iface)
    if (len(supers) == 0) return
    yes = (index(supers, " " // want // " ") > 0)
    if (.not. yes .and. index(want, ".") == 0) yes = (index(supers, "." // want // " ") > 0)
    if (yes) return
    p = 2
    do while (p <= len(supers))
       q = index(supers(p:), " ")
       if (q == 0) exit
       if (q > 1) then
          if (iface_extends(supers(p:p+q-2), want)) then
             yes = .true.
             return
          end if
       end if
       p = p + q
    end do
  end function iface_extends

  ! The interfaces an interface DIRECTLY extends, as clojure.lang
  ! declares them, space-delimited with a space at each end:
  ! what .getInterfaces answers for one, so `bases` and `parents` see
  ! it and `supers` takes the closure. Direct, not transitive, because
  ! print-method prefers RandomAccess to java.util.List: a transitive
  ! list that gave IPersistentVector a java.util.List parent let
  ! RandomAccess's method dominate the vector's own, and print-str of a
  ! vector answered #object[..].
  function iface_supers(iface) result(supers)
    character(len=*), intent(in) :: iface
    character(len=:), allocatable :: supers
    select case (iface)
    case ("clojure.lang.IPersistentMap")
       supers = " clojure.lang.Associative clojure.lang.Counted "
    case ("clojure.lang.IPersistentVector")
       supers = " clojure.lang.Associative clojure.lang.Sequential clojure.lang.IPersistentStack" // &
            " clojure.lang.Reversible clojure.lang.Indexed "
    case ("clojure.lang.IPersistentSet")
       supers = " clojure.lang.IPersistentCollection clojure.lang.Counted "
    case ("clojure.lang.IPersistentList")
       supers = " clojure.lang.Sequential clojure.lang.IPersistentStack "
    case ("clojure.lang.ISeq", "clojure.lang.IPersistentStack")
       supers = " clojure.lang.IPersistentCollection "
    case ("clojure.lang.Associative")
       supers = " clojure.lang.IPersistentCollection clojure.lang.ILookup "
    case ("clojure.lang.Indexed")
       supers = " clojure.lang.Counted "
    case ("clojure.lang.IPersistentCollection")
       supers = " clojure.lang.Seqable "
    case ("clojure.lang.IObj")
       supers = " clojure.lang.IMeta "
    case default
       supers = ""
    end select
  end function iface_supers

  ! Whether TEXT names a class. Kept for the reader and the analyser,
  ! which decide from a symbol's spelling; a VALUE is a class when its
  ! tag says so.
  logical function names_a_class(t)
    character(len=*), intent(in) :: t
    type(gc_value) :: none(0)
    names_a_class = .false.
    if (index(t, "/") > 0) return
    if (gc_kind(find_type(t)) == OBJ_TYPE) then
       names_a_class = .true.
    else if (index(t, "clotran.reify__") == 1 .or. index(t, "clotran.proxy__") == 1) then
       ! a reify's class is never registered (analyze_reify), but it
       ! is a class: isa? Object, so print-method reaches Object
       names_a_class = .true.
    else
       names_a_class = is_class_name(gc_sym(t, none))
    end if
  end function names_a_class

  ! A multimethod's slot 5: [hierarchy-ref prefers cache cached-hierarchy].
  function mf_aux(mf, i) result(out)
    type(gc_value), intent(in) :: mf
    integer, intent(in) :: i
    type(gc_value) :: out
    out = gc_nil()
    if (gcv_is(gc_slot(mf, 5))) out = gcv_nth(gc_slot(mf, 5), i)
  end function mf_aux

  subroutine mf_aux_set(mf, i, v)
    type(gc_value), intent(in) :: mf, v
    integer, intent(in) :: i
    type(gc_value) :: nv
    if (.not. gcv_is(gc_slot(mf, 5))) return
    nv = gcv_put(gc_slot(mf, 5), i, v, [mf, v])
    call gc_set_slot(mf, 5, nv)
  end subroutine mf_aux_set

  ! The hierarchy the multimethod dispatches over: its ref's value --
  ! #'global-hierarchy unless defmulti was given :hierarchy
  function mf_hierarchy(mf) result(h)
    type(gc_value), intent(in) :: mf
    type(gc_value) :: h, ref
    ref = mf_aux(mf, 0)
    h = ref
    if (gcn_is_var(ref)) then
       h = gcn_var_value(ref)
    else if (gc_kind(ref) == OBJ_ATOM) then
       h = gc_slot(ref, 1)
    end if
  end function mf_hierarchy

  subroutine mf_reset_cache(mf)
    type(gc_value), intent(in) :: mf
    call mf_aux_set(mf, 2, gca_empty([mf]))
    call mf_aux_set(mf, 3, gc_nil())
  end subroutine mf_reset_cache

  ! MultiFn.getFn: the method for a dispatch value, from the cache when
  ! the hierarchy is the one it was filled under; else the exact entry,
  ! else clotran.rt's mf-find-method -- isa? over the hierarchy, the
  ! preferences, the default, and the ambiguity error -- and cached.
  ! nil when there is none. (DEVIATIONS 8, resolved.)
  recursive function mf_lookup(mf, dv, roots) result(meth)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: mf, dv
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: meth, h, fargs, cache
    integer :: base
    vst => gc_my_stack()
    tctx => ctx_self()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, mf)
    call vs_set(vst, base + 2, dv)
    ! the exact entry first: it dominates whatever else matches, and
    ! it is the common case -- print-method on a map's class -- so it
    ! costs one lookup, as it always did
    meth = gca_get(gc_slot(vs_get(vst, base + 1), 4), vs_get(vst, base + 2))
    if (meth%tag /= GCT_NIL) then
       call vs_leave(vst, base)
       return
    end if
    h = mf_hierarchy(vs_get(vst, base + 1))
    call vs_set(vst, base + 3, h)
    if (.not. same_object(mf_aux(vs_get(vst, base + 1), 3), vs_get(vst, base + 3))) then
       call mf_reset_cache(vs_get(vst, base + 1))
       call mf_aux_set(vs_get(vst, base + 1), 3, vs_get(vst, base + 3))
    end if
    meth = gca_get(mf_aux(vs_get(vst, base + 1), 2), vs_get(vst, base + 2))
    if (meth%tag == GCT_NIL) then
       fargs = gcv_build(6, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       call vs_set(vst, base + 4, fargs)
       fargs = gcv_put(vs_get(vst, base + 4), 0, gc_slot(vs_get(vst, base + 1), 1), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, fargs)
       fargs = gcv_put(vs_get(vst, base + 4), 1, vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, fargs)
       fargs = gcv_put(vs_get(vst, base + 4), 2, vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, fargs)
       fargs = gcv_put(vs_get(vst, base + 4), 3, gc_slot(vs_get(vst, base + 1), 4), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, fargs)
       fargs = gcv_put(vs_get(vst, base + 4), 4, mf_aux(vs_get(vst, base + 1), 1), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, fargs)
       fargs = gcv_put(vs_get(vst, base + 4), 5, gc_slot(vs_get(vst, base + 1), 3), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 4, fargs)
       meth = mf_call("find-method", vs_get(vst, base + 4))
       if (tctx%has_error) then
          meth = gc_nil()
          call vs_leave(vst, base)
          return
       end if
    end if
    if (meth%tag /= GCT_NIL) then
       call vs_set(vst, base + 4, meth)
       cache = gca_assoc(mf_aux(vs_get(vst, base + 1), 2), vs_get(vst, base + 2), vs_get(vst, base + 4), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4)])
       call mf_aux_set(vs_get(vst, base + 1), 2, cache)
       meth = vs_get(vst, base + 4)
    end if
    call vs_leave(vst, base)
  end function mf_lookup

  ! The library a package name reaches: the path itself when it is a
  ! file; <path>.dylib or .so when it has no extension; and for a
  ! DIRECTORY, <dir>/lib<name>.dylib or .so, with the directory joining
  ! the classpath roots so that (require 'name) finds the package's own
  ! Clojure beside its library. That is what a package is: a directory
  ! holding a shared library and the namespaces that wrap it.
  function pkg_library(given) result(path)
    character(len=*), intent(in) :: given
    character(len=:), allocatable :: path, base, cand
    character(len=1024), allocatable :: grown(:)
    character(len=5), parameter :: exts(2) = [character(len=5) :: "dylib", "so"]
    logical :: there
    integer :: i, slash
    path = given
    inquire(file=given, exist=there)
    if (there .and. index(given, ".", back=.true.) > index(given, "/", back=.true.)) return
    slash = index(given, "/", back=.true.)
    base = given(slash+1:)
    do i = 1, 2
       cand = given // "/lib" // base // "." // trim(exts(i))
       inquire(file=cand, exist=there)
       if (there) then
          path = cand
          if (.not. allocated(pkg_roots)) allocate(pkg_roots(0))
          allocate(grown(size(pkg_roots) + 1))
          grown(1:size(pkg_roots)) = pkg_roots
          grown(size(grown)) = given
          call move_alloc(grown, pkg_roots)
          return
       end if
    end do
    do i = 1, 2
       cand = given // "." // trim(exts(i))
       inquire(file=cand, exist=there)
       if (there) then
          path = cand
          return
       end if
    end do
    ! a directory with no library in it says so, rather than handing
    ! the directory to dlopen for a page of paths it tried
    ! no extension and no library found: a package directory that is
    ! not built, not a file for dlopen to try a page of paths on
    if (index(base, ".") == 0) &
         call fail("load-package: no lib" // base // ".dylib or .so in " // given // " (is the package built?)")
  end function pkg_library

  ! (call-package* handle routine args), marshalled by the manifest and
  ! called through the shim (DynLoad.f90). A scalar goes by pointer to a
  ! temporary of its C type; an array by pointer into its registry
  ! buffer, followed by one int4 per extent; a string null-terminated.
  ! The :out and :inout scalars come back as a map by name, a :returns
  ! value as the value (under :return when there are outs as well);
  ! arrays are written in place.
  recursive function pkg_call(hv, routine, cargs, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: hv, routine, cargs
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    type(gc_value) :: spec, av, tv, res, k, rt
    integer :: hi, nspec, ncall, nargv, slot, dslot, i, j, r, d, nout, base, nme
    logical :: nrel
    integer(c_int), allocatable, target :: ti(:), td(:)
    integer(c_long), allocatable, target :: tl(:)
    real(c_double), allocatable, target :: tr(:)
    logical(c_bool), allocatable, target :: tb(:)
    type(cbuf), allocatable, target :: ts(:)
    type(c_ptr), allocatable :: argv(:)
    character(len=:), allocatable :: sym, rname, text, rty
    character(len=8), allocatable :: ty(:), it(:)
    integer, allocatable :: rk(:), ext(:)
    type(c_funptr) :: fp
    real(c_double), pointer, contiguous :: pr(:)
    integer, pointer, contiguous :: pi(:)
    logical :: ok, has_ret
    character(len=16) :: cbuf1, cbuf2

    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, strip_meta(routine))
    call vs_set(vst, base + 2, strip_meta(cargs))
    once: do
       hi = ival_of(hv)
       if (hi < 1 .or. hi > pkg_count) then
          call fail("call-package*: no such package handle")
          exit once
       end if
       k = gc_key("symbol", [roots, vs_get(vst, base + 1)])
       sym = text_of(gca_get(vs_get(vst, base + 1), k))
       k = gc_key("name", [roots, vs_get(vst, base + 1)])
       rname = text_of(gca_get(vs_get(vst, base + 1), k))
       k = gc_key("args", [roots, vs_get(vst, base + 1)])
       spec = strip_meta(gca_get(vs_get(vst, base + 1), k))
       call vs_set(vst, base + 3, spec)
       k = gc_key("returns", [roots, vs_get(vst, base + 1)])
       rt = strip_meta(gca_get(vs_get(vst, base + 1), k))
       has_ret = (rt%tag == GCT_KEY)
       rty = ""
       if (has_ret) rty = gc_ref_text(rt%ref)
       nspec = gcv_count(vs_get(vst, base + 3))
       ncall = gcv_count(vs_get(vst, base + 2))
       allocate(ty(nspec), it(nspec), rk(nspec))
       nargv = nspec
       do i = 1, nspec
          av = strip_meta(gcv_nth(vs_get(vst, base + 3), i - 1))
          k = gc_key("type", [roots, av])
          tv = strip_meta(gca_get(av, k))
          ty(i) = ""
          if (tv%tag == GCT_KEY) ty(i) = gc_ref_text(tv%ref)
          k = gc_key("intent", [roots, av])
          tv = strip_meta(gca_get(av, k))
          it(i) = "in"
          if (tv%tag == GCT_KEY) it(i) = gc_ref_text(tv%ref)
          k = gc_key("rank", [roots, av])
          tv = strip_meta(gca_get(av, k))
          rk(i) = 0
          if (tv%tag == GCT_INT) rk(i) = int(tv%ival)
          nargv = nargv + rk(i)
       end do
       if (has_ret) nargv = nargv + 1
       allocate(ti(nspec + 1), tl(nspec + 1), tr(nspec + 1), tb(nspec + 1), ts(nspec + 1), argv(nargv), td(max(1, nargv)))
       ti = 0; tl = 0; tr = 0.0_c_double; tb = .false.; td = 0
       ! the call's arguments are the manifest's, less the :out ones
       j = 0
       do i = 1, nspec
          if (it(i) /= "out") j = j + 1
       end do
       if (j /= ncall) then
          write(cbuf1, '(I0)') j
          write(cbuf2, '(I0)') ncall
          call raise_class("ArityException", "Wrong number of args (" // trim(cbuf2) // ") passed to: " // rname // &
               ", which takes " // trim(cbuf1), [roots, vs_get(vst, base + 1)])
          exit once
       end if
       slot = 0
       dslot = 0
       j = 0
       do i = 1, nspec
          tv = gc_nil()
          if (it(i) /= "out") then
             tv = strip_meta(gcv_nth(vs_get(vst, base + 2), j))
             j = j + 1
          end if
          slot = slot + 1
          if (rk(i) == 0) then
             select case (trim(ty(i)))
             case ("real8")
                if (it(i) /= "out") then
                   if (.not. is_number(tv)) then
                      call raise_class("ClassCastException", sym // ": argument " // trim(cbuf_of(i)) // " is not a number", [roots])
                      exit once
                   end if
                   tr(i) = real(num_dbl(tv), c_double)
                end if
                argv(slot) = c_loc(tr(i))
             case ("int4")
                if (it(i) /= "out") ti(i) = int(tv%ival, c_int)
                argv(slot) = c_loc(ti(i))
             case ("int8")
                if (it(i) /= "out") tl(i) = int(tv%ival, c_long)
                argv(slot) = c_loc(tl(i))
             case ("logical")
                if (it(i) /= "out") tb(i) = logical(truthy(tv), c_bool)
                argv(slot) = c_loc(tb(i))
             case ("string")
                if (it(i) == "out") then
                   call fail("call-package*: " // sym // ": a string cannot be an :out argument")
                   exit once
                end if
                text = text_of(tv)
                allocate(ts(i)%s(len(text) + 1))
                do d = 1, len(text)
                   ts(i)%s(d) = text(d:d)
                end do
                ts(i)%s(len(text) + 1) = c_null_char
                argv(slot) = c_loc(ts(i)%s)
             case default
                call fail("call-package*: " // sym // ": unknown argument type " // trim(ty(i)))
                exit once
             end select
          else
             ! an array: the registry buffer, then its extents
             if (gc_kind(tv) /= OBJ_ARRAY) then
                call fail("call-package*: " // sym // ": argument " // trim(cbuf_of(i)) // " must be an array")
                exit once
             end if
             if (gc_i2(tv) /= -1) then
                call fail("call-package*: " // sym // ": a slice is not contiguous; pass a whole array")
                exit once
             end if
             ext = gcna_extents(gc_i1(tv))
             if (size(ext) /= rk(i)) then
                call fail("call-package*: " // sym // ": argument " // trim(cbuf_of(i)) // " has the wrong rank")
                exit once
             end if
             ok = .false.
             select case (trim(ty(i)))
             case ("real8")
                call gcna_real8_ptr(gc_i1(tv), pr, ok)
                if (ok) argv(slot) = c_loc(pr)
             case ("int4")
                call gcna_int4_ptr(gc_i1(tv), pi, ok)
                if (ok) argv(slot) = c_loc(pi)
             end select
             if (.not. ok) then
                call fail("call-package*: " // sym // ": argument " // trim(cbuf_of(i)) // " is not a " // trim(ty(i)) // " array (it is a " // gcna_kind(gc_i1(tv)) // " array; fortran/make-array makes typed ones)")
                exit once
             end if
             do d = 1, rk(i)
                dslot = dslot + 1
                td(dslot) = int(ext(d), c_int)
                slot = slot + 1
                argv(slot) = c_loc(td(dslot))
             end do
          end if
       end do
       if (has_ret) then
          slot = slot + 1
          select case (rty)
          case ("real8");   argv(slot) = c_loc(tr(nspec + 1))
          case ("int4");    argv(slot) = c_loc(ti(nspec + 1))
          case ("int8");    argv(slot) = c_loc(tl(nspec + 1))
          case ("logical"); argv(slot) = c_loc(tb(nspec + 1))
          case default
             call fail("call-package*: " // sym // ": unknown return type " // rty)
             exit once
          end select
       end if
       fp = dl_sym(pkg_handles(hi), sym)
       if (.not. c_associated(fp)) then
          call fail("call-package*: the package has no " // sym)
          exit once
       end if
       ! off the baton while the routine runs, if this is a task (tasks.inc)
       call native_begin(nme, nrel)
       call dl_call_shim(fp, argv)
       if (nrel) call native_end(nme)
       ! the results
       res = gca_empty([roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 4, res)
       nout = 0
       do i = 1, nspec
          if (rk(i) /= 0 .or. it(i) == "in") cycle
          av = strip_meta(gcv_nth(vs_get(vst, base + 3), i - 1))
          k = gc_key("name", [roots, av])
          tv = strip_meta(gca_get(av, k))
          k = gc_key(text_of(tv), [roots, vs_get(vst, base + 4)])
          call vs_set(vst, base + 5, k)
          res = gca_assoc(vs_get(vst, base + 4), vs_get(vst, base + 5), temp_value(i), [roots, vs_get(vst, base + 5), vs_get(vst, base + 4)])
          call vs_set(vst, base + 4, res)
          nout = nout + 1
       end do
       if (has_ret) then
          if (nout == 0) then
             out = temp_value(nspec + 1)
          else
             k = gc_key("return", [roots, vs_get(vst, base + 4)])
             call vs_set(vst, base + 5, k)
             res = gca_assoc(vs_get(vst, base + 4), vs_get(vst, base + 5), temp_value(nspec + 1), [roots, vs_get(vst, base + 5), vs_get(vst, base + 4)])
             out = res
          end if
       else if (nout > 0) then
          out = vs_get(vst, base + 4)
       end if
       exit once
    end do once
    call vs_leave(vst, base)
  contains
    function temp_value(i) result(v)
      integer, intent(in) :: i
      type(gc_value) :: v
      character(len=8) :: t
      if (i > nspec) then
         t = rty
      else
         t = ty(i)
      end if
      select case (trim(t))
      case ("real8");   v = gc_real(real(tr(i), gc_dp))
      case ("int4");    v = gc_int(int(ti(i), gc_ip))
      case ("int8");    v = gc_int(int(tl(i), gc_ip))
      case ("logical"); v = gc_bool(logical(tb(i)))
      case default;     v = gc_nil()
      end select
    end function temp_value
    function cbuf_of(i) result(s)
      integer, intent(in) :: i
      character(len=16) :: s
      write(s, '(I0)') i
    end function cbuf_of
  end function pkg_call

  ! Whether a vector of class keywords names this class.
  logical function key_in_vector(vec, name)
    type(gc_value), intent(in) :: vec
    character(len=*), intent(in) :: name
    type(gc_value) :: k
    integer :: i
    key_in_vector = .false.
    do i = 0, gcv_count(vec) - 1
       k = gcv_nth(vec, i)
       if (k%tag /= GCT_CLASS) cycle
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
    if (cls%tag /= GCT_CLASS) return
    ! SHORTENED: a class value carries its canonical name, and the
    ! cases below are written the way a Clojure program writes the
    ! class -- Object, String, CharSequence -- so java.lang comes off
    ! first. Everything else keeps its package.
    c = short_class_name(gc_ref_text(cls%ref))
    ! an array class: the same element type and the same rank
    if (len(c) > 0) then
       if (c(1:1) == "[") then
          yes = gc_kind(strip_meta(v)) == OBJ_ARRAY
          if (yes) yes = (array_class_name(strip_meta(v)) == c)
          return
       end if
    end if
    t = type_name(v)
    ! A deftype/reify instance is an instance of its own class and of
    ! everything its :implements list names -- which is the whole
    ! hierarchy there is, and enough for find-protocol-impl, whose
    ! first question is (instance? (:on-interface protocol) x).
    ! An exception is an instance of its own class and of what catch
    ! would take it under
    if (t == "error" .and. is_throwable_class(c)) then
       yes = exc_class_matches(c, strip_meta(v))
       return
    end if
    if (gc_kind(strip_meta(v)) == OBJ_INST) then
       yes = class_matches(t, c) .or. (c == "Object") .or. &
            key_in_vector(gc_slot(gc_slot(strip_meta(v), 1), 4), c)
       if (.not. yes) yes = iface_in_vector(gc_slot(gc_slot(strip_meta(v), 1), 4), c)
       return
    end if
    select case (c)
    ! every array has ONE class here (DEVIATIONS 45), so an array is an
    ! instance of it -- (instance? (class (double-array 0)) a)
    case ("array")
       yes = (t == "array")
    case ("Class", "java.lang.Class")
       yes = (t == "class")
    case ("clojure.lang.Symbol");   yes = (t == "symbol")
    case ("clojure.lang.Keyword");  yes = (t == "keyword")
    case ("clojure.lang.Var");      yes = (t == "var")
    case ("clojure.lang.Namespace"); yes = (t == "ns")
    ! ifn? is (instance? clojure.lang.IFn x): a set, a map, a vector, a
    ! keyword, a symbol and a Var all invoke; fn? is Fn, functions only.
    case ("clojure.lang.IFn"); yes = (t == "fn" .or. t == "multifn" .or. t == "set" .or. t == "map" .or. &
         t == "vector" .or. t == "keyword" .or. t == "symbol" .or. t == "var")
    case ("clojure.lang.Fn"); yes = (t == "fn")
    case ("clojure.lang.MultiFn"); yes = (t == "multifn")
    case ("clojure.lang.IDeref", "clojure.lang.IPending")
       ! core.clj's deref is (if (instance? clojure.lang.IDeref ref)
       ! (.deref ref) (deref-future ref)), so a thing that derefs has
       ! to ANSWER to IDeref or it silently takes the future path --
       ! which is how @(delay 1) came back as the delay itself.
       yes = (t == "atom" .or. t == "delay" .or. t == "var" .or. t == "volatile")
       ! Reduced implements IDeref: @(reduced x) is x, and reduce's
       ! Clojure-side loops unwrap through deref
       if (c == "clojure.lang.IDeref" .and. .not. yes) yes = is_reduced(v)
    case ("clojure.lang.Delay"); yes = (t == "delay")
    case ("clojure.lang.Volatile"); yes = (t == "volatile")
    ! The concrete classes `class` answers (class_name_of), so that
    ! (instance? (class x) x) holds and a condp on them can ask.
    case ("clojure.lang.PersistentVector"); yes = (t == "vector")
    case ("clojure.lang.PersistentArrayMap", "clojure.lang.PersistentHashMap"); yes = (t == "map")
    case ("clojure.lang.PersistentHashSet"); yes = (t == "set")
    case ("clojure.lang.PersistentTreeMap"); yes = (t == "map") .and. is_sorted_coll(v)
    case ("clojure.lang.PersistentTreeSet"); yes = (t == "set") .and. is_sorted_coll(v)
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
    case ("clojure.lang.TaggedLiteral")
       ! the same marker-map trick as Reduced, just below
       yes = is_tagged_literal(v)
    case ("java.util.UUID", "UUID")
       ! a UUID is its text here (DEVIATIONS 12), so uuid? asks
       ! whether the string has the shape of one
       yes = is_uuid_text(v)
    case ("clojure.lang.Reduced")
       ! A Reduced is the one-key map (reduced x) builds, so instance?
       ! asks for the key. Without this reduce returned the WRAPPER
       ! instead of unwrapping it on an early exit.
       yes = is_reduced(v)
    case ("Throwable", "java.lang.Throwable", "Exception", "java.lang.Exception", &
          "Error", "IExceptionInfo", "clojure.lang.IExceptionInfo", &
          "ExceptionInfo", "clojure.lang.ExceptionInfo")
       yes = (t == "error")
    case ("clojure.lang.ISeq");     yes = (t == "list" .or. t == "lazy-seq" .or. t == "seq")
    case ("clojure.lang.IPersistentList"); yes = (t == "list")
    case ("clojure.lang.IPersistentVector", "clojure.lang.Indexed"); yes = (t == "vector")
    case ("clojure.lang.IPersistentMap", "java.util.Map"); yes = (t == "map")
    case ("clojure.lang.IPersistentSet"); yes = (t == "set")
    case ("java.util.Map$Entry", "clojure.lang.IMapEntry", "clojure.lang.MapEntry"); yes = is_map_entry(v)
    case ("clojure.lang.IKVReduce"); yes = (t == "vector" .or. t == "map")
    case ("clojure.lang.Sorted"); yes = is_sorted_coll(v)
    case ("clojure.lang.Reversible"); yes = (t == "vector") .or. is_sorted_coll(v)
    case ("clojure.lang.Associative"); yes = (t == "map" .or. t == "vector")
    ! A String is NOT Counted on the JVM: RT.count knows how to count
    ! one, but (counted? "ab") is false there, so bounded-count walks it.
    case ("clojure.lang.Counted"); &
         yes = (t == "list" .or. t == "vector" .or. t == "map" .or. t == "set" .or. &
                (t == "lazy-seq" .and. gc_i2(strip_meta(v)) == 1))
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
       ! "atom" is here because an atom, ref or agent is an
       ! IReference, which extends IMeta: reset-meta! and alter-meta!
       ! write the box's own metadata slot and `meta` must read it.
       yes = (t == "symbol" .or. t == "list" .or. t == "vector" .or. &
              t == "map" .or. t == "set" .or. t == "var" .or. t == "fn" .or. &
              t == "seq" .or. t == "lazy-seq" .or. t == "ns" .or. t == "atom")
       ! and anything with-meta has wrapped can report what it was given
       if (gc_kind(v) == OBJ_META) yes = .true.
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
    case ("String", "java.lang.String"); yes = (t == "string")
    ! A StringBuilder is a CharSequence but NOT a String, and
    ! clojure.string tells them apart: replace takes the CharSequence
    ! branch for a match or a replacement and calls the thing as a
    ! FUNCTION otherwise -- "not a function: a".
    case ("CharSequence"); yes = (t == "string" .or. t == "string-builder")
    case ("Character", "java.lang.Character"); yes = (t == "char")
    case ("Boolean", "java.lang.Boolean"); yes = (t == "boolean")
    case ("Long", "java.lang.Long", "Integer", "java.lang.Integer"); yes = (t == "int")
    ! int? is Long/Integer/Short/Byte and answers FALSE for a BigInt;
    ! integer? asks for this one as well, so (integer? 1N) is true.
    case ("clojure.lang.BigInt", "BigInt", "BigInteger", "java.math.BigInteger"); yes = (t == "bigint")
    ! decimal? is (instance? BigDecimal x), and nothing else answers it
    case ("BigDecimal", "java.math.BigDecimal"); yes = (t == "bigdec")
    case ("Double", "java.lang.Double", "Float"); yes = (t == "double")
    case ("Ratio", "clojure.lang.Ratio"); yes = (t == "ratio")
    case ("Number", "java.lang.Number")
       ! A Ratio is a Number on the JVM too, so (number? 1/2) is true.
       yes = (t == "int" .or. t == "double" .or. t == "ratio" .or. t == "bigint" &
            .or. t == "bigdec")
    end select
  end function is_instance

  ! Every element of a seqable, as a vector. The three host `create`
  ! statics all take a collection, so they all start here.
  recursive function coll_to_vector(coll, roots, limit) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: coll
    type(gc_value), intent(in) :: roots(:)
    integer, intent(in), optional :: limit   ! more elements than this is an error, not a hang
    type(gc_value) :: out, walk, item
    integer :: base, k
    character(len=16) :: buf

    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    out = gcv_empty(roots)
    call vs_set(vst, base + 1, out)
    walk = to_seq(coll, roots)
    call vs_set(vst, base + 2, walk)
    k = 0
    do while (walk%tag /= GCT_NIL)
       if (present(limit)) then
          k = k + 1
          if (k > limit) then
             write(buf, '(I0)') limit
             call fail("apply: more than " // trim(buf) // " arguments; the argument seq is realised here -- a native or a fixed-arity callee spreads it; only a variadic fn takes a seq as it is)")
             exit
          end if
       end if
       item = sq_first(vs_get(vst, base + 2), [vs_get(vst, base + 1)])
       out = gcv_conj(vs_get(vst, base + 1), item, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 1, out)
       walk = to_seq(sq_rest(vs_get(vst, base + 2), [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, walk)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function coll_to_vector

  ! Every element of a seq, as a proper list.
  recursive function seq_to_list(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, items
    integer :: base, i

    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    items = coll_to_vector(v, roots)
    call vs_set(vst, base + 1, items)
    out = gcl_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, out)
    do i = gcv_count(vs_get(vst, base + 1)) - 1, 0, -1
       out = gcl_cons(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, out)
    end do
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function seq_to_list

  ! Numeric comparison across int and double. Comparing %ival alone
  ! made (< 1.5 2.0) read two garbage integers; one place to decide it
  ! means < > <= >= and compare cannot disagree.
  ! Every ordering in the language funnels through here: <, >, <=, >=,
  ! min, max, zero?, pos?, neg? and compare. Two integral values are
  ! compared EXACTLY -- through the text when either is a BigInt --
  ! because a double cannot tell 2^63 from 2^63 + 1.
  logical function num_lt(a, b)
    type(gc_value), intent(in) :: a, b
    if (a%tag == GCT_INT .and. b%tag == GCT_INT) then
       num_lt = (a%ival < b%ival)
    else if ((a%tag == GCT_INT .or. a%tag == GCT_BIG) .and. &
             (b%tag == GCT_INT .or. b%tag == GCT_BIG)) then
       num_lt = (big_cmp(big_of(a), big_of(b)) < 0)
    else if (exact_num(a) .and. exact_num(b) .and. &
             (a%tag == GCT_DEC .or. b%tag == GCT_DEC)) then
       ! A decimal compares EXACTLY against another decimal, an
       ! integer or a BigInt -- a double would lose the difference
       ! between 1M and 1.0000000000000000001M.
       num_lt = (dec_cmp(dec_of(a), dec_of(b)) < 0)
    else
       num_lt = (num_dbl(a) < num_dbl(b))
    end if
  end function num_lt

  ! The decimal text of an INTEGRAL value -- an integer or a BigInt --
  ! which is the form every big operation takes and returns.
  ! A BigInt as a plain integer for rational arithmetic, while it
  ! fits. ok is false when it does not, and the caller raises.
  ! A value USED AS AN INTEGER -- an index, a count, a range bound.
  ! A BigInt that fits becomes the long it equals, because everything
  ! below reads %ival and a BigInt keeps 0 there: (nth v 1N) answered
  ! element 0, silently. One past the range stays a BigInt and the
  ! caller's own bounds check rejects it.
  function as_int(v0) result(o)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: o
    o = strip_meta(v0)
    if (o%tag /= GCT_BIG) return
    if (big_fits_i64(gc_big_text(o))) o = gc_int(big_to_i64(gc_big_text(o)))
  end function as_int

  ! An INDEX, which Clojure reads through RT.intCast: a double
  ! index is truncated, so (nth [:a :b :c] 2.0) is :c and
  ! (subs "abcd" 1.0) is "bcd". Not the same question as as_int --
  ! (get [:a :b] 1.0) is nil and (contains? [:a :b] 1.0) false,
  ! because a map-style lookup asks whether the KEY is an integer
  ! rather than coercing it. cl-format walks a double's digits with
  ! nth, which is how (cl-format nil "~R" 2e6) said "zero million".
  function as_index(v0) result(o)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: o
    o = strip_meta(v0)
    if (o%tag == GCT_INT) return
    if (o%tag == GCT_REAL .or. o%tag == GCT_BIG .or. o%tag == GCT_DEC &
         .or. o%tag == GCT_RATIO) o = gc_int(int_of_number(o))
  end function as_index

  function rat_operand(v, ok) result(o)
    type(gc_value), intent(in) :: v
    logical, intent(out) :: ok
    type(gc_value) :: o
    ok = .true.
    o = v
    if (v%tag /= GCT_BIG) return
    ok = big_fits_i64(gc_big_text(v))
    if (ok) o = gc_int(big_to_i64(gc_big_text(v)))
  end function rat_operand

  ! MathContext.DECIMAL128 as the map (MathContext. p mode) builds:
  ! 34 significant digits, rounding half to even. It is what
  ! *math-context* holds until something binds it.
  function default_math_context(roots) result(mc)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: mc, k, v
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    mc = gca_empty(roots)
    call vs_set(vst, base + 1, mc)
    k = gc_key("precision", [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, k)
    mc = gca_assoc(vs_get(vst, base + 1), vs_get(vst, base + 2), gc_int(34_gc_ip), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 1, mc)
    k = gc_key("rounding", [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, k)
    v = gc_key("HALF_EVEN", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, v)
    mc = gca_assoc(vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_leave(vst, base)
  end function default_math_context

  ! What with-precision bound, if anything: the precision (0 when
  ! there is no context, which every operation reads as "exact or
  ! throw") and the rounding mode.
  subroutine math_context(prec, mode)
    integer, intent(out) :: prec, mode
    type(gc_value) :: var, mc, pv, rv, none(0)
    prec = 0
    mode = DEC_HALF_UP
    if (.not. gc_root_live(math_ctx_root)) return
    var = gc_root_get(math_ctx_root)
    if (.not. gcn_is_var(var)) return
    mc = strip_meta(gcn_var_value(var))
    if (.not. gca_is(mc)) return
    pv = strip_meta(gca_get(mc, gc_key("precision", [mc])))
    if (pv%tag /= GCT_INT) return
    prec = int(pv%ival)
    rv = strip_meta(gca_get(mc, gc_key("rounding", [mc])))
    if (rv%tag == GCT_KEY) then
       if (dec_mode_of(gc_ref_text(rv%ref)) /= 0) mode = dec_mode_of(gc_ref_text(rv%ref))
    end if
  end subroutine math_context

  pure function cast_width_name(id) result(s)
    integer, intent(in) :: id
    character(len=:), allocatable :: s
    select case (id)
    case (B_CHKBYTE);  s = "byte"
    case (B_CHKSHORT); s = "short"
    case default;      s = "int"
    end select
  end function cast_width_name

  ! The integer a NUMBER carries, whatever kind it is: what the
  ! narrowing casts start from.
  function int_of_number(v) result(i)
    type(gc_value), intent(in) :: v
    integer(gc_ip) :: i
    if (v%tag == GCT_REAL) then
       i = int(v%rval, gc_ip)
    else if (v%tag == GCT_BIG) then
       i = big_to_i64(gc_big_text(v))
    else if (v%tag == GCT_DEC) then
       i = big_to_i64(dec_to_big(gc_dec_text(v)))
    else if (v%tag == GCT_RATIO) then
       i = gc_numerator(v) / gc_denominator(v)
    else
       i = v%ival
    end if
  end function int_of_number

  ! Whether a value is EXACT -- an integer, a BigInt or a decimal --
  ! which is what decides whether a comparison can avoid doubles. A
  ! Ratio is exact too but has no decimal form for every value.
  logical function exact_num(v)
    type(gc_value), intent(in) :: v
    exact_num = (v%tag == GCT_INT .or. v%tag == GCT_BIG .or. v%tag == GCT_DEC)
  end function exact_num

  ! An exact value as a DECIMAL, which an integer and a BigInt are at
  ! scale zero.
  function dec_of(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    if (v%tag == GCT_DEC) then
       s = gc_dec_text(v)
    else
       s = dec_from_big(big_of(v))
    end if
  end function dec_of

  ! The same, for an operand that may also be a RATIO: 1/2 is 0.5M and
  ! (+ 1M 1/2) is 1.5M, but 1/3 has no decimal form and Java's
  ! BigDecimal refuses rather than rounding. ok says which happened.
  function dec_operand(v, ok) result(s)
    type(gc_value), intent(in) :: v
    logical, intent(out) :: ok
    character(len=:), allocatable :: s
    ok = .true.
    if (v%tag == GCT_RATIO) then
       call dec_div(dec_from_big(big_from_i64(gc_numerator(v))), &
            dec_from_big(big_from_i64(gc_denominator(v))), s, ok)
    else
       s = dec_of(v)
    end if
  end function dec_operand

  function big_of(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    if (v%tag == GCT_BIG) then
       s = gc_big_text(v)
    else
       s = big_from_i64(v%ival)
    end if
  end function big_of

  ! Java's (long) of a double: truncate toward zero, saturate at the
  ! ends of the range, and 0 for NaN. Fortran's int() is undefined out
  ! of range, so the ends are handled first.
  function long_of_double(d) result(n)
    real(gc_dp), intent(in) :: d
    integer(gc_ip) :: n
    if (d /= d) then
       n = 0
    else if (d >= 9223372036854775807.0_gc_dp) then
       n = huge(0_gc_ip)
    else if (d <= -9223372036854775808.0_gc_dp) then
       n = -huge(0_gc_ip) - 1_gc_ip
    else
       n = int(d, gc_ip)
    end if
  end function long_of_double

  ! What RT's ((Number) x) raises for something that is not a number:
  ! a NullPointerException for nil, a ClassCastException otherwise,
  ! naming the class the way the JVM does.
  subroutine raise_number_cast(v, roots)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    if (v%tag == GCT_NIL) then
       call raise_class("NullPointerException", &
            'Cannot invoke "java.lang.Number.doubleValue()" because "x" is null', roots)
    else
       call raise_class("ClassCastException", "class " // class_name_of(v) // &
            " cannot be cast to class java.lang.Number", roots)
    end if
  end subroutine raise_number_cast

  function num_dbl(v) result(d)
    type(gc_value), intent(in) :: v
    real(gc_dp) :: d
    if (v%tag == GCT_REAL) then
       d = v%rval
    else if (v%tag == GCT_BIG) then
       d = big_to_dbl(gc_big_text(v))
    else if (v%tag == GCT_DEC) then
       d = dec_to_dbl(gc_dec_text(v))
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
    is_number = (v%tag == GCT_INT .or. v%tag == GCT_REAL .or. v%tag == GCT_RATIO &
         .or. v%tag == GCT_BIG .or. v%tag == GCT_DEC)
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
    if (dv%tag /= GCT_CLASS) return
    ! The chain table below is written in SHORT names for the java.lang
    ! ones (Number, Object) and in full for the rest, so the class name
    ! is shortened on the way in and canonicalised on the way out --
    ! a class value is its canonical name, and Number must come back as
    ! java.lang.Number or print-method Number will not match a Long.
    t = short_class_name(gc_ref_text(dv%ref))

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
      ! The clojure.lang interfaces only: what cljs.core's types also
      ! declare, under its own names. The java.util ones (List,
      ! RandomAccess, Map, Set, Collection) were here for core_print.clj
      ! and data.clj, which clotran no longer runs verbatim (B_RTLOAD).
      case ("clojure.lang.PersistentVector")
         chain(1:3) = [character(len=36) :: "clojure.lang.IPersistentVector", &
              "clojure.lang.IKVReduce", "clojure.lang.IPersistentCollection"]
         cnt = 3
      case ("clojure.lang.PersistentArrayMap")
         chain(1:2) = [character(len=36) :: "clojure.lang.IPersistentMap", "clojure.lang.IPersistentCollection"]
         cnt = 2
      case ("clojure.lang.PersistentHashSet")
         chain(1:2) = [character(len=36) :: "clojure.lang.IPersistentSet", "clojure.lang.IPersistentCollection"]
         cnt = 2
      case ("clojure.lang.PersistentTreeMap")
         chain(1:4) = [character(len=36) :: "clojure.lang.Sorted", "clojure.lang.Reversible", &
              "clojure.lang.IPersistentMap", "clojure.lang.IPersistentCollection"]
         cnt = 4
      case ("clojure.lang.PersistentTreeSet")
         chain(1:4) = [character(len=36) :: "clojure.lang.Sorted", "clojure.lang.Reversible", &
              "clojure.lang.IPersistentSet", "clojure.lang.IPersistentCollection"]
         cnt = 4
      case ("clojure.lang.PersistentList")
         chain(1:3) = [character(len=36) :: "clojure.lang.IPersistentList", "clojure.lang.ISeq", &
              "clojure.lang.IPersistentCollection"]
         cnt = 3
      case ("clojure.lang.LazySeq", "clojure.lang.PersistentVector$ChunkedSeq", "clojure.lang.Cons", &
            "clojure.lang.LongRange", "clojure.lang.Range", "clojure.lang.ChunkedCons")
         chain(1:2) = [character(len=36) :: "clojure.lang.ISeq", "clojure.lang.IPersistentCollection"]
         cnt = 2
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
         if (t == "Throwable" .or. t == "java.lang.Throwable") then
            ! Throwable's own supertype is Object alone: naming itself
            ! sent `supers` round in a circle, and printing an exception
            ! never returned
            cnt = 0
         else if (is_throwable_class(t)) then
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
      if (i >= 1 .and. i <= cnt) k = gc_class(class_key(trim(chain(i))), [roots])
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
    case (GCT_BOOL);  s = "java.lang.Boolean"
    case (GCT_INT);   s = "java.lang.Long"
    case (GCT_REAL);  s = "java.lang.Double"
    case (GCT_RATIO); s = "clojure.lang.Ratio"
    case (GCT_CHAR);  s = "java.lang.Character"
    case (GCT_CLASS); s = "java.lang.Class"
    case (GCT_DEC);   s = "java.math.BigDecimal"
    case (GCT_BIG);   s = "clojure.lang.BigInt"
    case (GCT_STR);   s = "java.lang.String"
    case (GCT_SYM);   s = "clojure.lang.Symbol"
    case (GCT_KEY);   s = "clojure.lang.Keyword"
    case default
       select case (gc_kind(v))
       case (OBJ_CONS);    s = "clojure.lang.PersistentList"
       case (OBJ_VECTOR);  s = "clojure.lang.PersistentVector"
       case (OBJ_MAP, OBJ_HAMT)
          s = "clojure.lang.PersistentArrayMap"
          if (gca_is_sorted(v)) s = "clojure.lang.PersistentTreeMap"
       case (OBJ_SET)
          s = "clojure.lang.PersistentHashSet"
          if (gca_is_sorted(gc_slot(v, 1))) s = "clojure.lang.PersistentTreeSet"
       case (OBJ_CLOSURE, OBJ_BUILTIN, OBJ_COMPILED); s = "clojure.lang.AFunction"
       case (OBJ_MULTIFN); s = "clojure.lang.MultiFn"
       case (OBJ_REGEX);   s = "java.util.regex.Pattern"
       case (OBJ_MATCHER); s = "java.util.regex.Matcher"
       case (OBJ_WRITER);  s = "java.io.PrintWriter"
       case (OBJ_SB);      s = "java.lang.StringBuilder"
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
       case (OBJ_TASK);    s = "java.util.concurrent.FutureTask"
       case (OBJ_VOLATILE); s = "clojure.lang.Volatile"
       case (OBJ_ATOM);    s = "clojure.lang.Atom"
       case (OBJ_ARRAY);   s = array_class_name(v)
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
    ! a loaded package's directory is a root too (pkg_library)
    if (allocated(pkg_roots)) then
       do i = 1, size(pkg_roots)
          do e = 1, 3
             cand = trim(pkg_roots(i)) // "/" // rel // "." // trim(exts(e))
             inquire(file=cand, exist=there)
             if (there) then
                path = cand
                return
             end if
          end do
       end do
    end if
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

  ! The namespace an auto-resolved keyword names, for the reader:
  ! ::x is the current namespace and ::a/x the ALIAS a -- an alias
  ! only, as LispReader.matchSymbol's lookupAlias is, so a namespace's
  ! full name is an invalid token there and here. "" when there is
  ! none.
  function kw_ns_of(alias) result(ns)
    character(len=*), intent(in) :: alias
    character(len=:), allocatable :: ns
    type(gc_value) :: nsv
    type(gc_value) :: none(0)
    ns = ""
    if (len(alias) == 0) then
       nsv = gcn_current(none)
    else
       nsv = alias_target(alias, none)
    end if
    if (gc_kind(nsv) == OBJ_NS) ns = gcn_name(nsv)
  end function kw_ns_of

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
    ! as_int, not strip_meta: an index may be a BigInt, and every
    ! branch below reads %ival (which a BigInt leaves at 0).
    kk = as_int(k)
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
       if (kk%ival >= 0 .and. kk%ival < int(u8_count(t), gc_ip)) &
            out = gc_char_cp(u8_at(t, int(kk%ival)))
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
    kk = as_int(k)
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
            kk%ival < int(u8_count(gc_ref_text(coll%ref)), gc_ip))
    else
       yes = gca_contains(coll, k)
    end if
  end function coll_has

  ! What a String.indexOf needle MEANS. A string is itself, and a
  ! character -- or an integer, which is how Java spells one
  ! here -- is the single character it names.
  function itoa(i) result(s)
    integer, intent(in) :: i
    character(len=:), allocatable :: s
    character(len=24) :: buf
    write(buf, '(I0)') i
    s = trim(buf)
  end function itoa

  ! One code point through ICU's simple case map.
  function case_cp(cp, up) result(r)
    integer, intent(in) :: cp
    logical, intent(in) :: up
    integer :: r
    if (up) then
       r = int(cu_toupper(int(cp, c_int32_t)))
    else
       r = int(cu_tolower(int(cp, c_int32_t)))
    end if
  end function case_cp

  function needle_text(v0) result(s)
    type(gc_value), intent(in) :: v0
    character(len=:), allocatable :: s
    type(gc_value) :: v
    v = strip_meta(v0)
    if (v%tag == GCT_INT .or. v%tag == GCT_CHAR) then
       s = u8_enc(int(v%ival, kind=4))
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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: coll0, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, coll
    integer :: base

    vst => gc_my_stack()
    coll = strip_meta(coll0)
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, coll)
    call vs_set(vst, base + 2, x)

    if (gcv_is(coll)) then
       out = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 2), roots)
    else if (gc_kind(coll) == OBJ_SET) then
       out = gc_obj(OBJ_SET, [gca_assoc(gc_slot(vs_get(vst, base + 1), 1), &
            vs_get(vst, base + 2), vs_get(vst, base + 2), roots)], roots)
    else if (gca_is(coll)) then
       if (x%tag == GCT_NIL) then
          ! CONJ OF NIL ONTO A MAP IS A NO-OP. APersistentMap.cons
          ! walks (RT/seq o), and the seq of nil is nil, so the
          ! loop never runs and the map comes back unchanged.
          ! Treating nil as a pair assoc'd nil to nil instead, and
          ! (merge m nil) is (conj m nil) -- so every map that
          ! passed through merge grew a spurious nil entry.
          ! clojure.data/diff folds with merge over [nil nil nil].
          out = vs_get(vst, base + 1)
       else if (gca_is(vs_get(vst, base + 2))) then
          block
            type(gc_value), allocatable :: kk(:), vv(:)
            type(gc_value) :: mm
            integer :: j
            call gca_entries(vs_get(vst, base + 2), kk, vv)
            mm = vs_get(vst, base + 1)
            do j = 1, size(kk)
               mm = gca_assoc(mm, kk(j), vv(j), roots)
            end do
            out = mm
          end block
       else
          out = gca_assoc(vs_get(vst, base + 1), &
               seq_elem(vs_get(vst, base + 2), 0, roots), &
               seq_elem(vs_get(vst, base + 2), 1, roots), roots)
       end if
    else if (coll%tag == GCT_NIL) then
       out = gcl_cons(vs_get(vst, base + 2), gcl_empty(roots), roots)
    else if (.not. seqable_quiet(coll) .or. coll%tag == GCT_STR .or. gc_kind(coll) == OBJ_ARRAY) then
       ! a string or an array is not a collection to conj onto
       out = gc_nil()
       call raise_class("ClassCastException", class_name_of(coll) // &
            " cannot be cast to clojure.lang.IPersistentCollection", roots)
    else
       out = gcl_cons(vs_get(vst, base + 2), to_seq(vs_get(vst, base + 1), roots), roots)
    end if
    call vs_leave(vst, base)
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

  ! A node kind's name, as the keyword the exported tree carries.
  ! Written out rather than derived, because the generator reads
  ! these and a number would tell it nothing.
  function node_kind_name(k) result(s)
    integer, intent(in) :: k
    character(len=:), allocatable :: s
    select case (k)
    case (N_CONST);   s = "const"
    case (N_LOCAL);   s = "local"
    case (N_VAR);     s = "var"
    case (N_IF);      s = "if"
    case (N_DO);      s = "do"
    case (N_CALL);    s = "call"
    case (N_VECTOR);  s = "vector"
    case (N_MAP);     s = "map"
    case (N_SET);     s = "set"
    case (N_DEF);     s = "def"
    case (N_LET);     s = "let"
    case (N_LOOP);    s = "loop"
    case (N_LETFN);   s = "letfn"
    case (N_FN);      s = "fn"
    case (N_LAZY);    s = "lazy"
    case (N_RECUR);   s = "recur"
    case (N_THROW);   s = "throw"
    case (N_TRY);     s = "try"
    case (N_CASE);    s = "case"
    case (N_DEFTYPE); s = "deftype"
    case (N_DOT);     s = "dot"
    case (N_NEW);     s = "new"
    case (N_NEWTYPE); s = "newtype"
    case (N_SETBANG); s = "set!"
    case (N_FAIL);    s = "fail"
    case (N_TOP);     s = "top"
    case (N_TOPDO);   s = "topdo"
    case (N_LATEVAR); s = "latevar"
    case default;     s = "unknown"
    end select
  end function node_kind_name

  ! One node as a map. The shape is deliberately GENERIC -- :op,
  ! :children, :p1, :p2, :i2, :pos -- rather than a key per kind,
  ! because it then cannot fall out of step with mk_node. A child or
  ! a p-slot that is itself a node is exported as a map; anything
  ! else is exported as the value it is, so a constant arrives as the
  ! constant and a Var as the Var.
  ! ---- a compiled function's constant pool, and its fingerprint -----
  !
  ! clotran.compiler numbers the pool entries its generated code reads,
  ! and clotran.loader rebuilds the pool in a LATER process by analysing
  ! the same form again: Vars, folded functions and subtrees handed to
  ! the interpreter are live objects no file can hold. Both sides take
  ! the pool from HERE, so there is one rule and no second copy to drift.
  !
  ! The walk covers the part of the body the generator emits -- the
  ! kinds below -- and stops at any other node: that node is itself the
  ! pool entry, and the interpreter runs it. The fingerprint is 32-bit
  ! FNV-1a (held in 64 bits, so the multiply cannot overflow)
  ! over what the generated code depends on: node kinds, slot numbers,
  ! spellable constants, and each pool entry's kind and identity by
  ! name. A local's NAME is left out: it is debugging text, and a gensym
  ! (G__1039) differs in every process.

  logical function pool_compiled_kind(k)
    integer, intent(in) :: k
    pool_compiled_kind = any(k == [N_CONST, N_LOCAL, N_IF, N_DO, N_CALL, N_VAR, N_LET, N_LOOP, N_RECUR])
  end function pool_compiled_kind

  ! A constant the generated code writes into its own source (the
  ! compiler's spellable?): nil, a boolean, a long other than
  ! Long/MIN_VALUE, a finite double.
  logical function pool_spellable(v0)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v
    v = strip_meta(v0)
    select case (v%tag)
    case (GCT_NIL, GCT_BOOL)
       pool_spellable = .true.
    case (GCT_INT)
       pool_spellable = (v%ival /= -huge(v%ival) - 1)
    case (GCT_REAL)
       pool_spellable = (v%rval == v%rval .and. abs(v%rval) <= huge(v%rval))
    case default
       pool_spellable = .false.
    end select
  end function pool_spellable

  subroutine fp_mix(h, x)
    integer(gc_ip), intent(inout) :: h
    integer(gc_ip), intent(in) :: x
    integer :: i
    do i = 0, 7
       h = ieor(h, iand(shiftr(x, 8 * i), 255_gc_ip))
       h = iand(h * 16777619_gc_ip, 4294967295_gc_ip)
    end do
  end subroutine fp_mix

  subroutine fp_mix_text(h, s)
    integer(gc_ip), intent(inout) :: h
    character(len=*), intent(in) :: s
    integer :: i
    call fp_mix(h, int(len(s), gc_ip))
    do i = 1, len(s)
       h = ieor(h, int(ichar(s(i:i)), gc_ip))
       h = iand(h * 16777619_gc_ip, 4294967295_gc_ip)
    end do
  end subroutine fp_mix_text

  ! A scalar field, or a vector of them -- a recur's [count start] --
  ! mixed in; a symbol, a node or anything else is not.
  ! Text with the digits after every "__" removed: mm__1096__auto__ and
  ! G__1039 are gensyms, and the counter in them depends on how much
  ! code ran before, not on what this code is.
  function without_gensym_counters(s) result(t)
    character(len=*), intent(in) :: s
    character(len=:), allocatable :: t
    character(len=len(s)) :: buf
    integer :: i, n
    logical :: skip
    n = 0
    skip = .false.
    do i = 1, len(s)
       if (skip .and. index("0123456789", s(i:i)) > 0) cycle
       skip = .false.
       n = n + 1
       buf(n:n) = s(i:i)
       if (i > 1) skip = (s(i-1:i) == "__")
    end do
    t = buf(1:n)
  end function without_gensym_counters

  recursive subroutine fp_mix_field(h, v0)
    integer(gc_ip), intent(inout) :: h
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v
    integer :: i
    v = strip_meta(v0)
    select case (v%tag)
    case (GCT_NIL)
       call fp_mix(h, -1_gc_ip)
    case (GCT_BOOL, GCT_INT)
       call fp_mix(h, int(v%ival, gc_ip))
    case (GCT_REAL)
       call fp_mix(h, transfer(v%rval, 0_gc_ip))
    case default
       if (gcv_is(v)) then
          do i = 0, gcv_count(v) - 1
             call fp_mix_field(h, gcv_nth(v, i))
          end do
       end if
    end select
  end subroutine fp_mix_field

  ! Append [kind value] to the pool at stack slot pb unless an entry of
  ! that kind already holds the same thing: a Var or a node by
  ! identity, a constant by value. Mixes the entry into the fingerprint
  ! either way, so where it recurs is part of the shape too.
  subroutine pool_add(pb, kind, v, h)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: pb
    character(len=*), intent(in) :: kind
    type(gc_value), intent(in) :: v
    integer(gc_ip), intent(inout) :: h
    type(gc_value) :: e, pool
    integer :: i, b, at
    vst => gc_my_stack()
    b = vs_enter(vst, 3)
    call vs_set(vst, b + 1, v)
    pool = vs_get(vst, pb)
    at = -1
    do i = 0, gcv_count(pool) - 1
       e = gcv_nth(pool, i)
       if (text_of(gcv_nth(e, 0)) /= kind) cycle
       e = gcv_nth(e, 1)
       if (kind == "const") then
          if (gc_equal(e, v)) at = i
       else if (e%tag == v%tag .and. e%ref == v%ref) then
          at = i
       end if
       if (at >= 0) exit
    end do
    call fp_mix_text(h, kind)
    select case (kind)
    case ("var")
       call fp_mix_text(h, gcp_str(v, .true.))
    case ("node")
       call fp_mix(h, int(gc_i1(v), gc_ip))
    case default
       if (gc_kind(strip_meta(v)) == OBJ_BUILTIN) then
          call fp_mix_text(h, text_of(gc_slot(strip_meta(v), 1)))
       else if (gc_kind(strip_meta(v)) == OBJ_CLOSURE) then
          call fp_mix_text(h, "fn")
       else
          call fp_mix_text(h, without_gensym_counters(gcp_str(v, .true.)))
       end if
    end select
    if (at < 0) then
       e = gcv_empty([vs_get(vst, pb), vs_get(vst, b + 1)])
       call vs_set(vst, b + 2, e)
       call vs_set(vst, b + 3, gc_key(kind, [vs_get(vst, pb), vs_get(vst, b + 1), vs_get(vst, b + 2)]))
       e = gcv_conj(vs_get(vst, b + 2), vs_get(vst, b + 3), [vs_get(vst, pb), vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, b + 3)])
       call vs_set(vst, b + 2, e)
       e = gcv_conj(vs_get(vst, b + 2), vs_get(vst, b + 1), [vs_get(vst, pb), vs_get(vst, b + 1), vs_get(vst, b + 2)])
       call vs_set(vst, b + 2, e)
       pool = gcv_conj(vs_get(vst, pb), vs_get(vst, b + 2), [vs_get(vst, pb), vs_get(vst, b + 2)])
       call vs_set(vst, pb, pool)
       at = gcv_count(pool) - 1
    end if
    call fp_mix(h, int(at, gc_ip))
    call vs_leave(vst, b)
  end subroutine pool_add

  recursive subroutine pool_walk(nd, pb, h)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: pb
    integer(gc_ip), intent(inout) :: h
    type(gc_value) :: kids
    integer :: b, i, k
    vst => gc_my_stack()
    if (gc_kind(nd) /= OBJ_AST) then
       call fp_mix_field(h, nd)
       return
    end if
    b = vs_enter(vst, 2)
    call vs_set(vst, b + 1, nd)
    k = gc_i1(nd)
    call fp_mix(h, int(k, gc_ip))
    if (.not. pool_compiled_kind(k)) then
       call pool_add(pb, "node", vs_get(vst, b + 1), h)
    else if (k == N_VAR) then
       call pool_add(pb, "var", gc_slot(vs_get(vst, b + 1), 2), h)
    else if (k == N_CONST) then
       if (pool_spellable(gc_slot(vs_get(vst, b + 1), 2))) then
          call fp_mix_field(h, gc_slot(vs_get(vst, b + 1), 2))
       else
          call pool_add(pb, "const", gc_slot(vs_get(vst, b + 1), 2), h)
       end if
    else
       call fp_mix(h, int(gc_i2(vs_get(vst, b + 1)), gc_ip))
       if (k /= N_LOCAL) call fp_mix_field(h, gc_slot(vs_get(vst, b + 1), 2))
       call fp_mix_field(h, gc_slot(vs_get(vst, b + 1), 3))
       kids = gc_slot(vs_get(vst, b + 1), 1)
       call vs_set(vst, b + 2, kids)
       if (gcv_is(kids)) then
          call fp_mix(h, int(gcv_count(kids), gc_ip))
          do i = 0, gcv_count(vs_get(vst, b + 2)) - 1
             call pool_walk(gcv_nth(vs_get(vst, b + 2), i), pb, h)
          end do
       end if
    end if
    if (k == N_LOCAL) call fp_mix(h, int(gc_i2(vs_get(vst, b + 1)), gc_ip))
    call vs_leave(vst, b)
  end subroutine pool_walk

  ! {:pool [[kind value] ...] :fingerprint n} for the analysed form
  ! `top` -- a top node over a fn -- from every arity's body, in order.
  ! Anything else answers an empty pool.
  recursive function compiled_pool(top, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: top
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, fnode, tmpl, arity, m
    integer(gc_ip) :: h
    integer :: b, ia
    vst => gc_my_stack()
    b = vs_enter(vst, 4)
    call vs_set(vst, b + 1, top)
    call vs_set(vst, b + 2, gcv_empty([roots, vs_get(vst, b + 1)]))
    h = 2166136261_gc_ip
    fnode = top
    if (gc_kind(fnode) == OBJ_AST) then
       if (gc_i1(fnode) == N_TOP) fnode = gc_slot(fnode, 2)
    end if
    if (gc_kind(fnode) == OBJ_AST) then
       if (gc_i1(fnode) == N_FN) then
          tmpl = gc_slot(fnode, 2)
          ! [name arities captures nslots selfslot slotnames]
          call fp_mix(h, int(gcv_count(gcv_nth(tmpl, 1)), gc_ip))
          call fp_mix_field(h, gcv_nth(tmpl, 3))
          call fp_mix_field(h, gcv_nth(tmpl, 4))
          ! each arity: [nfixed variadic start body]
          do ia = 0, gcv_count(gcv_nth(tmpl, 1)) - 1
             arity = gcv_nth(gcv_nth(tmpl, 1), ia)
             call fp_mix_field(h, gcv_nth(arity, 0))
             call fp_mix_field(h, gcv_nth(arity, 1))
             call fp_mix_field(h, gcv_nth(arity, 2))
             call pool_walk(gcv_nth(arity, 3), b + 2, h)
          end do
       end if
    end if
    m = gca_empty([roots, vs_get(vst, b + 1), vs_get(vst, b + 2)])
    call vs_set(vst, b + 3, m)
    call vs_set(vst, b + 4, gc_key("pool", [roots, vs_get(vst, b + 2), vs_get(vst, b + 3)]))
    m = gca_assoc(vs_get(vst, b + 3), vs_get(vst, b + 4), vs_get(vst, b + 2), [roots, vs_get(vst, b + 2), vs_get(vst, b + 3), vs_get(vst, b + 4)])
    call vs_set(vst, b + 3, m)
    call vs_set(vst, b + 4, gc_key("fingerprint", [roots, vs_get(vst, b + 3)]))
    m = gca_assoc(vs_get(vst, b + 3), vs_get(vst, b + 4), gc_int(int(h, gc_ip)), [roots, vs_get(vst, b + 3), vs_get(vst, b + 4)])
    out = m
    call vs_leave(vst, b)
  end function compiled_pool

  recursive function ast_data(nd, roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, kids, v
    integer :: b, i
    vst => gc_my_stack()
    tctx => ctx_self()
    out = nd
    if (gc_kind(nd) /= OBJ_AST) return
    b = vs_enter(vst, 4)
    call vs_set(vst, b + 1, nd)
    out = gca_empty([roots, [vs_get(vst, b + 1)]])
    call vs_set(vst, b + 2, out)
    call ast_put(b, roots, "op", gc_key(node_kind_name(gc_i1(vs_get(vst, b + 1))), &
         [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2)]]))
    ! the children, each one exported in turn
    kids = gc_slot(vs_get(vst, b + 1), 1)
    if (gcv_is(kids)) then
       call vs_set(vst, b + 3, kids)
       v = gcv_empty([roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, b + 3)]])
       call vs_set(vst, b + 4, v)
       do i = 0, gcv_count(vs_get(vst, b + 3)) - 1
          v = ast_walk(gcv_nth(vs_get(vst, b + 3), i), &
               [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, b + 3), vs_get(vst, b + 4)]])
          if (tctx%has_error) then
             call vs_leave(vst, b); return
          end if
          v = gcv_conj(vs_get(vst, b + 4), v, &
               [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, b + 3), vs_get(vst, b + 4), v]])
          call vs_set(vst, b + 4, v)
       end do
       call ast_put(b, roots, "children", vs_get(vst, b + 4))
    end if
    ! A CONSTANT's value is handed over as it is: it is data, not a
    ! tree, and walking it would rebuild collections and could force a
    ! seq. Every other p-slot is walked, because a fn hides its
    ! arity bodies inside a plain vector template.
    if (gc_i1(vs_get(vst, b + 1)) == N_CONST) then
       call ast_put(b, roots, "p1", gc_slot(vs_get(vst, b + 1), 2))
       ! A folded BUILTIN says which one it is. Analysis puts the
       ! function itself in the head of (+ i 1), and it is a fresh
       ! object each time, so a generator cannot recognise + by
       ! identity; the name in its slot 1 is stable.
       if (gc_kind(strip_meta(gc_slot(vs_get(vst, b + 1), 2))) == OBJ_BUILTIN) then
          call ast_put(b, roots, "builtin", &
               gc_slot(strip_meta(gc_slot(vs_get(vst, b + 1), 2)), 1))
       end if
    else
       call ast_put(b, roots, "p1", ast_walk(gc_slot(vs_get(vst, b + 1), 2), &
            [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2)]]))
    end if
    call ast_put(b, roots, "p2", ast_walk(gc_slot(vs_get(vst, b + 1), 3), &
         [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2)]]))
    ! THE NODE ITSELF, so a generator can hand an unhandled subtree
    ! back to the interpreter. The exported map is a copy; without
    ! this the original node is not reachable from Clojure at all,
    ! and the escape hatch would have nothing to run.
    call ast_put(b, roots, "node", vs_get(vst, b + 1))
    call ast_put(b, roots, "i2", gc_int(int(gc_i2(vs_get(vst, b + 1)), gc_ip)))
    call ast_put(b, roots, "pos", gc_slot(vs_get(vst, b + 1), 4))
    out = vs_get(vst, b + 2)
    call vs_leave(vst, b)
  end function ast_data

  ! A node, or a collection that might hold one. N_FN's p1 is the
  ! template vector [name arities captures nslots selfslot slotnames],
  ! and each arity's body node sits inside it, so exporting only
  ! direct AST slots showed a function with no body at all.
  recursive function ast_walk(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, e, m
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: b, i
    vst => gc_my_stack()
    tctx => ctx_self()
    out = v
    if (gc_kind(v) == OBJ_AST) then
       out = ast_data(v, roots)
       return
    end if
    if (gcv_is(v)) then
       b = vs_enter(vst, 2)
       call vs_set(vst, b + 1, v)
       out = gcv_empty([roots, [vs_get(vst, b + 1)]])
       call vs_set(vst, b + 2, out)
       do i = 0, gcv_count(vs_get(vst, b + 1)) - 1
          e = ast_walk(gcv_nth(vs_get(vst, b + 1), i), &
               [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2)]])
          if (tctx%has_error) then
             call vs_leave(vst, b); return
          end if
          out = gcv_conj(vs_get(vst, b + 2), e, &
               [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), e]])
          call vs_set(vst, b + 2, out)
       end do
       out = vs_get(vst, b + 2)
       call vs_leave(vst, b)
       return
    end if
    if (gca_is(v)) then
       b = vs_enter(vst, 3)
       call vs_set(vst, b + 1, v)
       call gca_entries(vs_get(vst, b + 1), ks, vls)
       out = gca_empty([roots, [vs_get(vst, b + 1)]])
       call vs_set(vst, b + 2, out)
       do i = 1, size(ks)
          e = ast_walk(vls(i), [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2)]])
          if (tctx%has_error) then
             call vs_leave(vst, b); return
          end if
          call vs_set(vst, b + 3, e)
          m = gca_assoc(vs_get(vst, b + 2), ks(i), vs_get(vst, b + 3), &
               [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, b + 3)]])
          call vs_set(vst, b + 2, m)
       end do
       out = vs_get(vst, b + 2)
       call vs_leave(vst, b)
       return
    end if
  end function ast_walk

  ! assoc one key into the map ast_data is building at b + 2. The
  ! keyword and the value are allocated one at a time and each lands
  ! on the stack before the next allocation, which is the rule two
  ! allocations in one argument list broke (NOTES.md).
  subroutine ast_put(b, roots, k, v)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: b
    type(gc_value), intent(in) :: roots(:)
    character(len=*), intent(in) :: k
    type(gc_value), intent(in) :: v
    type(gc_value) :: kw, m
    integer :: kb
    vst => gc_my_stack()
    kb = vs_enter(vst, 2)
    call vs_set(vst, kb + 1, v)
    kw = gc_key(k, [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, kb + 1)]])
    call vs_set(vst, kb + 2, kw)
    m = gca_assoc(vs_get(vst, b + 2), vs_get(vst, kb + 2), vs_get(vst, kb + 1), &
         [roots, [vs_get(vst, b + 1), vs_get(vst, b + 2), vs_get(vst, kb + 1), vs_get(vst, kb + 2)]])
    call vs_set(vst, b + 2, m)
    call vs_leave(vst, kb)
  end subroutine ast_put

  ! UUID/fromString and parse-uuid. A UUID is its TEXT here
  ! (DEVIATIONS 12: java.util.UUID is not a type clotran has), so
  ! this checks the shape and answers the string; a string that is
  ! not one raises, which is what parse-uuid catches to nil.
  function uuid_of(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    character(len=:), allocatable :: u
    integer :: i
    logical :: okuuid
    out = gc_nil()
    u = text_of(strip_meta(v))
    okuuid = (len(u) == 36)
    if (okuuid) then
       do i = 1, 36
          if (i == 9 .or. i == 14 .or. i == 19 .or. i == 24) then
             if (u(i:i) /= "-") okuuid = .false.
          else if (.not. ((u(i:i) >= "0" .and. u(i:i) <= "9") .or. &
               (u(i:i) >= "a" .and. u(i:i) <= "f") .or. &
               (u(i:i) >= "A" .and. u(i:i) <= "F"))) then
             okuuid = .false.
          end if
       end do
    end if
    if (okuuid) then
       out = gc_str(u, roots)
    else
       call raise_class("IllegalArgumentException", "Invalid UUID string: " // u, roots)
    end if
  end function uuid_of

  ! A SET holding a vector's elements. Same two lines B_SET runs;
  ! a set IS a map from each element to itself.
  function set_of_vector(vec, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: vec
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, mp
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, vec)
    mp = gca_empty([roots, [vs_get(vst, base + 1)]])
    call vs_set(vst, base + 2, mp)
    do i = 0, gcv_count(vs_get(vst, base + 1)) - 1
       mp = gca_assoc(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), &
            gcv_nth(vs_get(vst, base + 1), i), [roots, [vs_get(vst, base + 1), vs_get(vst, base + 2)]])
       call vs_set(vst, base + 2, mp)
    end do
    out = gc_obj(OBJ_SET, [vs_get(vst, base + 2)], [roots, [vs_get(vst, base + 2)]])
    call vs_leave(vst, base)
  end function set_of_vector

  ! Every #tag marker in a value replaced by what its data reader
  ! answers, innermost first -- which is the order Clojure's reader
  ! applies them in, since it reads the inner form before the outer
  ! tag can see it.
  !
  ! The tag is looked for in opts :readers, then among the readers
  ! EDN has built in, then opts :default (called with tag and form).
  ! A tag nothing answers is an error, as EdnReader raises one.
  recursive function resolve_tags(v, opts, roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: v, opts
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, tag, form, fn, av
    integer :: base, i
    vst => gc_my_stack()
    tctx => ctx_self()
    out = v
    if (tctx%has_error) return
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, v)
    call vs_set(vst, base + 2, opts)
    if (is_tagged_literal(vs_get(vst, base + 1))) then
       tag = gca_get(vs_get(vst, base + 1), gc_key("tag", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       call vs_set(vst, base + 3, tag)
       form = gca_get(vs_get(vst, base + 1), gc_key("form", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       call vs_set(vst, base + 4, form)
       form = resolve_tags(vs_get(vst, base + 4), vs_get(vst, base + 2), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       if (tctx%has_error) then
          call vs_leave(vst, base); return
       end if
       call vs_set(vst, base + 4, form)
       fn = gca_get(gca_get(vs_get(vst, base + 2), &
            gc_key("readers", [vs_get(vst, base + 1), vs_get(vst, base + 2)])), vs_get(vst, base + 3))
       call vs_set(vst, base + 5, fn)
       if (tag_of(vs_get(vst, base + 5)) /= GCT_NIL) then
          av = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 5)])
          call vs_set(vst, base + 6, av)
          av = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 4), &
               [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 5), vs_get(vst, base + 6)])
          call vs_set(vst, base + 6, av)
          out = apply(vs_get(vst, base + 5), vs_get(vst, base + 6))
       else if (name_part(vs_get(vst, base + 3)) == "uuid") then
          ! EDN has uuid built in. A UUID is its text here
          ! (DEVIATIONS 12), which is what parse-uuid answers too.
          out = uuid_of(vs_get(vst, base + 4), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       else
          fn = gca_get(vs_get(vst, base + 2), gc_key("default", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
          call vs_set(vst, base + 5, fn)
          if (tag_of(vs_get(vst, base + 5)) /= GCT_NIL) then
             av = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 5)])
             call vs_set(vst, base + 6, av)
             av = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 3), &
                  [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 5), vs_get(vst, base + 6)])
             call vs_set(vst, base + 6, av)
             av = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 4), &
                  [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 5), vs_get(vst, base + 6)])
             call vs_set(vst, base + 6, av)
             out = apply(vs_get(vst, base + 5), vs_get(vst, base + 6))
          else
             call raise_class("RuntimeException", "No reader function for tag " // &
                  name_part(vs_get(vst, base + 3)), [vs_get(vst, base + 1)])
             out = gc_nil()
          end if
       end if
       call vs_leave(vst, base)
       return
    end if
    ! Not a marker: walk the collections, since a tag can be nested.
    if (gcv_is(vs_get(vst, base + 1))) then
       av = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 6, av)
       do i = 0, gcv_count(vs_get(vst, base + 1)) - 1
          av = resolve_tags(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2), &
               [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 6)])
          if (tctx%has_error) then
             call vs_leave(vst, base); return
          end if
          call vs_set(vst, base + 5, av)
          av = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 5), &
               [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 5), vs_get(vst, base + 6)])
          call vs_set(vst, base + 6, av)
       end do
       out = vs_get(vst, base + 6)
    else if (gca_is(vs_get(vst, base + 1))) then
       block
         type(gc_value), allocatable :: ks(:), vls(:)
         type(gc_value) :: m, kk, vv
         call gca_entries(vs_get(vst, base + 1), ks, vls)
         m = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 6, m)
         do i = 1, size(ks)
            kk = resolve_tags(ks(i), vs_get(vst, base + 2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 6)])
            if (tctx%has_error) then
               call vs_leave(vst, base); return
            end if
            call vs_set(vst, base + 4, kk)
            vv = resolve_tags(vls(i), vs_get(vst, base + 2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 6)])
            if (tctx%has_error) then
               call vs_leave(vst, base); return
            end if
            call vs_set(vst, base + 5, vv)
            m = gca_assoc(vs_get(vst, base + 6), vs_get(vst, base + 4), vs_get(vst, base + 5), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4), vs_get(vst, base + 5), vs_get(vst, base + 6)])
            call vs_set(vst, base + 6, m)
         end do
         out = vs_get(vst, base + 6)
       end block
    else if (gc_kind(vs_get(vst, base + 1)) == OBJ_SET .or. &
         gc_kind(vs_get(vst, base + 1)) == OBJ_CONS) then
       block
         type(gc_value) :: sq, e
         sq = to_seq(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, base + 3, sq)
         av = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
         call vs_set(vst, base + 6, av)
         do while (tag_of(vs_get(vst, base + 3)) /= GCT_NIL)
            e = resolve_tags(sq_first(vs_get(vst, base + 3), [vs_get(vst, base + 3)]), vs_get(vst, base + 2), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 6)])
            if (tctx%has_error) then
               call vs_leave(vst, base); return
            end if
            call vs_set(vst, base + 5, e)
            av = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 5), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 5), vs_get(vst, base + 6)])
            call vs_set(vst, base + 6, av)
            sq = to_seq(sq_rest(vs_get(vst, base + 3), [vs_get(vst, base + 3)]), [vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, sq)
         end do
         if (gc_kind(vs_get(vst, base + 1)) == OBJ_SET) then
            out = set_of_vector(vs_get(vst, base + 6), [vs_get(vst, base + 1), vs_get(vst, base + 6)])
         else
            out = seq_to_list(vs_get(vst, base + 6), [vs_get(vst, base + 1), vs_get(vst, base + 6)])
         end if
       end block
    end if
    call vs_leave(vst, base)
  end function resolve_tags

  ! Compiler.munge: every character CHAR_MAP names replaced by its
  ! escape, everything else left alone.
  function munge_text(s) result(o)
    character(len=*), intent(in) :: s
    character(len=:), allocatable :: o
    integer :: i, j
    o = ""
    outer: do i = 1, len(s)
       do j = 1, size(MUNGE_CH)
          if (s(i:i) == MUNGE_CH(j)) then
             o = o // trim(MUNGE_ESC(j))
             cycle outer
          end if
       end do
       o = o // s(i:i)
    end do outer
  end function munge_text

  ! Compiler.demunge: the escapes read back, longest match first,
  ! plus the $ a nested class name carries standing for a slash.
  function demunge_text(s) result(o)
    character(len=*), intent(in) :: s
    character(len=:), allocatable :: o, e
    integer :: i, j, n
    logical :: hit
    o = ""
    i = 1
    n = len(s)
    do while (i <= n)
       if (s(i:i) == "$") then
          o = o // "/"
          i = i + 1
          cycle
       end if
       hit = .false.
       do j = 2, size(MUNGE_ESC)
          e = trim(MUNGE_ESC(j))
          if (i + len(e) - 1 <= n) then
             if (s(i:i+len(e)-1) == e) then
                o = o // MUNGE_CH(j)
                i = i + len(e)
                hit = .true.
                exit
             end if
          end if
       end do
       if (hit) cycle
       if (s(i:i) == "_") then
          o = o // "-"
       else
          o = o // s(i:i)
       end if
       i = i + 1
    end do
  end function demunge_text

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




  ! --- evaluation contexts ---------------------------------------------

  ! Context 1 is the one the program started in; it exists as soon as
  ! anything asks.
  subroutine ctx_ensure_main()
    logical :: ok
    if (n_ctx > 0) return
    if (.not. ctx_key_made) then
       if (.not. th_key_create(ctx_key)) error stop "clotran: no thread key for the evaluator's contexts"
       ctx_key_made = .true.
    end if
    allocate(ctxs(8))
    allocate(ctxs(1)%c)
    ctxs(1)%c%id = 1
    ok = th_cond_init(ctxs(1)%c%turn)
    n_ctx = 1
    ok = th_key_set(ctx_key, c_loc(ctxs(1)%c))
  end subroutine ctx_ensure_main

  ! This thread's context. The first call, on the main thread, makes the
  ! main context; a thread clotran did not start has none.
  function ctx_self() result(c)
    type(eval_ctx), pointer :: c
    type(c_ptr) :: p
    if (n_ctx == 0) call ctx_ensure_main()
    p = th_key_get(ctx_key)
    if (.not. c_associated(p)) error stop "clotran: the evaluator called on a thread with no context"
    call c_f_pointer(p, c)
  end function ctx_self

  ! A fresh context: empty stacks, no error, no bindings, its own root
  ! slots for the thrown value and the binding stack.
  function gce_ctx_new() result(id)
    integer :: id
    type(ctx_ref), allocatable :: bigger(:)
    integer :: n
    call ctx_ensure_main()
    if (n_free_ctx > 0) then
       ! one a finished task gave back, already emptied (ctx_release)
       id = free_ctx(n_free_ctx)
       n_free_ctx = n_free_ctx - 1
       return
    end if
    if (n_ctx >= size(ctxs)) then
       n = size(ctxs)
       allocate(bigger(2 * n))
       bigger(1:n) = ctxs(1:n)
       call move_alloc(bigger, ctxs)
    end if
    n_ctx = n_ctx + 1
    id = n_ctx
    allocate(ctxs(id)%c)   ! default-initialised
    ctxs(id)%c%id = id
    if (.not. th_cond_init(ctxs(id)%c%turn)) error stop "clotran: no condition for a new context"
    ctxs(id)%c%last_error = ""
    ctxs(id)%c%last_trace = ""
    call gc_stack_new(id)
  end function gce_ctx_new

  integer function gce_ctx_current()
    type(eval_ctx), pointer :: c
    c => ctx_self()
    gce_ctx_current = c%id
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
    type(eval_ctx), pointer :: c
    logical :: ok
    c => ctx_self()
    if (id == c%id .or. id < 1 .or. id > n_ctx) return
    call gc_stack_bind(id)
    ok = th_key_set(ctx_key, c_loc(ctxs(id)%c))
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
    integer :: i
    if (allocated(ctxs)) then
       do i = 1, n_ctx
          if (associated(ctxs(i)%c)) deallocate(ctxs(i)%c)
       end do
       deallocate(ctxs)
    end if
    n_ctx = 0
    handler_ctx = 0
    in_handler = .false.
    resume_pending = .false.
    step_at = 0
    repl_depth = 0
    n_free_ctx = 0
    call gc_stacks_reset()
  end subroutine ctx_reset

  ! A finished task's context, emptied and kept for the next one, so a
  ! pmap over ten thousand elements does not hold ten thousand stacks.
  subroutine ctx_release(id)
    integer, intent(in) :: id
    integer, allocatable :: bigger(:)
    if (id < 1 .or. id > n_ctx) return
    ! never the context this thread is running
    if (c_associated(th_key_get(ctx_key), c_loc(ctxs(id)%c))) return
    if (allocated(ctxs(id)%c%kst)) deallocate(ctxs(id)%c%kst)
    if (allocated(ctxs(id)%c%fstack_fn)) deallocate(ctxs(id)%c%fstack_fn, ctxs(id)%c%fstack_site)
    ctxs(id)%c%ksp = 0
    ctxs(id)%c%fstack_top = 0
    ctxs(id)%c%pending_site = 0
    ctxs(id)%c%ev_depth = 0
    ctxs(id)%c%has_error = .false.
    ctxs(id)%c%last_error = ""
    ctxs(id)%c%last_trace = ""
    call gc_stack_new(id)
    if (.not. allocated(free_ctx)) allocate(free_ctx(16))
    if (n_free_ctx >= size(free_ctx)) then
       allocate(bigger(2 * size(free_ctx)))
       bigger(1:n_free_ctx) = free_ctx(1:n_free_ctx)
       call move_alloc(bigger, free_ctx)
    end if
    n_free_ctx = n_free_ctx + 1
    free_ctx(n_free_ctx) = id
  end subroutine ctx_release

  include "analyze.inc"
  include "exec.inc"
  include "repl.inc"
  include "tasks.inc"
  include "sorted.inc"

end module Eval

! GCEval: a core evaluator over the GC heap.
!
! The last of the standalone modules, and the one that answers the
! question the whole port rests on: does rooting BY CONSTRUCTION
! actually hold up under real evaluation? Everything before this was
! data structures, where the roots are obvious. An evaluator is where
! they are not -- intermediate values live across recursive calls,
! each of which can allocate and therefore collect.
!
! Nothing uses this yet. It is not a port of Eval.f90: it is the core
! of one -- enough special forms and primitives to run real programs
! and prove the mechanism, deliberately not the ~5400 lines of the
! full evaluator. What it has:
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
module GCEval
  use GC
  use GCList
  use GCVector
  use GCAssoc
  use GCEnv
  use GCNamespace
  use GCPrinter
  use GCNativeArray
  use Regex
  use GCReader
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
  integer, parameter :: B_ISWS = 151, B_ISUPPER = 152, B_ISLOWER = 153
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

  public :: gce_eval, gce_base_env, gce_has_error, gce_error, gce_clear_error
  public :: gce_analyze

contains

  ! Cleared by the CALLER before a top-level evaluation, not by
  ! gce_eval itself: gce_eval is recursive, so clearing on entry would
  ! wipe an error raised deeper in the same evaluation. A REPL clears,
  ! evaluates, then checks -- which is exactly this shape.
  subroutine gce_clear_error()
    has_error = .false.
    last_error = ""
    call set_thrown(gc_nil())
  end subroutine gce_clear_error

  ! Re-checks the slot rather than trusting the index, for the same
  ! reason GCList's empty-list singleton does: gc_init clears the
  ! global-root registry but this module variable survives it.
  subroutine set_thrown(v)
    type(gc_value), intent(in) :: v
    call gc_global_keep(thrown_root, v)
  end subroutine set_thrown

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
  end subroutine fail

  ! An environment with the primitives bound. Built fresh rather than
  ! cached in a module variable: a cached handle would go stale across
  ! gc_init, which is exactly the singleton bug GCList's check 4c
  ! caught.
  function gce_base_env(roots) result(env)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: env, core
    integer :: base

    ! A fresh heap means every array handle from a previous one is
    ! orphaned; this is the one place that always follows gc_init.
    call gcna_reset()
    call gcp_set_forcer(gce_force)
    ! The sweep tells us when an object owning out-of-heap storage
    ! dies, so a native array's buffer is freed exactly once rather
    ! than leaking for the life of the process.
    call gc_set_finalizer(gce_finalize_obj)
    call gcn_reset(roots)
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
    end block
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
  subroutine bind_var(ns, name, val)
    type(gc_value), intent(in) :: ns, val
    character(len=*), intent(in) :: name
    type(gc_value) :: sym, var
    integer :: base
    base = vs_enter(2)
    call vs_set(base + 1, ns)
    call vs_set(base + 2, val)
    sym = gc_sym(name, [vs_get(base + 1), vs_get(base + 2)])
    var = gcn_intern(vs_get(base + 1), sym, vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 2), sym])
    call gc_set_i1(var, 1)
    call vs_leave(base)
  end subroutine bind_var

  subroutine bind_builtin(ns, name, id, is_macro)
    type(gc_value), intent(in) :: ns
    character(len=*), intent(in) :: name
    integer, intent(in) :: id
    logical, intent(in), optional :: is_macro
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
       if (is_macro) call var_set_macro(var, gc_nil())
    end if
    call vs_leave(base)
  end subroutine bind_builtin

  ! ---- evaluation ----

  ! A DEPTH GUARD on evaluation. Clojure gets a StackOverflowError it
  ! can report; a Fortran stack overflow is a bare segfault with the
  ! output buffer unflushed, so runaway recursion has to be caught
  ! before the stack goes rather than after.
  recursive function gce_eval(form, env, roots) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, head
    integer :: base
    logical :: found

    out = gc_nil()
    if (has_error) return

    if (ev_limit == 0) call read_depth_limit()
    ev_depth = ev_depth + 1
    if (ev_depth > ev_limit) then
       call fail("stack overflow near (" // first_form_name(form) // " ...)")
       ev_depth = ev_depth - 1
       return
    end if

    ! Slot 1 = the form, 2 = the env: both must survive every
    ! allocation below, and neither can be left in a Fortran local.
    base = vs_enter(4)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)

    select case (form%tag)
    case (GCT_SYM)
       ! Lexical scope first, then the namespace. A local shadows a
       ! Var of the same name, which is what makes (let [map ...])
       ! legal rather than a redefinition of clojure.core/map.
       found = gce_find(env, form, out)
       if (.not. found) then
          ! The ENV, not the form: resolve_var consults the namespace
          ! the enclosing closure was defined in, which lives in a frame.
          head = resolve_var(form, vs_get(base + 2))
          if (gcn_is_var(head)) then
             ! A bare symbol auto-derefs its Var, matching Clojure --
             ! #'x is how you ask for the Var itself.
             out = gcn_var_value(head)
             found = .true.
          end if
       end if
       if (.not. found) then
          ! A CLASS LITERAL, tried last, exactly where maybeClass sits:
          ! after locals and Vars have both missed. clotran's classes
          ! are its own type tags, so the literal evaluates to the
          ! keyword that names one -- (instance? clojure.lang.Symbol x)
          ! and (= :symbol (clotran-type x)) are then the same question
          ! asked twice.
          if (is_class_name(form)) then
             ! java.lang is implicitly imported, so Object and
             ! java.lang.Object are the SAME class -- and must be the
             ! same keyword, or a protocol extended to one is invisible
             ! to a lookup for the other. core/protocols extends
             ! CollReduce to Object and InternalReduce to
             ! java.lang.Object, and find-protocol-impl falls back to
             ! (impl Object) for both.
             out = gc_key(short_class_name(gc_ref_text(form%ref)), &
                  [vs_get(base + 1)])
             found = .true.
          else if (is_static_call(form)) then
             ! Class/member in VALUE position -- a static FIELD, not a
             ! call. clojure.lang.Compiler/LOADER is read that way, as a
             ! map key, by the with-loading-context every (ns ...)
             ! expands into.
             block
               character(len=:), allocatable :: t
               integer :: sl
               t = gc_ref_text(form%ref)
               sl = index(t, "/")
               out = static_member(t(1:sl-1), t(sl+1:), vs_get(base + 1))
               found = .not. has_error
               if (has_error) call gce_clear_error()
             end block
          end if
       end if
       if (.not. found) call fail("'" // gc_ref_text(form%ref) // "' not found")
    case (GCT_OBJ)
       select case (gc_kind(form))
       case (OBJ_LAZY, OBJ_SEQ)
          ! A SEQ IS A CALL. Compiler.eval dispatches on ISeq, not on
          ! one concrete list class, and it has to: a macro assembles
          ! its expansion with cons and seq, so what comes back is a
          ! lazy cell or a view over a vector, never a PersistentList.
          ! Evaluating only OBJ_CONS made every such expansion
          ! self-evaluate silently -- defmacro built the right form and
          ! nothing ran it.
          !
          ! Realised into a list rather than teaching eval_call to walk
          ! any seq: it happens once per expansion, off the hot path.
          out = gce_eval(seq_to_list(form, [vs_get(base + 1)]), env, &
               [vs_get(base + 1)])
       case (OBJ_CONS)
          if (gcl_count(form) == 0) then
             out = form
          else
             head = strip_meta(gcl_first(form))
             if (head%tag == GCT_SYM .and. is_member_sym(head)) then
                out = eval_member(form, env)
             else if (head%tag == GCT_SYM .and. is_static_call(head)) then
                out = eval_static(form, env)
             else if (head%tag == GCT_SYM .and. is_ctor_sym(head)) then
                out = eval_ctor(form, env)
             else if (head%tag == GCT_SYM .and. is_special(head)) then
                out = eval_special(form, env)
             else
                out = eval_call(form, env)
             end if
          end if
       case (OBJ_META)
          ! Metadata is information ABOUT a form, not part of what it
          ! evaluates to, so evaluation sees straight through the
          ! wrapper. Only def (and `meta`) look at it. Keeping the
          ! unwrap here is what stops OBJ_META leaking into every
          ! special form and builtin.
          out = gce_eval(gc_slot(form, 1), env, [vs_get(base + 1)])
       case (OBJ_VECTOR)
          out = eval_vector(form, env)
       case (OBJ_MAP, OBJ_HAMT)
          out = eval_map(form, env)
       case (OBJ_SET)
          out = eval_set(form, env)
       case default
          out = form ! closures, builtins, vars: self-evaluating
       end select
    case default
       out = form ! nil, bool, int, real, char, string, keyword
    end select

    call vs_leave(base)
    ev_depth = ev_depth - 1
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
          gc_ref_is(sym%ref, "var")
  end function is_special

  recursive function eval_special(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, rest, a, b
    logical :: has_value
    integer :: base

    out = gc_nil()
    head = strip_meta(gcl_first(form))
    base = vs_enter(4)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    rest = gcl_rest(form, [vs_get(base + 1)])
    call vs_set(base + 3, rest)

    if (gc_ref_is(head%ref, "quote")) then
       out = gcl_first(vs_get(base + 3))

    else if (gc_ref_is(head%ref, "if")) then
       a = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (has_error) then
          call vs_leave(base); return
       end if
       rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, rest)
       if (truthy(a)) then
          out = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       else
          rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
          call vs_set(base + 3, rest)
          if (gcl_count(vs_get(base + 3)) > 0) then
             out = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
          end if
       end if

    else if (gc_ref_is(head%ref, "do")) then
       do while (gcl_count(vs_get(base + 3)) > 0)
          out = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
          if (has_error) exit
          rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
          call vs_set(base + 3, rest)
       end do

    else if (gc_ref_is(head%ref, "def")) then
       ! Interns in the CURRENT NAMESPACE, not the enclosing frame --
       ! (let [] (def x 1)) really does define x at the top level,
       ! which is Clojure's behaviour and was the one divergence this
       ! evaluator had before namespaces existed.
       a = gcl_first(vs_get(base + 3))
       call vs_set(base + 4, a)
       rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, rest)
       has_value = (gcl_count(vs_get(base + 3)) > 0)
       b = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (.not. has_error) then
          block
            type(gc_value) :: nm, md, var
            integer :: db
            ! The name may arrive wrapped: (def ^{:macro true} let ...).
            nm = vs_get(base + 4)
            md = gc_nil()
            if (gc_kind(nm) == OBJ_META) then
               md = gc_slot(nm, 2)
               nm = strip_meta(nm)
            end if
            call vs_set(base + 4, nm)
            ! Var metadata is EVALUATED. Compiler.DefExpr analyses the
            ! meta map as an expression, and core.clj is written for
            ! that: defn quotes its :arglists -- (list 'quote (sigs
            ! fdecl)) -- precisely because the list would otherwise be
            ! CALLED. Storing it raw made (:test (meta #'t)) a list
            ! rather than a function, which is every clojure.test
            ! deftest, since deftest puts (fn [] body) there.
            db = vs_enter(2)
            call vs_set(db + 1, b)
            call vs_set(db + 2, md)
            if (md%tag /= GCT_NIL) then
               md = gce_eval(vs_get(db + 2), vs_get(base + 2), &
                    [vs_get(base + 1), vs_get(db + 1)])
               call vs_set(db + 2, md)
            end if
            if (has_error) then
               call vs_leave(db)
               call vs_leave(base)
               return
            end if
            var = gcn_intern(gcn_current([vs_get(base + 1)]), &
                 vs_get(base + 4), vs_get(db + 1), &
                 [vs_get(base + 1), vs_get(base + 4), vs_get(db + 2)])
            md = vs_get(db + 2)
            call vs_leave(db)
            ! Nothing more to do for (def ^{:macro true} let ...):
            ! putting the metadata on the Var IS declaring the macro,
            ! because that is where macro-ness is read from. core.clj
            ! defines let, loop and fn exactly this way, at its line 32.
            if (md%tag /= GCT_NIL) call gc_set_slot(var, 2, md)
            ! i1 marks a ROOT BINDING. (def x) with no value interns the
            ! Var and leaves it unbound -- Var's own constructor sets
            ! root to an Unbound -- and defmulti turns on exactly that:
            ! (let [v# (def name)] (when-not (.hasRoot v#) ...)).
            if (has_value) call gc_set_i1(var, 1)
            ! def evaluates to the VAR, not to the value. defmulti is
            ! written around it.
            out = var
          end block
       end if

    else if (gc_ref_is(head%ref, "let*")) then
       out = eval_let(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "letfn*")) then
       out = eval_letfn(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "fn*")) then
       out = make_closure(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "loop*")) then
       out = eval_loop(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "recur")) then
       out = eval_recur(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "var")) then
       ! The Var itself, undereferenced -- what #'x means, and what a
       ! caller needs to hold a stable reference across redefinition.
       ! The name can arrive hinted -- (. (var ^{:private true} x)
       ! (setMacro)) is what defmacro expands to for a private macro.
       out = resolve_var(strip_meta(gcl_first(vs_get(base + 3))), vs_get(base + 1))
       if (.not. gcn_is_var(out)) &
            call fail("Unable to resolve var: " // &
            gc_ref_text(nth_sym_ref(vs_get(base + 3))))

    else if (gc_ref_is(head%ref, "lazy-seq*")) then
       ! (lazy-seq* body) captures the body in a no-argument closure
       ! and hands back an unrealised node. Nothing of the body runs
       ! until something asks for the seq's first element, which is
       ! the entire point: (iterate inc 0) is a finite object.
       a = gc_obj(OBJ_CLOSURE, &
            [gcv_empty([vs_get(base + 1)]), vs_get(base + 3), vs_get(base + 2), gc_nil()], &
            [vs_get(base + 1), vs_get(base + 2)])
       out = gc_obj(OBJ_LAZY, [a, gc_nil(), gc_nil()], [vs_get(base + 1), a])
       call gc_set_i1(out, LAZY_PENDING)

    else if (gc_ref_is(head%ref, "throw")) then
       a = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (.not. has_error) then
          call set_thrown(a)
          has_error = .true.
          ! The message carries the thrown value. "thrown" on its own
          ! told a caller nothing, which made every assertion in
          ! core.clj look identical.
          last_error = gcp_str(a, .true.)
       end if

    else if (gc_ref_is(head%ref, "try")) then
       out = eval_try(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "case*")) then
       out = eval_case(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "deftype*")) then
       out = eval_deftype(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "reify*")) then
       out = eval_reify(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "quasiquote")) then
       ! Expand to ordinary cons/concat calls, then evaluate those.
       ! Syntax-quote is a source transformation, not a runtime thing,
       ! which is why it becomes a form rather than a value here.
       if (qq_depth == 0) call gc_global_keep(gensym_root, &
            gca_empty([vs_get(base + 1), vs_get(base + 2)]))
       qq_depth = qq_depth + 1
       a = qq_expand(gcl_first(vs_get(base + 3)), vs_get(base + 2))
       qq_depth = qq_depth - 1
       if (.not. has_error) out = gce_eval(a, vs_get(base + 2), [vs_get(base + 1)])

    else if (gc_ref_is(head%ref, "clojure.core/import*")) then
       ! Spelled qualified because that is its actual name:
       ! Symbol.intern("clojure.core", "import*") in the specials
       ! table, and core.clj emits it that way. The only special form
       ! with a namespace.
       !
       ! A NO-OP, and honestly so. import binds a short class name to a
       ! package-qualified one in the namespace; clotran recognises a
       ! class by the SHAPE of its name (is_class_name), so there is
       ! nothing to bind. Kept as a special form rather than left to
       ! fail, because core.clj imports at its top and every form after
       ! that would be lost.
       out = gc_nil()

    else if (gc_ref_is(head%ref, "set!")) then
       ! (set! var-or-symbol value). Clojure only permits this on a Var
       ! with a thread-local binding, or a host field; with one thread
       ! and one global binding stack there is nothing to distinguish,
       ! so it sets the Var. DEVIATIONS.md 11.
       block
         type(gc_value) :: tgt, val
         tgt = strip_meta(gcl_first(vs_get(base + 3)))
         if (tgt%tag == GCT_SYM) then
            tgt = resolve_var(tgt, vs_get(base + 1))
         else
            tgt = gce_eval(tgt, vs_get(base + 2), [vs_get(base + 1)])
         end if
         if (has_error) then
            call vs_leave(base)
            return
         end if
         call vs_set(base + 4, tgt)
         val = gce_eval(gcl_first(gcl_rest(vs_get(base + 3), [vs_get(base + 1)])), &
              vs_get(base + 2), [vs_get(base + 1), vs_get(base + 4)])
         if (.not. has_error) then
            if (gcn_is_var(vs_get(base + 4)) .or. &
                 gc_kind(vs_get(base + 4)) == OBJ_ATOM) then
               call gc_set_slot(vs_get(base + 4), 1, val)
               out = val
            else if (is_cache_field(gcl_first(vs_get(base + 3)))) then
               ! (set! (.__methodImplCache f) cache) -- the one host
               ! field with real storage behind it, in the closure
               ! slot a single-arity fn does not use.
               block
                 type(gc_value) :: tf
                 tf = strip_meta(gce_eval(gcl_first(gcl_rest( &
                      strip_meta(gcl_first(vs_get(base + 3))), &
                      [vs_get(base + 1)])), vs_get(base + 2), &
                      [vs_get(base + 1)]))
                 if (gc_kind(tf) == OBJ_CLOSURE) call gc_set_slot(tf, 5, val)
                 out = val
               end block
            else if (gcl_is(strip_meta(gcl_first(vs_get(base + 3))))) then
               ! (set! (.field obj) v) -- a HOST FIELD. The only one
               ! clotran models is the protocol dispatch cache, which
               ! has no storage, so the write is discarded and the
               ! value returned. A bare symbol that is not a Var is
               ! still an error, so this does not swallow a typo.
               out = val
            else
               call fail("set! needs a var")
            end if
         end if
       end block

    else if (gc_ref_is(head%ref, "new")) then
       out = eval_new(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, ".")) then
       out = eval_dot(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "defmacro*")) then
       a = gcl_first(vs_get(base + 3))
       call vs_set(base + 4, a)
       rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, rest)
       b = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (.not. has_error) then
          if (gc_kind(b) /= OBJ_CLOSURE) then
             call fail("defmacro* needs a function")
          else
             ! def plus setMacro, which is all defmacro is in core.clj
             ! too -- it just cannot say so until it exists.
             block
               type(gc_value) :: var
               var = gcn_intern(gcn_current([vs_get(base + 1)]), vs_get(base + 4), &
                    b, [vs_get(base + 1), vs_get(base + 4)])
               call var_set_macro(var, vs_get(base + 2))
               out = b
             end block
          end if
       end if
    end if

    call vs_leave(base)
  end function eval_special

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
  recursive function eval_deftype(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, w, cname, k, ty
    integer :: base

    out = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)

    ! Past the tagname (user/Name): it names the VAR core_deftype
    ! builds around this, and the CLASSNAME is what everything here
    ! keys on.
    w = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 3, w)
    cname = strip_meta(gcl_first(vs_get(base + 3)))
    if (cname%tag /= GCT_SYM) then
       call fail("deftype* needs a class name")
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, cname)

    w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 3, w)
    call vs_set(base + 5, strip_meta(gcl_first(vs_get(base + 3))))
    w = gcl_rest(vs_get(base + 3), &
         [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5)])
    call vs_set(base + 3, w)

    ! The options arrive as keyword/value pairs spliced in ahead of
    ! the methods, :implements among them. Only :implements is read;
    ! :load-ns and :no-print have nothing to correspond to here, and
    ! are skipped rather than rejected so a form using them still
    ! loads.
    w = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 6, w)
    do while (gcl_count(vs_get(base + 3)) > 0)
       k = strip_meta(gcl_first(vs_get(base + 3)))
       if (k%tag /= GCT_KEY) exit
       w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 6)])
       call vs_set(base + 3, w)
       if (gc_ref_is(k%ref, "implements")) &
            call vs_set(base + 6, strip_meta(gcl_first(vs_get(base + 3))))
       w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 6)])
       call vs_set(base + 3, w)
    end do

    ty = build_type(class_of_text(vs_get(base + 4)), vs_get(base + 5), &
         vs_get(base + 6), vs_get(base + 3), vs_get(base + 2))
    if (.not. has_error) then
       call vs_set(base + 4, ty)
       call register_type(vs_get(base + 4))
       out = vs_get(base + 4)
    end if
    call vs_leave(base)
  end function eval_deftype

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
  recursive function eval_reify(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, ty
    character(len=24) :: buf
    integer :: base

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    call vs_set(base + 3, strip_meta(gcl_first(vs_get(base + 1))))
    reify_id = reify_id + 1
    write(buf, '(I0)') reify_id
    ty = build_type("clotran.reify__" // trim(buf), &
         gcv_empty([vs_get(base + 1), vs_get(base + 3)]), vs_get(base + 3), &
         gcl_rest(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 3)]), &
         vs_get(base + 2))
    if (.not. has_error) then
       call vs_set(base + 4, ty)
       out = gc_obj(OBJ_INST, &
            [vs_get(base + 4), gcv_empty([vs_get(base + 4)]), gc_nil()], &
            [vs_get(base + 4)])
    end if
    call vs_leave(base)
  end function eval_reify

  ! A type object from its parts, with each method form compiled to a
  ! closure. Methods sharing a NAME become clauses of ONE closure: an
  ! interface method overloaded by arity arrives as several forms, and
  ! select_clause is already how a multi-arity fn picks between them.
  !
  ! Grouped by re-scanning the method list once per distinct name,
  ! which is quadratic in the number of methods. A type has a handful,
  ! and this runs once per deftype rather than once per call.
  recursive function build_type(cname, fields, ifaces, methods, env) result(out)
    character(len=*), intent(in) :: cname
    type(gc_value), intent(in) :: fields, ifaces, methods, env
    type(gc_value) :: out, w, m, mname, tmp
    integer :: base

    out = gc_nil()
    base = vs_enter(9)
    call vs_set(base + 1, fields)
    call vs_set(base + 2, ifaces)
    call vs_set(base + 3, methods)
    call vs_set(base + 4, env)
    tmp = gca_empty([vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 5, tmp)
    call vs_set(base + 6, vs_get(base + 3))

    do while (gcl_count(vs_get(base + 6)) > 0)
       m = strip_meta(gcl_first(vs_get(base + 6)))
       mname = strip_meta(gcl_first(m))
       if (mname%tag == GCT_SYM) then
          tmp = gc_key(gc_ref_text(mname%ref), &
               [vs_get(base + 5), vs_get(base + 6)])
          call vs_set(base + 7, tmp)
          if (.not. gca_contains(vs_get(base + 5), vs_get(base + 7))) then
             tmp = method_clauses(gc_ref_text(mname%ref), vs_get(base + 3), &
                  vs_get(base + 1))
             call vs_set(base + 8, tmp)
             ! Closure FIRST, then assoc. Two allocations as arguments
             ! to one call lets the second collect the first.
             tmp = make_closure(vs_get(base + 8), vs_get(base + 4))
             call vs_set(base + 9, tmp)
             tmp = gca_assoc(vs_get(base + 5), vs_get(base + 7), &
                  vs_get(base + 9), [vs_get(base + 5), vs_get(base + 7), &
                  vs_get(base + 9)])
             call vs_set(base + 5, tmp)
          end if
       end if
       tmp = gcl_rest(vs_get(base + 6), [vs_get(base + 5), vs_get(base + 6)])
       call vs_set(base + 6, tmp)
    end do

    ! The interfaces, normalised to the keyword a class literal
    ! evaluates to, so instance? is a string compare and not a second
    ! naming convention.
    tmp = iface_keys(vs_get(base + 2))
    call vs_set(base + 6, tmp)
    tmp = gc_str(cname, [vs_get(base + 5), vs_get(base + 6)])
    call vs_set(base + 7, tmp)
    out = gc_obj(OBJ_TYPE, [vs_get(base + 7), vs_get(base + 1), &
         vs_get(base + 5), vs_get(base + 6)], &
         [vs_get(base + 1), vs_get(base + 5), vs_get(base + 6), vs_get(base + 7)])
    call vs_leave(base)
  end function build_type

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
          tmp = gc_key(short_class_name(gc_ref_text(s%ref)), &
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
          if (gc_ref_is(mname%ref, name)) then
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
         gc_key(short_class_name(cname), [vs_get(base + 1)]))
    call vs_leave(base)
  end function find_type

  ! (new user.Name f1 f2) for a type deftype* created: the fields in
  ! declaration order, which is the one constructor deftype defines.
  recursive function construct_type(ty, argforms, env) result(out)
    type(gc_value), intent(in) :: ty, argforms, env
    type(gc_value) :: out, item, tmp
    character(len=24) :: want, got
    integer :: base

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, ty)
    call vs_set(base + 2, argforms)
    call vs_set(base + 3, env)
    tmp = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 4, tmp)
    call vs_set(base + 5, vs_get(base + 2))

    do while (gcl_count(vs_get(base + 5)) > 0)
       item = gce_eval(gcl_first(vs_get(base + 5)), vs_get(base + 3), &
            [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5)])
       if (has_error) then
          call vs_leave(base)
          return
       end if
       tmp = gcv_conj(vs_get(base + 4), item, &
            [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5), item])
       call vs_set(base + 4, tmp)
       tmp = gcl_rest(vs_get(base + 5), [vs_get(base + 4), vs_get(base + 5)])
       call vs_set(base + 5, tmp)
    end do

    ! A RECORD TAKES THREE ARITIES. defrecord conjes __meta,
    ! __extmap, __hash and __hasheq onto the declared fields, but
    ! ->Person calls (new Person name age) with only the declared
    ! ones, and .assoc calls it with those plus two. On the JVM those
    ! are extra CONSTRUCTORS: Compiler.java counts trailing fields
    ! named __meta/__extmap/__hash/__hasheq into altCtorDrops and, when
    ! that is non-zero, emits one ctor dropping all of them and one
    ! dropping the last two. Same rule here, by the same names.
    !
    ! The missing fields are filled the way those ctors fill them:
    ! ACONST_NULL for __meta and __extmap, ICONST_0 for the two
    ! hashes -- and the 0 matters, because core_deftype reads them
    ! back as (if (zero? __hasheq) ...recompute... __hasheq), which a
    ! nil would not survive.
    !
    ! A plain deftype has no such trailing fields, so drops is 0 and
    ! the arity stays exact: (Point. 1) on a two-field type is still
    ! an error rather than a silently half-built instance.
    block
      integer :: nf, na, drops
      nf = gcv_count(gc_slot(vs_get(base + 1), 2))
      na = gcv_count(vs_get(base + 4))
      drops = alt_ctor_drops(gc_slot(vs_get(base + 1), 2))
      if (na /= nf) then
         if (drops > 0 .and. (na == nf - drops .or. na == nf - 2)) then
            tmp = pad_record_fields(vs_get(base + 4), &
                 gc_slot(vs_get(base + 1), 2))
            call vs_set(base + 4, tmp)
         else
            write(want, '(I0)') nf
            write(got, '(I0)') na
            call fail(class_text(vs_get(base + 1)) // &
                 " takes " // trim(want) // " fields, given " // trim(got))
            call vs_leave(base)
            return
         end if
      end if
    end block

    out = gc_obj(OBJ_INST, [vs_get(base + 1), vs_get(base + 4), gc_nil()], &
         [vs_get(base + 1), vs_get(base + 4)])
    call vs_leave(base)
  end function construct_type

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
  recursive function eval_let(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, binds, child, k, v
    integer :: base, i, n

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    binds = gcl_first(rest)
    call vs_set(base + 3, binds)
    child = gce_new(env, [vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, child)

    n = gcv_count(vs_get(base + 3))
    if (mod(n, 2) /= 0) then
       call fail("let* needs an even number of binding forms")
       call vs_leave(base)
       return
    end if
    do i = 0, n - 2, 2
       ! The NAME can carry a type hint -- core.clj writes
       ! (let [^clojure.lang.Symbol tag (:tag m)] ...) -- so the wrapper
       ! comes off, exactly as it does for a parameter. Binding the
       ! wrapper makes the local invisible in its own body.
       k = strip_meta(gcv_nth(vs_get(base + 3), i))
       v = gce_eval(gcv_nth(vs_get(base + 3), i + 1), vs_get(base + 4), &
            [vs_get(base + 1), vs_get(base + 3)])
       if (has_error) then
          call vs_leave(base); return
       end if
       call gce_set(vs_get(base + 4), k, v, [vs_get(base + 1), vs_get(base + 3)])
    end do

    ! Body: every form, last value wins.
    binds = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 3, binds)
    do while (gcl_count(vs_get(base + 3)) > 0)
       out = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 4), [vs_get(base + 1)])
       if (has_error) exit
       binds = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, binds)
    end do
    call vs_leave(base)
  end function eval_let

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
  recursive function eval_letfn(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, binds, child, k, v
    integer :: base, i, n

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    binds = gcl_first(rest)
    call vs_set(base + 3, binds)
    child = gce_new(env, [vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, child)

    n = gcv_count(vs_get(base + 3))
    if (.not. gcv_is(vs_get(base + 3))) then
       call fail("letfn* needs a vector of bindings")
       call vs_leave(base)
       return
    end if
    if (mod(n, 2) /= 0) then
       call fail("letfn* needs an even number of binding forms")
       call vs_leave(base)
       return
    end if

    ! Pass one: seed every name.
    do i = 0, n - 2, 2
       k = strip_meta(gcv_nth(vs_get(base + 3), i))
       if (k%tag /= GCT_SYM) then
          call fail("letfn* needs a symbol to bind")
          call vs_leave(base)
          return
       end if
       call gce_set(vs_get(base + 4), k, gc_nil(), &
            [vs_get(base + 1), vs_get(base + 3)])
    end do

    ! Pass two: evaluate each init in the frame that already holds all
    ! of the names.
    do i = 0, n - 2, 2
       k = strip_meta(gcv_nth(vs_get(base + 3), i))
       v = gce_eval(gcv_nth(vs_get(base + 3), i + 1), vs_get(base + 4), &
            [vs_get(base + 1), vs_get(base + 3)])
       if (has_error) then
          call vs_leave(base); return
       end if
       call gce_set(vs_get(base + 4), k, v, [vs_get(base + 1), vs_get(base + 3)])
    end do

    binds = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 3, binds)
    do while (gcl_count(vs_get(base + 3)) > 0)
       out = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 4), [vs_get(base + 1)])
       if (has_error) exit
       binds = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, binds)
    end do
    call vs_leave(base)
  end function eval_letfn

  ! loop* binds like let*, then iterates: evaluate the body, and if it
  ! hands back a recur, rebind the same names from the recur's
  ! arguments and go again. The bindings are rebound in a FRESH frame
  ! each time rather than mutated, so a closure made during one
  ! iteration keeps the values it captured.
  recursive function eval_loop(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, binds, names, child, body, v
    integer :: base, i, n

    out = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    binds = gcl_first(rest)
    call vs_set(base + 3, binds)

    n = gcv_count(vs_get(base + 3))
    if (mod(n, 2) /= 0) then
       call fail("loop* needs an even number of binding forms")
       call vs_leave(base); return
    end if

    ! The names, kept so recur can rebind them by position.
    names = gcv_empty([vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, names)
    do i = 0, n - 2, 2
       names = gcv_conj(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 3), i)), &
            [vs_get(base + 1), vs_get(base + 3)])
       call vs_set(base + 4, names)
    end do

    ! Initial bindings, sequential like let*.
    child = gce_new(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 5, child)
    do i = 0, n - 2, 2
       v = gce_eval(gcv_nth(vs_get(base + 3), i + 1), vs_get(base + 5), &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       if (has_error) then
          call vs_leave(base); return
       end if
       call gce_set(vs_get(base + 5), gcv_nth(vs_get(base + 3), i), v, &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
    end do

    body = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 6, body)

    do
       out = eval_body(vs_get(base + 6), vs_get(base + 5))
       if (has_error) exit
       if (gc_kind(out) /= OBJ_RECUR) exit
       child = rebind(vs_get(base + 4), gc_slot(out, 1), vs_get(base + 2))
       if (has_error) exit
       call vs_set(base + 5, child)
    end do
    call vs_leave(base)
  end function eval_loop

  ! (recur a b) evaluates its arguments and hands back a marker. The
  ! nearest loop* or fn* catches it; anywhere else it simply escapes,
  ! which is a recur outside a recur point and would be a compile
  ! error in real Clojure. Left as a value here rather than diagnosed,
  ! since this evaluator has no compile pass to diagnose it in.
  recursive function eval_recur(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, args, item, walk
    integer :: base

    base = vs_enter(4)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    args = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 3, args)
    walk = vs_get(base + 1)
    call vs_set(base + 4, walk)
    do while (gcl_count(vs_get(base + 4)) > 0)
       item = gce_eval(gcl_first(vs_get(base + 4)), vs_get(base + 2), &
            [vs_get(base + 1), vs_get(base + 3)])
       if (has_error) then
          call vs_leave(base); return
       end if
       args = gcv_conj(vs_get(base + 3), item, [vs_get(base + 1), vs_get(base + 4)])
       call vs_set(base + 3, args)
       walk = gcl_rest(vs_get(base + 4), [vs_get(base + 1)])
       call vs_set(base + 4, walk)
    end do
    out = gc_obj(OBJ_RECUR, [vs_get(base + 3)], [vs_get(base + 1)])
    call vs_leave(base)
  end function eval_recur

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
  function bind_params(params, args, outer, recur_mode) result(child)
    type(gc_value), intent(in) :: params, args, outer
    logical, intent(in), optional :: recur_mode
    type(gc_value) :: child, rest, name
    logical :: rec
    integer :: base, i, n, amp

    rec = .false.
    if (present(recur_mode)) rec = recur_mode

    base = vs_enter(5)
    call vs_set(base + 1, params)
    call vs_set(base + 2, args)
    call vs_set(base + 3, outer)

    n = gcv_count(params)
    amp = -1
    do i = 0, n - 1
       name = strip_meta(gcv_nth(params, i))
       if (name%tag == GCT_SYM) then
          if (gc_ref_is(name%ref, "&")) then
             amp = i
             exit
          end if
       end if
    end do

    if (amp < 0) then
       if (n /= gcv_count(args)) then
          call fail("wrong number of arguments")
          child = gc_nil()
          call vs_leave(base); return
       end if
    else if (rec) then
       if (gcv_count(args) /= amp + 1) then
          call fail("wrong number of arguments to recur")
          child = gc_nil()
          call vs_leave(base); return
       end if
    else if (gcv_count(args) < amp) then
       call fail("too few arguments")
       child = gc_nil()
       call vs_leave(base); return
    else if (amp + 2 /= n) then
       call fail("& must be followed by exactly one name")
       child = gc_nil()
       call vs_leave(base); return
    end if

    child = gce_new(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 4, child)

    if (amp < 0) then
       do i = 0, n - 1
          call gce_set(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 1), i)), &
               gcv_nth(vs_get(base + 2), i), [vs_get(base + 1), vs_get(base + 2)])
       end do
    else if (rec) then
       do i = 0, amp - 1
          call gce_set(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 1), i)), &
               gcv_nth(vs_get(base + 2), i), [vs_get(base + 1), vs_get(base + 2)])
       end do
       call gce_set(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 1), amp + 1)), &
            gcv_nth(vs_get(base + 2), amp), [vs_get(base + 1), vs_get(base + 2)])
    else
       do i = 0, amp - 1
          call gce_set(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 1), i)), &
               gcv_nth(vs_get(base + 2), i), [vs_get(base + 1), vs_get(base + 2)])
       end do
       ! NIL when nothing is left, not the empty list. Clojure binds a
       ! rest parameter to a seq or to nil, and core.clj tests it
       ! directly: if-let asserts (nil? oldform) to reject a third form.
       ! An empty list is truthy, so that assertion fired on every
       ! correct call.
       if (gcv_count(vs_get(base + 2)) <= amp) then
          call gce_set(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 1), amp + 1)), &
               gc_nil(), [vs_get(base + 1), vs_get(base + 2)])
          child = vs_get(base + 4)
          call vs_leave(base)
          return
       end if
       rest = gcl_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 4)])
       call vs_set(base + 5, rest)
       do i = gcv_count(vs_get(base + 2)) - 1, amp, -1
          rest = gcl_cons(gcv_nth(vs_get(base + 2), i), vs_get(base + 5), &
               [vs_get(base + 1), vs_get(base + 2), vs_get(base + 4)])
          call vs_set(base + 5, rest)
       end do
       call gce_set(vs_get(base + 4), strip_meta(gcv_nth(vs_get(base + 1), amp + 1)), &
            vs_get(base + 5), [vs_get(base + 1), vs_get(base + 2)])
    end if

    child = vs_get(base + 4)
    call vs_leave(base)
  end function bind_params

  ! A fresh frame binding names(i) to vals(i), for a recur.
  function rebind(names, vals, outer) result(child)
    type(gc_value), intent(in) :: names, vals, outer
    type(gc_value) :: child
    integer :: base, i

    base = vs_enter(4)
    call vs_set(base + 1, names)
    call vs_set(base + 2, vals)
    call vs_set(base + 3, outer)
    if (gcv_count(names) /= gcv_count(vals)) then
       call fail("recur has the wrong number of arguments")
       child = gc_nil()
       call vs_leave(base); return
    end if
    child = gce_new(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 4, child)
    do i = 0, gcv_count(names) - 1
       call gce_set(vs_get(base + 4), gcv_nth(vs_get(base + 1), i), &
            gcv_nth(vs_get(base + 2), i), [vs_get(base + 1), vs_get(base + 2)])
    end do
    child = vs_get(base + 4)
    call vs_leave(base)
  end function rebind

  ! Every form in a body, last value wins.
  recursive function eval_body(body, env) result(out)
    type(gc_value), intent(in) :: body, env
    type(gc_value) :: out, walk
    integer :: base

    out = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, body)
    call vs_set(base + 2, env)
    walk = body
    call vs_set(base + 3, walk)
    do while (gcl_count(vs_get(base + 3)) > 0)
       out = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), &
            [vs_get(base + 1)])
       if (has_error) exit
       walk = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, walk)
    end do
    call vs_leave(base)
  end function eval_body

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
  recursive function make_closure(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, params, body, head
    type(gc_value) :: r(3)
    integer :: base

    base = vs_enter(4)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    head = gcl_first(rest)
    ! core.clj hints both halves of a fn head: (fn ^:static seq
    ! ^clojure.lang.ISeq [coll] ...) wraps the NAME and the PARAMETER
    ! VECTOR. Either arriving wrapped makes it unrecognisable, so the
    ! wrapper comes off before anything is decided about it.
    head = strip_meta(head)

    ! (fn* name [params] body) -- the optional SELF-NAME. core.clj
    ! writes almost every primitive that way, and not just for the
    ! stack trace: the name is bound inside the body so the function
    ! can call itself without going through its Var.
    !
    ! The knot is tied after the fact: build the closure over env,
    ! then give it a frame that binds the name to the closure itself
    ! and point it at that. Nothing can observe the intermediate state.
    if (head%tag == GCT_SYM) then
       call vs_set(base + 4, head)
       out = make_closure(gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), &
            vs_get(base + 2))
       block
         type(gc_value) :: frame
         call vs_set(base + 3, out)
         ! Over the env the recursive call BUILT, not the one passed in.
         ! That call tagged the closure with its defining namespace;
         ! building this frame over the original env and storing it back
         ! threw the tag away -- and core.clj writes almost every
         ! primitive with a self-name, so almost every primitive lost it.
         ! (clojure.core/last [1 2 3]) then answered :shadow in a
         ! namespace that had defined its own first.
         frame = gce_new(gc_slot(vs_get(base + 3), 3), &
              [vs_get(base + 3), vs_get(base + 4)])
         call gce_set(frame, vs_get(base + 4), vs_get(base + 3), &
              [vs_get(base + 3), vs_get(base + 4)])
         call gc_set_slot(vs_get(base + 3), 3, frame)
         out = vs_get(base + 3)
       end block
       call vs_leave(base)
       return
    end if

    ! A closure REMEMBERS THE NAMESPACE IT WAS DEFINED IN, by way
    ! of one extra frame binding a reserved name. Clojure resolves a
    ! symbol at compile time against the namespace the form was
    ! written in; resolving at call time against whatever namespace
    ! happens to be current is DEVIATIONS.md 3, and it shows the
    ! moment a function in one namespace calls a private helper in
    ! its own -- clojure.core.protocols/seq-reduce, called from a
    ! reduce running in clojure.core.
    !
    ! EVERY closure, clojure.core's included. Skipping core used to
    ! look free -- everything falls back to core anyway -- but the
    ! fallback is consulted LAST and the current namespace FIRST, so an
    ! untagged core function resolved its own free symbols against
    ! whatever namespace happened to be calling it. clojure.zip defines
    ! its own next, and from that form on every defn in the file
    ! expanded into core code that called the ZIPPER next. It hung.
    block
      type(gc_value) :: dns, inherited
      logical :: has_dns
      ! INHERITED if the enclosing env already carries one. Clojure
      ! binds the namespace while COMPILING, so every nested fn in a
      ! form belongs to the namespace that form was written in. Taking
      ! *ns* afresh here instead meant an inner (fn ...) created while
      ! a macro RAN was stamped with the caller's namespace, which
      ! shadowed the writer's -- clojure.template/do-template calls
      ! apply-template from inside exactly such a nested fn, and so
      ! could not find it.
      has_dns = .false.
      if (gce_is(vs_get(base + 2))) then
         if (gce_find(vs_get(base + 2), &
              gc_sym("__defining-ns__", [vs_get(base + 2)]), inherited)) &
              has_dns = (gc_kind(inherited) == OBJ_NS)
      end if
      dns = gcn_current([vs_get(base + 1), vs_get(base + 2)])
      if (.not. has_dns) then
        call vs_set(base + 4, dns)
        call vs_set(base + 2, gce_new(vs_get(base + 2), &
             [vs_get(base + 1), vs_get(base + 4)]))
        call gce_set(vs_get(base + 2), &
             gc_sym("__defining-ns__", [vs_get(base + 2)]), &
             vs_get(base + 4), [vs_get(base + 1), vs_get(base + 4)])
      end if
    end block

    if (gcl_is(head)) then
       ! Multi-arity: `rest` is already the list of clauses.
       r(1) = vs_get(base + 1); r(2) = vs_get(base + 2); r(3) = gc_nil()
       out = gc_obj(OBJ_CLOSURE, &
            [gc_nil(), gc_nil(), vs_get(base + 2), vs_get(base + 1)], r)
    else
       call vs_set(base + 3, head)
       body = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
       r(1) = vs_get(base + 1); r(2) = vs_get(base + 2); r(3) = vs_get(base + 3)
       out = gc_obj(OBJ_CLOSURE, &
            [vs_get(base + 3), body, vs_get(base + 2), gc_nil()], r)
    end if
    call vs_leave(base)
  end function make_closure

  ! Picks the clause matching argc: an exact arity wins, otherwise the
  ! first variadic one that can take this many. Real Clojure resolves
  ! this at compile time; here it is a short linear scan, which is
  ! fine for the handful of clauses a fn ever has.
  function select_clause(clauses, argc, params, body) result(found)
    type(gc_value), intent(in) :: clauses
    integer, intent(in) :: argc
    type(gc_value), intent(out) :: params, body
    logical :: found
    type(gc_value) :: clause, p, name
    integer :: base, i, n, j, amp

    found = .false.
    params = gc_nil()
    body = gc_nil()
    base = vs_enter(2)
    call vs_set(base + 1, clauses)
    n = gcl_count(clauses)
    do i = 0, n - 1
       clause = strip_meta(nth_of(vs_get(base + 1), i))
       call vs_set(base + 2, clause)
       p = strip_meta(gcl_first(clause))
       if (.not. gcv_is(p)) cycle
       amp = -1
       do j = 0, gcv_count(p) - 1
          name = strip_meta(gcv_nth(p, j))
          if (name%tag == GCT_SYM) then
             if (gc_ref_is(name%ref, "&")) then
                amp = j
                exit
             end if
          end if
       end do
       if (amp < 0) then
          if (gcv_count(p) /= argc) cycle
       else
          if (argc < amp) cycle
       end if
       params = p
       body = gcl_rest(vs_get(base + 2), [vs_get(base + 1)])
       found = .true.
       exit
    end do
    call vs_leave(base)
  end function select_clause

  recursive function eval_vector(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, item
    integer :: base, i

    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    out = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 3, out)
    do i = 0, gcv_count(vs_get(base + 1)) - 1
       item = gce_eval(gcv_nth(vs_get(base + 1), i), vs_get(base + 2), &
            [vs_get(base + 1), vs_get(base + 3)])
       if (has_error) exit
       out = gcv_conj(vs_get(base + 3), item, [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function eval_vector

  ! (. target member) and (. target (member args...)) -- host interop.
  !
  ! Clojure's host is the JVM, so `.` there reaches arbitrary Java.
  ! Ours is Fortran, and the only classes that exist are clotran's own
  ! runtime types -- so this is not a subset of Java interop, it is the
  ! same door onto a different house.
  !
  ! core.clj reaches through it exactly three times while bootstrapping
  ! (its lines 20, 338, 493) and those three are what is here. Anything
  ! else fails by MEMBER NAME, so a load report says what is missing
  ! rather than blaming `.` for all of it.
  recursive function eval_dot(args, env) result(out)
    type(gc_value), intent(in) :: args, env
    type(gc_value) :: out, target, member, rest, margs
    character(len=:), allocatable :: mname
    logical :: is_call
    integer :: base

    out = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, args)
    call vs_set(base + 2, env)

    target = gcl_first(vs_get(base + 1))
    rest = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    member = strip_meta(gcl_first(rest))

    ! A macro assembles its expansion with cons and concat, so the
    ! (method args) half of a dot form arrives as a LAZY SEQ rather
    ! than a list -- the same reason gce_eval realises a seq before
    ! treating it as a call. emit-method-builder builds exactly that
    ! shape, so every protocol method dispatched through its interface
    ! read the seq as a bare member name and failed on it.
    if (gc_kind(member) == OBJ_LAZY .or. gc_kind(member) == OBJ_SEQ) then
       call vs_set(base + 5, member)
       member = seq_to_list(vs_get(base + 5), [vs_get(base + 1), vs_get(base + 5)])
       call vs_set(base + 5, member)
    end if

    ! (. x m) names a member; (. x (m a b)) and (. x m a b) both
    ! call it -- Clojure accepts either spelling, so the arguments
    ! come from inside the parens when there are parens and from the
    ! rest of the form when there are not.
    ! PARENS MEAN A CALL, arguments or not. (. RT (nextID)) takes none
    ! and must still be invoked; returning the method itself is how a
    ! gensym ended up named seq__#<object>. Without parens it is a field
    ! read, which is what PersistentList/creator is.
    if (gcl_is(member)) then
       is_call = .true.
       margs = gcl_rest(member, [vs_get(base + 1)])
       ! The method NAME can be hinted -- a sig in a protocol keeps
       ! its metadata through defprotocol, and emit-method-builder
       ! splices that symbol in verbatim.
       member = strip_meta(gcl_first(member))
    else
       margs = gcl_rest(rest, [vs_get(base + 1)])
       is_call = (gcl_count(margs) > 0)
    end if
    if (member%tag /= GCT_SYM) then
       call fail(". needs a member name")
       call vs_leave(base)
       return
    end if
    mname = gc_ref_text(member%ref)
    call vs_set(base + 4, margs)

    ! A class name is NOT evaluated -- clojure.lang.RT is not a
    ! binding. Everything else is: (. (var defmacro) ...) has to run
    ! to produce the Var.
    if (target%tag == GCT_SYM) then
       ! A DEFTYPE CLASS in member position. The only static one has
       ! is a record's `create`, which is what map->Name calls.
       block
         type(gc_value) :: dty, marg
         dty = find_type(gc_ref_text(target%ref))
         if (gc_kind(dty) == OBJ_TYPE .and. mname == "create") then
            call vs_set(base + 5, dty)
            marg = gce_eval(gcl_first(vs_get(base + 4)), vs_get(base + 2), &
                 [vs_get(base + 1), vs_get(base + 5)])
            if (has_error) then
               call vs_leave(base)
               return
            end if
            call vs_set(base + 6, marg)
            out = record_create(vs_get(base + 5), vs_get(base + 6), &
                 [vs_get(base + 5), vs_get(base + 6)])
            call vs_leave(base)
            return
         end if
       end block
       if (is_host_class(target)) then
          out = static_member(gc_ref_text(target%ref), mname, vs_get(base + 1))
          if (.not. has_error .and. is_call) &
               out = apply_forms(out, vs_get(base + 4), vs_get(base + 2))
          call vs_leave(base)
          return
       end if
    end if

    target = gce_eval(target, vs_get(base + 2), [vs_get(base + 1)])
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, target)

    ! A deftype/reify instance answers its own methods and fields
    ! FIRST. They are what the type declares, and a host member of the
    ! same name would otherwise shadow the implementation the program
    ! actually wrote.
    if (gc_kind(strip_meta(vs_get(base + 3))) == OBJ_INST .and. len(mname) > 0) then
       block
         logical :: found
         call vs_set(base + 5, strip_meta(vs_get(base + 3)))
         ! (.-name x) is a field read and never a call; a bare name is
         ! a method if the type has one and a field otherwise, which
         ! is the order Compiler's HostExpr resolves them in.
         if (mname(1:1) == "-") then
            out = inst_field(vs_get(base + 5), mname(2:), found)
            if (.not. found) call fail("no such field: " // &
                 class_text(vs_get(base + 5)) // &
                 "." // mname(2:))
            call vs_leave(base)
            return
         end if
         call vs_set(base + 6, gca_get(gc_slot(gc_slot(vs_get(base + 5), 1), 3), &
              gc_key(mname, [vs_get(base + 1), vs_get(base + 5)])))
         if (gc_kind(vs_get(base + 6)) == OBJ_CLOSURE) then
            ! `this` is an explicit first parameter of the method, so
            ! the target is prepended exactly as for a host member.
            call vs_set(base + 4, gcl_cons(vs_get(base + 5), vs_get(base + 4), &
                 [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5), &
                  vs_get(base + 6)]))
            out = apply_forms_pre(vs_get(base + 6), vs_get(base + 5), &
                 vs_get(base + 4), vs_get(base + 2))
            call vs_leave(base)
            return
         end if
         out = inst_field(vs_get(base + 5), mname, found)
         if (found) then
            call vs_leave(base)
            return
         end if
       end block
    end if

    out = instance_member(mname, vs_get(base + 1))
    if (.not. has_error) then
       ! The target is the first argument, which is all an instance
       ! method is: (.withMeta x m) calls with-meta on x and m.
       margs = gcl_cons(vs_get(base + 3), vs_get(base + 4), &
            [vs_get(base + 3), vs_get(base + 4), out])
       call vs_set(base + 4, margs)
       out = apply_forms_pre(out, vs_get(base + 3), vs_get(base + 4), vs_get(base + 2))
       call vs_leave(base)
       return
    end if
    call gce_clear_error()

    if (mname == "setMacro" .and. gcn_is_var(vs_get(base + 3))) then
       ! Var.setMacro is alterMeta(assoc, {:macro true}) -- macro-ness
       ! is METADATA ON THE VAR, not a flag on the function. That is
       ! what makes (:macro (meta (var when))) true, and what makes
       ! (def foo some-macro) bind a plain function rather than a macro.
       call var_set_macro(vs_get(base + 3), vs_get(base + 2))
       out = gc_nil()
    else
       ! Name the TARGET as well as the member. A class literal that is
       ! not in is_host_class falls through to here, and "no such
       ! member: create" alone does not say which create.
       block
         type(gc_value) :: tv
         tv = strip_meta(vs_get(base + 3))
         if (tv%tag == GCT_KEY) then
            ! A class reached through a VARIABLE, not written as a
            ! literal. core.clj's `cast` is (. c (cast x)) with c a
            ! parameter, so is_host_class -- which tests the symbol
            ! before evaluation -- cannot see it; by here the target
            ! has been evaluated and IS the class. Retrying it as a
            ! static member is what makes (cast Number 1.5) work, and
            ! any other class held in a variable with it.
            out = static_member(gc_ref_text(tv%ref), mname, vs_get(base + 1))
            if (.not. has_error .and. is_call) &
                 out = apply_forms(out, vs_get(base + 4), vs_get(base + 2))
         else
            call fail("no such member: " // type_name(tv) // "." // mname)
         end if
       end block
    end if
    call vs_leave(base)
  end function eval_dot

  ! Evaluates each form and applies fn to the results.
  recursive function apply_forms(fn, forms, env) result(out)
    type(gc_value), intent(in) :: fn, forms, env
    type(gc_value) :: out, args, walk, item
    integer :: base

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, env)
    args = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, args)
    walk = forms
    call vs_set(base + 4, walk)
    do while (gcl_count(vs_get(base + 4)) > 0)
       item = gce_eval(gcl_first(vs_get(base + 4)), vs_get(base + 2), &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       if (has_error) then
          call vs_leave(base); return
       end if
       args = gcv_conj(vs_get(base + 3), item, &
            [vs_get(base + 1), vs_get(base + 4)])
       call vs_set(base + 3, args)
       walk = gcl_rest(vs_get(base + 4), [vs_get(base + 2)])
       call vs_set(base + 4, walk)
    end do
    out = apply(vs_get(base + 1), vs_get(base + 3))
    call vs_leave(base)
  end function apply_forms

  ! Instance members, as natives. Same rule as the static ones:
  ! these are clotran's own primitives under the names the JVM host
  ! gives them, not adapters written to look like them.
  function instance_member(mname, roots) result(out)
    character(len=*), intent(in) :: mname
    type(gc_value), intent(in) :: roots
    type(gc_value) :: out
    out = gc_nil()
    select case (mname)
    case ("meta");     out = native(B_META, "meta", [roots])
    case ("withMeta"); out = native(B_WITHMETA, "with-meta", [roots])
    case ("count");    out = native(B_COUNT, "count", [roots])
    case ("seq");      out = native(B_SEQ, "seq", [roots])
    case ("first");    out = native(B_FIRST, "first", [roots])
    case ("next");     out = native(B_NEXT, "next", [roots])
    case ("more");     out = native(B_REST, "rest", [roots])
    case ("cons");     out = native(B_CONS, "cons", [roots])
    case ("isInstance"); out = native(B_INSTANCE, "instance?", [roots])
    case ("getName", "getSimpleName"); out = native(B_GETNAME, "clotran-get-name", [roots])
    case ("getStackTrace"); out = native(B_EMPTYVEC, "clotran-empty-vector", [roots])
    case ("getNamespace"); out = native(B_NAMESPACE, "namespace", [roots])
    case ("getClass")
       ! clotran's classes are its type tags, so .getClass is
       ! clotran-type -- which is what makes (class x) answer something
       ! protocol dispatch can key on. It answered nil for a while,
       ! which silently emptied every protocol's impl lookup.
       out = native(B_TYPE, "clotran-type", [roots])
    case ("getComponentType")
       ! The element type of an array CLASS. clotran has one class
       ! keyword for every array -- :array, not [I versus [D -- so
       ! there is nothing to answer, and the only caller is aget's
       ! (Reflector/prepRet (.getComponentType (class array)) ...),
       ! which ignores it because nothing here is boxed.
       out = native(B_ALWAYS_NIL, "clotran-nil", [roots])
    case ("getClassLoader", "getContextClassLoader")
       out = native(B_ALWAYS_NIL, "clotran-nil", [roots])
    case ("isRealized"); out = native(B_ISREALIZED, "clotran-is-realized", [roots])
    case ("getResources")
       ! NOTHING, and honestly so. getResources enumerates a
       ! CLASSPATH for a named file, and clotran has no classpath --
       ! getContextClassLoader above already answers nil for the
       ! same reason. So there are no data_readers.clj files to find
       ! and the true answer is the empty enumeration.
       !
       ! This is the wall at core.clj form 708: (data-reader-urls)
       ! threw on nil.getResources, load-data-readers threw with it,
       ! and the catch clause re-throws -- so the form failed and the
       ! last sixteen forms of core.clj never loaded, update-keys and
       ! update-vals among them.
       out = native(B_ALWAYS_NIL, "clotran-nil", [roots])
    ! Namespace members. The mappings ARE slot 2 -- ns-map hands the
    ! same map the evaluator resolves against, not a copy.
    case ("getMappings"); out = native(B_NSMAP, "ns-map", [roots])
    case ("ns"); out = native(B_VARNS, "clotran-var-ns", [roots])
    ! Var.toSymbol is the ns-qualified name, which is how a protocol
    ! names the method it is dispatching.
    case ("toSymbol"); out = native(B_VARSYM, "clotran-var-symbol", [roots])
    case ("isPublic"); out = native(B_ISPUBLIC, "clotran-var-public", [roots])
    case ("isMacro"); out = native(B_ISMACRO, "clotran-var-macro", [roots])
    case ("setMacro"); out = native(B_SETMACRO, "clotran-set-macro", [roots])
    case ("getAliases");  out = native(B_NSALIASES, "ns-aliases", [roots])
    case ("refer"); out = native(B_NSREFER, "clotran-ns-refer", [roots])
    case ("addAlias"); out = native(B_NSADDALIAS, "clotran-ns-add-alias", [roots])
    ! The String methods core.clj reaches for while loading libs.
    case ("startsWith"); out = native(B_STARTSWITH, "clotran-starts-with", [roots])
    case ("endsWith"); out = native(B_ENDSWITH, "clotran-ends-with", [roots])
    case ("replace"); out = native(B_REPLACE, "clotran-replace", [roots])
    case ("length"); out = native(B_STRLEN, "clotran-length", [roots])
    case ("substring", "subSequence"); out = native(B_SUBSTRING, "subs", [roots])
    ! (. f (applyTo (seq args))) is core.clj's own apply, and the
    ! target becoming the first argument makes it exactly (apply f seq).
    case ("applyTo");   out = native(B_APPLY, "apply", [roots])
    case ("deref");     out = native(B_DEREF, "deref", [roots])
    case ("hasRoot");   out = native(B_HASROOT, "clotran-has-root", [roots])
    case ("addMethod"); out = native(B_ADDMETHOD, "clotran-add-method", [roots])
    ! preferMethod resolves an AMBIGUITY between two matching methods,
    ! and exact-match dispatch has no ambiguity to resolve -- so it
    ! records nothing and returns the multimethod. DEVIATIONS.md 8.
    ! The protocol dispatch cache field, read and written on the
    ! protocol function itself. Reading it answers nil -- a cold
    ! cache -- and writing it is discarded, which is what a cache
    ! with no storage behind it means.
    ! Class.isAssignableFrom asks whether one JVM type is a subtype
    ! of another. There are no interfaces here and no inheritance
    ! between clotran's types, so the answer is false -- which is
    ! what sends extends? and satisfies? down the extend-map path
    ! that clotran does implement.
    case ("getSuperclass")
       ! clotran's types form no hierarchy: :vector has no superclass.
       ! nil here is what sends find-protocol-impl to its (impl Object)
       ! fallback, which is the branch that actually resolves.
       out = native(B_ALWAYS_NIL, "clotran-nil", [roots])
    case ("getInterfaces")
       out = native(B_EMPTYVEC, "clotran-empty", [roots])
    case ("isAssignableFrom", "isInterface", "isArray")
       out = native(B_ALWAYS_FALSE, "clotran-false", [roots])
    ! The cache's named fields, read off the map it is.
    case ("sym");      out = native(B_FLD_SYM, "clotran-sym", [roots])
    case ("protocol"); out = native(B_FLD_PROTOCOL, "clotran-protocol", [roots])
    case ("methodk");  out = native(B_FLD_METHODK, "clotran-methodk", [roots])
    case ("map", "table"); out = native(B_FLD_MAP, "clotran-map", [roots])
    case ("fnFor")
       out = native(B_ALWAYS_NIL, "clotran-nil", [roots])
    case ("__methodImplCache")
       out = native(B_FLD_CACHE, "clotran-cache", [roots])
    case ("preferMethod", "getMethod")
       out = native(B_IDENTITY, "identity", [roots])
    case ("disjoin");   out = native(B_DISJ, "disj", [roots])

    case ("concat"); out = native(B_STR, "str", [roots])
    case ("toString"); out = native(B_TOSTRING, "clotran-to-string", [roots])
    case ("toUpperCase"); out = native(B_UPCASE, "clotran-upcase", [roots])
    case ("toLowerCase"); out = native(B_DOWNCASE, "clotran-downcase", [roots])
    ! Throwable.getCause is nil when nothing wrapped it, which is every
    ! error here: clotran has no cause chain to walk.
    case ("getCause"); out = native(B_ALWAYS_NIL, "clotran-nil", [roots])
    case ("append");   out = native(B_APPEND, "clotran-append", [roots])
    ! Writer methods. core_print reaches for all three.
    case ("charAt");   out = native(B_CHARAT, "clotran-char-at", [roots])
    case ("pattern");  out = native(B_TOSTRING, "clotran-to-string", [roots])
    case ("write");    out = native(B_WRITE, "clotran-write", [roots])
    case ("flush");    out = native(B_FLUSH, "clotran-flush", [roots])
    case ("getMessage", "getLocalizedMessage")
       out = native(B_EXMSG, "ex-message", [roots])
    case ("getData");   out = native(B_EXDATA, "ex-data", [roots])
    ! A map entry is a two-element vector here, so key and val are the
    ! two nths -- which is what Clojure's MapEntry is too.
    case ("getKey");   out = native(B_KEY, "key", [roots])
    case ("getValue"); out = native(B_VAL, "val", [roots])
    ! IReference.alterMeta is resetMeta(alter.applyTo(listStar(meta(),
    ! args))) -- the function sees the current metadata first.
    case ("alterMeta"); out = native(B_ALTERMETA, "clotran-alter-meta", [roots])
    case ("resetMeta", "setMeta")
       out = native(B_RESETMETA, "clotran-reset-meta", [roots])
    case ("set", "reset"); out = native(B_SETVAL, "clotran-set-val", [roots])
    case ("swap")
       out = native(B_SWAPVAL, "clotran-swap-val", [roots])
    case ("alter", "commute", "alterRoot")
       ! alterRoot is alter on a Var's root, which is slot 1 -- the same
       ! slot a Ref and an atom keep their value in.
       out = native(B_ALTERVAL, "clotran-alter-val", [roots])
    case ("bindRoot"); out = native(B_SETVAL, "clotran-set-val", [roots])
    ! String.indexOf, 0-based and -1 when absent, which is the value
    ! core.clj compares against: (Util/equiv (.indexOf (.getName tag) ".") -1).
    case ("indexOf");  out = native(B_INDEXOF, "clotran-index-of", [roots])
    case ("lastIndexOf"); out = native(B_LASTINDEXOF, "clotran-last-index-of", [roots])
    case ("equiv", "equals"); out = native(B_EQ, "=", [roots])
    ! TRANSIENTS ARE THE PERSISTENT COLLECTIONS HERE. A transient is an
    ! optimisation, not a semantic: used correctly -- single-threaded and
    ! linearly -- (persistent! (conj! (transient c) x)) and (conj c x)
    ! are the same value. So asTransient and persistent are identity and
    ! the bang operations are the ordinary ones. DEVIATIONS.md 11.
    !
    ! What is lost is the SPEED, and the error when a transient is used
    ! after being persisted, which Clojure catches and we do not.
    case ("asTransient", "persistent")
       out = native(B_IDENTITY, "identity", [roots])
    case ("conj");     out = native(B_CONJ, "conj", [roots])
    case ("assoc");    out = native(B_ASSOC, "assoc", [roots])
    case ("without");  out = native(B_DISSOC, "dissoc", [roots])
    case ("valAt");    out = native(B_GET, "get", [roots])
    ! .get is two different methods in Java -- Var.get() takes nothing
    ! and derefs, Map.get(k) takes a key -- so it dispatches on how many
    ! arguments arrived.
    ! Resource loading, which is all core.clj asks a ClassLoader for.
    case ("getResourceAsStream")
       out = native(B_RESOURCE, "clotran-resource", [roots])
    case ("load");        out = native(B_PROPLOAD, "clotran-props-load", [roots])
    case ("getProperty"); out = native(B_PROPGET, "clotran-props-get", [roots])
    ! with-open closes what it opened. Our streams are strings; there is
    ! nothing to release, but the call must succeed.
    case ("close");       out = native(B_CLOSE, "clotran-close", [roots])
    case ("get");      out = native(B_DOTGET, "clotran-dot-get", [roots])
    case ("nth");      out = native(B_NTH, "nth", [roots])
    case ("contains"); out = native(B_STRCONTAINS, "clotran-dot-contains", [roots])
    ! java.util.regex.Pattern/Matcher instance methods -- see Regex.f90.
    case ("matcher");    out = native(B_RE_MATCHER, "re-matcher", [roots])
    case ("find");       out = native(B_RE_FIND, "re-find*", [roots])
    case ("matches");    out = native(B_RE_MATCHES, "re-matches*", [roots])
    case ("groupCount"); out = native(B_RE_GROUPCOUNT, "re-group-count", [roots])
    case ("group");      out = native(B_RE_GROUP, "re-group", [roots])
    case default;       call fail("no such member: " // mname)
    end select
  end function instance_member

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
    is_member_sym = (t(1:1) == ".")
  end function is_member_sym

  recursive function eval_member(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, rest, args
    character(len=:), allocatable :: hname
    integer :: base

    out = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    head = gcl_first(vs_get(base + 1))
    hname = gc_ref_text(head%ref)
    rest = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 3, rest)
    if (gcl_count(vs_get(base + 3)) < 1) then
       call fail("Malformed member expression, expecting (.member target ...)")
       call vs_leave(base)
       return
    end if
    ! (target member . rest) -- the shape eval_dot reads.
    args = gcl_cons(gc_sym(hname(2:), [vs_get(base + 3)]), &
         gcl_rest(vs_get(base + 3), [vs_get(base + 3)]), [vs_get(base + 3)])
    args = gcl_cons(gcl_first(vs_get(base + 3)), args, [vs_get(base + 3), args])
    out = eval_dot(args, vs_get(base + 2))
    call vs_leave(base)
  end function eval_member

  ! apply fn to already-evaluated first argument plus evaluated rest.
  recursive function apply_forms_pre(fn, first_arg, all_forms, env) result(out)
    type(gc_value), intent(in) :: fn, first_arg, all_forms, env
    type(gc_value) :: out, args, walk, item
    integer :: base

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, env)
    args = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    args = gcv_conj(args, first_arg, [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, args)
    walk = gcl_rest(all_forms, [vs_get(base + 2)])
    call vs_set(base + 4, walk)
    do while (gcl_count(vs_get(base + 4)) > 0)
       item = gce_eval(gcl_first(vs_get(base + 4)), vs_get(base + 2), &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       if (has_error) then
          call vs_leave(base); return
       end if
       args = gcv_conj(vs_get(base + 3), item, &
            [vs_get(base + 1), vs_get(base + 4)])
       call vs_set(base + 3, args)
       walk = gcl_rest(vs_get(base + 4), [vs_get(base + 2)])
       call vs_set(base + 4, walk)
    end do
    out = apply(vs_get(base + 1), vs_get(base + 3))
    call vs_leave(base)
  end function apply_forms_pre

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

  recursive function eval_ctor(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, args
    character(len=:), allocatable :: t
    integer :: base

    base = vs_enter(2)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    head = gcl_first(vs_get(base + 1))
    t = gc_ref_text(head%ref)
    args = gcl_cons(gc_sym(t(1:len(t)-1), [vs_get(base + 1)]), &
         gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), [vs_get(base + 1)])
    out = eval_new(args, vs_get(base + 2))
    call vs_leave(base)
  end function eval_ctor

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

  recursive function eval_static(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, args
    character(len=:), allocatable :: t
    integer :: base, slash

    out = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    head = gcl_first(vs_get(base + 1))
    t = gc_ref_text(head%ref)
    slash = index(t, "/")
    ! (Class (member . args)) -- the PARENTHESISED shape, because
    ! Class/member in head position is always a call, arguments or not.
    ! (clojure.lang.Var/popThreadBindings) takes none, and handing
    ! eval_dot the bare symbol made it read the member as a field and
    ! return the function itself. binding then never restored anything.
    args = gcl_cons(gc_sym(t(slash+1:), [vs_get(base + 1)]), &
         gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), [vs_get(base + 1)])
    args = gcl_cons(args, gcl_empty([vs_get(base + 1)]), [vs_get(base + 1), args])
    call vs_set(base + 3, args)
    args = gcl_cons(gc_sym(t(1:slash-1), [vs_get(base + 3)]), vs_get(base + 3), &
         [vs_get(base + 3)])
    out = eval_dot(args, vs_get(base + 2))
    call vs_leave(base)
  end function eval_static

  ! (new Class args...). The one class core.clj constructs during the
  ! bootstrap is LazySeq, which `lazy-seq` expands into -- and a
  ! LazySeq is exactly an unrealised node over a no-argument thunk,
  ! which is what lazy-seq* already builds. Everything else is named
  ! in the error, so a load report says which class is missing.
  recursive function eval_new(args, env) result(out)
    type(gc_value), intent(in) :: args, env
    type(gc_value) :: out, cls, thunk
    character(len=:), allocatable :: cname
    integer :: base

    out = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, args)
    call vs_set(base + 2, env)
    cls = gcl_first(vs_get(base + 1))
    if (cls%tag /= GCT_SYM) then
       call fail("new needs a class name")
       call vs_leave(base)
       return
    end if
    cname = gc_ref_text(cls%ref)

    if (cname == "clojure.lang.Reduced") then
       ! (reduced x) wraps a value to say "stop reducing". A
       ! one-key map is enough to carry the mark and the value,
       ! and the key is one no Clojure program can write.
       thunk = gce_eval(gcl_first(gcl_rest(vs_get(base + 1), &
            [vs_get(base + 1)])), vs_get(base + 2), [vs_get(base + 1)])
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 3, thunk)
       out = gca_assoc(gca_empty([vs_get(base + 3)]), &
            gc_key("clotran/reduced", [vs_get(base + 3)]), &
            vs_get(base + 3), [vs_get(base + 3)])
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
         type(gc_value) :: mp, w2, item2
         integer :: fi
         character(len=12) :: fname
         mp = gca_empty([vs_get(base + 1)])
         call vs_set(base + 3, mp)
         w2 = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
         fi = 0
         do while (gcl_count(w2) > 0)
            item2 = gce_eval(gcl_first(w2), vs_get(base + 2), &
                 [vs_get(base + 1), vs_get(base + 3)])
            if (has_error) then
               call vs_leave(base)
               return
            end if
            select case (fi)
            case (0); fname = "sym"
            case (1); fname = "protocol"
            case (2); fname = "methodk"
            case default; fname = "map"
            end select
            mp = gca_assoc(vs_get(base + 3), &
                 gc_key(trim(fname), [vs_get(base + 3)]), item2, &
                 [vs_get(base + 1), vs_get(base + 3)])
            call vs_set(base + 3, mp)
            fi = fi + 1
            w2 = gcl_rest(w2, [vs_get(base + 1), vs_get(base + 3)])
         end do
         if (fi < 4) then
            mp = gca_assoc(vs_get(base + 3), gc_key("map", [vs_get(base + 3)]), &
                 gca_empty([vs_get(base + 3)]), [vs_get(base + 3)])
            call vs_set(base + 3, mp)
         end if
         out = vs_get(base + 3)
       end block
    else if (cname == "clojure.lang.Ref" .or. cname == "clojure.lang.Atom" .or. &
         cname == "clojure.lang.Agent") then
       ! A Ref IS an atom here: a mutable box, with no transaction
       ! around it. Single-threaded that is indistinguishable; the
       ! moment threads arrive it is not. DEVIATIONS.md 9.
       thunk = gce_eval(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), &
            vs_get(base + 2), [vs_get(base + 1)])
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_ATOM, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
    else if (cname == "java.util.Properties" .or. cname == "Properties") then
       thunk = gca_empty([vs_get(base + 1)])
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_ATOM, [vs_get(base + 3), gc_nil()], [vs_get(base + 3)])
    else if (cname == "StringBuilder" .or. cname == "java.lang.StringBuilder" .or. &
         cname == "StringBuffer" .or. cname == "java.lang.StringBuffer" .or. &
         cname == "java.io.StringWriter" .or. cname == "StringWriter") then
       thunk = gc_str("", [vs_get(base + 1)])
       if (gcl_count(vs_get(base + 1)) > 1) then
          thunk = gce_eval(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), &
               vs_get(base + 2), [vs_get(base + 1)])
          if (has_error) then
             call vs_leave(base)
             return
          end if
       end if
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_SB, [vs_get(base + 3)], [vs_get(base + 3)])
    else if (cname == "clojure.lang.MultiFn") then
       ! (new MultiFn name dispatch-fn default hierarchy). The
       ! hierarchy is accepted and ignored -- see DEVIATIONS.md 7.
       block
         type(gc_value) :: parts, w, a
         integer :: k
         parts = gcv_empty([vs_get(base + 1)])
         call vs_set(base + 3, parts)
         w = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
         do k = 1, 3
            a = gce_eval(gcl_first(w), vs_get(base + 2), &
                 [vs_get(base + 1), vs_get(base + 3)])
            if (has_error) then
               call vs_leave(base)
               return
            end if
            parts = gcv_conj(vs_get(base + 3), a, [vs_get(base + 1), vs_get(base + 3)])
            call vs_set(base + 3, parts)
            w = gcl_rest(w, [vs_get(base + 1), vs_get(base + 3)])
         end do
         out = gc_obj(OBJ_MULTIFN, &
              [gcv_nth(vs_get(base + 3), 0), gcv_nth(vs_get(base + 3), 1), &
               gcv_nth(vs_get(base + 3), 2), gca_empty([vs_get(base + 3)])], &
              [vs_get(base + 3)])
       end block
    else if (cname == "clojure.lang.Delay") then
       ! (delay body) is (new clojure.lang.Delay (fn [] body)) in
       ! core.clj, so the argument is already a no-argument closure and
       ! nothing here needs to know about the body.
       thunk = gce_eval(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), &
            vs_get(base + 2), [vs_get(base + 1)])
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 3, thunk)
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
       thunk = gce_eval(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), &
            vs_get(base + 2), [vs_get(base + 1)])
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 3, thunk)
       out = gc_obj(OBJ_LAZY, [vs_get(base + 3), gc_nil(), gc_nil()], &
            [vs_get(base + 3)])
       call gc_set_i1(out, LAZY_PENDING)
    else if (is_throwable_class(cname)) then
       ! Every exception class core.clj names takes a message, and
       ! ex-info adds a data map. Anything else about a Java exception
       ! -- its hierarchy, its stack trace -- has nothing to correspond
       ! to here, so the class name is kept as written and nothing is
       ! invented around it.
       block
         type(gc_value) :: parts, w, item
         parts = gcv_empty([vs_get(base + 1)])
         call vs_set(base + 3, parts)
         w = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
         do while (gcl_count(w) > 0)
            item = gce_eval(gcl_first(w), vs_get(base + 2), &
                 [vs_get(base + 1), vs_get(base + 3)])
            if (has_error) then
               call vs_leave(base)
               return
            end if
            parts = gcv_conj(vs_get(base + 3), item, &
                 [vs_get(base + 1), vs_get(base + 3)])
            call vs_set(base + 3, parts)
            w = gcl_rest(w, [vs_get(base + 1), vs_get(base + 3)])
         end do
         out = gc_obj(OBJ_ERR, &
              [gc_sym(cname, [vs_get(base + 3)]), &
               nth_or_nil(vs_get(base + 3), 0), &
               nth_or_nil(vs_get(base + 3), 1)], &
              [vs_get(base + 3)])
       end block
    else
       ! A type deftype* created. Last, so nothing above is shadowed
       ! by a deftype that happens to pick one of those names.
       block
         type(gc_value) :: ty
         ty = find_type(cname)
         if (gc_kind(ty) == OBJ_TYPE) then
            call vs_set(base + 3, ty)
            out = construct_type(vs_get(base + 3), &
                 gcl_rest(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 3)]), &
                 vs_get(base + 2))
         else
            call fail("no such class: " // cname)
         end if
       end block
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
  end function is_throwable_class

  function nth_or_nil(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    out = gc_nil()
    if (i < gcv_count(v)) out = gcv_nth(v, i)
  end function nth_or_nil

  logical function is_host_class(sym)
    type(gc_value), intent(in) :: sym
    is_host_class = gc_ref_is(sym%ref, "clojure.lang.PersistentList") .or. &
         gc_ref_is(sym%ref, "clojure.lang.RT") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Util") .or. &
         gc_ref_is(sym%ref, "clojure.lang.MapEntry") .or. &
         gc_ref_is(sym%ref, "clojure.lang.EnumerationSeq") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Delay") .or. &
         gc_ref_is(sym%ref, "java.lang.reflect.Array") .or. &
         gc_ref_is(sym%ref, "Array") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Reflector") .or. &
         gc_ref_is(sym%ref, "clojure.lang.LazilyPersistentVector") .or. &
         gc_ref_is(sym%ref, "LazilyPersistentVector") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentHashMap") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentArrayMap") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentHashSet") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentTreeSet") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentTreeMap") .or. &
         gc_ref_is(sym%ref, "java.util.regex.Pattern") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Symbol") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Keyword") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Numbers") .or. &
         gc_ref_is(sym%ref, "Number") .or. &
         gc_ref_is(sym%ref, "java.lang.Number") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Compiler$HostExpr") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Compiler") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Namespace") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Var") .or. &
         gc_ref_is(sym%ref, "clojure.lang.LockingTransaction") .or. &
         gc_ref_is(sym%ref, "Class") .or. &
         gc_ref_is(sym%ref, "java.lang.Class") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Repeat") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Iterate") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Cycle") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Range") .or. &
         gc_ref_is(sym%ref, "clojure.lang.LongRange") .or. &
         gc_ref_is(sym%ref, "Integer") .or. gc_ref_is(sym%ref, "java.lang.Integer") .or. &
         gc_ref_is(sym%ref, "Double") .or. gc_ref_is(sym%ref, "java.lang.Double") .or. &
         gc_ref_is(sym%ref, "Long") .or. gc_ref_is(sym%ref, "java.lang.Long") .or. &
         gc_ref_is(sym%ref, "Thread") .or. gc_ref_is(sym%ref, "java.lang.Thread") .or. &
         gc_ref_is(sym%ref, "Character") .or. gc_ref_is(sym%ref, "java.lang.Character") .or. &
         gc_ref_is(sym%ref, "Math") .or. gc_ref_is(sym%ref, "java.lang.Math") .or. &
         gc_ref_is(sym%ref, "System") .or. gc_ref_is(sym%ref, "java.lang.System")
  end function is_host_class

  ! A static member, as a VALUE -- (. C m) hands it back, (. C (m a))
  ! calls it, and both go through here.
  !
  ! These are the primitives core.clj bootstraps on. They are OUR
  ! natives under the names the JVM host gives them, not adapters:
  ! RT.more is what clotran already means by `rest`, and RT.next is
  ! that put through seq.
  function static_member(cls, mname, roots) result(out)
    character(len=*), intent(in) :: cls, mname
    type(gc_value), intent(in) :: roots
    type(gc_value) :: out

    out = gc_nil()
    if (cls == "clojure.lang.PersistentList") then
       ! PersistentList.creator is a static IFn (a Primordial) that
       ! builds a list from its arguments -- our `list`.
       if (mname == "creator") then
          out = native(B_LIST, "list", [roots])
          return
       end if
    else if (cls == "java.lang.reflect.Array" .or. cls == "Array") then
       ! core.clj's own make-array, aget, aset and the aset-int family
       ! are written against these, so implementing them is what makes
       ! Clojure's array code work rather than shadowing it.
       !
       ! Every typed variant -- getInt, setDouble, getBoolean -- shares
       ! one implementation, because those exist on the JVM to avoid
       ! boxing and clotran has no boxing to avoid. The element's kind
       ! is the array's, not the accessor's name.
       select case (mname)
       case ("newInstance")
          out = native(B_ANEWINST, "clotran-array-new", [roots]); return
       case ("get", "getInt", "getLong", "getDouble", "getFloat", &
             "getBoolean", "getChar", "getByte", "getShort")
          out = native(B_AGET, "aget", [roots]); return
       case ("set", "setInt", "setLong", "setDouble", "setFloat", &
             "setBoolean", "setChar", "setByte", "setShort")
          out = native(B_ASET, "aset", [roots]); return
       case ("getLength")
          out = native(B_ALENGTH, "alength", [roots]); return
       end select
    else if (cls == "clojure.lang.Reflector") then
       ! prepRet UNBOXES on the JVM -- it turns a boxed Integer back
       ! into a primitive for a known component type. There is nothing
       ! boxed here, so the value it is handed is already the answer.
       if (mname == "prepRet") then
          out = native(B_PREPRET, "clotran-prep-ret", [roots]); return
       end if
    else if (cls == "clojure.lang.Delay") then
       ! (force x) is Delay/force, which derefs a delay and hands
       ! anything else straight back -- which is what deref already
       ! does for a value that is not a reference type.
       if (mname == "force") then
          out = native(B_DEREF, "deref", [roots])
          return
       end if
    else if (cls == "clojure.lang.EnumerationSeq") then
       ! (enumeration-seq e) is EnumerationSeq/create, and a seq over
       ! an enumeration that does not exist is a seq over nothing --
       ! which `seq` already answers for nil.
       if (mname == "create") then
          out = native(B_SEQ, "seq", [roots])
          return
       end if
    else if (cls == "clojure.lang.MapEntry") then
       ! A MAP ENTRY IS A TWO-ELEMENT VECTOR here, which is what
       ! (key e) and (val e) already read and what Clojure's MapEntry
       ! is too -- it implements IPersistentVector and answers to two
       ! nths. So MapEntry/create is `vector`, and needs to exist
       ! because a record's own seq builds its entries with it.
       if (mname == "create") then
          out = native(B_VECTOR, "vector", [roots])
          return
       end if
    else if (cls == "clojure.lang.Util") then
       select case (mname)
       case ("equiv", "equals"); out = native(B_EQ, "=", [roots]); return
       case ("identical")
          ! REFERENCE IDENTITY, not =. Util.identical is
          ! (x == y) on the JVM, so (identical? [1] [1]) is false
          ! while (= [1] [1]) is true. Sharing the = builtin made
          ! it answer true, which was wrong on its own and became
          ! fatal once a record's equiv could be reached: that
          ! method opens with (identical? this other), so = on two
          ! records called equiv, which called = , until the stack
          ! ran out. Printing a record segfaulted in gc_equal.
          out = native(B_IDENTICAL, "identical?", [roots]); return
       case ("hash", "hasheq")
          out = native(B_HASH, "hash", [roots]); return
       case ("isReduced")
          out = native(B_ISREDUCED, "reduced?", [roots]); return
       case ("classOf")
          ! clotran's classes ARE its type tags, so classOf is
          ! clotran-type. Protocol dispatch then keys on :vector, :map
          ! and so on, and Object -- the catch-all every protocol
          ! extends -- is the keyword :Object.
          out = native(B_TYPE, "clotran-type", [roots]); return
       end select
    else if (cls == "clojure.lang.LazilyPersistentVector" .or. &
             cls == "LazilyPersistentVector") then
       if (mname == "create" .or. mname == "createOwning") then
          out = native(B_VEC, "vec", [roots]); return
       end if
    else if (cls == "clojure.lang.PersistentHashMap" .or. &
             cls == "clojure.lang.PersistentArrayMap") then
       if (mname == "create" .or. mname == "createWithCheck" .or. &
           mname == "createAsIfByAssoc") then
          out = native(B_HMAP, "hash-map", [roots]); return
       end if
    else if (cls == "clojure.lang.PersistentHashSet" .or. &
             cls == "clojure.lang.PersistentTreeSet") then
       ! A sorted set is an ORDINARY set here -- no ordering. core.clj
       ! reaches for one first to hold *loaded-libs*, which only ever
       ! asks about membership. DEVIATIONS.md 9.
       if (mname == "create" .or. mname == "createWithCheck") then
          out = native(B_HSET, "hash-set", [roots]); return
       end if
    else if (cls == "clojure.lang.PersistentTreeMap") then
       if (mname == "create" .or. mname == "createWithCheck") then
          out = native(B_HMAP, "hash-map", [roots]); return
       end if
    else if (cls == "System" .or. cls == "java.lang.System") then
       if (mname == "getProperty") then
          out = native(B_GETPROP, "clotran-get-property", [roots]); return
       end if
    else if (cls == "clojure.lang.Numbers") then
       select case (mname)
       case ("add", "addP", "unchecked_add", "unchecked_int_add")
          out = native(B_ADD, "+", [roots]); return
       case ("minus", "minusP", "unchecked_minus", "unchecked_int_subtract")
          out = native(B_SUB, "-", [roots]); return
       case ("multiply", "multiplyP", "unchecked_multiply")
          out = native(B_MUL, "*", [roots]); return
       case ("divide", "unchecked_divide", "unchecked_int_divide")
          out = native(B_DIV, "/", [roots]); return
       case ("lt"); out = native(B_LT, "<", [roots]); return
       case ("gt"); out = native(B_GT, ">", [roots]); return
       case ("lte"); out = native(B_LTE, "<=", [roots]); return
       case ("gte"); out = native(B_GTE, ">=", [roots]); return
       case ("equiv", "equal")
          ! Numbers/equiv is ==, NOT =. They disagree across types:
          ! (= 1 1.0) is false and (== 1 1.0) is true, because = is
          ! Object.equals -- a Long is never equal to a Double -- and
          ! == compares numeric VALUE. Routing this to B_EQ made
          ! (== 1 1.0) answer false.
          out = native(B_NUMEQ, "==", [roots]); return
       case ("abs")
          out = native(B_ABS, "abs", [roots]); return
       case ("compare"); out = native(B_COMPARE, "compare", [roots]); return
       case ("inc", "incP", "unchecked_inc", "unchecked_int_inc")
          out = native(B_INC, "inc", [roots]); return
       case ("dec", "decP", "unchecked_dec", "unchecked_int_dec")
          out = native(B_DEC, "dec", [roots]); return
       case ("remainder", "unchecked_int_remainder")
          out = native(B_REM, "rem", [roots]); return
       case ("quotient"); out = native(B_QUOT, "quot", [roots]); return
       case ("num"); out = native(B_IDENTITY, "identity", [roots]); return
       ! The bit operations. Fortran has these as intrinsics, so they
       ! are the one part of Numbers that maps across exactly.
       case ("and"); out = native(B_BITAND, "bit-and", [roots]); return
       case ("or"); out = native(B_BITOR, "bit-or", [roots]); return
       case ("xor"); out = native(B_BITXOR, "bit-xor", [roots]); return
       case ("not"); out = native(B_BITNOT, "bit-not", [roots]); return
       case ("andNot"); out = native(B_BITAND, "bit-and", [roots]); return
       case ("shiftLeft"); out = native(B_SHL, "bit-shift-left", [roots]); return
       case ("shiftRight", "unsignedShiftRight")
          out = native(B_SHR, "bit-shift-right", [roots]); return
       case ("isZero"); out = native(B_ZERO, "zero?", [roots]); return
       case ("isPos"); out = native(B_POS, "pos?", [roots]); return
       case ("isNeg"); out = native(B_NEG, "neg?", [roots]); return
       case ("max"); out = native(B_MAX, "max", [roots]); return
       case ("min"); out = native(B_MIN, "min", [roots]); return
       end select
    else if (cls == "Number" .or. cls == "java.lang.Number") then
       ! core.clj's one-argument arithmetic is ([x] (cast Number x)),
       ! and `cast` is (. c (cast x)) -- so without this, (+ 1.5),
       ! (- 1.5) and (* 2.0) all failed with "no such member".
       if (mname == "cast") then
          out = native(B_NUMCAST, "clotran-num-cast", [roots]); return
       end if
    else if (cls == "Class" .or. cls == "java.lang.Class") then
       if (mname == "forName") then
          out = native(B_FORNAME, "clotran-for-name", [roots]); return
       end if
    else if (cls == "clojure.lang.Iterate") then
       if (mname == "create") then
          out = native(B_ITERATE, "iterate", [roots]); return
       end if
    else if (cls == "clojure.lang.Cycle") then
       if (mname == "create") then
          out = native(B_CYCLE, "cycle", [roots]); return
       end if
    else if (cls == "clojure.lang.Repeat") then
       if (mname == "create") then
          out = native(B_REPEAT, "repeat", [roots]); return
       end if
    else if (cls == "clojure.lang.Range" .or. cls == "clojure.lang.LongRange") then
       if (mname == "create") then
          out = native(B_RANGE, "range", [roots]); return
       end if
    else if (cls == "java.util.regex.Pattern") then
       if (mname == "compile") then
          out = native(B_RE_COMPILE, "re-pattern", [roots]); return
       end if
    else if (cls == "clojure.lang.LockingTransaction") then
       ! dosync with no transaction: call the thunk. Single-threaded
       ! that is what a transaction does -- the retry, the isolation and
       ! the write skew are all about other threads. DEVIATIONS.md 11.
       if (mname == "runInTransaction") then
          out = native(B_RUNTX, "clotran-run-tx", [roots]); return
       end if
    else if (cls == "clojure.lang.Namespace") then
       if (mname == "find" .or. mname == "findOrCreate") then
          out = native(B_FINDNS, "find-ns", [roots]); return
       end if
    else if (cls == "clojure.lang.Var") then
       select case (mname)
       case ("pushThreadBindings")
          out = native(B_PUSHTB, "push-thread-bindings", [roots]); return
       case ("popThreadBindings")
          out = native(B_POPTB, "pop-thread-bindings", [roots]); return
       case ("find")
          out = native(B_FINDVAR, "clotran-find-var", [roots]); return
       case ("intern")
          ! Var.intern CREATES the Var in the namespace given, with
          ! the value given. Mapping it to a lookup meant defprotocol
          ! interned its protocol map and none of its METHODS -- so
          ! coll-reduce did not exist and reduce could not resolve.
          out = native(B_VARINTERN, "clotran-var-intern", [roots]); return
       end select
    else if (cls == "clojure.lang.Compiler") then
       if (mname == "eval") then
          out = native(B_EVAL, "eval", [roots]); return
       end if
       if (mname == "munge" .or. mname == "demunge") then
          ! munge makes a Clojure name legal as a JVM identifier --
          ! hyphens to underscores and so on. Nothing here constrains a
          ! name, so there is nothing to mangle and nothing to undo.
          out = native(B_IDENTITY, "identity", [roots]); return
       end if
       if (mname == "LOADER") then
          ! A class loader is a JVM thing with no analogue. nil is safe
          ! here: its only use is as a key in the map handed to
          ! pushThreadBindings, which skips anything that is not a Var.
          out = gc_nil(); return
       end if
       if (mname == "maybeResolveIn" .or. mname == "resolveIn" .or. &
            mname == "resolve") then
          ! Resolve a symbol to its Var, or nil. The namespace argument
          ! is ignored -- resolution here is current-ns then
          ! clojure.core, which is DEVIATIONS.md 3.
          out = native(B_MAYBERESOLVE, "clotran-maybe-resolve", [roots]); return
       end if
    else if (cls == "clojure.lang.Compiler$HostExpr") then
       ! The compiler internals sigs consults to normalise a :tag. Both
       ! answer nil here, which is the honest answer: there are no
       ! primitive tags and no classes to resolve a hint to, so
       ! resolve-tag leaves the parameter vector as written.
       if (mname == "maybeSpecialTag" .or. mname == "maybeClass") then
          out = native(B_ALWAYS_NIL, "clotran-nil", [roots]); return
       end if
    else if (cls == "clojure.lang.Symbol") then
       if (mname == "intern" .or. mname == "create") then
          out = native(B_SYMBOL, "symbol", [roots]); return
       end if
    else if (cls == "clojure.lang.Keyword") then
       if (mname == "intern" .or. mname == "find") then
          out = native(B_KEYWORD, "keyword", [roots]); return
       end if
    else if (cls == "clojure.lang.RT") then
       select case (mname)
       case ("baseLoader")
          out = native(B_BASELOADER, "clotran-base-loader", [roots]); return
       ! The array accessors alength, aget, aset and aclone inline to
       ! RT/... rather than to Array/..., so both spellings have to
       ! reach the same place.
       case ("alength")
          out = native(B_ALENGTH, "alength", [roots]); return
       case ("aget")
          out = native(B_AGET, "aget", [roots]); return
       case ("aset")
          out = native(B_ASET, "aset", [roots]); return
       case ("aclone")
          out = native(B_ACLONE, "aclone", [roots]); return
       ! The primitive casts. Fortran has its own integer and real
       ! kinds and clotran has one of each, so the width-named casts
       ! all land on the same two conversions.
       case ("longCast", "uncheckedLongCast", "intCast", "uncheckedIntCast", &
             "shortCast", "uncheckedShortCast", "byteCast", "uncheckedByteCast")
          out = native(B_LONGCAST, "long", [roots]); return
       case ("doubleCast", "uncheckedDoubleCast", "floatCast", "uncheckedFloatCast")
          out = native(B_DBLCAST, "double", [roots]); return
       case ("booleanCast"); out = native(B_BOOLCAST, "boolean", [roots]); return
       case ("charCast", "uncheckedCharCast")
          out = native(B_CHARCAST, "char", [roots]); return
       ! RT.nextID is the counter gensym counts on. Shared with the
       ! auto-gensym counter, so a gensym and an x# can never collide.
       case ("isReduced"); out = native(B_ISREDUCED, "reduced?", [roots]); return
       case ("toArray"); out = native(B_TOARRAY, "to-array", [roots]); return
       case ("nextID"); out = native(B_NEXTID, "clotran-next-id", [roots]); return
       case ("load"); out = native(B_RTLOAD, "clotran-rt-load", [roots]); return
       case ("subvec"); out = native(B_SUBVEC, "subvec", [roots]); return
       case ("first");  out = native(B_FIRST, "first", [roots]); return
       case ("next");   out = native(B_NEXT, "next", [roots]);   return
       case ("more");   out = native(B_REST, "rest", [roots]);   return
       case ("seq");    out = native(B_SEQ, "seq", [roots]);     return
       case ("cons");   out = native(B_CONS, "cons", [roots]);   return
       case ("count");  out = native(B_COUNT, "count", [roots]); return
       case ("get");    out = native(B_GET, "get", [roots]);     return
       case ("nth");    out = native(B_NTH, "nth", [roots]);     return
       case ("conj");   out = native(B_CONJ, "conj", [roots]);   return
       case ("assoc");  out = native(B_ASSOC, "assoc", [roots]); return
       case ("dissoc"); out = native(B_DISSOC, "dissoc", [roots]); return
       case ("pop"); out = native(B_POP, "pop", [roots]); return
       case ("peek"); out = native(B_PEEK, "peek", [roots]); return
       case ("contains"); out = native(B_STRCONTAINS, "clotran-dot-contains", [roots]); return
       case ("find"); out = native(B_FIND, "find", [roots]); return
       case ("keys");   out = native(B_KEYS, "keys", [roots]);   return
       case ("vals");   out = native(B_VALS, "vals", [roots]);   return
       end select
    end if
    ! Thread.currentThread is asked for ONE thing here: a stack trace
    ! to put a file and line on a test failure. clojure.test's do-report
    ! calls it on every :fail, so without it a failing assertion threw
    ! while being reported and came out as an ERROR instead -- which is
    ! why the whole suite read fail=0. There is one thread and there are
    ! no traces, so it answers itself and .getStackTrace answers empty.
    ! Character's static predicates. clojure.string leans on these,
    ! and so does anything classifying input a character at a time.
    ! One builtin id each: call_builtin dispatches on the id alone and
    ! cannot see which name the member table matched.
    if (cls == "Character" .or. cls == "java.lang.Character") then
       select case (mname)
       case ("isWhitespace");    out = native(B_ISWS, "clotran-ws?", [roots]); return
       case ("isUpperCase");     out = native(B_ISUPPER, "clotran-upper?", [roots]); return
       case ("isLowerCase");     out = native(B_ISLOWER, "clotran-lower?", [roots]); return
       case ("isDigit");         out = native(B_ISDIGIT, "clotran-digit?", [roots]); return
       case ("isLetter");        out = native(B_ISLETTER, "clotran-letter?", [roots]); return
       case ("isLetterOrDigit"); out = native(B_ISALNUM, "clotran-alnum?", [roots]); return
       case ("toUpperCase");     out = native(B_UPCASE, "clotran-upcase", [roots]); return
       case ("toLowerCase");     out = native(B_DOWNCASE, "clotran-downcase", [roots]); return
       end select
    end if
    if (cls == "Thread" .or. cls == "java.lang.Thread") then
       if (mname == "currentThread") then
          out = native(B_BASELOADER, "clotran-current-thread", [roots]); return
       end if
    end if
    if (cls == "Integer" .or. cls == "java.lang.Integer") then
       select case (mname)
       case ("MAX_VALUE"); out = gc_int(huge(0)); return
       case ("MIN_VALUE"); out = gc_int(-huge(0) - 1); return
       end select
    end if
    if (cls == "Integer" .or. cls == "java.lang.Integer" .or. &
         cls == "Long" .or. cls == "java.lang.Long") then
       select case (mname)
       case ("valueOf", "parseInt", "parseLong")
          out = native(B_INTVALUE, "clotran-int-value", [roots]); return
       end select
    end if
    if (cls == "Double" .or. cls == "java.lang.Double" .or. &
         cls == "Float" .or. cls == "java.lang.Float") then
       ! parse-double is (Double/valueOf s), and it is only reached
       ! after core.clj has already matched the string against its own
       ! regex -- so this converts, it does not validate.
       select case (mname)
       case ("valueOf", "parseDouble", "parseFloat")
          out = native(B_DBLVALUE, "clotran-double-value", [roots]); return
       case ("isNaN")
          out = native(B_ISNAN, "clotran-is-nan", [roots]); return
       case ("isInfinite")
          out = native(B_ISINF, "clotran-is-infinite", [roots]); return
       end select
    end if
    ! Class/TYPE is a JVM primitive-class constant -- Float/TYPE and
    ! friends, which core_print uses to dispatch on primitive ARRAY
    ! types. There are no primitive arrays here, so each answers a
    ! distinct keyword: inert, never equal to anything clotran
    ! produces, and enough for the dispatch table to be built.
    if (mname == "TYPE") then
       out = gc_key(cls // "/TYPE", [roots])
       return
    end if
    call fail("no such member: " // cls // "/" // mname)
  end function static_member

  ! Sets :macro true in the Var's metadata, creating the map if the Var
  ! has none. Var metadata is slot 2.
  subroutine var_set_macro(var, env)
    type(gc_value), intent(in) :: var, env
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
    if (gce_find(env, head, md)) return
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
  function resolve_var(sym, roots) result(var)
    type(gc_value), intent(in) :: sym, roots
    type(gc_value) :: var, bare, dns, ans
    character(len=:), allocatable :: t
    integer :: slash

    ! The namespace the enclosing function was DEFINED in comes
    ! FIRST. Clojure resolves a free symbol while compiling the form
    ! that contains it, in the namespace being compiled -- the caller's
    ! namespace never enters into it. Asking the current namespace
    ! first meant a function's meaning depended on who called it, which
    ! is the whole shadowing bug: see make_closure above.
    !
    ! With no enclosing closure -- a form typed at the REPL, or a
    ! top-level form being loaded -- there is no defining namespace and
    ! the current one is the right and only answer.
    if (gce_is(roots)) then
       if (gce_find(roots, gc_sym("__defining-ns__", [roots]), dns)) then
          var = gcn_lookup(dns, sym)
          if (gcn_is_var(var)) return
       end if
    end if

    var = gcn_lookup(gcn_current([roots]), sym)
    if (gcn_is_var(var)) return

    ! A QUALIFIED symbol names its own namespace. Syntax-quote produces
    ! these constantly -- every `when in core.clj reads as
    ! clojure.core/when -- so this is not an edge case, it is most of
    ! what a macro expands into.
    if (sym%tag == GCT_SYM) then
       t = gc_ref_text(sym%ref)
       slash = index(t, "/")
       if (slash > 1 .and. slash < len(t)) then
          bare = gc_sym(t(slash+1:), [roots])
          ! An ALIAS first. Without this the prefix was taken as a
          ! namespace name, find-or-create made an empty one, and the
          ! lookup could only miss -- which is every :as in every ns
          ! form Clojure's own test suite writes.
          ! In the DEFINING namespace first. Clojure resolves a
          ! symbol while compiling the form, in the namespace being
          ! compiled; clotran resolves at call time, when *ns* is
          ! wherever the caller happens to be. A deftest body invoked
          ! by run-tests is exactly that case -- the alias is real, it
          ! is just not in the namespace doing the calling.
          ans = gc_nil()
          if (gce_is(roots)) then
             if (gce_find(roots, gc_sym("__defining-ns__", [roots]), dns)) &
                  ans = alias_in(dns, t(1:slash-1), [roots, bare])
          end if
          if (gc_kind(ans) /= OBJ_NS) &
               ans = alias_target(t(1:slash-1), [roots, bare])
          if (gc_kind(ans) == OBJ_NS) then
             var = gcn_lookup(ans, bare)
             if (gcn_is_var(var)) return
          end if
          var = gcn_lookup(gcn_find_or_create(t(1:slash-1), [roots, bare]), bare)
          if (gcn_is_var(var)) return
          var = gc_nil()
          return
       end if
    end if

    var = gcn_lookup(gcn_find_or_create("clojure.core", [roots]), sym)
  end function resolve_var

  ! A MAP LITERAL EVALUATES ITS ENTRIES, and a set literal its members.
  ! {:k (+ 1 2)} is {:k 3}, not a map holding a form.
  !
  ! Vectors already did this; maps and sets did not, and the cost was
  ! not cosmetic. #{'&} held the form (quote &) rather than the symbol,
  ! so destructure's (some #{'&} b) never found the rest marker and
  ! every (let [[a & b] ...]) produced a binding for b with nothing
  ! bound to it.
  recursive function eval_map(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, k, v
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i

    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    call gca_entries(form, ks, vls)
    out = gca_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    do i = 1, size(ks)
       k = gce_eval(ks(i), vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3)])
       if (has_error) then
          call vs_leave(base); return
       end if
       v = gce_eval(vls(i), vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3), k])
       if (has_error) then
          call vs_leave(base); return
       end if
       out = gca_assoc(vs_get(base + 3), k, v, [vs_get(base + 1), vs_get(base + 3)])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function eval_map

  recursive function eval_set(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, item, mp
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i

    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)
    call gca_entries(gc_slot(form, 1), ks, vls)
    mp = gca_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, mp)
    do i = 1, size(ks)
       item = gce_eval(ks(i), vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3)])
       if (has_error) then
          call vs_leave(base); return
       end if
       mp = gca_assoc(vs_get(base + 3), item, item, [vs_get(base + 1), vs_get(base + 3)])
       call vs_set(base + 3, mp)
    end do
    out = gc_obj(OBJ_SET, [vs_get(base + 3)], [vs_get(base + 3)])
    call vs_leave(base)
  end function eval_set

  ! Evaluates the head and every argument, then applies. Arguments
  ! accumulate in a GC vector rather than a Fortran array for the same
  ! reason the reader does it: the collector cannot see a local array.
  recursive function eval_call(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, fn, args, rest, item
    integer :: base

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)

    ! A macro receives its arguments UNEVALUATED and its result is
    ! evaluated in the caller's environment, so the question has to be
    ! asked before anything is touched -- including the head itself.
    !
    ! Asked of the VAR, not of the function it holds, which is
    ! Compiler.isMacro. Two consequences worth naming: a local shadows
    ! a macro ("no local macros for now"), and (def foo when) binds a
    ! plain function, because the new Var carries no :macro.
    fn = macro_var(gcl_first(form), env)
    if (gcn_is_var(fn)) then
       call vs_set(base + 3, gcn_var_value(fn))
       out = expand_macro(vs_get(base + 3), vs_get(base + 1), vs_get(base + 2))
       if (.not. has_error) out = gce_eval(out, vs_get(base + 2), [vs_get(base + 1)])
       call vs_leave(base)
       return
    end if

    fn = gce_eval(gcl_first(form), env, [vs_get(base + 1)])
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 3, fn)

    args = gcv_empty([vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, args)
    rest = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 5, rest)
    do while (gcl_count(vs_get(base + 5)) > 0)
       item = gce_eval(gcl_first(vs_get(base + 5)), vs_get(base + 2), &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       if (has_error) then
          call vs_leave(base); return
       end if
       args = gcv_conj(vs_get(base + 4), item, &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 5)])
       call vs_set(base + 4, args)
       rest = gcl_rest(vs_get(base + 5), [vs_get(base + 1)])
       call vs_set(base + 5, rest)
    end do

    out = apply(vs_get(base + 3), vs_get(base + 4))
    call vs_leave(base)
  end function eval_call

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
  recursive function eval_try(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, item, head2, exc, child, fin
    logical :: caught
    integer :: base, i, n

    out = gc_nil()
    base = vs_enter(7)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    n = gcl_count(rest)
    fin = gc_nil()

    ! Body first: everything up to the first catch or finally.
    do i = 0, n - 1
       item = nth_of(vs_get(base + 1), i)
       if (is_clause(item, "catch") .or. is_clause(item, "finally")) exit
       call vs_set(base + 3, item)
       out = gce_eval(vs_get(base + 3), vs_get(base + 2), [vs_get(base + 1)])
       if (has_error) exit
    end do

    if (has_error) then
       ! Capture the thrown value BEFORE clearing: clearing resets it.
       exc = thrown_value()
       if (exc%tag == GCT_NIL) exc = error_value(gce_error(), [vs_get(base + 1)])
       call vs_set(base + 5, exc)
       caught = .false.
       do i = 0, n - 1
          item = nth_of(vs_get(base + 1), i)
          if (.not. is_clause(item, "catch")) cycle
          if (gcl_count(item) < 3) cycle
          call vs_set(base + 4, item)
          if (.not. catch_matches(nth_of(vs_get(base + 4), 1), vs_get(base + 5), &
               vs_get(base + 2))) cycle
          call gce_clear_error()
          child = gce_new(vs_get(base + 2), &
               [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5)])
          call vs_set(base + 6, child)
          call gce_set(vs_get(base + 6), strip_meta(nth_of(vs_get(base + 4), 2)), &
               vs_get(base + 5), [vs_get(base + 1), vs_get(base + 4)])
          out = eval_body(gcl_rest(gcl_rest(gcl_rest(vs_get(base + 4), &
               [vs_get(base + 1)]), [vs_get(base + 1)]), [vs_get(base + 1)]), &
               vs_get(base + 6))
          caught = .true.
          exit
       end do
    end if

    ! finally runs whether or not anything was caught, and its value is
    ! discarded -- but an error inside it wins.
    do i = 0, n - 1
       item = nth_of(vs_get(base + 1), i)
       if (.not. is_clause(item, "finally")) cycle
       call vs_set(base + 7, item)
       block
         logical :: had
         type(gc_value) :: saved_exc
         character(len=:), allocatable :: saved_msg
         had = has_error
         saved_msg = last_error
         saved_exc = thrown_value()
         call gce_clear_error()
         fin = eval_body(gcl_rest(vs_get(base + 7), [vs_get(base + 1)]), &
              vs_get(base + 2))
         if (.not. has_error .and. had) then
            has_error = .true.
            last_error = saved_msg
            call set_thrown(saved_exc)
         end if
       end block
       exit
    end do

    call vs_leave(base)
  end function eval_try

  ! (case* expr shift mask default map<case-int [test then]> table-type
  !  test-type skip-check?)
  !
  ! On the JVM this compiles to a tableswitch, which is the whole point
  ! of the shift/mask apparatus core.clj builds around it. Here it is a
  ! lookup in that same map, keyed on the case-int recomputed from the
  ! runtime value -- so clojure.lang.Util/hash MUST be gc_hash, because
  ! these keys were built with it at macroexpansion time. Constant time
  ! either way; only the constant differs.
  recursive function eval_case(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, val, entry, tt
    integer :: base, shift, mask, h, n
    logical :: hit

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    n = gcl_count(rest)

    val = gce_eval(nth_of(vs_get(base + 1), 0), vs_get(base + 2), &
         [vs_get(base + 1)])
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 3, val)

    shift = ival_of(nth_of(vs_get(base + 1), 1))
    mask = ival_of(nth_of(vs_get(base + 1), 2))
    call vs_set(base + 4, strip_meta(nth_of(vs_get(base + 1), 4)))

    ! :int keys on the integer itself; the two hash modes on gc_hash.
    tt = strip_meta(nth_of(vs_get(base + 1), 6))
    if (tt%tag == GCT_KEY .and. gc_ref_is(tt%ref, "int")) then
       h = ival_of(vs_get(base + 3))
    else
       h = gc_hash(vs_get(base + 3))
    end if
    ! A zero mask means the map was keyed on the raw hash, unshifted --
    ! prep-hashes only shifts when it had to squeeze the ints together.
    if (mask /= 0) h = iand(ishft(h, -shift), mask)

    entry = gca_get(vs_get(base + 4), gc_int(h))
    call vs_set(base + 5, strip_meta(entry))

    hit = .false.
    if (gc_kind(vs_get(base + 5)) == OBJ_VECTOR) then
       if (gcv_count(vs_get(base + 5)) == 2) then
          ! A case-int in skip-check holds a condp that re-tests for
          ! itself. It is there BECAUSE two constants hashed alike, so
          ! comparing against the stored test would ask the wrong
          ! question -- the stored test is the hash, not a constant.
          if (n >= 8 .and. in_skip(nth_of(vs_get(base + 1), 7), h)) then
             hit = .true.
          else
             hit = deep_equal(vs_get(base + 3), gcv_nth(vs_get(base + 5), 0), &
                  [vs_get(base + 3), vs_get(base + 5)])
          end if
       end if
    end if

    if (hit) then
       out = gce_eval(gcv_nth(vs_get(base + 5), 1), vs_get(base + 2), &
            [vs_get(base + 1)])
    else
       out = gce_eval(nth_of(vs_get(base + 1), 3), vs_get(base + 2), &
            [vs_get(base + 1)])
    end if
    call vs_leave(base)
  end function eval_case

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
    yes = (gc_ref_text(got%ref) == want)
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
    args = gcv_empty([vs_get(base + 1)])
    r = apply(gc_slot(vs_get(base + 1), 1), args)
    call vs_set(base + 2, r)
    if (has_error) then
       call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
       call vs_leave(base)
       return
    end if

    do while (gc_kind(vs_get(base + 2)) == OBJ_LAZY)
       call gce_force(vs_get(base + 2))
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

  ! `temp/do-template -- syntax-quote RESOLVES an alias, so what the
  ! expansion carries is clojure.template/do-template and the reader of
  ! that expansion needs to know nothing about temp. Compiler's
  ! resolveSymbol does it while READING; clotran expands at eval time,
  ! so the namespace to ask is the one the quote was WRITTEN in -- which
  ! the closure carries as __defining-ns__ -- and NOT *ns*, which by
  ! then is whoever called the macro.
  !
  ! clojure.test's `are` is the case that forced this: it aliases
  ! clojure.template as temp, and every (are ...) in Clojure's own test
  ! suite expands through it.
  function qq_alias(sym, env) result(out)
    type(gc_value), intent(in) :: sym, env
    type(gc_value) :: out, nsv, tgt, dns
    character(len=:), allocatable :: t
    integer :: slash

    out = sym
    if (sym%tag /= GCT_SYM) return
    t = gc_ref_text(sym%ref)
    nsv = gc_nil()
    if (gce_is(env)) then
       if (gce_find(env, gc_sym("__defining-ns__", [sym]), dns)) nsv = dns
    end if
    if (gc_kind(nsv) /= OBJ_NS) nsv = gcn_current([sym])

    slash = index(t, "/")
    if (slash > 1 .and. slash < len(t)) then
       tgt = alias_in(nsv, t(1:slash-1), [sym])
       if (gc_kind(tgt) /= OBJ_NS) return
       out = gc_sym(gcn_name(tgt) // "/" // t(slash+1:), [sym])
       return
    end if

    ! An UNQUALIFIED symbol resolves against the writing namespace too:
    ! `apply-template inside clojure.template means that namespace's
    ! Var, not clojure.core's. clotran used to leave it bare and let
    ! resolution fall back to clojure.core, which is right for core.clj
    ! and wrong for every other library.
    !
    ! Guarded on the lookup SUCCEEDING there, so a special form or a
    ! core name is still left alone -- exactly the symbols that have no
    ! Var in the writing namespace, and exactly the ones the fallback
    ! already handles.
    ! NOT for clojure.core. Its names already resolve by fallback
    ! (deviation 3), so qualifying them buys nothing -- and it produced
    ! clojure.core/<, clojure.core/chunked-seq? and friends, which
    ! resolve at a REPL but not from inside every evaluation context,
    ! turning a whole test file into one 'not found'. The case this is
    ! for is a LIBRARY referring to its own Var: `apply-template inside
    ! clojure.template.
    if (gcn_name(nsv) == "clojure.core") return
    ! NOT for clojure.core. Its names already resolve by fallback
    ! (deviation 3), so qualifying them buys nothing -- and it produced
    ! clojure.core/<, clojure.core/chunked-seq? and friends, which
    ! resolve at a REPL but not from inside every evaluation context,
    ! turning a whole test file into one "not found". The case this is
    ! for is a LIBRARY referring to its own Var, as clojure.template
    ! does with apply-template.
    if (gcn_name(nsv) == "clojure.core") return
    if (.not. gcn_is_var(gcn_lookup(nsv, sym))) return
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
  recursive function expand_clauses(clauses, env) result(out)
    type(gc_value), intent(in) :: clauses, env
    type(gc_value) :: out, walk, clause, built
    integer :: base, i, n

    base = vs_enter(4)
    call vs_set(base + 1, clauses)
    call vs_set(base + 2, env)
    n = gcl_count(clauses)
    out = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 3, out)
    do i = n - 1, 0, -1
       clause = nth_of(vs_get(base + 1), i)
       call vs_set(base + 4, clause)
       built = gcl_cons(gcl_first(vs_get(base + 4)), &
            expand_forms(gcl_rest(vs_get(base + 4), [vs_get(base + 1)]), &
                         vs_get(base + 2)), &
            [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       out = gcl_cons(built, vs_get(base + 3), [vs_get(base + 1), built])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function expand_clauses

  recursive function expand_forms(forms, env) result(out)
    type(gc_value), intent(in) :: forms, env
    type(gc_value) :: out, item
    integer :: base, i, n

    base = vs_enter(3)
    call vs_set(base + 1, forms)
    call vs_set(base + 2, env)
    n = gcl_count(forms)
    out = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 3, out)
    do i = n - 1, 0, -1
       item = macroexpand_all(nth_of(vs_get(base + 1), i), vs_get(base + 2))
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 1), item])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function expand_forms

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
  recursive function gce_analyze(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out
    ev_depth = 0
    out = macroexpand_all(form, env)
  end function gce_analyze

  ! No depth limit of its own: Clojure has none, and the runaway
  ! expansions this used to catch were bugs in the walk, not depth --
  ! it treated a metadata wrapper and a lazy seq as leaves, so whole
  ! function bodies escaped analysis and were re-expanded at call time.
  ! Both are fixed. Genuine runaway expansion now surfaces as the
  ! evaluation depth limit, which is where the JVM would report it too.
  recursive function macroexpand_all(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out
    out = mx_walk(form, env)
  end function macroexpand_all

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

  recursive function mx_walk(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, mvar, expanded, item
    integer :: base, i, n

    out = form
    base = vs_enter(4)
    call vs_set(base + 1, form)
    call vs_set(base + 2, env)

    if (gc_kind(vs_get(base + 1)) == OBJ_LAZY .or. &
         gc_kind(vs_get(base + 1)) == OBJ_SEQ) then
       ! A SEQ IS CODE, same as a list. A macro assembles its expansion
       ! with cons, list* and concat, so pieces of it come back as lazy
       ! cells and views rather than cons chains -- lazy-seq itself
       ! expands through (list* ^{:once true} fn* [] body), and treating
       ! that as a leaf meant the body of every lazy-seq in core.clj
       ! escaped analysis and kept its macros for call time.
       call vs_set(base + 1, seq_to_list(vs_get(base + 1), &
            [vs_get(base + 1), vs_get(base + 2)]))
    end if

    if (gc_kind(vs_get(base + 1)) == OBJ_META) then
       ! METADATA IS TRANSPARENT TO THE WALK, and this one mattered more
       ! than any other place: defn returns its expansion wrapped --
       ! (with-meta (cons `fn fdecl) {:rettag ...}) -- so treating the
       ! wrapper as a leaf meant EVERY function body escaped analysis
       ! and kept its macros to be re-expanded at call time.
       out = gc_obj(OBJ_META, &
            [macroexpand_all(gc_slot(vs_get(base + 1), 1), vs_get(base + 2)), &
             gc_slot(vs_get(base + 1), 2)], &
            [vs_get(base + 1), vs_get(base + 2)])
       call vs_leave(base)
       return
    end if

    if (gcv_is(vs_get(base + 1))) then
       ! A vector holds forms too -- (let [x (when a b)] ...).
       out = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, out)
       do i = 0, gcv_count(vs_get(base + 1)) - 1
          item = macroexpand_all(gcv_nth(vs_get(base + 1), i), vs_get(base + 2))
          out = gcv_conj(vs_get(base + 3), item, [vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 3, out)
       end do
       out = vs_get(base + 3)
       call vs_leave(base)
       return
    end if

    if (.not. gcl_is(vs_get(base + 1))) then
       call vs_leave(base)
       return
    end if
    if (gcl_count(vs_get(base + 1)) == 0) then
       call vs_leave(base)
       return
    end if

    head = strip_meta(gcl_first(vs_get(base + 1)))
    ! quote and quasiquote hold DATA, not code, so the walk stops at
    ! both. Descending into a template expanded the `let` inside
    ! (`(let [v# ...] ...)) at definition time, before qq_expand had
    ! renamed v# -- which left a bare v# in the emitted code.
    !
    ! Clojure never has to make this distinction: syntax-quote is a
    ! READER macro there, so by the time analyze sees the form the
    ! template is already (seq (concat ...)) over quoted data. Ours is
    ! a special form, which is DEVIATIONS.md 6.
    if (head%tag == GCT_SYM) then
       if (gc_ref_is(head%ref, "quote") .or. &
            gc_ref_is(head%ref, "quasiquote")) then
          call vs_leave(base)
          return
       end if
    end if

    ! Expand this form for as long as it names a macro.
    do
       mvar = macro_var(head, vs_get(base + 2))
       if (.not. gcn_is_var(mvar)) exit
       expanded = expand_macro(gcn_var_value(mvar), vs_get(base + 1), vs_get(base + 2))
       ! An expansion failure is a COMPILE ERROR, and it propagates.
       ! Swallowing it left the form unexpanded and handed it to the
       ! evaluator, which expanded it again at call time -- against
       ! whatever the macro had become by then. That is precisely the
       ! re-expansion this pass exists to prevent.
       if (has_error) exit
       ! A macro can return anything, including a seq that is not a
       ! list; the rest of this walk needs a list.
       if (gc_kind(expanded) == OBJ_LAZY .or. gc_kind(expanded) == OBJ_SEQ) &
            expanded = seq_to_list(expanded, [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 1, expanded)
       if (.not. gcl_is(vs_get(base + 1))) then
          out = macroexpand_all(vs_get(base + 1), vs_get(base + 2))
          call vs_leave(base)
          return
       end if
       if (gcl_count(vs_get(base + 1)) == 0) exit
       head = strip_meta(gcl_first(vs_get(base + 1)))
       if (head%tag == GCT_SYM) then
          if (gc_ref_is(head%ref, "quote") .or. &
               gc_ref_is(head%ref, "quasiquote")) then
             out = vs_get(base + 1)
             call vs_leave(base)
             return
          end if
       end if
    end do

    n = gcl_count(vs_get(base + 1))
    out = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 3, out)
    do i = n - 1, 0, -1
       item = macroexpand_all(nth_of(vs_get(base + 1), i), vs_get(base + 2))
       out = gcl_cons(item, vs_get(base + 3), [vs_get(base + 1), item])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function mx_walk

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
  recursive function range_cell(lo, hi, stp, roots) result(out)
    integer, intent(in) :: lo, hi, stp
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, frame, body, callf, thunk, tail
    integer :: base

    out = gcl_empty(roots)
    if (stp > 0 .and. lo >= hi) return
    if (stp < 0 .and. lo <= hi) return

    base = vs_enter(3)
    frame = gce_new(gc_nil(), roots)
    call vs_set(base + 1, frame)
    ! The head is lo; the frame carries where the TAIL starts.
    call gce_set(vs_get(base + 1), gc_sym("__lo", [vs_get(base + 1)]), &
         gc_int(lo + stp), [vs_get(base + 1)])
    call gce_set(vs_get(base + 1), gc_sym("__hi", [vs_get(base + 1)]), &
         gc_int(hi), [vs_get(base + 1)])
    call gce_set(vs_get(base + 1), gc_sym("__st", [vs_get(base + 1)]), &
         gc_int(stp), [vs_get(base + 1)])

    ! (clojure.lang.Range/create __lo __hi __st)
    callf = gcl_empty([vs_get(base + 1)])
    callf = gcl_cons(gc_sym("__st", [vs_get(base + 1)]), callf, &
         [vs_get(base + 1), callf])
    callf = gcl_cons(gc_sym("__hi", [vs_get(base + 1)]), callf, &
         [vs_get(base + 1), callf])
    callf = gcl_cons(gc_sym("__lo", [vs_get(base + 1)]), callf, &
         [vs_get(base + 1), callf])
    callf = gcl_cons(gc_sym("clojure.lang.Range/create", [vs_get(base + 1)]), &
         callf, [vs_get(base + 1), callf])
    call vs_set(base + 2, callf)
    body = gcl_cons(vs_get(base + 2), gcl_empty([vs_get(base + 2)]), &
         [vs_get(base + 2)])
    call vs_set(base + 2, body)

    thunk = gc_obj(OBJ_CLOSURE, [gcv_empty([vs_get(base + 2)]), &
         vs_get(base + 2), vs_get(base + 1), gc_nil()], &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, thunk)
    tail = gc_obj(OBJ_LAZY, [vs_get(base + 3), gc_nil(), gc_nil()], &
         [vs_get(base + 3)])
    call gc_set_i1(tail, LAZY_PENDING)
    call vs_set(base + 3, tail)
    out = gc_obj(OBJ_LAZY, [gc_nil(), gc_int(lo), vs_get(base + 3)], &
         [vs_get(base + 3)])
    call gc_set_i1(out, LAZY_CONS)
    call vs_leave(base)
  end function range_cell

  recursive function iterate_cell(f, x, roots) result(out)
    type(gc_value), intent(in) :: f, x
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, frame, body, callf, nextf, thunk, tail
    integer :: base

    base = vs_enter(6)
    call vs_set(base + 1, f)
    call vs_set(base + 2, x)
    frame = gce_new(gc_nil(), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, frame)
    call gce_set(vs_get(base + 3), gc_sym("__f", [vs_get(base + 3)]), &
         vs_get(base + 1), [vs_get(base + 1), vs_get(base + 3)])
    call gce_set(vs_get(base + 3), gc_sym("__x", [vs_get(base + 3)]), &
         vs_get(base + 2), [vs_get(base + 2), vs_get(base + 3)])

    ! (__f __x)
    callf = gcl_empty([vs_get(base + 3)])
    callf = gcl_cons(gc_sym("__x", [vs_get(base + 3)]), callf, &
         [vs_get(base + 3), callf])
    callf = gcl_cons(gc_sym("__f", [vs_get(base + 3)]), callf, &
         [vs_get(base + 3), callf])
    call vs_set(base + 4, callf)

    ! (clojure.lang.Iterate/create __f (__f __x))
    nextf = gcl_empty([vs_get(base + 4)])
    nextf = gcl_cons(vs_get(base + 4), nextf, [vs_get(base + 4), nextf])
    nextf = gcl_cons(gc_sym("__f", [vs_get(base + 4)]), nextf, &
         [vs_get(base + 4), nextf])
    nextf = gcl_cons(gc_sym("clojure.lang.Iterate/create", &
         [vs_get(base + 4)]), nextf, [vs_get(base + 4), nextf])
    body = gcl_cons(nextf, gcl_empty([vs_get(base + 4)]), &
         [vs_get(base + 4), nextf])
    call vs_set(base + 5, body)

    thunk = gc_obj(OBJ_CLOSURE, [gcv_empty([vs_get(base + 5)]), &
         vs_get(base + 5), vs_get(base + 3), gc_nil()], &
         [vs_get(base + 3), vs_get(base + 5)])
    call vs_set(base + 6, thunk)
    tail = gc_obj(OBJ_LAZY, [vs_get(base + 6), gc_nil(), gc_nil()], &
         [vs_get(base + 6)])
    call gc_set_i1(tail, LAZY_PENDING)
    call vs_set(base + 6, tail)
    out = gc_obj(OBJ_LAZY, [gc_nil(), vs_get(base + 2), vs_get(base + 6)], &
         [vs_get(base + 2), vs_get(base + 6)])
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
       params = gc_slot(fn, 1)
       body = gc_slot(fn, 2)
       if (gcl_is(gc_slot(fn, 4))) then
          if (.not. select_clause(gc_slot(fn, 4), gcv_count(args), params, body)) then
             call fail("no matching arity")
             call vs_leave(base); return
          end if
       end if
       call vs_set(base + 4, body)
       child = bind_params(params, args, gc_slot(fn, 3))
       if (has_error) then
          call vs_leave(base); return
       end if
       call vs_set(base + 3, child)
       ! A fn* body is a recur point, exactly like loop*: recur rebinds
       ! the parameters and re-enters the body rather than growing the
       ! stack, which is what makes a self-recursive function with
       ! recur run in constant space.
       do
          out = eval_body(vs_get(base + 4), vs_get(base + 3))
          if (has_error) exit
          if (gc_kind(out) /= OBJ_RECUR) exit
          child = bind_params(params, gc_slot(out, 1), gc_slot(vs_get(base + 1), 3), .true.)
          if (has_error) exit
          call vs_set(base + 3, child)
       end do
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
             out = gca_get(strip_meta(gcv_nth(args, 0)), fn)
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
               if (ix%tag == GCT_INT) out = gcv_nth(fn, ix%ival)
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
    integer :: base, i, n, acc
    logical :: hit

    out = gc_nil()
    hit = .false.
    n = gcv_count(args)
    ! Three slots: args, plus two scratch for the builtins that
    ! accumulate a collection (conj onto a map, the host create
    ! statics). Writing base + 2 out of a one-slot frame is a write
    ! past the stack top, which reads back as nil.
    base = vs_enter(3)
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
            logical :: any_real
            real(gc_dp) :: racc
            any_real = .false.
            do i = 0, n - 1
               b = gcv_nth(args, i)
               if (b%tag == GCT_REAL) any_real = .true.
            end do
            a = gcv_nth(args, 0)
            if (any_real) then
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
                  b = gcv_nth(args, i)
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
         if (gcv_is(coll) .or. coll%tag == GCT_STR) then
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
       out = gca_get(a, gcv_nth(args, 1))
       if (out%tag == GCT_NIL .and. n >= 3) then
          if (.not. gca_contains(a, gcv_nth(args, 1))) out = gcv_nth(args, 2)
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
       out = gca_assoc(a, &
            gcv_nth(vs_get(base + 1), 1), &
            gcv_nth(vs_get(base + 1), 2), [vs_get(base + 1)])
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
       if (a%tag == GCT_REAL .or. b%tag == GCT_REAL) then
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
       a = gcv_nth(args, 0)
       if (a%tag == GCT_REAL) then
          out = gc_int(int(a%rval))
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
         if (v%tag == GCT_INT .or. v%tag == GCT_REAL) then
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
         if (x%tag /= GCT_INT .and. x%tag /= GCT_REAL) then
            call fail("== : not a number")
         else
            do k = 1, n - 1
               y = strip_meta(gcv_nth(args, k))
               if (y%tag /= GCT_INT .and. y%tag /= GCT_REAL) then
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
         else
            out = gc_int(abs(x%ival))
         end if
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
         integer :: k, h, at, nsub, iv, own_rank, foff, fstr
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
         integer :: u, st, fsize, j
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
            forms = gcr_read_all(text, [vs_get(base + 1), vs_get(base + 2)])
            if (gcr_has_error()) then
               call fail("load-file " // path // ": " // gcr_error())
            else
               call vs_set(base + 3, forms)
               do j = 0, gcv_count(vs_get(base + 3)) - 1
                  f = gce_analyze(gcv_nth(vs_get(base + 3), j), vs_get(base + 2))
                  if (has_error) exit
                  out = gce_eval(f, vs_get(base + 2), &
                       [vs_get(base + 1), vs_get(base + 3)])
                  if (has_error) exit
               end do
            end if
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
       call var_set_macro(a, gc_nil())
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
    case (B_ISWS, B_ISUPPER, B_ISLOWER, B_ISDIGIT, B_ISLETTER, B_ISALNUM)
       block
         type(gc_value) :: cv
         character :: c
         cv = strip_meta(gcv_nth(args, 0))
         c = achar(max(0, min(255, cv%ival)))
         select case (id)
         case (B_ISWS)
            out = gc_bool(c == " " .or. c == achar(9) .or. c == achar(10) &
                 .or. c == achar(13) .or. c == achar(12))
         case (B_ISUPPER); out = gc_bool(c >= "A" .and. c <= "Z")
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
       ! (.write w s). A char writes as itself; anything else goes
       ! through str, as Writer.write(int) does for a code point.
       block
         type(gc_value) :: w
         w = strip_meta(gcv_nth(args, 0))
         if (gc_kind(w) == OBJ_WRITER) then
            write(gc_i1(w), '(A)', advance='no') text_of(gcv_nth(args, 1))
         else if (gc_kind(w) == OBJ_SB) then
            call gc_set_slot(w, 1, gc_str( &
                 text_of(gc_slot(w, 1)) // text_of(gcv_nth(args, 1)), &
                 [vs_get(base + 1)]))
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
       out = gc_str("src/clj", [vs_get(base + 1)])
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
         type(gc_value) :: coll
         coll = strip_meta(gcv_nth(args, 0))
         if (coll%tag == GCT_STR) then
            out = gc_bool(index(text_of(coll), text_of(gcv_nth(args, 1))) > 0)
         else if (gc_kind(coll) == OBJ_INST) then
            ! THE path contains? takes: core.clj's contains? is
            ! (. clojure.lang.RT (contains coll key)), which lands
            ! here rather than on the contains? builtin.
            out = inst_invoke(coll, "containsKey", rest_args(args, 1), hit)
            if (.not. hit) out = gc_bool(gca_contains(coll, gcv_nth(args, 1)))
         else
            if (gc_kind(coll) == OBJ_SET) coll = gc_slot(coll, 1)
            out = gc_bool(gca_contains(coll, gcv_nth(args, 1)))
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
       ! A Java array is a VECTOR here -- there is no other kind of
       ! indexable, and every use core.clj makes of to-array feeds
       ! it straight back into a seq.
       out = coll_to_vector(gcv_nth(args, 0), [vs_get(base + 1)])
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
         type(gc_value) :: iv
         integer :: lo, hi, stp
         lo = 0; stp = 1
         iv = strip_meta(gcv_nth(args, 0))
         hi = int(iv%ival)
         if (n >= 2) then
            lo = hi
            iv = strip_meta(gcv_nth(args, 1))
            hi = int(iv%ival)
         end if
         if (n >= 3) then
            iv = strip_meta(gcv_nth(args, 2))
            stp = int(iv%ival)
         end if
         out = range_cell(lo, hi, stp, [vs_get(base + 1)])
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
         if (gc_kind(coll) == OBJ_SET) coll = gc_slot(coll, 1)
         out = gc_bool(gca_contains(coll, gcv_nth(args, 1)))
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
    case (B_SETVAL)
       a = gcv_nth(args, 0)
       out = gcv_nth(args, 1)
       call gc_set_slot(a, 1, out)
    case (B_SWAPVAL)
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
         if (.not. has_error) call gc_set_slot(vs_get(lb + 1), 1, out)
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
         ned = text_of(gcv_nth(args, 1))
         hit = 0
         if (len(ned) > 0 .and. len(ned) <= len(hay)) then
            do j = 1, len(hay) - len(ned) + 1
               if (hay(j:j+len(ned)-1) == ned) hit = j
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
       block
         character(len=:), allocatable :: hay, ned
         hay = text_of(gcv_nth(args, 0))
         ned = text_of(gcv_nth(args, 1))
         out = gc_int(index(hay, ned) - 1)
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
                call vs_leave(base)
                return
             end if
             call gc_set_slot(vs_get(base + 2), 2, b)
             call gc_set_i1(vs_get(base + 2), 1)
             a = vs_get(base + 2)
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
       a = gcv_nth(args, 0); b = gcv_nth(args, 1)
       if (a%tag == GCT_INT .and. b%tag == GCT_INT) then
          ! Integer division only when it divides exactly; Clojure
          ! gives a Ratio otherwise, and a silent truncation here would
          ! be worse than a double.
          if (b%ival /= 0) then
             if (mod(a%ival, b%ival) == 0) then
                out = gc_int(a%ival / b%ival)
             else
                out = gc_real(real(a%ival, gc_dp) / real(b%ival, gc_dp))
             end if
          else
             call fail("Divide by zero")
          end if
       else
          out = gc_real(num_dbl(a) / num_dbl(b))
       end if
    case (B_INC, B_DEC)
       a = gcv_nth(args, 0)
       if (a%tag == GCT_INT) then
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
       a = gcv_nth(args, 0); b = gcv_nth(args, 1)
       if (num_lt(a, b)) then
          out = gc_int(-1)
       else if (num_lt(b, a)) then
          out = gc_int(1)
       else
          out = gc_int(0)
       end if
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
  function lazy_len(v) result(n)
    type(gc_value), intent(in) :: v
    type(gc_value) :: p
    integer :: base, n
    n = 0
    base = vs_enter(1)
    p = v
    call vs_set(base + 1, p)
    do
       if (gc_kind(vs_get(base + 1)) == OBJ_LAZY) then
          call gce_force(vs_get(base + 1))
          if (gc_i1(vs_get(base + 1)) /= LAZY_CONS) exit
          n = n + 1
          call vs_set(base + 1, gc_slot(vs_get(base + 1), 3))
       else if (gcl_is(vs_get(base + 1))) then
          n = n + gcl_count(vs_get(base + 1))
          exit
       else
          exit
       end if
    end do
    call vs_leave(base)
  end function lazy_len

  function nth_sym_ref(l) result(r)
    type(gc_value), intent(in) :: l
    type(gc_value) :: x
    integer :: r
    x = gcl_first(l)
    r = x%ref
  end function nth_sym_ref

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
         gc_kind(v) == OBJ_LAZY .or. gc_kind(v) == OBJ_SEQ
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

  function seq_at(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    out = gc_nil()
    if (gcl_is(v)) then
       out = nth_of(v, i)
    else if (gcv_is(v)) then
       out = gcv_nth(v, i)
    end if
  end function seq_at

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
       return
    end if
    if (gc_kind(v) == OBJ_SEQ) then
       if (seq_len(gc_slot(v, 1)) > gc_i1(v)) out = v
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
    integer :: h, iv, real_at
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
    case ("java.util.regex.Pattern"); yes = (t == "regex")
    case ("java.util.regex.Matcher"); yes = (t == "matcher")
    case ("clojure.lang.Reduced")
       ! A Reduced is the one-key map (reduced x) builds, so instance?
       ! asks for the key. Without this reduce returned the WRAPPER
       ! instead of unwrapping it on an early exit.
       yes = gca_contains(strip_meta(v), gc_key("clotran/reduced", [v]))
    case ("Throwable", "java.lang.Throwable", "Exception", "java.lang.Exception", &
          "Error", "IExceptionInfo", "clojure.lang.IExceptionInfo")
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
    case ("Number", "java.lang.Number"); yes = (t == "int" .or. t == "double")
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
    else
       d = real(v%ival, gc_dp)
    end if
  end function num_dbl

  ! A value as plain text: a string'\''s own characters, anything else
  ! printed the way `str` prints it.
  ! A writer is nothing but the Fortran unit it writes to. No buffer:
  ! the host already has one, and giving it a second would mean every
  ! print needed an explicit flush to be seen.
  ! clotran's classes ARE its type tags, but core.clj registers its
  ! print-method methods on the JVM INTERFACES -- IPersistentVector,
  ! ISeq, Number. With no hierarchy, (class [1 2]) answered :vector,
  ! matched no method, and fell to :default -- whose IObj branch calls
  ! print-method on that same vector again. Unbounded recursion, and
  ! the segfault that made (pr [1 2]) kill the process.
  !
  ! This is DEVIATIONS 8's missing hierarchy, cut down to the fixed
  ! host part of it: what each clotran type would implement on the JVM,
  ! most specific first. Consulted only AFTER an exact miss and only
  ! BEFORE :default, so no dispatch that resolves today can change.
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

    select case (t)
    case ("vector")
       select case (i)
       case (1); k = gc_key("clojure.lang.IPersistentVector", [roots])
       case (2); k = gc_key("java.util.List", [roots])
       case (3); k = gc_key("java.util.RandomAccess", [roots])
       end select
    case ("map")
       select case (i)
       case (1); k = gc_key("clojure.lang.IPersistentMap", [roots])
       case (2); k = gc_key("java.util.Map", [roots])
       end select
    case ("set")
       select case (i)
       case (1); k = gc_key("clojure.lang.IPersistentSet", [roots])
       case (2); k = gc_key("java.util.Set", [roots])
       end select
    case ("list", "seq", "lazy", "cons")
       select case (i)
       case (1); k = gc_key("clojure.lang.ISeq", [roots])
       case (2); k = gc_key("java.util.List", [roots])
       end select
    case ("keyword")
       if (i == 1) k = gc_key("clojure.lang.Keyword", [roots])
    case ("symbol")
       if (i == 1) k = gc_key("clojure.lang.Symbol", [roots])
    case ("var")
       if (i == 1) k = gc_key("clojure.lang.Var", [roots])
    case ("atom")
       if (i == 1) k = gc_key("clojure.lang.IDeref", [roots])
    case ("regex")
       if (i == 1) k = gc_key("java.util.regex.Pattern", [roots])
    case ("string")
       if (i == 1) k = gc_key("String", [roots])
    case ("char")
       if (i == 1) k = gc_key("java.lang.Character", [roots])
    case ("bool")
       if (i == 1) k = gc_key("Boolean", [roots])
    case ("error")
       if (i == 1) k = gc_key("Throwable", [roots])
    case ("int")
       if (i == 1) k = gc_key("Number", [roots])
    case ("float")
       select case (i)
       case (1); k = gc_key("Double", [roots])
       case (2); k = gc_key("Number", [roots])
       end select
    end select
    ! Everything is an Object, which is where core.clj's catch-all
    ! print-method is registered.
    if (k%tag == GCT_NIL .and. i == 4) k = gc_key("Object", [roots])
  end function host_super

  ! The classpath. One root was enough while only core.clj was being
  ! loaded, but Clojure's own test suite lives under test/clj and
  ! requires clojure.test-helper from there. First root holding the
  ! file wins, which is what a classpath means.
  function classpath_find(rel) result(path)
    character(len=*), intent(in) :: rel
    character(len=:), allocatable :: path, cand
    character(len=8) :: roots(3)
    logical :: there
    integer :: i

    roots(1) = "src/clj"
    roots(2) = "test/clj"
    roots(3) = "."
    ! The src/clj spelling is the fallback too, so a genuinely missing
    ! file still reports the path a reader would expect to see.
    path = "src/clj/" // rel // ".clj"
    do i = 1, 3
       cand = trim(roots(i)) // "/" // rel // ".clj"
       inquire(file=cand, exist=there)
       if (there) then
          path = cand
          return
       end if
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
       if (gca_is(vs_get(base + 2))) then
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

end module GCEval
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

  ! The auto-gensym map for the syntax-quote currently being expanded,
  ! and the counter that makes each name unique. GENSYM_ENV in
  ! LispReader is a dynamic Var bound around one syntax-quote; a
  ! module variable plus a depth count is the same scoping here.
  type(gc_root), save :: gensym_root
  integer, save :: gensym_id = 0
  integer, save :: qq_depth = 0

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

    call gcp_set_forcer(gce_force)
    call gcn_reset(roots)
    base = vs_enter(2)
    env = gce_new(gc_nil(), roots)
    call vs_set(base + 1, env)
    core = gcn_find_or_create("clojure.core", [vs_get(base + 1)])
    call vs_set(base + 2, core)
    call bind_builtin(core, "+", B_ADD)
    call bind_builtin(core, "-", B_SUB)
    call bind_builtin(core, "*", B_MUL)
    call bind_builtin(core, "=", B_EQ)
    call bind_builtin(core, "<", B_LT)
    call bind_builtin(core, "list", B_LIST)
    call bind_builtin(core, "vector", B_VECTOR)
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

  recursive function gce_eval(form, env, roots) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, head
    integer :: base
    logical :: found

    out = gc_nil()
    if (has_error) return

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
          head = resolve_var(form, vs_get(base + 1))
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
             out = gc_key(gc_ref_text(form%ref), [vs_get(base + 1)])
             found = .true.
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
       case default
          out = form ! maps, closures, builtins: self-evaluating here
       end select
    case default
       out = form ! nil, bool, int, real, char, string, keyword
    end select

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
          gc_ref_is(sym%ref, "loop*") .or. gc_ref_is(sym%ref, "recur") .or. &
          gc_ref_is(sym%ref, "defmacro*") .or. gc_ref_is(sym%ref, "quasiquote") .or. &
          gc_ref_is(sym%ref, "try*") .or. gc_ref_is(sym%ref, "throw") .or. &
          gc_ref_is(sym%ref, "lazy-seq*") .or. gc_ref_is(sym%ref, ".") .or. &
          gc_ref_is(sym%ref, "new") .or. &
          gc_ref_is(sym%ref, "var")
  end function is_special

  recursive function eval_special(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, rest, a, b
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
       b = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (.not. has_error) then
          block
            type(gc_value) :: nm, md, var
            ! The name may arrive wrapped: (def ^{:macro true} let ...).
            nm = vs_get(base + 4)
            md = gc_nil()
            if (gc_kind(nm) == OBJ_META) then
               md = gc_slot(nm, 2)
               nm = strip_meta(nm)
            end if
            call vs_set(base + 4, nm)
            var = gcn_intern(gcn_current([vs_get(base + 1)]), &
                 vs_get(base + 4), b, [vs_get(base + 1), vs_get(base + 4)])
            ! Nothing more to do for (def ^{:macro true} let ...):
            ! putting the metadata on the Var IS declaring the macro,
            ! because that is where macro-ness is read from. core.clj
            ! defines let, loop and fn exactly this way, at its line 32.
            if (md%tag /= GCT_NIL) call gc_set_slot(var, 2, md)
            out = gcn_var_value(var)
          end block
       end if

    else if (gc_ref_is(head%ref, "let*")) then
       out = eval_let(vs_get(base + 3), vs_get(base + 2))

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
          last_error = "thrown"
       end if

    else if (gc_ref_is(head%ref, "try*")) then
       out = eval_try(vs_get(base + 3), vs_get(base + 2))

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
       k = gcv_nth(vs_get(base + 3), i)
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
       names = gcv_conj(vs_get(base + 4), gcv_nth(vs_get(base + 3), i), &
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
         frame = gce_new(vs_get(base + 2), [vs_get(base + 3), vs_get(base + 4)])
         call gce_set(frame, vs_get(base + 4), vs_get(base + 3), &
              [vs_get(base + 3), vs_get(base + 4)])
         call gc_set_slot(vs_get(base + 3), 3, frame)
         out = vs_get(base + 3)
       end block
       call vs_leave(base)
       return
    end if

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
    integer :: base

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, args)
    call vs_set(base + 2, env)

    target = gcl_first(vs_get(base + 1))
    rest = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    member = gcl_first(rest)

    ! (. x m) names a member; (. x (m a b)) and (. x m a b) both
    ! call it -- Clojure accepts either spelling, so the arguments
    ! come from inside the parens when there are parens and from the
    ! rest of the form when there are not.
    if (gcl_is(member)) then
       margs = gcl_rest(member, [vs_get(base + 1)])
       member = gcl_first(member)
    else
       margs = gcl_rest(rest, [vs_get(base + 1)])
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
       if (is_host_class(target)) then
          out = static_member(gc_ref_text(target%ref), mname, vs_get(base + 1))
          if (.not. has_error .and. gcl_count(vs_get(base + 4)) > 0) &
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
       call fail("no such member: " // mname)
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
    case ("getName", "getSimpleName"); out = native(B_NAME, "name", [roots])
    ! (. f (applyTo (seq args))) is core.clj's own apply, and the
    ! target becoming the first argument makes it exactly (apply f seq).
    case ("applyTo");   out = native(B_APPLY, "apply", [roots])
    case ("disjoin");   out = native(B_DISJ, "disj", [roots])

    case ("concat", "toString"); out = native(B_STR, "str", [roots])
    case ("equiv");    out = native(B_EQ, "=", [roots])
    case default;       call fail("no such member: " // mname)
    end select
  end function instance_member

  ! (.member target args...) is (. target member args...), which is
  ! where macroexpand1 turns it into too -- the sugar is a rewrite, not
  ! a second kind of call.
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
    ! (Class member . args) -- the shape eval_dot reads.
    args = gcl_cons(gc_sym(t(slash+1:), [vs_get(base + 1)]), &
         gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), [vs_get(base + 1)])
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

    if (cname == "clojure.lang.LazySeq") then
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
    else
       call fail("no such class: " // cname)
    end if
    call vs_leave(base)
  end function eval_new

  logical function is_host_class(sym)
    type(gc_value), intent(in) :: sym
    is_host_class = gc_ref_is(sym%ref, "clojure.lang.PersistentList") .or. &
         gc_ref_is(sym%ref, "clojure.lang.RT") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Util") .or. &
         gc_ref_is(sym%ref, "clojure.lang.LazilyPersistentVector") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentHashMap") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentArrayMap") .or. &
         gc_ref_is(sym%ref, "clojure.lang.PersistentHashSet") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Symbol") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Keyword") .or. &
         gc_ref_is(sym%ref, "clojure.lang.Numbers")
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
    else if (cls == "clojure.lang.Util") then
       select case (mname)
       case ("equiv", "equals", "identical"); out = native(B_EQ, "=", [roots]); return
       end select
    else if (cls == "clojure.lang.LazilyPersistentVector") then
       if (mname == "create" .or. mname == "createOwning") then
          out = native(B_VEC, "vec", [roots]); return
       end if
    else if (cls == "clojure.lang.PersistentHashMap" .or. &
             cls == "clojure.lang.PersistentArrayMap") then
       if (mname == "create" .or. mname == "createWithCheck" .or. &
           mname == "createAsIfByAssoc") then
          out = native(B_HMAP, "hash-map", [roots]); return
       end if
    else if (cls == "clojure.lang.PersistentHashSet") then
       if (mname == "create" .or. mname == "createWithCheck") then
          out = native(B_HSET, "hash-set", [roots]); return
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
       case ("equiv", "equal"); out = native(B_EQ, "=", [roots]); return
       case ("compare"); out = native(B_COMPARE, "compare", [roots]); return
       case ("inc", "incP", "unchecked_inc", "unchecked_int_inc")
          out = native(B_INC, "inc", [roots]); return
       case ("dec", "decP", "unchecked_dec", "unchecked_int_dec")
          out = native(B_DEC, "dec", [roots]); return
       case ("remainder", "unchecked_int_remainder")
          out = native(B_REM, "rem", [roots]); return
       case ("quotient"); out = native(B_QUOT, "quot", [roots]); return
       case ("num"); out = native(B_IDENTITY, "identity", [roots]); return
       end select
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
       case ("keys");   out = native(B_KEYS, "keys", [roots]);   return
       case ("vals");   out = native(B_VALS, "vals", [roots]);   return
       end select
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
    type(gc_value) :: var, bare
    character(len=:), allocatable :: t
    integer :: slash

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
          var = gcn_lookup(gcn_find_or_create(t(1:slash-1), [roots, bare]), bare)
          if (gcn_is_var(var)) return
          var = gc_nil()
          return
       end if
    end if

    var = gcn_lookup(gcn_find_or_create("clojure.core", [roots]), sym)
  end function resolve_var

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
  recursive function eval_try(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, body, clause, name, handler, child, exc
    integer :: base

    out = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    body = gcl_first(rest)
    call vs_set(base + 3, body)
    clause = gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)]))
    call vs_set(base + 4, clause)

    out = gce_eval(vs_get(base + 3), vs_get(base + 2), [vs_get(base + 1)])
    if (.not. has_error) then
       call vs_leave(base); return
    end if
    if (.not. gcl_is(vs_get(base + 4))) then
       call vs_leave(base); return   ! no catch clause: propagate
    end if
    if (gcl_count(vs_get(base + 4)) /= 3) then
       call vs_leave(base); return
    end if

    ! Capture the exception BEFORE clearing, since clearing resets the
    ! thrown value too.
    exc = thrown_value()
    if (exc%tag == GCT_NIL) exc = error_value(gce_error(), [vs_get(base + 1)])
    call vs_set(base + 5, exc)
    call gce_clear_error()

    name = nth_of(vs_get(base + 4), 1)
    handler = nth_of(vs_get(base + 4), 2)
    call vs_set(base + 6, handler)
    child = gce_new(vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 5), vs_get(base + 6)])
    call gce_set(child, name, vs_get(base + 5), &
         [vs_get(base + 1), vs_get(base + 6)])
    out = gce_eval(vs_get(base + 6), child, [vs_get(base + 1)])
    call vs_leave(base)
  end function eval_try

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
       call gc_set_i1(vs_get(base + 1), LAZY_EMPTY)
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

    if (.not. gcl_is(form)) then
       if (form%tag == GCT_SYM) then
          call vs_set(base + 1, auto_gensym(vs_get(base + 1)))
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

  ! A collection inside syntax-quote: expand its elements as a seq,
  ! then rebuild the collection from them with `ctor`.
  recursive function qq_rebuild(form, ctor, env) result(out)
    type(gc_value), intent(in) :: form, env
    character(len=*), intent(in) :: ctor
    type(gc_value) :: out, lst, inner
    integer :: base, i

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
    call vs_leave(base)
  end function qq_rebuild

  recursive function apply(fn, args) result(out)
    type(gc_value), intent(in) :: fn, args
    type(gc_value) :: out, child, body, params
    integer :: base, i, n

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
    case default
       ! A keyword and a map are both callable in Clojure, and neither
       ! is a closure: (:k m) looks itself up IN m, and (m :k) looks up
       ! its argument. Same lookup from opposite sides, which is why
       ! both live here rather than as builtins.
       if (fn%tag == GCT_KEY) then
          if (gcv_count(args) >= 1) out = gca_get(gcv_nth(args, 0), fn)
       else if (gca_is(fn)) then
          if (gcv_count(args) >= 1) out = gca_get(fn, gcv_nth(args, 0))
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

    out = gc_nil()
    n = gcv_count(args)
    ! Three slots: args, plus two scratch for the builtins that
    ! accumulate a collection (conj onto a map, the host create
    ! statics). Writing base + 2 out of a one-slot frame is a write
    ! past the stack top, which reads back as nil.
    base = vs_enter(3)
    call vs_set(base + 1, args)

    select case (id)
    case (B_ADD, B_SUB, B_MUL)
       if (n == 0) then
          if (id == B_MUL) then
             out = gc_int(1)
          else
             out = gc_int(0)
          end if
       else
          a = gcv_nth(args, 0)
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
    case (B_EQ)
       out = gc_bool(.true.)
       do i = 1, n - 1
          if (.not. deep_equal(gcv_nth(args, i - 1), gcv_nth(args, i))) then
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
            acc2 = acc2 // gcp_str(gcv_nth(vs_get(base + 1), i), .false.)
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
       out = gca_get(gcv_nth(args, 0), gcv_nth(args, 1))
       if (out%tag == GCT_NIL .and. n >= 3) then
          if (.not. gca_contains(gcv_nth(args, 0), gcv_nth(args, 1))) &
               out = gcv_nth(args, 2)
       end if
    case (B_ASSOC)
       out = gca_assoc(gcv_nth(vs_get(base + 1), 0), gcv_nth(vs_get(base + 1), 1), &
            gcv_nth(vs_get(base + 1), 2), [vs_get(base + 1)])
    case (B_KEYS, B_VALS)
       block
         type(gc_value), allocatable :: ks(:), vls(:)
         call gca_entries(gcv_nth(vs_get(base + 1), 0), ks, vls)
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
       a = gcv_nth(vs_get(base + 1), 0)
       b = gcv_nth(vs_get(base + 1), 1)
       if (gcv_is(a)) then
          out = gcv_conj(a, b, [vs_get(base + 1)])
       else if (gca_is(a)) then
          ! A pair assocs; a MAP MERGES. APersistentMap.cons walks the
          ! seq of the argument and assocs each entry, so (conj m1 m2)
          ! is a merge -- which is how defn accumulates a Var's
          ! metadata out of the doc string and the attr map.
          if (gca_is(b)) then
             block
               type(gc_value) :: ks(0), vls(0), mm
               type(gc_value), allocatable :: kk(:), vv(:)
               integer :: j
               call gca_entries(b, kk, vv)
               mm = a
               call vs_set(base + 2, mm)
               do j = 1, size(kk)
                  mm = gca_assoc(vs_get(base + 2), kk(j), vv(j), &
                       [vs_get(base + 1), vs_get(base + 2)])
                  call vs_set(base + 2, mm)
               end do
               out = vs_get(base + 2)
             end block
          else
             out = gca_assoc(a, seq_elem(b, 0, [vs_get(base + 1)]), &
                  seq_elem(b, 1, [vs_get(base + 1)]), [vs_get(base + 1)])
          end if
       else if (a%tag == GCT_NIL) then
          out = gcl_cons(b, gcl_empty([vs_get(base + 1)]), [vs_get(base + 1)])
       else
          out = gcl_cons(b, to_seq(a, [vs_get(base + 1)]), [vs_get(base + 1)])
       end if
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
         last = gcv_nth(vs_get(base + 1), n - 1)
         do j = 0, seq_count(last) - 1
            fargs = gcv_conj(fargs, seq_at(last, j), [vs_get(base + 1), fargs])
         end do
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
       a = gcv_nth(vs_get(base + 1), 2)
       if (gc_kind(a) == OBJ_META) a = gc_slot(a, 1)
       if (a%tag /= GCT_SYM) then
          call fail("ns needs a symbol name")
       else
          out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(base + 1)])
          call gcn_set_current(out)
       end if
    case (B_INNS)
       ! A FUNCTION, not a macro -- RT.java interns inNamespace without
       ! setMacro, so (in-ns 'user) evaluates its argument.
       a = gcv_nth(vs_get(base + 1), 0)
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
       if (gcn_is_var(a)) then
          out = gc_slot(a, 2)
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
    case (B_QUOT)
       a = gcv_nth(args, 0); b = gcv_nth(args, 1)
       out = gc_int(a%ival / b%ival)
    case (B_REM)
       a = gcv_nth(args, 0); b = gcv_nth(args, 1)
       out = gc_int(mod(a%ival, b%ival))
    case (B_SECOND)
       out = sq_first(sq_rest(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)]), &
            [vs_get(base + 1)])
    case (B_SEQ)
       out = to_seq(gcv_nth(vs_get(base + 1), 0), [vs_get(base + 1)])
    case (B_DISSOC)
       out = gca_dissoc(gcv_nth(vs_get(base + 1), 0), gcv_nth(vs_get(base + 1), 1), &
            [vs_get(base + 1)])
    case (B_NAME)
       a = gcv_nth(args, 0)
       out = gc_str(gc_ref_text(a%ref), [vs_get(base + 1)])
    case (B_KEYWORD)
       a = gcv_nth(args, 0)
       out = gc_key(gc_ref_text(a%ref), [vs_get(base + 1)])
    case (B_SYMBOL)
       a = gcv_nth(args, 0)
       out = gc_sym(gc_ref_text(a%ref), [vs_get(base + 1)])
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
  recursive function deep_equal(a, b) result(eq)
    type(gc_value), intent(in) :: a, b
    logical :: eq
    type(gc_value), allocatable :: ka(:), va(:), kb(:), vb(:)
    integer :: i, n

    ! A list and a vector of the same elements are equal in Clojure --
    ! both are sequential -- so this compares seq-ness, not kind.
    if (seqable(a) .and. seqable(b)) then
       n = seq_count(a)
       eq = (n == seq_count(b))
       if (.not. eq) return
       do i = 0, n - 1
          if (.not. deep_equal(seq_at(a, i), seq_at(b, i))) then
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
          if (.not. deep_equal(va(i), gca_get(b, ka(i)))) then
             eq = .false.
             return
          end if
       end do
       return
    end if

    eq = gc_equal(a, b)
  end function deep_equal

  function seqable(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = gcl_is(v) .or. gcv_is(v)
  end function seqable

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
  recursive function to_seq(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base

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
  recursive function sq_first(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, s
    integer :: base

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
  recursive function sq_rest(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, s
    integer :: base

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
  recursive function sq_count(v, roots) result(n)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: s
    integer :: base, n

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
       case (OBJ_LAZY);    s = "lazy-seq"
       case (OBJ_VAR);     s = "var"
       case (OBJ_NS);      s = "ns"
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
  function is_instance(cls, v) result(yes)
    type(gc_value), intent(in) :: cls, v
    logical :: yes
    character(len=:), allocatable :: c, t
    yes = .false.
    if (cls%tag /= GCT_KEY) return
    c = gc_ref_text(cls%ref)
    t = type_name(v)
    select case (c)
    case ("clojure.lang.Symbol");   yes = (t == "symbol")
    case ("clojure.lang.Keyword");  yes = (t == "keyword")
    case ("clojure.lang.Var");      yes = (t == "var")
    case ("clojure.lang.Namespace"); yes = (t == "ns")
    case ("clojure.lang.IFn", "clojure.lang.Fn"); yes = (t == "fn")
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
    case ("clojure.lang.IObj", "clojure.lang.IMeta"); &
         yes = (t == "symbol" .or. t == "list" .or. t == "vector" .or. &
                t == "map" .or. t == "set" .or. t == "fn" .or. t == "var")
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

  function truthy(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = .true.
    if (v%tag == GCT_NIL) yes = .false.
    if (v%tag == GCT_BOOL .and. v%ival == 0) yes = .false.
  end function truthy

end module GCEval

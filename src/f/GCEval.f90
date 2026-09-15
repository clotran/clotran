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
    type(gc_value) :: env
    integer :: base

    call gcp_set_forcer(gce_force)
    call gcn_reset(roots)
    base = vs_enter(1)
    env = gce_new(gc_nil(), roots)
    call vs_set(base + 1, env)
    call bind_builtin(env, "+", B_ADD)
    call bind_builtin(env, "-", B_SUB)
    call bind_builtin(env, "*", B_MUL)
    call bind_builtin(env, "=", B_EQ)
    call bind_builtin(env, "<", B_LT)
    call bind_builtin(env, "list", B_LIST)
    call bind_builtin(env, "vector", B_VECTOR)
    call bind_builtin(env, "count", B_COUNT)
    call bind_builtin(env, "first", B_FIRST)
    call bind_builtin(env, "rest", B_REST)
    call bind_builtin(env, "cons", B_CONS)
    call bind_builtin(env, "concat", B_CONCAT)
    call bind_builtin(env, "str", B_STR)
    call bind_builtin(env, "not", B_NOT)
    call bind_builtin(env, "nth", B_NTH)
    call bind_builtin(env, "get", B_GET)
    call bind_builtin(env, "conj", B_CONJ)
    call bind_builtin(env, "empty?", B_EMPTY)
    call bind_builtin(env, "nil?", B_NILP)
    call bind_builtin(env, "apply", B_APPLY)
    call bind_builtin(env, "assoc", B_ASSOC)
    call bind_builtin(env, "keys", B_KEYS)
    call bind_builtin(env, "vals", B_VALS)
    call bind_builtin(env, "prn", B_PRN)
    call bind_builtin(env, "quot", B_QUOT)
    call bind_builtin(env, "rem", B_REM)
    call bind_builtin(env, "seq", B_SEQ)
    call bind_builtin(env, "dissoc", B_DISSOC)
    call bind_builtin(env, "name", B_NAME)
    call bind_builtin(env, "keyword", B_KEYWORD)
    call bind_builtin(env, "symbol", B_SYMBOL)
    call bind_builtin(env, "subs", B_SUBS)
    call bind_builtin(env, "clotran-type", B_TYPE)
    call bind_builtin(env, "second", B_SECOND)
    env = vs_get(base + 1)
    call vs_leave(base)
  end function gce_base_env

  subroutine bind_builtin(env, name, id)
    type(gc_value), intent(in) :: env
    character(len=*), intent(in) :: name
    integer, intent(in) :: id
    type(gc_value) :: sym, fn
    type(gc_value) :: r(2)
    integer :: base

    base = vs_enter(2)
    call vs_set(base + 1, env)
    sym = gc_sym(name, [vs_get(base + 1)])
    call vs_set(base + 2, sym)
    r(1) = vs_get(base + 1)
    r(2) = vs_get(base + 2)
    fn = gc_obj(OBJ_BUILTIN, [sym], r)
    call gc_set_i1(fn, id)
    call gce_set(env, vs_get(base + 2), fn, r)
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
          head = gcn_lookup(gcn_current([vs_get(base + 1)]), form)
          if (gcn_is_var(head)) then
             ! A bare symbol auto-derefs its Var, matching Clojure --
             ! #'x is how you ask for the Var itself.
             out = gcn_var_value(head)
             found = .true.
          end if
       end if
       if (.not. found) call fail("'" // gc_ref_text(form%ref) // "' not found")
    case (GCT_OBJ)
       select case (gc_kind(form))
       case (OBJ_CONS)
          if (gcl_count(form) == 0) then
             out = form
          else
             head = gcl_first(form)
             if (head%tag == GCT_SYM .and. is_special(head)) then
                out = eval_special(form, env)
             else
                out = eval_call(form, env)
             end if
          end if
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

  function is_special(sym) result(yes)
    type(gc_value), intent(in) :: sym
    logical :: yes
    yes = gc_ref_is(sym%ref, "quote") .or. gc_ref_is(sym%ref, "if") .or. &
          gc_ref_is(sym%ref, "do") .or. gc_ref_is(sym%ref, "def") .or. &
          gc_ref_is(sym%ref, "let*") .or. gc_ref_is(sym%ref, "fn*") .or. &
          gc_ref_is(sym%ref, "loop*") .or. gc_ref_is(sym%ref, "recur") .or. &
          gc_ref_is(sym%ref, "defmacro*") .or. gc_ref_is(sym%ref, "quasiquote") .or. &
          gc_ref_is(sym%ref, "try*") .or. gc_ref_is(sym%ref, "throw") .or. &
          gc_ref_is(sym%ref, "lazy-seq*") .or. gc_ref_is(sym%ref, "in-ns*") .or. &
          gc_ref_is(sym%ref, "var")
  end function is_special

  recursive function eval_special(form, env) result(out)
    type(gc_value), intent(in) :: form, env
    type(gc_value) :: out, head, rest, a, b
    integer :: base

    out = gc_nil()
    head = gcl_first(form)
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
          out = gcn_var_value(gcn_intern(gcn_current([vs_get(base + 1)]), &
               vs_get(base + 4), b, [vs_get(base + 1), vs_get(base + 4)]))
       end if

    else if (gc_ref_is(head%ref, "let*")) then
       out = eval_let(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "fn*")) then
       out = make_closure(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "loop*")) then
       out = eval_loop(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "recur")) then
       out = eval_recur(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "in-ns*")) then
       a = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (.not. has_error) then
          out = gcn_find_or_create(gc_ref_text(a%ref), [vs_get(base + 1)])
          call gcn_set_current(out)
       end if

    else if (gc_ref_is(head%ref, "var")) then
       ! The Var itself, undereferenced -- what #'x means, and what a
       ! caller needs to hold a stable reference across redefinition.
       out = gcn_lookup(gcn_current([vs_get(base + 1)]), gcl_first(vs_get(base + 3)))
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
       a = qq_expand(gcl_first(vs_get(base + 3)), vs_get(base + 2))
       if (.not. has_error) out = gce_eval(a, vs_get(base + 2), [vs_get(base + 1)])

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
             ! Macro-ness lives on the closure, exactly as clotran's
             ! own is_macro does: real Clojure keeps it in Var
             ! metadata, but there are no Vars in this evaluator.
             call gc_set_i1(b, 1)
             call gce_set(vs_get(base + 2), vs_get(base + 4), b, [vs_get(base + 1)])
             out = b
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
  function bind_params(params, args, outer) result(child)
    type(gc_value), intent(in) :: params, args, outer
    type(gc_value) :: child, rest, name
    integer :: base, i, n, amp

    base = vs_enter(5)
    call vs_set(base + 1, params)
    call vs_set(base + 2, args)
    call vs_set(base + 3, outer)

    n = gcv_count(params)
    amp = -1
    do i = 0, n - 1
       name = gcv_nth(params, i)
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
          call gce_set(vs_get(base + 4), gcv_nth(vs_get(base + 1), i), &
               gcv_nth(vs_get(base + 2), i), [vs_get(base + 1), vs_get(base + 2)])
       end do
    else
       do i = 0, amp - 1
          call gce_set(vs_get(base + 4), gcv_nth(vs_get(base + 1), i), &
               gcv_nth(vs_get(base + 2), i), [vs_get(base + 1), vs_get(base + 2)])
       end do
       rest = gcl_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 4)])
       call vs_set(base + 5, rest)
       do i = gcv_count(vs_get(base + 2)) - 1, amp, -1
          rest = gcl_cons(gcv_nth(vs_get(base + 2), i), vs_get(base + 5), &
               [vs_get(base + 1), vs_get(base + 2), vs_get(base + 4)])
          call vs_set(base + 5, rest)
       end do
       call gce_set(vs_get(base + 4), gcv_nth(vs_get(base + 1), amp + 1), &
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
  function make_closure(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, params, body, head
    type(gc_value) :: r(3)
    integer :: base

    base = vs_enter(3)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    head = gcl_first(rest)

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
       clause = nth_of(vs_get(base + 1), i)
       call vs_set(base + 2, clause)
       p = gcl_first(clause)
       if (.not. gcv_is(p)) cycle
       amp = -1
       do j = 0, gcv_count(p) - 1
          name = gcv_nth(p, j)
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

    fn = gce_eval(gcl_first(form), env, [vs_get(base + 1)])
    if (has_error) then
       call vs_leave(base); return
    end if
    call vs_set(base + 3, fn)

    ! A macro receives its arguments UNEVALUATED and its result is
    ! evaluated in the caller's environment. That is the whole
    ! difference between a macro and a function, and it is why the
    ! check has to happen here, before the arguments are touched.
    if (gc_kind(fn) == OBJ_CLOSURE .and. gc_i1(fn) == 1) then
       out = expand_macro(vs_get(base + 3), vs_get(base + 1))
       if (.not. has_error) out = gce_eval(out, vs_get(base + 2), [vs_get(base + 1)])
       call vs_leave(base)
       return
    end if

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
  recursive function expand_macro(fn, form) result(out)
    type(gc_value), intent(in) :: fn, form
    type(gc_value) :: out, args, walk
    integer :: base

    base = vs_enter(4)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, form)
    args = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
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

    if (.not. gcl_is(form)) then
       if (form%tag == GCT_SYM) then
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
          child = bind_params(params, gc_slot(out, 1), gc_slot(vs_get(base + 1), 3))
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
    base = vs_enter(1)
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
          if (.not. (a%ival < b%ival)) then
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
    case (B_CONS)
       ! (cons x <lazy>) cannot build a plain cons cell: its tail
       ! would have to be a realised list, and forcing here would
       ! defeat the whole point -- (cons n (from (+ n 1))) is how an
       ! infinite seq is written. So it builds an ALREADY-REALISED
       ! lazy cell instead, head and tail in place, nothing forced.
       ! clotran's RT.f90 has the same lazy_cons for the same reason.
       a = gcv_nth(args, 1)
       if (gc_kind(a) == OBJ_LAZY) then
          out = gc_obj(OBJ_LAZY, [gc_nil(), gcv_nth(args, 0), a], &
               [vs_get(base + 1)])
          call gc_set_i1(out, LAZY_CONS)
       else
          out = gcl_cons(gcv_nth(args, 0), as_list(a, [vs_get(base + 1)]), &
               [vs_get(base + 1)])
       end if
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
       a = gcv_nth(args, 0)
       b = gcv_nth(args, 1)
       out = gc_nil()
       if (gcv_is(a)) then
          out = gcv_nth(a, b%ival)
       else if (gcl_is(a)) then
          if (b%ival >= 0 .and. b%ival < gcl_count(a)) out = nth_of(a, b%ival)
       end if
       if (out%tag == GCT_NIL .and. n >= 3) out = gcv_nth(args, 2)
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
       a = gcv_nth(vs_get(base + 1), 0)
       b = gcv_nth(vs_get(base + 1), 1)
       if (gcv_is(a)) then
          out = gcv_conj(a, b, [vs_get(base + 1)])
       else if (gcl_is(a)) then
          out = gcl_cons(b, a, [vs_get(base + 1)])
       else
          out = a
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
  function type_name(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
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
       case (OBJ_CLOSURE, OBJ_BUILTIN); s = "fn"
       case (OBJ_LAZY);    s = "lazy-seq"
       case (OBJ_VAR);     s = "var"
       case (OBJ_NS);      s = "ns"
       case default;       s = "object"
       end select
    end select
  end function type_name

  function truthy(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = .true.
    if (v%tag == GCT_NIL) yes = .false.
    if (v%tag == GCT_BOOL .and. v%ival == 0) yes = .false.
  end function truthy

end module GCEval

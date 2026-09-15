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
  use GCPrinter
  implicit none
  private

  ! Primitive ids. Order is arbitrary; only the mapping matters.
  integer, parameter :: B_ADD = 1, B_SUB = 2, B_MUL = 3, B_EQ = 4, B_LT = 5
  integer, parameter :: B_LIST = 6, B_VECTOR = 7, B_COUNT = 8
  integer, parameter :: B_FIRST = 9, B_REST = 10
  integer, parameter :: B_CONS = 11, B_CONCAT = 12

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  ! The value a `throw` is carrying, as a GC GLOBAL ROOT rather than a
  ! plain module variable. It has to be: between the throw and the
  ! catch, nothing else refers to it -- the stack frames that held it
  ! are unwinding -- so an ordinary variable would be a value the
  ! collector cannot see, and a collection in that window would free
  ! the exception before its handler ever ran.
  integer, save :: thrown_root = 0

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
    if (thrown_root == 0) then
       thrown_root = gc_global_new(v)
    else
       call gc_global_set(thrown_root, v)
    end if
  end subroutine set_thrown

  function thrown_value() result(v)
    type(gc_value) :: v
    v = gc_nil()
    if (thrown_root /= 0) v = gc_global_get(thrown_root)
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
       found = gce_find(env, form, out)
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
          gc_ref_is(sym%ref, "try*") .or. gc_ref_is(sym%ref, "throw")
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
       a = gcl_first(vs_get(base + 3))
       call vs_set(base + 4, a)
       rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
       call vs_set(base + 3, rest)
       b = gce_eval(gcl_first(vs_get(base + 3)), vs_get(base + 2), [vs_get(base + 1)])
       if (.not. has_error) then
          call gce_set(vs_get(base + 2), vs_get(base + 4), b, [vs_get(base + 1)])
          out = b
       end if

    else if (gc_ref_is(head%ref, "let*")) then
       out = eval_let(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "fn*")) then
       out = make_closure(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "loop*")) then
       out = eval_loop(vs_get(base + 3), vs_get(base + 2))

    else if (gc_ref_is(head%ref, "recur")) then
       out = eval_recur(vs_get(base + 3), vs_get(base + 2))

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
       call fail("not a function: " // gcp_str(fn, .true.))
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
          if (.not. gc_equal(gcv_nth(args, i - 1), gcv_nth(args, i))) then
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
       a = gcv_nth(args, 0)
       if (gcl_is(a)) then
          out = gc_int(gcl_count(a))
       else if (gcv_is(a)) then
          out = gc_int(gcv_count(a))
       else if (gca_is(a)) then
          out = gc_int(gca_count(a))
       else
          out = gc_int(0)
       end if
    case (B_FIRST)
       a = gcv_nth(args, 0)
       if (gcl_is(a)) then
          out = gcl_first(a)
       else if (gcv_is(a)) then
          if (gcv_count(a) > 0) out = gcv_nth(a, 0)
       end if
    case (B_REST)
       a = gcv_nth(args, 0)
       if (gcl_is(a)) out = gcl_rest(a, [vs_get(base + 1)])
    case (B_CONS)
       out = gcl_cons(gcv_nth(args, 0), as_list(gcv_nth(args, 1), &
            [vs_get(base + 1)]), [vs_get(base + 1)])
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

  ! Clojure's truthiness: everything except nil and false.
  function truthy(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = .true.
    if (v%tag == GCT_NIL) yes = .false.
    if (v%tag == GCT_BOOL .and. v%ival == 0) yes = .false.
  end function truthy

end module GCEval

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
!   special forms   quote, if, do, def, let*, fn*
!   primitives      + - * = < list vector count first rest
!   closures        with lexical capture and recursion
!
! What it does NOT have, listed rather than silently missing: macros,
! loop/recur and tail calls, try/catch, destructuring, varargs,
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

  character(len=:), allocatable :: last_error
  logical :: has_error = .false.

  public :: gce_eval, gce_base_env, gce_has_error, gce_error, gce_clear_error

contains

  ! Cleared by the CALLER before a top-level evaluation, not by
  ! gce_eval itself: gce_eval is recursive, so clearing on entry would
  ! wipe an error raised deeper in the same evaluation. A REPL clears,
  ! evaluates, then checks -- which is exactly this shape.
  subroutine gce_clear_error()
    has_error = .false.
    last_error = ""
  end subroutine gce_clear_error

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
          gc_ref_is(sym%ref, "let*") .or. gc_ref_is(sym%ref, "fn*")
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

  function make_closure(rest, env) result(out)
    type(gc_value), intent(in) :: rest, env
    type(gc_value) :: out, params, body
    type(gc_value) :: r(3)
    integer :: base

    base = vs_enter(3)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, env)
    params = gcl_first(rest)
    call vs_set(base + 3, params)
    body = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    r(1) = vs_get(base + 1); r(2) = vs_get(base + 2); r(3) = vs_get(base + 3)
    out = gc_obj(OBJ_CLOSURE, [vs_get(base + 3), body, vs_get(base + 2), gc_nil()], r)
    call vs_leave(base)
  end function make_closure

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
       n = gcv_count(params)
       if (n /= gcv_count(args)) then
          call fail("wrong number of arguments")
          call vs_leave(base); return
       end if
       child = gce_new(gc_slot(fn, 3), [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, child)
       do i = 0, n - 1
          call gce_set(vs_get(base + 3), gcv_nth(params, i), gcv_nth(args, i), &
               [vs_get(base + 1), vs_get(base + 2)])
       end do
       body = gc_slot(vs_get(base + 1), 2)
       call vs_set(base + 4, body)
       do while (gcl_count(vs_get(base + 4)) > 0)
          out = gce_eval(gcl_first(vs_get(base + 4)), vs_get(base + 3), &
               [vs_get(base + 1), vs_get(base + 2)])
          if (has_error) exit
          body = gcl_rest(vs_get(base + 4), [vs_get(base + 1)])
          call vs_set(base + 4, body)
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
    end select

    call vs_leave(base)
  end function call_builtin

  ! Clojure's truthiness: everything except nil and false.
  function truthy(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = .true.
    if (v%tag == GCT_NIL) yes = .false.
    if (v%tag == GCT_BOOL .and. v%ival == 0) yes = .false.
  end function truthy

end module GCEval

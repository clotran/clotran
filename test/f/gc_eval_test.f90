! Reader, evaluator and printer together: evaluate a string of real
! Clojure and check what it prints.
!
! This is the check the whole port rests on. Every earlier module
! tested a data structure, where the roots are obvious. An evaluator
! is where they are not: intermediate values live across recursive
! calls, every one of which can allocate and therefore collect. If
! rooting by construction works here, it works.
!
! Every group is run TWICE -- once normally, once with a collection at
! every single allocation. The torture pass is the real test; the
! normal pass only tells you the answer is right when nothing moves.
program gc_eval_test
  use GC
  use GCReader
  use GCPrinter
  use GCEval
  implicit none

  logical :: all_ok
  logical :: torturing
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  torturing = .false.
  call run_all("plain")
  torturing = .true.
  call run_all("torture")

  if (all_ok) then
     print *, ""
     print *, "ALL GCEVAL CHECKS PASSED"
  else
     print *, ""
     print *, "GCEVAL CHECKS FAILED"
     stop 1
  end if

contains

  subroutine run_all(tag)
    character(len=*), intent(in) :: tag
    print '(A,A,A)', "--- ", tag, " ---"
    call check_literals()
    call check_arithmetic()
    call check_if()
    call check_def_and_symbols()
    call check_let()
    call check_fn()
    call check_collections()
    call check_loop_recur()
    call check_varargs()
    call check_quasiquote()
    call check_macros()
    call check_errors()
    call check_heap_sound()
  end subroutine run_all

  ! Reads, evaluates and prints, in one value-stack frame so the form
  ! survives its own evaluation.
  subroutine ev(label, text, expected)
    character(len=*), intent(in) :: label, text, expected
    type(gc_value) :: form, env, result
    integer :: base
    character(len=:), allocatable :: got

    call gc_init(64)
    gc_torture = .false.          ! reading and setup are not the subject
    base = vs_enter(3)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    form = gcr_read(text, [vs_get(base + 1)])
    call vs_set(base + 2, form)
    if (gcr_has_error()) then
       print '(A,A,A,A)', "FAIL - ", label, "read error: ", gcr_error()
       all_ok = .false.
       call vs_leave(base)
       return
    end if

    gc_torture = torturing        ! from here on, collect at every allocation
    call gce_clear_error()
    result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
    call vs_set(base + 3, result)
    if (gce_has_error()) then
       gc_torture = .false.
       print '(A,A,A,A)', "FAIL - ", label, "eval error: ", gce_error()
       all_ok = .false.
       call vs_leave(base)
       return
    end if
    got = gcp_str(vs_get(base + 3), .true.)
    gc_torture = .false.
    call vs_leave(base)

    if (got == expected) then
       print '(A,A,A)', "ok   - ", label, got
    else
       print '(A,A,A,A,A)', "FAIL - ", label, got, "  (expected ", expected // ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine ev

  subroutine ok(label, condition)
    character(len=*), intent(in) :: label
    logical, intent(in) :: condition
    if (condition) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok

  subroutine check_literals()
    call ev("1a. ", "42", "42")
    call ev("1b. ", "nil", "nil")
    call ev("1c. ", "true", "true")
    call ev("1d. ", ":kw", ":kw")
    call ev("1e. ", """s""", """s""")
    call ev("1f. ", "(quote (a b))", "(a b)")
  end subroutine check_literals

  subroutine check_arithmetic()
    call ev("2a. ", "(+ 1 2)", "3")
    call ev("2b. ", "(+ 1 2 3 4 5)", "15")
    call ev("2c. ", "(- 10 3)", "7")
    call ev("2d. ", "(* 2 3 4)", "24")
    call ev("2e. ", "(+ (* 2 3) (- 10 4))", "12")
    call ev("2f. ", "(= 1 1)", "true")
    call ev("2g. ", "(= 1 2)", "false")
    call ev("2h. ", "(< 1 2 3)", "true")
  end subroutine check_arithmetic

  subroutine check_if()
    call ev("3a. ", "(if true 1 2)", "1")
    call ev("3b. ", "(if false 1 2)", "2")
    ! Clojure truthiness: only nil and false are falsey.
    call ev("3c. ", "(if nil 1 2)", "2")
    call ev("3d. ", "(if 0 1 2)", "1")
    call ev("3e. ", "(if false 1)", "nil")
    ! The untaken branch must NOT be evaluated -- if it were, this
    ! would fail on an unbound symbol rather than returning 1.
    call ev("3f. ", "(if true 1 undefined-symbol)", "1")
  end subroutine check_if

  subroutine check_def_and_symbols()
    call ev("4a. ", "(do (def x 5) x)", "5")
    call ev("4b. ", "(do (def x 5) (+ x x))", "10")
    call ev("4c. ", "(do (def x 1) (def x 2) x)", "2")
  end subroutine check_def_and_symbols

  subroutine check_let()
    call ev("5a. ", "(let* [a 1] a)", "1")
    call ev("5b. ", "(let* [a 1 b 2] (+ a b))", "3")
    ! Sequential binding: b can see a.
    call ev("5c. ", "(let* [a 1 b (+ a 1)] b)", "2")
    ! Shadowing, and the outer binding restored afterwards.
    call ev("5d. ", "(do (def a 10) (let* [a 1] a))", "1")
    call ev("5e. ", "(do (def a 10) (let* [a 1] a) a)", "10")
    call ev("5f. ", "(let* [a 1] (let* [b 2] (+ a b)))", "3")
  end subroutine check_let

  subroutine check_fn()
    call ev("6a. ", "((fn* [x] x) 7)", "7")
    call ev("6b. ", "((fn* [x y] (+ x y)) 3 4)", "7")
    call ev("6c. ", "(do (def inc1 (fn* [n] (+ n 1))) (inc1 41))", "42")
    ! Lexical capture: the closure keeps the env it was made in, and
    ! must still see it after that scope is gone.
    call ev("6d. ", "(do (def mk (fn* [n] (fn* [m] (+ n m)))) ((mk 10) 5))", "15")
    ! Recursion through a def'd name -- the closure's env chain reaches
    ! the frame the name was defined in.
    call ev("6e. ", &
         "(do (def f (fn* [n] (if (< n 1) 0 (+ n (f (- n 1)))))) (f 5))", "15")
    call ev("6f. ", &
         "(do (def fib (fn* [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))) (fib 10))", &
         "55")
  end subroutine check_fn

  subroutine check_collections()
    call ev("7a. ", "(list 1 2 3)", "(1 2 3)")
    call ev("7b. ", "[1 2 3]", "[1 2 3]")
    ! A vector literal evaluates its elements.
    call ev("7c. ", "[(+ 1 1) (* 2 2)]", "[2 4]")
    call ev("7d. ", "(count (list 1 2 3))", "3")
    call ev("7e. ", "(first (list 1 2 3))", "1")
    call ev("7f. ", "(rest (list 1 2 3))", "(2 3)")
    call ev("7g. ", "(count [1 2 3 4])", "4")
    call ev("7h. ", "(let* [v [1 2]] (count v))", "2")
  end subroutine check_collections

  ! recur is the whole reason Clojure needs no general TCO: it is an
  ! explicit jump to the nearest loop* or fn*, and must run in
  ! CONSTANT stack however many times it goes round.
  subroutine check_loop_recur()
    call ev("8a. ", "(loop* [i 0] i)", "0")
    call ev("8b. ", "(loop* [i 0] (if (< i 3) (recur (+ i 1)) i))", "3")
    call ev("8c. ", "(loop* [i 0 acc 0] (if (< i 5) (recur (+ i 1) (+ acc i)) acc))", "10")
    ! recur inside a fn*, rebinding the parameters.
    call ev("8d. ", &
         "(do (def cd (fn* [n] (if (< n 1) :done (recur (- n 1))))) (cd 5))", ":done")
    ! The one that matters: 100000 iterations. Without recur rebinding
    ! in place this is a stack overflow, not a wrong answer.
    call ev("8e. ", "(loop* [i 0] (if (< i 100000) (recur (+ i 1)) i))", "100000")
    call ev("8f. ", &
         "(do (def sum (fn* [n acc] (if (< n 1) acc (recur (- n 1) (+ acc n))))) (sum 10000 0))", &
         "50005000")
    ! A closure made during one iteration keeps THAT iteration's value.
    ! The fn* here is built when i is 1, so calling it must give 1 --
    ! not the loop's final 2. If recur mutated the frame in place
    ! instead of rebinding into a fresh one, this would return 2.
    call ev("8g. ", &
         "(loop* [i 0 f nil] (if (< i 2) (recur (+ i 1) (fn* [] i)) (f)))", "1")
  end subroutine check_loop_recur

  ! & collects the remaining arguments into a LIST -- empty rather
  ! than nil when there are none, which is what lets variadic core
  ! functions work without special-casing the zero case.
  subroutine check_varargs()
    call ev("11a. ", "((fn* [& xs] xs) 1 2 3)", "(1 2 3)")
    call ev("11b. ", "((fn* [a & xs] xs) 1 2 3)", "(2 3)")
    call ev("11c. ", "((fn* [a & xs] a) 1 2 3)", "1")
    call ev("11d. ", "((fn* [a & xs] xs) 1)", "()")
    call ev("11e. ", "((fn* [& xs] (count xs)))", "0")
    call ev("11f. ", "(do (def f (fn* [a & r] (cons a r))) (f 1 2 3))", "(1 2 3)")
  end subroutine check_varargs

  subroutine check_quasiquote()
    call ev("12a. ", "(quasiquote 1)", "1")
    ! A bare symbol is quoted, not evaluated.
    call ev("12b. ", "(do (def x 9) (quasiquote x))", "x")
    ! ~x evaluates; the reader turns it into (unquote x).
    call ev("12c. ", "(do (def x 9) `~x)", "9")
    call ev("12d. ", "(do (def x 9) `(a ~x))", "(a 9)")
    call ev("12e. ", "`(1 2 3)", "(1 2 3)")
    ! ~@ splices a list in rather than nesting it.
    call ev("12f. ", "(do (def xs (list 2 3)) `(1 ~@xs 4))", "(1 2 3 4)")
    call ev("12g. ", "(do (def xs (list 2 3)) `(1 ~xs))", "(1 (2 3))")
    call ev("12h. ", "`(a (b ~(+ 1 2)))", "(a (b 3))")
  end subroutine check_quasiquote

  ! A macro gets its arguments UNEVALUATED and its result is evaluated
  ! in the caller's environment. 13c is the test that tells a macro
  ! from a function: a function would evaluate the unbound symbol.
  subroutine check_macros()
    call ev("13a. ", &
         "(do (defmacro* m (fn* [a] a)) (m 1))", "1")
    call ev("13b. ", &
         "(do (defmacro* unless (fn* [c t] `(if ~c nil ~t))) (unless false :yes))", &
         ":yes")
    call ev("13c. ", &
         "(do (defmacro* ig (fn* [a] 7)) (ig undefined-symbol))", "7")
    ! A macro building a form from its unevaluated argument.
    call ev("13d. ", &
         "(do (defmacro* twice (fn* [f] `(+ ~f ~f))) (twice 5))", "10")
    ! Variadic macro, which needs & and ~@ working together.
    call ev("13e. ", &
         "(do (defmacro* my-list (fn* [& xs] `(list ~@xs))) (my-list 1 2 3))", &
         "(1 2 3)")
  end subroutine check_macros

  subroutine check_errors()
    type(gc_value) :: form, env, result
    integer :: base
    call gc_init(64)
    base = vs_enter(2)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    form = gcr_read("(undefined-thing 1)", [vs_get(base + 1)])
    call vs_set(base + 2, form)
    call gce_clear_error()
    result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
    call ok("9a. an unbound symbol is an error: ", gce_has_error())
    ! Leave the flag clear, or every evaluation after this one
    ! short-circuits -- which is exactly what the torture pass caught.
    call gce_clear_error()
    call vs_leave(base)
  end subroutine check_errors

  ! After all of the above, the heap must still be internally
  ! consistent: no live object referring to a freed or out-of-range
  ! slot.
  subroutine check_heap_sound()
    call ok("10a. the heap passes its own audit: ", gc_check_heap() == "")
  end subroutine check_heap_sound

end program gc_eval_test

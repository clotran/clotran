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
    call ok("8a. an unbound symbol is an error: ", gce_has_error())
    ! Leave the flag clear, or every evaluation after this one
    ! short-circuits -- which is exactly what the torture pass caught.
    call gce_clear_error()
    call vs_leave(base)
  end subroutine check_errors

  ! After all of the above, the heap must still be internally
  ! consistent: no live object referring to a freed or out-of-range
  ! slot.
  subroutine check_heap_sound()
    call ok("9a. the heap passes its own audit: ", gc_check_heap() == "")
  end subroutine check_heap_sound

end program gc_eval_test

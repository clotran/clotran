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
program eval_test
  use GC
  use LispReader
  use Printer
  use Eval
  use NativeArray
  use Regex
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
    call check_try_catch()
    call check_multi_arity()
    call check_laziness()
    call check_namespaces()
    call check_equality()
    call check_callables()
    call check_core_builtins()
    call check_regex()
    call check_case()
    call check_deftype()
    call check_letfn()
    call check_symbol_names()
    call check_meta_lookup()
    call check_contexts()
    call check_sorted()
    call check_native_arrays()
    call check_regex_release()
    call check_resources()
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

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call gc_init(64)
    gc_torture = .false.          ! reading and setup are not the subject
    base = vs_enter(3)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    form = gcr_read(text, [vs_get(base + 1)])
    call vs_set(base + 2, form)
    if (gcr_has_error()) then
       block
          call gcr_error(s=dlt_1)
          print '(A,A,A,A)', "FAIL - ", label, "read error: ", dlt_1
       end block
       all_ok = .false.
       call vs_leave(base)
       return
    end if

    gc_torture = torturing        ! from here on, collect at every allocation
    call gce_clear_error()
    ! Analysed, then executed: the same two halves main.f90 runs, so
    ! the torture pass covers the analyser's rooting too.
    result = gce_analyze(vs_get(base + 2), vs_get(base + 1))
    call vs_set(base + 2, result)
    if (.not. gce_has_error()) result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
    call vs_set(base + 3, result)
    if (gce_has_error()) then
       gc_torture = .false.
       block
          call gce_error(s=dlt_1)
          print '(A,A,A,A)', "FAIL - ", label, "eval error: ", dlt_1
       end block
       all_ok = .false.
       call vs_leave(base)
       return
    end if
    block
       call gcp_str(vs_get(base + 3), .true., s=dlt_1)
       got = dlt_1
    end block
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

  ! The same, for a form that MUST fail. A wrong answer that looks
  ! plausible is worse than a crash, so the cases where clotran should
  ! refuse are worth asserting as directly as the ones where it
  ! should answer.
  subroutine ev_err(label, text)
    character(len=*), intent(in) :: label, text
    type(gc_value) :: form, env, result
    integer :: base
    logical :: errored

    call gc_init(64)
    gc_torture = .false.
    base = vs_enter(3)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    form = gcr_read(text, [vs_get(base + 1)])
    call vs_set(base + 2, form)
    gc_torture = torturing
    call gce_clear_error()
    ! Analysed, then executed: the same two halves main.f90 runs, so
    ! the torture pass covers the analyser's rooting too.
    result = gce_analyze(vs_get(base + 2), vs_get(base + 1))
    call vs_set(base + 2, result)
    if (.not. gce_has_error()) result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
    call vs_set(base + 3, result)
    errored = gce_has_error()
    gc_torture = .false.
    call gce_clear_error()
    call vs_leave(base)
    call ok(label, errored)
  end subroutine ev_err

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
    ! Clojure fails to COMPILE this -- Unable to resolve symbol -- and
    ! since the analyser resolves every symbol before anything runs,
    ! so does clotran. It used to answer 1 because the branch was
    ! never evaluated; that was deviation 16, now closed.
    call ev_err("3f. ", "(if true 1 undefined-symbol)")
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

  ! & collects the remaining arguments into a seq, or NIL when there
  ! are none. This comment used to claim the opposite -- an empty list
  ! -- and 11d asserted it. babashka says otherwise, and so does
  ! core.clj: if-let rejects a third form by asserting (nil? oldform),
  ! and an empty list is truthy, so that assertion fired on every
  ! correct call.
  subroutine check_varargs()
    call ev("11a. ", "((fn* [& xs] xs) 1 2 3)", "(1 2 3)")
    call ev("11b. ", "((fn* [a & xs] xs) 1 2 3)", "(2 3)")
    call ev("11c. ", "((fn* [a & xs] a) 1 2 3)", "1")
    call ev("11d. ", "((fn* [a & xs] xs) 1)", "nil")
    call ev("11e. ", "((fn* [& xs] (count xs)))", "0")   ! (count nil) is 0
    call ev("11f. ", "(do (def f (fn* [a & r] (cons a r))) (f 1 2 3))", "(1 2 3)")
  end subroutine check_varargs

  subroutine check_quasiquote()
    call ev("12a. ", "(quasiquote 1)", "1")
    ! A bare symbol is quoted, not evaluated -- and QUALIFIED with
    ! the namespace it resolves in, which is what makes a macro's
    ! expansion mean the same thing wherever it lands. Real Clojure
    ! answers user/x here too; this asserted bare x while syntax-quote
    ! qualified nothing.
    call ev("12b. ", "(do (def x 9) (quasiquote x))", "user/x")
    ! ~x evaluates; the reader turns it into (clojure.core/unquote x).
    call ev("12c. ", "(do (def x 9) `~x)", "9")
    call ev("12d. ", "(do (def x 9) `(a ~x))", "(user/a 9)")
    call ev("12e. ", "`(1 2 3)", "(1 2 3)")
    ! ~@ splices a list in rather than nesting it.
    call ev("12f. ", "(do (def xs (list 2 3)) `(1 ~@xs 4))", "(1 2 3 4)")
    call ev("12g. ", "(do (def xs (list 2 3)) `(1 ~xs))", "(1 (2 3))")
    call ev("12h. ", "`(a (b ~(+ 1 2)))", "(user/a (user/b 3))")
  end subroutine check_quasiquote

  ! A macro gets its arguments UNEVALUATED and its result is evaluated
  ! in the caller's environment. 13c is the test that tells a macro
  ! from a function: a function would evaluate the unbound symbol.
  subroutine check_macros()
    call ev("13a. ", &
         "(do (defmacro* m (fn* [&form &env a] a)) (m 1))", "1")
    call ev("13b. ", &
         "(do (defmacro* unless (fn* [&form &env c t] `(if ~c nil ~t))) (unless false :yes))", &
         ":yes")
    call ev("13c. ", &
         "(do (defmacro* ig (fn* [&form &env a] 7)) (ig undefined-symbol))", "7")
    ! A macro building a form from its unevaluated argument.
    call ev("13d. ", &
         "(do (defmacro* twice (fn* [&form &env f] `(+ ~f ~f))) (twice 5))", "10")
    ! Variadic macro, which needs & and ~@ working together.
    call ev("13e. ", &
         "(do (defmacro* my-list (fn* [&form &env & xs] `(list ~@xs))) (my-list 1 2 3))", &
         "(1 2 3)")
  end subroutine check_macros

  ! throw carries a VALUE, not just a message, and that value has to
  ! survive between the throw and the catch -- when nothing on the
  ! stack refers to it any more. Under torture that window is a
  ! guaranteed collection, which is why the thrown value is a GC
  ! global root rather than a plain module variable.
  subroutine check_try_catch()
    call ev("14a. ", "(try 1 (catch Throwable e 2))", "1")
    call ev("14b. ", "(try (throw 7) (catch Throwable e e))", "7")
    call ev("14c. ", "(try (throw :boom) (catch Throwable e e))", ":boom")
    ! A thrown collection: the value has to be traced, not just copied.
    call ev("14d. ", "(try (throw (list 1 2 3)) (catch Throwable e (count e)))", "3")
    ! An internal error is catchable too, and arrives as a MAP rather
    ! than a bare string -- so a handler can tell it from a value the
    ! program itself threw. 14i is that distinction.
    ! A compile error is not a thrown value: try cannot catch an
    ! unresolved symbol, in Clojure or here. Checked against clj.
    call ev_err("14e. ", "(try undefined-thing (catch Throwable e :caught))")
    ! The handler runs in a scope where e is bound, and the outer
    ! environment is still visible.
    call ev("14f. ", "(do (def x 10) (try (throw 5) (catch Throwable e (+ e x))))", "15")
    ! Nothing thrown: the catch clause must not run.
    call ev("14g. ", "(try (+ 1 1) (catch Throwable e :no))", "2")
    ! Nested: the inner catch handles it, the outer does not fire.
    call ev("14h. ", &
         "(try (try (throw 1) (catch Throwable e (+ e 10))) (catch Throwable e :outer))", "11")
    ! A thrown string stays a string; an internal error is a map. If
    ! internal errors were strings too, these two would be
    ! indistinguishable to a handler that wants to re-raise what it
    ! does not recognise.
    call ev("14i. ", '(try (throw "x") (catch Throwable e e))', '"x"')
    call ev_err("14j. ", "(try nope (catch Throwable e (count e)))")
  end subroutine check_try_catch

  subroutine check_multi_arity()
    call ev("15a. ", "((fn* ([] 0) ([x] x)) )", "0")
    call ev("15b. ", "((fn* ([] 0) ([x] x)) 5)", "5")
    call ev("15c. ", "((fn* ([x] :one) ([x y] :two)) 1 2)", ":two")
    ! A variadic clause alongside fixed ones.
    call ev("15d. ", "((fn* ([x] :one) ([x & r] :many)) 1 2 3)", ":many")
    call ev("15e. ", "((fn* ([x] :one) ([x & r] :many)) 1)", ":one")
    ! Single-arity fns must keep working unchanged.
    call ev("15f. ", "((fn* [x] x) 3)", "3")
    ! recur inside a multi-arity clause rebinds that clause's params.
    call ev("15g. ", &
         "(do (def f (fn* ([n] (f n 0)) ([n acc] (if (< n 1) acc (recur (- n 1) (+ acc n)))))) (f 100 ))", &
         "5050")
  end subroutine check_multi_arity

  ! Laziness is what map/filter/range are built on, and the property
  ! that matters is that the body does NOT run until something asks.
  subroutine check_laziness()
    call ev("16a. ", "(first (lazy-seq* (list 1 2 3)))", "1")
    call ev("16b. ", "(count (lazy-seq* (list 1 2 3)))", "3")
    call ev("16c. ", "(lazy-seq* (list 1 2 3))", "(1 2 3)")
    call ev("16d. ", "(lazy-seq* nil)", "()")
    ! Nothing is evaluated at construction: the body throws, and this
    ! still returns a value because nobody asked for an element.
    call ev("16e. ", "(do (def s (lazy-seq* (throw :boom))) :made-it)", ":made-it")
    ! ...and asking DOES run it.
    call ev("16f. ", &
         "(try (first (lazy-seq* (throw :boom))) (catch Throwable e e))", ":boom")
    ! An INFINITE seq, taken finitely. Without laziness this does not
    ! terminate; with it, only three cells are ever realised.
    call ev("16g. ", &
         "(do (def from (fn* [n] (lazy-seq* (cons n (from (+ n 1))))))" // &
         " (first (rest (rest (from 10)))))", "12")
    ! A lazy seq built on another lazy seq, realised through both.
    call ev("16h. ", &
         "(do (def from (fn* [n] (lazy-seq* (cons n (from (+ n 1))))))" // &
         " (def taking (fn* [k s] (if (< k 1) (list)" // &
         " (cons (first s) (taking (- k 1) (rest s))))))" // &
         " (taking 4 (from 1)))", "(1 2 3 4)")
    ! Realisation is memoised on the node, so walking a seq twice
    ! costs O(1) per cell rather than re-running the thunk. Forcing
    ! the same cell repeatedly must keep giving the same answer.
    call ev("16i. ", &
         "(do (def from (fn* [n] (lazy-seq* (cons n (from (+ n 1))))))" // &
         " (def s (from 1)) (+ (first s) (first s) (first (rest s))))", "4")
  end subroutine check_laziness

  ! def binds in the NAMESPACE, not the enclosing frame -- which is
  ! the divergence this evaluator had before namespaces existed.
  subroutine check_namespaces()
    call ev("17a. ", "(do (def x 5) x)", "5")
    ! The one that was wrong before: a def inside a let still defines
    ! at the top level, exactly as Clojure does.
    call ev("17b. ", "(do (let* [y 1] (def z 9)) z)", "9")
    ! A local SHADOWS a var of the same name rather than redefining it.
    call ev("17c. ", "(do (def w 1) (let* [w 2] w))", "2")
    call ev("17d. ", "(do (def w 1) (let* [w 2] w) w)", "1")
    ! A function body sees namespace vars, not just its own frame.
    call ev("17e. ", "(do (def g 7) ((fn* [] g)))", "7")
    ! VAR IDENTITY: a closure built before a redefinition sees the new
    ! value, because def mutates the same Var rather than replacing
    ! it. This is the whole reason Vars exist, and it is what makes
    ! redefining a function at a REPL work.
    call ev("17f. ", &
         "(do (def target (fn* [] :old)) (def caller (fn* [] (target)))" // &
         " (def target (fn* [] :new)) (caller))", ":new")
    ! #'x is the Var itself, not its value.
    call ev("17g. ", "(do (def q 3) (var q))", "#'user/q")
    call ev_err("17h. ", "(try (var nosuch) (catch Throwable e :unresolved))")
    ! A second namespace has its own bindings.
    call ev("17i. ", &
         "(do (def a 1) (in-ns (quote other)) (def a 2) a)", "2")
    ! Namespace.toString is its NAME. (str *ns*) is "other", not
    ! "#<ns other>" -- clj agrees, and namespace-munge is literally
    ! (.replace (str ns) \- \_), so printing the wrapper here handed
    ! deftype the class name "#<ns other>.Point".
    call ev("17j. ", &
         "(str (in-ns (quote other)))", """other""")
    ! ...but NESTED it keeps the print form, because a
    ! collection's toString prints its elements rather than
    ! calling toString on each. Clojure shows
    ! "[#object[clojure.lang.Namespace ...]]" here, not "[user]".
    call ev("17k. ", &
         "(str [(in-ns (quote other))])", """[#<ns other>]""")
  end subroutine check_namespaces

  ! `=` is STRUCTURAL in Clojure: two vectors of equal elements are
  ! equal however they were built, and a list equals a vector of the
  ! same elements because both are sequential.
  subroutine check_equality()
    call ev("18a. ", "(= [1 2] [1 2])", "true")
    call ev("18b. ", "(= [1 2] [1 3])", "false")
    call ev("18c. ", "(= (list 1 2) [1 2])", "true")
    call ev("18d. ", "(= [1 [2 3]] [1 [2 3]])", "true")
    call ev("18e. ", "(= [1 [2 3]] [1 [2 4]])", "false")
    call ev("18f. ", "(= {:a 1} {:a 1})", "true")
    call ev("18g. ", "(= {:a 1} {:a 2})", "false")
    call ev("18h. ", "(= {:a [1 2]} {:a [1 2]})", "true")
    ! Built by different routes, still equal.
    call ev("18i. ", "(= (conj [1] 2) [1 2])", "true")
  end subroutine check_equality

  ! Keywords, maps and vectors are callable in Clojure, and none of
  ! them is a function -- (:k m) and (m :k) are the same lookup from
  ! opposite sides.
  subroutine check_callables()
    call ev("19a. ", "(:a {:a 1})", "1")
    call ev("19b. ", "({:a 1} :a)", "1")
    call ev("19c. ", "(:missing {:a 1})", "nil")
    call ev("19d. ", "([:x :y :z] 1)", ":y")
    call ev("19e. ", "(let* [m {:k 7}] (:k m))", "7")
  end subroutine check_callables

  subroutine check_core_builtins()
    call ev("20a. ", "(str)", '""')
    call ev("20b. ", '(str "n=" 42)', '"n=42"')
    call ev("20c. ", "(not nil)", "true")
    call ev("20d. ", "(nth [1 2 3] 1)", "2")
    call ev("20e. ", "(get {:a 1} :b :fallback)", ":fallback")
    call ev("20f. ", "(conj [1] 2)", "[1 2]")
    call ev("20g. ", "(conj (list 2) 1)", "(1 2)")
    call ev("20h. ", "(empty? [])", "true")
    call ev("20i. ", "(empty? [1])", "false")
    ! apply spreads its last argument, which is what makes variadic
    ! forwarding work at all.
    call ev("20j. ", "(apply + [1 2 3])", "6")
    call ev("20k. ", "(apply + 1 [2 3])", "6")
    call ev("20l. ", "(assoc {:a 1} :b 2)", "{:a 1, :b 2}")
    call ev("20m. ", "(nil? nil)", "true")
  end subroutine check_core_builtins

  ! #"..." compiles to a real ICU Pattern at READ time (LispReader's
  ! read_regex), so these exercise the reader, the printer, and the six
  ! interop points Eval hangs off Pattern/Matcher -- Pattern/compile,
  ! .matcher, .find, .matches, .groupCount, .group. Real core.clj's own
  ! re-pattern/re-matcher/re-find/re-matches/re-groups/re-seq are
  ! defined in terms of exactly these six (src/clj/clojure/core.clj,
  ! lines 5061-5133) -- nothing here is invented. See Regex.f90 and
  ! DEVIATIONS.md 14.
  subroutine check_regex()
    ! A pattern prints as its own source text, same as real Clojure's
    ! Pattern.toString -- this is also the read/print round trip.
    call ev('21a. ', '#"a(b)c"', '#"a(b)c"')
    call ev('21b. ', '(instance? java.util.regex.Pattern #"x")', 'true')
    call ev('21c. ', '(instance? java.util.regex.Matcher (.matcher #"x" "y"))', &
         'true')
    ! .find advances the SAME matcher's search position -- two calls in
    ! one let* body, both against the one Matcher object.
    call ev('21d. ', &
         '(let* [m (.matcher #"\d+" "a 12 b 34")] (.find m) (.group m))', &
         '"12"')
    call ev('21e. ', &
         '(let* [m (.matcher #"\d+" "a 12 b 34")] (.find m) (.find m) (.group m))', &
         '"34"')
    ! No more matches: false, not an error.
    call ev('21f. ', &
         '(let* [m (.matcher #"\d+" "none here")] (.find m))', 'false')
    ! Capturing groups, numbered from 1; group 0 is the whole match.
    call ev('21g. ', &
         '(let* [m (.matcher #"(\d+)\.(\d+)" "v1.13 ")] (.find m) (.group m 1))', &
         '"1"')
    call ev('21h. ', &
         '(let* [m (.matcher #"(\d+)\.(\d+)" "v1.13 ")] (.find m) (.group m 2))', &
         '"13"')
    call ev('21i. ', &
         '(let* [m (.matcher #"(\d+)\.(\d+)" "v1.13 ")] (.find m) (.groupCount m))', &
         '2')
    ! matches() anchors both ends -- a partial match is false, unlike
    ! find().
    call ev('21j. ', '(.matches (.matcher #"\d+" "12"))', 'true')
    call ev('21k. ', '(.matches (.matcher #"\d+" "a12"))', 'false')
  end subroutine check_regex

  subroutine check_case()
    ! hash is gc_hash under the JVM's name. Its VALUES are ours, so
    ! what is checked is the only property case* relies on: equal
    ! things hash equal, unequal things generally do not.
    call ev('22a. ', '(= (clojure.lang.Util/hash "ab") (clojure.lang.Util/hash "ab"))', &
         'true')
    call ev('22b. ', '(= (clojure.lang.Util/hash :a) (clojure.lang.Util/hash :b))', &
         'false')
    ! The bounds `case` reads to decide whether its tests fit an int
    ! dispatch. clotran ints ARE Fortran default integers.
    call ev('22c. ', 'Integer/MAX_VALUE', '2147483647')
    call ev('22d. ', 'Integer/MIN_VALUE', '-2147483648')

    ! case* below the `case` macro, so these test OUR dispatch rather
    ! than core.clj's expansion of it. The shape is
    !   (case* expr shift mask default map<case-int [test then]>
    !          table-type test-type skip-check?)
    call ev('22e. ', &
         '(case* 2 0 0 :other {1 [1 :one] 2 [2 :two]} :compact :int)', ':two')
    call ev('22f. ', &
         '(case* 9 0 0 :other {1 [1 :one] 2 [2 :two]} :compact :int)', ':other')
    ! The post-switch equivalence check: landing on a case-int is not
    ! enough, the value must still equal that entry's test constant.
    call ev('22g. ', &
         '(case* 2 0 0 :other {2 [99 :wrong]} :compact :int)', ':other')
    ! ...unless the case-int is in skip-check, where the entry holds a
    ! condp that re-tests for itself because two constants collided.
    call ev('22h. ', &
         '(case* 2 0 0 :other {2 [99 :wrong]} :compact :int #{2})', ':wrong')
    ! A non-zero mask means the keys were shifted down to pack them:
    ! (8 >> 1) & 3 == 0, which is the key this map was built with.
    call ev('22i. ', &
         '(case* 8 1 3 :other {0 [8 :hit]} :compact :int)', ':hit')
  end subroutine check_case

  subroutine check_resources()
    ! String.contains is a SUBSTRING test. It used to be wired to
    ! contains?, which asks whether a KEY is present -- so it answered
    ! false for every (.contains s sub) in the tree, core.clj's own
    ! (.contains version-string "SNAPSHOT") included.
    call ev('23a. ', '(.contains "abc" "b")', 'true')
    call ev('23b. ', '(.contains "abc" "z")', 'false')
    call ev('23c. ', '(Integer/valueOf "12")', '12')
    ! with-open closes what it opened; our streams are strings.
    call ev('23d. ', '(.close "anything")', 'nil')
    ! A missing resource is nil, as ClassLoader.getResourceAsStream
    ! answers null rather than throwing.
    call ev('23e. ', &
         '(.getResourceAsStream (clojure.lang.RT/baseLoader) "clojure/nope")', &
         'nil')
    ! java.util.Properties is an atom over a map, because .load fills
    ! it in place.
    call ev('23f. ', &
         '(let* [p (new java.util.Properties)] (.load p "version=9") ' // &
         '(.getProperty p "version"))', &
         '"9"')
    ! The whole of core.clj form 656 on one line: a ClassLoader that is
    ! a directory, a resource read off it, and Properties parsing what
    ! came back. Pinned by the vendored version.properties.
    call ev('23g. ', &
         '(let* [p (new java.util.Properties)] ' // &
         '(.load p (.getResourceAsStream (clojure.lang.RT/baseLoader) ' // &
         '"clojure/version.properties")) (.getProperty p "version"))', &
         '"1.12.6"')
  end subroutine check_resources


  ! deftype* and reify* below the deftype/reify macros, so these test
  ! OUR special forms rather than core_deftype.clj's expansion of
  ! them -- the same split check_case makes between case* and case.
  !
  ! The shape emit-deftype* produces:
  !   (deftype* ns/Name pkg.Name [fields] :implements [ifaces]
  !             (method [this args*] body)*)
  subroutine check_deftype()
    ! A field is readable through .-name, and (new pkg.Name ...) takes
    ! the fields in declaration order.
    call ev('24a. ', &
         '(do (deftype* t/P t.P [x y] :implements []) (.-y (new t.P 1 2)))', '2')
    ! The bare name works too, because deftype emits (import pkg.Name)
    ! and clotran has nowhere to record that.
    call ev('24b. ', &
         '(do (deftype* t/Q t.Q [x] :implements []) (.-x (new Q 7)))', '7')
    ! A method body sees the fields as PLAIN NAMES, which is the whole
    ! reason bind_fields exists.
    call ev('24c. ', &
         '(do (deftype* t/R t.R [w h] :implements [] (area [this] (* w h)))' // &
         ' (. (new t.R 3 4) (area)))', '12')
    ! A PARAMETER of the same name wins over the field -- the field is
    ! skipped rather than shadowing the argument the caller passed.
    call ev('24d. ', &
         '(do (deftype* t/S t.S [w] :implements [] (get [this w] w))' // &
         ' (. (new t.S 1) (get 99)))', '99')
    ! Several bodies under one name become one multi-arity closure.
    call ev('24e. ', &
         '(do (deftype* t/T t.T [n] :implements []' // &
         ' (go [this] n) (go [this k] (+ n k)))' // &
         ' (+ (. (new t.T 5) (go)) (. (new t.T 5) (go 1))))', '11')
    ! instance? answers for the type's own name and for everything
    ! :implements lists, which is the whole hierarchy there is.
    call ev('24f. ', &
         '(do (deftype* t/U t.U [] :implements [some.IFace])' // &
         ' [(instance? t.U (new t.U)) (instance? some.IFace (new t.U))' // &
         '  (instance? java.util.Date (new t.U))])', '[true true false]')
    ! type/class answer with the full class name, which is the key a
    ! protocol's :impls map is keyed by.
    call ev('24g. ', &
         '(do (deftype* t/V t.V [] :implements []) (clotran-type (new t.V)))', ':t.V')
    ! The wrong number of fields is an error, not a silently short
    ! instance.
    call ev_err('24h. ', &
         '(do (deftype* t/W t.W [a b] :implements []) (new t.W 1))')
    ! reify* builds and instantiates in one step, and its bodies ARE
    ! closures over the surrounding scope -- the example in reify''s
    ! own docstring.
    call ev('24i. ', &
         '(let* [f "foo"] (. (reify* [] (toString [this] f)) (toString)))', &
         '"foo"')
    call ev('24j. ', &
         '(let* [n 7] (. (reify* [] (twice [this] (* 2 n))) (twice)))', '14')
    ! An unknown member on an instance still fails rather than
    ! answering nil, which is what makes a typo findable.
    call ev_err('24k. ', &
         '(do (deftype* t/X t.X [a] :implements []) (.-nope (new t.X 1)))')
  end subroutine check_deftype

  ! letfn* is let* with one difference that is the whole point:
  ! every name is in scope in every init, so the functions can call
  ! each other. Compiler.java's LetFnExpr calls that pre-seeding the
  ! env, like Lisp labels.
  subroutine check_letfn()
    ! MUTUAL recursion -- ev? is written before od? exists.
    call ev('25a. ', &
         '(letfn* [ev? (fn* [n] (if (= n 0) true (od? (- n 1))))' // &
         '          od? (fn* [n] (if (= n 0) false (ev? (- n 1))))]' // &
         '   (ev? 10))', 'true')
    call ev('25b. ', &
         '(letfn* [ev? (fn* [n] (if (= n 0) true (od? (- n 1))))' // &
         '          od? (fn* [n] (if (= n 0) false (ev? (- n 1))))]' // &
         '   (od? 10))', 'false')
    ! SELF recursion, which let* could not do either.
    call ev('25c. ', &
         '(letfn* [f (fn* [n] (if (< n 2) 1 (* n (f (- n 1)))))] (f 5))', &
         '120')
    ! The body sees the names too, not just the inits.
    call ev('25d. ', '(letfn* [g (fn* [] :g)] (g))', ':g')
    ! An init CLOSES OVER the shared frame, so a later binding is
    ! visible to an earlier closure -- the seeded nil must have been
    ! overwritten in the same frame, not in a copy of it.
    call ev('25e. ', &
         '(letfn* [a (fn* [] (b)) b (fn* [] 7)] (a))', '7')
    call ev_err('25f. ', '(letfn* [x] x)')
  end subroutine check_letfn

  ! `symbol` and `keyword` with ONE argument keep the whole name.
  ! Symbol.intern(String) splits on the slash and sets both halves,
  ! so the qualifier survives -- stripping it is what `name` does.
  subroutine check_symbol_names()
    call ev('26a. ', '(symbol "a.b.C/create")', 'a.b.C/create')
    call ev('26b. ', '(namespace (symbol "a.b.C/create"))', '"a.b.C"')
    call ev('26c. ', '(name (symbol "a.b.C/create"))', '"create"')
    ! Two arguments still glue, and an unqualified name is untouched.
    call ev('26d. ', '(symbol "a.b.C" "create")', 'a.b.C/create')
    call ev('26e. ', '(symbol "plain")', 'plain')
    call ev('26f. ', '(keyword "a/b")', ':a/b')
  end subroutine check_symbol_names

  ! METADATA IS INVISIBLE TO LOOKUP as well as to equality. `apply`
  ! strips it from the thing being CALLED, so a wrapped map worked as
  ! a function; the ARGUMENT was not stripped, so a keyword applied
  ! to a wrapped map looked itself up in the wrapper and answered nil.
  !
  ! That is how `require` lost its :refer -- select-keys ends
  ! (with-meta ret (meta map)), so load-lib asked (:refer filter-opts)
  ! of a wrapped map and never called refer at all.
  ! A second context, switched to under torture, must not lose what
  ! the first was holding on its value stack: the parked stack is
  ! scanned by the collector like the live one.
  ! A sorted map under torture: every assoc copies both runs through
  ! the comparer, which is where a rooting slip would show.
  subroutine check_sorted()
    type(gc_value) :: env, r
    integer :: base
    character(len=:), allocatable :: got
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call gc_init(64)
    gc_torture = .false.
    base = vs_enter(1)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    gc_torture = torturing
    r = gce_analyze(gcr_read("(dissoc (assoc (assoc (clojure.lang.PersistentTreeMap/create (list 3 :c 1 :a 9 :z)) 2 :b) 0 :zero) 9)", no_roots), gc_nil())
    if (.not. gce_has_error()) r = gce_eval(r, gc_nil(), no_roots)
    block
       call gcp_str(r, .true., s=dlt_1)
       got = dlt_1
    end block
    call ok("31a. a sorted map keeps its keys in order through assoc and dissoc: " // got, &
         got == "{0 :zero, 1 :a, 2 :b, 3 :c}" .and. .not. gce_has_error())
    gc_torture = .false.
    call vs_leave(base)
  end subroutine check_sorted

  subroutine check_contexts()
    type(gc_value) :: env, form, r
    integer :: base, c1, c2
    character(len=:), allocatable :: got

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call gc_init(64)
    gc_torture = .false.
    base = vs_enter(3)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    form = gcr_read("(list 1 2 3 (str ""a"" ""b"") [4 5] {:k 6})", [vs_get(base + 1)])
    call vs_set(base + 2, form)
    c1 = gce_ctx_current()
    c2 = gce_ctx_new()
    gc_torture = torturing
    call gce_ctx_switch(c2)
    ! allocate a lot in the new context; every allocation collects
    r = gce_analyze(gcr_read("(loop* [i 0 acc []] (if (< i 200) (recur (+ i 1) (conj acc (str i))) (count acc)))", no_roots), gc_nil())
    if (.not. gce_has_error()) r = gce_eval(r, gc_nil(), no_roots)
    block
       call gcp_str(r, .true., s=dlt_1)
       got = dlt_1
    end block
    call ok("30a. a form evaluates in a second context: " // got, got == "200" .and. .not. gce_has_error())
    call gce_ctx_switch(c1)
    gc_torture = .false.
    block
       call gcp_str(vs_get(base + 2), .true., s=dlt_1)
       got = dlt_1
    end block
    call ok("30b. the first context's stack survived the switch: " // got, &
         got == "(list 1 2 3 (str ""a"" ""b"") [4 5] {:k 6})")
    call ok("30c. and it is current again", gce_ctx_current() == c1)
    call vs_leave(base)
  end subroutine check_contexts

  subroutine check_meta_lookup()
    call ev('27a. ', '(:a (with-meta {:a 1} {:x 9}))', '1')
    call ev('27b. ', '(get (with-meta {:a 1} {:x 9}) :a)', '1')
    ! The other direction already worked, and must keep working.
    call ev('27c. ', '((with-meta {:a 1} {:x 9}) :a)', '1')
    call ev('27d. ', '(:a {:a 1})', '1')
    ! A missing key is still nil, wrapper or not.
    call ev('27e. ', '(:zz (with-meta {:a 1} {:x 9}))', 'nil')
  end subroutine check_meta_lookup

  ! A native array's buffer lives OUTSIDE the heap -- it has to, since
  ! the point is a contiguous Fortran array at a stable address. So the
  ! collector freeing the object is not enough; the sweep has to tell
  ! NativeArray that the handle died, or the buffer is held for the
  ! life of the process.
  !
  ! That leak is invisible from Clojure, which is why it is checked
  ! here against the registry's own count rather than through any
  ! value. DEVIATIONS 14 records the same leak for Matcher, found the
  ! same way and still open.
  subroutine check_native_arrays()
    type(gc_value) :: form, env, result
    integer :: base, before

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    call gc_init(64)
    gc_torture = .false.
    base = vs_enter(3)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    before = gcna_live_count()

    form = gcr_read('(fortran/make-array "real8" 4)', [vs_get(base + 1)])
    call vs_set(base + 2, form)
    call gce_clear_error()
    ! Analysed, then executed: the same two halves main.f90 runs, so
    ! the torture pass covers the analyser's rooting too.
    result = gce_analyze(vs_get(base + 2), vs_get(base + 1))
    call vs_set(base + 2, result)
    if (.not. gce_has_error()) result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
    call vs_set(base + 3, result)
    call ok("28a. an array claims a buffer: ", gcna_live_count() - before == 1)
    block
       call gcna_kind(gc_i1(vs_get(base + 3)), s=dlt_1)
       call ok("28b. ...of the kind asked for: ", dlt_1 == "real8")
    end block
    call ok("28c. ...with the extent asked for: ", &
         gcna_total(gc_i1(vs_get(base + 3))) == 4)

    ! Still rooted on the value stack, so a collection must NOT free it.
    ! Getting this backwards is the failure that looks like a working
    ! finalizer right up until something reads a freed buffer.
    call gc_collect(no_roots)
    call ok("28d. a collection keeps it while rooted: ", &
         gcna_live_count() - before == 1)

    ! Drop every reference and collect again.
    call vs_set(base + 3, gc_nil())
    call vs_set(base + 2, gc_nil())
    call gc_collect(no_roots)
    call ok("28e. ...and frees the buffer once unreachable: ", &
         gcna_live_count() - before == 0)

    call vs_leave(base)
  end subroutine check_native_arrays

  ! A Pattern and a Matcher each hold an ICU object, and a Matcher holds
  ! a subject-text buffer as well -- ICU keeps only a shallow reference
  ! to that, so nothing else can free it.
  !
  ! `cre_close` was declared in the interface and never called from
  ! anywhere, so every compiled pattern and every matcher leaked its
  ! whole handle for the life of the process. DEVIATIONS 14 recorded
  ! only the text half of that, and called it structural -- "a
  ! destructor path, which nothing else in the GC heap has either" --
  ! which stopped being true when native arrays gave the sweep a
  ! finalizer hook.
  !
  ! Checked against the registry's own count, because the leak is
  ! invisible from Clojure. That is exactly why it survived this long.
  subroutine check_regex_release()
    type(gc_value) :: form, env, result
    integer :: base, before

    call gc_init(64)
    gc_torture = .false.
    base = vs_enter(3)
    env = gce_base_env(no_roots)
    call vs_set(base + 1, env)
    before = regex_live_count()

    form = gcr_read('(. #"a+" (matcher "aaa"))', [vs_get(base + 1)])
    call vs_set(base + 2, form)
    call gce_clear_error()
    ! Analysed, then executed: the same two halves main.f90 runs, so
    ! the torture pass covers the analyser's rooting too.
    result = gce_analyze(vs_get(base + 2), vs_get(base + 1))
    call vs_set(base + 2, result)
    if (.not. gce_has_error()) result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
    call vs_set(base + 3, result)
    ! The pattern and the matcher's own clone are two distinct handles.
    call ok("29a. a matcher opens handles: ", regex_live_count() - before >= 2)

    call gc_collect(no_roots)
    call ok("29b. a collection keeps them while rooted: ", &
         regex_live_count() - before >= 2)

    call vs_set(base + 3, gc_nil())
    call vs_set(base + 2, gc_nil())
    call gc_collect(no_roots)
    call ok("29c. ...and closes them once unreachable: ", &
         regex_live_count() - before == 0)

    call vs_leave(base)
  end subroutine check_regex_release

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
    ! Analysed, then executed: the same two halves main.f90 runs, so
    ! the torture pass covers the analyser's rooting too.
    result = gce_analyze(vs_get(base + 2), vs_get(base + 1))
    call vs_set(base + 2, result)
    if (.not. gce_has_error()) result = gce_eval(vs_get(base + 2), vs_get(base + 1), no_roots)
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call gc_check_heap(problem=dlt_1)
       call ok("10a. the heap passes its own audit: ", dlt_1 == "")
    end block
  end subroutine check_heap_sound

end program eval_test

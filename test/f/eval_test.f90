! Validates Eval end to end: parses real mal source text (same as the
! REPL will), evaluates it, and checks the printed result. Covers
! arithmetic, def!/let*, nested scope, and error reporting.
program eval_test
  use values
  use Env
  use LispReader, only: read_str
  use Eval, only: eval_top, repl_env
  use printer, only: pr_str
  implicit none

  logical :: all_ok
  type(env_ref) :: env

  all_ok = .true.
  env = repl_env()

  call expect_result("1a. simple addition: ", env, "(+ 1 2)", "3", all_ok)
  call expect_result("1b. nested arithmetic: ", env, "(+ 5 (* 2 3))", "11", all_ok)
  call expect_result("1c. subtraction, n-ary: ", env, "(- 10 2 3)", "5", all_ok)
  call expect_result("1d. division: ", env, "(/ 20 2 2)", "5", all_ok)
  call expect_result("1e. negation: ", env, "(- 5)", "-5", all_ok)

  call expect_result("2a. self-evaluating int: ", env, "7", "7", all_ok)
  call expect_result("2b. self-evaluating string: ", env, '"hi"', '"hi"', all_ok)
  call expect_result("2c. vector elements are evaluated: ", env, "[1 (+ 1 1) 3]", "[1 2 3]", all_ok)

  call expect_result("3a. def! binds and returns the value: ", env, "(def! x 10)", "10", all_ok)
  call expect_result("3b. the binding persists in this env: ", env, "(+ x 1)", "11", all_ok)

  call expect_result("4a. let* creates a scoped binding: ", env, "(let* (a 5) (+ a 1))", "6", all_ok)
  call expect_result("4b. let* bindings can see earlier ones: ", env, "(let* (a 2 b (* a 3)) b)", "6", all_ok)
  call expect_result("4c. let*'s bindings don't leak out: ", env, "x", "10", all_ok)

  call expect_error("5a. unbound symbol is an error: ", env, "undefined_symbol")
  call expect_error("5b. calling a non-function is an error: ", env, "(1 2 3)")

  call expect_result("6a. quote returns its argument unevaluated: ", env, "'(1 2 3)", "(1 2 3)", all_ok)
  call expect_result("6b. list builds a list from evaluated args: ", env, "(list 1 (+ 1 1))", "(1 2)", all_ok)
  call expect_result("6c. vector builds a vector: ", env, "(vector 1 2)", "[1 2]", all_ok)
  call expect_result("6d. first/rest/cons/conj: ", env, "(cons 0 (conj (rest '(1 2 3)) 9))", "(0 9 2 3)", all_ok)
  call expect_result("6e. count: ", env, "(count (list 1 2 3))", "3", all_ok)
  call expect_result("6f. nth: ", env, "(nth [1 2 3] 1)", "2", all_ok)

  ! 7. Keywords and maps are callable, same as real Clojure.
  call expect_result("7a. a keyword invoked on a map looks itself up: ", env, "(:a {:a 1 :b 2})", "1", all_ok)
  call expect_result("7b. a map invoked on a key does the same: ", env, "({:a 1} :a)", "1", all_ok)
  call expect_result("7c. get with a missing key and a default: ", env, "(get {:a 1} :z 42)", "42", all_ok)
  call expect_result("7d. assoc: ", env, "(assoc {:a 1} :b 2)", "{:a 1 :b 2}", all_ok)

  call expect_result("8a. real-number literal reads and prints back: ", env, "18.0", "18.00", all_ok)

  call expect_result("9a. if, truthy branch: ", env, "(if 1 2 3)", "2", all_ok)
  call expect_result("9b. if, falsy (nil) branch: ", env, "(if nil 2 3)", "3", all_ok)
  call expect_result("9c. if with no else, falsy: ", env, "(if false 2)", "nil", all_ok)
  call expect_result("9d. do evaluates in order, returns the last: ", env, "(do (def! y 1) (+ y 1))", "2", all_ok)

  call expect_result("10a. fn* applies to args: ", env, "((fn* (a b) (+ a b)) 3 4)", "7", all_ok)
  call expect_result("10b. fn* closes over its defining env: ", env, &
       "(((fn* (a) (fn* (b) (+ a b))) 5) 7)", "12", all_ok)
  call expect_result("10c. fn* recurses through def!: ", env, &
       "(def! sumdown (fn* (n) (if (> n 0) (+ n (sumdown (- n 1))) 0)))", "#<fn>", all_ok)
  call expect_result("10c'. ...and the recursive call works: ", env, "(sumdown 3)", "6", all_ok)
  call expect_result("10d. & rest args collect into a list: ", env, "((fn* (a & more) (count more)) 1 2 3)", "2", all_ok)
  call expect_result("10e. multiple body forms run in order, last is returned: ", env, &
       "((fn* (x) (+ x 1) (+ x 100)) 5)", "105", all_ok)
  call expect_result("10f. ...and earlier forms' side effects (def!) still happen: ", env, &
       "(do (def! g (fn* (x) (def! y (+ x 1)) (* y 2))) (g 5))", "12", all_ok)
  call expect_result("10g. fn* takes an optional self-reference name: ", env, &
       "((fn* fact (n) (if (< n 2) 1 (* n (fact (- n 1))))) 5)", "120", all_ok)
  call expect_result("10h. ...invisible outside the fn (no outer def leaks): ", env, &
       "(try* fact (catch* e true))", "true", all_ok)

  call expect_result("11a. numeric comparisons: ", env, "(list (< 1 2) (>= 2 2) (<= 3 2))", "(true true false)", all_ok)
  call expect_result("11b. = is structural, list and vector cross-compare: ", env, "(= (list 1 2) [1 2])", "true", all_ok)
  call expect_result("11c. list?/empty?: ", env, "(list (list? [1]) (empty? (list)))", "(false true)", all_ok)

  ! 12. TCO: without it, these would blow the Fortran call stack instead
  ! of returning -- the point of step5.
  call expect_result("12a. tail-recursive self-call: ", env, &
       "(def! sum2 (fn* (n acc) (if (= n 0) acc (sum2 (- n 1) (+ n acc)))))", "#<fn>", all_ok)
  call expect_result("12a'. ...10000 deep doesn't overflow the stack: ", env, "(sum2 10000 0)", "50005000", all_ok)
  call expect_result("12b. tail-recursive mutual call: ", env, &
       "(def! ping (fn* (n) (if (= n 0) 0 (pong (- n 1)))))", "#<fn>", all_ok)
  call expect_result("12b'. ...: ", env, "(def! pong (fn* (n) (if (= n 0) 0 (ping (- n 1)))))", "#<fn>", all_ok)
  call expect_result("12b''. ...10000 deep, mutual: ", env, "(ping 10000)", "0", all_ok)

  call expect_result("13a. read-string parses without evaluating: ", env, &
       '(read-string "(+ 1 2)")', "(+ 1 2)", all_ok)
  call expect_result("13b. eval evaluates the result: ", env, &
       '(eval (read-string "(+ 1 2)"))', "3", all_ok)
  call expect_result("13c. eval ignores the calling env, always uses the repl env: ", env, &
       '(let* (x 99) (eval (read-string "x")))', "10", all_ok)

  call expect_result("14a. atom, deref: ", env, "(deref (atom 5))", "5", all_ok)
  call expect_result("14b. atom?: ", env, "(list (atom? (atom 5)) (atom? 5))", "(true false)", all_ok)
  call expect_result("14c. reset!: ", env, "(def! at (atom 1))", "(atom 1)", all_ok)
  call expect_result("14c'. ...changes what deref sees: ", env, "(reset! at 7)", "7", all_ok)
  call expect_result("14c''. ...", env, "(deref at)", "7", all_ok)
  call expect_result("14d. swap! applies f to the current value: ", env, "(swap! at (fn* (a b) (+ a b)) 3)", "10", all_ok)

  ! 15. Namespaces: def! interns in *ns* (clojure.core), not the
  ! lexical env; a bare builtin resolves through clojure.core's
  ! auto-refer, same as a real Clojure REPL in `user`.
  call expect_result("15a. + resolves via clojure.core's auto-refer: ", env, "(+ 1 2)", "3", all_ok)
  call expect_result("15b. def! interns in *ns*, visible after: ", env, "(def! ns-x 5)", "5", all_ok)
  call expect_result("15b'. ...: ", env, "ns-x", "5", all_ok)
  call expect_result("15c. def! inside let* still lands in *ns*, not the local env: ", env, &
       "(let* (y 1) (def! ns-y 99))", "99", all_ok)
  call expect_result("15c'. ...visible at top level after the let* exits: ", env, "ns-y", "99", all_ok)
  call expect_result("15d. in-ns switches *ns*, creating it if new: ", env, "(in-ns 'other)", "other", all_ok)
  call expect_result("15e. clojure.core is still auto-referred from the new ns: ", env, "(+ 1 1)", "2", all_ok)
  call expect_error("15f. ...but user's own bindings are NOT visible from other: ", env, "ns-x")
  call expect_result("15g. back to user: ", env, "(in-ns 'user)", "user", all_ok)
  call expect_result("15g'. ...ns-x is visible again: ", env, "ns-x", "5", all_ok)
  ! ns: name is never evaluated (unlike in-ns, which expects a quoted
  ! symbol) -- same as def's name position, and clauses after the
  ! name (:require/:import, not built) are silently ignored for now.
  call expect_result("15h. ns switches *ns* too, name never evaluated: ", env, "(ns another.ns)", "another.ns", all_ok)
  call expect_result("15h'. ...clojure.core still auto-referred: ", env, "(+ 3 4)", "7", all_ok)
  call expect_result("15h''. back to user: ", env, "(in-ns 'user)", "user", all_ok)

  ! 16. Real syntax-quote: unquote/splice-unquote work like mal's, but
  ! plain symbols get namespace-qualified and vectors stay vectors
  ! (mal's own reference impls produce a list for a quasiquoted vector
  ! -- a known limitation this project doesn't inherit).
  call expect_result("16a. quasiquote on a literal is identity: ", env, "`(1 2 3)", "(1 2 3)", all_ok)
  call expect_result("16b. unquote evaluates: ", env, "`(1 ~(+ 1 1) 3)", "(1 2 3)", all_ok)
  call expect_result("16c. splice-unquote splices a list's elements in: ", env, &
       "`(1 ~@(list 8 9) 3)", "(1 8 9 3)", all_ok)
  call expect_result("16d. a quasiquoted vector stays a vector: ", env, "`[1 ~(+ 1 1) 3]", "[1 2 3]", all_ok)
  call expect_result("16e. a bare symbol gets namespace-qualified: ", env, "`ns-x", "user/ns-x", all_ok)
  call expect_result("16f. ...via clojure.core's auto-refer when that's where it lives: ", env, "`+", "clojure.core/+", all_ok)
  call expect_result("16g. special form names stay bare: ", env, "`if", "if", all_ok)
  call expect_result("16h. x# auto-gensyms (not literally x): ", env, "(= (quote x) (first (rest `(a x# c))))", &
       "false", all_ok)
  call expect_result("16i. ...but consistently within one quasiquote: ", env, &
       "(let* (r `(x# x#)) (= (first r) (first (rest r))))", "true", all_ok)

  ! 17. defmacro/macroexpand: real Clojure's own syntax and semantics,
  ! not mal's (defmacro! name (fn* (params) body)) with an unevaluated
  ! macroexpand -- see NOTES.md for why that diverges from mal's spec.
  call expect_result("17a. defmacro takes params/body directly, real Clojure style: ", env, &
       "(defmacro unless [pred a b] `(if ~pred ~b ~a))", "#<macro>", all_ok)
  call expect_result("17b. a macro call expands then evaluates: ", env, "(unless false 7 8)", "7", all_ok)
  call expect_result("17b'. ...: ", env, "(unless true 7 8)", "8", all_ok)
  call expect_result("17c. macroexpand needs its argument quoted, like real Clojure (not mal's): ", env, &
       "(macroexpand '(unless false 7 8))", "(if false 8 7)", all_ok)
  call expect_result("17d. a macro's params can close over/shadow like any closure: ", env, &
       "(defmacro identity [x] x)", "#<macro>", all_ok)
  call expect_result("17d'. ...: ", env, "(let* (a 123) (identity a))", "123", all_ok)

  ! 18. cond/not: the first bootstrapped-in-this-language core macros
  ! (real clojure.core's own cond is written in Clojure too, not Java).
  call expect_result("18a. not: ", env, "(list (not false) (not true))", "(true false)", all_ok)
  call expect_result("18b. cond with no clauses: ", env, "(cond)", "nil", all_ok)
  call expect_result("18c. cond picks the first truthy test: ", env, "(cond false 7 true 8 true 9)", "8", all_ok)
  call expect_result("18d. cond falls through to nil if nothing matches: ", env, "(cond false 7 false 8)", "nil", all_ok)
  call expect_result("18e. cond recurses through many clauses without overflowing (TCO): ", env, &
       "(cond false 1 false 2 false 3 false 4 false 5 false 6 false 7 false 8 true 9)", "9", all_ok)

  ! 19. Explicitly namespace-qualified symbols resolve directly in the
  ! named namespace -- what makes cond's own self-reference (quasiquote
  ! qualifies it to clojure.core/cond) actually work when invoked.
  ! #<fn>, not #<builtin +>: real core.clj defines its own + over
  ! clojure.lang.Numbers and that's what clojure.core/+ now holds --
  ! the native one is still there as clotran.native/+ (see 25g).
  call expect_result("19a. an explicitly qualified symbol resolves in that namespace: ", env, &
       "clojure.core/+", "#<fn>", all_ok)
  call expect_result("19b. ...and is callable as such: ", env, "(clojure.core/+ 1 2)", "3", all_ok)

  ! 20. throw/try/catch: real Clojure's own names (try*/catch* also
  ! recognized, same as def!/def). Any value can be thrown, not just a
  ! string -- and internal errors (symbol not found, nth out of
  ! bounds) are catchable the same way, wrapped as a string.
  call expect_result("20a. try with no error just returns the body: ", env, "(try 123 (catch Exception e 456))", "123", all_ok)
  call expect_result("20b. an internal error is catchable, as a string: ", env, &
       "(try abc (catch Exception exc exc))", '"'//"'abc' not found"//'"', all_ok)
  call expect_result("20c. nth out of bounds errors, catchably: ", env, &
       "(try (nth (list) 1) (catch Exception exc 99))", "99", all_ok)
  call expect_result("20d. (throw x) throws x, caught and bound: ", env, &
       "(try (throw (list 1 2)) (catch Exception e e))", "(1 2)", all_ok)
  ! doall, because map is genuinely lazy now (see NOTES.md): real
  ! Clojure wouldn't throw here either until the seq is realized.
  call expect_result("20e. throw is an ordinary function, usable as a value: ", env, &
       "(try (doall (map throw (list 99))) (catch Exception e e))", "99", all_ok)
  call expect_result("20f. try*/catch* (mal's names) work too: ", env, "(try* 7 (catch* e 8))", "7", all_ok)

  ! 21. apply/map/type predicates.
  call expect_result("21a. apply spreads the last arg's elements: ", env, "(apply + (list 2 3))", "5", all_ok)
  call expect_result("21b. ...with fixed args before it: ", env, "(apply + 4 (list 5))", "9", all_ok)
  call expect_result("21c. apply works on a user fn* too: ", env, "(apply (fn* (a b) (+ a b)) (list 2 3))", "5", all_ok)
  call expect_result("21d. map applies f to every element, eagerly, as a list: ", env, &
       "(map (fn* (a) (* 2 a)) (list 1 2 3))", "(2 4 6)", all_ok)
  call expect_result("21e. symbol?/nil?/true?/false?: ", env, &
       "(list (symbol? (quote abc)) (nil? nil) (true? true) (false? false) (symbol? 5))", &
       "(true true true true false)", all_ok)

  ! 22. *host-language*: readline itself needs real stdin, exercised
  ! via the official mal suite/manual testing instead.
  call expect_result("22a. *host-language* names this implementation: ", env, &
       '(= *host-language* "something bogus")', "false", all_ok)

  ! 23. The step9 deferred extras: hash-map ops, symbol/keyword
  ! constructors, remaining type predicates, and finally str/pr-str
  ! (deferred all the way back at step4).
  call expect_result("23a. hash-map builds a map from alternating args: ", env, &
       '(hash-map "a" 1 "b" 2)', '{"a" 1 "b" 2}', all_ok)
  call expect_result("23b. contains?: ", env, '(list (contains? {"a" 1} "a") (contains? {"a" 1} "z"))', &
       "(true false)", all_ok)
  call expect_result("23c. keys/vals, in insertion order: ", env, &
       '(list (keys (hash-map "a" 1 "b" 2)) (vals (hash-map "a" 1 "b" 2)))', &
       '(("a" "b") (1 2))', all_ok)
  call expect_result("23d. dissoc removes keys, persistently: ", env, &
       '(list (dissoc {"a" 1 "b" 2} "a") {"a" 1 "b" 2})', '({"b" 2} {"a" 1 "b" 2})', all_ok)
  call expect_result("23e. symbol/keyword constructors: ", env, &
       '(list (symbol "abc") (keyword "abc") (keyword :abc))', "(abc :abc :abc)", all_ok)
  call expect_result("23f. keyword?/vector?/map?/sequential?: ", env, &
       "(list (keyword? :a) (vector? [1]) (map? {}) (sequential? (list 1)) (sequential? {}))", &
       "(true true true true false)", all_ok)
  call expect_result("23g. str: non-readable, no separator: ", env, &
       '(str "A" {:abc "val"} "Z")', '"A{:abc val}Z"', all_ok)
  call expect_result("23h. pr-str: readable, space-separated, returned not printed: ", env, &
       '(pr-str "A" "Z")', '"\"A\" \"Z\""', all_ok)
  call expect_result("23i. assoc is variadic, applying every pair: ", env, &
       '(count (keys (assoc {"a" 1} "b" 2 "c" 3)))', "3", all_ok)
  call expect_result("23j. maps compare by value, not identity: ", env, &
       '(list (= {} {}) (= {:a 1} {:a 1}) (= {:a 1} {:a 2}) (= {:a 1} {:a 1 :b 2}))', &
       "(true true false false)", all_ok)
  call expect_result("24a. number?/string?/fn?/seq: ", env, &
       '(list (number? 1) (string? "a") (fn? +) (seq [1 2]))', "(true true true (1 2))", all_ok)
  call expect_result("24b. with-meta attaches metadata without mutating the original: ", env, &
       '(def! f (with-meta (fn* (x) x) {"doc" "orig"}))', "#<fn>", all_ok)
  call expect_result("24c. ...meta reads it back: ", env, &
       '(get (meta f) "doc")', '"orig"', all_ok)
  call expect_result("24d. ...a value with no metadata has none: ", env, &
       "(meta (fn* (x) x))", "nil", all_ok)
  call expect_result("24e. ...with-meta on the same fn again doesn't touch the first: ", env, &
       '(list (get (meta (with-meta f {"doc" "new"})) "doc") (get (meta f) "doc"))', &
       '("new" "orig")', all_ok)
  ! ^META FORM attaches META to FORM itself, never evaluated -- real
  ! Clojure's actual reader behavior (not mal's own (with-meta FORM
  ! META), an evaluated call). Needed so `(def ^{...} name val)`'s
  ! name position reads as a bare symbol, metadata riding along
  ! invisibly, not an unevaluated list sitting where def expects a
  ! symbol -- pervasive in real clojure/core.clj's own bootstrap.
  call expect_result("24j. ^META on a def's name reads as a bare symbol: ", env, &
       '(def ^{:doc "x"} tagged-name 42)', "#'user/tagged-name", all_ok)
  call expect_result("24j'. ...still correctly bound, not lost: ", env, &
       "tagged-name", "42", all_ok)
  call expect_result("24k. ^META on a fn*'s self-reference name works too: ", env, &
       "((fn* ^:static named-self [n] (if (< n 1) 0 (+ n (named-self (- n 1))))) 3)", "6", all_ok)
  call expect_result("24f. time-ms is non-decreasing: ", env, &
       "(let* [t (time-ms)] (>= (time-ms) t))", "true", all_ok)
  call expect_result("24g. fn?/macro? tell functions and macros apart: ", env, &
       "(list (fn? +) (fn? cond) (macro? cond) (macro? +))", "(true false true false)", all_ok)
  call expect_result("24h. conj is variadic, left to right: ", env, &
       "(list (conj (list 2 3) 4 5 6) (conj [2 3] 4 5 6))", "((6 5 4 2 3) [2 3 4 5 6])", all_ok)
  call expect_result("24i. seq on a string splits into characters: ", env, &
       '(seq "abc")', '(\a \b \c)', all_ok)

  ! 25. Reader conditionals: #?(:cljf a :clj b) reads as whichever
  ! branch matches this host's own feature key, first match wins.
  call expect_result("25a. :cljf branch is picked over :clj: ", env, &
       "#?(:cljf 1 :clj 2)", "1", all_ok)
  call expect_result("25b. ...regardless of branch order: ", env, &
       "#?(:clj 1 :cljf 2)", "2", all_ok)
  call expect_result("25c. :default matches when there's no :cljf branch: ", env, &
       "#?(:clj 1 :default 2)", "2", all_ok)
  call expect_result("25d. reads as one form, nested inside another: ", env, &
       "(+ 1 #?(:cljf 10 :clj 20))", "11", all_ok)
  call expect_result("25e. auto-gensym (trailing #) still tokenizes as one symbol: ", env, &
       "(let* (r `(a# a#)) (= (first r) (first (rest r))))", "true", all_ok)
  call expect_result("25f. every builtin is also reachable via clotran.native, unqualified: ", env, &
       "(clotran.native/first (list 1 2 3))", "1", all_ok)
  call expect_result("25g. ...surviving even if clojure.core/first gets shadowed: ", env, &
       '(do (def first (fn* [x] "shadowed"))' // &
       '    (def shadow-result (list (first [1 2 3]) (clotran.native/first [1 2 3])))' // &
       '    (def first clotran.native/first)' // & ! put it back: every later check needs a working first
       '    shadow-result)', &
       '("shadowed" 1)', all_ok)

  ! 26. Multi-arity fn*: (fn* name? ([p1] b1) ([p2] b2) ...), dispatched
  ! by argument count, same as real Clojure's own fn*/fn.
  call expect_result("26a. dispatches by argument count: ", env, &
       "(def multi (fn* ([] :zero) ([a] :one) ([a b] :two)))", "#'user/multi", all_ok)
  call expect_result("26a'. ...zero args: ", env, "(multi)", ":zero", all_ok)
  call expect_result("26a''. ...one arg: ", env, "(multi 1)", ":one", all_ok)
  call expect_result("26a'''. ...two args: ", env, "(multi 1 2)", ":two", all_ok)
  call expect_result("26b. a variadic clause matches anything at or above its minimum: ", env, &
       "(def variadic-multi (fn* ([a] :one) ([a b & c] (count c))))", "#'user/variadic-multi", all_ok)
  call expect_result("26b'. ...exact fixed arity still wins over a variadic clause: ", env, &
       "(variadic-multi 1)", ":one", all_ok)
  call expect_result("26b''. ...variadic collects everything past its required params: ", env, &
       "(variadic-multi 1 2 3 4)", "2", all_ok)
  call expect_result("26c. an unmatched arity is a catchable error: ", env, &
       "(try* (multi 1 2 3) (catch* e true))", "true", all_ok)
  call expect_result("26d. mal-style paren params still work (not mistaken for multi-arity): ", env, &
       "((fn* (a b) (+ a b)) 3 4)", "7", all_ok)
  call expect_result("26e. ...named self-reference plus multi-arity together: ", env, &
       "((fn* countdown ([n] (countdown n 0)) ([n acc] (if (= n 0) acc (countdown (- n 1) (+ acc 1))))) 5)", &
       "5", all_ok)

  ! 27. Sets: #{...} reader syntax, backed by the same array_map_t as
  ! hash-maps (each element mapped to itself), same as real Clojure's
  ! PersistentHashSet wrapping a map.
  call expect_result("27a. #{...} reads and prints back: ", env, "#{1 2 3}", "#{1 2 3}", all_ok)
  call expect_result("27b. get finds a present element, nil otherwise: ", env, &
       "(list (get #{1 2 3} 2) (get #{1 2 3} 5))", "(2 nil)", all_ok)
  call expect_result("27c. contains?/set?/count: ", env, &
       "(list (contains? #{1 2} 1) (set? #{1 2}) (set? [1 2]) (count #{1 2 3}))", "(true true false 3)", all_ok)
  call expect_result("27d. = is unordered: ", env, "(= #{1 2} #{2 1})", "true", all_ok)
  call expect_result("27e. hash-set dedups, conj adds, disj removes: ", env, &
       "(list (hash-set 1 2 2 3) (conj #{1 2} 3) (disj #{1 2 3} 2) (disj #{1 2 3} 2 3))", &
       "(#{1 2 3} #{1 2 3} #{1 3} #{1})", all_ok)
  call expect_result("27f. seq gives elements directly, not [k v] pairs: ", env, &
       "(seq #{1 2 3})", "(1 2 3)", all_ok)

  ! 28. #(...) anonymous-fn literals: bare % means %1, a higher %N
  ! implies the lower ones are params too, %& is the rest-arg -- all
  ! verified against real Clojure's own macroexpansion, not guessed.
  call expect_result("28a. bare % is the first (and only) arg: ", env, "(#(+ % 1) 5)", "6", all_ok)
  call expect_result("28b. %1/%2 address args positionally: ", env, "(#(+ %1 %2) 3 4)", "7", all_ok)
  call expect_result("28c. ...order in the body doesn't change which arg is which: ", env, &
       "(#(- %2 %1) 3 10)", "7", all_ok)
  call expect_result("28d. %& collects the rest: ", env, "(#(apply + %&) 1 2 3)", "6", all_ok)
  call expect_result("28e. no %-refs at all is a zero-arg fn: ", env, "(#(vector))", "[]", all_ok)

  ! 29. #'sym: real Clojure's (var sym) shorthand, resolving to a real
  ! Var (see Namespace.f90) -- prints as #'ns/name, not the bare symbol.
  call expect_result("29a. def! then #'sym prints the Var, qualified: ", env, &
       "(do (def! some-name 42) (pr-str #'some-name))", '"#''user/some-name"', all_ok)
  call expect_result("29b. var-get returns the Var's current value: ", env, &
       "(var-get #'some-name)", "42", all_ok)
  call expect_result("29c. redefinition mutates the SAME Var, doesn't replace it: ", env, &
       "(let* (v (var some-name)) (def! some-name 99) (var-get v))", "99", all_ok)
  call expect_error("29d. #'sym on a truly unbound symbol is a resolve error: ", env, "#'totally-unbound-name")

  ! 30. #"pattern": real Clojure's regex-literal syntax. No regex
  ! engine exists here (a real, separate feature) -- read as a plain
  ! string, taken raw (not unescaped like an ordinary string), since a
  ! regex's own backslash escapes (\d, \s, ...) must stay literal --
  ! confirmed against real Clojure (#"\d+" is a 3-character pattern,
  ! backslash included), not guessed.
  call expect_result("30a. #""pattern"" keeps backslashes literal, unlike a normal string: ", env, &
       '(count #"\d+")', "3", all_ok)
  call expect_result("30a'. ...an already-escaped backslash is 4 characters: ", env, &
       '(count #"\\d+")', "4", all_ok)

  ! 31. Real lazy seqs (TAG_LAZYSEQ, see NOTES.md). The point of each
  ! check is a big-O property, not just the value: nothing realizes
  ! until asked, first costs one cell, an infinite seq is finite to
  ! take/nth, and a realized cell is never recomputed.
  call expect_result("31a. nothing is realized at definition time: ", env, &
       "(do (def lz-c (atom 0)) (def lz (map (fn [x] (swap! lz-c inc) x) (range 50))) (deref lz-c))", &
       "0", all_ok)
  call expect_result("31b. first realizes exactly one cell: ", env, &
       "(do (first lz) (deref lz-c))", "1", all_ok)
  call expect_result("31c. count realizes the rest, once: ", env, &
       "(do (count lz) (count lz) (deref lz-c))", "50", all_ok)
  call expect_result("31d. an infinite seq is fine as long as you take from it: ", env, &
       "(take 5 (iterate inc 0))", "(0 1 2 3 4)", all_ok)
  call expect_result("31e. ...including (range) with no bound: ", env, "(nth (range) 7)", "7", all_ok)
  call expect_result("31f. repeat/cycle are infinite too: ", env, &
       "(list (take 3 (repeat :x)) (take 4 (cycle [1 2])))", "((:x :x :x) (1 2 1 2))", all_ok)

  ! 32. binding: real dynamic scope over a real Var, pushed and popped
  ! around the body (the pop lives in binding's own finally).
  call expect_result("32a. binding shadows the root inside its body: ", env, &
       "(do (def ^:dynamic *dv* 1) (binding [*dv* 99] *dv*))", "99", all_ok)
  call expect_result("32b. ...and the root is restored after: ", env, "*dv*", "1", all_ok)
  call expect_result("32c. a function called inside sees the bound value: ", env, &
       "(do (defn dv-read [] *dv*) (list (binding [*dv* 7] (dv-read)) (dv-read)))", "(7 1)", all_ok)
  call expect_result("32d. nested bindings restore one level at a time: ", env, &
       "(binding [*dv* 1] (list (binding [*dv* 2] *dv*) *dv*))", "(2 1)", all_ok)

  ! 33. Character literals: a real type of their own, not a
  ! one-character string -- so (= \a "a") is false, same as Clojure.
  call expect_result("33a. a bare character literal: ", env, "\a", "\a", all_ok)
  call expect_result("33b. the named characters: ", env, &
       "[\space \newline \tab]", "[\space \newline \tab]", all_ok)
  call expect_result("33c. ...including ones that aren't regular symbol characters: ", env, &
       "[\/ \( \]]", "[\/ \( \]]", all_ok)
  call expect_result("33d. a character is not the one-character string: ", env, &
       '(list (= \a \a) (= \a "a") (char? \a) (string? \a))', "(true false true false)", all_ok)
  call expect_result("33e. ...and str still renders it as its own text: ", env, &
       "(str \a \b)", '"ab"', all_ok)
  call expect_result("33f. characters work as map keys: ", env, &
       "(get {\a 1 \b 2} \b)", "2", all_ok)

  ! 34. #_ discards exactly the next form, wherever it appears.
  call expect_result("34a. mid-collection: ", env, "[1 #_2 3]", "[1 3]", all_ok)
  call expect_result("34b. ...even when the discarded form is a whole list: ", env, &
       "(+ 1 #_(/ 1 0) 2)", "3", all_ok)
  call expect_result("34c. ...and it doesn't need whitespace after it: ", env, &
       "#_x :kept", ":kept", all_ok)

  ! 35. Multimethods: defmulti builds a real clojure.lang.MultiFn,
  ! defmethod mutates its table in place, dispatch falls back to
  ! :default. No hierarchy (isa?) dispatch yet -- see apply_multifn.
  call expect_result("35a. dispatches on the dispatch fn's value: ", env, &
       "(do (defmulti shape-area :shape)" // &
       "    (defmethod shape-area :square [s] (* (:side s) (:side s)))" // &
       "    (shape-area {:shape :square :side 4}))", "16", all_ok)
  call expect_result("35b. a later defmethod is seen by the same multifn: ", env, &
       "(do (defmethod shape-area :line [s] 0) (shape-area {:shape :line}))", "0", all_ok)
  call expect_result("35c. :default catches everything unmatched: ", env, &
       "(do (defmethod shape-area :default [s] :dunno) (shape-area {:shape :blob}))", ":dunno", all_ok)
  call expect_result("35d. methods exposes the table, remove-method prunes it: ", env, &
       "(do (remove-method shape-area :line)" // &
       "    (contains? (methods shape-area) :line))", "false", all_ok)
  call expect_result("35e. no matching method and no :default is an error: ", env, &
       "(do (defmulti no-default (fn [x] x))" // &
       "    (try (no-default 1) (catch Throwable e (str e))))", &
       '"No method in multimethod for dispatch value: 1"', all_ok)

  ! 36. core.clj's own printing stack, end to end: pr-str goes through
  ! with-out-str -> a StringWriter bound to *out* -> pr -> pr-on ->
  ! the print-method multimethod. Every link has to work for any of it
  ! to (see eval_core_bootstrap's :default method).
  call expect_result("36a. pr-str is readable, space-separated: ", env, &
       '(pr-str [1 "x" :k])', '"[1 \"x\" :k]"', all_ok)
  call expect_result("36b. print-str is the display form instead: ", env, &
       '(print-str "x" \y)', '"x y"', all_ok)
  call expect_result("36c. with-out-str captures what's written to *out*: ", env, &
       '(with-out-str (pr :a) (pr :b))', '":a:b"', all_ok)
  call expect_result("36d. a later defmethod overrides the default for one type: ", env, &
       '(do (defmethod print-method clojure.lang.Keyword [x w] (. w append "K"))' // &
       '    (let [out (pr-str :anything)]' // &
       '      (remove-method print-method clojure.lang.Keyword)' // & ! put it back, see 25g
       '      out))', '"K"', all_ok)
  call expect_result("36d'. ...and removing it falls back to the default again: ", env, &
       '(pr-str :anything)', '":anything"', all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL EVAL CHECKS PASSED"
  else
     print *, ""
     print *, "EVAL CHECKS FAILED"
     stop 1
  end if

contains

  subroutine expect_result(label, env, source, expected, ok)
    character(len=*), intent(in) :: label, source, expected
    type(env_ref), intent(in) :: env
    logical, intent(inout) :: ok
    type(cons_value) :: ast, val
    character(len=:), allocatable :: read_err, eval_err, got
    logical :: read_ok

    read_ok = read_str(source, ast, read_err)
    if (.not. read_ok) then
       print '(A,A,A,A)', "FAIL - ", label, "reader error: ", read_err
       ok = .false.
       return
    end if
    val = eval_top(ast, env, eval_err)
    if (len(eval_err) > 0) then
       print '(A,A,A,A)', "FAIL - ", label, "eval error: ", eval_err
       ok = .false.
       return
    end if
    got = pr_str(val)
    if (got == expected) then
       print '(A,A,A)', "ok   - ", label, got
    else
       print '(A,A,A,A,A)', "FAIL - ", label, got, "  (expected ", expected // ")"
       ok = .false.
    end if
    flush(6)
  end subroutine expect_result

  subroutine expect_error(label, env, source)
    character(len=*), intent(in) :: label, source
    type(env_ref), intent(in) :: env
    type(cons_value) :: ast, val
    character(len=:), allocatable :: read_err, eval_err
    logical :: read_ok

    read_ok = read_str(source, ast, read_err)
    if (.not. read_ok) then
       print '(A,A)', "FAIL - ", label // "(reader rejected it before eval could)"
       all_ok = .false.
       return
    end if
    val = eval_top(ast, env, eval_err)
    if (len(eval_err) > 0) then
       print '(A,A,A)', "ok   - ", label, eval_err
    else
       print '(A,A)', "FAIL - ", label // "(expected an eval error, got a value)"
       all_ok = .false.
    end if
    flush(6)
  end subroutine expect_error

end program eval_test

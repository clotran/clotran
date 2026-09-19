;; Host-level checks with core.clj loaded, run by `make test`.
;;
;; What is here is what real Clojure CANNOT answer: Fortran arrays,
;; `clotran-type`, and blocks that mix setup with assertions. Everything
;; real Clojure can answer lives in oracle.clj, where `clj` supplies the
;; expected value (scripts/oracle) and nothing is typed in by hand --
;; because 14 of the 477 hand-typed expectations that used to live here
;; turned out to be clotran's answer, not Clojure's. Before adding a
;; check here, ask whether it belongs in oracle.clj instead.
;;
;; The contract with the Makefile is the last line: this prints
;; LANGUAGE TESTS PASSED only when nothing failed, and `make test`
;; greps for it. A crash part-way through therefore fails the gate too,
;; which is the point -- a missing marker is a failure, not a pass.

(def ^:dynamic *failures* (atom 0))

(defn check [label got want]
  (if (= got want)
    (println "ok   -" label)
    (do (swap! *failures* inc)
        (println "FAIL -" label "got" (pr-str got) "want" (pr-str want)))))

;;; ---- deftype ----------------------------------------------------

(deftype Point [x y]
  Object
  (toString [this] (str "Point(" x "," y ")")))

(def p (->Point 3 4))

;; A deftype is NOT a map, and must not pretend to be one.

;;; ---- reify ------------------------------------------------------

;; The example from reify's own docstring.

;;; ---- protocols on a deftype -------------------------------------

(defprotocol Shape
  (area [s])
  (scale [s k]))

(deftype Rect [w h]
  Shape
  (area [_] (* w h))
  (scale [_ k] (Rect. (* w k) (* h k))))

(def r (->Rect 2 5))


;;; ---- letfn ------------------------------------------------------


;;; ---- defrecord --------------------------------------------------
;;
;; Each of these answered a WRONG value rather than failing, before the
;; generic operations learned to ask an instance for its own method.

(defrecord P [a b])

(def rec (->P 1 2))


;;; ---- identical? -------------------------------------------------
;;
;; Reference identity, NOT =. Sharing the = builtin made the first of
;; these true, and made a record's equiv call itself until the stack
;; ran out.


;;; ---- symbol / keyword names -------------------------------------


;;; ---- namespaces as strings --------------------------------------
;;
;; Namespace.toString is its NAME, which is what namespace-munge reads
;; and therefore what deftype builds a class name out of. Nested, it
;; keeps the print form instead, because a collection's toString prints
;; its elements.


;;; ---- sequential equality ----------------------------------------
;;
;; A lazy seq is Sequential, so it is equal to a vector of the same
;; elements. This walks element at a time rather than counting
;; first, which is what both Clojure (ASeq.equiv) and ClojureScript
;; (equiv-sequential) do, and is why the infinite cases below
;; terminate instead of realising forever.

;; Not Sequential, so not equal however the elements line up.
;; Metadata is invisible to equality, as it is in Clojure.
;; INFINITE on one side, and these must RETURN. They do because the
;; count shortcut is taken only when both sides are counted.

;;; ---- require :refer ----------------------------------------------
;;
;; `require` silently ignored :refer. load-lib guards the call with
;; (when (or use (:refer filter-opts)) ...), and filter-opts comes
;; from select-keys, which ends (with-meta ret (meta map)) -- so the
;; keyword was looked up in the metadata WRAPPER and answered nil.
;; Whole test files then died on (deftest ...) having interned
;; nothing.

(require (quote [clojure.string :refer [join]]))
(require (quote [clojure.string :refer :all]))
(require (quote [clojure.set :as st]))

;; Set equality: other must be a set, same count, every element
;; contained. A set used to fall past that to reference equality, so
;; two literals spelled the same way were not equal.
;; A collection as an ELEMENT used to match by identity, so this was
;; false. It is structural now -- see the collections-as-keys section
;; below, which is where the rest of that case lives.
;; The underlying bug, directly.

;;; ---- the core.clj tail -------------------------------------------
;;
;; None of these existed while core.clj stopped at form 708. They are
;; the last sixteen forms, and the nil-on-bad-input cases matter:
;; parse-long is written as (try (Long/valueOf s) (catch
;; NumberFormatException _ nil)), so it depends on the exception
;; having a TYPE a catch clause can name.

;; A delay runs its body ONCE, on the first deref.

;;; ---- native arrays ------------------------------------------------
;;
;; A REAL Fortran array: contiguous, column-major, declared kind, at an
;; address the collector never moves -- the one thing this host has
;; that the JVM does not, and the reason the collector is non-moving.
;;
;; In a `fortran` namespace rather than clojure.core, because these are
;; not Clojure's array functions with a different implementation: they
;; take a Fortran KIND NAME rather than a class. SEAMS.md asked for
;; fortran.* to mean exactly this.

(alias 'f 'fortran)

(def arr (f/make-array "real8" 3))
(check "array kind"    (f/array-kind arr) "real8")
(check "array length"  (f/alength arr) 3)
(check "array shape"   (f/array-shape arr) [3])
;; Zero-filled, not whatever the allocator left behind.
(check "fresh array is zeroed" (f/aget arr 1) 0.0)
(do (f/aset arr 0 1.5) (f/aset arr 2 3.25))
(check "aset then aget" [(f/aget arr 0) (f/aget arr 2)] [1.5 3.25])

;; Rank is not special-cased: subscripts are per DIMENSION and the
;; flattening is column-major, done in one place.
(def m2 (f/make-array "int4" 2 3))
(check "rank-2 shape"  (f/array-shape m2) [2 3])
;; alength is the OUTER length, not the element count: clj says
;; (alength (make-array Integer/TYPE 2 3)) is 2, because a Java [[I
;; is an array of 2 rows. Ours is one rank-2 block, so the same
;; answer comes from the first extent.
(check "rank-2 length" (f/alength m2) 2)
(do (f/aset m2 1 2 7))
(check "rank-2 aset/aget" [(f/aget m2 1 2) (f/aget m2 0 0)] [7 0])

;; Loud, not silent, on the two ways to get it wrong.
(check "out of bounds" (try (f/aget arr 9) (catch Throwable e :err)) :err)
(check "unknown kind"  (try (f/make-array "nope" 2) (catch Throwable e :err)) :err)

;; A `value` array holds clotran values, so its storage is a GC run
;; rather than a raw buffer -- otherwise the collector would free its
;; elements out from under it.
(def va (f/make-array "value" 2))
(do (f/aset va 0 :hello))
(check "value array" [(f/aget va 0) (f/aget va 1)] [:hello nil])

;;; ---- numeric literals --------------------------------------------
;;
;; Clojure's reader has three patterns (LispReader.java 70-74) and
;; clotran had only "all digits" and "digits with a dot". Every value
;; below is what `clj` printed for the same literal. The two that were
;; SILENTLY WRONG rather than merely unsupported are 077, which read as
;; 77, and .5, which read as 0.5 instead of interning a symbol.
;;
;; The literals that must be REFUSED live in test/f/reader_test.f90:
;; a reader error aborts this whole file, so they cannot be asserted
;; here.

;; floatPat needs a digit BEFORE the dot, so this is a name.

;; A number Clojure reads that clotran has no TYPE for must NOT be a
;; reader error. It was, briefly, and the cost was out of all
;; proportion: clotran aborts a whole file on a reader error, so one
;; 2/3 took every form after it down, across the 12 of Clojure's 67
;; test namespaces that contain a ratio literal -- 766 passing
;; assertions became 223, control.clj alone losing 153.
;;
;; These two used to assert that 42N and 1.5M read as SYMBOLS,
;; which is what clotran did and what stood as the falsification.
;; They are numbers now -- see the N and M suffixes further down --
;; so what is left to guard is only that neither RAISES, since a
;; reader error here stops this whole file loading and takes the
;; gate red.

;;; ---- arithmetic ---------------------------------------------------
;;
;; Every expected value here is what `clj` printed for the same form.
;; The bugs these caught were not subtle: +, -, * and quot/rem all read
;; the integer field only, so a real operand contributed ZERO --
;; (* 2.0 3) answered 0, (quot 7.0 2) answered 0. `/` and inc/dec were
;; always right, which is what made it look fine in passing.
;;
;; The lesson for the next function: test VALUES against clj, not just
;; that a form is accepted. The reader work before this checked 29
;; literals and never once checked that arithmetic on them was right.

;; Contagion: one double makes the whole result a double.
;; One argument goes through (cast Number x), a host member that was
;; missing entirely -- (+ 1.5) failed with "no such member".

;; / is the one that already handled reals. (/ 1 0) throws but
;; (/ 1.0 0) is ##Inf -- they are not the same rule.
;; quot and rem DO throw on a zero divisor, doubles included.

;; = is Object.equals, == is numeric VALUE. They disagree here, and
;; clotran answered = for both.

;;; ---- struct maps ---------------------------------------------------
;;
;; A struct map IS a map. PersistentStructMap on the JVM is a storage
;; optimisation -- one shared key basis plus a flat value array, so N
;; instances do not each carry their keys -- and nothing about its
;; behaviour differs. So clotran's structs are its maps, and the basis
;; is a vector of the keys.
;;
;; This is not a curiosity: clojure/pprint.clj uses defstruct, and
;; clojure.test-clojure.reflect does (:use clojure.pprint), so without
;; it neither loads. Every value below is what `clj` printed.

(defstruct point :x :y)
;; An unsupplied basis key is PRESENT and nil, not absent.
;; ...and a key outside the basis is allowed.

;; Keyword-argument destructuring reaches two host members nothing else
;; did -- PersistentArrayMap/EMPTY and createAsIfByAssoc. EMPTY was
;; missing outright; createAsIfByAssoc was wired to hash-map, which
;; takes its keys and values as separate arguments where this takes one
;; collection of them, so it made a map OF the collection.

;;; ---- print-method finds its host type ------------------------------
;;
;; Three tables have to spell a type the same way: type_name, which
;; names the value; host_super, which maps that name to the host
;; classes a method may be registered on; and the class literal in
;; (defmethod print-method C ...), which is the key the method lands
;; under. Where they disagreed, print-method found nothing, fell to
;; :default, and reached print-simple -- which does not quote.
;;
;; Two disagreements, both one word:
;;   OBJ_SEQ had NO name at all and answered "object"
;;   host_super said "lazy" where type_name says "lazy-seq"
;;   host_super said "java.lang.Character" but a class literal
;;     strips that prefix, so the method key is :Character
;;
;; Nothing about the printer itself was wrong, which is why the values
;; were right the whole time and only the display was not.

;; A seq view now has a type at all. The NAME is clotran's own --
;; clj answers clojure.lang.PersistentVector$ChunkedSeq here, since
;; clotran's classes are its tags -- but it has to be the name
;; is_instance already expected, or the two disagree about one value.

;; Characters: the method that knows \\newline never ran, so a
;; newline character printed as an actual newline.
;; str is the unreadable one, and still is.

;;; ---- sort, and compare underneath it ------------------------------
;;
;; `sort` is (let [a (to-array coll)] (. java.util.Arrays (sort a cmp))
;; (seq a)) -- so it needed four things clotran did not have: a real
;; mutable array from to-array, arrays that seq, Arrays/sort itself,
;; and a `compare` that works on more than numbers.
;;
;; That last one mattered most: compare answered 0 for anything
;; non-numeric, so (sort ["b" "a"]) would have come back in its
;; original order and reported no error at all.
;;
;; Compared as VALUES rather than printed text: a seq of strings still
;; prints unreadably, which is a separate print-method bug.

;; A vector compares by COUNT first, then element by element.

;; A comparator that answers a BOOLEAN is a predicate -- AFunction
;; treats true as "less" -- which is what makes (sort > coll) work.
;; Clojure promises stability: equal elements keep their order.
;; Big enough to exercise the merge rather than the base case.
;; Built with (range) descending rather than (reverse ...): an
;; earlier test in this file does (require [clojure.string :refer
;; :all]), which shadows core reverse with the StringBuilder one.

;; to-array now answers a REAL array, and an array seqs as its
;; elements -- both needed by sort, and both wrong before.

;;; ---- collections as keys -------------------------------------------
;;
;; A collection used to hash and compare by its POOL SLOT, so an equal
;; key built somewhere else missed. `=` was structural all along, which
;; is what made it confusing: the value compared equal and the lookup
;; still failed.
;;
;; Hash and equality have to agree exactly -- a structural hash with an
;; identity equality puts one key in a trie twice -- so both are
;; installed together through gc_set_coll_ops, against deep_equal,
;; which is the equality `=` already used.

;; Entry order must not matter: two equal maps may hand back their
;; entries differently, so their hash is a sum rather than a fold.
;; A list and a vector of the same elements are equal, so they must
;; hash alike and be interchangeable as keys.
;; case* buckets by hash, so it was failing for the same reason.
;; ...and things that are NOT equal must still miss.

;;; ---- 64-bit integers -----------------------------------------------
;;
;; Clojure's default integer is `long`, and clotran's was Fortran's
;; default `integer` -- 32 bits. A literal past 2^31 was truncated on
;; the way in and nothing said so: 9999999999 read back as 1410065407,
;; and 2147483648 as -2147483648. The real beside it in gc_value had
;; been widened to real(8) years earlier on exactly this argument.
;;
;; Width has to hold all the way through: the literal is accumulated
;; digit by digit in the reader, stored in the value, and summed in
;; the accumulator. A 32-bit link anywhere truncates, so each of these
;; exercises a different one.

;; The radix forms share the reader's accumulator.
;; Equal values must still hash equal now that the hash folds 64 bits
;; into 32 -- a map keyed on a large integer finds it again.
;; case* buckets integer keys by a 32-bit hash, and ival_of still
;; narrows to build it. That is safe only because the bucket is
;; followed by a real equality check -- these pair each value with the
;; 32-bit truncation it used to collapse to, so a narrowing that
;; reached the comparison would pick the wrong branch.

;;; ---- ratios --------------------------------------------------------
;;
;; Exact rational arithmetic -- the thing (/ 1 3) needs to stop being
;; 0.3333333333. Every value below is what `clj` printed.
;;
;; A ratio is an IMMEDIATE here: numerator in the int field,
;; denominator in the field a heap reference would use, so it costs no
;; allocation and the collector never sees one. It is always in normal
;; form, which is what lets equality compare the two fields directly.

;; Normalized on construction: reduced, sign on the numerator, and
;; never denominator 1 -- Clojure collapses that to an integer.

;; Contagion is double > ratio > integer.

;; = is by type, == is by value -- and 2/1 never exists to be compared.


;; Everything else that takes a number has to know about the third
;; kind too. Each of these was wrong once: inc/dec dropped a ratio to
;; a double, quot/rem read it as its numerator alone, and int handed
;; it straight back unconverted.

;;; ---- Clojure's OWN array API ------------------------------------
;;
;; Not f/make-array: clojure.core's make-array/aget/aset/alength,
;; running unmodified over the Fortran backing. They are written
;; against java.lang.reflect.Array and clojure.lang.RT, so making
;; those work is what lets core.clj's array code run rather than be
;; shadowed. Every expected value below is what `clj` printed for
;; the same forms.
;;
;; aset-int, not aset: on a primitive array the JVM's Array/set
;; refuses a boxed Long, so real Clojure throws here too.

(def cm (make-array Integer/TYPE 2 3))
(do (aset-int cm 0 0 10) (aset-int cm 0 1 11) (aset-int cm 0 2 12)
    (aset-int cm 1 0 20) (aset-int cm 1 1 21) (aset-int cm 1 2 22))
;; The OUTER length -- 2 rows -- not 6 elements.

;; core.clj's aget is ([array idx & idxs] (apply aget (aget array idx) idxs)),
;; so (aget cm 0) MUST hand back something that is itself an array.
(def crow (aget cm 0))
;; and it is a VIEW, not a copy -- writing through it is visible in
;; the parent. This is the assertion that fails if slices ever start
;; copying.
(do (aset-int crow 1 999))

;; aclone takes the shape of the VIEW, not of the buffer behind it,
;; and shares nothing with it afterwards.
(def cclone (aclone crow))
(do (aset-int cclone 0 -1))

;; An Object array is the `value` kind: it holds clotran values, so
;; plain aset works and a fresh slot reads nil, not 0.
(def cobj (make-array Object 2))
(do (aset cobj 0 :hello))

(def cdbl (make-array Double/TYPE 2))
(do (aset-double cdbl 1 2.5))

;;; ---- printing a function -----------------------------------------
;;
;; (prn (fn [x] x)) used to SEGFAULT. print-method's :default is
;;   (if (instance? IObj o) (print-method (vary-meta o ...) w)
;;                          (print-simple o w))
;; and clotran claimed a closure was IObj while having no
;; print-method dispatch could reach -- so :default called itself on
;; the same object until the stack ran out. DEVIATIONS 23.

;; A vector really does hold anything, which is the thing that
;; turned this up.
;; with-meta on a function still works -- it does not consult the
;; instance? answer that changed.


;;; ---- macroexpand-1 and special-symbol? ---------------------------
;; Compiler.macroexpand1 is ONE step and does not descend, which is
;; what makes it different from the analysis pass clotran already
;; had. Every expectation below was run through `clj` first.

;; macroexpand loops to a fixed point but still does not descend --
;; the inner `when` survives.

;; Clojure's list, 24 entries -- not clotran's own special forms.


;;; ---- #_ discard ------------------------------------------------
;; #_ is a kind of WHITESPACE, not a form that reads as nothing --
;; which only shows at the end of a collection, where there is no
;; following form to pair it with. Values checked against `clj`.



;;; ---- the quote is not a delimiter --------------------------------
;; isTerminatingMacro excludes #, % and ' -- so a prime suffix is part
;; of the name, the way ss' and x' are written in Clojure's own suite.



;;; ---- reader metadata --------------------------------------------
;; Checked against `clj` by KEY, not by whole map: Clojure's reader
;; also attaches :line and :column, which clotran does not track.

;; A VECTOR is metadata too -- ^[long] is 1.12's param-tags.
(check "^[long] is param-tags"  (:param-tags (meta (quote ^[long] (x)))) '[long])


;;; ---- empty ------------------------------------------------------
;; core.clj's `empty` is (.empty coll) behind an instance? guard, so
;; the answer keeps the collection's CATEGORY and a non-collection
;; answers nil rather than erroring. All checked against `clj`.



;;; ---- swap-vals!, reset-vals!, and the multimethod table ----------
;; All of these are core.clj reaching for a host member it declares in
;; its own type hints. Values from `clj`.


(defmulti ltest-area :shape)
(defmethod ltest-area :square [s] (* (:side s) (:side s)))
(defmethod ltest-area :circle [s] 3)
(defmethod ltest-area :default [s] :none)

;; get-method answers what WOULD apply, so an unregistered value finds
;; the default rather than nil.
;; preferMethod records nothing here (DEVIATIONS 8), so the table is
;; empty rather than absent.


;;; ---- java.lang.Math ---------------------------------------------
;; clojure/math.clj is a thin wrapper over java.lang.Math, so the whole
;; namespace rests on these. Every expectation below is `clj`'s answer,
;; bit for bit -- the awkward ones (ulp, next-up, IEEE-remainder,
;; get-exponent) come out of Fortran's spacing/nearest/exponent
;; intrinsics rather than a libm binding.
;;
;; Math permits up to 1 ulp of error, and exp is where clotran and the
;; JVM use it: (m/exp 1) differs in the last bit. Nothing here asserts
;; on that one.

(require (quote clojure.math))



;; rint rounds HALF TO EVEN, which neither truncation nor
;; round-half-away gives.

;; expm1 and log1p keep their digits near zero, where exp(x)-1 would
;; lose all of them.

;; The *Exact family throws where ordinary arithmetic wraps.
;; Floor division, not truncation.

;; Math/abs is overloaded on the JVM: a long stays a long.


;;; ---- format -----------------------------------------------------
;; core.clj's `format` is (String/format fmt (to-array args)), so this
;; is java.util.Formatter -- the subset Clojure's own source and suite
;; actually write. Every line checked against `clj`.

;; %b is false only for nil and false -- 0 is true.
;; String.valueOf(null) is "null", not Clojure's nil.
;; core_print's own use of it.


;;; ---- range over more than longs ---------------------------------
;; core.clj picks between LongRange/create and Range/create on
;; (int? x); clotran has one builtin behind both, and it used to read
;; the integer field regardless -- so every bound of a double range
;; read as 0 and it yielded zeros forever. Values from `clj`.

;; A ratio step stays exact rather than becoming a double.


;;; ---- long lazy sequences ----------------------------------------
;; These are GC tests wearing Clojure clothes. Each of them realises
;; far more cells than the heap holds at once, so the collector runs
;; many times mid-walk; every one of them answered a SMALLER, WRONG
;; number before the roots in range_cell, iterate_cell and the static
;; call path were fixed.
;;
;; 8000 is chosen, not more: it is past the point where the first
;; failure appeared (about 5800), and these are a GATE -- the whole
;; file runs under both compilers on every commit, and clotran walks
;; a lazy cell in milliseconds, not microseconds. A bigger number
;; would buy no more confidence and cost minutes.



;;; ---- printing doubles -------------------------------------------
;; Double.toString: the SHORTEST decimal that reads back as the same
;; double, plain while 1e-3 <= |d| < 1e7 and scientific outside that.
;; The old printer wrote ten fixed decimals, so 0.479425538604203 came
;; out as 0.4794255386 -- a different double -- and Double/MAX_VALUE
;; overran the buffer outright. Every line below is `clj`'s output.

;; The round trip is the point: these need all their digits.
;; The plain/scientific boundary is 1e-3 and 1e7, not Fortran's.

;;; ---- read-string ------------------------------------------------
;; (RT/readString s) reads ONE form and ignores what follows.


;;; ---- the boxed number classes -----------------------------------
;; Long/MAX_VALUE and its neighbours, and Double.compare -- the TOTAL
;; order, which ranks -0.0 below 0.0 and NaN above everything, neither
;; of which < can say. Values from `clj`.

;; NaN is greater than everything, and equal to itself.


;;; ---- clojure.string's host members -------------------------------
;; clojure.string is written entirely against java.util.regex's
;; Pattern and Matcher plus StringBuilder, so none of split, replace
;; or reverse worked without them. Every expectation is `clj`'s.

(require (quote [clojure.string :as ltstr]))

;; A positive limit caps the parts and the last keeps the rest unsplit.
;; No limit drops trailing empties; -1 keeps them.


;; $1 and $2 name groups -- the one place a replacement is not literal.


;;; ---- a delay that threw -----------------------------------------
;; Delay.deref catches the throwable, drops the thunk and rethrows the
;; SAME object on every later deref -- so the body runs once whether it
;; returned or threw. Values from `clj`.

(let [n (atom 0)
      d (delay (swap! n inc) (throw (Exception. "broken")))
      tc (fn [] (try @d (catch Exception e e)))
      r1 (tc)]
  (check "a delay's exception is an exception" (instance? Exception r1) true)
  (check "the same exception comes back"       (identical? r1 (tc)) true)
  (check "the body ran once"                   @n 1)
  (check "the message survives"                (.getMessage r1) "broken")
  (check "a thrown delay is realized"          (realized? d) true))
(let [ok (delay 42)]
  (check "an ordinary delay"  [@ok @ok (realized? ok)] [42 42 true]))


;;; ---- (var x) resolves where the code was written -----------------
;; resolve_var reads the defining namespace out of the enclosing
;; frame, and the `var` special form was handing it the FORM instead --
;; so a (binding [x ...]) inside one namespace, called from another,
;; looked x up in the CALLER's namespace and failed. clojure.test's own
;; (binding [*report-counters* ...]) is exactly that, which is why
;; run-tests reported nothing from a foreign namespace.

(ns lt.other)
(def ^:dynamic *lt-counter* :unbound)
(defn lt-with [f] (binding [*lt-counter* 7] (f)))
(defn lt-peek [] *lt-counter*)
(in-ns 'user)



;;; ---- a set answers a lookup --------------------------------------
;; A set's contents live one slot down, and get/keyword lookup never
;; unwrapped them -- so (get #{:at} :at) and (:at #{:at}) both answered
;; nil where Clojure answers :at. cl_format.clj asks exactly that of
;; its allowed-flags set for every directive it compiles, so every flag
;; looked illegal and clojure.pprint would not load at all.


;;; ---- indexOf takes a character CODE ------------------------------
;; String.indexOf is overloaded on (int ch) as well as (String), and
;; cl_format.clj writes (.indexOf s (int \~)) to find its directives.
;; Searching for the TEXT "126" never found one, so every format string
;; compiled to itself and cl-format returned the format unchanged.



;;; ---- arrays, and the exceptions that ask for one -----------------
;; .getStackTrace answered an empty VECTOR, and Throwable->map asks
;; (alength st) straight after -- so every printed exception, and every
;; thrown-with-cause-msg? in Clojure's suite, died on "alength: not an
;; array" rather than on anything real. There is no stack trace to
;; report here; there is an empty array.

;; The component type is read and discarded -- there are no primitive
;; component types here (DEVIATIONS 24).

;;; ---- ExceptionInfo -----------------------------------------------
;; It does not end in "Exception", so it was not recognised as a
;; throwable class at all -- and a catch naming it in full could not
;; match a throw that named it short.



;;; ---- proxy -------------------------------------------------------
;; `proxy` is a MACRO in Clojure, in core_proxy.clj, which is not
;; vendored -- it is written against the class loader. clojure.pprint's
;; writers are proxies, so without it the pretty printer cannot exist.
;; Here it is a special form built on reify's machinery, with the two
;; differences proxy has: `this` is implicit, and arities nest inside
;; one method form.
;;
;; Only the first three are `clj`'s answers. The rest declare methods
;; the superclass does not, which real Clojure REJECTS -- there is no
;; class to check against here, so clotran accepts them. DEVIATIONS 28.


;; Several arities inside ONE method form, which reify writes as
;; several forms.
;; `this` is bound without being named.

;;; ---- `..` is a macro, not a member access ------------------------
;; Clojure never has to say so: Compiler.macroexpand1 asks isMacro
;; before it reaches the dot sugar, and `..` is a macro. clotran asks
;; the other way round -- equivalent for every other name, since .foo
;; is never a macro, and wrong for exactly this one, where
;; (.. a getClass isArray) read as the member "." on a.



;;; ---- a vector is associative by index ----------------------------
;; All four of these came out of one namespace, clojure.data, which is
;; written entirely against them: assoc on a vector answered NIL,
;; get and contains? by index answered nothing, and conj of nil onto a
;; map added a nil entry. Values from `clj`.

;; An index equal to the count APPENDS -- the one place assoc grows a
;; vector. Past that it throws.

;; .contains on a String is still substring containment -- the two
;; methods share a name and the argument tells them apart.

;; APersistentMap.cons walks (seq o), and the seq of nil is nil, so a
;; map comes back unchanged. (merge m nil) is (conj m nil).

;;; ---- protocols see the host supertypes ---------------------------
;; core.clj's `supers` is built from .getInterfaces, and answering an
;; empty one sent EVERY protocol dispatch to its (impl Object)
;; fallback. clojure.data's equality-partition called a map an :atom
;; even though java.util.Map was in the impls map all along.

(require (quote [clojure.data :as ltdata]))



;;; ---- a bad arity is an ArityException -----------------------------
;; clotran said "no matching arity" through its internal error map,
;; which no (catch SomeClass e) could match and which did not say how
;; many arguments arrived or to whom. Clojure's wording, class and
;; catchability, all checked against `clj`.

(defn ltf0 [] 0)
(defn ltf1 [a] a)
(defn ltfm ([a] 1) ([a b] 2))

;; ArityException extends IllegalArgumentException, which Clojure's own
;; suite relies on.


;;; ---- agents, validators and latches ------------------------------
;; core.clj's `agent` sets an error mode on its very first line, so
;; nothing about agents worked at all. Dispatch here is SYNCHRONOUS --
;; the action runs before send returns -- which is DEVIATIONS 29; the
;; error bookkeeping around it is Clojure's. Values from `clj`.

(let [a (agent 1)]
  (check "a new agent fails by default" (error-mode a) :fail)
  (send a inc) (await a)
  (check "send"                @a 2)
  (send a + 10) (await a)
  (check "send with arguments" @a 12)
  (send a (fn [x & ys] (apply + x ys)) 1 2 3) (await a)
  (check "send with several"   @a 18))

(let [b (agent 1)]
  (send b (fn [x] (throw (Exception. "boom"))))
  (check "a failed agent keeps its value" @b 1)
  (check "and records the error"          (.getMessage (agent-error b)) "boom")
  (check "and refuses more work"
         (try (send b inc) :no (catch Throwable e :refused)) :refused)
  (restart-agent b 5)
  (check "restart clears it"   [@b (agent-error b)] [5 nil])
  (send b inc) (await b)
  (check "and it works again"  @b 6))

;; An error handler makes the default mode :continue, so the agent
;; carries on as if nothing happened.
(let [c (agent 1 :error-handler (fn [ag e] nil))]
  (check "a handler means continue" (error-mode c) :continue)
  (send c (fn [x] (throw (Exception. "oops"))))
  (check "a continuing agent is not failed" [@c (agent-error c)] [1 nil])
  (send c inc) (await c)
  (check "and takes more work"      @c 2))


;; A latch is a counter when there is one thread.

;;; ---- set-validator! ----------------------------------------------
;; Every reference type takes one, and a refusal leaves the reference
;; alone rather than writing a bad value.

(let [v (atom 1)]
  (set-validator! v pos?)
  (check "the validator is remembered" (nil? (get-validator v)) false)
  (check "reset! is refused"  (try (reset! v -1) :no (catch IllegalStateException e :invalid)) :invalid)
  (check "and the value stands" @v 1)
  (check "swap! is refused"   (try (swap! v - 5) :no (catch IllegalStateException e :invalid)) :invalid)
  (check "still stands"       @v 1)
  (check "a good value goes through" (do (reset! v 7) @v) 7))
;; Clojure validates the CURRENT value on the way in.


;;; ---- PrintWriter, and RT/print -----------------------------------
;; A PrintWriter over a writer IS that writer here: Java's wraps to add
;; buffering and the print methods, and clotran's writers already take
;; text and hold it. What has to hold is that writing to the wrapper is
;; visible through the wrapped one, which sharing gives directly.
;; Clojure's own test helper builds *err* this way.

;; (RT/print x w) is `pr` underneath -- the readable form, written to a
;; writer rather than returned.


;;; ---- clojure.core is already loaded ------------------------------
;; (require 'clojure.core) reached clotran's loader and re-read the
;; whole file, re-evaluating every definition against a namespace that
;; already had them -- and died partway with an arity error. Clojure
;; answers nil and changes nothing. Clojure's own test helper opens
;; every temporary namespace with (clojure.core/use 'clojure.core), so
;; nothing written through eval-in-temp-ns ran at all.



;;; ---- the N and M suffixes ----------------------------------------
;; Clojure reads 1N as a BigInt and 1M as a BigDecimal. clotran has
;; neither and used to read both as SYMBOLS, so (cond 0M :a true :b)
;; was "unable to resolve symbol" rather than :a.
;;
;; Each drops to the nearest thing clotran has, chosen by what `=` then
;; says: 1N is an integer because (= 1N 1) is true in Clojure, and 1M is
;; a DOUBLE because (= 1M 1) is false there -- reading 45M as the
;; integer 45 would have made it true. DEVIATIONS 30.

;; A letter that is not a suffix still makes a symbol, and a token that
;; is neither is still a reader error.


;;; ---- the boxing constructors -------------------------------------
;; (Long. 1) is 1 and (String. "x") is "x": on the JVM these wrap a
;; primitive in an object, and there is no unboxed number here to wrap.
;; What they still have to do is CONVERT, because (Long. "12") parses.
;; Every line below is `clj`'s answer.



;;; ---- the host supertype chain ------------------------------------
;; host_super feeds multimethod dispatch, and it was picked by index
;; with two silent holes: entries keyed "float" and "bool" where
;; type_name says "double" and "boolean" -- so a double and a boolean
;; had NO supertypes -- and an Object fallback at index 4 that only a
;; type with exactly three supertypes ever reached. print-dup on a
;; double was "No method in multimethod for dispatch value: :double".
;;
;; Order is specific-to-general, because dispatch takes the first
;; match: print-dup has a method on Long and another on Number, and
;; only Long's prints 1 rather than #=(java.lang.Long. "1").
;; All checked against `clj`.

;; core_print registers print-dup on PersistentVector and
;; PersistentHashSet by NAME, and only those print plainly.

;; print-method still finds what it found before.
;; Double's own predicates, which print-method asks of it.


;;; ---- hash follows equality ---------------------------------------
;; Clojure guarantees (= a b) implies (= (hash a) (hash b)). Three
;; things broke it, and `case` is where they showed, because case
;; dispatches on the hash:
;;
;;   - the cons walk stopped on KIND, and the empty tail is itself a
;;     cons, so every list hashed one extra nil -- (hash '(1)) came out
;;     equal to (hash [1 2]).
;;   - a seq VIEW was not structural at all, so it hashed by identity
;;     while comparing equal to its vector.
;;   - the tag was XORed straight onto the value, and the tags are
;;     small integers, so (hash 2) was 0 -- the same as (hash nil),
;;     because GCT_INT is 2.


;;; ---- case ---------------------------------------------------------
;; case compiles to a lookup keyed on the hash, with a shift and mask
;; when the constants have to be squeezed together. The shift is
;; ARITHMETIC in core.clj -- (bit-shift-right x shift) propagates the
;; sign -- and Fortran's ishft fills with zeros, so a negative hash
;; landed in a different bucket at runtime than the macro put it in.
;; A case small enough to need no shift hid it completely.

(let [two 2
      f #(case %
           1 :number
           "foo" :string
           \a :char
           pow :symbol
           :zap :keyword
           (2 \b "bar") :one-of-many
           [1 2] :sequential-thing
           {:a 2} :map
           {:r 2 :d 2} :droid
           #{2 3 4 5} :set
           [1 [[[2]]]] :deeply-nested
           nil :nil
           :default)]
  (check "case over many kinds of constant"
         (mapv f [1 "foo" \a :zap 'pow 2 \b "bar" [1 2] (list 1 2) [1 two]
                  {:a 2} #{2 3 4 5} #{2 3 4 5 6} {:r 2 :d 2} [1 [[[two]]]] nil 42])
         [:number :string :char :keyword :symbol :one-of-many :one-of-many :one-of-many
          :sequential-thing :sequential-thing :sequential-thing :map :set :default
          :droid :deeply-nested :nil :default]))

;;; ---- report -----------------------------------------------------


;;; ---- dgemm: the first Fortran routine called from clotran -------
;;
;; A = [[1 2 3] [4 5 6]], B = [[7 8] [9 10] [11 12]]; A x B is
;; [[58 64] [139 154]]. Checked against the same product computed in
;; Clojure over aget, and then against the numbers.
(alias 'fb 'fortran)
(def dgA (fb/make-array "real8" 2 3))
(def dgB (fb/make-array "real8" 3 2))
(dotimes [i 2] (dotimes [j 3] (fb/aset dgA i j (double (+ 1 j (* 3 i))))))
(dotimes [i 3] (dotimes [j 2] (fb/aset dgB i j (double (+ 7 j (* 2 i))))))
(def dgC (fb/dgemm dgA dgB))
(check "dgemm answers a real8 array" (fb/array-kind dgC) "real8")
(check "dgemm answers m x n" (fb/array-shape dgC) [2 2])
(check "dgemm C = A x B"
       (vec (for [i (range 2) j (range 2)] (fb/aget dgC i j)))
       (vec (for [i (range 2) j (range 2)]
              (reduce + (for [l (range 3)] (* (fb/aget dgA i l) (fb/aget dgB l j)))))))
(check "dgemm C = A x B, the numbers" (vec (for [i (range 2) j (range 2)] (fb/aget dgC i j))) [58.0 64.0 139.0 154.0])
(check "dgemm refuses mismatched shapes"
       (try (fb/dgemm dgA dgA) (catch Throwable t :refused)) :refused)

;;; ---- stack traces --------------------------------------------------
;;
;; A thrown Throwable carries the call stack it was thrown from, as
;; elements answering the four StackTraceElement questions
;; clojure.stacktrace and clojure.test ask. Host check: the frame names
;; are clotran's, so real Clojure cannot answer these.
(defn st-thrower [] (throw (ex-info "boom" {})))
(defn st-caller [] (st-thrower))
(def st-trace (try (st-caller) (catch Throwable t (.getStackTrace t))))
;; As on the JVM, the top frame is ex-info's own: the exception is
;; constructed inside it.
(check "a trace has a frame per call" (>= (alength st-trace) 3) true)
(check "the top frame is ex-info" (.getClassName (aget st-trace 0)) "clojure.core/ex-info")
(check "then the thrower" (.endsWith (.getClassName (aget st-trace 1)) "st-thrower") true)
(check "then the caller" (.endsWith (.getClassName (aget st-trace 2)) "st-caller") true)
(check "a frame's method is invoke" (.getMethodName (aget st-trace 0)) "invoke")
(check "a frame names its file" (boolean (re-find #"language_test" (str (.getFileName (aget st-trace 1))))) true)
(check "a frame has a line" (pos? (.getLineNumber (aget st-trace 1))) true)

(println "")
(if (zero? @*failures*)
  (println "LANGUAGE TESTS PASSED")
  (println "LANGUAGE TESTS FAILED:" @*failures*))

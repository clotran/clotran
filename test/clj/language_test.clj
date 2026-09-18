;; Language-level tests, run by `make test` against a clotran that has
;; already loaded core.clj.
;;
;; WHY THIS FILE EXISTS. test/f is the gate, and it is written against
;; the BASE ENVIRONMENT -- no core.clj, so no deftype, no defrecord, no
;; protocols, none of the macros. That is the right place to test a
;; special form, and it cannot reach anything built on top of one.
;;
;; So the behaviour that depends on core.clj had no gate at all: records
;; were checked by hand against `clj` and nothing would have caught a
;; regression. Every expectation here was taken from real Clojure, not
;; from what clotran happened to print.
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

(check "deftype field read" (.-x p) 3)
(check "deftype method sees fields as names" (.toString p) "Point(3,4)")
(check "deftype instance? by short name" (instance? Point p) true)
;; A deftype is NOT a map, and must not pretend to be one.
(check "deftype is not map-like" (:x p) nil)

;;; ---- reify ------------------------------------------------------

;; The example from reify's own docstring.
(check "reify closes over its scope"
       (str (let [f "foo"] (reify Object (toString [this] f))))
       "foo")

;;; ---- protocols on a deftype -------------------------------------

(defprotocol Shape
  (area [s])
  (scale [s k]))

(deftype Rect [w h]
  Shape
  (area [_] (* w h))
  (scale [_ k] (Rect. (* w k) (* h k))))

(def r (->Rect 2 5))

(check "protocol method on a deftype" (area r) 10)
(check "a method can construct its own type" (area (scale r 3)) 90)
(check "satisfies? a protocol it declares" (satisfies? Shape r) true)
(check "satisfies? one it does not" (satisfies? Shape p) false)

;;; ---- letfn ------------------------------------------------------

(check "letfn mutual recursion"
       (letfn [(ev? [n] (if (zero? n) true (od? (dec n))))
               (od? [n] (if (zero? n) false (ev? (dec n))))]
         [(ev? 10) (od? 10)])
       [true false])
(check "letfn self recursion"
       (letfn [(f [n] (if (< n 2) 1 (* n (f (dec n)))))] (f 5))
       120)
(check "map-indexed" (map-indexed vector [:a :b :c]) [[0 :a] [1 :b] [2 :c]])

;;; ---- defrecord --------------------------------------------------
;;
;; Each of these answered a WRONG value rather than failing, before the
;; generic operations learned to ask an instance for its own method.

(defrecord P [a b])

(def rec (->P 1 2))

(check "record keyword lookup"      (:a rec) 1)
(check "record get"                 (get rec :a) 1)
(check "record get not-found"       (get rec :nope :none) :none)
(check "record count"               (count rec) 2)
(check "record seq"                 (seq rec) [[:a 1] [:b 2]])
(check "record keys"                (keys rec) [:a :b])
(check "record vals"                (vals rec) [1 2])
(check "record equality by value"   (= (->P 1 2) (->P 1 2)) true)
(check "record inequality"          (= (->P 1 2) (->P 1 9)) false)
(check "record?"                    (record? rec) true)
(check "record assoc keeps type"    (:a (assoc rec :a 9)) 9)
(check "record assoc a new key"     (:c (assoc rec :c 3)) 3)
(check "record contains?"           (contains? rec :a) true)
(check "map-> factory"              (:b (map->P {:a 1 :b 2})) 2)
(check "map-> extra keys"           (:z (map->P {:a 1 :b 2 :z 9})) 9)

;;; ---- identical? -------------------------------------------------
;;
;; Reference identity, NOT =. Sharing the = builtin made the first of
;; these true, and made a record's equiv call itself until the stack
;; ran out.

(check "identical? on equal collections" (identical? [1] [1]) false)
(check "= on equal collections"          (= [1] [1]) true)
(check "identical? on interned keywords"  (identical? :a :a) true)
(check "identical? on the same object"   (let [v [1]] (identical? v v)) true)

;;; ---- symbol / keyword names -------------------------------------

(check "symbol keeps its qualifier" (symbol "a.b.C/create") 'a.b.C/create)
(check "namespace of that symbol"   (namespace (symbol "a.b.C/create")) "a.b.C")
(check "name of that symbol"        (name (symbol "a.b.C/create")) "create")
(check "keyword keeps its qualifier" (keyword "a/b") :a/b)

;;; ---- namespaces as strings --------------------------------------
;;
;; Namespace.toString is its NAME, which is what namespace-munge reads
;; and therefore what deftype builds a class name out of. Nested, it
;; keeps the print form instead, because a collection's toString prints
;; its elements.

(check "str of a namespace" (str (the-ns 'clojure.core)) "clojure.core")
(check "str of a namespace nested" (str [(the-ns 'clojure.core)])
       "[#<ns clojure.core>]")

;;; ---- sequential equality ----------------------------------------
;;
;; A lazy seq is Sequential, so it is equal to a vector of the same
;; elements. This walks element at a time rather than counting
;; first, which is what both Clojure (ASeq.equiv) and ClojureScript
;; (equiv-sequential) do, and is why the infinite cases below
;; terminate instead of realising forever.

(check "lazy seq = vector"     (= (map inc [0 1]) [1 2]) true)
(check "vector = lazy seq"     (= [1 2] (map inc [0 1])) true)
(check "lazy seq = lazy seq"   (= (map inc [0 1]) (map inc [0 1])) true)
(check "list = vector"         (= (list 1 2) [1 2]) true)
(check "seq of a string"       (= (seq "ab") [\a \b]) true)
(check "seq of a map"          (= (seq {:a 1}) [[:a 1]]) true)
(check "nested lazy"           (= (map vector [1] [2]) [[1 2]]) true)
(check "shorter lazy seq"      (= (map inc [0]) [1 2]) false)
(check "longer lazy seq"       (= (map inc [0 1 2]) [1 2]) false)
;; Not Sequential, so not equal however the elements line up.
(check "a set is not sequential"    (= #{1 2} [1 2]) false)
(check "a string is not sequential" (= "ab" [\a \b]) false)
(check "nil is not an empty vector" (= nil []) false)
;; Metadata is invisible to equality, as it is in Clojure.
(check "metadata does not change =" (= (with-meta [1 2] {:a 1}) [1 2]) true)
;; INFINITE on one side, and these must RETURN. They do because the
;; count shortcut is taken only when both sides are counted.
(check "infinite vs vector"    (= (range) [1 2]) false)
(check "infinite sharing a prefix" (= (iterate inc 1) [1 2]) false)

;;; ---- require :refer ----------------------------------------------
;;
;; `require` silently ignored :refer. load-lib guards the call with
;; (when (or use (:refer filter-opts)) ...), and filter-opts comes
;; from select-keys, which ends (with-meta ret (meta map)) -- so the
;; keyword was looked up in the metadata WRAPPER and answered nil.
;; Whole test files then died on (deftest ...) having interned
;; nothing.

(require (quote [clojure.string :refer [join]]))
(check "require :refer [sym]" (join "-" [1 2]) "1-2")
(require (quote [clojure.string :refer :all]))
(check "require :refer :all" (capitalize "ab") "Ab")
(require (quote [clojure.set :as st]))
(check "require :as still works" (st/union #{1} #{2}) #{1 2})

;; Set equality: other must be a set, same count, every element
;; contained. A set used to fall past that to reference equality, so
;; two literals spelled the same way were not equal.
(check "set = set"          (= #{1 2} #{1 2}) true)
(check "set built vs literal" (= (conj #{1} 2) #{1 2}) true)
(check "sets differing"     (= #{1} #{2}) false)
(check "sets sized apart"   (= #{1} #{1 2}) false)
(check "empty sets"         (= #{} #{}) true)
;; A collection as an ELEMENT used to match by identity, so this was
;; false. It is structural now -- see the collections-as-keys section
;; below, which is where the rest of that case lives.
(check "collection in a set" (= #{[1]} #{[1]}) true)
;; The underlying bug, directly.
(check "keyword on a map with meta" (:a (with-meta {:a 1} {:x 9})) 1)
(check "select-keys result is looked up"
       (:refer (select-keys {:refer [1] :as 2} (quote (:refer)))) [1])

;;; ---- the core.clj tail -------------------------------------------
;;
;; None of these existed while core.clj stopped at form 708. They are
;; the last sixteen forms, and the nil-on-bad-input cases matter:
;; parse-long is written as (try (Long/valueOf s) (catch
;; NumberFormatException _ nil)), so it depends on the exception
;; having a TYPE a catch clause can name.

(check "update-vals"    (update-vals {:a 1 :b 2} inc) {:a 2 :b 3})
(check "update-keys"    (update-keys {:a 1} name) {"a" 1})
(check "parse-long"     (parse-long "42") 42)
(check "parse-long nil" (parse-long "x") nil)
(check "parse-double"   (parse-double "1.5") 1.5)
(check "parse-double nil" (parse-double "x") nil)
(check "parse-boolean"  (parse-boolean "true") true)
(check "parse-boolean nil" (parse-boolean "x") nil)
(check "NaN?"           (NaN? (/ 0.0 0.0)) true)
(check "NaN? on a number" (NaN? 1.0) false)
(check "infinite?"      (infinite? (/ 1.0 0.0)) true)
(check "infinite? on a number" (infinite? 1.0) false)
;; A delay runs its body ONCE, on the first deref.
(check "delay" (let [n (atom 0)
                     d (delay (swap! n inc))]
                 [(realized? d) @d @d (realized? d) @n])
       [false 1 1 true 1])
(check "force"          (force (delay 7)) 7)
(check "force a non-delay" (force 7) 7)

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
;; The literals that must be REFUSED live in test/f/gc_reader_test.f90:
;; a reader error aborts this whole file, so they cannot be asserted
;; here.

(check "hex"            [0x1F 0X1f -0x1f] [31 31 -31])
(check "octal"          [077 +077 0] [63 63 0])
(check "radix"          [2r1011 -2r1011 36rZ 2R1011] [11 -11 35 11])
(check "exponent"       [1e3 1.5e-3 1E3] [1000.0 0.0015 1000.0])
(check "exponent forms" [1.e3 10e3 0e3] [1000.0 10000.0 0.0])
(check "plain"          [42 -42 5. 1.5] [42 -42 5.0 1.5])
;; floatPat needs a digit BEFORE the dot, so this is a name.
(check ".5 is a symbol" (symbol? (quote .5)) true)

;; A number Clojure reads that clotran has no TYPE for must NOT be a
;; reader error. It was, briefly, and the cost was out of all
;; proportion: clotran aborts a whole file on a reader error, so one
;; 2/3 took every form after it down, across the 12 of Clojure's 67
;; test namespaces that contain a ratio literal -- 766 passing
;; assertions became 223, control.clj alone losing 153.
;;
;; 2/3 is a real number here now, so only the suffixes are left to
;; stand as the falsification: a literal Clojure reads as a number
;; that clotran cannot type. If the reader ever raises on one again
;; this whole file stops loading and the gate goes red -- which is
;; exactly what failed to happen last time, because no test anywhere
;; contained one.
(check "an N suffix is a symbol"            (symbol? (quote 42N)) true)
(check "an M suffix is a symbol"            (symbol? (quote 1.5M)) true)

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

(check "identities"    [(+) (*) (+ 5) (* 5) (- 5)] [0 1 5 5 -5])
(check "integer"       [(+ 1 2) (- 5 2) (* 3 4) (+ 1 2 3 4) (- 10 1 2) (* 2 3 4)]
                       [3 3 12 10 7 24])
;; Contagion: one double makes the whole result a double.
(check "mixed"         [(+ 1.5 2) (* 2.0 3) (- 5.5 1)] [3.5 6.0 4.5])
(check "mixed varargs" [(+ 1 2.5 3) (* 2 3 0.5) (- 10 1.5 2)] [6.5 3.0 6.5])
;; One argument goes through (cast Number x), a host member that was
;; missing entirely -- (+ 1.5) failed with "no such member".
(check "one argument"  [(+ 1.5) (- 1.5) (* 2.0)] [1.5 -1.5 2.0])

;; / is the one that already handled reals. (/ 1 0) throws but
;; (/ 1.0 0) is ##Inf -- they are not the same rule.
(check "division"      [(/ 4 2) (/ 100 5 2) (/ 4.0 2)] [2 10 2.0])
;; quot and rem DO throw on a zero divisor, doubles included.
(check "quot rem mod"  [(quot 7 2) (rem 7 2) (mod 7 2)] [3 1 1])
(check "...negative"   [(quot -7 2) (rem -7 2) (mod -7 2)] [-3 -1 1])
(check "...on reals"   [(quot 7.0 2) (rem 7.0 2) (mod 7.0 2)] [3.0 1.0 1.0])
(check "quot by zero"  (try (quot 1 0) (catch Throwable e :err)) :err)

;; = is Object.equals, == is numeric VALUE. They disagree here, and
;; clotran answered = for both.
(check "= across types"  (= 1 1.0) false)
(check "== across types" (== 1 1.0) true)
(check "== varargs"      [(== 1 1.0 1) (== 1 2)] [true false])
(check "comparisons"   [(< 1 2.0) (> 3 2.5) (<= 2 2.0)] [true true true])
(check "min max abs"   [(min 1 2.5) (max 1 2.5) (abs -3) (abs -3.5)] [1 2.5 3 3.5])
(check "inc dec"       [(inc 1) (inc 1.5) (dec 1) (dec 1.5)] [2 2.5 0 0.5])

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
(check "struct"          (struct point 1 2) {:x 1 :y 2})
;; An unsupplied basis key is PRESENT and nil, not absent.
(check "struct partial"  (struct point 1) {:x 1 :y nil})
(check "struct-map"      (struct-map point :x 1) {:x 1 :y nil})
;; ...and a key outside the basis is allowed.
(check "struct extra"    (struct-map point :x 1 :z 9) {:x 1 :y nil :z 9})
(check "struct keys"     (vec (keys (struct point 1 2))) [:x :y])
(check "struct is a map" (map? (struct point 1 2)) true)
(check "struct assoc"    (assoc (struct point 1 2) :z 3) {:x 1 :y 2 :z 3})
(check "accessor"        ((accessor point :x) (struct point 1 2)) 1)
(check "too many vals"   (try (struct point 1 2 3) (catch Throwable e :err)) :err)
(check "not a basis key" (try (accessor point :q) (catch Throwable e :err)) :err)

;; Keyword-argument destructuring reaches two host members nothing else
;; did -- PersistentArrayMap/EMPTY and createAsIfByAssoc. EMPTY was
;; missing outright; createAsIfByAssoc was wired to hash-map, which
;; takes its keys and values as separate arguments where this takes one
;; collection of them, so it made a map OF the collection.
(check "kwargs"      ((fn [& {:keys [a b]}] [a b]) :a 1 :b 2) [1 2])
(check "kwargs map"  ((fn [& {:keys [a b]}] [a b]) {:a 1 :b 2}) [1 2])
(check "empty map"   (= {} (apply hash-map [])) true)

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

(check "seq of strings"   (pr-str (seq ["b" "a"])) "(\"b\" \"a\")")
(check "rest of strings"  (pr-str (rest ["a" "b"])) "(\"b\")")
(check "seq nests"        (pr-str (seq [["a"]])) "([\"a\"])")
(check "a lazy seq"       (pr-str (map identity ["a"])) "(\"a\")")
;; A seq view now has a type at all. The NAME is clotran's own --
;; clj answers clojure.lang.PersistentVector$ChunkedSeq here, since
;; clotran's classes are its tags -- but it has to be the name
;; is_instance already expected, or the two disagree about one value.
(check "a seq has a type" (type (seq ["a"])) :seq)

;; Characters: the method that knows \\newline never ran, so a
;; newline character printed as an actual newline.
(check "char readably"    (pr-str \a) "\\a")
(check "char in a vector" (pr-str [\a \b]) "[\\a \\b]")
(check "char in a seq"    (pr-str (seq [\a])) "(\\a)")
(check "named chars"      [(pr-str \newline) (pr-str \space) (pr-str \tab)]
                          ["\\newline" "\\space" "\\tab"])
;; str is the unreadable one, and still is.
(check "str of a char"    (str \a) "a")

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

(check "compare numbers" [(compare 1 2) (compare 2 1) (compare 1 1)] [-1 1 0])
(check "compare text"    [(compare "a" "b") (compare :a :b) (compare \a \b)] [-1 -1 -1])
(check "compare nil"     [(compare nil 1) (compare 1 nil) (compare nil nil)] [-1 1 0])
(check "compare bool"    [(compare false true) (compare true false)] [-1 1])
;; A vector compares by COUNT first, then element by element.
(check "compare vectors" [(compare [1] [2]) (compare [1 2] [1]) (compare [1 2] [1 2])] [-1 1 0])
(check "compare refuses" (try (compare 1 "a") (catch Throwable e :err)) :err)

(check "sort numbers"    (vec (sort [3 1 2])) [1 2 3])
(check "sort empty"      (vec (sort [])) [])
(check "sort a list"     (vec (sort (quote (3 1 2)))) [1 2 3])
(check "sort strings"    (vec (sort ["b" "a" "c"])) ["a" "b" "c"])
(check "sort keywords"   (vec (sort [:b :a])) [:a :b])
(check "sort vectors"    (vec (sort [[2] [1]])) [[1] [2]])
;; A comparator that answers a BOOLEAN is a predicate -- AFunction
;; treats true as "less" -- which is what makes (sort > coll) work.
(check "sort with >"     (vec (sort > [1 3 2])) [3 2 1])
(check "sort-by"         (vec (sort-by - [1 3 2])) [3 2 1])
;; Clojure promises stability: equal elements keep their order.
(check "sort is stable"  (vec (sort-by first [[1 :a] [0 :x] [1 :b] [0 :y]]))
                         [[0 :x] [0 :y] [1 :a] [1 :b]])
;; Big enough to exercise the merge rather than the base case.
;; Built with (range) descending rather than (reverse ...): an
;; earlier test in this file does (require [clojure.string :refer
;; :all]), which shadows core reverse with the StringBuilder one.
(check "sort 50"         (= (sort (range 49 -1 -1)) (range 50)) true)

;; to-array now answers a REAL array, and an array seqs as its
;; elements -- both needed by sort, and both wrong before.
(check "to-array is an array" (let [a (to-array [3 1 2])] [(alength a) (aget a 0)]) [3 3])
(check "an array seqs"        (vec (to-array [3 1 2])) [3 1 2])
(check "first of an array"    (first (to-array [3 1 2])) 3)

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

(check "vector as a key"   (get {[1] 2} [1]) 2)
(check "map with a key"    (= {[1] 2} {[1] 2}) true)
(check "set of a vector"   (= #{[1]} #{[1]}) true)
(check "map as a key"      [(get {{:a 1} :v} {:a 1}) (contains? #{{:a 1}} {:a 1})] [:v true])
;; Entry order must not matter: two equal maps may hand back their
;; entries differently, so their hash is a sum rather than a fold.
(check "order of entries"  (get {{:b 2 :a 1} :m} {:a 1 :b 2}) :m)
;; A list and a vector of the same elements are equal, so they must
;; hash alike and be interchangeable as keys.
(check "list and vector"   [(= [1 2] (list 1 2)) (get {[1 2] :v} (list 1 2)) (get {(list 1 2) :v} [1 2])]
                           [true :v :v])
;; case* buckets by hash, so it was failing for the same reason.
(check "case on a map"     (case {:a 1 :b 2} {:b 2 :a 1} :map :default) :map)
(check "case on a vector"  (case [1 2] [1 2] :vec :default) :vec)
(check "case on a set"     (case #{1 2} #{2 1} :set :default) :set)
;; ...and things that are NOT equal must still miss.
(check "still not equal"   [(= #{1} [1]) (get {[1] :v} [2])] [false nil])

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

(check "large literals"  [9999999999 2147483648 -9999999999]
                         [9999999999 2147483648 -9999999999])
(check "very large"      123456789012345 123456789012345)
(check "large arith"     [(+ 9999999999 1) (* 3000000000 3) (- 0 9999999999)]
                         [10000000000 9000000000 -9999999999])
;; The radix forms share the reader's accumulator.
(check "large hex"       0xFFFFFFFFF 68719476735)
(check "large compare"   [(= 9999999999 9999999999) (< 2147483647 2147483648)]
                         [true true])
;; Equal values must still hash equal now that the hash folds 64 bits
;; into 32 -- a map keyed on a large integer finds it again.
(check "large as a key"  (get {9999999999 :found} 9999999999) :found)
(check "large in a set"  (contains? #{9999999999} 9999999999) true)
;; case* buckets integer keys by a 32-bit hash, and ival_of still
;; narrows to build it. That is safe only because the bucket is
;; followed by a real equality check -- these pair each value with the
;; 32-bit truncation it used to collapse to, so a narrowing that
;; reached the comparison would pick the wrong branch.
(check "case on a large int" (case 9999999999 9999999999 :yes 1410065407 :collided :no) :yes)
(check "...and its old truncation" (case 1410065407 9999999999 :wrong 1410065407 :right :no) :right)
(check "...across the sign flip" (case 2147483648 2147483648 :big -2147483648 :collided :no) :big)

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
(check "reduced"      [(/ 2 4) 2/4 -2/6] [1/2 1/2 -1/3])
(check "collapses"    [(/ 4 2) (/ 6 3) (/ 0 5)] [2 2 0])
(check "sign"         [(/ -1 3) (/ 1 -3)] [-1/3 -1/3])
(check "reciprocal"   (/ 2) 1/2)
(check "inexact div"  (/ 1 3) 1/3)
(check "div by zero"  (try (/ 1 0) (catch Throwable e :err)) :err)

;; Contagion is double > ratio > integer.
(check "ratio arith"  [(+ 1/2 1/3) (- 1/2 1/3) (* 2/3 3/4)] [5/6 1/6 1/2])
(check "with integer" (+ 1/2 1) 3/2)
(check "a double wins" (+ 1/2 0.5) 1.0)

;; = is by type, == is by value -- and 2/1 never exists to be compared.
(check "ratio ="      [(= 1/2 1/2) (= 1/2 0.5)] [true false])
(check "ratio =="     [(== 1/2 0.5) (= 2/1 2)] [true true])
(check "ratio order"  (< 1/3 1/2) true)

(check "ratio parts"  [(numerator 3/4) (denominator 3/4)] [3 4])
(check "ratio?"       [(ratio? 3/4) (ratio? 2) (ratio? 0.5)] [true false false])
(check "a ratio is a number" (number? 1/2) true)
(check "prints as n/d" (pr-str 3/4) "3/4")

;; Everything else that takes a number has to know about the third
;; kind too. Each of these was wrong once: inc/dec dropped a ratio to
;; a double, quot/rem read it as its numerator alone, and int handed
;; it straight back unconverted.
(check "ratio inc dec"  [(inc 1/2) (dec 1/2)] [3/2 -1/2])
(check "ratio abs"      (abs -1/2) 1/2)
(check "ratio min max"  [(min 1/2 1/3) (max 1/2 1/3)] [1/3 1/2])
(check "ratio quot rem" [(quot 7/2 1) (rem 7/2 1) (mod 7/2 1)] [3 1/2 1/2])
(check "ratio coerce"   [(int 1/2) (double 1/2)] [0 0.5])
(check "ratio compare"  [(compare 1/3 1/2) (compare 1/2 1/2)] [-1 0])
(check "ratio signs"    [(pos? 1/2) (neg? -1/2)] [true true])

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
(check "core alength"   (alength cm) 2)
(check "core aget full" [(aget cm 1 2) (aget cm 0 0)] [22 10])

;; core.clj's aget is ([array idx & idxs] (apply aget (aget array idx) idxs)),
;; so (aget cm 0) MUST hand back something that is itself an array.
(def crow (aget cm 0))
(check "a row is an array" [(alength crow) (aget crow 0) (aget crow 2)] [3 10 12])
(check "row then index"    (aget (aget cm 1) 2) 22)
;; and it is a VIEW, not a copy -- writing through it is visible in
;; the parent. This is the assertion that fails if slices ever start
;; copying.
(do (aset-int crow 1 999))
(check "a row is a view" (aget cm 0 1) 999)

;; aclone takes the shape of the VIEW, not of the buffer behind it,
;; and shares nothing with it afterwards.
(def cclone (aclone crow))
(do (aset-int cclone 0 -1))
(check "aclone of a row"
       [(alength cclone) (aget cclone 0) (aget crow 0) (aget cclone 1)]
       [3 -1 10 999])

;; An Object array is the `value` kind: it holds clotran values, so
;; plain aset works and a fresh slot reads nil, not 0.
(def cobj (make-array Object 2))
(do (aset cobj 0 :hello))
(check "object array" [(aget cobj 0) (aget cobj 1) (alength cobj)] [:hello nil 2])

(def cdbl (make-array Double/TYPE 2))
(do (aset-double cdbl 1 2.5))
(check "double array" [(aget cdbl 0) (aget cdbl 1)] [0.0 2.5])

;;; ---- printing a function -----------------------------------------
;;
;; (prn (fn [x] x)) used to SEGFAULT. print-method's :default is
;;   (if (instance? IObj o) (print-method (vary-meta o ...) w)
;;                          (print-simple o w))
;; and clotran claimed a closure was IObj while having no
;; print-method dispatch could reach -- so :default called itself on
;; the same object until the stack ran out. DEVIATIONS 23.

(check "print a function"        (pr-str (fn [x] x)) "#<fn>")
(check "a function in a vector"  (pr-str [1 (fn [x] x) 2]) "[1 #<fn> 2]")
(check "str of a function"       (str (fn [x] x)) "#<fn>")
;; A vector really does hold anything, which is the thing that
;; turned this up.
(check "heterogeneous vector"
       (let [v [1 2 3 "a" (fn [x] x) :kw {:m 1} #{9} [0]]]
         [(count v) (nth v 3) ((nth v 4) 42)])
       [9 "a" 42])
;; with-meta on a function still works -- it does not consult the
;; instance? answer that changed.
(check "meta on a function" (meta (with-meta (fn [] 1) {:a 1})) {:a 1})


;;; ---- macroexpand-1 and special-symbol? ---------------------------
;; Compiler.macroexpand1 is ONE step and does not descend, which is
;; what makes it different from the analysis pass clotran already
;; had. Every expectation below was run through `clj` first.

(check "macroexpand-1 a macro"   (macroexpand-1 '(when a b)) '(if a (do b)))
(check "macroexpand-1 not a macro" (macroexpand-1 '(inc 1)) '(inc 1))
(check "macroexpand-1 a symbol"  (macroexpand-1 'foo) 'foo)
(check "macroexpand-1 .member"   (macroexpand-1 '(.foo x 1 2)) '(. x foo 1 2))
(check "macroexpand-1 ctor"      (macroexpand-1 '(String. "a")) '(new String "a"))
;; macroexpand loops to a fixed point but still does not descend --
;; the inner `when` survives.
(check "macroexpand stops at the top"
       (macroexpand '(when a (when b c))) '(if a (do (when b c))))

(check "special-symbol? if"      (special-symbol? 'if) true)
(check "special-symbol? amp"     (special-symbol? '&) true)
(check "special-symbol? a name"  (special-symbol? 'foo) false)
;; Clojure's list, 24 entries -- not clotran's own special forms.
(check "specials count"          (count (. clojure.lang.Compiler specials)) 24)


;;; ---- #_ discard ------------------------------------------------
;; #_ is a kind of WHITESPACE, not a form that reads as nothing --
;; which only shows at the end of a collection, where there is no
;; following form to pair it with. Values checked against `clj`.

(check "discard in a vector"     [1 #_2 3] [1 3])
(check "discard an argument"     (+ 1 #_(inc 9) 2) 3)
(check "discard at the end"      (and true #_(= 1 1)) true)
(check "discard last in vector"  [1 2 #_3] [1 2])
(check "discard a map pair"      {:a 1 #_:b #_2 :c 3} {:a 1 :c 3})
(check "discard in a set"        #{1 #_2 3} #{1 3})
(check "two discards in a row"   (list #_#_1 2 3) '(3))


;;; ---- the quote is not a delimiter --------------------------------
;; isTerminatingMacro excludes #, % and ' -- so a prime suffix is part
;; of the name, the way ss' and x' are written in Clojure's own suite.

(check "prime-suffixed symbol"  (let [ss' 1 x'y 2] [ss' x'y]) [1 2])
(check "quote still quotes"     '(a 'b) '(a (quote b)))
(check "prime in a quoted name" (str 'foo') "foo'")
(check "the quote character"    \' \')


;;; ---- reader metadata --------------------------------------------
;; Checked against `clj` by KEY, not by whole map: Clojure's reader
;; also attaches :line and :column, which clotran does not track.

(check "#^ is the old ^"        (:a (meta (quote #^{:a 1} (x)))) 1)
(check "#^Tag"                  (:tag (meta (quote #^Integer (x)))) 'Integer)
(check "#^:kw"                  (:dynamic (meta (quote #^:dynamic (x)))) true)
;; A VECTOR is metadata too -- ^[long] is 1.12's param-tags.
(check "^[long] is param-tags"  (:param-tags (meta (quote ^[long] (x)))) '[long])


;;; ---- empty ------------------------------------------------------
;; core.clj's `empty` is (.empty coll) behind an instance? guard, so
;; the answer keeps the collection's CATEGORY and a non-collection
;; answers nil rather than erroring. All checked against `clj`.

(check "empty a vector"   (empty [1 2]) [])
(check "empty a map"      (empty {:a 1}) {})
(check "empty a set"      (empty #{1}) #{})
(check "empty a list"     (empty '(1 2)) '())
(check "empty a seq"      (empty (seq [1 2])) '())
(check "empty a lazy seq" (empty (lazy-seq [1 2])) '())
(check "empty nil"        (empty nil) nil)
(check "empty a number"   (empty 1) nil)
(check "empty a string"   (empty "ab") nil)
(check "empty keeps type"
       [(vector? (empty [1])) (map? (empty {:a 1}))
        (set? (empty #{1})) (list? (empty '(1)))]
       [true true true true])


;;; ---- swap-vals!, reset-vals!, and the multimethod table ----------
;; All of these are core.clj reaching for a host member it declares in
;; its own type hints. Values from `clj`.

(check "swap-vals!"        (let [a (atom 1)] [(swap-vals! a inc) @a]) [[1 2] 2])
(check "swap-vals! args"   (let [a (atom 1)] [(swap-vals! a + 1 2 3 4) @a]) [[1 11] 11])
(check "swap-vals! conj"   (let [a (atom [])] [(swap-vals! a conj :x) @a]) [[[] [:x]] [:x]])
(check "reset-vals!"       (let [a (atom 1)] [(reset-vals! a 9) @a]) [[1 9] 9])

(defmulti ltest-area :shape)
(defmethod ltest-area :square [s] (* (:side s) (:side s)))
(defmethod ltest-area :circle [s] 3)
(defmethod ltest-area :default [s] :none)

(check "methods"           (count (methods ltest-area)) 3)
(check "methods keys"      (sort-by str (keys (methods ltest-area))) '(:circle :default :square))
(check "get-method"        ((get-method ltest-area :square) {:side 4}) 16)
;; get-method answers what WOULD apply, so an unregistered value finds
;; the default rather than nil.
(check "get-method default" ((get-method ltest-area :hexagon) {}) :none)
;; preferMethod records nothing here (DEVIATIONS 8), so the table is
;; empty rather than absent.
(check "prefers"           (prefers ltest-area) {})
(check "remove-method"     (do (remove-method ltest-area :circle)
                               (count (methods ltest-area))) 2)


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

(check "Math/E"  (= Math/E clojure.math/E) true)
(check "Math/PI" (= Math/PI clojure.math/PI) true)

(check "sin"        (clojure.math/sin 0.5) 0.479425538604203)
(check "sqrt"       (clojure.math/sqrt 2) 1.4142135623730951)
(check "cbrt of -8" (clojure.math/cbrt -8) -2.0)
(check "log10"      (clojure.math/log10 1000) 3.0)
(check "hypot"      (clojure.math/hypot 3 4) 5.0)
(check "pow"        (clojure.math/pow 2 10) 1024.0)
(check "tanh"       (clojure.math/tanh 1) 0.7615941559557649)

;; rint rounds HALF TO EVEN, which neither truncation nor
;; round-half-away gives.
(check "rint"       [(clojure.math/rint 2.5) (clojure.math/rint 3.5) (clojure.math/rint -2.5)]
                    [2.0 4.0 -2.0])
(check "round"      [(clojure.math/round 2.5) (clojure.math/round -2.5) (clojure.math/round 2.4)]
                    [3 -2 2])
(check "signum"     [(clojure.math/signum -3.0) (clojure.math/signum 0.0) (clojure.math/signum 4.0)]
                    [-1.0 0.0 1.0])
(check "ceil/floor" [(clojure.math/ceil 1.2) (clojure.math/floor -1.2)] [2.0 -2.0])

(check "ulp"        (clojure.math/ulp 1.0) 2.220446049250313E-16)
(check "next-up"    (clojure.math/next-up 1.0) 1.0000000000000002)
(check "next-down"  (clojure.math/next-down 1.0) 0.9999999999999999)
(check "next-after" (clojure.math/next-after 1.0 2.0) 1.0000000000000002)
(check "get-exponent"
       [(clojure.math/get-exponent 1.0) (clojure.math/get-exponent 8.0)
        (clojure.math/get-exponent 0.5)]
       [0 3 -1])
(check "scalb"      (clojure.math/scalb 3.0 4) 48.0)
(check "copy-sign"  (clojure.math/copy-sign 3.0 -1.0) -3.0)
(check "IEEE-remainder" (clojure.math/IEEE-remainder 5.0 3.0) -1.0)
;; expm1 and log1p keep their digits near zero, where exp(x)-1 would
;; lose all of them.
(check "expm1"      (clojure.math/expm1 1e-9) 1.0000000005000001E-9)
(check "log1p"      (clojure.math/log1p 1e-9) 9.999999995E-10)
(check "to-radians" (clojure.math/to-radians 180.0) Math/PI)
(check "to-degrees" (clojure.math/to-degrees Math/PI) 180.0)

;; The *Exact family throws where ordinary arithmetic wraps.
(check "exact arithmetic"
       [(clojure.math/add-exact 1 2) (clojure.math/subtract-exact 5 9)
        (clojure.math/multiply-exact 6 7) (clojure.math/increment-exact 1)
        (clojure.math/decrement-exact 1) (clojure.math/negate-exact 5)]
       [3 -4 42 2 0 -5])
(check "add-exact overflows"
       (try (clojure.math/add-exact Long/MAX_VALUE 1) :no (catch Throwable e :threw))
       :threw)
(check "multiply-exact overflows"
       (try (clojure.math/multiply-exact Long/MAX_VALUE 2) :no (catch Throwable e :threw))
       :threw)
;; Floor division, not truncation.
(check "floor-div/mod" [(clojure.math/floor-div -7 2) (clojure.math/floor-mod -7 2)] [-4 1])

;; Math/abs is overloaded on the JVM: a long stays a long.
(check "Math/abs"   [(Math/abs -3) (Math/abs -3.5)] [3 3.5])


;;; ---- format -----------------------------------------------------
;; core.clj's `format` is (String/format fmt (to-array args)), so this
;; is java.util.Formatter -- the subset Clojure's own source and suite
;; actually write. Every line checked against `clj`.

(check "format %s"      (format "%s" "a") "a")
(check "format two"     (format "%s-%s" :a 1) ":a-1")
(check "format %d"      (format "%d" 42) "42")
(check "width and flags" (format "%5d|%-5d|%05d" 42 42 42) "   42|42   |00042")
(check "format %x %X %o" (format "%x %X %o" 255 255 8) "ff FF 10")
(check "format %f"      (format "%f" 1.5) "1.500000")
(check "format precision" (format "%.2f" 3.14159) "3.14")
(check "float width"    (format "%10.3f|%-10.3f|" 3.14159 3.14159) "     3.142|3.142     |")
(check "format %e"      (format "%e" 1234.5) "1.234500e+03")
;; %b is false only for nil and false -- 0 is true.
(check "format %b"      (format "%b %b %b %b" true false nil 0) "true false false true")
(check "format %c"      (format "%c" \a) "a")
(check "format %%"      (format "100%%") "100%")
(check "format %n"      (format "a%nb") "a\nb")
(check "format %S"      (format "%S" "ab") "AB")
(check "string precision" (format "%.2s" "abcdef") "ab")
;; String.valueOf(null) is "null", not Clojure's nil.
(check "format nil"     (format "%s" nil) "null")
(check "format a vector" (format "%s" [1 2]) "[1 2]")
;; core_print's own use of it.
(check "format like core_print" (format "0x%x " 255) "0xff ")


;;; ---- range over more than longs ---------------------------------
;; core.clj picks between LongRange/create and Range/create on
;; (int? x); clotran has one builtin behind both, and it used to read
;; the integer field regardless -- so every bound of a double range
;; read as 0 and it yielded zeros forever. Values from `clj`.

(check "double range"       (count (range 0.0 360.0 5.0)) 72)
(check "double range head"  (take 5 (range 0.0 360.0 5.0)) '(0.0 5.0 10.0 15.0 20.0))
(check "fractional step"    (range 0.0 1.0 0.25) '(0.0 0.25 0.5 0.75))
(check "double end only"    (range 2.5) '(0 1 2))
;; A ratio step stays exact rather than becoming a double.
(check "ratio step"         (range 0 1 1/4) '(0 1/4 1/2 3/4))
(check "ratio end"          (range 0 5/2) '(0 1 2))
(check "negative step"      (range 10 0 -2) '(10 8 6 4 2))
(check "negative double step" (range 10.0 0.0 -2.5) '(10.0 7.5 5.0 2.5))
(check "integer range"      (range 0 10 2) '(0 2 4 6 8))
(check "empty range"        (range 0 0) '())
(check "infinite range"     (take 3 (range)) '(0 1 2))


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

(check "count a long range"    (count (range 8000)) 8000)
(check "count a long take"     (count (take 8000 (range 50000))) 8000)
(check "count a long map"      (count (take 8000 (map inc (range 50000)))) 8000)
(check "count a long iterate"  (count (take 8000 (iterate inc 0))) 8000)
(check "walk a long range"     (do (dorun (range 8000)) :ok) :ok)
(check "the last of a long range" (last (range 8000)) 7999)


;;; ---- printing doubles -------------------------------------------
;; Double.toString: the SHORTEST decimal that reads back as the same
;; double, plain while 1e-3 <= |d| < 1e7 and scientific outside that.
;; The old printer wrote ten fixed decimals, so 0.479425538604203 came
;; out as 0.4794255386 -- a different double -- and Double/MAX_VALUE
;; overran the buffer outright. Every line below is `clj`'s output.

(check "a whole double"     (pr-str 2.0) "2.0")
(check "a negative double"  (pr-str -3.5) "-3.5")
(check "negative zero"      (pr-str -0.0) "-0.0")
(check "zero"               (pr-str 0.0) "0.0")
;; The round trip is the point: these need all their digits.
(check "seventeen digits"   (pr-str 0.479425538604203) "0.479425538604203")
(check "a third"            (pr-str (/ 1.0 3.0)) "0.3333333333333333")
(check "pi"                 (pr-str 3.141592653589793) "3.141592653589793")
(check "one tenth"          (pr-str 0.1) "0.1")
;; The plain/scientific boundary is 1e-3 and 1e7, not Fortran's.
(check "just inside"        [(pr-str 0.001) (pr-str 1000000.0)] ["0.001" "1000000.0"])
(check "just outside"       [(pr-str 1.0E-4) (pr-str 1.0E7)] ["1.0E-4" "1.0E7"])
(check "large"              (pr-str 1.0E20) "1.0E20")
(check "the largest double" (pr-str Double/MAX_VALUE) "1.7976931348623157E308")
(check "a subnormal"        (pr-str 2.2250738585072014E-308) "2.2250738585072014E-308")
(check "reads back"         (= (read-string (pr-str 0.479425538604203)) 0.479425538604203) true)

;;; ---- read-string ------------------------------------------------
;; (RT/readString s) reads ONE form and ignores what follows.

(check "read a list"     (read-string "(1 2 3)") '(1 2 3))
(check "read a map"      (read-string "{:a 1}") {:a 1})
(check "read one form"   (read-string "1 2 3") 1)
(check "read a keyword"  (read-string ":kw") :kw)
(check "a bad form throws" (try (read-string "(1") :no (catch Throwable e :threw)) :threw)

;;; ---- the boxed number classes -----------------------------------
;; Long/MAX_VALUE and its neighbours, and Double.compare -- the TOTAL
;; order, which ranks -0.0 below 0.0 and NaN above everything, neither
;; of which < can say. Values from `clj`.

(check "Long bounds"    [Long/MAX_VALUE Long/MIN_VALUE] [9223372036854775807 -9223372036854775808])
(check "Long size"      [Long/SIZE Long/BYTES] [64 8])
(check "Integer bounds" [Integer/MAX_VALUE Integer/MIN_VALUE] [2147483647 -2147483648])
(check "Short bounds"   [Short/MAX_VALUE Short/MIN_VALUE] [32767 -32768])
(check "Byte bounds"    [Byte/MAX_VALUE Byte/MIN_VALUE] [127 -128])
(check "Double bounds"  [Double/MAX_VALUE Double/MIN_VALUE]
                        [1.7976931348623157E308 4.9E-324])
(check "Double exponents" [Double/MAX_EXPONENT Double/MIN_EXPONENT] [1023 -1022])
(check "the non-finite constants"
       [(pr-str Double/POSITIVE_INFINITY) (pr-str Double/NEGATIVE_INFINITY)
        (pr-str Double/NaN)]
       ["##Inf" "##-Inf" "##NaN"])
(check "compare"        [(Double/compare 1.0 2.0) (Double/compare 2.0 1.0)
                         (Double/compare 1.0 1.0)] [-1 1 0])
(check "compare signed zero"
       [(Double/compare -0.0 0.0) (Double/compare 0.0 -0.0) (Double/compare -0.0 -0.0)]
       [-1 1 0])
;; NaN is greater than everything, and equal to itself.
(check "compare NaN"
       [(Double/compare Double/NaN 1.0) (Double/compare 1.0 Double/NaN)
        (Double/compare Double/NaN Double/NaN)
        (Double/compare Double/NaN Double/POSITIVE_INFINITY)]
       [1 -1 0 1])
(check "Long compare"   [(Long/compare 1 2) (Long/compare 2 1) (Long/compare 1 1)] [-1 1 0])


;;; ---- clojure.string's host members -------------------------------
;; clojure.string is written entirely against java.util.regex's
;; Pattern and Matcher plus StringBuilder, so none of split, replace
;; or reverse worked without them. Every expectation is `clj`'s.

(require (quote [clojure.string :as ltstr]))

(check "split"           (ltstr/split "a,b,c" #",") ["a" "b" "c"])
;; A positive limit caps the parts and the last keeps the rest unsplit.
(check "split with a limit" (ltstr/split "a,b,c" #"," 2) ["a" "b,c"])
;; No limit drops trailing empties; -1 keeps them.
(check "split drops trailing empties" (ltstr/split "a,b,c," #",") ["a" "b" "c"])
(check "split -1 keeps them"          (ltstr/split "a,b,c," #"," -1) ["a" "b" "c" ""])
(check "split on empty pattern"       (ltstr/split "abc" #"") ["a" "b" "c"])
(check "split-lines"     (ltstr/split-lines "a\nb\r\nc") ["a" "b" "c"])

(check "reverse"         (ltstr/reverse "abc") "cba")
(check "re-quote-replacement" (ltstr/re-quote-replacement "a$b\\c") "a\\$b\\\\c")
(check "index-of a char" [(ltstr/index-of "hello" \l) (ltstr/last-index-of "hello" \l)] [2 3])

(check "replace a pattern"   (ltstr/replace "abc" #"b" "X") "aXc")
(check "replace with a fn"   (ltstr/replace "abc" #"b" (fn [m] (ltstr/upper-case m))) "aBc")
;; $1 and $2 name groups -- the one place a replacement is not literal.
(check "replace with groups"
       (ltstr/replace "Almost Pig Latin" #"\b(\w)(\w+)\b" "$2$1ay")
       "lmostAay igPay atinLay")
(check "replace-first"       (ltstr/replace-first "aaa" #"a" "X") "Xaa")
(check "replace a char"      (ltstr/replace "abc" \b \X) "aXc")
(check "replace a string"    (ltstr/replace "abcabc" "bc" "X") "aXaX")
(check "replace an empty pattern" (ltstr/replace "abc" #"" "-") "-a-b-c-")


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

(check "binding across namespaces" (lt.other/lt-with lt.other/lt-peek) 7)
(check "and it unwinds"            (lt.other/lt-peek) :unbound)


;;; ---- a set answers a lookup --------------------------------------
;; A set's contents live one slot down, and get/keyword lookup never
;; unwrapped them -- so (get #{:at} :at) and (:at #{:at}) both answered
;; nil where Clojure answers :at. cl_format.clj asks exactly that of
;; its allowed-flags set for every directive it compiles, so every flag
;; looked illegal and clojure.pprint would not load at all.

(check "keyword on a set"    (:at #{:colon :at}) :at)
(check "get on a set"        (get #{:at} :at) :at)
(check "get on a set misses" (:zz #{:at}) nil)
(check "get with not-found"  (get #{:at} :zz :d) :d)
(check "maps still work"     [(get {:a 1} :a) (:a {:a 1})] [1 1])

;;; ---- indexOf takes a character CODE ------------------------------
;; String.indexOf is overloaded on (int ch) as well as (String), and
;; cl_format.clj writes (.indexOf s (int \~)) to find its directives.
;; Searching for the TEXT "126" never found one, so every format string
;; compiled to itself and cl-format returned the format unchanged.

(check "indexOf a code"   (.indexOf "abcabc" (int \b)) 1)
(check "indexOf a string" (.indexOf "abcabc" "b") 1)
(check "indexOf from"     (.indexOf "abcabc" "b" 2) 4)
(check "indexOf misses"   (.indexOf "abc" "z") -1)
(check "index-of a char"  [(clojure.string/index-of "hello" \l)
                           (clojure.string/index-of "hello" "l" 3)
                           (clojure.string/last-index-of "hello" \l)]
                          [2 3 3])


;;; ---- arrays, and the exceptions that ask for one -----------------
;; .getStackTrace answered an empty VECTOR, and Throwable->map asks
;; (alength st) straight after -- so every printed exception, and every
;; thrown-with-cause-msg? in Clojure's suite, died on "alength: not an
;; array" rather than on anything real. There is no stack trace to
;; report here; there is an empty array.

(check "into-array length"   (alength (into-array [1 2 3])) 3)
(check "into-array element"  (aget (into-array [1 2 3]) 1) 2)
(check "into-array seq"      (seq (into-array [:x :y])) '(:x :y))
(check "an empty into-array" (alength (into-array [])) 0)
;; The component type is read and discarded -- there are no primitive
;; component types here (DEVIATIONS 24).
(check "into-array with a type" (vec (into-array String ["a" "b"])) ["a" "b"])
(check "an empty stack trace" (alength (.getStackTrace (Exception. "x"))) 0)
(check "Throwable->map"      (:cause (Throwable->map (Exception. "boom"))) "boom")

;;; ---- ExceptionInfo -----------------------------------------------
;; It does not end in "Exception", so it was not recognised as a
;; throwable class at all -- and a catch naming it in full could not
;; match a throw that named it short.

(check "ex-data"    (ex-data (ex-info "m" {:a 1})) {:a 1})
(check "ex-message" (ex-message (ex-info "m" {:a 1})) "m")
(check "instance?"  (instance? clojure.lang.ExceptionInfo (ex-info "m" {})) true)
(check "catch it by its full name"
       (try (throw (ex-info "m" {:a 1})) (catch clojure.lang.ExceptionInfo e (ex-data e)))
       {:a 1})
(check "a plain exception has no data" (ex-data (Exception. "plain")) nil)


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

(check "a proxy method"    (.toString (proxy [Object] [] (toString [] "hello"))) "hello")
(check "str goes through it" (str (proxy [Object] [] (toString [] "world"))) "world")
(check "a closure"         (let [n 5] (.toString (proxy [Object] [] (toString [] (str n))))) "5")

(check "arguments"         (let [q (proxy [Object] []
                                     (greet [n] (str "hi " n))
                                     (two [a b] (+ a b)))]
                             [(.greet q "x") (.two q 1 2)])
                           ["hi x" 3])
;; Several arities inside ONE method form, which reify writes as
;; several forms.
(check "nested arities"    (let [m (proxy [Object] [] (f ([] 0) ([a] a) ([a b] (+ a b))))]
                             [(.f m) (.f m 7) (.f m 3 4)])
                           [0 7 7])
;; `this` is bound without being named.
(check "this is implicit"  (let [s (proxy [Object] [] (me [] this))] (identical? s (.me s))) true)

;;; ---- `..` is a macro, not a member access ------------------------
;; Clojure never has to say so: Compiler.macroexpand1 asks isMacro
;; before it reaches the dot sugar, and `..` is a macro. clotran asks
;; the other way round -- equivalent for every other name, since .foo
;; is never a macro, and wrong for exactly this one, where
;; (.. a getClass isArray) read as the member "." on a.

(check "threading"       (.. "abc" toString toString) "abc")
(check "with arguments"  (.. "hello" (substring 1) (substring 1)) "llo")
(check "a plain member still works" (.toString "x") "x")
(check ".. expands to ." (macroexpand-1 '(.. a b)) '(. a b))


;;; ---- a vector is associative by index ----------------------------
;; All four of these came out of one namespace, clojure.data, which is
;; written entirely against them: assoc on a vector answered NIL,
;; get and contains? by index answered nothing, and conj of nil onto a
;; map added a nil entry. Values from `clj`.

(check "assoc a vector"      (assoc [1 2] 0 9) [9 2])
;; An index equal to the count APPENDS -- the one place assoc grows a
;; vector. Past that it throws.
(check "assoc appends at the end" (assoc [nil] 1 2) [nil 2])
(check "assoc into an empty vector" (assoc [] 0 :x) [:x])
(check "assoc past the end throws" (try (assoc [1] 5 :x) (catch Throwable e :threw)) :threw)
(check "assoc-in through a vector" (assoc-in [[1]] [0 0] 9) [[9]])
(check "update a vector"      (update [1 2] 0 inc) [2 2])

(check "contains? an index"  [(contains? [1 2] 0) (contains? [1 2] 1)
                              (contains? [1 2] 5) (contains? [1 2] -1)]
                             [true true false false])
(check "get by index"        [(get [1 2] 0) (get [1 2] 5) (get [1 2] 5 :d) (get [1 2] :k)]
                             [1 nil :d nil])
(check "a string too"        [(contains? "ab" 0) (contains? "ab" 9) (get "ab" 0) (get "ab" 9)]
                             [true false \a nil])
;; .contains on a String is still substring containment -- the two
;; methods share a name and the argument tells them apart.
(check "String.contains"     [(.contains "abc" "b") (.contains "abc" "z")] [true false])

;; APersistentMap.cons walks (seq o), and the seq of nil is nil, so a
;; map comes back unchanged. (merge m nil) is (conj m nil).
(check "conj nil onto a map"  (conj {:a 1} nil) {:a 1})
(check "merge with nil"       [(merge {:a 1} nil) (merge nil nil)] [{:a 1} nil])

;;; ---- protocols see the host supertypes ---------------------------
;; core.clj's `supers` is built from .getInterfaces, and answering an
;; empty one sent EVERY protocol dispatch to its (impl Object)
;; fallback. clojure.data's equality-partition called a map an :atom
;; even though java.util.Map was in the impls map all along.

(require (quote [clojure.data :as ltdata]))

(check "diff of maps"        (ltdata/diff {:a 1} {:a 1 :b 2}) [nil {:b 2} {:a 1}])
(check "diff of vectors"     (ltdata/diff [1 2] [1 3]) [[nil 2] [nil 3] [1]])
(check "diff of sets"        (ltdata/diff #{1 2} #{2 3}) [#{1} #{3} #{2}])
(check "diff of unlike things" (ltdata/diff {:a 1} :b) [{:a 1} :b nil])
(check "diff of equals"      (ltdata/diff 1 1) [nil nil 1])
(check "diff nested"         (ltdata/diff {:a {:b 1 :c 2}} {:a {:b 1 :c 3}})
                             [{:a {:c 2}} {:a {:c 3}} {:a {:b 1}}])


;;; ---- a bad arity is an ArityException -----------------------------
;; clotran said "no matching arity" through its internal error map,
;; which no (catch SomeClass e) could match and which did not say how
;; many arguments arrived or to whom. Clojure's wording, class and
;; catchability, all checked against `clj`.

(defn ltf0 [] 0)
(defn ltf1 [a] a)
(defn ltfm ([a] 1) ([a b] 2))

(check "the message says how many"
       (try (ltf0 1) (catch Throwable e (boolean (re-find #"Wrong number of args \(1\) passed to" (.getMessage e)))))
       true)
(check "and which function"
       (try (ltf0 1) (catch Throwable e (boolean (re-find #"ltf0" (.getMessage e)))))
       true)
(check "too few"
       (try (ltf1) (catch Throwable e (boolean (re-find #"Wrong number of args \(0\)" (.getMessage e)))))
       true)
(check "a multi-arity fn"
       (try (ltfm 1 2 3) (catch Throwable e (boolean (re-find #"Wrong number of args \(3\)" (.getMessage e)))))
       true)
(check "catchable as ArityException"
       (try (ltf0 1) :no (catch clojure.lang.ArityException e :arity)) :arity)
;; ArityException extends IllegalArgumentException, which Clojure's own
;; suite relies on.
(check "and as IllegalArgumentException"
       (try (ltf0 1) :no (catch IllegalArgumentException e :iae)) :iae)
(check "the right arities still work" [(ltfm 1) (ltfm 1 2)] [1 2])


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

(check "an explicit mode"    (error-mode (agent 1 :error-mode :continue)) :continue)
(check "a validator does not change the mode" (error-mode (agent 1 :validator pos?)) :fail)

;; A latch is a counter when there is one thread.
(check "a countdown latch"
       (let [l (java.util.concurrent.CountDownLatch. 2)] (.countDown l) (.getCount l))
       1)

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
(check "a validator the state already fails is refused"
       (try (set-validator! (atom -1) pos?) :no (catch IllegalStateException e :refused))
       :refused)

;;; ---- report -----------------------------------------------------


(println "")
(if (zero? @*failures*)
  (println "LANGUAGE TESTS PASSED")
  (println "LANGUAGE TESTS FAILED:" @*failures*))

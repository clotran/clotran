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
;; A collection as an ELEMENT still matches by identity -- the same
;; limitation map keys have. DEVIATIONS 22.
(check "collection in a set (DEVIATIONS 22)" (= #{[1]} #{[1]}) false)
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

;; A number Clojure reads and clotran has no TYPE for must NOT be a
;; reader error. It was, briefly, and the cost was out of all
;; proportion: clotran aborts a whole file on a reader error, so one
;; 2/3 took every form after it down, across the 12 of Clojure's 67
;; test namespaces that contain a ratio literal -- 766 passing
;; assertions became 223, control.clj alone losing 153.
;;
;; These four lines are the falsification: each is a literal that
;; Clojure reads as a number, so if the reader ever raises on one
;; again this whole file stops loading and the gate goes red -- which
;; is exactly what failed to happen last time, because no test
;; anywhere contained one.
(check "a ratio is a symbol, not an error"  (symbol? (quote 2/3)) true)
(check "...and a negative one"              (symbol? (quote -2/3)) true)
(check "an N suffix is a symbol"            (symbol? (quote 42N)) true)
(check "an M suffix is a symbol"            (symbol? (quote 1.5M)) true)

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

;;; ---- report -----------------------------------------------------


(println "")
(if (zero? @*failures*)
  (println "LANGUAGE TESTS PASSED")
  (println "LANGUAGE TESTS FAILED:" @*failures*))

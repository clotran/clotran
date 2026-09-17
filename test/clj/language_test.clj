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

;;; ---- report -----------------------------------------------------

(println "")
(if (zero? @*failures*)
  (println "LANGUAGE TESTS PASSED")
  (println "LANGUAGE TESTS FAILED:" @*failures*))

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
;; `vec` on both sides deliberately: (= lazy-seq vector) is false here,
;; which is DEVIATIONS 22 and not what this line is testing.
(check "map-indexed" (vec (map-indexed vector [:a :b :c])) [[0 :a] [1 :b] [2 :c]])

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
(check "record seq"                 (vec (seq rec)) [[:a 1] [:b 2]])
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

;;; ---- report -----------------------------------------------------

(println "")
(if (zero? @*failures*)
  (println "LANGUAGE TESTS PASSED")
  (println "LANGUAGE TESTS FAILED:" @*failures*))

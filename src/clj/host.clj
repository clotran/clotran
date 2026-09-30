;; The shim between clotran's host primitives and what Clojure code
;; expects. NOT a core library, and deliberately not a re-implementation
;; of one.
;;
;; The project's thesis is that clotran runs Rich Hickey's actual
;; core.clj. Anything written here that core.clj also defines is a
;; SECOND, DIFFERENT implementation that the real file will replace --
;; so the only things that belong here are the ones core.clj cannot
;; supply, because they depend on how this host represents values.
;;
;; That is exactly the type predicates. Real Clojure asks `instance?`
;; about clj classes; clotran has no clj classes, so it answers with
;; `clotran-type` and the predicates are written on top of it. Every
;; other function Clojure programs use -- map, filter, reduce, take,
;; range, merge, into, sort -- is a defn in core.clj and must come from
;; there, not from here.
;;
;; The few macros below exist only because the predicates cannot be
;; written without them. They are scaffolding, and they go the moment
;; the evaluator can load the real core.clj, which is the actual goal.

;; Interned in clojure.core, not in user: this is bootstrap, and
;; RT.doInit puts its natives in clojure.core for the same reason --
;; core.clj is loaded with clojure.core current and must see them.
(in-ns (quote clojure.core))

;; --- scaffolding: the minimum needed to write a defn at all -------

(defmacro* defn
  (fn* [&form &env name params & body]
    `(def ~name (fn* ~params ~@body))))

(defmacro* fn  (fn* [&form &env params & body] `(fn* ~params ~@body)))
(defmacro* let (fn* [&form &env bindings & body] `(let* ~bindings ~@body)))

;; --- the shim proper ---------------------------------------------
;;
;; One host primitive, `clotran-type`, and the predicates over it.
;; core.clj cannot define these: it would ask instance? about
;; clotran.host.string and clotran.host.persistent_vector, and neither
;; exists here.

(defn nil?     [x] (= (clotran-type x) :nil))
(defn list?    [x] (= (clotran-type x) :list))
(defn vector?  [x] (= (clotran-type x) :vector))
(defn map?     [x] (= (clotran-type x) :map))
(defn keyword? [x] (= (clotran-type x) :keyword))
(defn symbol?  [x] (= (clotran-type x) :symbol))
(defn string?  [x] (= (clotran-type x) :string))
(defn fn?      [x] (= (clotran-type x) :fn))
(defn number?  [x] (if (= (clotran-type x) :int) true (= (clotran-type x) :double)))

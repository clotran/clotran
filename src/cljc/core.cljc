;; clotran's own clojure.core -- grown incrementally against exactly
;; the primitives the Fortran host provides (fn*, def, defmacro, if,
;; do, let*, quasiquote). Not a port of real clojure/core.clj: that
;; file leans on clojure.lang.* Java interop from its very first
;; definitions (list, cons, first, defmacro all call straight into
;; Java statics), so there is nothing in it to port. Every definition
;; here is freshly written to match real Clojure's actual
;; macroexpansion and behavior -- verified against the real `clojure`
;; CLI as an oracle while writing it, not from memory -- the same way
;; gfortran cross-checks flang elsewhere in this project.
;;
;; fn* itself is single-arity only (no multi-arity dispatch yet), so
;; every macro below that expands to fn*/def is single-arity only too
;; -- a known, deliberate simplification, not an oversight.

(def not (fn* [a] (if a false true)))

(defmacro cond [& clauses]
  (if (empty? clauses)
    nil
    `(if ~(first clauses)
       ~(first (rest clauses))
       (cond ~@(rest (rest clauses))))))

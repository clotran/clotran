;; DERIVED from test/clj/clojure/test_clojure/evaluation.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.evaluation (:use clojure.test clojure.test-helper))

(defmacro in-test-ns [& body]
  `(binding [*ns* *ns*]
     (in-ns 'clojure.test-clojure.evaluation)
     ~@body))

(defmacro #^{:private true} evaluates-to-itself? [expr]
  `(let [v# ~expr
         q# (quote ~expr)]
     (is (= (eval q#) q#) (str q# " does not evaluate to itself"))))

(def foo "abc")

(in-ns 'resolution-test)

(def bar 123)

(def #^{:private true} baz 456)

(in-ns 'clojure.test-clojure.evaluation)

(defn a-match? [re s] (not (nil? (re-matches re s))))

(def x 1)

(def y 2)

;; evaluation.clj:197 [language]
(deftest Collections
  (in-test-ns
    (test-that
      "Vectors and Maps yield vectors and (hash) maps whose contents are the
      evaluated values of the objects they contain."
      (is (= (eval '[x y 3]) [1 2 3]))
      (is (= (eval '{:x x :y y :z 3}) {:x 1 :y 2 :z 3}))
      (is (instance? clojure.lang.IPersistentMap (eval '{:x x :y y})))))

  (in-test-ns
    (test-that
      "Metadata maps yield maps whose contents are the evaluated values of
      the objects they contain. If a vector or map has metadata, the evaluated
      metadata map will become the metadata of the resulting value."
      (is (= (eval #^{:x x} '[x y]) #^{:x 1} [1 2]))))

  (test-that
    "An empty list () evaluates to an empty list."
    (is (= (eval '()) ()))
    (is (empty? (eval ())))
    (is (= (eval (list)) ())))

  ;aargh, fragile tests, please fix
  #_(test-that
    "Non-empty lists are considered calls"
    (is (thrown? Compiler$CompilerException (eval '(1 2 3))))))

;; evaluation.clj:224 [language]
(deftest Macros)

;; evaluation.clj:226 [language]
(deftest Loading)

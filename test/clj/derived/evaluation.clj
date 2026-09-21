;; DERIVED from test/clj/clojure/test_clojure/evaluation.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.evaluation (:use clojure.test clojure.test-helper))

(defmacro #^{:private true} evaluates-to-itself? [expr]
  `(let [v# ~expr
         q# (quote ~expr)]
     (is (= (eval q#) q#) (str q# " does not evaluate to itself"))))

(def foo "abc")

(def bar 123)

(def #^{:private true} baz 456)

(defn a-match? [re s] (not (nil? (re-matches re s))))

(def x 1)

(def y 2)

;; evaluation.clj:224 [language]
(deftest Macros)

;; evaluation.clj:226 [language]
(deftest Loading)

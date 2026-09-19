;; DERIVED from test/clj/clojure/test_clojure/predicates.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.predicates (:use clojure.test))

(def myvar 42)

;; predicates.clj:139 [language]
(deftest test-string?-more
  (are [x] (not (string? x))
    (new java.lang.StringBuilder "abc")
    (new java.lang.StringBuffer "xyz")))

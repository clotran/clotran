;; DERIVED from test/clj/clojure/test_clojure/rt.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.rt (:require [clojure.string :as string] clojure.set) (:use clojure.test clojure.test-helper))

(def example-var)

;; rt.clj:26 [language]
(deftest rt-print-prior-to-print-initialize
  (testing "pattern literals"
    (is (= "#\"foo\"" (bare-rt-print #"foo")))))

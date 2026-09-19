;; DERIVED from test/clj/clojure/test_clojure/run_single_test.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.run-single-test (:require [clojure.test :refer [is deftest run-test run-tests]] [clojure.test-helper :refer [with-err-string-writer]]))

(defn not-a-test
  [])

(defmacro should-print-to-err
  [re & body]
  `(is (re-find ~re (with-err-string-writer ~@body))))

;; run_single_test.clj:21 [language]
(deftest reports-missing-var
  (should-print-to-err #"^Unable to resolve .*/function-missing to a test function.*"
    (let [result (eval `(run-test function-missing))]
      (is (nil? result)))))

;; run_single_test.clj:26 [language]
(deftest reports-non-test-var
  (should-print-to-err #"^.*/not-a-test is not a test.*"
    (let [result (eval `(run-test not-a-test))]
      (is (nil? result)))))

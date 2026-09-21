;; DERIVED from test/clj/clojure/test_clojure/ns_libs.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.ns-libs (:use clojure.test))



;; ns_libs.clj:32 [language]
(deftest test-require
         (is (thrown? Exception (require :foo)))
         (is (thrown? Exception (require))))

;; ns_libs.clj:36 [language]
(deftest test-use
         (is (thrown? Exception (use :foo)))
         (is (thrown? Exception (use))))

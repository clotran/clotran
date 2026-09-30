;; DERIVED from upstream/clojure/test/clojure/test_clojure/ns_libs.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.ns-libs (:use clojure.test))



;; ns_libs.clj:32 [language]
(deftest test-require
         (is (thrown? clotran.host.exception (require :foo)))
         (is (thrown? clotran.host.exception (require))))

;; ns_libs.clj:36 [language]
(deftest test-use
         (is (thrown? clotran.host.exception (use :foo)))
         (is (thrown? clotran.host.exception (use))))

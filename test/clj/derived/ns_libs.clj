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

;; ns_libs.clj:40 [language]
(deftest reimporting-deftypes
  (let [inst1 (binding [*ns* *ns*]
                (eval '(do (ns exporter)
                           (defrecord ReimportMe [a])
                           (ns importer)
                           (import exporter.ReimportMe)
                           (ReimportMe. 1))))
        inst2 (binding [*ns* *ns*]
                (eval '(do (ns exporter)
                           (defrecord ReimportMe [a b])
                           (ns importer)
                           (import exporter.ReimportMe)
                           (ReimportMe. 1 2))))]
    (testing "you can reimport a changed class and see the changes"
      (is (= [:a] (keys inst1)))
      (is (= [:a :b] (keys inst2))))
    ;fragile tests, please fix
    #_(testing "you cannot import same local name from a different namespace"
      (is (thrown? clojure.lang.Compiler$CompilerException
                  #"ReimportMe already refers to: class exporter.ReimportMe in namespace: importer"
                  (binding [*ns* *ns*]
                    (eval '(do (ns exporter-2)
                               (defrecord ReimportMe [a b])
                               (ns importer)
                               (import exporter-2.ReimportMe)
                               (ReimportMe. 1 2)))))))))

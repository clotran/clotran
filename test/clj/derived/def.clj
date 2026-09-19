;; DERIVED from test/clj/clojure/test_clojure/def.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.def (:use clojure.test clojure.test-helper))



;; def.clj:13 [language]
(deftest defn-error-messages
  (testing "multiarity syntax invalid parameter declaration"
    (is (fails-with-cause? 
          clojure.lang.ExceptionInfo
          #"Call to clojure.core/defn did not conform to spec"
          (eval-in-temp-ns (defn foo (arg1 arg2))))))

  (testing "multiarity syntax invalid signature"
    (is (fails-with-cause? 
          clojure.lang.ExceptionInfo
          #"Call to clojure.core/defn did not conform to spec"
          (eval-in-temp-ns (defn foo 
                             ([a] 1)
                             [a b])))))

  (testing "assume single arity syntax"
    (is (fails-with-cause? 
          clojure.lang.ExceptionInfo
          #"Call to clojure.core/defn did not conform to spec"
          (eval-in-temp-ns (defn foo a)))))

  (testing "bad name"
    (is (fails-with-cause? 
          clojure.lang.ExceptionInfo
          #"Call to clojure.core/defn did not conform to spec"
          (eval-in-temp-ns (defn "bad docstring" testname [arg1 arg2])))))
         
  (testing "missing parameter/signature"
    (is (fails-with-cause? 
          clojure.lang.ExceptionInfo
          #"Call to clojure.core/defn did not conform to spec"
          (eval-in-temp-ns (defn testname)))))

  (testing "allow trailing map"
    (is (eval-in-temp-ns (defn a "asdf" ([a] 1) {:a :b}))))

  (testing "don't allow interleaved map"
    (is (fails-with-cause? 
          clojure.lang.ExceptionInfo
          #"Call to clojure.core/defn did not conform to spec"
          (eval-in-temp-ns (defn a "asdf" ([a] 1) {:a :b} ([] 1)))))))

;; def.clj:63 [language]
(deftest dynamic-redefinition
  ;; too many contextual things for this kind of caching to work...
  (testing "classes are never cached, even if their bodies are the same"
    (is (= :b
          (eval
            '(do
               (defmacro my-macro [] :a)
               (defn do-macro [] (my-macro))
               (defmacro my-macro [] :b)
               (defn do-macro [] (my-macro))
               (do-macro)))))))

;; def.clj:75 [language]
(deftest nested-dynamic-declaration
  (testing "vars :dynamic meta data is applied immediately to vars declared anywhere"
    (is (= 10
          (eval
            '(do
               (list
                 (declare ^:dynamic p)
                 (defn q [] @p))
               (binding [p (atom 10)]
                 (q))))))))

;; DERIVED from upstream/clojure/test/clojure/test_clojure/fn.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.fn (:use clojure.test))



;; fn.clj:14 [language]
(deftest fn-error-checking
  (testing "bad arglist"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn "a" a)))))

  (testing "treat first param as args"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn "a" [])))))

  (testing "looks like listy signature, but malformed declaration"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn (1))))))

  (testing "checks each signature"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn
                   ([a] 1)
                   ("a" 2))))))

  (testing "correct name but invalid args"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn a "a")))))

  (testing "first sig looks multiarity, rest of sigs should be lists"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn a
                   ([a] 1)
                   [a b])))))
  
  (testing "missing parameter declaration"
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn a))))
    (is (fails-with-cause? clotran.host.exception_info
          #"Call to clojure.core/fn did not conform to spec"
          (eval '(fn))))))

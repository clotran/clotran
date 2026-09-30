;; DERIVED from upstream/clojure/test/clojure/test_clojure/test.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.test (:use clojure.test))

(declare does-not-exist)

(declare ^:dynamic original-report)

(defn custom-report [data]
  (let [event (:type data)
        msg (:message data)
        expected (:expected data)
        actual (:actual data)
        passed (cond
                 (= event :fail) (= msg "Should fail")
                 (= event :pass) (= msg "Should pass")
                 (= event :error) (= msg "Should error")
                 :else true)]
    (if passed
      (original-report {:type :pass, :message msg,
                        :expected expected, :actual actual})
      (original-report {:type :fail, :message (str msg " but got " event)
                        :expected expected, :actual actual}))))

(defn test-ns-hook []
  (binding [original-report report
            report custom-report]
    (test-all-vars (find-ns 'clojure.test-clojure.test))))

;; test.clj:22 [language]
(deftest can-test-symbol
  (let [x true]
    (is x "Should pass"))
  (let [x false]
    (is x "Should fail")))

;; test.clj:28 [language]
(deftest can-test-boolean
  (is true "Should pass")
  (is false "Should fail"))

;; test.clj:32 [language]
(deftest can-test-nil
  (is nil "Should fail"))

;; test.clj:35 [language]
(deftest can-test-=
  (is (= 2 (+ 1 1)) "Should pass")
  (is (= 3 (+ 2 2)) "Should fail"))

;; test.clj:43 [language]
(deftest can-test-thrown
  (is (thrown? clotran.host.arithmetic_exception (/ 1 0)) "Should pass")
  ;; No exception is thrown:
  (is (thrown? clotran.host.exception (+ 1 1)) "Should fail")
  ;; Wrong class of exception is thrown:
  (is (thrown? clotran.host.arithmetic_exception (throw (clotran.host.runtime_exception.))) "Should error"))

;; test.clj:50 [language]
(deftest can-test-thrown-with-msg
  (is (thrown-with-msg? clotran.host.arithmetic_exception #"Divide by zero" (/ 1 0)) "Should pass")
  ;; Wrong message string:
  (is (thrown-with-msg? clotran.host.arithmetic_exception #"Something else" (/ 1 0)) "Should fail")
  ;; No exception is thrown:
  (is (thrown? clotran.host.exception (+ 1 1)) "Should fail")
  ;; Wrong class of exception is thrown:
  (is (thrown-with-msg? clotran.host.illegal_argument_exception #"Divide by zero" (/ 1 0)) "Should error"))

;; test.clj:59 [language]
(deftest can-catch-unexpected-exceptions
  (is (= 1 (throw (clotran.host.exception.))) "Should error"))

;; test.clj:70 [language]
(deftest can-test-regexps
  (is (re-matches #"^ab.*$" "abbabba") "Should pass")
  (is (re-matches #"^cd.*$" "abbabba") "Should fail")
  (is (re-find #"ab" "abbabba") "Should pass")
  (is (re-find #"cd" "abbabba") "Should fail"))

;; test.clj:84 [language]
(deftest #^{:has-meta true} can-add-metadata-to-tests
  (is (:has-meta (meta #'can-add-metadata-to-tests)) "Should pass"))

;; test.clj:126 [language]
(deftest clj-1588-symbols-in-are-isolated-from-test-clauses
  (binding [report original-report]
    (are [x y] (= x y)
      ((fn [x] (inc x)) 1) 2)))

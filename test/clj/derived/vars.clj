;; DERIVED from upstream/clojure/test/clojure/test_clojure/vars.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.vars (:use clojure.test))

(def ^:dynamic a)

(def stub-me :original)

(def ^:dynamic dynamic-var 1)

(defn sample [& args]
  0)

;; vars.clj:23 [language]
(deftest test-binding
  (are [x y] (= x y)
      (eval `(binding [a 4] a)) 4     ; regression in Clojure SVN r1370
  ))

;; vars.clj:84 [concurrency]
(deftest test-with-redefs-throw
  (let [p (promise)]
    (is (thrown? clotran.host.exception
      (with-redefs [stub-me :temp]
        (deliver p stub-me)
        (throw (clotran.host.exception. "simulated failure in with-redefs")))))
    (is (= :temp @p))
    (is (= :original stub-me))))

;; vars.clj:95 [language]
(deftest test-with-redefs-inside-binding
  (binding [dynamic-var 2]
    (is (= 2 dynamic-var))
    (with-redefs [dynamic-var 3]
      (is (= 2 dynamic-var))))
  (is (= 1 dynamic-var)))

;; vars.clj:105 [concurrency]
(deftest test-vars-apply-lazily
  (is (= 0 (deref (future (apply sample (range)))
                  1000 :timeout)))
  (is (= 0 (deref (future (apply #'sample (range)))
                  1000 :timeout))))

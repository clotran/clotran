;; DERIVED from upstream/clojure/test/clojure/test_clojure/volatiles.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.volatiles (:use clojure.test))



;; volatiles.clj:14 [language]
(deftest volatile-basics
  (let [vol (volatile! "abc")]
    (is (volatile? vol))
    (is (= "abc" @vol))
    (is (= "def" (vreset! vol "def")))
    (is (= "def" @vol))))

;; volatiles.clj:21 [language]
(deftest volatile-vswap!
  (let [vol (volatile! 10)]
    (is (= 11 (vswap! vol inc)))
    (is (= 11 @vol)))
  (let [vol (volatile! 10)]
    (is (= 20 (vswap! vol + 10)))
    (is (= 20 @vol)))
  (let [vol (volatile! 10)]
    (is (= 25 (vswap! vol + 10 5)))
    (is (= 25 @vol))))

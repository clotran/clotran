;; DERIVED from test/clj/clojure/test_clojure/vectors.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.vectors (:use clojure.test))

(defn =vec
  [expected v] (and (vector? v) (= expected v)))

;; vectors.clj:387 [language]
(deftest test-mapv
  (are [r c1] (=vec r (mapv + c1))
       [1 2 3] [1 2 3])
  (are [r c1 c2] (=vec r (mapv + c1 c2))
       [2 3 4] [1 2 3] (repeat 1))
  (are [r c1 c2 c3] (=vec r (mapv + c1 c2 c3))
       [3 4 5] [1 2 3] (repeat 1) (repeat 1))
  (are [r c1 c2 c3 c4] (=vec r (mapv + c1 c2 c3 c4))
       [4 5 6] [1 2 3] [1 1 1] [1 1 1] [1 1 1]))

;; vectors.clj:397 [language]
(deftest test-filterv
  (are [r c1] (=vec r (filterv even? c1))
       [] [1 3 5]
       [2 4] [1 2 3 4 5]))

;; vectors.clj:402 [language]
(deftest test-subvec
  (let [v1 (vec (range 100))
        v2 (subvec v1 50 57)]
    (is (thrown? IndexOutOfBoundsException (v2 -1)))
    (is (thrown? IndexOutOfBoundsException (v2 7)))
    (is (= (v1 50) (v2 0)))
    (is (= (v1 56) (v2 6)))))

;; vectors.clj:424 [language]
(deftest test-reduce-kv-vectors
  (is (= 25 (reduce-kv + 10 [2 4 6])))
  (is (= 25 (reduce-kv + 10 (subvec [0 2 4 6] 1)))))

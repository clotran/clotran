;; DERIVED from test/clj/clojure/test_clojure/vectors.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.vectors (:use clojure.test))

(defn =vec
  [expected v] (and (vector? v) (= expected v)))

(set! *warn-on-reflection* true)

;; vectors.clj:88 [language]
(deftest test-primitive-subvector-reduce
  ;; regression test for CLJ-1082
  (is (== 60 (let [prim-vec (into (vector-of :long) (range 1000))]
               (reduce + (subvec prim-vec 10 15))))))

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

;; vectors.clj:410 [language]
(deftest test-vec
  (is (= [1 2] (vec (first {1 2}))))
  (is (= [0 1 2 3] (vec [0 1 2 3])))
  (is (= [0 1 2 3] (vec (list 0 1 2 3))))
  (is (= [0 1 2 3] (vec (sorted-set 0 1 2 3))))
  (is (= [[1 2] [3 4]] (vec (sorted-map 1 2 3 4))))
  (is (= [0 1 2 3] (vec (range 4))))
  (is (= [\a \b \c \d] (vec "abcd")))
  (is (= [0 1 2 3] (vec (object-array (range 4)))))
  (is (= [1 2 3 4] (vec (eduction (map inc) (range 4)))))
  (is (= [0 1 2 3] (vec (reify clojure.lang.IReduceInit
                          (reduce [_ f start]
                            (reduce f start (range 4))))))))

;; vectors.clj:424 [language]
(deftest test-reduce-kv-vectors
  (is (= 25 (reduce-kv + 10 [2 4 6])))
  (is (= 25 (reduce-kv + 10 (subvec [0 2 4 6] 1)))))

;; vectors.clj:428 [language]
(deftest test-vector-eqv-to-non-counted-types
  (is (not= (range) [0 1 2]))
  (is (not= [0 1 2] (range)))
  (is (= [0 1 2] (take 3 (range))))
  (is (= [0 1 2] (new java.util.ArrayList [0 1 2])))
  (is (not= [1 2] (take 1 (cycle [1 2]))))
  (is (= [1 2 3 nil 4 5 6 nil] (eduction cat [[1 2 3 nil] [4 5 6 nil]]))))

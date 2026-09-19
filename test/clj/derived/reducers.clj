;; DERIVED from test/clj/clojure/test_clojure/reducers.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.reducers (:use clojure.test))

(defmacro defequivtest
  ;; f is the core fn, r is the reducers equivalent, rt is the reducible ->
  ;; coll transformer
  [name [f r rt] fns]
  `(deftest ~name
     (let [c# (range -100 1000)]
       (doseq [fn# ~fns]
         (is (= (~f fn# c#)
                (~rt (~r fn# c#))))))))

(defn reduced-at-probe
  [m p]
  (reduce-kv (fn [_ k v] (when (== p k) (reduced :foo))) nil m))

(defspec reduced-always-returns
  (fn [probe to-end]
    (let [len (+ probe to-end 1)
          nums (range len)
          m (zipmap nums nums)]
      (reduced-at-probe m probe)))
  [^{:tag `gen-num} probe ^{:tag `gen-num} to-end]
  (assert (= :foo %)))

;; reducers.clj:53 [language]
(deftest test-sorted-maps
  (let [m (into (sorted-map)
                '{1 a, 2 b, 3 c, 4 d})]
    (is (= "1a2b3c4d" (reduce-kv str "" m))
        "Sorted maps should reduce-kv in sorted order")
    (is (= 1 (reduce-kv (fn [acc k v]
                          (reduced (+ acc k)))
                        0 m))
        "Sorted maps should stop reduction when asked")))

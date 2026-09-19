;; DERIVED from test/clj/clojure/test_clojure/predicates.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.predicates (:use clojure.test))

(def myvar 42)

;; predicates.clj:126 [language]
(deftest test-type-preds
  (doseq [tp type-preds]
    (doseq [dt sample-data]
      (if (some #(= % (first dt)) (second tp))
        (is ((first tp) (second dt))
          (pr-str (list (get-fn-name (first tp)) (second dt))))
        (is (not ((first tp) (second dt)))
          (pr-str (list 'not (list (get-fn-name (first tp)) (second dt)))))))))

;; predicates.clj:139 [language]
(deftest test-string?-more
  (are [x] (not (string? x))
    (new java.lang.StringBuilder "abc")
    (new java.lang.StringBuffer "xyz")))

;; predicates.clj:168 [language]
(deftest test-preds
  (let [[preds & rows] pred-val-table]
    (doseq [row rows]
      (let [v (first row)]
        (dotimes [i (count row)]
          (is (= ((resolve (nth preds i)) v) (nth row i))
              (pr-str (list (nth preds i) v))))))))

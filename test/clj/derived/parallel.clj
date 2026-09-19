;; DERIVED from test/clj/clojure/test_clojure/parallel.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.parallel (:use clojure.test))

(def ^:dynamic *test-value* 1)

;; parallel.clj:26 [concurrency]
(deftest pmap-does-its-thing
  ;; regression fixed in r1218; was OutOfMemoryError
  (is (= '(1) (pmap inc [0]))))

;; parallel.clj:33 [concurrency]
(deftest future-fn-properly-retains-conveyed-bindings
  (let [a (atom [])]
    (binding [*test-value* 2]
      @(future (dotimes [_ 3]
                 ;; we need some binding to trigger binding pop
                 (binding [*print-dup* false]
                   (swap! a conj *test-value*))))
      (is (= [2 2 2] @a)))))

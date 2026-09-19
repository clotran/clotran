;; DERIVED from test/clj/clojure/test_clojure/clojure_walk.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.clojure-walk (:require [clojure.walk :as w]) (:use clojure.test))

(defrecord Foo [a b c])

(defrecord RM [a])

;; clojure_walk.clj:5 [language]
(deftest t-prewalk-replace
  (is (= (w/prewalk-replace {:a :b} [:a {:a :a} (list 3 :c :a)])
         [:b {:b :b} (list 3 :c :b)])))

;; clojure_walk.clj:9 [language]
(deftest t-postwalk-replace 
  (is (= (w/postwalk-replace {:a :b} [:a {:a :a} (list 3 :c :a)])
         [:b {:b :b} (list 3 :c :b)])))

;; clojure_walk.clj:13 [language]
(deftest t-stringify-keys
  (is (= (w/stringify-keys {:a 1, nil {:b 2 :c 3}, :d 4})
         {"a" 1, nil {"b" 2 "c" 3}, "d" 4})))

;; clojure_walk.clj:17 [language]
(deftest t-prewalk-order
  (is (= (let [a (atom [])]
           (w/prewalk (fn [form] (swap! a conj form) form)
                      [1 2 {:a 3} (list 4 [5])])
           @a)
         [[1 2 {:a 3} (list 4 [5])]
          1 2 {:a 3} [:a 3] :a 3 (list 4 [5])
          4 [5] 5])))

;; clojure_walk.clj:26 [language]
(deftest t-postwalk-order
  (is (= (let [a (atom [])]
           (w/postwalk (fn [form] (swap! a conj form) form)
                      [1 2 {:a 3} (list 4 [5])])
           @a)
         [1 2
          :a 3 [:a 3] {:a 3}
          4 5 [5] (list 4 [5])
          [1 2 {:a 3} (list 4 [5])]])))

;; clojure_walk.clj:61 [language]
(deftest walk-mapentry
  "Checks that walk preserves the MapEntry type. See CLJ-2031."
  (let [coll [:html {:a ["b" 1]} ""]
        f (fn [e] (if (and (vector? e) (not (map-entry? e))) (apply list e) e))]
    (is (= (list :html {:a (list "b" 1)} "") (w/postwalk f coll)))))

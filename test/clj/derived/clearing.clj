;; DERIVED from test/clj/clojure/test_clojure/clearing.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.clearing (:require [clojure.string :as str] [clojure.test :refer :all]))

(set! *warn-on-reflection* true)

(defn special-fn-field?
  [^String field-name]
  (or (= field-name "__meta")
    (str/starts-with? field-name "__cached_class__")
    (str/starts-with? field-name "const__")
    (str/ends-with? field-name "__")))

(defn private-field-value [^Object obj ^Field field]
  (. field (setAccessible true))
  (. field (get obj)))

(defn cleared?
  [fobj]
  (every? #(nil? (private-field-value fobj %)) (clearable-closed-overs fobj)))

(defn check-clear
  [f]
  (is (not (cleared? f)))
  (f)
  (cleared? f))

(defn consume [x] (doseq [_ x] _))

(defn call-and-keep [f] (f) f)

(defn repro [x]
  (if true (call-and-keep (^:once fn* [] (consume x)))))

;; clearing.clj:58 [language]
(deftest test-clearing
  (let [x :a]
    ;; base case
    (is (check-clear (^{:once true} fn* [] x)))

    ;; conditional above fn
    (when true
      (is (check-clear (^{:once true} fn* [] x))))
    (case x
      :a (is (check-clear (^{:once true} fn* [] x))))

    ;; loop above fn
    (loop []
      (is (check-clear (^{:once true} fn* [] x))))

    ;; conditional below fn
    (is (check-clear (^{:once true} fn* [] (when true x))))

    ;; loop below fn
    (is (not (check-clear (^{:once true} fn* [] (loop [] x)))))
    (is (not (check-clear (^{:once true} fn* [] (loop [] x) nil))))

    ;; recur in :once below fn
    (is (not (check-clear (^{:once true} fn* [] (if false (recur) x)))))
    ))

;; clearing.clj:84 [language]
(deftest test-nested
  (let [x :a]
    ;; nested fns
    (let [inner (^{:once true} fn* [] x)
          outer (fn* [] inner)]
      (is (not (check-clear outer))) ;; outer not :once
      (is (check-clear inner)))

    (let [inner (^{:once true} fn* [] x)
          outer (^{:once true} fn* [] inner)]
      (is (check-clear outer))
      (is (check-clear inner)))

    (let [inner (^{:once true} fn* [] x)
          middle (^{:once true} fn* [] inner)
          outer (^{:once true} fn* [] middle)]
      (is (check-clear outer))
      (is (check-clear middle))
      (is (check-clear inner)))))

;; clearing.clj:109 [language]
(deftest CLJ-2145-repro
  (let [f (repro (range 100))] ;; 1e9 to exhaust
    (is (cleared? f))))

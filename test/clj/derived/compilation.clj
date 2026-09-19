;; DERIVED from test/clj/clojure/test_clojure/compilation.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.compilation (:require [clojure.test-clojure.compilation.line-number-examples :as line]) (:use clojure.test [clojure.test-helper :only (should-not-reflect should-print-err-message)]))

(defn hinted
  (^String [])
  (^Integer [a])
  (^java.util.List [a & args]))

(defn ^String hinting-conflict ^Integer [])

(defn ^String legacy-hinting [])

(defprotocol HintedProtocol
  (hintedp ^String [a]
           ^Integer [a b]))

(defn primfn
  (^long [])
  (^double [a]))

(defspec test-munge-roundtrip
  munge-roundtrip
  [^{:tag clojure.test-clojure.compilation/gen-name} n]
  (assert (= n %)))

(defn ^{:tag 'long} hinted-primfn [^long x] x)

(defn unhinted-primfn [^long x] x)

(defrecord Y [a])

#clojure.test_clojure.compilation.Y[1]

(defrecord Y [b])

(deftype CLJ1399 [munged-field-name])

(def zf (fn rf [x] (lazy-seq (cons x (rf x)))))

;; compilation.clj:122 [language]
(deftest test-CLJ-671-regression
  (testing "that the presence of hints does not cause the compiler to infinitely loop"
    (letfn [(gcd [x y]
              (loop [x (long x) y (long y)]
                (if (== y 0)
                  x
                  (recur y ^Long(rem x y)))))]
      (is (= 4 (gcd 8 100))))))

;; compilation.clj:391 [language]
(deftest CLJ-1456-compiler-error-on-incorrect-number-of-parameters-to-throw
  (is (thrown? RuntimeException (eval '(defn foo [] (throw)))))
  (is (thrown? RuntimeException (eval '(defn foo [] (throw RuntimeException any-symbol)))))
  (is (thrown? RuntimeException (eval '(defn foo [] (throw (RuntimeException.) any-symbol)))))
  (is (var? (eval '(defn foo [] (throw (IllegalArgumentException.)))))))

;; compilation.clj:397 [language]
(deftest clj-1809
  (is (eval `(fn [y#]
               (try
                 (finally
                   (let [z# y#])))))))

;; compilation.clj:413 [language]
(deftest test-anon-recursive-fn
  (is (= [0 0] (take 2 ((fn rf [x] (lazy-seq (cons x (rf x)))) 0))))
  (is (= [0 0] (take 2 (zf 0)))))

;; compilation.clj:436 [language]
(deftest CLJ-2284
  (testing "CLJ-2284 Can call static methods on interfaces"
    (is (= 42 (compilation.JDK8InterfaceMethods/staticMethod0 42)))
    (is (= "test" (compilation.JDK8InterfaceMethods/staticMethod1 "test")))
    (is (= 1 (if (compilation.JDK8InterfaceMethods/staticMethod2 true) 1 2)))))

;; compilation.clj:442 [language]
(deftest CLJ-2580
  (testing "CLJ-2580 Correctly calculate exit branches of case"
    (is (zero? (let [d (case nil :x nil 0)] d)))
    (is (nil? (let [d (case nil :x 0 nil)] d)))))

;; compilation.clj:447 [language]
(deftest CLJ-2945
  (testing "CLJ-2945 Reify form and obj meta"
    (are [m x]  (= (set (keys m)) x)
      (meta (reify clojure.lang.ILookup)) #{}
      (meta ^:foo (reify clojure.lang.ILookup)) #{:foo}
      (meta (macroexpand-1 '(reify clojure.lang.ILookup))) #{:line :column}
      (meta (macroexpand-1 '^:foo (reify clojure.lang.ILookup))) #{:line :column :foo})))

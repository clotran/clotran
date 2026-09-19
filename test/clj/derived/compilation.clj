;; DERIVED from test/clj/clojure/test_clojure/compilation.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.compilation (:require [clojure.test-clojure.compilation.line-number-examples :as line]) (:use clojure.test [clojure.test-helper :only (should-not-reflect should-print-err-message)]))

(defn hinted
  (^String [])
  (^Integer [a])
  (^java.util.List [a & args]))

(defn ^String hinting-conflict ^Integer [])

(defn ^String legacy-hinting [])

(defn primfn
  (^long [])
  (^double [a]))

(defn ^{:tag 'long} hinted-primfn [^long x] x)

(defn unhinted-primfn [^long x] x)

(defrecord Y [a])

(defrecord Y [b])

(deftype CLJ1399 [munged-field-name])

;; compilation.clj:58 [language]
(deftest test-compiler-resolution
  (testing "resolve nonexistent class create should return nil (assembla #262)"
    (is (nil? (resolve 'NonExistentClass.))))
  (testing "resolve nonexistent class should return nil"
    (is (nil? (resolve 'NonExistentClass.Name)))))

;; compilation.clj:388 [language]
(deftest CLJ-1586-lazyseq-literals-preserve-metadata
  (should-not-reflect (eval (list '.substring (with-meta (concat '(identity) '("foo")) {:tag 'String}) 0))))

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

;; compilation.clj:430 [language]
(deftest clj-1714
  (testing "CLJ-1714 Classes shouldn't have their static initialisers called simply by type hinting or importing"
    ;; ClassWithFailingStaticInitialiser will throw if its static initialiser is called
    (is (eval '(fn [^compilation.ClassWithFailingStaticInitialiser c])))
    (is (eval '(import (compilation ClassWithFailingStaticInitialiser))))))

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

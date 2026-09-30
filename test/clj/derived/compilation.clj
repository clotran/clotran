;; DERIVED from upstream/clojure/test/clojure/test_clojure/compilation.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.compilation (:require [clojure.test-clojure.compilation.line-number-examples :as line]) (:use clojure.test [clojure.test-helper :only (should-not-reflect should-print-err-message)]))

(defn ^clotran.host.string legacy-hinting [])

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

;; compilation.clj:391 [language]
(deftest CLJ-1456-compiler-error-on-incorrect-number-of-parameters-to-throw
  (is (thrown? clotran.host.runtime_exception (eval '(defn foo [] (throw)))))
  (is (thrown? clotran.host.runtime_exception (eval '(defn foo [] (throw clotran.host.runtime_exception any-symbol)))))
  (is (thrown? clotran.host.runtime_exception (eval '(defn foo [] (throw (clotran.host.runtime_exception.) any-symbol)))))
  (is (var? (eval '(defn foo [] (throw (clotran.host.illegal_argument_exception.)))))))

;; compilation.clj:397 [language]
(deftest clj-1809
  (is (eval `(fn [y#]
               (try
                 (finally
                   (let [z# y#])))))))

;; compilation.clj:442 [language]
(deftest CLJ-2580
  (testing "CLJ-2580 Correctly calculate exit branches of case"
    (is (zero? (let [d (case nil :x nil 0)] d)))
    (is (nil? (let [d (case nil :x 0 nil)] d)))))

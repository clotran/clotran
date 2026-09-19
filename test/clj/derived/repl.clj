;; DERIVED from test/clj/clojure/test_clojure/repl.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.repl (:use clojure.test [clojure.test-helper :only [platform-newlines]] clojure.test-clojure.repl.example) (:require [clojure.string :as str]))

(defmacro call-ns 
  "Call ns with a unique namespace name. Return the result of calling ns"
  []  `(ns a#))

(defmacro call-ns-sym 
  "Call ns wih a unique namespace name. Return the namespace symbol."
  [] `(do (ns a#) 'a#))

;; repl.clj:57 [language]
(deftest test-dynamic-ns
  (testing "a call to ns returns nil"
   (is (= nil (call-ns))))
  (testing "requiring a dynamically created ns should not throw an exception"
    (is (= nil (let [a (call-ns-sym)] (require a))))))

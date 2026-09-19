;; DERIVED from test/clj/clojure/test_clojure/repl.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.repl (:use clojure.test [clojure.test-helper :only [platform-newlines]] clojure.test-clojure.repl.example) (:require [clojure.string :as str]))



;; repl.clj:8 [language]
(deftest test-doc
  (testing "with namespaces"
    (is (= "clojure.pprint"
           (second (str/split-lines (with-out-str (doc clojure.pprint)))))))
  (testing "with special cases"
    (is (= (with-out-str (doc catch)) (with-out-str (doc try))))))

;; repl.clj:20 [language]
(deftest test-source-read-eval-unknown
  (is (thrown? IllegalStateException (binding [*read-eval* :unknown] (source reduce)))))

;; repl.clj:23 [language]
(deftest test-source-read-eval-false
  (is (binding [*read-eval* false] (with-out-str (source reduce)))))

;; repl.clj:33 [language]
(deftest test-apropos
  (testing "with a regular expression"
    (is (= '[clojure.core/defmacro] (apropos #"^defmacro$")))
    (is (some #{'clojure.core/defmacro} (apropos #"def.acr.")))
    (is (= [] (apropos #"nothing-has-this-name"))))

  (testing "with a string"
    (is (some #{'clojure.core/defmacro} (apropos "defmacro")))
    (is (some #{'clojure.core/defmacro} (apropos "efmac")))
    (is (= [] (apropos "nothing-has-this-name"))))

  (testing "with a symbol"
    (is (some #{'clojure.core/defmacro} (apropos 'defmacro)))
    (is (some #{'clojure.core/defmacro} (apropos 'efmac)))
    (is (= [] (apropos 'nothing-has-this-name)))))

;; repl.clj:57 [language]
(deftest test-dynamic-ns
  (testing "a call to ns returns nil"
   (is (= nil (call-ns))))
  (testing "requiring a dynamically created ns should not throw an exception"
    (is (= nil (let [a (call-ns-sym)] (require a))))))

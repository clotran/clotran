;; DERIVED from test/clj/clojure/test_clojure/parse.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.parse (:require [clojure.test :refer :all]))



;; parse.clj:10 [language]
(deftest test-parse-long
  (are [s expected]
    (= expected (parse-long s))
    "100" 100
    "+100" 100
    "0" 0
    "+0" 0
    "-0" 0
    "-42" -42
    "9223372036854775807" Long/MAX_VALUE
    "+9223372036854775807" Long/MAX_VALUE
    "-9223372036854775808" Long/MIN_VALUE
    "077" 77) ;; leading 0s are ignored! (not octal)

  (are [s] ;; do not parse
    (nil? (parse-long s))
    "0.3" ;; no float
    "9223372036854775808" ;; past max long
    "-9223372036854775809" ;; past min long
    "0xA0" ;; no hex
    "2r010")) ;; no radix support

;; parse.clj:86 [language]
(deftest test-parse-boolean
  (is (identical? true (parse-boolean "true")))
  (is (identical? false (parse-boolean "false")))

  (are [s] ;; nil on invalid string
    (nil? (parse-boolean s))
    "abc"
    "TRUE"
    "FALSE"
    " true ")

  (are [s] ;; throw on invalid type (not string)
    (try (parse-boolean s) (is false) (catch Throwable _ (is true)))
    nil
    false
    true
    100))

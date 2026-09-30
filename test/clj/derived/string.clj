;; DERIVED from upstream/clojure/test/clojure/test_clojure/string.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.string (:require [clojure.string :as s]) (:use clojure.test))



;; string.clj:7 [language]
(deftest t-split
  (is (= ["a" "b"] (s/split "a-b" #"-")))
  (is (= ["a" "b-c"] (s/split "a-b-c" #"-" 2)))
  (is (vector? (s/split "abc" #"-"))))

;; string.clj:12 [language]
(deftest t-reverse
  (is (= "tab" (s/reverse "bat"))))

;; string.clj:15 [language]
(deftest t-replace
  (is (= "faabar" (s/replace "foobar" \o \a)))
  (is (= "foobar" (s/replace "foobar" \z \a)))
  (is (= "barbarbar" (s/replace "foobarfoo" "foo" "bar")))
  (is (= "foobarfoo" (s/replace "foobarfoo" "baz" "bar")))
  (is (= "f$$d" (s/replace "food" "o" "$")))
  (is (= "f\\\\d" (s/replace "food" "o" "\\")))
  (is (= "barbarbar" (s/replace "foobarfoo" #"foo" "bar")))
  (is (= "foobarfoo" (s/replace "foobarfoo" #"baz" "bar")))
  (is (= "f$$d" (s/replace "food" #"o" (s/re-quote-replacement "$"))))
  (is (= "f\\\\d" (s/replace "food" #"o" (s/re-quote-replacement "\\"))))
  (is (= "FOObarFOO" (s/replace "foobarfoo" #"foo" s/upper-case)))
  (is (= "foobarfoo" (s/replace "foobarfoo" #"baz" s/upper-case)))
  (is (= "OObarOO" (s/replace "foobarfoo" #"f(o+)" (fn [[m g1]] (s/upper-case g1)))))
  (is (= "baz\\bang\\" (s/replace "bazslashbangslash" #"slash" (constantly "\\")))))

;; string.clj:31 [language]
(deftest t-replace-first
  (is (= "faobar" (s/replace-first "foobar" \o \a)))
  (is (= "foobar" (s/replace-first "foobar" \z \a)))
  (is (= "z.ology" (s/replace-first "zoology" \o \.)))
  (is (= "barbarfoo" (s/replace-first "foobarfoo" "foo" "bar")))
  (is (= "foobarfoo" (s/replace-first "foobarfoo" "baz" "bar")))
  (is (= "f$od" (s/replace-first "food" "o" "$")))
  (is (= "f\\od" (s/replace-first "food" "o" "\\")))
  (is (= "barbarfoo" (s/replace-first "foobarfoo" #"foo" "bar")))
  (is (= "foobarfoo" (s/replace-first "foobarfoo" #"baz" "bar")))
  (is (= "f$od" (s/replace-first "food" #"o" (s/re-quote-replacement "$"))))
  (is (= "f\\od" (s/replace-first "food" #"o" (s/re-quote-replacement "\\"))))
  (is (= "FOObarfoo" (s/replace-first "foobarfoo" #"foo" s/upper-case)))
  (is (= "foobarfoo" (s/replace-first "foobarfoo" #"baz" s/upper-case)))
  (is (= "OObarfoo" (s/replace-first "foobarfoo" #"f(o+)" (fn [[m g1]] (s/upper-case g1)))))
  (is (= "baz\\bangslash" (s/replace-first "bazslashbangslash" #"slash" (constantly "\\")))))

;; string.clj:48 [language]
(deftest t-join
  (are [x coll] (= x (s/join coll))
       "" nil
       "" []
       "1" [1]
       "12" [1 2])
  (are [x sep coll] (= x (s/join sep coll))
       "1,2,3" \, [1 2 3]
       "" \, []
       "1" \, [1]
       "1 and-a 2 and-a 3" " and-a " [1 2 3]))

;; string.clj:60 [language]
(deftest t-trim-newline
  (is (= "foo" (s/trim-newline "foo\n")))
  (is (= "foo" (s/trim-newline "foo\r\n")))
  (is (= "foo" (s/trim-newline "foo")))
  (is (= "" (s/trim-newline ""))))

;; string.clj:66 [language]
(deftest t-capitalize
  (is (= "Foobar" (s/capitalize "foobar")))
  (is (= "Foobar" (s/capitalize "FOOBAR"))))

;; string.clj:70 [language]
(deftest t-triml
  (is (= "foo " (s/triml " foo ")))
  (is (= "" (s/triml "   ")))
  (is (= "bar" (s/triml "\u2002 \tbar"))))

;; string.clj:75 [language]
(deftest t-trimr
  (is (= " foo" (s/trimr " foo ")))
  (is (= "" (s/trimr "   ")))
  (is (= "bar" (s/trimr "bar\t \u2002"))))

;; string.clj:80 [language]
(deftest t-trim
  (is (= "foo" (s/trim "  foo  \r\n")))
  (is (= "bar" (s/trim "\u2000bar\t \u2002"))))

;; string.clj:84 [language]
(deftest t-upper-case
  (is (= "FOOBAR" (s/upper-case "Foobar"))))

;; string.clj:87 [language]
(deftest t-lower-case
  (is (= "foobar" (s/lower-case "FooBar"))))

;; string.clj:90 [language]
(deftest nil-handling
  (are [f args] (thrown? clotran.host.null_pointer_exception (apply f args))
       s/reverse [nil]
       s/replace [nil #"foo" "bar"]
       s/replace-first [nil #"foo" "bar"]
       s/re-quote-replacement [nil]
       s/capitalize [nil]
       s/upper-case [nil]
       s/lower-case [nil]
       s/split [nil #"-"]
       s/split [nil #"-" 1]
       s/trim [nil]
       s/triml [nil]
       s/trimr [nil]
       s/trim-newline [nil]))

;; string.clj:129 [language]
(deftest t-escape
  (is (= "&lt;foo&amp;bar&gt;"
         (s/escape "<foo&bar>" {\& "&amp;" \< "&lt;" \> "&gt;"})))
  (is (= " \\\"foo\\\" "
         (s/escape " \"foo\" " {\" "\\\""})))
  (is (= "faabor"
         (s/escape "foobar" {\a \o, \o \a}))))

;; string.clj:137 [language]
(deftest t-blank
  (is (s/blank? nil))
  (is (s/blank? ""))
  (is (s/blank? " "))
  (is (s/blank? " \t \n  \r "))
  (is (not (s/blank? "  foo  "))))

;; string.clj:144 [language]
(deftest t-split-lines
  (let [result (s/split-lines "one\ntwo\r\nthree")]
    (is (= ["one" "two" "three"] result))
    (is (vector? result)))
  (is (= (list "foo") (s/split-lines "foo"))))

;; string.clj:193 [language]
(deftest empty-collections
  (is (= "()" (str ())))
  (is (= "{}" (str {})))
  (is (= "[]" (str []))))

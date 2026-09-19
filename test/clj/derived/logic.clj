;; DERIVED from test/clj/clojure/test_clojure/logic.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.logic (:use clojure.test [clojure.test-helper :only (exception)]))



;; logic.clj:85 [language]
(deftest test-nil-punning
  (are [x y]  (= (if x :no :yes) y)
    (first []) :yes
    (next [1]) :yes
    (rest [1]) :no

    (butlast [1]) :yes

    (seq nil) :yes
    (seq []) :yes

    (sequence nil) :no
    (sequence []) :no

    (lazy-seq nil) :no
    (lazy-seq []) :no

    (filter #(> % 10) [1 2 3]) :no
    (map identity []) :no
    (apply concat []) :no

    (concat) :no
    (concat []) :no

    (reverse nil) :no
    (reverse []) :no

    (sort nil) :no
    (sort []) :no ))

;; logic.clj:116 [language]
(deftest test-and
  (are [x y] (= x y)
      (and) true
      (and true) true
      (and nil) nil
      (and false) false

      (and true nil) nil
      (and true false) false

      (and 1 true :kw 'abc "abc") "abc"

      (and 1 true :kw nil 'abc "abc") nil
      (and 1 true :kw nil (exception) 'abc "abc") nil

      (and 1 true :kw 'abc "abc" false) false
      (and 1 true :kw 'abc "abc" false (exception)) false ))

;; logic.clj:135 [language]
(deftest test-or
  (are [x y] (= x y)
      (or) nil
      (or true) true
      (or nil) nil
      (or false) false

      (or nil false true) true
      (or nil false 1 2) 1
      (or nil false "abc" :kw) "abc"

      (or false nil) nil
      (or nil false) false
      (or nil nil nil false) false

      (or nil true false) true
      (or nil true (exception) false) true
      (or nil false "abc" (exception)) "abc" ))

;; logic.clj:155 [language]
(deftest test-not
;  (is (thrown? IllegalArgumentException (not)))
  (are [x] (= (not x) true)
      nil
      false )
  (are [x]  (= (not x) false)
      true

      ; numbers
      0
      0.0
      42
      1.2
      0/2
      2/3

      ; characters
      \space
      \tab
      \a

      ; strings
      ""
      "abc"

      ; regexes
      #""
      #"a*b"

      ; symbols
      (symbol "")
      'abc

      ; keywords
      :kw

      ; collections/arrays
      ()
      '(1 2)
      []
      [1 2]
      {}
      {:a 1 :b 2}
      #{}
      #{1 2}
      (into-array [])
      (into-array [1 2])

      ; Java objects
      (new java.util.Date) ))

;; logic.clj:206 [language]
(deftest test-some?
  (are [expected x] (= expected (some? x))
       false nil
       true false
       true 0
       true "abc"
       true []))

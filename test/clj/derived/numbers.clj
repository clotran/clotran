;; DERIVED from upstream/clojure/test/clojure/test_clojure/numbers.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.numbers (:use clojure.test clojure.template) (:require [clojure.test-helper :as helper]))

(defonce DELTA 1e-12)

(defn longable?
  [n]
  (try
   (long n)
   true
   (catch clotran.host.exception _)))

;; numbers.clj:154 [language]
(deftest unchecked-cast-char
  ; in keeping with the checked cast functions, char and Character can only be cast to int
  (is (unchecked-int (char 0xFFFF)))
  (is (let [c (char 0xFFFF)] (unchecked-int c)))) ; force primitive char

;; numbers.clj:194 [language]
(deftest test-add
  (are [x y] (= x y)
      (+) 0
      (+ 1) 1
      (+ 1 2) 3
      (+ 1 2 3) 6

      (+ -1) -1
      (+ -1 -2) -3
      (+ -1 +2 -3) -2

      (+ 1 -1) 0
      (+ -1 1) 0

      (+ 2/3) 2/3
      (+ 2/3 1) 5/3
      (+ 2/3 1/3) 1 )

  (are [x y] (< (- x y) DELTA)
      (+ 1.2) 1.2
      (+ 1.1 2.4) 3.5
      (+ 1.1 2.2 3.3) 6.6 )

  (is (> (+ clotran.host.int4/MAX_VALUE 10) clotran.host.int4/MAX_VALUE))  ; no overflow
  (is (thrown? clotran.host.class_cast_exception (+ "ab" "cd"))) )    ; no string concatenation

;; numbers.clj:221 [language]
(deftest test-subtract
  (is (thrown? clotran.host.illegal_argument_exception (-)))
  (are [x y] (= x y)
      (- 1) -1
      (- 1 2) -1
      (- 1 2 3) -4

      (- -2) 2
      (- 1 -2) 3
      (- 1 -2 -3) 6

      (- 1 1) 0
      (- -1 -1) 0

      (- 2/3) -2/3
      (- 2/3 1) -1/3
      (- 2/3 1/3) 1/3 )

  (are [x y] (< (- x y) DELTA)
      (- 1.2) -1.2
      (- 2.2 1.1) 1.1
      (- 6.6 2.2 1.1) 3.3 )

  (is (< (- clotran.host.int4/MIN_VALUE 10) clotran.host.int4/MIN_VALUE)) )  ; no underflow

;; numbers.clj:247 [language]
(deftest test-multiply
  (are [x y] (= x y)
      (*) 1
      (* 2) 2
      (* 2 3) 6
      (* 2 3 4) 24

      (* -2) -2
      (* 2 -3) -6
      (* 2 -3 -1) 6

      (* 1/2) 1/2
      (* 1/2 1/3) 1/6
      (* 1/2 1/3 -1/4) -1/24 )

  (are [x y] (< (- x y) DELTA)
      (* 1.2) 1.2
      (* 2.0 1.2) 2.4
      (* 3.5 2.0 1.2) 8.4 )

  (is (> (* 3 (int (/ clotran.host.int4/MAX_VALUE 2.0))) clotran.host.int4/MAX_VALUE)) )  ; no overflow

;; numbers.clj:280 [language]
(deftest test-ratios-simplify-to-ints-where-appropriate
  (testing "negative denominator (assembla #275)"
    (is (integer? (/ 1 -1/2)))
    (is (integer? (/ 0 -1/2)))))

;; numbers.clj:285 [language]
(deftest test-divide
  (are [x y] (= x y)
      (/ 1) 1
      (/ 2) 1/2
      (/ 3 2) 3/2
      (/ 4 2) 2
      (/ 24 3 2) 4
      (/ 24 3 2 -1) -4

      (/ -1) -1
      (/ -2) -1/2
      (/ -3 -2) 3/2
      (/ -4 -2) 2
      (/ -4 2) -2 )

  (are [x y] (< (- x y) DELTA)
      (/ 4.5 3) 1.5
      (/ 4.5 3.0 3.0) 0.5 )

  (is (thrown? clotran.host.arithmetic_exception (/ 0)))
  (is (thrown? clotran.host.arithmetic_exception (/ 2 0)))
  (is (thrown? clotran.host.illegal_argument_exception (/))) )

;; numbers.clj:327 [language]
(deftest test-mod
  ; wrong number of args
;  (is (thrown? IllegalArgumentException (mod)))
;  (is (thrown? IllegalArgumentException (mod 1)))
;  (is (thrown? IllegalArgumentException (mod 3 2 1)))

  ; divide by zero
  (is (thrown? clotran.host.arithmetic_exception (mod 9 0)))
  (is (thrown? clotran.host.arithmetic_exception (mod 0 0)))

  (are [x y] (= x y)
    (mod 4 2) 0
    (mod 3 2) 1
    (mod 6 4) 2
    (mod 0 5) 0

    (mod 2 1/2) 0
    (mod 2/3 1/2) 1/6
    (mod 1 2/3) 1/3

    (mod 4.0 2.0) 0.0
    (mod 4.5 2.0) 0.5

    ; |num| > |div|, num != k * div
    (mod 42 5) 2      ; (42 / 5) * 5 + (42 mod 5)        = 8 * 5 + 2        = 42
    (mod 42 -5) -3    ; (42 / -5) * (-5) + (42 mod -5)   = -9 * (-5) + (-3) = 42
    (mod -42 5) 3     ; (-42 / 5) * 5 + (-42 mod 5)      = -9 * 5 + 3       = -42
    (mod -42 -5) -2   ; (-42 / -5) * (-5) + (-42 mod -5) = 8 * (-5) + (-2)  = -42

    ; |num| > |div|, num = k * div
    (mod 9 3) 0       ; (9 / 3) * 3 + (9 mod 3) = 3 * 3 + 0 = 9
    (mod 9 -3) 0
    (mod -9 3) 0
    (mod -9 -3) 0

    ; |num| < |div|
    (mod 2 5) 2       ; (2 / 5) * 5 + (2 mod 5)        = 0 * 5 + 2          = 2
    (mod 2 -5) -3     ; (2 / -5) * (-5) + (2 mod -5)   = (-1) * (-5) + (-3) = 2
    (mod -2 5) 3      ; (-2 / 5) * 5 + (-2 mod 5)      = (-1) * 5 + 3       = -2
    (mod -2 -5) -2    ; (-2 / -5) * (-5) + (-2 mod -5) = 0 * (-5) + (-2)    = -2

    ; num = 0, div != 0
    (mod 0 3) 0       ; (0 / 3) * 3 + (0 mod 3) = 0 * 3 + 0 = 0
    (mod 0 -3) 0

    ; large args
    (mod 3216478362187432 432143214) 120355456
  )
)

;; numbers.clj:380 [language]
(deftest test-rem
  ; wrong number of args
;  (is (thrown? IllegalArgumentException (rem)))
;  (is (thrown? IllegalArgumentException (rem 1)))
;  (is (thrown? IllegalArgumentException (rem 3 2 1)))

  ; divide by zero
  (is (thrown? clotran.host.arithmetic_exception (rem 9 0)))
  (is (thrown? clotran.host.arithmetic_exception (rem 0 0)))
  
  (are [x y] (= x y)
    (rem 4 2) 0
    (rem 3 2) 1
    (rem 6 4) 2
    (rem 0 5) 0

    (rem 2 1/2) 0
    (rem 2/3 1/2) 1/6
    (rem 1 2/3) 1/3

    (rem 4.0 2.0) 0.0
    (rem 4.5 2.0) 0.5

    ; |num| > |div|, num != k * div
    (rem 42 5) 2      ; (8 * 5) + 2 == 42
    (rem 42 -5) 2     ; (-8 * -5) + 2 == 42
    (rem -42 5) -2    ; (-8 * 5) + -2 == -42
    (rem -42 -5) -2   ; (8 * -5) + -2 == -42

    ; |num| > |div|, num = k * div
    (rem 9 3) 0
    (rem 9 -3) 0
    (rem -9 3) 0
    (rem -9 -3) 0

    ; |num| < |div|
    (rem 2 5) 2
    (rem 2 -5) 2
    (rem -2 5) -2
    (rem -2 -5) -2
    
    ; num = 0, div != 0
    (rem 0 3) 0
    (rem 0 -3) 0
  )
)

;; numbers.clj:427 [language]
(deftest test-quot
  ; wrong number of args
;  (is (thrown? IllegalArgumentException (quot)))
;  (is (thrown? IllegalArgumentException (quot 1)))
;  (is (thrown? IllegalArgumentException (quot 3 2 1)))

  ; divide by zero
  (is (thrown? clotran.host.arithmetic_exception (quot 9 0)))
  (is (thrown? clotran.host.arithmetic_exception (quot 0 0)))
  
  (are [x y] (= x y)
    (quot 4 2) 2
    (quot 3 2) 1
    (quot 6 4) 1
    (quot 0 5) 0

    (quot 2 1/2) 4
    (quot 2/3 1/2) 1
    (quot 1 2/3) 1

    (quot 4.0 2.0) 2.0
    (quot 4.5 2.0) 2.0

    ; |num| > |div|, num != k * div
    (quot 42 5) 8     ; (8 * 5) + 2 == 42
    (quot 42 -5) -8   ; (-8 * -5) + 2 == 42
    (quot -42 5) -8   ; (-8 * 5) + -2 == -42
    (quot -42 -5) 8   ; (8 * -5) + -2 == -42

    ; |num| > |div|, num = k * div
    (quot 9 3) 3
    (quot 9 -3) -3
    (quot -9 3) -3
    (quot -9 -3) 3

    ; |num| < |div|
    (quot 2 5) 0
    (quot 2 -5) 0
    (quot -2 5) 0
    (quot -2 -5) 0

    ; num = 0, div != 0
    (quot 0 3) 0
    (quot 0 -3) 0
  )
)

;; numbers.clj:500 [language]
(deftest test-even?
  (are [x] (true? x)
    (even? -4)
    (not (even? -3))
    (even? 0)
    (not (even? 5))
    (even? 8))
  (is (thrown? clotran.host.illegal_argument_exception (even? 1/2)))
  (is (thrown? clotran.host.illegal_argument_exception (even? (double 10)))))

;; numbers.clj:510 [language]
(deftest test-odd?
  (are [x] (true? x)
    (not (odd? -4))
    (odd? -3)
    (not (odd? 0))
    (odd? 5)
    (not (odd? 8)))
  (is (thrown? clotran.host.illegal_argument_exception (odd? 1/2)))
  (is (thrown? clotran.host.illegal_argument_exception (odd? (double 10)))))

;; numbers.clj:568 [language]
(deftest test-bit-clear
  (is (= 2r1101 (bit-clear 2r1111 1)))
  (is (= 2r1101 (bit-clear 2r1101 1))))

;; numbers.clj:572 [language]
(deftest test-bit-set
  (is (= 2r1111 (bit-set 2r1111 1)))
  (is (= 2r1111 (bit-set 2r1101 1))))

;; numbers.clj:576 [language]
(deftest test-bit-flip
  (is (= 2r1101 (bit-flip 2r1111 1)))
  (is (= 2r1111 (bit-flip 2r1101 1))))

;; numbers.clj:580 [language]
(deftest test-bit-test
  (is (true? (bit-test 2r1111 1)))
  (is (false? (bit-test 2r1101 1))))

;; numbers.clj:660 [language]
(deftest test-abs
  (are [in ex] (= ex (abs in))
    -1 1
    1 1
    clotran.host.int8/MIN_VALUE clotran.host.int8/MIN_VALUE ;; special case!
    -1.0 1.0
    -0.0 0.0
    ##-Inf ##Inf
    ##Inf ##Inf
    -123.456M 123.456M
    -123N 123N
    -1/5 1/5)
  (is (NaN? (abs ##NaN))))

;; DERIVED from test/clj/clojure/test_clojure/math.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.math (:require [clojure.test :refer :all] [clojure.math :as m]))

(defn ulp=
  "Tests that y = x +/- m*ulp(x)"
  [x y ^double m]
  (let [mu (* (m/ulp x) m)]
    (<= (- x mu) y (+ x mu))))

;; math.clj:38 [language]
(deftest test-cos
  (is (NaN? (m/cos ##NaN)))
  (is (NaN? (m/cos ##-Inf)))
  (is (NaN? (m/cos ##Inf)))
  (is (= 1.0 (m/cos 0.0) (m/cos -0.0)))
  (is (ulp= (m/cos m/PI) (m/cos (- m/PI)) 1)))

;; math.clj:53 [language]
(deftest test-asin
  (is (NaN? (m/asin ##NaN)))
  (is (NaN? (m/asin 2.0)))
  (is (NaN? (m/asin -2.0)))
  (is (zero? (m/asin -0.0))))

;; math.clj:59 [language]
(deftest test-acos
  (is (NaN? (m/acos ##NaN)))
  (is (NaN? (m/acos -2.0)))
  (is (NaN? (m/acos 2.0)))
  (is (ulp= (* 2 (m/acos 0.0)) m/PI 1)))

;; math.clj:71 [language]
(deftest test-radians-degrees-roundtrip
  (doseq [d (range 0.0 360.0 5.0)]
    (is (ulp= (m/round d) (m/round (-> d m/to-radians m/to-degrees)) 1))))

;; math.clj:82 [language]
(deftest test-log
  (is (NaN? (m/log ##NaN)))
  (is (NaN? (m/log -1.0)))
  (is (= ##Inf (m/log ##Inf)))
  (is (= ##-Inf (m/log 0.0)))
  (is (ulp= (m/log m/E) 1.0 1)))

;; math.clj:89 [language]
(deftest test-log10
  (is (NaN? (m/log10 ##NaN)))
  (is (NaN? (m/log10 -1.0)))
  (is (= ##Inf (m/log10 ##Inf)))
  (is (= ##-Inf (m/log10 0.0)))
  (is (ulp= (m/log10 10) 1.0 1)))

;; math.clj:110 [language]
(deftest test-IEEE-remainder
  (is (NaN? (m/IEEE-remainder ##NaN 1.0)))
  (is (NaN? (m/IEEE-remainder 1.0 ##NaN)))
  (is (NaN? (m/IEEE-remainder ##Inf 2.0)))
  (is (NaN? (m/IEEE-remainder ##-Inf 2.0)))
  (is (NaN? (m/IEEE-remainder 2 0.0)))
  (is (= 1.0 (m/IEEE-remainder 5.0 4.0))))

;; math.clj:118 [language]
(deftest test-ceil
  (is (NaN? (m/ceil ##NaN)))
  (is (= ##Inf (m/ceil ##Inf)))
  (is (= ##-Inf (m/ceil ##-Inf)))
  (is (= 4.0 (m/ceil m/PI))))

;; math.clj:124 [language]
(deftest test-floor
  (is (NaN? (m/floor ##NaN)))
  (is (= ##Inf (m/floor ##Inf)))
  (is (= ##-Inf (m/floor ##-Inf)))
  (is (= 3.0 (m/floor m/PI))))

;; math.clj:178 [language]
(deftest test-round
  (is (= 0 (m/round ##NaN)))
  (is (= Long/MIN_VALUE (m/round ##-Inf)))
  (is (= Long/MIN_VALUE (m/round (- Long/MIN_VALUE 2.0))))
  (is (= Long/MAX_VALUE (m/round ##Inf)))
  (is (= Long/MAX_VALUE (m/round (+ Long/MAX_VALUE 2.0))))
  (is (= 4 (m/round 3.5))))

;; math.clj:186 [language]
(deftest test-add-exact
  (try
    (m/add-exact Long/MAX_VALUE 1)
    (is false)
    (catch ArithmeticException _
      (is true))))

;; math.clj:193 [language]
(deftest test-subtract-exact
  (try
    (m/subtract-exact Long/MIN_VALUE 1)
    (is false)
    (catch ArithmeticException _
      (is true))))

;; math.clj:200 [language]
(deftest test-multiply-exact
  (try
    (m/multiply-exact Long/MAX_VALUE 2)
    (is false)
    (catch ArithmeticException _
      (is true))))

;; math.clj:207 [language]
(deftest test-increment-exact
  (try
    (m/increment-exact Long/MAX_VALUE)
    (is false)
    (catch ArithmeticException _
      (is true))))

;; math.clj:214 [language]
(deftest test-decrement-exact
  (try
    (m/decrement-exact Long/MIN_VALUE)
    (is false)
    (catch ArithmeticException _
      (is true))))

;; math.clj:221 [language]
(deftest test-negate-exact
  (is (= (inc Long/MIN_VALUE) (m/negate-exact Long/MAX_VALUE)))
  (try
    (m/negate-exact Long/MIN_VALUE)
    (is false)
    (catch ArithmeticException _
      (is true))))

;; math.clj:229 [language]
(deftest test-floor-div
  (is (= Long/MIN_VALUE (m/floor-div Long/MIN_VALUE -1)))
  (is (= -1 (m/floor-div -2 5))))

;; math.clj:233 [language]
(deftest test-floor-mod
  (is (= 3 (m/floor-mod -2 5))))

;; math.clj:236 [language]
(deftest test-ulp
  (is (NaN? (m/ulp ##NaN)))
  (is (= ##Inf (m/ulp ##Inf)))
  (is (= ##Inf (m/ulp ##-Inf)))
  (is (= Double/MIN_VALUE (m/ulp 0.0)))
  (is (= (m/pow 2 971) (m/ulp Double/MAX_VALUE)))
  (is (= (m/pow 2 971) (m/ulp (- Double/MAX_VALUE)))))

;; math.clj:244 [language]
(deftest test-signum
  (is (NaN? (m/signum ##NaN)))
  (is (zero? (m/signum 0.0)))
  (is (zero? (m/signum -0.0)))
  (is (= 1.0 (m/signum 42.0)))
  (is (= -1.0 (m/signum -42.0))))

;; math.clj:251 [language]
(deftest test-sinh
  (is (NaN? (m/sinh ##NaN)))
  (is (= ##Inf (m/sinh ##Inf)))
  (is (= ##-Inf (m/sinh ##-Inf)))
  (is (= 0.0 (m/sinh 0.0))))

;; math.clj:257 [language]
(deftest test-cosh
  (is (NaN? (m/cosh ##NaN)))
  (is (= ##Inf (m/cosh ##Inf)))
  (is (= ##Inf (m/cosh ##-Inf)))
  (is (= 1.0 (m/cosh 0.0))))

;; math.clj:263 [language]
(deftest test-tanh
  (is (NaN? (m/tanh ##NaN)))
  (is (= 1.0 (m/tanh ##Inf)))
  (is (= -1.0 (m/tanh ##-Inf)))
  (is (= 0.0 (m/tanh 0.0))))

;; math.clj:269 [language]
(deftest test-hypot
  (is (= ##Inf (m/hypot 1.0 ##Inf)))
  (is (= ##Inf (m/hypot ##Inf 1.0)))
  (is (NaN? (m/hypot ##NaN 1.0)))
  (is (NaN? (m/hypot 1.0 ##NaN)))
  (is (= 13.0 (m/hypot 5.0 12.0))))

;; math.clj:276 [language]
(deftest test-expm1
  (is (NaN? (m/expm1 ##NaN)))
  (is (= ##Inf (m/expm1 ##Inf)))
  (is (= -1.0 (m/expm1 ##-Inf)))
  (is (= 0.0 (m/expm1 0.0))))

;; math.clj:289 [language]
(deftest test-copy-sign
  (is (= 1.0 (m/copy-sign 1.0 42.0)))
  (is (= -1.0 (m/copy-sign 1.0 -42.0)))
  (is (= -1.0 (m/copy-sign 1.0 ##-Inf))))

;; math.clj:310 [language]
(deftest test-next-up
  (is (NaN? (m/next-up ##NaN)))
  (is (= ##Inf (m/next-up ##Inf)))
  (is (= Double/MIN_VALUE (m/next-up 0.0))))

;; math.clj:315 [language]
(deftest test-next-down
  (is (NaN? (m/next-down ##NaN)))
  (is (= ##-Inf (m/next-down ##-Inf)))
  (is (= (- Double/MIN_VALUE) (m/next-down 0.0))))

(ns ftypes.oracle
  "Fortran's intrinsic types as an executable specification, in Clojure,
  run on real clj. The SECOND oracle (James, 2026-11-21): clotran's and
  Lemmis's types are Fortran's, so what a Fortran type does is decided
  here, not by clojure.core. This file is checked against gfortran and
  flang (scripts/ftypes-check); clotran is then checked against this file.

  A value is [kind x]: x is a Long in range for an integer kind, a Double
  holding exactly a binary32 or binary64 number for a real kind. Kinds are
  iso_fortran_env's: :int8 :int16 :int32 :int64 :real32 :real64. A real
  literal is a STRING, so it is rounded once, from its text, as Fortran
  rounds it. Where the standard leaves a result to the processor (integer
  overflow, division by zero, an inexact power, a value out of range), the
  oracle throws ex-info with {:undefined why}: those cases are not compared
  with the compilers, and an implementation must refuse them (clotran
  throws)."
  (:import (java.math BigDecimal BigInteger RoundingMode)))

(def kinds
  {:int8 {:type :integer :bits 8 :n 1}   :int16 {:type :integer :bits 16 :n 2}
   :int32 {:type :integer :bits 32 :n 4} :int64 {:type :integer :bits 64 :n 8}
   :real32 {:type :real :bits 32 :n 4}   :real64 {:type :real :bits 64 :n 8}})

;; the default kinds: gfortran and flang agree, the standard says only
;; "a processor-dependent kind"
(def default-integer :int32)
(def default-real :real32)

(defn int-kind? [k] (= :integer (:type (kinds k))))
(defn real-kind? [k] (= :real (:type (kinds k))))

(defn- undefined [why] (throw (ex-info (str "undefined: " why) {:undefined why})))
(defn- ill-typed [msg] (throw (ex-info (str "ill-typed: " msg) {:ill-typed msg})))

(defn- imax [k] (bigint (.subtract (.shiftLeft BigInteger/ONE (dec (:bits (kinds k)))) BigInteger/ONE)))
(defn- imin [k] (bigint (.negate (.shiftLeft BigInteger/ONE (dec (:bits (kinds k)))))))

(defn- fit
  "An exact integer, as a value of kind k, or undefined: integer overflow."
  [k x]
  (if (<= (imin k) x (imax k)) [k (long x)] (undefined :integer-overflow)))

(defn- rnd
  "A double, rounded to real kind k (binary32 by one more rounding of a
  binary64 result, exact for + - * / and sqrt of binary32 operands)."
  [k x]
  (let [d (double x)]
    (case k :real64 [k d] :real32 [k (double (float d))])))

(defn lit
  "A literal: [:int32 5], or [:real32 \"1.1\"] (a real as its text)."
  [[k x]]
  (if (int-kind? k)
    (fit k x)
    [k (case k :real64 (Double/parseDouble x) :real32 (double (Float/parseFloat x)))]))

(defn- conv
  "Value v converted to kind k (an assignment's or an operand's)."
  [k [k0 x]]
  (cond (= k k0) [k x]
        (and (int-kind? k) (int-kind? k0)) (fit k x)
        (and (real-kind? k) (int-kind? k0))
        [k (case k :real64 (double x) :real32 (double (float (long x))))]
        (and (real-kind? k) (real-kind? k0)) (rnd k x)
        :else (ill-typed (str "real to integer needs int, nint, floor or ceiling: " k0 " to " k))))

(defn promote
  "The kind of a mixed operation: integer with integer, the larger; real
  with real, the larger; integer with real, the real's kind."
  [k1 k2]
  (let [b #(:bits (kinds %))]
    (cond (and (int-kind? k1) (int-kind? k2)) (if (>= (b k1) (b k2)) k1 k2)
          (and (real-kind? k1) (real-kind? k2)) (if (>= (b k1) (b k2)) k1 k2)
          (int-kind? k1) k2
          :else k1)))

(defn- exact [x] (BigDecimal. (double x)))
(defn- finite! [x] (when (or (Double/isNaN x) (Double/isInfinite x)) (undefined :non-finite)) x)

(defn- arith [op [k1 a :as u] [k2 b :as v]]
  (let [k (promote k1 k2)
        x (second (conv k u))
        y (second (conv k v))]
    (if (int-kind? k)
      (fit k (case op
               + (+' (bigint x) (bigint y))
               - (-' (bigint x) (bigint y))
               * (*' (bigint x) (bigint y))
               / (if (zero? y) (undefined :division-by-zero) (quot (bigint x) (bigint y)))))
      (rnd k (case op + (+ x y) - (- x y) * (* x y) / (/ x y))))))

(defn- power [[k1 a :as u] [k2 b :as v]]
  (cond
    (and (int-kind? k1) (int-kind? k2))
    (let [k (promote k1 k2)]
      (cond (>= b 0) (fit k (loop [r 1N i b] (if (zero? i) r (recur (*' r (bigint a)) (dec i)))))
            (= a 1) (fit k 1)
            (= a -1) (fit k (if (even? b) 1 -1))
            (zero? a) (undefined :zero-to-negative-power)
            :else (fit k 0)))
    ;; x**2 is x*x everywhere; any other real power is processor dependent
    ;; (DEVIATIONS: FM062, 6.1.2 of F77), so it is undefined here
    (and (real-kind? k1) (int-kind? k2) (= b 2)) (arith '* u u)
    :else (undefined :inexact-power)))

(defn- need-same [who & vs]
  (when-not (apply = (map first vs)) (ill-typed (str who " needs one kind: " (mapv first vs)))))

(defn- kind-arg [args dflt] (if (seq args) (first args) dflt))

(defn- to-int [mode k [k0 x]]
  (if (int-kind? k0)
    (fit k x)
    (fit k (.toBigInteger (.setScale (exact (finite! x)) 0 mode)))))

(defn- fmod [[k a] [_ p]]
  (when (zero? p) (undefined :mod-by-zero))
  [k (double (.remainder (exact a) (exact p)))])

(declare ev)

(defn- call [op args]
  (let [vs (mapv #(if (keyword? %) % (ev %)) args)]
    (case op
      (+ - * /) (if (and (= op '-) (= 1 (count vs)))
                  (let [[k x] (first vs)] (if (int-kind? k) (fit k (-' (bigint x))) [k (- x)]))
                  (arith op (vs 0) (vs 1)))
      ** (power (vs 0) (vs 1))
      int (to-int RoundingMode/DOWN (kind-arg (rest vs) default-integer) (first vs))
      nint (to-int RoundingMode/HALF_UP (kind-arg (rest vs) default-integer) (first vs))
      floor (to-int RoundingMode/FLOOR (kind-arg (rest vs) default-integer) (first vs))
      ceiling (to-int RoundingMode/CEILING (kind-arg (rest vs) default-integer) (first vs))
      real (conv (kind-arg (rest vs) default-real) (first vs))
      dble (conv :real64 (first vs))
      abs (let [[k x] (first vs)] (if (int-kind? k) (fit k (clojure.core/abs (bigint x))) [k (Math/abs (double x))]))
      sqrt (let [[k x] (first vs)]
             (when-not (real-kind? k) (ill-typed "sqrt needs a real"))
             (when (neg? x) (undefined :sqrt-of-negative))
             (rnd k (Math/sqrt x)))
      mod (let [[a p] vs] (need-same 'mod a p)
            (if (int-kind? (first a))
              (if (zero? (second p)) (undefined :mod-by-zero) [(first a) (rem (second a) (second p))])
              (fmod a p)))
      modulo (let [[a p] vs] (need-same 'modulo a p)
               (if (int-kind? (first a))
                 (if (zero? (second p)) (undefined :mod-by-zero) [(first a) (mod (second a) (second p))])
                 (let [[k r] (fmod a p)
                       ex (if (and (not (zero? r)) (not= (neg? r) (neg? (second p))))
                            (.add (exact r) (exact (second p))) (exact r))]
                   (rnd k ex))))
      sign (let [[a b] vs] (need-same 'sign a b)
             (let [[k x] a [_ y] b]
               (if (int-kind? k)
                 (fit k (if (neg? y) (-' (clojure.core/abs (bigint x))) (clojure.core/abs (bigint x))))
                 [k (Math/copySign (Math/abs (double x)) (double y))])))
      (max min) (do (apply need-same op vs)
                    [(first (first vs)) (apply (if (= op 'max) max min) (map second vs))])
      huge (let [[k] (first vs)] (if (int-kind? k) [k (long (imax k))] [k (case k :real64 Double/MAX_VALUE :real32 (double Float/MAX_VALUE))]))
      tiny (let [[k] (first vs)] (when-not (real-kind? k) (ill-typed "tiny needs a real"))
             [k (case k :real64 Double/MIN_NORMAL :real32 (double Float/MIN_NORMAL))])
      epsilon (let [[k] (first vs)] (when-not (real-kind? k) (ill-typed "epsilon needs a real"))
                [k (case k :real64 (Math/ulp 1.0) :real32 (double (Math/ulp (float 1.0))))])
      kind [default-integer (:n (kinds (first (first vs))))]
      digits [default-integer (let [k (first (first vs))]
                                (if (int-kind? k) (dec (:bits (kinds k))) (case k :real32 24 :real64 53)))]
      (ill-typed (str "unknown operation " op)))))

(defn ev
  "The value of an expression: a literal [kind x], or (op args...)."
  [e]
  (cond (vector? e) (lit e)
        (seq? e) (call (first e) (rest e))
        :else (ill-typed (str "not an expression: " (pr-str e)))))

(defn run-case
  "[:ok kind x] | [:undefined why] | [:ill-typed msg]. x is a long or a double."
  [e]
  (try (let [[k x] (ev e)] [:ok k x])
       (catch clojure.lang.ExceptionInfo ex
         (let [d (ex-data ex)]
           (cond (:undefined d) [:undefined (:undefined d)]
                 (:ill-typed d) [:ill-typed (:ill-typed d)]
                 :else (throw ex))))))

(defn case-expr
  "A case is an expression, or {:undefined expr}: one the standard leaves to the processor."
  [c] (if (map? c) (:undefined c) c))

(defn run-file
  "Prints one EDN vector per case of the EDN file: the answers, in order."
  [path]
  (doseq [e (clojure.edn/read-string (slurp path))]
    (prn (run-case (case-expr e)))))

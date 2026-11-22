(ns ftypes.oracle
  "Fortran's intrinsic types as an executable specification, in Clojure,
  run on real clj. The SECOND oracle (James, 2026-11-21): clotran's and
  Lemmis's types are Fortran's, so what a Fortran type does is decided
  here, not by clojure.core. This file is checked against gfortran and
  flang (scripts/ftypes-check); clotran is then checked against this file.

  A value is [kind x]: x is a Long in range for an integer kind, a Double
  holding exactly a binary32 or binary64 number for a real kind. Kinds are
  iso_fortran_env's: :int1 :int2 :int4 :int8 :real4 :real8. A real
  literal is a STRING, so it is rounded once, from its text, as Fortran
  rounds it. Where the standard leaves a result to the processor (integer
  overflow, division by zero, an inexact power, a value out of range), the
  oracle throws ex-info with {:undefined why}: those cases are not compared
  with the compilers, and an implementation must refuse them (clotran
  throws)."
  (:require [ftypes.refmath :as rm]))

(def kinds
  {:int1 {:type :integer :bits 8 :n 1}   :int2 {:type :integer :bits 16 :n 2}
   :int4 {:type :integer :bits 32 :n 4} :int8 {:type :integer :bits 64 :n 8}
   :real4 {:type :real :bits 32 :n 4}   :real8 {:type :real :bits 64 :n 8}
   ;; complex(4) and complex(8): a value is [kind [re im]], each part a real of the part kind
   :complex4 {:type :complex :bits 64 :n 4 :part :real4} :complex8 {:type :complex :bits 128 :n 8 :part :real8}})

;; the default kinds: gfortran and flang agree, the standard says only
;; "a processor-dependent kind"
(def default-integer :int4)
(def default-real :real4)

(defn int-kind? [k] (= :integer (:type (kinds k))))
(defn real-kind? [k] (= :real (:type (kinds k))))
(defn complex-kind? [k] (= :complex (:type (kinds k))))
(def ^:private part-complex {:real4 :complex4 :real8 :complex8})

(defn- undefined [why] (throw (ex-info (str "undefined: " why) {:undefined why})))
(defn- ill-typed [msg] (throw (ex-info (str "ill-typed: " msg) {:ill-typed msg})))

(defn- pow2 [n] (loop [r 1N i n] (if (zero? i) r (recur (*' r 2) (dec i)))))
(defn- imax [k] (dec (pow2 (dec (:bits (kinds k))))))
(defn- imin [k] (-' (pow2 (dec (:bits (kinds k))))))

(defn- fit
  "An exact integer, as a value of kind k, or undefined: integer overflow."
  [k x]
  (if (<= (imin k) x (imax k)) [k (long x)] (undefined :integer-overflow)))

(defn- rnd
  "A double, rounded to real kind k (binary32 by one more rounding of a
  binary64 result, exact for + - * / and sqrt of binary32 operands)."
  [k x]
  (let [d (double x)]
    ;; .floatValue is the host's plain narrowing: infinity on overflow, as IEEE rounds; clojure.core's float
    ;; throws "Value out of range for float", which is Clojure's, not Fortran's
    (case k :real8 [k d] :real4 [k (double (.floatValue d))])))

(declare lit*)
(defn lit
  "A literal: [:int4 5], [:real4 \"1.1\"] (a real as its text), or [:complex8 [\"1.5\" \"2.5\"]]."
  [[k x]]
  (if (complex-kind? k)
    [k (mapv #(second (lit [(:part (kinds k)) %])) x)]
    (lit* [k x])))

(defn- lit* [[k x]]
  (if (int-kind? k)
    (fit k x)
    [k (case k :real8 (clotran.host.real8/parseDouble x) :real4 (double (clotran.host.real4/parseFloat x)))]))

(defn- conv
  "Value v converted to kind k (an assignment's or an operand's)."
  [k [k0 x]]
  (cond (= k k0) [k x]
        ;; to a complex kind: a real or integer is the real part, the imaginary part zero
        (and (complex-kind? k) (complex-kind? k0))
        [k (mapv #(second (rnd (:part (kinds k)) %)) x)]
        (complex-kind? k) [k [(second (conv (:part (kinds k)) [k0 x])) 0.0]]
        (complex-kind? k0) (ill-typed (str "a complex is not a " k " : use real, aimag or int of its part"))
        (and (int-kind? k) (int-kind? k0)) (fit k x)
        (and (real-kind? k) (int-kind? k0))
        [k (case k :real8 (double x) :real4 (double (float (long x))))]
        (and (real-kind? k) (real-kind? k0)) (rnd k x)
        :else (ill-typed (str "real to integer needs int, nint, floor or ceiling: " k0 " to " k))))

(defn promote
  "The kind of a mixed operation: integer with integer, the larger; real
  with real, the larger; integer with real, the real's kind."
  [k1 k2]
  (let [b #(:bits (kinds %))]
    (cond (or (complex-kind? k1) (complex-kind? k2))
          ;; the complex kind whose parts are as wide as the widest real part or real operand
          (let [part (fn [k] (cond (complex-kind? k) (:part (kinds k)) (real-kind? k) k))
                ps (remove nil? [(part k1) (part k2)])]
            (part-complex (apply max-key #(:bits (kinds %)) ps)))
          (and (int-kind? k1) (int-kind? k2)) (if (>= (b k1) (b k2)) k1 k2)
          (and (real-kind? k1) (real-kind? k2)) (if (>= (b k1) (b k2)) k1 k2)
          (int-kind? k1) k2
          :else k1)))

(defn- exact [x] (clotran.host.decimal. (double x)))
(defn- finite! [x] (when (or (clotran.host.real8/isNaN x) (clotran.host.real8/isInfinite x)) (undefined :non-finite)) x)

(declare arith*)
(defn- exact-part [x] (clotran.host.decimal. (double x)))

(defn- carith
  "Complex + - * /. + and - are IEEE on each part. * is the textbook (ac - bd) + (ad + bc)i and
  is defined only where every product and sum is exact (compilers differ otherwise: FCVS
  FM828-831, lemmis/model/SCOPE.md); / is processor dependent."
  [op u v]
  (let [k (promote (first u) (first v)) pk (:part (kinds k))
        [_ [a b]] (conv k u) [_ [c d]] (conv k v)
        r #(second (rnd pk %))]
    (case op
      + [k [(r (+ a c)) (r (+ b d))]]
      - [k [(r (- a c)) (r (- b d))]]
      * (let [E exact-part
              ac (.multiply (E a) (E c)) bd (.multiply (E b) (E d))
              ad (.multiply (E a) (E d)) bc (.multiply (E b) (E c))
              re (.subtract ac bd) im (.add ad bc)
              repr? (fn [x] (= x (E (r x))))]
          (if (every? repr? [ac bd ad bc re im])
            [k [(r re) (r im)]]
            (undefined :inexact-complex)))
      / (undefined :complex-division))))

(defn- arith [op [k1 a :as u] [k2 b :as v]]
  (if (or (complex-kind? k1) (complex-kind? k2))
    (carith op u v)
    (arith* op u v)))

(defn- arith* [op [k1 a :as u] [k2 b :as v]]
  (let [k (promote k1 k2)
        x (second (conv k u))
        y (second (conv k v))]
    (if (int-kind? k)
      (fit k (case op
               + (+' (bigint x) (bigint y))
               - (-' (bigint x) (bigint y))
               * (*' (bigint x) (bigint y))
               / (if (zero? y) (undefined :division-by-zero) (quot (bigint x) (bigint y)))))
      ;; primitive doubles: boxed, clojure.core's / throws "Divide by zero" for 0.0, where IEEE says
      ;; infinity (or NaN)
      (let [x (double x) y (double y)]
        (rnd k (case op + (+ x y) - (- x y) * (* x y) / (/ x y)))))))

(defn- power [[k1 a :as u] [k2 b :as v]]
  (cond
    (and (int-kind? k1) (int-kind? k2))
    (let [k (promote k1 k2)]
      (cond (and (>= b 0) (#{0 1 -1} a)) (fit k (cond (zero? b) 1 (= a -1) (if (even? b) 1 -1) :else a))
            ;; |a| >= 2: past 64 factors it has left every kind
            (>= b 0) (fit k (loop [r 1N i b] (if (or (zero? i) (> (abs r) (pow2 64))) r (recur (*' r (bigint a)) (dec i)))))
            (= a 1) (fit k 1)
            (= a -1) (fit k (if (even? b) 1 -1))
            (zero? a) (undefined :zero-to-negative-power)
            :else (fit k 0)))
    ;; a real to an integer power is x multiplied n times (1/x**|n| for a negative n): its value is
    ;; the processor's (a power function, or n-1 roundings in some order) unless every partial power is exact (FCVS FM062, lemmis/model/SCOPE.md), so
    ;; that is where it is defined; a real to a real power never is
    (and (real-kind? k1) (int-kind? k2))
    (cond (zero? b) [k1 (second (rnd k1 1.0))]
          (= b 1) [k1 a]
          ;; x**2 is one multiplication, correctly rounded on any IEEE processor, so always defined
          (= b 2) (arith '* u u)
          (> (clojure.core/abs b) 64) (undefined :inexact-power)
          (and (zero? a) (neg? b)) (undefined :zero-to-negative-power)
          :else
          (let [E exact
                n (clojure.core/abs b)
                partials (take n (iterate #(.multiply % (E a)) (E a)))
                ok? (fn [x] (= x (E (second (rnd k1 x)))))]
            (if (every? ok? partials)
              (let [pn (last partials)
                    v (if (neg? b) (try (.divide (clotran.host.decimal. "1") pn) (catch clotran.host.throwable _ nil)) pn)]
                (if (and v (ok? v)) (rnd k1 v) (undefined :inexact-power)))
              (undefined :inexact-power))))
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

(def ^:private elementary
  {'exp rm/exp* 'log rm/log* 'log10 rm/log10* 'sin rm/sin* 'cos rm/cos* 'tan rm/tan*
   'asin rm/asin* 'acos rm/acos* 'atan rm/atan* 'sinh rm/sinh* 'cosh rm/cosh* 'tanh rm/tanh*})

(defn- elem
  "EXP, LOG, SIN ...: the value to 80 digits (test/ftypes/refmath.clj), rounded once to the argument's
  kind. The standard gives no accuracy, so a result is checked within an ulp bound of this one; an
  argument outside the function's domain is the processor's."
  [op vs]
  (let [[k x] (first vs)]
    (when-not (real-kind? k) (ill-typed (str op " needs a real")))
    (finite! x)
    (when (and ('#{log log10} op) (not (pos? x))) (undefined :domain))
    (when (and ('#{asin acos} op) (clojure.core/> (clotran.host.math/abs x) 1.0)) (undefined :domain))
    [k (rm/round-to k ((elementary op) (rm/bd x)))]))

(defn- elem2
  "ATAN2(y, x) the same way."
  [vs]
  (apply need-same 'atan2 vs)
  (let [[[k y] [_ x]] vs]
    (when-not (real-kind? k) (ill-typed "atan2 needs reals"))
    (finite! y) (finite! x)
    (when (and (zero? x) (zero? y)) (undefined :domain))
    [k (rm/round-to k (rm/atan2* (rm/bd y) (rm/bd x)))]))

(defn- celem
  "EXP, LOG, SQRT, SIN, COS of a complex: each part to 80 digits (refmath's cexp* ...), rounded once to
  the part kind, so an implementation is checked within an ulp bound of each part. LOG of zero is
  undefined (the standard: X shall not be zero); a part not finite, the processor's."
  [op [k [a b]]]
  (finite! a) (finite! b)
  (when (and (= op 'log) (zero? a) (zero? b)) (undefined :domain))
  (let [pk (:part (kinds k))
        f ({'exp rm/cexp* 'log rm/clog* 'sqrt rm/csqrt* 'sin rm/csin* 'cos rm/ccos*} op)]
    [k (mapv #(rm/round-to pk %) (f a b))]))

;; TAN ASIN ACOS ATAN SINH COSH TANH of a complex are Fortran 2008's, not here yet (ill-typed); LOG10 and
;; ATAN2 of a complex are not Fortran
(def ^:private complex-ok '#{+ - * / ** abs real dble cmplx conjg aimag kind exp log sqrt csqrt sin cos})

(defn- call [op args]
  (let [vs (mapv #(if (keyword? %) % (ev %)) args)
        op (if (and (= op 'sqrt) (vector? (first vs)) (complex-kind? (first (first vs)))) 'csqrt op)]
    (when (and (some #(and (vector? %) (complex-kind? (first %))) vs) (not (complex-ok op)))
      (ill-typed (str op " of a complex")))
    (case op
      (exp log sin cos) (if (complex-kind? (first (first vs))) (celem op (first vs)) (elem op vs))
      (log10 tan asin acos atan sinh cosh tanh) (elem op vs)
      atan2 (elem2 vs)
      cmplx (let [k (kind-arg (drop 2 vs) :complex4) pk (:part (kinds k)) [x y] vs]
              (when-not (complex-kind? k) (ill-typed "cmplx's kind is a complex kind"))
              (if (complex-kind? (first x))
                (conv k x)
                [k [(second (conv pk x)) (if (keyword? y) 0.0 (second (conv pk y)))]]))
      conjg (let [[k [a b]] (first vs)] [k [a (- b)]])
      aimag (let [[k [a b]] (first vs)] [(:part (kinds k)) b])
      (+ - * /) (if (and (= op '-) (= 1 (count vs)))
                  (let [[k x] (first vs)]
                    (cond (int-kind? k) (fit k (-' (bigint x)))
                          (complex-kind? k) [k (mapv - x)]
                          :else [k (- x)]))
                  (arith op (vs 0) (vs 1)))
      ** (power (vs 0) (vs 1))
      ;; an array element of kind k assigned the value (the narrow kinds' aset): converted as an assignment
      ;; converts, so an integer out of the element's range is undefined
      store (let [[k v] vs]
              (when-not (or (and (int-kind? k) (int-kind? (first v))) (and (real-kind? k) (real-kind? (first v))))
                (ill-typed "store needs a value of the element's class"))
              (conv k v))
      ;; checked before sqrt's real case below
      csqrt (celem 'sqrt (first vs))
      int (to-int clotran.host.rounding_mode/DOWN (kind-arg (rest vs) default-integer) (first vs))
      nint (to-int clotran.host.rounding_mode/HALF_UP (kind-arg (rest vs) default-integer) (first vs))
      floor (to-int clotran.host.rounding_mode/FLOOR (kind-arg (rest vs) default-integer) (first vs))
      ceiling (to-int clotran.host.rounding_mode/CEILING (kind-arg (rest vs) default-integer) (first vs))
      real (let [[k x] (first vs)]
             (if (complex-kind? k)
               ;; REAL of a complex is its real part, of the PART's kind unless a kind says otherwise
               (conv (kind-arg (rest vs) (:part (kinds k))) [(:part (kinds k)) (first x)])
               (conv (kind-arg (rest vs) default-real) (first vs))))
      dble (let [[k x] (first vs)]
             (if (complex-kind? k) (conv :real8 [(:part (kinds k)) (first x)]) (conv :real8 (first vs))))
      abs (let [[k x] (first vs)]
            (if (complex-kind? k)
              ;; sqrt(a**2 + b**2) to 80 digits, rounded once to the part kind: checked within an ulp bound
              (let [pk (:part (kinds k)) [a b] x]
                (finite! a) (finite! b)
                [pk (rm/round-to pk (rm/cabs* a b))])
            (if (int-kind? k) (fit k (clojure.core/abs (bigint x))) [k (clotran.host.math/abs (double x))])))
      sqrt (let [[k x] (first vs)]
             (when-not (real-kind? k) (ill-typed "sqrt needs a real"))
             (when (neg? x) (undefined :sqrt-of-negative))
             (rnd k (clotran.host.math/sqrt x)))
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
                 [k (clotran.host.math/copySign (clotran.host.math/abs (double x)) (double y))])))
      ;; MAX and MIN of a NaN: the standard leaves it to the processor (gfortran answers the other one)
      (max min) (do (apply need-same op vs)
                    (when (some #(and (real-kind? (first %)) (clotran.host.real8/isNaN (second %))) vs) (undefined :nan-argument))
                    [(first (first vs)) (apply (if (= op 'max) max min) (map second vs))])
      huge (let [[k] (first vs)] (if (int-kind? k) [k (long (imax k))] [k (case k :real8 clotran.host.real8/MAX_VALUE :real4 (double clotran.host.real4/MAX_VALUE))]))
      tiny (let [[k] (first vs)] (when-not (real-kind? k) (ill-typed "tiny needs a real"))
             [k (case k :real8 clotran.host.real8/MIN_NORMAL :real4 (double clotran.host.real4/MIN_NORMAL))])
      epsilon (let [[k] (first vs)] (when-not (real-kind? k) (ill-typed "epsilon needs a real"))
                [k (case k :real8 (clotran.host.math/ulp 1.0) :real4 (double (clotran.host.math/ulp (float 1.0))))])
      kind [default-integer (:n (kinds (first (first vs))))]
      digits [default-integer (let [k (first (first vs))]
                                (if (int-kind? k) (dec (:bits (kinds k))) (case k :real4 24 :real8 53)))]
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
       (catch clotran.host.exception_info ex
         (let [d (ex-data ex)]
           (cond (:undefined d) [:undefined (:undefined d)]
                 (:ill-typed d) [:ill-typed (:ill-typed d)]
                 :else (throw ex))))))

(defn case-expr
  "A case is an expression; {:undefined expr}, one the standard leaves to the processor;
  {:processor expr}, the same, where compiled Fortran may answer with the processor's value; or
  {:interpreted expr}, one that is defined and that the pure Fortran tier may decline to lower;
  or {:ulp n :expr expr}, an elementary function, whose value an implementation may have within n
  units in the last place of the correctly rounded one this oracle computes."
  [c] (if (map? c) (or (:undefined c) (:processor c) (:interpreted c) (:expr c)) c))

(defn run-file
  "Prints one EDN vector per case of the EDN file: the answers, in order."
  [path]
  (doseq [e (clojure.edn/read-string (slurp path))]
    (prn (run-case (case-expr e)))))

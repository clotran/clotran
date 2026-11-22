(ns ftypes.refmath
  "Elementary functions to 80 significant digits: the REFERENCE the ulp checks measure gfortran,
  flang, fortran.ops and the compiled code against (test/ftypes/oracle.clj). The standard gives
  SIN, EXP, LOG and the rest no accuracy; what a processor gives is its libm's. Here the value
  is computed by series in decimal arithmetic far wider than any real kind and rounded ONCE to
  the kind, so it is the correctly rounded value, and a result's error is its distance from it
  in units in the last place. Plain Clojure on clj, like the oracle.")

;; the working precision, 80 digits; ftypes.accuracy recomputes a sample at more to check the reference
(def ^:dynamic *mc* (clotran.host.math_context. 80))
(def ^:dynamic *eps* (clotran.host.decimal. "1E-78"))
(defmacro with-digits "body with p digits" [p & body]
  `(binding [*mc* (clotran.host.math_context. ~p) *eps* (.scaleByPowerOfTen (clotran.host.decimal. 1) (- 2 ~p))] ~@body))

(defn bd "A double as the exact decimal it is." [x] (clotran.host.decimal. (double x)))
(defn- add [a b] (.add a b *mc*))
(defn- sub [a b] (.subtract a b *mc*))
(defn- mul [a b] (.multiply a b *mc*))
(defn- div [a b] (.divide a b *mc*))
(defn- tiny? [x] (neg? (.compareTo (.abs x) *eps*)))
(def ^:private two (clotran.host.decimal. 2))

(defn exp* [x]
  (let [s (loop [s 0 y (.abs x)] (if (neg? (.compareTo y (clotran.host.decimal. "0.5"))) s (recur (inc s) (div y two))))
        r (loop [i 0 v x] (if (= i s) v (recur (inc i) (div v two))))
        taylor (loop [term (clotran.host.decimal. 1) sum (clotran.host.decimal. 1) n 1]
                 (let [term (div (mul term r) (clotran.host.decimal. n)) sum (add sum term)]
                   (if (tiny? term) sum (recur term sum (inc n)))))]
    (loop [v taylor i 0] (if (= i s) v (recur (mul v v) (inc i))))))

(defn- halley-log [x]
  ;; Halley's iteration on exp from the double's log: cubic, so four steps from 16 digits pass 400
  (let [g (bd (clotran.host.math/log (double x)))]
    (loop [y g i 0]
      (if (= i 4)
        y
        (let [e (exp* y)] (recur (add y (div (mul two (sub x e)) (add x e))) (inc i)))))))
(def ^:private ln10 (memoize (fn [_] (halley-log (clotran.host.decimal. 10)))))
(defn log*
  "log x for any positive decimal: one outside the double range (a complex's |z|^2 of 1e600) as
  m * 10^e, log m + e log 10."
  [x]
  (let [e (- (.precision x) (.scale x) 1)]
    (if (< -300 e 300)
      (halley-log x)
      (add (halley-log (.movePointLeft x e)) (mul (clotran.host.decimal. e) (ln10 (.getPrecision *mc*)))))))
(defn log1p*
  "log (1 + t), t exact: near 0 as 2 atanh (t / (2 + t)), so a tiny t keeps its 80 digits."
  [t]
  (if (neg? (.compareTo (.abs t) (clotran.host.decimal. "0.5")))
    (let [u (div t (add two t)) u2 (mul u u)]
      (if (zero? (.signum u))
        u
        (loop [term u sum u n 1]
          (let [term (mul term u2) n (+ n 2) t (div term (clotran.host.decimal. n)) sum (add sum t)]
            (if (tiny? (div t sum)) (mul two sum) (recur term sum n))))))
    (log* (add (clotran.host.decimal. 1) t))))

(defn- atan-series [r]
  (let [r2 (mul r r)]
    (loop [term r sum r n 1 sgn -1]
      (let [term (mul term r2) n (+ n 2)
            t (div term (clotran.host.decimal. n))
            sum (if (neg? sgn) (sub sum t) (add sum t))]
        (if (tiny? t) sum (recur term sum n (- sgn)))))))

(def ^:private pi-hi
  ;; pi to 720 digits (Machin), for reducing an argument as large as the greatest real(8), 1.8e308:
  ;; the reduction keeps 20 more digits after the point than the working precision, of a quotient with
  ;; up to 309 before it
  (delay (let [m (clotran.host.math_context. 720) e (clotran.host.decimal. "1E-718") one (clotran.host.decimal. 1)
               at (fn [r] (let [r2 (.multiply r r m)]
                            (loop [term r sum r n 1 sgn -1]
                              (let [term (.multiply term r2 m) n (+ n 2)
                                    t (.divide term (clotran.host.decimal. n) m)
                                    sum (if (neg? sgn) (.subtract sum t m) (.add sum t m))]
                                (if (neg? (.compareTo (.abs t) e)) sum (recur term sum n (- sgn)))))))]
           (.subtract (.multiply (clotran.host.decimal. 16) (at (.divide one (clotran.host.decimal. 5) m)) m)
                      (.multiply (clotran.host.decimal. 4) (at (.divide one (clotran.host.decimal. 239) m)) m) m))))
(defn pi* "pi to the working precision" [] (.round @pi-hi *mc*))

(defn atan* [x]
  ;; halve the angle until the series converges quickly: atan x = 2 atan (x / (1 + sqrt (1 + x^2)))
  (let [one (clotran.host.decimal. 1)
        [r k] (loop [r x k 0]
                (if (neg? (.compareTo (.abs r) (clotran.host.decimal. "0.05")))
                  [r k]
                  (recur (div r (add one (.sqrt (add one (mul r r)) *mc*))) (inc k))))]
    (loop [v (atan-series r) i 0] (if (= i k) v (recur (mul v two) (inc i))))))

(defn atan2*
  "The angle of the point (x, y) in (-pi, pi]; y = 0 with x < 0 is +pi."
  [y x]
  (let [pi (pi*)]
    (cond (pos? (.signum x)) (atan* (div y x))
          (neg? (.signum x)) (if (neg? (.signum y)) (sub (atan* (div y x)) pi) (add (atan* (div y x)) pi))
          :else (if (pos? (.signum y)) (div pi two) (.negate (div pi two))))))

(defn- sincos [x]
  ;; x reduced into [-pi, pi] keeping 20 more digits after the point than the working precision,
  ;; whatever its size (so sin of 1e308, or of a real(8) within 1e-19 of a multiple of pi, keeps its 80
  ;; digits), then both series
  (let [m (clotran.host.math_context. (+ 20 (.getPrecision *mc*) (max 0 (- (.precision x) (.scale x)))))
        tau (.multiply two @pi-hi m)
        k (.setScale (.divide x tau m) 0 clotran.host.rounding_mode/HALF_EVEN)
        r (.round (.subtract x (.multiply k tau m) m) *mc*)
        r2 (mul r r)
        sin (loop [term r sum r n 1]
              (let [term (div (mul (.negate term) r2) (clotran.host.decimal. (* (inc n) (+ n 2)))) sum (add sum term) n (+ n 2)]
                (if (tiny? term) sum (recur term sum n))))
        cos (loop [term (clotran.host.decimal. 1) sum (clotran.host.decimal. 1) n 0]
              (let [term (div (mul (.negate term) r2) (clotran.host.decimal. (* (+ n 1) (+ n 2)))) sum (add sum term) n (+ n 2)]
                (if (tiny? term) sum (recur term sum n))))]
    [sin cos]))

(defn sin* [x] (first (sincos x)))
(defn cos* [x] (second (sincos x)))
(defn tan* [x] (let [[s c] (sincos x)] (div s c)))
(defn sinh* [x]
  ;; near zero (e - 1/e)/2 cancels (to 0 for x = 1e-300), so the series there
  (if (neg? (.compareTo (.abs x) (clotran.host.decimal. 1)))
    (if (zero? (.signum x)) x
    (let [x2 (mul x x)]
      (loop [term x sum x n 1]
        (let [term (div (mul term x2) (clotran.host.decimal. (* (inc n) (+ n 2)))) sum (add sum term)]
          (if (tiny? (div term sum)) sum (recur term sum (+ n 2)))))))
    (let [e (exp* x)] (div (sub e (div (clotran.host.decimal. 1) e)) two))))
(defn cosh* [x] (let [e (exp* x)] (div (add e (div (clotran.host.decimal. 1) e)) two)))
(defn tanh* [x]
  (if (neg? (.compareTo (.abs x) (clotran.host.decimal. 1)))
    (div (sinh* x) (cosh* x))
    (let [e (exp* (mul two x))] (div (sub e (clotran.host.decimal. 1)) (add e (clotran.host.decimal. 1))))))
(defn log10* [x] (div (log* x) (log* (clotran.host.decimal. 10))))
(defn asin* [x]
  (let [one (clotran.host.decimal. 1)]
    (if (zero? (.compareTo (.abs x) one))
      (if (pos? (.signum x)) (div (pi*) two) (.negate (div (pi*) two)))
      (atan* (div x (.sqrt (sub one (mul x x)) *mc*))))))
(defn acos* [x] (sub (div (pi*) two) (asin* x)))

;; Complex: a function of a + bi, a and b doubles (the parts of a complex(4) or complex(8)), answering
;; [re im], each a decimal, or a double where a zero's sign is the point (a decimal has no -0). Fortran
;; says only: LOG and SQRT are principal values, LOG's imaginary part in (-pi, pi], -pi only for a
;; negative real part and a -0 imaginary part; SQRT's real part >= 0, and where it is 0 the imaginary
;; part has the sign of b.
(defn- neg-sign? [x] (neg? (clotran.host.math/copySign 1.0 (double x))))
(defn- norm2 [a b] (.add (.multiply (bd a) (bd a)) (.multiply (bd b) (bd b))))   ; exact
(defn cabs* [a b] (.sqrt (norm2 a b) *mc*))
(defn cexp* [a b]
  (let [e (exp* (bd a))]
    (if (zero? b) [e b] (let [[s c] (sincos (bd b))] [(mul e c) (mul e s)]))))
(defn clog*
  "log z = log |z| + i arg z; log |z| = log1p(|z|^2 - 1) / 2 with |z|^2 - 1 exact, so z near the unit
  circle keeps its digits. z = 0 is the caller's to refuse."
  [a b]
  [(div (log1p* (.subtract (norm2 a b) (clotran.host.decimal. 1))) two)
   (cond (and (zero? b) (neg? a)) (if (neg-sign? b) (.negate (pi*)) (pi*))
         (zero? b) b
         :else (atan2* (bd b) (bd a)))])
(defn csqrt*
  "The principal square root, by halves that do not cancel: for a >= 0, re = sqrt((|z| + a)/2) and
  im = b / (2 re); for a < 0, |im| = sqrt((|z| - a)/2) with b's sign and re = |b| / (2 |im|)."
  [a b]
  (if (and (zero? a) (zero? b))
    [0.0 b]
    (let [m (cabs* a b)]
      (if (not (neg? a))
        (let [re (.sqrt (div (add m (bd a)) two) *mc*)] [re (if (zero? b) b (div (bd b) (mul two re)))])
        (let [t (.sqrt (div (sub m (bd a)) two) *mc*)]
          [(if (zero? b) 0.0 (div (.abs (bd b)) (mul two t))) (if (neg-sign? b) (.negate t) t)])))))
(defn csin* [a b] (let [[s c] (sincos (bd a))] [(mul s (cosh* (bd b))) (mul c (sinh* (bd b)))]))
(defn ccos* [a b] (let [[s c] (sincos (bd a))] [(mul c (cosh* (bd b))) (.negate (mul s (sinh* (bd b))))]))

(defn round-to
  "A decimal rounded ONCE to a real kind: a double holding the nearest real(4) or real(8), ties to
  even, past the greatest finite value plus half its last place infinity. The host's conversion is a
  candidate only: it is checked exactly against its two neighbours, so the reference does not rest on
  the host rounding a decimal correctly. A double (a signed zero) is its own value."
  [kind x]
  (if (double? x)
    (case kind :real8 x :real4 (double (unchecked-float x)))
    (let [f4 (= kind :real4)
          big (if f4 (double clotran.host.real4/MAX_VALUE) clotran.host.real8/MAX_VALUE)
          edge (.add (bd big) (.divide (bd (if f4 (double (clotran.host.math/ulp (float big))) (clotran.host.math/ulp big))) two))]
      (if (not (neg? (.compareTo (.abs x) edge)))
        (if (neg? (.signum x)) ##-Inf ##Inf)
        (let [c (if f4 (double (.floatValue x)) (.doubleValue x))
              c (if (clotran.host.real8/isInfinite c) (if (neg? c) (- big) big) c)
              nb (fn [g] (if f4 (double (g (float c))) (g c)))
              cands (filter #(not (clotran.host.real8/isInfinite %)) [c (nb clotran.host.math/nextUp) (nb clotran.host.math/nextDown)])
              dist (fn [y] (.abs (.subtract x (bd y))))
              odd (fn [y] (if f4 (odd? (clotran.host.real4/floatToIntBits (float y))) (odd? (clotran.host.real8/doubleToLongBits y))))]
          (first (sort-by (juxt dist odd) cands)))))))

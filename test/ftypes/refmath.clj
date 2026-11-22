(ns ftypes.refmath
  "Elementary functions to 80 significant digits: the REFERENCE the ulp checks measure gfortran,
  flang, fortran.ops and the compiled code against (test/ftypes/oracle.clj). The standard gives
  SIN, EXP, LOG and the rest no accuracy; what a processor gives is its libm's. Here the value
  is computed by series in decimal arithmetic far wider than any real kind and rounded ONCE to
  the kind, so it is the correctly rounded value, and a result's error is its distance from it
  in units in the last place. Plain Clojure on clj, like the oracle.")

(def ^:private mc (clotran.host.math_context. 80))
(def ^:private eps (clotran.host.decimal. "1E-78"))

(defn bd "A double as the exact decimal it is." [x] (clotran.host.decimal. (double x)))
(defn- add [a b] (.add a b mc))
(defn- sub [a b] (.subtract a b mc))
(defn- mul [a b] (.multiply a b mc))
(defn- div [a b] (.divide a b mc))
(defn- tiny? [x] (neg? (.compareTo (.abs x) eps)))
(def ^:private two (clotran.host.decimal. 2))

(defn exp* [x]
  (let [s (loop [s 0 y (.abs x)] (if (neg? (.compareTo y (clotran.host.decimal. "0.5"))) s (recur (inc s) (div y two))))
        r (loop [i 0 v x] (if (= i s) v (recur (inc i) (div v two))))
        taylor (loop [term (clotran.host.decimal. 1) sum (clotran.host.decimal. 1) n 1]
                 (let [term (div (mul term r) (clotran.host.decimal. n)) sum (add sum term)]
                   (if (tiny? term) sum (recur term sum (inc n)))))]
    (loop [v taylor i 0] (if (= i s) v (recur (mul v v) (inc i))))))

(defn log* [x]
  ;; Halley's iteration on exp from the double's log: cubic, so three steps pass 80 digits
  (let [g (bd (clotran.host.math/log (double x)))]
    (loop [y g i 0]
      (if (= i 4)
        y
        (let [e (exp* y)] (recur (add y (div (mul two (sub x e)) (add x e))) (inc i)))))))

(defn- atan-series [r]
  (let [r2 (mul r r)]
    (loop [term r sum r n 1 sgn -1]
      (let [term (mul term r2) n (+ n 2)
            t (div term (clotran.host.decimal. n))
            sum (if (neg? sgn) (sub sum t) (add sum t))]
        (if (tiny? t) sum (recur term sum n (- sgn)))))))

(def pi* (delay (sub (mul (clotran.host.decimal. 16) (atan-series (div (clotran.host.decimal. 1) (clotran.host.decimal. 5))))
                     (mul (clotran.host.decimal. 4) (atan-series (div (clotran.host.decimal. 1) (clotran.host.decimal. 239)))))))

(defn atan* [x]
  ;; halve the angle until the series converges quickly: atan x = 2 atan (x / (1 + sqrt (1 + x^2)))
  (let [one (clotran.host.decimal. 1)
        [r k] (loop [r x k 0]
                (if (neg? (.compareTo (.abs r) (clotran.host.decimal. "0.05")))
                  [r k]
                  (recur (div r (add one (.sqrt (add one (mul r r)) mc))) (inc k))))]
    (loop [v (atan-series r) i 0] (if (= i k) v (recur (mul v two) (inc i))))))

(defn atan2*
  "The angle of the point (x, y) in (-pi, pi]; y = 0 with x < 0 is +pi."
  [y x]
  (let [pi @pi*]
    (cond (pos? (.signum x)) (atan* (div y x))
          (neg? (.signum x)) (if (neg? (.signum y)) (sub (atan* (div y x)) pi) (add (atan* (div y x)) pi))
          :else (if (pos? (.signum y)) (div pi two) (.negate (div pi two))))))

(defn- sincos [x]
  ;; x reduced into [-pi, pi]; both series
  (let [pi @pi* tau (mul two pi)
        k (.setScale (div x tau) 0 clotran.host.rounding_mode/HALF_EVEN)
        r (sub x (mul k tau))
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
(defn sinh* [x] (let [e (exp* x)] (div (sub e (div (clotran.host.decimal. 1) e)) two)))
(defn cosh* [x] (let [e (exp* x)] (div (add e (div (clotran.host.decimal. 1) e)) two)))
(defn tanh* [x] (let [e (exp* (mul two x))] (div (sub e (clotran.host.decimal. 1)) (add e (clotran.host.decimal. 1)))))
(defn log10* [x] (div (log* x) (log* (clotran.host.decimal. 10))))
(defn asin* [x]
  (let [one (clotran.host.decimal. 1)]
    (if (zero? (.compareTo (.abs x) one))
      (if (pos? (.signum x)) (div @pi* two) (.negate (div @pi* two)))
      (atan* (div x (.sqrt (sub one (mul x x)) mc))))))
(defn acos* [x] (sub (div @pi* two) (asin* x)))

(defn round-to
  "A decimal rounded ONCE to a real kind: a double holding the nearest real(4) or real(8)."
  [kind x]
  (case kind :real8 (.doubleValue x) :real4 (double (.floatValue x))))

(ns ftypes.accuracy
  "The correctly rounded reference for scripts/ftypes-accuracy, on clj: one line in, one line out.
  A line is FN KIND A [B]: a function's name, :real4 or :real8 (a complex kind's parts, for the
  complex functions), and its arguments as the bits of the kind (a real(4)'s 32, a real(8)'s 64).
  The answer is the result's bits, rounded once from refmath's 80 digits; a complex result is two."
  (:require [ftypes.refmath :as rm] [clojure.string :as str]))

(defn from-bits [k b] (case k :real4 (double (clotran.host.real4/intBitsToFloat (int b))) :real8 (clotran.host.real8/longBitsToDouble b)))
(defn to-bits [k x] (case k :real4 (long (clotran.host.real4/floatToRawIntBits (unchecked-float x))) :real8 (clotran.host.real8/doubleToRawLongBits x)))

(def real1
  {"exp" rm/exp* "log" rm/log* "log10" rm/log10* "sin" rm/sin* "cos" rm/cos* "tan" rm/tan*
   "asin" rm/asin* "acos" rm/acos* "atan" rm/atan* "sinh" rm/sinh* "cosh" rm/cosh* "tanh" rm/tanh*})

(defn atan2-ref
  "ATAN2(y, x) with the signs of zero IEEE gives it: y = +-0 is +-0 for x > 0 and +-pi for x < 0."
  [y x]
  (cond (and (zero? y) (pos? x)) y
        (and (zero? y) (neg? x)) (if (neg? (clotran.host.math/copySign 1.0 y)) (.negate (rm/pi*)) (rm/pi*))
        :else (rm/atan2* (rm/bd y) (rm/bd x))))

;; + - * / and SQRT, exactly (a quotient and a root to the working precision, which cannot sit on a
;; midpoint of either kind unless they are exact)
(def arith
  {"add" (fn [x y] (.add (rm/bd x) (rm/bd y))) "sub" (fn [x y] (.subtract (rm/bd x) (rm/bd y)))
   "mul" (fn [x y] (.multiply (rm/bd x) (rm/bd y))) "div" (fn [x y] (.divide (rm/bd x) (rm/bd y) rm/*mc*))
   "sqrt" (fn [x] (.sqrt (rm/bd x) rm/*mc*))})

(defn reference
  "The bits of the value rounded to the kind; for a real(4) with one part, also \" | \" and the bits of
  the value rounded to real(8), from which rounding again to real(4) is a double rounding."
  [line]
  (let [[f k & bs] (str/split (str/trim line) #"\s+")
        k (keyword k)
        xs (map #(from-bits k (parse-long %)) bs)
        v (cond (arith f) [(apply (arith f) xs)]
                (real1 f) [((real1 f) (rm/bd (first xs)))]
                (= f "atan2") [(apply atan2-ref xs)]
                :else (let [g (or (resolve (symbol "ftypes.refmath" (str f "*"))) (throw (ex-info (str "no reference for " f) {})))
                            r (apply @g xs)]
                        (if (vector? r) r [r])))]
    (str (str/join " " (map #(to-bits k (rm/round-to k %)) v))
         (when (and (= k :real4) (= 1 (count v))) (str " | " (to-bits :real8 (rm/round-to :real8 (first v))))))))

(defn run
  "The reference of every line of in, to out; then every step-th line again at 110 digits, which must
  round the same: prints how many were rechecked and how many differ."
  [in out step]
  (let [ls (str/split-lines (slurp in))
        rs (vec (pmap reference ls))
        again (vec (pmap (fn [i] [i (rm/with-digits 110 (reference (ls i)))]) (range 0 (count ls) step)))
        bad (filter (fn [[i r]] (not= r (rs i))) again)]
    (spit out (str (str/join "\n" rs) "\n"))
    (println "RECHECK" (count again) (count bad) (pr-str (vec (take 5 (map (fn [[i r]] [(ls i) (rs i) r]) bad)))))))

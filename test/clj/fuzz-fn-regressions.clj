;; Functions scripts/fuzz-fn found a compiled-mode difference in, compiled
;; as the namespace's own definitions (scripts/fuzz --fixture), so pure
;; lowering sees them; their calls are test/clj/fuzz-fn-regressions.edn.
;; A recur passing a local another type than its init: clj boxes the
;; local, so (fz-recur-box 2.5 18) is the long -3. Pure Fortran has no
;; box; that version is declined and compiled through the runtime.
(defn fz-recur-box [p ^long q] (loop [i 0 acc p] (if (< i 3) (recur (inc i) (long -3)) acc)))
(defn fz-recur-box-init ^long [^long n] (loop [x 0.0 i 0] (if (< i n) (recur 1 (inc i)) (long x))))
;; The smallest long reaching an unhinted parameter: clj's boxed minus
;; overflows negating it, clotran subtracts exactly (DEVIATIONS 72). The
;; literal is here, not in the case, so the fuzzer's allowance for it has
;; to read the fixture too (scripts/fuzz-fn, 2026-10-17).
(defn fz-min-sub [p] (- -5 p))
(defn fz-min-sub-k [] (fz-min-sub -9223372036854775808))

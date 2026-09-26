;; Eight futures allocating at once, run by `make test` under
;; CLOTRAN_GC_VERIFY=1: every young collection then checks the whole heap
;; for a reference to something freed (GC.f90, gc_check_heap), and the
;; answers must equal the same work done serially. This is the check for
;; per-thread allocation (PLAN.md step 14d) -- a young object missing from
;; the young collection's view was invisible to every other test here.

(defn work [k]
  (let [v (into [] (comp (map #(str "k" (* k %))) (filter #(< (count %) 6))) (range 3000))
        m (reduce (fn [m i] (assoc m (keyword (str "x" (mod (* i k) 53))) [i (pr-str [k i])])) {} (range 600))]
    [(count v) (count m) (reduce + (map (comp first val) m))]))

(def serial (mapv work (range 1 9)))

(dotimes [round 3]
  (let [par (mapv deref (mapv (fn [k] (future (work k))) (range 1 9)))]
    (when (not= par serial)
      (println "THREADS HEAP FAILED: round" round "gave" par "serially" serial)
      (System/exit 1))))

(println "THREADS HEAP PASSED")

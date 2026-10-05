;; test/clj/torture_check.clj -- a few forms under CLOTRAN_GC_EVERY=1, a
;; collection at every object allocation: each is the shape of a rooting
;; mistake that was found the slow way, and with a collection at every
;; allocation a value held in a plain local across one is freed at once
;; rather than when the timing is right. (CLOTRAN_GC_TORTURE=1 does the
;; same with full collections, at 10 ms each on core's heap -- 90 s for
;; these two reads; the young collections here take 0.2 s and caught the
;; same bug.) core.clj itself is not under it: main.f90 switches it on
;; after the first file.

;; read-string's result was a plain local while the #tag scan walked
;; it, and the scan allocates over every map literal (2026-09-28: one
;; clojuredocs case lost its forms, only when a collection landed there)
(def r1 (read-string "[{:a 1, :b [2 3]} (f {:c 4}) #{5} {:d {:e 6}}]"))
(def r2 (read-string "{:x [1 {:y 2}]}"))
;; a regex literal is compiled while its form is read, and read_regex
;; rooted only its own text: a collection there freed the form being
;; read around it, and (def p #"a") read as nothing (2026-09-29: the
;; oracle's one-run-in-a-hundred flake, PLAN step 20)
(def rx1 [#"a(b)" {:k #"c+"} (list #"d")])
;; the cursors over maps and sets, and the vector's pop and view, each
;; allocate while holding a node, a leaf or a frame of the walk (PLAN
;; step 28, 2026-10-01): a collection there must not free it
(def hm (zipmap (range 60) (range 60)))
(def sm (into (sorted-map) (map vector (range 70) (range 70))))
(def walks [(sort (map key (seq hm))) (= (keys hm) (map key (seq hm))) (take 3 (rseq sm))
            (subseq sm >= 40 < 43) (reduce + (map val sm)) (sort (seq (set (range 0 90 3))))
            (pop (vec (range 70))) (vec (subvec (vec (range 50)) 10 14)) (vec (rseq (vec (range 5))))
            (nth "héllo wörld" 7) (subs "héllo wörld ß" 3 9)])

;; swap!'s new value, and an agent action's, sat in a plain local while
;; the validator's key was made -- a STRING allocation, which torture did
;; not collect at (2026-10-05: spec's registry atom read [] one run in
;; twenty, whatever had reused the freed map's slot)
(def at (atom {}))
(dotimes [i 30] (swap! at assoc i (str "v" i)))
(def ag (agent {}))
(dotimes [i 10] (send ag assoc i (str "w" i)))
(await ag)
(def refs [@at @ag])

(if (and (= r1 '[{:a 1, :b [2 3]} (f {:c 4}) #{5} {:d {:e 6}}])
         (= r2 {:x [1 {:y 2}]})
         (= (map str [(first rx1) (:k (second rx1)) (first (nth rx1 2))]) ["a(b)" "c+" "d"])
         (= (re-find (first rx1) "xab") ["ab" "b"])
         (= walks [(range 60) true '([69 69] [68 68] [67 67]) '([40 40] [41 41] [42 42]) 2415 (range 0 90 3)
                   (vec (range 69)) [10 11 12 13] [4 3 2 1 0] \ö "lo wör"])
         (= refs [(into {} (map (fn [i] [i (str "v" i)]) (range 30))) (into {} (map (fn [i] [i (str "w" i)]) (range 10)))]))
  (println "TORTURE CHECK PASSED")
  (println "FAIL - under torture:" (pr-str r1) (pr-str r2) (pr-str walks) (pr-str refs)))
(shutdown-agents)

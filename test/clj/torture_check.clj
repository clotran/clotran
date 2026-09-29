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

(if (and (= r1 '[{:a 1, :b [2 3]} (f {:c 4}) #{5} {:d {:e 6}}])
         (= r2 {:x [1 {:y 2}]})
         (= (map str [(first rx1) (:k (second rx1)) (first (nth rx1 2))]) ["a(b)" "c+" "d"])
         (= (re-find (first rx1) "xab") ["ab" "b"]))
  (println "TORTURE CHECK PASSED")
  (println "FAIL - read-string under torture:" (pr-str r1) (pr-str r2)))

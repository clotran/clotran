; The array map's reads at the level the Fortran is generated from:
; arraymap's am-index, am-get and the positional reads as
; src/f/PersistentArrayMap.f90 runs them on GC.f90's pools, guard-verified,
; so scripts/acl2-fortran -b arraymapg writes src/f/gen/arraymap_gen.inc and
; index_of, gcm_contains, gcm_get, gcm_key_at and gcm_val_at are shims round
; it.
;
; The map, as GC.f90 lays it out: an object (tag 8) of kind OBJ_MAP (3),
; its count h-oi1, its slot 1 (word 5o) the keys' run, slot 2 (word 5o+1)
; the values' run; a run (tag 9) is h-vlen words of the arena from h-voff.
; A word past a run's length, or of a slot that is not a run, reads as nil
; (gc_vec_get's answer), the words (0 0 0).
;
; THE ANSWER IS A PLACE, as vmrt's reads answer: 0 nil, else -w-1, the
; arena word w; the shim copies what the place holds (gc_word_at). Nothing
; is built and nothing is written.
;
; THE HOST'S EQUALITY: index_of compares a key with gc_equal, which is
; Clojure's = and the runtime's, by design (docs/model-coverage.md). Here
; it is amg-keq, constrained only to answer true or false, on the two
; values' words (tag ref ival). The refinement theorems take, as a named
; hypothesis (amg-keq-ok), that on the run's keys it is equality of what
; the words mean (amg-mean, constrained only to mean nil by the words
; (0 0 0)). It fails for =, which is not reflexive, on NaN: a NaN key is
; found by no lookup, in the map as in clj.
;
; Theorems:
;   amg-index-refines  the scan answers arraymap's am-index of the map
;                      the heap holds (amg-abs), so am-index-from-member,
;                      am-assoc-get and the rest hold of it
;   amg-contains-refines  index /= 0 is am-contains
;   amg-get-refines    the place answered holds arraymap's am-get
;   amg-at-refines     key_at and val_at hold the i-th key and value
;   amg-index-cost     the scan compares at most count keys, a turn each
;
; Named, outside the model: the count is a default integer (gc_i1), so
; below 2^40 (the theorems' hypothesis; the scan stops there); every
; arena word read is inside the arena (the shim's accessors are
; GC.f90's hp_*, the arena 1-based, as heap_gen.inc's are).

(in-package "ACL2")

(include-book "arraymap")
(include-book "heapsq")

; ---- THE HOST --------------------------------------------------------------------------

; gc_equal on two values, given as their words (key, then the run's word:
; the hand-written index_of's order, gc_equal(key_i, k) with k second)
(encapsulate (((amg-keq * * * * * *) => *))
  (local (defun amg-keq (kt kr kv wt wr wv) (and (equal kt wt) (equal kr wr) (equal kv wv))))
  (defthm booleanp-amg-keq (booleanp (amg-keq kt kr kv wt wr wv)) :rule-classes :type-prescription))

; what a value's words mean (only in the theorems)
(encapsulate (((amg-mean * * *) => *))
  (local (defun amg-mean (wt wr wv) (if (and (equal wt 0) (equal wr 0) (equal wv 0)) nil (list wt wr wv))))
  (defthm amg-mean-nil (equal (amg-mean 0 0 0) nil)))

; ---- READS (generated) -----------------------------------------------------------------

(defun amg-voff (v hpg)
  (declare (xargs :stobjs hpg :guard (sb64p v)))
  (if (and (integerp v) (<= 0 v) (< v (h-voff-length hpg))) (h-voffi v hpg) -1))

(defun amg-vlen (v hpg)
  (declare (xargs :stobjs hpg :guard (sb64p v)))
  (if (and (integerp v) (<= 0 v) (< v (h-vlen-length hpg))) (h-vleni v hpg) 0))

(defun amg-wt (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (if (and (integerp w) (< 0 w) (< w (h-atag-length hpg))) (h-atagi w hpg) 0))

(defun amg-wr (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (if (and (integerp w) (< 0 w) (< w (h-aref-length hpg))) (h-arefi w hpg) 0))

(defun amg-wv (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (if (and (integerp w) (< 0 w) (< w (h-aival-length hpg))) (h-aivali w hpg) 0))

(defthm amg-reads-sb64
  (implies (and (hpgp hpg) (integerp j))
           (and (sb64p (amg-voff j hpg)) (sb64p (amg-vlen j hpg))
                (sb64p (amg-wt j hpg)) (sb64p (amg-wr j hpg)) (sb64p (amg-wv j hpg))))
  :hints (("Goal" :in-theory (disable nth))))
(defthm amg-voff-int (implies (hpgp hpg) (integerp (amg-voff j hpg))) :rule-classes :type-prescription)
(defthm amg-vlen-int (implies (hpgp hpg) (integerp (amg-vlen j hpg))) :rule-classes :type-prescription)
(defthm amg-wt-int (implies (hpgp hpg) (integerp (amg-wt j hpg))) :rule-classes :type-prescription)
(defthm amg-wr-int (implies (hpgp hpg) (integerp (amg-wr j hpg))) :rule-classes :type-prescription)
(defthm amg-wv-int (implies (hpgp hpg) (integerp (amg-wv j hpg))) :rule-classes :type-prescription)
(in-theory (disable amg-voff amg-vlen amg-wt amg-wr amg-wv))

; the run in object word s: its offset and length, (0 0) when s holds no run
(defun amg-roff (s hpg)
  (declare (xargs :stobjs hpg :guard (sb64p s)))
  (if (equal (hpg-ot s hpg) 9) (amg-voff (hpg-or s hpg) hpg) 0))

(defun amg-rlen (s hpg)
  (declare (xargs :stobjs hpg :guard (sb64p s)))
  (if (equal (hpg-ot s hpg) 9) (amg-vlen (hpg-or s hpg) hpg) 0))

; the arena word of the run's element i (0-based), -1 for nil
(defun amg-w (off len i)
  (declare (xargs :guard (and (sb64p off) (sb64p len) (natp i) (< i *hb40*))))
  (if (and (< i len) (< 0 off) (< off *hb40*)) (+ off i) -1))

(defun amg-place (w) (declare (xargs :guard (sb64p w))) (if (< w 0) 0 (- -1 w)))

; ---- THE OPERATIONS (generated) ----------------------------------------------------------

(defun amg-map (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (and (hpg-obj-at tag ref hpg) (equal (hpg-okd ref hpg) 3)))

; whether gc_equal finds k the run's element i (the loop's test: a let in a loop
; body is not a tail call the generator turns into a loop)
(defun amg-kat (kt kr kv off len i hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p kt) (sb64p kr) (sb64p kv) (sb64p off) (sb64p len) (natp i) (< i *hb40*))))
  (let ((w (amg-w off len i)))
    (amg-keq kt kr kv (amg-wt w hpg) (amg-wr w hpg) (amg-wv w hpg))))

; index_of's loop: the first i (1-based) from i0 whose key gc_equal finds k, or 0
(defun amg-index-from (kt kr kv off len i n hpg)
  (declare (xargs :stobjs hpg
                  :guard (and (sb64p kt) (sb64p kr) (sb64p kv) (sb64p off) (sb64p len) (natp i) (sb64p n))
                  :measure (nfix (- *hb40* (nfix i)))))
  (if (and (natp i) (< i n) (< i *hb40*))
      (if (amg-kat kt kr kv off len i hpg)
          (+ 1 i)
        (amg-index-from kt kr kv off len (+ 1 i) n hpg))
    0))

(defthm amg-index-from-natp (natp (amg-index-from kt kr kv off len i n hpg)) :rule-classes :type-prescription)
(defthm amg-index-from-hb40 (<= (amg-index-from kt kr kv off len i n hpg) *hb40*) :rule-classes :linear)

(defun amg-index (tag ref kt kr kv hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref) (sb64p kt) (sb64p kr) (sb64p kv))))
  (if (amg-map tag ref hpg)
      (let ((s (* 5 ref)))
        (amg-index-from kt kr kv (amg-roff s hpg) (amg-rlen s hpg) 0 (hpg-oi ref hpg) hpg))
    0))

; slot k's (0 keys, 1 values) element i (1-based) of a map, as a place
(defun amg-at (tag ref k i hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref) (sb64p k) (sb64p i))))
  (if (and (amg-map tag ref hpg) (< 0 i) (<= i (hpg-oi ref hpg)) (<= i *hb40*) (or (equal k 0) (equal k 1)))
      (let ((s (+ k (* 5 ref))))
        (amg-place (amg-w (amg-roff s hpg) (amg-rlen s hpg) (- i 1))))
    0))

; gcm_get: the value's place, 0 when k is absent
(defun amg-get (tag ref kt kr kv hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref) (sb64p kt) (sb64p kr) (sb64p kv))))
  (let ((at (amg-index tag ref kt kr kv hpg)))
    (if (equal at 0) 0 (amg-at tag ref 1 at hpg))))

; ---- THE ABSTRACTION ---------------------------------------------------------------------

(defun amg-wmean (w hpg) (declare (xargs :stobjs hpg :verify-guards nil)) (amg-mean (amg-wt w hpg) (amg-wr w hpg) (amg-wv w hpg)))
(in-theory (disable amg-wmean))
(defun amg-pmean (p hpg) (declare (xargs :stobjs hpg :verify-guards nil)) (if (equal p 0) nil (amg-wmean (- -1 p) hpg)))

; the run's elements i .. n-1, what they mean
(defun amg-run (off len i n hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (ifix n) (nfix i)))))
  (if (and (natp i) (integerp n) (< i n))
      (cons (amg-wmean (amg-w off len i) hpg) (amg-run off len (+ 1 i) n hpg))
    nil))

; the map the heap holds: arraymap's (count keys vals)
(defun amg-abs (ref hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (let ((n (hpg-oi ref hpg)) (s (* 5 ref)))
    (am-make n (amg-run (amg-roff s hpg) (amg-rlen s hpg) 0 n hpg)
             (amg-run (amg-roff (+ 1 s) hpg) (amg-rlen (+ 1 s) hpg) 0 n hpg))))

; THE HYPOTHESIS: on keys i .. n-1, gc_equal is equality of meaning
(defun amg-keq-ok (kt kr kv off len i n hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (ifix n) (nfix i)))))
  (if (and (natp i) (integerp n) (< i n))
      (let ((w (amg-w off len i)))
        (and (iff (amg-keq kt kr kv (amg-wt w hpg) (amg-wr w hpg) (amg-wv w hpg))
                  (equal (amg-wmean w hpg) (amg-mean kt kr kv)))
             (amg-keq-ok kt kr kv off len (+ 1 i) n hpg)))
    t))

(defun amg-keys-ok (tag ref kt kr kv hpg)
  (declare (xargs :stobjs hpg :verify-guards nil) (ignore tag))
  (let ((s (* 5 ref)))
    (amg-keq-ok kt kr kv (amg-roff s hpg) (amg-rlen s hpg) 0 (hpg-oi ref hpg) hpg)))

; ---- REFINEMENT --------------------------------------------------------------------------

(defthm amg-index-from-refines
  (implies (and (natp i) (integerp n) (<= n *hb40*)
                (amg-keq-ok kt kr kv off len i n hpg))
           (equal (amg-index-from kt kr kv off len i n hpg)
                  (am-index-from (amg-run off len i n hpg) (amg-mean kt kr kv) (+ 1 i))))
  :hints (("Goal" :induct (amg-index-from kt kr kv off len i n hpg) :in-theory (disable amg-w))))

(defun amg-nth-ind (i j n)
  (declare (xargs :measure (nfix j)))
  (if (and (natp i) (integerp n) (< i n) (not (zp j))) (amg-nth-ind (+ 1 i) (- j 1) n) (list i j n)))

(defthm nth-amg-run
  (implies (and (natp i) (natp j) (integerp n) (< (+ i j) n))
           (equal (nth j (amg-run off len i n hpg))
                  (amg-wmean (amg-w off len (+ i j)) hpg)))
  :hints (("Goal" :induct (amg-nth-ind i j n) :expand ((amg-run off len i n hpg)) :in-theory (disable amg-w))))

(defthm len-amg-run
  (implies (and (natp i) (integerp n)) (equal (len (amg-run off len i n hpg)) (nfix (- n i)))))

(defthm am-index-from-bound
  (implies (posp i0) (< (am-index-from ks k i0) (+ i0 (len ks))))
  :rule-classes nil)

; COST: the scan compares a key a turn, at most the count of them (index_of n,
; arraymap's cost)
(defun amg-index-turns (kt kr kv off len i n hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- *hb40* (nfix i)))))
  (if (and (natp i) (< i n) (< i *hb40*))
      (let ((w (amg-w off len i)))
        (if (amg-keq kt kr kv (amg-wt w hpg) (amg-wr w hpg) (amg-wv w hpg))
            1
          (+ 1 (amg-index-turns kt kr kv off len (+ 1 i) n hpg))))
    0))

(defthm amg-index-cost
  (implies (and (natp i) (integerp n))
           (<= (amg-index-turns kt kr kv off len i n hpg) (nfix (- n i))))
  :rule-classes :linear
  :hints (("Goal" :induct (amg-index-turns kt kr kv off len i n hpg) :in-theory (disable amg-w))))

(defthm amg-index-from-le
  (implies (and (natp i) (integerp n)) (<= (amg-index-from kt kr kv off len i n hpg) (nfix n)))
  :rule-classes nil
  :hints (("Goal" :induct (amg-index-from kt kr kv off len i n hpg) :in-theory (disable amg-w))))

(in-theory (e/d (am-index am-get am-contains am-keys am-vals am-make am-count) (amg-index-from amg-run amg-keq-ok am-index-from)))

(defthm amg-index-refines
  (implies (and (hpgp hpg) (integerp ref) (amg-map tag ref hpg) (<= (hpg-oi ref hpg) *hb40*)
                (amg-keys-ok tag ref kt kr kv hpg))
           (equal (amg-index tag ref kt kr kv hpg)
                  (am-index (amg-abs ref hpg) (amg-mean kt kr kv)))))

(defthm amg-contains-refines
  (implies (and (hpgp hpg) (integerp ref) (amg-map tag ref hpg) (<= (hpg-oi ref hpg) *hb40*)
                (amg-keys-ok tag ref kt kr kv hpg))
           (iff (not (equal (amg-index tag ref kt kr kv hpg) 0))
                (am-contains (amg-abs ref hpg) (amg-mean kt kr kv)))))

(defthm amg-wmean-nil
  (implies (and (integerp w) (<= w 0)) (equal (amg-wmean w hpg) nil))
  :hints (("Goal" :in-theory (enable amg-wmean amg-wt amg-wr amg-wv))))

(defthm amg-neg-neg (implies (acl2-numberp x) (equal (- (- x)) x)))

(defthm amg-pmean-place
  (implies (integerp w) (equal (amg-pmean (amg-place w) hpg) (amg-wmean w hpg))))

(defthm amg-at-refines
  (implies (and (hpgp hpg) (integerp ref) (amg-map tag ref hpg) (posp i) (<= i (hpg-oi ref hpg)) (<= (hpg-oi ref hpg) *hb40*))
           (and (equal (amg-pmean (amg-at tag ref 0 i hpg) hpg) (nth (- i 1) (am-keys (amg-abs ref hpg))))
                (equal (amg-pmean (amg-at tag ref 1 i hpg) hpg) (nth (- i 1) (am-vals (amg-abs ref hpg)))))))

(defthm amg-index-le
  (implies (and (hpgp hpg) (integerp ref))
           (<= (amg-index tag ref kt kr kv hpg) (nfix (hpg-oi ref hpg))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance amg-index-from-le (off (amg-roff (* 5 ref) hpg)) (len (amg-rlen (* 5 ref) hpg)) (i 0) (n (hpg-oi ref hpg)))))))

(defthm amg-pmean-0 (equal (amg-pmean 0 hpg) nil))

(defthm amg-get-refines
  (implies (and (hpgp hpg) (integerp ref) (amg-map tag ref hpg) (<= (hpg-oi ref hpg) *hb40*)
                (amg-keys-ok tag ref kt kr kv hpg))
           (equal (amg-pmean (amg-get tag ref kt kr kv hpg) hpg)
                  (am-get (amg-abs ref hpg) (amg-mean kt kr kv))))
  :hints (("Goal" :in-theory (e/d (amg-get) (amg-at amg-index amg-abs amg-map amg-keys-ok am-index am-get-is-lookup amg-pmean))
                  :use ((:instance amg-index-refines)
                        (:instance amg-index-le)
                        (:instance amg-at-refines (i (amg-index tag ref kt kr kv hpg)))))))

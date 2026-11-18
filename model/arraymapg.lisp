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
; THE EDITS (generated too): gcm_assoc's and gcm_dissoc's writes into the
; runs they allocate -- copy_run's loop and dissoc's close-up (amg-copy), the
; swap (amg-mv), the value set or the pair appended (amg-put) -- as
; amg-assoc-fill and amg-dissoc-fill. The allocation stays the shim's
; (gc_vec, gc_obj, gc_set_i1), and so does the generational barrier: the
; shim remembers a new run the collector has marked old once its words are
; written (amg_barrier, the per-word check gc_vec_set makes, after the
; fact). Theorems:
;   amg-assoc-fill-refines  the runs written, with the count, are arraymap's
;                           am-assoc of the map the heap holds
;   amg-dissoc-fill-refines likewise am-dissoc, swap or not
;   amg-assoc-cost          index_of's steps and the writes are am-assoc-steps
;   amg-dissoc-cost         ... at most am-dissoc-steps
; Named, under them: AMG-FRESH, what gc_vec answers -- each new run as
; long as the map will be, inside the arena, apart from the other new run
; and from the map's own runs; that allocating (and any collection it runs)
; keeps what the rooted map means, so the index found before (`at`) is
; am-index after; the count non-negative and below 2^40 - 1; no other
; thread writes the runs between gc_vec and gc_obj (they are not yet
; reachable).
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

; ---- EDITS (generated) -------------------------------------------------------------------

; an arena word the edits may write: inside every one of the word's three arrays
(defun amg-in (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (and (< 0 w) (< w (h-atag-length hpg)) (< w (h-aref-length hpg)) (< w (h-aival-length hpg))))

; gc_vec_set without the barrier: the run's element i (0-based) the words (wt wr wv)
(defun amg-put (off len i wt wr wv hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p off) (sb64p len) (natp i) (< i *hb40*) (sb64p wt) (sb64p wr) (sb64p wv))))
  (let ((w (amg-w off len i)))
    (if (amg-in w hpg)
        (let* ((hpg (update-h-atagi w wt hpg))
               (hpg (update-h-arefi w wr hpg))
               (hpg (update-h-aivali w wv hpg)))
          hpg)
      hpg)))

; the destination's element i the source's element j (what gc_vec_get answers)
(defun amg-mv (soff slen j doff dlen i hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p soff) (sb64p slen) (natp j) (< j *hb40*)
                                          (sb64p doff) (sb64p dlen) (natp i) (< i *hb40*))))
  (let ((w (amg-w soff slen j)))
    (amg-put doff dlen i (amg-wt w hpg) (amg-wr w hpg) (amg-wv w hpg) hpg)))

; copy_run's loop (d 0) and dissoc's close-up (d 1): the destination's
; elements i .. n-1 the source's i+d
(defun amg-copy (soff slen doff dlen d i n hpg)
  (declare (xargs :stobjs hpg
                  :guard (and (sb64p soff) (sb64p slen) (sb64p doff) (sb64p dlen) (sb64p d) (natp i) (sb64p n))
                  :measure (nfix (- *hb40* (nfix i)))))
  (if (and (natp i) (< i n) (< n *hb40*) (or (equal d 0) (equal d 1)))
      (let ((hpg (amg-mv soff slen (+ i d) doff dlen i hpg)))
        (amg-copy soff slen doff dlen d (+ 1 i) n hpg))
    hpg))

; gcm_assoc's writes into the fresh runs kq (keys) and vq (values), each
; n long (k present at at) or n + 1 (absent, at 0): both runs copied, then
; the value set in place, or the pair appended
(defun amg-assoc-w (ko kl vo vl nko nkl nvo nvl n at kt kr kv vt vr vv hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ko) (sb64p kl) (sb64p vo) (sb64p vl) (sb64p nko) (sb64p nkl)
                                          (sb64p nvo) (sb64p nvl) (natp n) (< (+ 1 n) *hb40*) (sb64p at)
                                          (sb64p kt) (sb64p kr) (sb64p kv) (sb64p vt) (sb64p vr) (sb64p vv))))
  (let* ((hpg (amg-copy ko kl nko nkl 0 0 n hpg))
         (hpg (amg-copy vo vl nvo nvl 0 0 n hpg)))
    (if (equal at 0)
        (let ((hpg (amg-put nko nkl n kt kr kv hpg)))
          (amg-put nvo nvl n vt vr vv hpg))
      (if (and (< 0 at) (<= at n))
          (amg-put nvo nvl (- at 1) vt vr vv hpg)
        hpg))))

(defun amg-assoc-fill (ref at kt kr kv vt vr vv kq vq hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ref) (sb64p at) (sb64p kt) (sb64p kr) (sb64p kv)
                                          (sb64p vt) (sb64p vr) (sb64p vv) (sb64p kq) (sb64p vq))))
  (let ((n (hpg-oi ref hpg)) (s (* 5 ref)))
    (if (and (<= 0 ref) (< ref *hb40*) (<= 0 n) (< (+ 1 n) *hb40*))
        (amg-assoc-w (amg-roff s hpg) (amg-rlen s hpg) (amg-roff (+ 1 s) hpg) (amg-rlen (+ 1 s) hpg)
                     (amg-voff kq hpg) (amg-vlen kq hpg) (amg-voff vq hpg) (amg-vlen vq hpg)
                     n at kt kr kv vt vr vv hpg)
      hpg)))

; gcm_dissoc's writes into the fresh runs kq and vq, each n - 1 long, k at
; at (/= 0): n - 1 of each copied, then the last entry into the hole (swap)
; or the entries after the hole moved up one, in order
(defun amg-dissoc-w (ko kl vo vl nko nkl nvo nvl n at sw hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ko) (sb64p kl) (sb64p vo) (sb64p vl) (sb64p nko) (sb64p nkl)
                                          (sb64p nvo) (sb64p nvl) (natp n) (< (+ 1 n) *hb40*) (natp at) (< 0 at) (<= at n)
                                          (sb64p sw))))
  (let* ((hpg (amg-copy ko kl nko nkl 0 0 (- n 1) hpg))
         (hpg (amg-copy vo vl nvo nvl 0 0 (- n 1) hpg)))
    (if (not (equal sw 0))
        (if (equal at n) hpg
          (let ((hpg (amg-mv ko kl (- n 1) nko nkl (- at 1) hpg)))
            (amg-mv vo vl (- n 1) nvo nvl (- at 1) hpg)))
      (let ((hpg (amg-copy ko kl nko nkl 1 (- at 1) (- n 1) hpg)))
        (amg-copy vo vl nvo nvl 1 (- at 1) (- n 1) hpg)))))

(defun amg-dissoc-fill (ref at sw kq vq hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ref) (sb64p at) (sb64p sw) (sb64p kq) (sb64p vq))))
  (let ((n (hpg-oi ref hpg)) (s (* 5 ref)))
    (if (and (<= 0 ref) (< ref *hb40*) (< 0 at) (<= at n) (< (+ 1 n) *hb40*))
        (amg-dissoc-w (amg-roff s hpg) (amg-rlen s hpg) (amg-roff (+ 1 s) hpg) (amg-rlen (+ 1 s) hpg)
                      (amg-voff kq hpg) (amg-vlen kq hpg) (amg-voff vq hpg) (amg-vlen vq hpg)
                      n at sw hpg)
      hpg)))

; ---- THE EDITS' FRAME ----------------------------------------------------------------------

(defthm amg-put-frame
  (and (equal (amg-voff j (amg-put off len i wt wr wv hpg)) (amg-voff j hpg))
       (equal (amg-vlen j (amg-put off len i wt wr wv hpg)) (amg-vlen j hpg))
       (equal (hpg-ot j (amg-put off len i wt wr wv hpg)) (hpg-ot j hpg))
       (equal (hpg-or j (amg-put off len i wt wr wv hpg)) (hpg-or j hpg))
       (equal (hpg-oi j (amg-put off len i wt wr wv hpg)) (hpg-oi j hpg))
       (equal (hpg-okd j (amg-put off len i wt wr wv hpg)) (hpg-okd j hpg))
       (equal (amg-in j (amg-put off len i wt wr wv hpg)) (amg-in j hpg)))
  :hints (("Goal" :in-theory (enable amg-voff amg-vlen hpg-ot hpg-or hpg-oi hpg-okd))))

(defthm amg-put-wmean
  (implies (integerp x)
           (equal (amg-wmean x (amg-put off len i wt wr wv hpg))
                  (if (and (equal x (amg-w off len i)) (amg-in x hpg))
                      (amg-mean wt wr wv)
                    (amg-wmean x hpg))))
  :hints (("Goal" :in-theory (enable amg-wmean amg-wt amg-wr amg-wv))))

(in-theory (disable amg-put amg-in))


(defthm amg-wmean-words (equal (amg-mean (amg-wt w hpg) (amg-wr w hpg) (amg-wv w hpg)) (amg-wmean w hpg))
  :hints (("Goal" :in-theory (enable amg-wmean))))

; a run disjoint from the written one reads as it did
(defthm amg-run-put-other
  (implies (and (integerp off) (integerp len) (integerp doff) (integerp dlen) (natp j)
                (or (<= (+ off len) doff) (<= (+ doff dlen) off)))
           (equal (amg-run off len i n (amg-put doff dlen j wt wr wv hpg))
                  (amg-run off len i n hpg)))
  :hints (("Goal" :induct (amg-run off len i n hpg) :in-theory (enable amg-in amg-run))))

(defthm amg-w-int (implies (and (integerp off) (integerp i)) (integerp (amg-w off len i))) :rule-classes :type-prescription)

; two elements' words are one word only when both are nil's
(defthm amg-w-inj
  (implies (and (integerp off) (natp i) (natp j))
           (equal (equal (amg-w off len i) (amg-w off len j))
                  (or (equal i j) (and (equal (amg-w off len i) -1) (equal (amg-w off len j) -1))))))

(defthm amg-in-neg (implies (<= w 0) (not (amg-in w hpg))) :hints (("Goal" :in-theory (enable amg-in))))

; a write below the elements read leaves them
(defthm amg-run-put-below
  (implies (and (natp i) (natp j) (integerp off) (< j i))
           (equal (amg-run off len i n (amg-put off len j wt wr wv hpg))
                  (amg-run off len i n hpg)))
  :hints (("Goal" :induct (amg-run off len i n hpg) :in-theory (enable amg-run amg-in))))

; the written run: its element j the words written
(defthm amg-run-put-same
  (implies (and (natp i) (natp j) (integerp n) (integerp off) (<= i j) (< j n) (amg-in (amg-w off len j) hpg))
           (equal (amg-run off len i n (amg-put off len j wt wr wv hpg))
                  (update-nth (- j i) (amg-mean wt wr wv) (amg-run off len i n hpg))))
  :hints (("Goal" :induct (amg-run off len i n hpg) :in-theory (e/d (amg-run) (amg-w)))))

; a run every element of which is an arena word the edits may write
(defun amg-run-in (off len hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (and (integerp off) (< 0 off) (< off *hb40*) (natp len)
       (<= (+ off len) (h-atag-length hpg)) (<= (+ off len) (h-aref-length hpg)) (<= (+ off len) (h-aival-length hpg))))

(defthm amg-run-in-w
  (implies (and (amg-run-in off len hpg) (natp i) (< i len)) (amg-in (amg-w off len i) hpg))
  :hints (("Goal" :in-theory (enable amg-in))))

(defthm amg-put-run-in
  (equal (amg-run-in off len (amg-put doff dlen i wt wr wv hpg)) (amg-run-in off len hpg))
  :hints (("Goal" :in-theory (enable amg-put amg-in))))
(defthm amg-run-in-fc
  (implies (amg-run-in off len hpg) (and (integerp off) (< 0 off) (< off *hb40*) (natp len)))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable amg-run-in))))
(in-theory (disable amg-run-in))

; ---- THE LOOP, AS A LIST -------------------------------------------------------------------

; amg-copy on the runs as arraymap's lists: new's elements i .. n-1 old's i+d
(defun amg-cpl (d i n new old)
  (declare (xargs :measure (nfix (- (ifix n) (nfix i)))))
  (if (and (natp i) (integerp n) (< i n))
      (amg-cpl d (+ 1 i) n (update-nth i (nth (+ i (nfix d)) old) new) old)
    new))

(defthm amg-copy-frame
  (and (equal (amg-voff j (amg-copy soff slen doff dlen d i n hpg)) (amg-voff j hpg))
       (equal (amg-vlen j (amg-copy soff slen doff dlen d i n hpg)) (amg-vlen j hpg))
       (equal (hpg-ot j (amg-copy soff slen doff dlen d i n hpg)) (hpg-ot j hpg))
       (equal (hpg-or j (amg-copy soff slen doff dlen d i n hpg)) (hpg-or j hpg))
       (equal (hpg-oi j (amg-copy soff slen doff dlen d i n hpg)) (hpg-oi j hpg))
       (equal (hpg-okd j (amg-copy soff slen doff dlen d i n hpg)) (hpg-okd j hpg))
       (equal (amg-run-in off len (amg-copy soff slen doff dlen d i n hpg)) (amg-run-in off len hpg))))

; a run disjoint from the destination reads as it did
(defthm amg-run-copy-other
  (implies (and (integerp off) (integerp len) (integerp doff) (integerp dlen)
                (or (<= (+ off len) doff) (<= (+ doff dlen) off)))
           (equal (amg-run off len k m (amg-copy soff slen doff dlen d i n hpg))
                  (amg-run off len k m hpg))))

(defthm amg-run-copy
  (implies (and (integerp soff) (integerp slen) (amg-run-in doff dlen hpg)
                (or (<= (+ soff slen) doff) (<= (+ doff dlen) soff))
                (natp i) (integerp n) (natp m) (<= n m) (<= m dlen) (< n *hb40*)
                (or (equal d 0) (equal d 1)))
           (equal (amg-run doff dlen 0 m (amg-copy soff slen doff dlen d i n hpg))
                  (amg-cpl d i n (amg-run doff dlen 0 m hpg) (amg-run soff slen 0 (+ n d) hpg))))
  :hints (("Goal" :induct (amg-copy soff slen doff dlen d i n hpg) :in-theory (disable amg-w))))

(defthm amg-cpl-nth
  (implies (and (natp k) (natp i) (natp d))
           (equal (nth k (amg-cpl d i n new old))
                  (if (and (<= i k) (integerp n) (< k n)) (nth (+ k d) old) (nth k new)))))

(defthm amg-cpl-len
  (implies (and (natp i) (<= (ifix n) (len new))) (equal (len (amg-cpl d i n new old)) (len new))))

(defthm amg-cpl-true-listp
  (implies (true-listp new) (true-listp (amg-cpl d i n new old))))

; two true lists as long as each other, equal where they first differ, are equal
(defun amg-nd (a b)
  (if (or (atom a) (atom b)) 0 (if (equal (car a) (car b)) (+ 1 (amg-nd (cdr a) (cdr b))) 0)))

(defthm amg-nth-equal
  (implies (and (true-listp a) (true-listp b) (equal (len a) (len b))
                (equal (nth (amg-nd a b) a) (nth (amg-nd a b) b)))
           (equal a b))
  :rule-classes nil)

(defthm amg-nth-past (implies (<= (len l) (nfix k)) (equal (nth k l) nil)))
(defthm amg-nd-natp (natp (amg-nd a b)) :rule-classes :type-prescription)

; copy_run: the first p of old, into a run p long
(defthm amg-cpl-take
  (implies (and (true-listp x) (natp p) (equal (len x) p))
           (equal (amg-cpl 0 0 p x l) (am-take p l)))
  :hints (("Goal" :use ((:instance amg-nth-equal (a (amg-cpl 0 0 p x l)) (b (am-take p l))))
                  :in-theory (disable amg-cpl amg-nd))))

(defthm amg-take-all (implies (and (true-listp l) (equal (len l) p)) (equal (am-take p l) l)))

; copy_run into a run one longer, the pair appended
(defthm amg-update-nth-append-end
  (implies (and (true-listp l) (equal (len l) n))
           (equal (update-nth n k (append l (list y))) (append l (list k)))))

(defthm amg-cpl-append
  (implies (and (true-listp x) (natp n) (equal (len x) (+ 1 n)))
           (equal (update-nth n k (amg-cpl 0 0 n x l)) (append (am-take n l) (list k))))
  :hints (("Goal" :use ((:instance amg-nth-equal (a (update-nth n k (amg-cpl 0 0 n x l))) (b (append (am-take n l) (list k)))))
                  :in-theory (disable amg-cpl amg-nd))))

; dissoc's close-up is arraymap's shift-loop
(defthm amg-cpl-shift
  (implies (posp at) (equal (amg-cpl 1 (- at 1) (- n 1) new old) (shift-loop at n new old)))
  :hints (("Goal" :induct (shift-loop at n new old))))

; ---- THE ALLOCATION (the shim's, named) ------------------------------------------------------

(defun amg-disj (a al b bl) (or (<= (+ a al) b) (<= (+ b bl) a)))

; what gc_vec answers, twice, for the map's new runs kq and vq: each n2 long,
; inside the arena, apart from each other and from the map's own runs
(defun amg-fresh (ref kq vq n2 hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (let* ((s (* 5 ref))
         (ko (amg-roff s hpg)) (kl (amg-rlen s hpg))
         (vo (amg-roff (+ 1 s) hpg)) (vl (amg-rlen (+ 1 s) hpg))
         (nko (amg-voff kq hpg)) (nkl (amg-vlen kq hpg))
         (nvo (amg-voff vq hpg)) (nvl (amg-vlen vq hpg)))
    (and (amg-run-in nko nkl hpg) (amg-run-in nvo nvl hpg) (equal nkl n2) (equal nvl n2)
         (amg-disj nko nkl nvo nvl)
         (amg-disj ko kl nko nkl) (amg-disj ko kl nvo nvl)
         (amg-disj vo vl nko nkl) (amg-disj vo vl nvo nvl))))

; the map gc_obj builds of the runs kq and vq, its count n2
(defun amg-new-abs (n2 kq vq hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (am-make n2 (amg-run (amg-voff kq hpg) (amg-vlen kq hpg) 0 n2 hpg)
           (amg-run (amg-voff vq hpg) (amg-vlen vq hpg) 0 n2 hpg)))

(defthm amg-roff-int (implies (hpgp hpg) (integerp (amg-roff s hpg))) :rule-classes :type-prescription)
(defthm amg-rlen-int (implies (hpgp hpg) (integerp (amg-rlen s hpg))) :rule-classes :type-prescription)

(defthm amg-run-empty (implies (<= (ifix n) (nfix i)) (equal (amg-run off len i n hpg) nil)) :hints (("Goal" :in-theory (enable amg-run))))
(defun amg-take-ind (p i) (if (zp p) i (amg-take-ind (- p 1) (+ 1 i))))
(defthm amg-take-run
  (implies (and (natp p) (natp i) (integerp q) (<= (+ i p) q))
           (equal (am-take p (amg-run off len i q hpg)) (amg-run off len i (+ i p) hpg)))
  :hints (("Goal" :induct (amg-take-ind p i) :in-theory (enable amg-run) :expand ((amg-run off len i q hpg) (amg-run off len i (+ i p) hpg)))))

(defthm amg-run-true-listp (true-listp (amg-run off len i n hpg)) :hints (("Goal" :in-theory (enable amg-run))))

; ---- REFINEMENT (the edits) -----------------------------------------------------------------

(defthm amg-assoc-w-runs
  (implies (and (integerp ko) (integerp kl) (integerp vo) (integerp vl) (natp n) (< (+ 1 n) *hb40*)
                (amg-run-in nko nkl hpg) (amg-run-in nvo nvl hpg)
                (equal nkl (if (equal at 0) (+ 1 n) n)) (equal nvl (if (equal at 0) (+ 1 n) n))
                (or (equal at 0) (and (posp at) (<= at n)))
                (amg-disj nko nkl nvo nvl) (amg-disj ko kl nko nkl) (amg-disj ko kl nvo nvl)
                (amg-disj vo vl nko nkl) (amg-disj vo vl nvo nvl))
           (let ((h2 (amg-assoc-w ko kl vo vl nko nkl nvo nvl n at kt kr kv vt vr vv hpg)))
             (and (equal (amg-run nko nkl 0 nkl h2)
                         (if (equal at 0) (append (amg-run ko kl 0 n hpg) (list (amg-mean kt kr kv)))
                           (amg-run ko kl 0 n hpg)))
                  (equal (amg-run nvo nvl 0 nvl h2)
                         (if (equal at 0) (append (amg-run vo vl 0 n hpg) (list (amg-mean vt vr vv)))
                           (update-nth (- at 1) (amg-mean vt vr vv) (amg-run vo vl 0 n hpg)))))))
  :hints (("Goal" :in-theory (disable amg-w amg-cpl amg-copy amg-put))))

(defthm amg-wmean-put-other
  (implies (and (integerp off) (integerp len) (integerp doff) (integerp dlen) (natp j) (natp i) (amg-disj off len doff dlen))
           (equal (amg-wmean (amg-w off len j) (amg-put doff dlen i wt wr wv hpg)) (amg-wmean (amg-w off len j) hpg)))
  :hints (("Goal" :in-theory (enable amg-in))))

(defthm amg-wmean-copy-other
  (implies (and (integerp off) (integerp len) (integerp doff) (integerp dlen) (natp j) (amg-disj off len doff dlen))
           (equal (amg-wmean (amg-w off len j) (amg-copy soff slen doff dlen d i n hpg)) (amg-wmean (amg-w off len j) hpg)))
  :hints (("Goal" :induct (amg-copy soff slen doff dlen d i n hpg) :in-theory (disable amg-w amg-disj))))

(defthm amg-dissoc-w-runs
  (implies (and (integerp ko) (integerp kl) (integerp vo) (integerp vl) (natp n) (< (+ 1 n) *hb40*)
                (posp at) (<= at n)
                (amg-run-in nko nkl hpg) (amg-run-in nvo nvl hpg)
                (equal nkl (- n 1)) (equal nvl (- n 1))
                (amg-disj nko nkl nvo nvl) (amg-disj ko kl nko nkl) (amg-disj ko kl nvo nvl)
                (amg-disj vo vl nko nkl) (amg-disj vo vl nvo nvl))
           (let ((h2 (amg-dissoc-w ko kl vo vl nko nkl nvo nvl n at sw hpg)))
             (and (equal (amg-run nko nkl 0 nkl h2)
                         (if (not (equal sw 0)) (swap-fill at n (amg-run ko kl 0 n hpg))
                           (shift-loop at n (am-take (- n 1) (amg-run ko kl 0 n hpg)) (amg-run ko kl 0 n hpg))))
                  (equal (amg-run nvo nvl 0 nvl h2)
                         (if (not (equal sw 0)) (swap-fill at n (amg-run vo vl 0 n hpg))
                           (shift-loop at n (am-take (- n 1) (amg-run vo vl 0 n hpg)) (amg-run vo vl 0 n hpg)))))))
  :hints (("Goal" :in-theory (e/d (swap-fill) (amg-w amg-cpl amg-copy amg-put shift-loop shift-loop-is remove-at-is-rm-pos shift-loop-rm-pos swap-fill-last)))))

(defthm amg-w-frame
  (and (equal (amg-voff j (amg-assoc-w ko kl vo vl nko nkl nvo nvl n at kt kr kv vt vr vv hpg)) (amg-voff j hpg))
       (equal (amg-vlen j (amg-assoc-w ko kl vo vl nko nkl nvo nvl n at kt kr kv vt vr vv hpg)) (amg-vlen j hpg))
       (equal (amg-voff j (amg-dissoc-w ko kl vo vl nko nkl nvo nvl n at sw hpg)) (amg-voff j hpg))
       (equal (amg-vlen j (amg-dissoc-w ko kl vo vl nko nkl nvo nvl n at sw hpg)) (amg-vlen j hpg)))
  :hints (("Goal" :in-theory (disable amg-copy amg-put))))

(defthm amg-index-abs-range
  (implies (and (natp n) (equal (len ks) n))
           (or (equal (am-index-from ks k 1) 0)
               (and (posp (am-index-from ks k 1)) (<= (am-index-from ks k 1) n))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance am-index-from-range (i 1)) (:instance am-index-from-member (i 1))))))

(defthm amg-assoc-fill-refines
  (implies (and (hpgp hpg) (integerp ref) (amg-map tag ref hpg)
                (<= 0 (hpg-oi ref hpg)) (< (+ 1 (hpg-oi ref hpg)) *hb40*)
                (equal at (am-index (amg-abs ref hpg) (amg-mean kt kr kv)))
                (amg-fresh ref kq vq (if (equal at 0) (+ 1 (hpg-oi ref hpg)) (hpg-oi ref hpg)) hpg))
           (equal (amg-new-abs (if (equal at 0) (+ 1 (hpg-oi ref hpg)) (hpg-oi ref hpg)) kq vq
                               (amg-assoc-fill ref at kt kr kv vt vr vv kq vq hpg))
                  (am-assoc (amg-abs ref hpg) (amg-mean kt kr kv) (amg-mean vt vr vv))))
  :hints (("Goal" :in-theory (e/d (am-assoc) (amg-assoc-w amg-assoc-w-runs amg-roff amg-rlen amg-run-in amg-disj am-index-from))
                  :use ((:instance amg-assoc-w-runs
                                   (ko (amg-roff (* 5 ref) hpg)) (kl (amg-rlen (* 5 ref) hpg))
                                   (vo (amg-roff (+ 1 (* 5 ref)) hpg)) (vl (amg-rlen (+ 1 (* 5 ref)) hpg))
                                   (nko (amg-voff kq hpg)) (nkl (amg-vlen kq hpg)) (nvo (amg-voff vq hpg)) (nvl (amg-vlen vq hpg))
                                   (n (hpg-oi ref hpg)))
                        (:instance amg-index-abs-range (n (hpg-oi ref hpg)) (k (amg-mean kt kr kv))
                                   (ks (amg-run (amg-roff (* 5 ref) hpg) (amg-rlen (* 5 ref) hpg) 0 (hpg-oi ref hpg) hpg)))))))

(defthm amg-dissoc-fill-refines
  (implies (and (hpgp hpg) (integerp ref) (amg-map tag ref hpg)
                (<= 0 (hpg-oi ref hpg)) (< (+ 1 (hpg-oi ref hpg)) *hb40*)
                (equal at (am-index (amg-abs ref hpg) (amg-mean kt kr kv))) (not (equal at 0))
                (amg-fresh ref kq vq (- (hpg-oi ref hpg) 1) hpg))
           (equal (amg-new-abs (- (hpg-oi ref hpg) 1) kq vq (amg-dissoc-fill ref at sw kq vq hpg))
                  (am-dissoc (amg-abs ref hpg) (amg-mean kt kr kv) (not (equal sw 0)))))
  :hints (("Goal" :in-theory (e/d (am-dissoc) (amg-dissoc-w amg-dissoc-w-runs amg-roff amg-rlen amg-run-in amg-disj am-index-from
                                                swap-fill shift-loop shift-loop-is remove-at-is-rm-pos shift-loop-rm-pos swap-fill-last))
                  :use ((:instance amg-dissoc-w-runs
                                   (ko (amg-roff (* 5 ref) hpg)) (kl (amg-rlen (* 5 ref) hpg))
                                   (vo (amg-roff (+ 1 (* 5 ref)) hpg)) (vl (amg-rlen (+ 1 (* 5 ref)) hpg))
                                   (nko (amg-voff kq hpg)) (nkl (amg-vlen kq hpg)) (nvo (amg-voff vq hpg)) (nvl (amg-vlen vq hpg))
                                   (n (hpg-oi ref hpg)))
                        (:instance amg-index-abs-range (n (hpg-oi ref hpg)) (k (amg-mean kt kr kv))
                                   (ks (amg-run (amg-roff (* 5 ref) hpg) (amg-rlen (* 5 ref) hpg) 0 (hpg-oi ref hpg) hpg)))))))

; ---- COST (the edits) -----------------------------------------------------------------------
;
; a write a turn: amg-copy's loop writes once a turn, amg-put and amg-mv once

(defun amg-copy-turns (d i n)
  (declare (xargs :measure (nfix (- *hb40* (nfix i)))))
  (if (and (natp i) (< i n) (< n *hb40*) (or (equal d 0) (equal d 1))) (+ 1 (amg-copy-turns d (+ 1 i) n)) 0))

(defthm amg-copy-turns-is
  (implies (and (natp i) (integerp n) (< n *hb40*) (or (equal d 0) (equal d 1)))
           (equal (amg-copy-turns d i n) (nfix (- n i)))))

(defun amg-assoc-turns (n at) (+ (amg-copy-turns 0 0 n) (amg-copy-turns 0 0 n) (if (equal at 0) 2 1)))

(defun amg-dissoc-turns (n at swap)
  (+ (amg-copy-turns 0 0 (- n 1)) (amg-copy-turns 0 0 (- n 1))
     (if swap (if (equal at n) 0 2) (+ (amg-copy-turns 1 (- at 1) (- n 1)) (amg-copy-turns 1 (- at 1) (- n 1))))))

; the index_of before them and these writes are arraymap's steps: assoc's
; exactly, dissoc's at most (the swap at the last place writes nothing)
(defthm amg-assoc-cost
  (implies (and (hpgp hpg) (integerp ref) (<= 0 (hpg-oi ref hpg)) (< (+ 1 (hpg-oi ref hpg)) *hb40*)
                (equal at (am-index (amg-abs ref hpg) k)))
           (equal (+ (am-index-steps (am-keys (amg-abs ref hpg)) k) (amg-assoc-turns (hpg-oi ref hpg) at))
                  (am-assoc-steps (amg-abs ref hpg) k)))
  :hints (("Goal" :in-theory (disable amg-run amg-roff amg-rlen))))

(defthm amg-dissoc-cost
  (implies (and (hpgp hpg) (integerp ref) (<= 0 (hpg-oi ref hpg)) (< (+ 1 (hpg-oi ref hpg)) *hb40*)
                (equal at (am-index (amg-abs ref hpg) k)) (not (equal at 0)))
           (<= (+ (am-index-steps (am-keys (amg-abs ref hpg)) k) (amg-dissoc-turns (hpg-oi ref hpg) at swap))
               (am-dissoc-steps (amg-abs ref hpg) k swap)))
  :hints (("Goal" :in-theory (disable amg-run amg-roff amg-rlen am-index-from)
                  :use ((:instance amg-index-abs-range (n (hpg-oi ref hpg))
                                   (ks (amg-run (amg-roff (* 5 ref) hpg) (amg-rlen (* 5 ref) hpg) 0 (hpg-oi ref hpg) hpg)))))))

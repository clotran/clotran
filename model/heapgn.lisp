; clotran's heap under the model (PLAN step 33, stage 1c): THE WRITE
; BARRIER's test, at the level the Fortran is generated from
; (src/f/gen/heap_gen.inc), guard-verified. A write of (tag, ref) into an
; old object (one the last collection left marked) remembers the object
; when what is written is YOUNG: a reference into a pool, in range, not
; marked -- GC.f90's is_young, which gc_set_slot asks.
;
; heapgn-proof.lisp: hpg-young-ref is (not (marked-ref tag ref)), so the
; barrier is hpg-barrier, which keeps the remembered-set invariant
; (barrier-keeps) that makes the young collection sound (young-closed).

(in-package "ACL2")

(include-book "heapsq")

(defun hpg-young-ref (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (and (< 0 ref)
       (cond ((equal tag 8) (and (< ref (h-omark-length hpg)) (equal (h-omarki ref hpg) 0)))
             ((equal tag 9) (and (< ref (h-vmark-length hpg)) (< ref (h-vlen-length hpg)) (equal (h-vmarki ref hpg) 0)))
             ((hpg-text-tag tag) (and (< ref (h-smark-length hpg)) (equal (h-smarki ref hpg) 0)))
             (t nil))))

; its cost: at most one mark read
(defun-nx hpg-young-ref-reads (tag ref)
  (if (and (< 0 ref) (or (equal tag 8) (equal tag 9) (hpg-text-tag tag))) 1 0))

(defthm hpg-young-ref-reads-bound (<= (hpg-young-ref-reads tag ref) 1) :rule-classes (:rewrite :linear))

; ---- AGING'S TEST: WHAT REFERENCES AN AGED OBJECT OR RUN ---------------------------------
;
; A young survivor is AGED (its mark cleared, flagged aged); an old object
; or run referencing one must then be remembered (heapgn-proof's
; aging-keeps). collect_young asks it of each promoted object and run,
; forget_young of each remembered one -- these, generated.

(hsb64-elems h-oagedp) (hpg-elem oaged)
(hsb64-elems h-vagedp) (hpg-elem vaged)

(defun hpg-aged-ref (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (and (< 0 ref)
       (cond ((equal tag 8) (and (< ref (h-oaged-length hpg)) (not (equal (h-oagedi ref hpg) 0))))
             ((equal tag 9) (and (< ref (h-vaged-length hpg)) (not (equal (h-vagedi ref hpg) 0))))
             (t nil))))

; object i's slots k .. 4: any an aged reference
(defun hpg-obj-refs-aged (i k hpg)
  (declare (xargs :stobjs hpg :measure (nfix (- 5 (nfix k)))
                  :guard (and (natp i) (< i *hb40*) (natp k) (<= k 5))))
  (if (or (not (natp k)) (<= 5 k))
      nil
    (let ((j (+ (* 5 i) k)))
      (if (and (< j (h-otag-length hpg)) (< j (h-oref-length hpg)))
          (or (hpg-aged-ref (h-otagi j hpg) (h-orefi j hpg) hpg)
              (hpg-obj-refs-aged i (+ 1 k) hpg))
        nil))))

; the arena's words j .. e-1: any an aged reference
(defun hpg-run-refs-aged (j e hpg)
  (declare (xargs :stobjs hpg :measure (nfix (- (nfix e) (nfix j)))
                  :guard (and (natp j) (natp e) (<= e *hb40*))))
  (if (or (not (natp j)) (not (natp e)) (<= e j))
      nil
    (if (and (< j (h-atag-length hpg)) (< j (h-aref-length hpg)))
        (or (hpg-aged-ref (h-atagi j hpg) (h-arefi j hpg) hpg)
            (hpg-run-refs-aged (+ 1 j) e hpg))
      nil)))

; run i's words, as hpg-scan-vec reads them
(defun hpg-vec-refs-aged (i hpg)
  (declare (xargs :stobjs hpg :guard (and (natp i) (< i *hb40*))
                  :guard-hints (("Goal" :in-theory (disable nth hpgp) :use ((:instance hpg-voff-elem (j i)) (:instance hpg-vlen-elem (j i)))))))
  (if (and (< i (h-voff-length hpg)) (< i (h-vlen-length hpg)))
      (let ((off (nfix (h-voffi i hpg))) (n (nfix (h-vleni i hpg))))
        (if (and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*))
            (hpg-run-refs-aged off (+ off n) hpg)
          nil))
    nil))

; their cost: an object's 5 slots, a run's words -- each one flag read
(defun-nx hpg-obj-refs-aged-reads (k) (nfix (- 5 (nfix k))))
(defthm hpg-obj-refs-aged-reads-bound (<= (hpg-obj-refs-aged-reads k) 5) :rule-classes (:rewrite :linear))

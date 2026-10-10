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

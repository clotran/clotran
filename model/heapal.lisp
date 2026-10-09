; clotran's heap under the model (PLAN step 33, stage 1b): ALLOCATION, at
; the level the Fortran is generated from (src/f/gen/heap_gen.inc),
; guard-verified. Objects here; runs and texts take the same shape.
;
; A slot comes from the free list's head, or else from past the used end
; while the pool has room (bumping `used`): GC.f90's obj_take without a
; batch. With batching (several threads), a thread FILLS its batch from the
; list and the used end -- each slot taken from the end flagged free while
; it waits -- and takes the batch's last. USE is what gc_obj then does to
; the slot: no longer free, not marked.
;
; heapal-proof.lisp: with the free list well formed -- the slots on it
; distinct, each free and used, linked head to 0 -- and the batch's slots
; distinct, free and off the list, a take hands out a slot that is free or
; past the used end, so never one in use and never one still on the list or
; in the batch; and taking, filling, using and the sweep's frees keep it so.

(in-package "ACL2")

(include-book "heapsw")

(defun hpg-al-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-sw-ok hpg)
       (natp (h-oused hpg)) (<= (h-oused hpg) *hb40*) (natp (h-ocap hpg)) (<= (h-ocap hpg) *hb40*)
       (<= (h-ob-length hpg) *hb40*) (natp (h-nob hpg)) (< (h-nob hpg) (h-ob-length hpg))))

; ---- THE PLAIN TAKE -----------------------------------------------------------------------

; the free list's head, or a slot past the used end, or 0: none
(defun hpg-obj-take (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (hpg-al-ok hpg)))
  (let ((h (h-ohead hpg)))
    (if (and (< 0 h) (< h (h-onext-length hpg)))
        (let ((hpg (update-h-ohead (hpg-s64 (h-onexti h hpg)) hpg)))
          (mv h hpg))
      (if (< (h-oused hpg) (h-ocap hpg))
          (let* ((u (+ 1 (h-oused hpg)))
                 (hpg (update-h-oused u hpg)))
            (mv u hpg))
        (mv 0 hpg)))))

; the slot handed out, in use: not free, not marked (gc_obj)
(defun hpg-obj-use (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-al-ok hpg) (natp i) (< i (h-ofree-length hpg)) (< i (h-omark-length hpg)))))
  (let ((hpg (update-h-ofreei i 0 hpg)))
    (update-h-omarki i 0 hpg)))

; ---- THE BATCH -----------------------------------------------------------------------------

; one slot into the batch: the free list's head
(defun hpg-obj-fill-list (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-al-ok hpg) (< (+ 1 (h-nob hpg)) (h-ob-length hpg))
                              (< 0 (h-ohead hpg)) (< (h-ohead hpg) (h-onext-length hpg)))))
  (let* ((h (h-ohead hpg))
         (n (+ 1 (h-nob hpg)))
         (hpg (update-h-obi n h hpg))
         (hpg (update-h-nob n hpg)))
    (update-h-ohead (hpg-s64 (h-onexti h hpg)) hpg)))

; one slot into the batch: past the used end, flagged free while it waits
(defun hpg-obj-fill-end (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-al-ok hpg) (< (+ 1 (h-nob hpg)) (h-ob-length hpg))
                              (< (h-oused hpg) (h-ocap hpg)) (< (+ 1 (h-oused hpg)) (h-ofree-length hpg))
                              (< (+ 1 (h-oused hpg)) (h-onext-length hpg)))))
  (let* ((u (+ 1 (h-oused hpg)))
         (hpg (update-h-oused u hpg))
         (hpg (update-h-ofreei u 1 hpg))
         (n (+ 1 (h-nob hpg)))
         (hpg (update-h-obi n u hpg)))
    (update-h-nob n hpg)))

; the batch filled to its capacity from the list and the used end, at most
; fuel slots
(defun hpg-obj-fill (fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel)
                  :guard (and (hpg-al-ok hpg) (natp fuel))))
  (if (or (zp fuel) (not (< (+ 1 (h-nob hpg)) (h-ob-length hpg))))
      hpg
    (if (and (< 0 (h-ohead hpg)) (< (h-ohead hpg) (h-onext-length hpg)))
        (let ((hpg (hpg-obj-fill-list hpg)))
          (hpg-obj-fill (- fuel 1) hpg))
      (if (and (< (h-oused hpg) (h-ocap hpg)) (< (+ 1 (h-oused hpg)) (h-ofree-length hpg))
               (< (+ 1 (h-oused hpg)) (h-onext-length hpg)))
          (let ((hpg (hpg-obj-fill-end hpg)))
            (hpg-obj-fill (- fuel 1) hpg))
        hpg))))

; the batch's last, or 0: an empty batch
(defun hpg-obj-pop (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (hpg-al-ok hpg)))
  (let ((n (h-nob hpg)))
    (if (and (< 0 n) (< n (h-ob-length hpg)))
        (let* ((i (h-obi n hpg))
               (hpg (update-h-nob (- n 1) hpg)))
          (mv i hpg))
      (mv 0 hpg))))

; ---- GUARDS ---------------------------------------------------------------------------------

(hsb64-elems h-obp) (hsb64-update h-obp) (hpg-elem ob)

; the stobj's scalars are integers, with hpgp closed
(defthm hpgp-scalars
  (implies (hpgp hpg)
           (and (integerp (nth *h-ohead* hpg)) (integerp (nth *h-vhead* hpg)) (integerp (nth *h-shead* hpg))
                (integerp (nth *h-oused* hpg)) (integerp (nth *h-nob* hpg))))
  :hints (("Goal" :in-theory (enable hpgp)))
  :rule-classes :forward-chaining)

; what the allocation's registers say, with hpg-al-ok closed
(defthm hpg-al-ok-facts
  (implies (hpg-al-ok hpg)
           (and (natp (nth *h-nob* hpg)) (< (nth *h-nob* hpg) (len (nth *h-obi* hpg)))
                (<= (len (nth *h-obi* hpg)) *hb40*)
                (natp (nth *h-oused* hpg)) (<= (nth *h-oused* hpg) *hb40*)
                (natp (nth *h-ocap* hpg)) (<= (nth *h-ocap* hpg) *hb40*)
                (<= (len (nth *h-onexti* hpg)) *hb40*) (<= (len (nth *h-ofreei* hpg)) *hb40*)))
  :rule-classes :forward-chaining)

(defmacro al-keeps-ok (call)
  `(implies (and (hpgp hpg) (hpg-al-ok hpg)) (and (hpgp ,call) (hpg-al-ok ,call))))

(defthm hpg-obj-take-ok (al-keeps-ok (mv-nth 1 (hpg-obj-take hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(defthm hpg-obj-take-range
  (implies (and (hpgp hpg) (hpg-al-ok hpg))
           (and (natp (mv-nth 0 (hpg-obj-take hpg))) (<= (mv-nth 0 (hpg-obj-take hpg)) *hb40*)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-obj-take)

(defthm hpg-obj-use-ok
  (implies (and (natp i) (< i (len (nth *h-ofreei* hpg))) (< i (len (nth *h-omarki* hpg))))
           (al-keeps-ok (hpg-obj-use i hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-obj-use)

(defthm hpg-obj-fill-list-ok
  (implies (and (< (+ 1 (nth *h-nob* hpg)) (len (nth *h-obi* hpg)))
                (< 0 (nth *h-ohead* hpg)) (< (nth *h-ohead* hpg) (len (nth *h-onexti* hpg))))
           (al-keeps-ok (hpg-obj-fill-list hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-obj-fill-list)
(defthm hpg-obj-fill-end-ok
  (implies (and (< (+ 1 (nth *h-nob* hpg)) (len (nth *h-obi* hpg)))
                (< (nth *h-oused* hpg) (nth *h-ocap* hpg)) (< (+ 1 (nth *h-oused* hpg)) (len (nth *h-ofreei* hpg)))
                (< (+ 1 (nth *h-oused* hpg)) (len (nth *h-onexti* hpg))))
           (al-keeps-ok (hpg-obj-fill-end hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-obj-fill-end)
(defthm hpg-obj-fill-ok (al-keeps-ok (hpg-obj-fill fuel hpg))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-obj-fill-list hpg-obj-fill-end hpgp hpg-al-ok))))
(verify-guards hpg-obj-fill :hints (("Goal" :in-theory (disable nth update-nth hpg-obj-fill-list hpg-obj-fill-end hpgp hpg-al-ok))))

(defthm hpg-obj-pop-ok (al-keeps-ok (mv-nth 1 (hpg-obj-pop hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-obj-pop)

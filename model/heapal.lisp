; clotran's heap under the model (PLAN step 33, stage 1b): ALLOCATION, at
; the level the Fortran is generated from (src/f/gen/heap_gen.inc),
; guard-verified, for each of the three pools: objects, vectors and texts.
;
; A slot comes from the free list's head, or else from past the used end
; while the pool has room (bumping `used`): GC.f90's obj_take, vec_take and
; str_take without a batch. With batching (several threads), a thread
; FILLS its batch from the list and the used end -- each slot taken from
; the end flagged free while it waits -- and takes the batch's last. USE is
; what gc_obj, gc_vec and gc_str then do to the slot: no longer free, not
; marked.
;
; The three pools are one text: *pool-alloc* below, written for a pool @
; whose functions are named %, instantiated as (o obj), (v vec) and
; (s str) -- h-@head is h-ohead, h-vhead, h-shead, and hpg-%-take is
; hpg-obj-take, hpg-vec-take, hpg-str-take. The proofs (heapal-proof.lisp)
; are one text the same way.
;
; heapal-proof.lisp: with the free list well formed -- the slots on it
; distinct, each free and used, linked head to 0 -- and the batch's slots
; distinct, free and off the list, a take hands out a slot that is free or
; past the used end, so never one in use and never one still on the list or
; in the batch; and taking, filling, using and the sweep's frees keep it so.

(in-package "ACL2")

(include-book "heapsw")

; ---- ONE TEXT, THREE POOLS ---------------------------------------------------------------

(defun pool-chars (cs o w)
  (declare (xargs :mode :program))
  (cond ((endp cs) nil)
        ((eql (car cs) #\@) (append o (pool-chars (cdr cs) o w)))
        ((eql (car cs) #\%) (append w (pool-chars (cdr cs) o w)))
        (t (cons (car cs) (pool-chars (cdr cs) o w)))))

; every symbol with an @ or a % in its name, renamed for the pool
(defun pool-tree (x o w)
  (declare (xargs :mode :program))
  (cond ((consp x) (cons (pool-tree (car x) o w) (pool-tree (cdr x) o w)))
        ((and (symbolp x) x (not (keywordp x))
              (or (member #\@ (coerce (symbol-name x) 'list)) (member #\% (coerce (symbol-name x) 'list))))
         (intern-in-package-of-symbol
          (coerce (pool-chars (coerce (symbol-name x) 'list) (coerce (symbol-name o) 'list) (coerce (symbol-name w) 'list))
                  'string)
          'hpg))
        (t x)))

; the forms, once for each pool
(defmacro for-pools (forms)
  `(progn ,@(pool-tree forms 'o 'obj) ,@(pool-tree forms 'v 'vec) ,@(pool-tree forms 's 'str)))

; ---- THE REGISTERS -------------------------------------------------------------------------

(defun hpg-al-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-sw-ok hpg)
       (natp (h-oused hpg)) (<= (h-oused hpg) *hb40*) (natp (h-ocap hpg)) (<= (h-ocap hpg) *hb40*)
       (<= (h-ob-length hpg) *hb40*) (natp (h-nob hpg)) (< (h-nob hpg) (h-ob-length hpg))
       (natp (h-vused hpg)) (<= (h-vused hpg) *hb40*) (natp (h-vcap hpg)) (<= (h-vcap hpg) *hb40*)
       (<= (h-vb-length hpg) *hb40*) (natp (h-nvb hpg)) (< (h-nvb hpg) (h-vb-length hpg))
       (natp (h-sused hpg)) (<= (h-sused hpg) *hb40*) (natp (h-scap hpg)) (<= (h-scap hpg) *hb40*)
       (<= (h-sb-length hpg) *hb40*) (natp (h-nsb hpg)) (< (h-nsb hpg) (h-sb-length hpg))))

(hsb64-elems h-obp) (hsb64-update h-obp) (hpg-elem ob)
(hsb64-elems h-vbp) (hsb64-update h-vbp) (hpg-elem vb)
(hsb64-elems h-sbp) (hsb64-update h-sbp) (hpg-elem sb)

; the stobj's scalars are integers, with hpgp closed
(defthm hpgp-scalars
  (implies (hpgp hpg)
           (and (integerp (nth *h-ohead* hpg)) (integerp (nth *h-vhead* hpg)) (integerp (nth *h-shead* hpg))
                (integerp (nth *h-oused* hpg)) (integerp (nth *h-nob* hpg))
                (integerp (nth *h-vused* hpg)) (integerp (nth *h-nvb* hpg))
                (integerp (nth *h-sused* hpg)) (integerp (nth *h-nsb* hpg))))
  :hints (("Goal" :in-theory (enable hpgp)))
  :rule-classes :forward-chaining)

(defmacro al-keeps-ok (call)
  `(implies (and (hpgp hpg) (hpg-al-ok hpg)) (and (hpgp ,call) (hpg-al-ok ,call))))

; ---- THE POOL'S ALLOCATION -------------------------------------------------------------------

(defconst *pool-alloc*
  '(
; what the pool's allocation registers say, with hpg-al-ok closed
(defthm hpg-%-al-ok-facts
  (implies (hpg-al-ok hpg)
           (and (natp (nth *h-n@b* hpg)) (< (nth *h-n@b* hpg) (len (nth *h-@bi* hpg)))
                (<= (len (nth *h-@bi* hpg)) *hb40*)
                (natp (nth *h-@used* hpg)) (<= (nth *h-@used* hpg) *hb40*)
                (natp (nth *h-@cap* hpg)) (<= (nth *h-@cap* hpg) *hb40*)
                (<= (len (nth *h-@nexti* hpg)) *hb40*) (<= (len (nth *h-@freei* hpg)) *hb40*)))
  :hints (("Goal" :in-theory (enable hpg-al-ok hpg-sw-ok hpg-ok hpg-lens)))
  :rule-classes :forward-chaining)

; the free list's head, or a slot past the used end, or 0: none
(defun hpg-%-take (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (hpg-al-ok hpg)))
  (let ((h (h-@head hpg)))
    (if (and (< 0 h) (< h (h-@next-length hpg)))
        (let ((hpg (update-h-@head (hpg-s64 (h-@nexti h hpg)) hpg)))
          (mv h hpg))
      (if (< (h-@used hpg) (h-@cap hpg))
          (let* ((u (+ 1 (h-@used hpg)))
                 (hpg (update-h-@used u hpg)))
            (mv u hpg))
        (mv 0 hpg)))))

; the slot handed out, in use: not free, not marked (gc_obj, gc_vec, gc_str)
(defun hpg-%-use (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-al-ok hpg) (natp i) (< i (h-@free-length hpg)) (< i (h-@mark-length hpg)))))
  (let ((hpg (update-h-@freei i 0 hpg)))
    (update-h-@marki i 0 hpg)))

; one slot into the batch: the free list's head
(defun hpg-%-fill-list (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-al-ok hpg) (< (+ 1 (h-n@b hpg)) (h-@b-length hpg))
                              (< 0 (h-@head hpg)) (< (h-@head hpg) (h-@next-length hpg)))))
  (let* ((h (h-@head hpg))
         (n (+ 1 (h-n@b hpg)))
         (hpg (update-h-@bi n h hpg))
         (hpg (update-h-n@b n hpg)))
    (update-h-@head (hpg-s64 (h-@nexti h hpg)) hpg)))

; one slot into the batch: past the used end, flagged free while it waits
(defun hpg-%-fill-end (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-al-ok hpg) (< (+ 1 (h-n@b hpg)) (h-@b-length hpg))
                              (< (h-@used hpg) (h-@cap hpg)) (< (+ 1 (h-@used hpg)) (h-@free-length hpg))
                              (< (+ 1 (h-@used hpg)) (h-@next-length hpg)))))
  (let* ((u (+ 1 (h-@used hpg)))
         (hpg (update-h-@used u hpg))
         (hpg (update-h-@freei u 1 hpg))
         (n (+ 1 (h-n@b hpg)))
         (hpg (update-h-@bi n u hpg)))
    (update-h-n@b n hpg)))

; the batch filled to its capacity from the list and the used end, at most
; fuel slots
(defun hpg-%-fill (fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel)
                  :guard (and (hpg-al-ok hpg) (natp fuel))))
  (if (or (zp fuel) (not (< (+ 1 (h-n@b hpg)) (h-@b-length hpg))))
      hpg
    (if (and (< 0 (h-@head hpg)) (< (h-@head hpg) (h-@next-length hpg)))
        (let ((hpg (hpg-%-fill-list hpg)))
          (hpg-%-fill (- fuel 1) hpg))
      (if (and (< (h-@used hpg) (h-@cap hpg)) (< (+ 1 (h-@used hpg)) (h-@free-length hpg))
               (< (+ 1 (h-@used hpg)) (h-@next-length hpg)))
          (let ((hpg (hpg-%-fill-end hpg)))
            (hpg-%-fill (- fuel 1) hpg))
        hpg))))

; the batch's last, or 0: an empty batch
(defun hpg-%-pop (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (hpg-al-ok hpg)))
  (let ((n (h-n@b hpg)))
    (if (and (< 0 n) (< n (h-@b-length hpg)))
        (let* ((i (h-@bi n hpg))
               (hpg (update-h-n@b (- n 1) hpg)))
          (mv i hpg))
      (mv 0 hpg))))

; ---- GUARDS ----

(defthm hpg-%-take-ok (al-keeps-ok (mv-nth 1 (hpg-%-take hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(defthm hpg-%-take-range
  (implies (and (hpgp hpg) (hpg-al-ok hpg))
           (and (natp (mv-nth 0 (hpg-%-take hpg))) (<= (mv-nth 0 (hpg-%-take hpg)) *hb40*)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-%-take)

(defthm hpg-%-use-ok
  (implies (and (natp i) (< i (len (nth *h-@freei* hpg))) (< i (len (nth *h-@marki* hpg))))
           (al-keeps-ok (hpg-%-use i hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-%-use)

(defthm hpg-%-fill-list-ok
  (implies (and (< (+ 1 (nth *h-n@b* hpg)) (len (nth *h-@bi* hpg)))
                (< 0 (nth *h-@head* hpg)) (< (nth *h-@head* hpg) (len (nth *h-@nexti* hpg))))
           (al-keeps-ok (hpg-%-fill-list hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-%-fill-list)
(defthm hpg-%-fill-end-ok
  (implies (and (< (+ 1 (nth *h-n@b* hpg)) (len (nth *h-@bi* hpg)))
                (< (nth *h-@used* hpg) (nth *h-@cap* hpg)) (< (+ 1 (nth *h-@used* hpg)) (len (nth *h-@freei* hpg)))
                (< (+ 1 (nth *h-@used* hpg)) (len (nth *h-@nexti* hpg))))
           (al-keeps-ok (hpg-%-fill-end hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-%-fill-end)
(defthm hpg-%-fill-ok (al-keeps-ok (hpg-%-fill fuel hpg))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-%-fill-list hpg-%-fill-end hpgp hpg-al-ok))))
(verify-guards hpg-%-fill :hints (("Goal" :in-theory (disable nth update-nth hpg-%-fill-list hpg-%-fill-end hpgp hpg-al-ok))))

(defthm hpg-%-pop-ok (al-keeps-ok (mv-nth 1 (hpg-%-pop hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-%-pop)
))

(make-event (list 'for-pools *pool-alloc*))

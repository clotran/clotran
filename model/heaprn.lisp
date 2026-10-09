; clotran's heap under the model (PLAN step 33, stage 1b): THE ARENA'S
; ALLOCATION, at the level the Fortran is generated from
; (src/f/gen/heap_gen.inc), guard-verified.
;
; A vector's elements live in a run of the arena: 2^(c-1) words for its
; size class c, the smallest that holds it. A run comes from its class's
; free list -- linked through the first word's ival, as the sweep's
; hpg-slab-free left it -- or else fresh from past the arena's used end,
; if it fits. With batching, the thread's batch of its class (classes 1
; to 8, 64 runs each) is filled the same way when empty and the run is
; the batch's last: GC.f90's run_take, runs_fill and slab_alloc. A run
; that does not fit is 0 here: the caller grows the arena, with the world
; stopped, and asks again.
;
; heaprn-proof.lisp: no run handed out overlaps a run still free or
; batched, and taking, filling and the sweep's frees keep the free and
; batched runs apart from one another and inside the used arena.

(in-package "ACL2")

(include-book "heapal")

(defconst *run-batch* 64)
(defconst *run-classes* 8)

(defun hpg-rn-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-al-ok hpg)
       (natp (h-aused hpg)) (<= (h-aused hpg) *hb40*) (natp (h-acap hpg)) (<= (h-acap hpg) *hb40*)
       (natp (h-areu hpg)) (<= (h-areu hpg) *hb40*) (natp (h-afre hpg)) (<= (h-afre hpg) *hb40*)
       (natp (h-asince hpg)) (<= (h-asince hpg) *hb40*)
       (<= (h-rb-length hpg) *hb40*) (<= (h-nrb-length hpg) *hb40*)
       (<= (h-aival-length hpg) *hb40*) (<= (h-chead-length hpg) *hb40*)))

; a class's run length, 2^(c-1): k from 1, p from 1, doubling
(defun hpg-class-len (c k p)
  (declare (xargs :measure (nfix (- (nfix c) (nfix k)))
                  :guard (and (natp c) (<= c 64) (natp k) (natp p) (<= p *hb40*))))
  (if (or (not (natp c)) (not (natp k)) (<= c k) (< 64 c))
      (hpg-n40 p)
    (hpg-class-len c (+ 1 k) (hpg-n40 (* 2 (hpg-n40 p))))))

; a run of class c, l words: its free list's head, or fresh past the used
; end if it fits, or 0
(defun hpg-run-new (c l hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))))
  (let ((h (if (< c (h-chead-length hpg)) (h-cheadi c hpg) 0)))
    (if (and (< 0 h) (< h (h-aival-length hpg)))
        (let* ((hpg (update-h-cheadi c (hpg-s64 (h-aivali h hpg)) hpg))
               (hpg (update-h-areu (hpg-add (h-areu hpg) 1) hpg))
               (hpg (update-h-asince (hpg-add (h-asince hpg) l) hpg)))
          (mv h hpg))
      (if (and (< 0 l) (<= (+ (h-aused hpg) l) (h-acap hpg)))
          (let* ((off (+ 1 (h-aused hpg)))
                 (hpg (update-h-aused (+ (h-aused hpg) l) hpg))
                 (hpg (update-h-afre (hpg-add (h-afre hpg) 1) hpg))
                 (hpg (update-h-asince (hpg-add (h-asince hpg) l) hpg)))
            (mv off hpg))
        (mv 0 hpg)))))

; the batch's slot for class c's k-th run
(defmacro rb-at (c k) `(+ (* (- ,c 1) *run-batch*) ,k))

; a run onto class c's batch, as its n+1-th
(defun hpg-run-push (c n off hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (<= 1 c) (< c (h-nrb-length hpg)) (natp n) (< n *run-batch*)
                              (< (rb-at c (+ 1 n)) (h-rb-length hpg)) (natp off) (<= off *hb40*))))
  (let ((hpg (update-h-rbi (rb-at c (+ 1 n)) off hpg)))
    (update-h-nrbi c (+ 1 n) hpg)))

; class c's batch filled to 64 from its free list and the arena's end, at
; most fuel runs
(defun hpg-runs-fill (c l fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel)
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*) (natp fuel))))
  (if (or (zp fuel) (not (and (<= 1 c) (<= c *run-classes*) (< c (h-nrb-length hpg)))))
      hpg
    (let ((n (h-nrbi c hpg)))
      (if (not (and (<= 0 n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (h-rb-length hpg))))
          hpg
        (mv-let (off hpg) (hpg-run-new c l hpg)
          (if (equal off 0)
              hpg
            (let ((hpg (hpg-run-push c n off hpg)))
              (hpg-runs-fill c l (- fuel 1) hpg))))))))

; class c's batch's last, or 0 (and nothing popped when the last is not a
; run, which a batch never holds)
(defun hpg-run-pop (c hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-rn-ok hpg) (natp c))))
  (if (and (<= 1 c) (<= c *run-classes*) (< c (h-nrb-length hpg)))
      (let ((n (h-nrbi c hpg)))
        (if (and (< 0 n) (<= n *run-batch*) (< (rb-at c n) (h-rb-length hpg)))
            (let ((off (h-rbi (rb-at c n) hpg)))
              (if (< 0 off)
                  (let ((hpg (update-h-nrbi c (- n 1) hpg)))
                    (mv off hpg))
                (mv 0 hpg)))
          (mv 0 hpg)))
    (mv 0 hpg)))

; a run for a vector of n: from the thread's batch of its class when
; batching (not 0) and the class is small, else from the free list or the
; arena's end; 0 when it does not fit
; class c's batch's last, or else a run from its list or the arena's end
(defun hpg-run-from-batch (c l hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*))))
  (mv-let (off hpg) (hpg-run-pop c hpg)
    (if (< 0 off)
        (mv off hpg)
      (hpg-run-new c l hpg))))

; a run of class c, l words: through the batch, filled first if empty,
; when batching and the class is small; else from the list or the end
(defun hpg-run-take-c (c l batching hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp c) (natp l) (<= l *hb40*) (integerp batching))))
  (if (and (not (equal batching 0)) (<= c *run-classes*))
      (if (and (< c (h-nrb-length hpg)) (equal (h-nrbi c hpg) 0))
          (let ((hpg (hpg-runs-fill c l *run-batch* hpg)))
            (hpg-run-from-batch c l hpg))
        (hpg-run-from-batch c l hpg))
    (hpg-run-new c l hpg)))

(defun hpg-run-take (n batching hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-rn-ok hpg) (natp n) (<= n *hb40*) (integerp batching))))
  (if (not (< 0 n))
      (mv 0 hpg)
    (let* ((c (hpg-size-class n 1 1))
           (l (hpg-class-len c 1 1)))
      (hpg-run-take-c c l batching hpg))))

; ---- GUARDS ---------------------------------------------------------------------------------

(hsb64-elems h-rbp) (hsb64-update h-rbp) (hpg-elem rb)
(hsb64-elems h-nrbp) (hsb64-update h-nrbp) (hpg-elem nrb)

(defthm hpgp-arena-scalars
  (implies (hpgp hpg)
           (and (integerp (nth *h-aused* hpg)) (integerp (nth *h-acap* hpg))
                (integerp (nth *h-areu* hpg)) (integerp (nth *h-afre* hpg)) (integerp (nth *h-asince* hpg))))
  :hints (("Goal" :in-theory (enable hpgp)))
  :rule-classes :forward-chaining)

(defthm hpg-rn-ok-facts
  (implies (hpg-rn-ok hpg)
           (and (hpg-al-ok hpg)
                (natp (nth *h-aused* hpg)) (<= (nth *h-aused* hpg) *hb40*)
                (natp (nth *h-acap* hpg)) (<= (nth *h-acap* hpg) *hb40*)
                (natp (nth *h-areu* hpg)) (<= (nth *h-areu* hpg) *hb40*)
                (natp (nth *h-afre* hpg)) (<= (nth *h-afre* hpg) *hb40*)
                (natp (nth *h-asince* hpg)) (<= (nth *h-asince* hpg) *hb40*)
                (<= (len (nth *h-rbi* hpg)) *hb40*) (<= (len (nth *h-nrbi* hpg)) *hb40*)
                (<= (len (nth *h-aivali* hpg)) *hb40*) (<= (len (nth *h-cheadi* hpg)) *hb40*)))
  :rule-classes :forward-chaining)

(defthm hpg-class-len-bounds
  (and (natp (hpg-class-len c k p)) (<= (hpg-class-len c k p) *hb40*))
  :rule-classes ((:rewrite) (:linear :corollary (<= (hpg-class-len c k p) *hb40*))
                 (:type-prescription :corollary (natp (hpg-class-len c k p)))))

; ---- FRAMES: A WRITE THE ARENA MAKES KEEPS THE STOBJ'S TYPE AND hpg-rn-ok ----

(defmacro rn-scalar-frame (name fld)
  `(defthm ,name
     (implies (and (hpgp h) (hpg-rn-ok h) (natp v) (<= v *hb40*))
              (and (hpgp (update-nth ,fld v h)) (hpg-rn-ok (update-nth ,fld v h))))
     :hints (("Goal" :in-theory (e/d (hpgp) (nth update-nth))))))
(rn-scalar-frame aused-frame *h-aused*) (rn-scalar-frame areu-frame *h-areu*)
(rn-scalar-frame afre-frame *h-afre*) (rn-scalar-frame asince-frame *h-asince*)

(defmacro rn-array-frame (name fld)
  `(defthm ,name
     (implies (and (equal x (nth ,fld h)) (hpgp h) (hpg-rn-ok h) (natp i) (< i (len x)) (sb64ip v))
              (and (hpgp (update-nth ,fld (update-nth i v x) h))
                   (hpg-rn-ok (update-nth ,fld (update-nth i v x) h))))
     :hints (("Goal" :in-theory (e/d (hpgp) (nth update-nth))))))
(rn-array-frame chead-frame *h-cheadi*) (rn-array-frame rb-frame *h-rbi*) (rn-array-frame nrb-frame *h-nrbi*)

(in-theory (disable hpgp hpg-rn-ok))

(defthm hpg-s64-sb64 (sb64ip (hpg-s64 x)) :hints (("Goal" :in-theory (enable hpg-s64))))

(defmacro rn-keeps-ok (call)
  `(implies (and (hpgp hpg) (hpg-rn-ok hpg)) (and (hpgp ,call) (hpg-rn-ok ,call))))

(defthm hpg-run-new-ok
  (implies (and (natp c) (natp l) (<= l *hb40*)) (rn-keeps-ok (mv-nth 1 (hpg-run-new c l hpg))))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(defthm hpg-run-new-range
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c) (natp l))
           (and (natp (car (hpg-run-new c l hpg))) (<= (car (hpg-run-new c l hpg)) *hb40*)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
; a run taken leaves the batches as they were
(defthm hpg-run-new-batches
  (and (equal (nth *h-nrbi* (mv-nth 1 (hpg-run-new c l hpg))) (nth *h-nrbi* hpg))
       (equal (nth *h-rbi* (mv-nth 1 (hpg-run-new c l hpg))) (nth *h-rbi* hpg)))
  :hints (("Goal" :in-theory (disable nth))))
(verify-guards hpg-run-new :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm hpg-run-push-ok
  (implies (and (natp c) (<= 1 c) (< c (len (nth *h-nrbi* hpg))) (natp n) (< n *run-batch*)
                (< (rb-at c (+ 1 n)) (len (nth *h-rbi* hpg))) (natp off) (<= off *hb40*))
           (rn-keeps-ok (hpg-run-push c n off hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-run-push)

(defthm hpg-runs-fill-ok
  (implies (and (natp c) (natp l) (<= l *hb40*)) (rn-keeps-ok (hpg-runs-fill c l fuel hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-run-new hpg-run-push hpgp hpg-rn-ok))))
(verify-guards hpg-runs-fill :hints (("Goal" :in-theory (disable nth update-nth hpg-run-new hpg-run-push hpgp hpg-rn-ok))))

; a count one down is an integer when the count is (the element lemmas say
; so only by rewriting)
(defthm integerp-one-down (implies (integerp x) (integerp (+ -1 x))))

(defthm hpg-run-pop-ok (implies (natp c) (rn-keeps-ok (mv-nth 1 (hpg-run-pop c hpg))))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(defthm hpg-run-pop-range
  (implies (and (hpgp hpg) (hpg-rn-ok hpg) (natp c))
           (and (integerp (car (hpg-run-pop c hpg))) (rationalp (car (hpg-run-pop c hpg)))))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-nrb-elem hpg-rb-elem) :use ((:instance hpg-nrb-elem (j c)) (:instance hpg-rb-elem (j (rb-at c (nth c (nth *h-nrbi* hpg)))))))))
(verify-guards hpg-run-pop :hints (("Goal" :in-theory (disable nth update-nth hpg-nrb-elem hpg-rb-elem) :use ((:instance hpg-nrb-elem (j c)) (:instance hpg-rb-elem (j (rb-at c (nth c (nth *h-nrbi* hpg)))))))))

(defthm hpg-run-from-batch-ok
  (implies (and (natp c) (natp l) (<= l *hb40*)) (rn-keeps-ok (mv-nth 1 (hpg-run-from-batch c l hpg))))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-run-new hpg-run-pop hpgp hpg-rn-ok))))
(verify-guards hpg-run-from-batch :hints (("Goal" :in-theory (disable nth update-nth hpg-run-new hpg-run-pop hpgp hpg-rn-ok))))
(defthm hpg-run-take-c-ok
  (implies (and (natp c) (natp l) (<= l *hb40*)) (rn-keeps-ok (mv-nth 1 (hpg-run-take-c c l batching hpg))))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-run-new hpg-runs-fill hpg-run-from-batch hpgp hpg-rn-ok))))
(verify-guards hpg-run-take-c :hints (("Goal" :in-theory (disable nth update-nth hpg-run-new hpg-runs-fill hpg-run-from-batch hpgp hpg-rn-ok))))
(defthm hpg-run-take-ok
  (implies (natp n) (rn-keeps-ok (mv-nth 1 (hpg-run-take n batching hpg))))
  :hints (("Goal" :in-theory (disable nth update-nth hpg-run-take-c hpgp hpg-rn-ok))))
(verify-guards hpg-run-take :hints (("Goal" :in-theory (disable nth update-nth hpg-run-take-c hpgp hpg-rn-ok))))

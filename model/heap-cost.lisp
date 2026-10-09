; The heap's cost (PLAN step 33), by step counting, as vm-cost.lisp does
; the VM's (James, 2026-10-04 and 2026-10-09: cost theorems for every
; algorithm in the model). A function with no loop is one step; a loop's
; steps are its turns, each a constant number of the stobj's reads and
; writes (an array read or write by index, which nth and update-nth stand
; for -- their list walk is the logic's, not the cost of the thing
; modelled). Each count below follows its function's own recursion, the
; state stepped by the function's own body.
;
;   the size class of n <= 2^40       at most 41 doublings
;   a class's run length              at most 63 doublings
;   a pool's batch fill               at most fuel turns, and at most the
;                                     batch's room
;   the sweep of slots i .. n         exactly n+1-i turns, a vector's free
;                                     at most 41 steps more
;   the arena's batch fill            at most fuel turns, and at most the
;                                     batch's room, 64
;   run_take                          at most 41 + 63 + 64 + 2 steps
;   the mark stack's drain            at most the stack's and the unmarked
;                                     heap's scan costs: each object and
;                                     vector scanned at most once
;
; so taking a slot or a run is O(1), a sweep O(pool), and marking O(heap).

(in-package "ACL2")

(include-book "heaprn")

(in-theory (disable nth update-nth hpgp))

; ---- SIZE CLASSES ---------------------------------------------------------------------------

(defun-nx size-class-steps (n c p)
  (declare (xargs :measure (nfix (- (+ 1 *hb40*) (nfix p)))))
  (if (or (not (natp p)) (< p 1) (<= n p) (< *hb40* p) (not (natp c)) (<= 64 c))
      0
    (+ 1 (size-class-steps n (+ 1 c) (* 2 p)))))

; how many doublings take p past 2^40
(defun dbl (p)
  (declare (xargs :measure (nfix (- (+ 1 *hb40*) (nfix p)))))
  (if (or (not (natp p)) (< p 1) (< *hb40* p)) 0 (+ 1 (dbl (* 2 p)))))

(defthm size-class-steps-dbl (<= (size-class-steps n c p) (dbl p)))

(defthm size-class-steps-41 (<= (size-class-steps n c 1) 41)
  :hints (("Goal" :use ((:instance size-class-steps-dbl (p 1))) :in-theory (disable size-class-steps-dbl)))
  :rule-classes (:rewrite :linear))

(defun-nx class-len-steps (c k p)
  (declare (xargs :measure (nfix (- (nfix c) (nfix k)))))
  (if (or (not (natp c)) (not (natp k)) (<= c k) (< 64 c))
      0
    (+ 1 (class-len-steps c (+ 1 k) (hpg-n40 (* 2 (hpg-n40 p)))))))

(defthm class-len-steps-bound
  (implies (and (natp k) (<= c 64)) (<= (class-len-steps c k p) (nfix (- c k)))))
(defthm class-len-steps-63 (<= (class-len-steps c 1 p) 63)
  :hints (("Goal" :cases ((<= c 64)) :use ((:instance class-len-steps-bound (k 1)))))
  :rule-classes (:rewrite :linear))

; ---- THE POOLS' BATCH FILL ----------------------------------------------------------------

(defconst *pool-cost*
  '(
(defun-nx hpg-%-fill-steps (fuel hpg)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (< (+ 1 (h-n@b hpg)) (h-@b-length hpg))))
      0
    (if (and (< 0 (h-@head hpg)) (< (h-@head hpg) (h-@next-length hpg)))
        (+ 1 (hpg-%-fill-steps (- fuel 1) (hpg-%-fill-list hpg)))
      (if (and (< (h-@used hpg) (h-@cap hpg)) (< (+ 1 (h-@used hpg)) (h-@free-length hpg))
               (< (+ 1 (h-@used hpg)) (h-@next-length hpg)))
          (+ 1 (hpg-%-fill-steps (- fuel 1) (hpg-%-fill-end hpg)))
        0))))

(defthm hpg-%-fill-list-batch
  (implies (and (natp (nth *h-n@b* hpg)) (< (+ 1 (nth *h-n@b* hpg)) (len (nth *h-@bi* hpg))))
  (and (equal (nth *h-n@b* (hpg-%-fill-list hpg)) (+ 1 (nth *h-n@b* hpg)))
       (equal (len (nth *h-@bi* (hpg-%-fill-list hpg)))
              (len (nth *h-@bi* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-%-fill-list))))
(defthm hpg-%-fill-end-batch
  (implies (and (natp (nth *h-n@b* hpg)) (< (+ 1 (nth *h-n@b* hpg)) (len (nth *h-@bi* hpg))))
  (and (equal (nth *h-n@b* (hpg-%-fill-end hpg)) (+ 1 (nth *h-n@b* hpg)))
       (equal (len (nth *h-@bi* (hpg-%-fill-end hpg)))
              (len (nth *h-@bi* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-%-fill-end))))

; A FILL takes at most fuel turns, and at most the batch's room
(defthm hpg-%-fill-cost
  (implies (natp (nth *h-n@b* hpg))
           (and (<= (hpg-%-fill-steps fuel hpg) (nfix fuel))
                (<= (hpg-%-fill-steps fuel hpg) (nfix (- (- (len (nth *h-@bi* hpg)) 1) (nth *h-n@b* hpg))))))
  :hints (("Goal" :induct (hpg-%-fill-steps fuel hpg)
           :in-theory (disable hpg-%-fill-list hpg-%-fill-end))))
))

(make-event (list 'for-pools *pool-cost*))

; ---- THE SWEEP ------------------------------------------------------------------------------

(defun-nx sweep-steps (i n)
  (declare (xargs :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (< n i)) 0 (+ 1 (sweep-steps (+ 1 i) n))))

; A SWEEP of slots i .. n takes exactly n+1-i turns (hpg-sweep-objs,
; -vecs and -strs all recur so, whatever each turn frees)
(defthm sweep-cost
  (implies (and (natp i) (natp n)) (equal (sweep-steps i n) (nfix (- (+ 1 n) i)))))

; each turn's free: a constant, and a vector's free one size class, at
; most 41 steps more
(defthm slab-free-cost (<= (size-class-steps len 1 1) 41)
  :hints (("Goal" :use ((:instance size-class-steps-41 (n len) (c 1))))))

; ---- THE ARENA ------------------------------------------------------------------------------

(defun-nx runs-fill-steps (c l fuel hpg)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (and (<= 1 c) (<= c *run-classes*) (< c (h-nrb-length hpg)))))
      0
    (let ((n (h-nrbi c hpg)))
      (if (not (and (<= 0 n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (h-rb-length hpg))))
          0
        (mv-let (off hpg) (hpg-run-new c l hpg)
          (if (equal off 0)
              0
            (+ 1 (runs-fill-steps c l (- fuel 1) (hpg-run-push c n off hpg)))))))))

(defthm hpg-run-new-nrb
  (and (equal (nth *h-nrbi* (mv-nth 1 (hpg-run-new c l hpg))) (nth *h-nrbi* hpg))
       (equal (len (nth *h-rbi* (mv-nth 1 (hpg-run-new c l hpg)))) (len (nth *h-rbi* hpg))))
  :hints (("Goal" :in-theory (enable hpg-run-new nth update-nth))))
(defthm hpg-run-push-nrb
  (implies (and (natp c) (< c (len (nth *h-nrbi* hpg))))
           (equal (nth c (nth *h-nrbi* (hpg-run-push c n off hpg))) (+ 1 n)))
  :hints (("Goal" :in-theory (enable hpg-run-push))))
(defthm hpg-run-push-len
  (implies (and (natp c) (< c (len (nth *h-nrbi* hpg))))
           (equal (len (nth *h-nrbi* (hpg-run-push c n off hpg))) (len (nth *h-nrbi* hpg))))
  :hints (("Goal" :in-theory (enable hpg-run-push))))

; THE ARENA'S FILL takes at most fuel turns, and at most its batch's room
(defthm runs-fill-cost
  (implies (and (natp c) (integerp (nth c (nth *h-nrbi* hpg))))
           (and (<= (runs-fill-steps c l fuel hpg) (nfix fuel))
                (<= (runs-fill-steps c l fuel hpg) (nfix (- *run-batch* (nth c (nth *h-nrbi* hpg)))))))
  :hints (("Goal" :induct (runs-fill-steps c l fuel hpg) :in-theory (disable hpg-run-new hpg-run-push))))

; RUN_TAKE: a size class, a run length, at most one fill, and a pop or a
; take -- each of those last a constant
(defun-nx run-take-steps (n batching hpg)
  (if (not (< 0 n))
      1
    (let* ((c (hpg-size-class n 1 1)) (l (hpg-class-len c 1 1)))
      (+ (size-class-steps n 1 1) (class-len-steps c 1 1) 2
         (if (and (not (equal batching 0)) (<= c *run-classes*)
                  (< c (h-nrb-length hpg)) (equal (h-nrbi c hpg) 0))
             (runs-fill-steps c l *run-batch* hpg)
           0)))))

(defthm run-take-cost (<= (run-take-steps n batching hpg) (+ 41 63 64 2))
  :hints (("Goal" :in-theory (disable size-class-steps class-len-steps runs-fill-steps hpg-size-class hpg-class-len runs-fill-cost)
           :use ((:instance runs-fill-cost (c (hpg-size-class n 1 1)) (l (hpg-class-len (hpg-size-class n 1 1) 1 1))
                            (fuel 64))))))

; ---- MARKING: THE DRAIN IS LINEAR IN THE HEAP --------------------------------------------
;
; A potential. Each entry on the mark stack carries the cost of scanning
; it -- 6 for an object (its turn and its five slots), 1 + its length for
; a vector, 1 for anything else -- and each unmarked object or vector the
; same, in reserve. A push only moves an object's or vector's cost from
; the reserve onto the stack (or drops it, when the stack is full); a turn
; pops an entry and does at most that entry's cost of work. So the
; drain's work is at most the stack's and the unmarked heap's cost when it
; starts: every object and every vector scanned at most once.

(defmacro omark (h) `(nth *h-omarki* ,h))
(defmacro vmark (h) `(nth *h-vmarki* ,h))
(defmacro vlen (h) `(nth *h-vleni* ,h))
(defmacro mtag (h) `(nth *h-mtagi* ,h))
(defmacro mref (h) `(nth *h-mrefi* ,h))

(defun ecost (tag ref h)
  (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) 6)
        ((and (equal tag 9) (natp ref) (< 0 ref) (< ref (len (vlen h)))) (+ 1 (nfix (nth ref (vlen h)))))
        (t 1)))

(defun ssum (k h)
  (if (zp k) 0 (+ (ecost (nth (1- k) (mtag h)) (nth (1- k) (mref h)) h) (ssum (1- k) h))))

(defun unm-o (i n h)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (<= n i)) 0
    (+ (if (equal (nth i (omark h)) 0) 6 0) (unm-o (+ 1 i) n h))))

(defun unm-v (i n h)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (<= n i)) 0
    (+ (if (and (equal (nth i (vmark h)) 0) (< i (len (vlen h)))) (+ 1 (nfix (nth i (vlen h)))) 0)
       (unm-v (+ 1 i) n h))))

(defun phi (h) (+ (ssum (nth *h-msp* h) h) (unm-o 1 (len (omark h)) h) (unm-v 1 (len (vmark h)) h)))

; ---- what each sum reads

(defthm ecost-frame (implies (and (natp fld) (not (equal fld *h-vleni*))) (equal (ecost tag ref (update-nth fld v h)) (ecost tag ref h))))
(defthm ssum-frame
  (implies (and (natp fld) (not (equal fld *h-vleni*)) (not (equal fld *h-mtagi*)) (not (equal fld *h-mrefi*)))
           (equal (ssum k (update-nth fld v h)) (ssum k h))))
(defthm unm-o-frame (implies (and (natp fld) (not (equal fld *h-omarki*))) (equal (unm-o i n (update-nth fld v h)) (unm-o i n h))))
(defthm unm-v-frame
  (implies (and (natp fld) (not (equal fld *h-vmarki*)) (not (equal fld *h-vleni*)))
           (equal (unm-v i n (update-nth fld v h)) (unm-v i n h))))

; a stack slot written at or above k: the sum below k as it was
(defthm ssum-write-above
  (implies (and (natp k) (natp j) (<= k j))
           (and (implies (equal x (mtag h)) (equal (ssum k (update-nth *h-mtagi* (update-nth j v x) h)) (ssum k h)))
                (implies (equal x (mref h)) (equal (ssum k (update-nth *h-mrefi* (update-nth j v x) h)) (ssum k h))))))

(defthm ssum-step (implies (posp k) (equal (ssum k h) (+ (ecost (nth (1- k) (mtag h)) (nth (1- k) (mref h)) h) (ssum (1- k) h)))))

; a mark written below the range: the sum as it was
(defthm unm-o-write-below
  (implies (and (equal x (omark h)) (natp r) (< r i))
           (equal (unm-o i n (update-nth *h-omarki* (update-nth r v x) h)) (unm-o i n h)))
  :hints (("Goal" :induct (unm-o i n h))))
(defthm unm-v-write-below
  (implies (and (equal x (vmark h)) (natp r) (< r i))
           (equal (unm-v i n (update-nth *h-vmarki* (update-nth r v x) h)) (unm-v i n h)))
  :hints (("Goal" :induct (unm-v i n h))))

; an object or vector marked: its cost out of the reserve
(defthm unm-o-mark
  (implies (and (equal x (omark h)) (natp r) (natp i) (natp n) (<= i r) (< r n) (equal (nth r x) 0))
           (equal (unm-o i n (update-nth *h-omarki* (update-nth r v x) h))
                  (- (unm-o i n h) (if (equal v 0) 0 6))))
  :hints (("Goal" :induct (unm-o i n h))))
(defthm unm-v-mark
  (implies (and (equal x (vmark h)) (natp r) (natp i) (natp n) (<= i r) (< r n) (equal (nth r x) 0) (< r (len (vlen h))))
           (equal (unm-v i n (update-nth *h-vmarki* (update-nth r v x) h))
                  (- (unm-v i n h) (if (equal v 0) 0 (+ 1 (nfix (nth r (vlen h))))))))
  :hints (("Goal" :induct (unm-v i n h))))

(defthm unm-o-nonneg (<= 0 (unm-o i n h)) :rule-classes :linear)
(defthm unm-v-nonneg (<= 0 (unm-v i n h)) :rule-classes :linear)
(defthm ssum-nonneg (<= 0 (ssum k h)) :rule-classes :linear)

; ---- the push, the scans, a turn

(defthm hpg-ok-lens-facts
  (implies (hpg-ok h)
           (and (<= (len (omark h)) *hb40*) (natp (nth *h-msp* h)) (<= (nth *h-msp* h) (len (mtag h)))
                (<= (len (mtag h)) (len (mref h)))))
  :rule-classes :forward-chaining)

; onto the stack: the entry's cost added, or nothing when it is full
(defthm phi-spush
  (implies (and (natp (nth *h-msp* h)) (<= (nth *h-msp* h) (len (mtag h))) (<= (len (mtag h)) (len (mref h))))
           (<= (phi (hpg-spush tag ref h)) (+ (phi h) (ecost tag ref h))))
  :hints (("Goal" :in-theory (enable hpg-spush))))

(in-theory (disable hpg-ok))

; a field the potential does not read, written
(defthm phi-frame
  (implies (and (natp fld) (not (equal fld *h-msp*)) (not (equal fld *h-mtagi*)) (not (equal fld *h-mrefi*))
                (not (equal fld *h-omarki*)) (not (equal fld *h-vmarki*)) (not (equal fld *h-vleni*)))
           (equal (phi (update-nth fld v h)) (phi h))))

; an object or a vector marked: its cost out of the reserve
(defthm phi-mark-obj
  (implies (and (equal x (omark h)) (natp ref) (< 0 ref) (< ref (len x)) (equal (nth ref x) 0))
           (equal (phi (update-nth *h-omarki* (update-nth ref 1 x) h)) (- (phi h) 6))))
(defthm phi-mark-vec
  (implies (and (equal x (vmark h)) (natp ref) (< 0 ref) (< ref (len x)) (< ref (len (vlen h))) (equal (nth ref x) 0))
           (equal (phi (update-nth *h-vmarki* (update-nth ref 1 x) h)) (- (phi h) (+ 1 (nfix (nth ref (vlen h))))))))

(in-theory (disable phi))

(defthm phi-spush-linear
  (implies (and (natp (nth *h-msp* h)) (<= (nth *h-msp* h) (len (mtag h))) (<= (len (mtag h)) (len (mref h))))
           (<= (phi (hpg-spush tag ref h)) (+ (phi h) (ecost tag ref h))))
  :hints (("Goal" :use phi-spush :in-theory (disable phi-spush)))
  :rule-classes :linear)

(defthm phi-push
  (implies (and (hpgp h) (hpg-ok h) (sb64p tag) (sb64p ref)) (<= (phi (hpg-push tag ref h)) (phi h)))
  :hints (("Goal" :in-theory (e/d (hpg-push) (phi-spush))
           :use ((:instance phi-spush-linear (tag 8)
                            (h (update-nth *h-nobj* (hpg-add (nth *h-nobj* h) 1)
                                           (update-nth *h-omarki* (update-nth ref 1 (omark h)) h)))))))
  :rule-classes (:rewrite :linear))



; a slot's or a run word's reference pushed, as the scans push them
(defthm phi-push-slot
  (implies (and (hpgp h) (hpg-ok h) (natp j) (< j (len (nth *h-otagi* h))) (< j (len (nth *h-orefi* h))))
           (<= (phi (hpg-push (nth j (nth *h-otagi* h)) (nth j (nth *h-orefi* h)) h)) (phi h)))
  :hints (("Goal" :in-theory (disable phi-push hpg-otag-elem hpg-oref-elem)
           :use ((:instance phi-push (tag (nth j (nth *h-otagi* h))) (ref (nth j (nth *h-orefi* h))))
                 (:instance hpg-otag-elem (hpg h)) (:instance hpg-oref-elem (hpg h)))))
  :rule-classes (:rewrite :linear))
(defthm phi-push-word
  (implies (and (hpgp h) (hpg-ok h) (natp j) (< j (len (nth *h-atagi* h))) (< j (len (nth *h-arefi* h))))
           (<= (phi (hpg-push (nth j (nth *h-atagi* h)) (nth j (nth *h-arefi* h)) h)) (phi h)))
  :hints (("Goal" :in-theory (disable phi-push hpg-atag-elem hpg-aref-elem)
           :use ((:instance phi-push (tag (nth j (nth *h-atagi* h))) (ref (nth j (nth *h-arefi* h))))
                 (:instance hpg-atag-elem (hpg h)) (:instance hpg-aref-elem (hpg h)))))
  :rule-classes (:rewrite :linear))

(defun-nx scan-obj-steps (i k h)
  (declare (xargs :measure (nfix (- 5 (nfix k)))))
  (if (or (not (natp k)) (<= 5 k)) 0
    (let ((j (+ (* 5 i) k)))
      (if (and (< j (len (nth *h-otagi* h))) (< j (len (nth *h-orefi* h))))
          (+ 1 (scan-obj-steps i (+ 1 k) (hpg-push (nth j (nth *h-otagi* h)) (nth j (nth *h-orefi* h)) h)))
        0))))

(defun-nx scan-run-steps (j e h)
  (declare (xargs :measure (nfix (- (nfix e) (nfix j)))))
  (if (or (not (natp j)) (not (natp e)) (<= e j)) 0
    (if (and (< j (len (nth *h-atagi* h))) (< j (len (nth *h-arefi* h))))
        (+ 1 (scan-run-steps (+ 1 j) e (hpg-push (nth j (nth *h-atagi* h)) (nth j (nth *h-arefi* h)) h)))
      0)))

; AN OBJECT'S SCAN is at most its five slots, A RUN'S its length
(defthm scan-obj-cost (implies (natp k) (<= (scan-obj-steps i k h) (nfix (- 5 k)))))
(defthm scan-run-cost (<= (scan-run-steps j e h) (nfix (- (nfix e) (nfix j)))))

; and neither raises the potential
(defthm phi-scan-obj
  (implies (and (hpgp h) (hpg-ok h) (natp i)) (<= (phi (hpg-scan-obj i k h)) (phi h)))
  :hints (("Goal" :induct (hpg-scan-obj i k h) :in-theory (e/d (hpg-scan-obj) (hpg-ok))))
  :rule-classes (:rewrite :linear))
(defthm phi-scan-run
  (implies (and (hpgp h) (hpg-ok h)) (<= (phi (hpg-scan-run j e h)) (phi h)))
  :hints (("Goal" :induct (hpg-scan-run j e h) :in-theory (e/d (hpg-scan-run) (hpg-ok))))
  :rule-classes (:rewrite :linear))
(defthm phi-scan-vec
  (implies (and (hpgp h) (hpg-ok h)) (<= (phi (hpg-scan-vec i h)) (phi h)))
  :hints (("Goal" :in-theory (e/d (hpg-scan-vec) (hpg-ok hpg-scan-run))))
  :rule-classes (:rewrite :linear))

; one turn of the drain: the top popped and scanned
(defun-nx dstep (h)
  (let* ((sp (- (nth *h-msp* h) 1))
         (tag (nth sp (mtag h)))
         (ref (nth sp (mref h)))
         (h (update-nth *h-msp* sp h)))
    (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) (hpg-scan-obj ref 0 h))
          ((and (equal tag 9) (< 0 ref)) (hpg-scan-vec ref h))
          (t h))))

(defthm hpg-drain-is-dstep
  (equal (hpg-drain fuel h)
         (if (or (zp fuel) (zp (nth *h-msp* h)) (not (equal (nth *h-err* h) 0)))
             h
           (hpg-drain (- fuel 1) (dstep h))))
  :hints (("Goal" :in-theory (enable hpg-drain)))
  :rule-classes ((:definition :controller-alist ((hpg-drain t nil)))))

; a turn's work: one, and its scan's steps
(defun-nx turn-work (h)
  (let* ((sp (- (nth *h-msp* h) 1))
         (tag (nth sp (mtag h)))
         (ref (nth sp (mref h)))
         (h (update-nth *h-msp* sp h)))
    (+ 1 (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) (scan-obj-steps ref 0 h))
               ((and (equal tag 9) (< 0 ref) (< ref (len (nth *h-voffi* h))) (< ref (len (vlen h))))
                (let ((off (nfix (nth ref (nth *h-voffi* h)))) (n (nfix (nth ref (vlen h)))))
                  (if (and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*)) (scan-run-steps off (+ off n) h) 0)))
               (t 0)))))

(defmacro top-cost (h)
  `(ecost (nth (- (nth *h-msp* ,h) 1) (mtag ,h)) (nth (- (nth *h-msp* ,h) 1) (mref ,h)) ,h))

; A TURN does at most its entry's cost of work, and lowers the potential
; by at least that cost
(defthm turn-work-cost
  (implies (and (hpgp h) (hpg-ok h) (< 0 (nth *h-msp* h))) (<= (turn-work h) (top-cost h)))
  :hints (("Goal" :in-theory (disable scan-obj-steps scan-run-steps scan-obj-cost scan-run-cost)
           :use ((:instance scan-obj-cost (i (nth (- (nth *h-msp* h) 1) (mref h))) (k 0)
                            (h (update-nth *h-msp* (- (nth *h-msp* h) 1) h)))
                 (:instance scan-run-cost
                            (j (nfix (nth (nth (- (nth *h-msp* h) 1) (mref h)) (nth *h-voffi* h))))
                            (e (+ (nfix (nth (nth (- (nth *h-msp* h) 1) (mref h)) (nth *h-voffi* h)))
                                  (nfix (nth (nth (- (nth *h-msp* h) 1) (mref h)) (vlen h)))))
                            (h (update-nth *h-msp* (- (nth *h-msp* h) 1) h))))))
  :rule-classes (:rewrite :linear))

(defthm phi-dstep
  (implies (and (hpgp h) (hpg-ok h) (< 0 (nth *h-msp* h)))
           (<= (+ (phi (dstep h)) (top-cost h)) (phi h)))
  :hints (("Goal" :in-theory (e/d (phi) (hpg-ok hpg-scan-obj hpg-scan-vec phi-scan-obj phi-scan-vec))
           :use ((:instance phi-scan-obj (i (nth (- (nth *h-msp* h) 1) (mref h))) (k 0)
                            (h (update-nth *h-msp* (- (nth *h-msp* h) 1) h)))
                 (:instance phi-scan-vec (i (nth (- (nth *h-msp* h) 1) (mref h)))
                            (h (update-nth *h-msp* (- (nth *h-msp* h) 1) h))))))
  :rule-classes (:rewrite :linear))

; a turn keeps the heap well formed
(defthm dstep-ok
  (implies (and (hpgp h) (hpg-ok h) (< 0 (nth *h-msp* h))) (and (hpgp (dstep h)) (hpg-ok (dstep h))))
  :hints (("Goal" :in-theory (e/d (hpg-ok) (hpg-scan-obj hpg-scan-vec)))))

; ---- THE DRAIN'S WORK -------------------------------------------------------------------

(defun-nx drain-work (fuel h)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (zp (nth *h-msp* h)) (not (equal (nth *h-err* h) 0)))
      0
    (+ (turn-work h) (drain-work (- fuel 1) (dstep h)))))

; THE DRAIN'S WORK is at most the potential it starts with: the cost of
; scanning what is on the stack and every object and vector not yet
; marked, each once -- linear in the heap
(defthm drain-cost
  (implies (and (hpgp h) (hpg-ok h)) (<= (drain-work fuel h) (phi h)))
  :hints (("Goal" :induct (drain-work fuel h)
           :in-theory (disable turn-work dstep hpg-ok ecost phi turn-work-cost phi-dstep))
          ("Subgoal *1/2" :use (turn-work-cost phi-dstep))))

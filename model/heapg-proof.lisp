; The collector's marking (model/heapg.lisp) proved: a drain that empties
; its stack, with no overflow, leaves every marked object's and run's
; references marked -- the mark set closed, which is what a sweep of the
; unmarked needs (alloc-old.lisp's old-gc-invisible: a sweep that keeps a
; set closed under fields and holding the roots changes nothing a program
; observes).
;
; THE INVARIANT (hpg-inv): every marked object or run is on the stack (to
; be scanned) or BLACK (each reference it holds marked) -- or the stack
; overflowed and the run says so. Push, scan and pop keep it; an empty
; stack leaves only black.
;
; Underneath, the frame facts: marking writes no word of the pools
; (hpg-*-keeps), never unmarks (hpg-*-marks-up), and a push leaves what is
; below the stack's top as it was (hpg-*-stack-below).

(in-package "ACL2")

(include-book "heapg")

(in-theory (disable hpgp hpg-ok nth update-nth))

; ---- THE POOLS ARE NEVER WRITTEN ---------------------------------------------------------

(defmacro hpg-pool-same (a b)
  `(and (equal (nth *h-otagi* ,a) (nth *h-otagi* ,b)) (equal (nth *h-orefi* ,a) (nth *h-orefi* ,b))
        (equal (nth *h-voffi* ,a) (nth *h-voffi* ,b)) (equal (nth *h-vleni* ,a) (nth *h-vleni* ,b))
        (equal (nth *h-atagi* ,a) (nth *h-atagi* ,b)) (equal (nth *h-arefi* ,a) (nth *h-arefi* ,b))
        (equal (len (nth *h-omarki* ,a)) (len (nth *h-omarki* ,b)))
        (equal (len (nth *h-vmarki* ,a)) (len (nth *h-vmarki* ,b)))
        (equal (len (nth *h-smarki* ,a)) (len (nth *h-smarki* ,b)))))

(defthm hpg-spush-keeps (hpg-pool-same (hpg-spush tag ref hpg) hpg)
  :hints (("Goal" :in-theory (enable hpg-spush))))

(defthm hpg-push-keeps (hpg-pool-same (hpg-push tag ref hpg) hpg)
  :hints (("Goal" :in-theory (enable hpg-push))))

(defthm hpg-scan-obj-keeps (hpg-pool-same (hpg-scan-obj i k hpg) hpg)
  :hints (("Goal" :in-theory (enable hpg-scan-obj))))

(defthm hpg-scan-run-keeps (hpg-pool-same (hpg-scan-run j e hpg) hpg)
  :hints (("Goal" :in-theory (enable hpg-scan-run))))

(defthm hpg-scan-vec-keeps (hpg-pool-same (hpg-scan-vec i hpg) hpg)
  :hints (("Goal" :in-theory (enable hpg-scan-vec))))

(defthm hpg-drain-keeps (hpg-pool-same (hpg-drain fuel hpg) hpg)
  :hints (("Goal" :in-theory (enable hpg-drain))))

; ---- MARKS ONLY GO UP ------------------------------------------------------------------

(defun omarked (r hpg)
  (and (natp r) (< 0 r) (< r (len (nth *h-omarki* hpg))) (not (equal (nth r (nth *h-omarki* hpg)) 0))))
(defun vmarked (r hpg)
  (and (natp r) (< 0 r) (< r (len (nth *h-vmarki* hpg))) (not (equal (nth r (nth *h-vmarki* hpg)) 0))))
(defun smarked (r hpg)
  (and (natp r) (< 0 r) (< r (len (nth *h-smarki* hpg))) (not (equal (nth r (nth *h-smarki* hpg)) 0))))

(defmacro marks-up (op)
  `(implies (and (natp r) (< 0 r))
            (and (implies (omarked r hpg) (omarked r ,op))
                 (implies (vmarked r hpg) (vmarked r ,op))
                 (implies (smarked r hpg) (smarked r ,op)))))

; the push onto the stack touches the stack, its top and the error flag only
(defthm hpg-spush-fields
  (and (equal (nth *h-omarki* (hpg-spush tag ref hpg)) (nth *h-omarki* hpg))
       (equal (nth *h-vmarki* (hpg-spush tag ref hpg)) (nth *h-vmarki* hpg))
       (equal (nth *h-smarki* (hpg-spush tag ref hpg)) (nth *h-smarki* hpg))
       (equal (nth *h-vleni* (hpg-spush tag ref hpg)) (nth *h-vleni* hpg)))
  :hints (("Goal" :in-theory (enable hpg-spush))))

(defthm hpg-spush-marks-up (marks-up (hpg-spush tag ref hpg)))

(defthm hpg-push-marks-up (marks-up (hpg-push tag ref hpg))
  :hints (("Goal" :in-theory (enable hpg-push))))

(defthm hpg-scan-obj-marks-up (marks-up (hpg-scan-obj i k hpg))
  :hints (("Goal" :in-theory (e/d (hpg-scan-obj) (omarked vmarked smarked)))))

(defthm hpg-scan-run-marks-up (marks-up (hpg-scan-run j e hpg))
  :hints (("Goal" :in-theory (e/d (hpg-scan-run) (omarked vmarked smarked)))))

(defthm hpg-scan-vec-marks-up (marks-up (hpg-scan-vec i hpg))
  :hints (("Goal" :in-theory (e/d (hpg-scan-vec) (omarked vmarked smarked hpg-scan-run)))))

; the error flag, once set, stays
(defthm hpg-spush-err-up
  (implies (not (equal (nth *h-err* hpg) 0)) (not (equal (nth *h-err* (hpg-spush tag ref hpg)) 0)))
  :hints (("Goal" :in-theory (enable hpg-spush))))
(defthm hpg-push-err-up
  (implies (not (equal (nth *h-err* hpg) 0)) (not (equal (nth *h-err* (hpg-push tag ref hpg)) 0)))
  :hints (("Goal" :in-theory (enable hpg-push))))
(defthm hpg-scan-obj-err-up
  (implies (not (equal (nth *h-err* hpg) 0)) (not (equal (nth *h-err* (hpg-scan-obj i k hpg)) 0)))
  :hints (("Goal" :in-theory (enable hpg-scan-obj))))
(defthm hpg-scan-run-err-up
  (implies (not (equal (nth *h-err* hpg) 0)) (not (equal (nth *h-err* (hpg-scan-run j e hpg)) 0)))
  :hints (("Goal" :in-theory (enable hpg-scan-run))))
(defthm hpg-scan-vec-err-up
  (implies (not (equal (nth *h-err* hpg) 0)) (not (equal (nth *h-err* (hpg-scan-vec i hpg)) 0)))
  :hints (("Goal" :in-theory (e/d (hpg-scan-vec) (hpg-scan-run)))))

; ---- A REFERENCE HELD MARKED -------------------------------------------------------------

; what the scans make true of each word they push: the reference it holds
; is marked, or it is no reference the marker follows
(defun marked-ref (tag ref hpg)
  (cond ((not (and (integerp ref) (< 0 ref))) t)
        ((equal tag 8) (or (not (< ref (len (nth *h-omarki* hpg)))) (omarked ref hpg)))
        ((equal tag 9) (or (not (< ref (len (nth *h-vmarki* hpg)))) (not (< ref (len (nth *h-vleni* hpg))))
                           (vmarked ref hpg)))
        ((hpg-text-tag tag) (or (not (< ref (len (nth *h-smarki* hpg)))) (smarked ref hpg)))
        (t t)))

(defthm hpg-push-marks
  (marked-ref tag ref (hpg-push tag ref hpg))
  :hints (("Goal" :in-theory (enable hpg-push))))

(defmacro marked-ref-up (op)
  `(implies (marked-ref tag ref hpg) (marked-ref tag ref ,op)))

(defthm hpg-push-marked-ref-up (marked-ref-up (hpg-push tg rf hpg))
  :hints (("Goal" :in-theory (disable hpg-push omarked vmarked smarked))))
(defthm hpg-scan-obj-marked-ref-up (marked-ref-up (hpg-scan-obj i k hpg))
  :hints (("Goal" :in-theory (disable hpg-scan-obj omarked vmarked smarked))))
(defthm hpg-scan-run-marked-ref-up (marked-ref-up (hpg-scan-run j e hpg))
  :hints (("Goal" :in-theory (disable hpg-scan-run omarked vmarked smarked))))
(defthm hpg-scan-vec-marked-ref-up (marked-ref-up (hpg-scan-vec i hpg))
  :hints (("Goal" :in-theory (disable hpg-scan-vec omarked vmarked smarked))))

; ---- THE STACK BELOW THE TOP STAYS ---------------------------------------------------------

(defun on-stack (tg rf s hpg)
  (if (zp s)
      nil
    (or (and (equal (nth (1- s) (nth *h-mtagi* hpg)) tg) (equal (nth (1- s) (nth *h-mrefi* hpg)) rf))
        (on-stack tg rf (1- s) hpg))))

(defthm on-stack-more
  (implies (and (on-stack tg rf s h) (natp s) (natp s2) (<= s s2)) (on-stack tg rf s2 h))
  :hints (("Goal" :induct (on-stack tg rf s2 h))))

; the entries below s alike in a and b
(defun stack-same (s a b)
  (if (zp s)
      t
    (and (equal (nth (1- s) (nth *h-mtagi* a)) (nth (1- s) (nth *h-mtagi* b)))
         (equal (nth (1- s) (nth *h-mrefi* a)) (nth (1- s) (nth *h-mrefi* b)))
         (stack-same (1- s) a b))))

(defthm on-stack-same
  (implies (and (stack-same s a b) (on-stack tg rf s a)) (on-stack tg rf s b)))

(defthm stack-same-less
  (implies (and (stack-same s2 a b) (natp s) (natp s2) (<= s s2)) (stack-same s a b))
  :hints (("Goal" :induct (stack-same s2 a b))))

(defthm stack-same-trans
  (implies (and (stack-same s a b) (stack-same s b c)) (stack-same s a c)))

(defthm stack-same-refl (stack-same s a a))

(defmacro msp-of (h) `(nth *h-msp* ,h))

(defthm stack-same-spush
  (implies (and (natp (msp-of h)) (natp s) (<= s (msp-of h)))
           (stack-same s h (hpg-spush tg rf h)))
  :hints (("Goal" :induct (stack-same s h h) :in-theory (enable hpg-spush))))

(defthm hpg-spush-msp-up
  (implies (natp (msp-of h)) (and (natp (msp-of (hpg-spush tg rf h))) (<= (msp-of h) (msp-of (hpg-spush tg rf h)))))
  :hints (("Goal" :in-theory (enable hpg-spush)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (natp (msp-of h)) (<= (msp-of h) (msp-of (hpg-spush tg rf h)))))))

; a write to any field but the stack's leaves the stack alike
(defthm stack-same-update-other
  (implies (and (natp i) (not (equal i *h-mtagi*)) (not (equal i *h-mrefi*)))
           (equal (stack-same s a (update-nth i v b)) (stack-same s a b)))
  :hints (("Goal" :induct (stack-same s a b))))

(defthm stack-same-spush2
  (implies (and (stack-same s h x) (natp (msp-of x)) (natp s) (<= s (msp-of x)))
           (stack-same s h (hpg-spush tg rf x)))
  :hints (("Goal" :in-theory (disable stack-same-spush stack-same-trans)
           :use ((:instance stack-same-spush (h x)) (:instance stack-same-trans (a h) (b x) (c (hpg-spush tg rf x)))))))

; the push's mark writes leave the stack: only hpg-spush touches it
(defthm hpg-push-stack
  (implies (and (natp (msp-of h)) (natp s) (<= s (msp-of h)))
           (and (stack-same s h (hpg-push tg rf h))
                (natp (msp-of (hpg-push tg rf h)))
                (<= (msp-of h) (msp-of (hpg-push tg rf h)))))
  :hints (("Goal" :in-theory (enable hpg-push))))

; relative to a fixed original h0, as an induction over pushes carries it
(defthm hpg-push-stack-gen
  (implies (and (stack-same s h0 h) (natp (msp-of h)) (natp s) (<= s (msp-of h)))
           (stack-same s h0 (hpg-push tg rf h)))
  :hints (("Goal" :in-theory (enable hpg-push))))

(defmacro stack-kept (op)
  `(implies (and (stack-same s h0 h) (natp (msp-of h)) (natp s) (<= s (msp-of h)))
            (and (stack-same s h0 ,op) (natp (msp-of ,op)) (<= (msp-of h) (msp-of ,op)))))

(defthm hpg-scan-obj-stack (stack-kept (hpg-scan-obj i k h))
  :hints (("Goal" :in-theory (e/d (hpg-scan-obj) (hpg-push-stack)) :induct (hpg-scan-obj i k h))
          ("Subgoal *1/2" :use ((:instance hpg-push-stack (tg (nth (+ k (* 5 i)) (nth *h-otagi* h)))
                                           (rf (nth (+ k (* 5 i)) (nth *h-orefi* h))) (s (msp-of h)))))))

(defthm hpg-scan-run-stack (stack-kept (hpg-scan-run j e h))
  :hints (("Goal" :in-theory (e/d (hpg-scan-run) (hpg-push-stack)) :induct (hpg-scan-run j e h))
          ("Subgoal *1/2" :use ((:instance hpg-push-stack (tg (nth j (nth *h-atagi* h)))
                                           (rf (nth j (nth *h-arefi* h))) (s (msp-of h)))))))

(defthm hpg-scan-vec-stack (stack-kept (hpg-scan-vec i h))
  :hints (("Goal" :in-theory (enable hpg-scan-vec))))

; ---- BLACK: EVERY REFERENCE HELD MARKED ------------------------------------------------------

; object i's slots k .. 4 marked, as hpg-scan-obj reads them
(defun slots-marked (i k hpg)
  (declare (xargs :measure (nfix (- 5 (nfix k)))))
  (if (or (not (natp k)) (<= 5 k))
      t
    (let ((j (+ (* 5 i) k)))
      (if (and (< j (len (nth *h-otagi* hpg))) (< j (len (nth *h-orefi* hpg))))
          (and (marked-ref (nth j (nth *h-otagi* hpg)) (nth j (nth *h-orefi* hpg)) hpg)
               (slots-marked i (+ 1 k) hpg))
        t))))

; the arena's words j .. e-1 marked, as hpg-scan-run reads them
(defun run-marked (j e hpg)
  (declare (xargs :measure (nfix (- (nfix e) (nfix j)))))
  (if (or (not (natp j)) (not (natp e)) (<= e j))
      t
    (if (and (< j (len (nth *h-atagi* hpg))) (< j (len (nth *h-arefi* hpg))))
        (and (marked-ref (nth j (nth *h-atagi* hpg)) (nth j (nth *h-arefi* hpg)) hpg)
             (run-marked (+ 1 j) e hpg))
      t)))

(defun black-vec (i hpg)
  (if (and (< i (len (nth *h-voffi* hpg))) (< i (len (nth *h-vleni* hpg))))
      (let ((off (nfix (nth i (nth *h-voffi* hpg)))) (n (nfix (nth i (nth *h-vleni* hpg)))))
        (if (and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*))
            (run-marked off (+ off n) hpg)
          t))
    t))

(defun black-obj (i hpg) (slots-marked i 0 hpg))

(in-theory (disable marked-ref omarked vmarked smarked))

; black stays black: every operation only marks more and writes no pool
(defmacro black-up (nm op)
  (let ((n1 (intern-in-package-of-symbol (concatenate 'string (symbol-name nm) "-SLOTS-UP") 'hpg))
        (n2 (intern-in-package-of-symbol (concatenate 'string (symbol-name nm) "-RUN-UP") 'hpg))
        (n3 (intern-in-package-of-symbol (concatenate 'string (symbol-name nm) "-VEC-UP") 'hpg)))
    `(progn
       (defthm ,n1 (implies (slots-marked i k hpg) (slots-marked i k ,op))
         :hints (("Goal" :induct (slots-marked i k hpg))))
       (defthm ,n2 (implies (run-marked j e hpg) (run-marked j e ,op))
         :hints (("Goal" :induct (run-marked j e hpg))))
       (defthm ,n3 (implies (black-vec i hpg) (black-vec i ,op))
         :hints (("Goal" :in-theory (disable run-marked)))))))

(black-up hpg-push (hpg-push tg rf hpg))
(black-up hpg-scan-obj (hpg-scan-obj i2 k2 hpg))
(black-up hpg-scan-run (hpg-scan-run j2 e2 hpg))
(black-up hpg-scan-vec (hpg-scan-vec i2 hpg))

; ---- A SCAN THAT DID NOT OVERFLOW LEAVES ITS OBJECT BLACK ------------------------------------

(defthm hpg-scan-obj-blackens
  (implies (equal (nth *h-err* (hpg-scan-obj i k h)) 0)
           (slots-marked i k (hpg-scan-obj i k h)))
  :hints (("Goal" :in-theory (enable hpg-scan-obj) :induct (hpg-scan-obj i k h))))

(defthm hpg-scan-run-blackens
  (implies (equal (nth *h-err* (hpg-scan-run j e h)) 0)
           (run-marked j e (hpg-scan-run j e h)))
  :hints (("Goal" :in-theory (enable hpg-scan-run) :induct (hpg-scan-run j e h))))

(defthm hpg-scan-vec-blackens
  (implies (equal (nth *h-err* (hpg-scan-vec i h)) 0)
           (black-vec i (hpg-scan-vec i h)))
  :hints (("Goal" :in-theory (enable hpg-scan-vec))))

; ---- THE INVARIANT, ONE REFERENCE AT A TIME --------------------------------------------------

(defun perr (h) (not (equal (nth *h-err* h) 0)))

(defun pobj (r h) (implies (omarked r h) (or (on-stack 8 r (msp-of h) h) (black-obj r h))))
(defun pvec (r h)
  (implies (and (vmarked r h) (< r (len (nth *h-vleni* h)))) (or (on-stack 9 r (msp-of h) h) (black-vec r h))))

(defthm hpg-push-black-obj-up (implies (black-obj i hpg) (black-obj i (hpg-push tg rf hpg))))
(defthm hpg-scan-obj-black-obj-up (implies (black-obj i hpg) (black-obj i (hpg-scan-obj i2 k2 hpg))))
(defthm hpg-scan-vec-black-obj-up (implies (black-obj i hpg) (black-obj i (hpg-scan-vec i2 hpg))))
(in-theory (disable black-obj black-vec))

; a push that marks something new pushes it
(defthm hpg-push-new-obj
  (implies (and (natp (msp-of h)) (not (omarked r h)) (omarked r (hpg-push tg rf h)) (not (perr (hpg-push tg rf h))))
           (on-stack 8 r (msp-of (hpg-push tg rf h)) (hpg-push tg rf h)))
  :hints (("Goal" :in-theory (enable hpg-push hpg-spush omarked nth update-nth))))

(defthm hpg-push-new-vec
  (implies (and (natp (msp-of h)) (not (vmarked r h)) (vmarked r (hpg-push tg rf h)) (not (perr (hpg-push tg rf h))))
           (on-stack 9 r (msp-of (hpg-push tg rf h)) (hpg-push tg rf h)))
  :hints (("Goal" :in-theory (enable hpg-push hpg-spush vmarked nth update-nth))))

; what was on the stack stays on it
(defthm on-stack-kept
  (implies (and (on-stack tg rf (msp-of h) h) (natp (msp-of h))
                (stack-same (msp-of h) h h2) (natp (msp-of h2)) (<= (msp-of h) (msp-of h2)))
           (on-stack tg rf (msp-of h2) h2))
  :hints (("Goal" :in-theory (disable on-stack-more on-stack-same)
           :use ((:instance on-stack-same (s (msp-of h)) (a h) (b h2))
                 (:instance on-stack-more (s (msp-of h)) (s2 (msp-of h2)) (h h2))))))

(defthm hpg-push-p
  (implies (natp (msp-of h))
           (and (implies (pobj r h) (or (perr (hpg-push tg rf h)) (pobj r (hpg-push tg rf h))))
                (implies (pvec r h) (or (perr (hpg-push tg rf h)) (pvec r (hpg-push tg rf h))))))
  :hints (("Goal" :in-theory (disable hpg-push perr)
           :use ((:instance hpg-push-stack (s (msp-of h)))
                 (:instance on-stack-kept (tg 8) (rf r) (h2 (hpg-push tg rf h)))
                 (:instance on-stack-kept (tg 9) (rf r) (h2 (hpg-push tg rf h)))))))

(defthm hpg-push-msp-natp
  (implies (natp (msp-of h)) (natp (msp-of (hpg-push tg rf h))))
  :hints (("Goal" :use ((:instance hpg-push-stack (s 0))))))

(defthm perr-up
  (implies (perr h)
           (and (perr (hpg-push tg rf h)) (perr (hpg-scan-obj i k h)) (perr (hpg-scan-run j e h))
                (perr (hpg-scan-vec i h)))))

(defmacro p-kept (op)
  `(implies (natp (msp-of h))
            (and (implies (pobj r h) (or (perr ,op) (pobj r ,op)))
                 (implies (pvec r h) (or (perr ,op) (pvec r ,op))))))

(defthm hpg-scan-obj-p (p-kept (hpg-scan-obj i k h))
  :hints (("Goal" :in-theory (e/d (hpg-scan-obj) (pobj pvec perr hpg-push hpg-push-p perr-up)) :induct (hpg-scan-obj i k h))
          ("Subgoal *1/2"
           :use ((:instance hpg-push-p (tg (nth (+ k (* 5 i)) (nth *h-otagi* h))) (rf (nth (+ k (* 5 i)) (nth *h-orefi* h))))
                 (:instance perr-up (h (hpg-push (nth (+ k (* 5 i)) (nth *h-otagi* h)) (nth (+ k (* 5 i)) (nth *h-orefi* h)) h))
                            (i i) (k (+ 1 k)))))))

(defthm hpg-scan-run-p (p-kept (hpg-scan-run j e h))
  :hints (("Goal" :in-theory (e/d (hpg-scan-run) (pobj pvec perr hpg-push hpg-push-p perr-up)) :induct (hpg-scan-run j e h))
          ("Subgoal *1/2"
           :use ((:instance hpg-push-p (tg (nth j (nth *h-atagi* h))) (rf (nth j (nth *h-arefi* h))))
                 (:instance perr-up (h (hpg-push (nth j (nth *h-atagi* h)) (nth j (nth *h-arefi* h)) h))
                            (j (+ 1 j)) (e e))))))

(defthm hpg-scan-vec-p (p-kept (hpg-scan-vec i h))
  :hints (("Goal" :in-theory (e/d (hpg-scan-vec) (pobj pvec perr hpg-scan-run hpg-scan-run-p))
           :use ((:instance hpg-scan-run-p (j (nfix (nth i (nth *h-voffi* h))))
                            (e (+ (nfix (nth i (nth *h-voffi* h))) (nfix (nth i (nth *h-vleni* h))))))))))

; what a mark says of its reference, and the pools' bound, with both closed
(defthm omarked-facts
  (implies (omarked r h) (and (natp r) (< 0 r) (< r (len (nth *h-omarki* h)))))
  :hints (("Goal" :in-theory (enable omarked)))
  :rule-classes :forward-chaining)

(defthm vmarked-facts
  (implies (vmarked r h) (and (natp r) (< 0 r) (< r (len (nth *h-vmarki* h)))))
  :hints (("Goal" :in-theory (enable vmarked)))
  :rule-classes :forward-chaining)

(defthm hpg-ok-pools
  (implies (hpg-ok h) (and (<= (len (nth *h-omarki* h)) *hb40*) (<= (len (nth *h-vmarki* h)) *hb40*)))
  :hints (("Goal" :in-theory (enable hpg-ok)))
  :rule-classes :forward-chaining)

; ---- THE DRAIN -------------------------------------------------------------------------------

; one turn of hpg-drain: the top popped and scanned
(defun hpg-step (hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (let* ((sp (- (h-msp hpg) 1))
         (tag (h-mtagi sp hpg))
         (ref (h-mrefi sp hpg))
         (hpg (update-h-msp sp hpg)))
    (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) (hpg-scan-obj ref 0 hpg))
          ((and (equal tag 9) (< 0 ref)) (hpg-scan-vec ref hpg))
          (t hpg))))

(defthm hpg-drain-is-steps
  (equal (hpg-drain fuel hpg)
         (if (or (zp fuel) (zp (h-msp hpg)) (not (equal (h-err hpg) 0)))
             hpg
           (hpg-drain (- fuel 1) (hpg-step hpg))))
  :hints (("Goal" :in-theory (enable hpg-drain)))
  :rule-classes ((:definition :controller-alist ((hpg-drain t nil)))))

(in-theory (disable hpg-drain))

(defthm slots-marked-pop (equal (slots-marked i k (update-nth *h-msp* v h)) (slots-marked i k h))
  :hints (("Goal" :induct (slots-marked i k h) :in-theory (enable marked-ref omarked vmarked smarked))))
(defthm run-marked-pop (equal (run-marked j e (update-nth *h-msp* v h)) (run-marked j e h))
  :hints (("Goal" :induct (run-marked j e h) :in-theory (enable marked-ref omarked vmarked smarked))))

; the pop changes the stack's top alone
(defthm pop-keeps-marks
  (and (equal (omarked r (update-nth *h-msp* v h)) (omarked r h))
       (equal (vmarked r (update-nth *h-msp* v h)) (vmarked r h))
       (equal (black-obj r (update-nth *h-msp* v h)) (black-obj r h))
       (equal (black-vec r (update-nth *h-msp* v h)) (black-vec r h))
       (equal (on-stack tg rf s (update-nth *h-msp* v h)) (on-stack tg rf s h))
       (equal (perr (update-nth *h-msp* v h)) (perr h)))
  :hints (("Goal" :in-theory (enable omarked vmarked black-obj black-vec))))


(defmacro pop1 (h) `(update-nth *h-msp* (+ -1 (nth *h-msp* ,h)) ,h))
(defmacro top-tag (h) `(nth (+ -1 (nth *h-msp* ,h)) (nth *h-mtagi* ,h)))
(defmacro top-ref (h) `(nth (+ -1 (nth *h-msp* ,h)) (nth *h-mrefi* ,h)))

; the pop keeps every reference's case but the top's own
(defthm pop-pobj
  (implies (and (pobj r h) (natp (msp-of h)) (< 0 (msp-of h))
                (not (and (equal (top-tag h) 8) (equal (top-ref h) r))))
           (pobj r (pop1 h)))
  :hints (("Goal" :expand ((on-stack 8 r (nth *h-msp* h) h)))))

(defthm pop-pvec
  (implies (and (pvec r h) (natp (msp-of h)) (< 0 (msp-of h))
                (not (and (equal (top-tag h) 9) (equal (top-ref h) r))))
           (pvec r (pop1 h)))
  :hints (("Goal" :expand ((on-stack 9 r (nth *h-msp* h) h)))))

(in-theory (disable pobj pvec perr))

; THE TOP AN OBJECT: scanned, so black; everything else as the pop left it
(defthm step-obj-p
  (implies (and (natp (msp-of h)) (< 0 (msp-of h)) (equal (top-tag h) 8))
           (and (implies (pobj r h) (or (perr (hpg-scan-obj (top-ref h) 0 (pop1 h))) (pobj r (hpg-scan-obj (top-ref h) 0 (pop1 h)))))
                (implies (pvec r h) (or (perr (hpg-scan-obj (top-ref h) 0 (pop1 h))) (pvec r (hpg-scan-obj (top-ref h) 0 (pop1 h)))))))
  :hints (("Goal" :in-theory (e/d (pobj perr black-obj) (hpg-scan-obj-p hpg-scan-obj-blackens))
           :cases ((equal r (top-ref h)))
           :use ((:instance hpg-scan-obj-p (i (top-ref h)) (k 0) (h (pop1 h)))
                 (:instance hpg-scan-obj-blackens (i (top-ref h)) (k 0) (h (pop1 h)))))))

(defthm step-vec-p
  (implies (and (natp (msp-of h)) (< 0 (msp-of h)) (equal (top-tag h) 9))
           (and (implies (pobj r h) (or (perr (hpg-scan-vec (top-ref h) (pop1 h))) (pobj r (hpg-scan-vec (top-ref h) (pop1 h)))))
                (implies (pvec r h) (or (perr (hpg-scan-vec (top-ref h) (pop1 h))) (pvec r (hpg-scan-vec (top-ref h) (pop1 h)))))))
  :hints (("Goal" :in-theory (e/d (pvec perr) (hpg-scan-vec-p hpg-scan-vec-blackens))
           :cases ((equal r (top-ref h)))
           :use ((:instance hpg-scan-vec-p (i (top-ref h)) (h (pop1 h)))
                 (:instance hpg-scan-vec-blackens (i (top-ref h)) (h (pop1 h)))))))

; THE TOP NOTHING TO SCAN: a marked reference is positive and under the
; pools' bound, so the top was no marked reference's
(defthm step-none-p
  (implies (and (hpg-ok h) (natp (msp-of h)) (< 0 (msp-of h))
                (not (and (equal (top-tag h) 8) (< 0 (top-ref h)) (< (top-ref h) *hb40*)))
                (not (and (equal (top-tag h) 9) (< 0 (top-ref h)))))
           (and (implies (pobj r h) (pobj r (pop1 h)))
                (implies (pvec r h) (pvec r (pop1 h)))))
  :hints (("Goal" :in-theory (enable pobj pvec)
           :expand ((on-stack 8 r (nth *h-msp* h) h) (on-stack 9 r (nth *h-msp* h) h)))))

(defthm hpg-step-p
  (implies (and (hpg-ok h) (< 0 (msp-of h)))
           (and (implies (pobj r h) (or (perr (hpg-step h)) (pobj r (hpg-step h))))
                (implies (pvec r h) (or (perr (hpg-step h)) (pvec r (hpg-step h))))))
  :hints (("Goal" :in-theory (e/d (hpg-step) (step-obj-p step-vec-p step-none-p))
           :use (step-obj-p step-vec-p step-none-p (:instance hpg-ok-stack (hpg h))))))

; ---- THE INVARIANT OVER EVERY REFERENCE, AND THE THEOREM -------------------------------------

(defun-sk hpg-inv-all (h) (forall r (and (pobj r h) (pvec r h))))

(defun hpg-inv (h) (or (perr h) (hpg-inv-all h)))

(defthm hpg-step-ok
  (implies (and (hpgp h) (hpg-ok h) (< 0 (msp-of h)))
           (and (hpgp (hpg-step h)) (hpg-ok (hpg-step h))))
  :hints (("Goal" :in-theory (enable hpg-step) :use ((:instance hpg-ok-stack (hpg h))))))

(defthm hpg-step-perr-up
  (implies (perr h) (perr (hpg-step h)))
  :hints (("Goal" :in-theory (enable hpg-step perr))))

(defthm hpg-step-inv
  (implies (and (hpg-ok h) (< 0 (msp-of h)) (hpg-inv h))
           (hpg-inv (hpg-step h)))
  :hints (("Goal" :in-theory (disable hpg-step hpg-step-p hpg-inv-all-necc)
           :expand ((hpg-inv-all (hpg-step h)))
           :use ((:instance hpg-step-p (r (hpg-inv-all-witness (hpg-step h))))
                 (:instance hpg-inv-all-necc (r (hpg-inv-all-witness (hpg-step h))))))))

(defun drain-ind (fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (zp (h-msp hpg)) (not (equal (h-err hpg) 0)))
      hpg
    (let ((hpg (hpg-step hpg))) (drain-ind (- fuel 1) hpg))))

(defthm hpg-drain-inv
  (implies (and (hpgp h) (hpg-ok h) (hpg-inv h))
           (hpg-inv (hpg-drain fuel h)))
  :hints (("Goal" :induct (drain-ind fuel h) :in-theory (e/d (perr) (hpg-inv hpg-step)))
          ("Subgoal *1/2" :use ((:instance hpg-step-inv) (:instance hpg-step-ok)))))

; THE THEOREM: from a state the invariant holds in -- all marks clear and
; the roots just pushed, as a full collection starts -- a drain that ends
; with its stack empty and no overflow leaves every marked object's slots
; and every marked run's words marked: the mark set closed under references
(defthm hpg-drain-closed
  (implies (and (hpgp h) (hpg-ok h) (hpg-inv h)
                (equal (msp-of (hpg-drain fuel h)) 0)
                (not (perr (hpg-drain fuel h))))
           (and (implies (omarked r (hpg-drain fuel h)) (black-obj r (hpg-drain fuel h)))
                (implies (and (vmarked r (hpg-drain fuel h)) (< r (len (nth *h-vleni* (hpg-drain fuel h)))))
                         (black-vec r (hpg-drain fuel h)))))
  :hints (("Goal" :in-theory (e/d (pobj pvec) (hpg-drain-inv hpg-drain-is-steps hpg-inv-all-necc))
           :use ((:instance hpg-drain-inv)
                 (:instance hpg-inv-all-necc (h (hpg-drain fuel h)))))))

; and the start: no marks and an empty stack hold the invariant, and so
; does every push of a root from there (hpg-push-p)
(defthm hpg-inv-empty
  (implies (and (equal (msp-of h) 0)
                (not (omarked r h)) (not (vmarked r h)))
           (and (pobj r h) (pvec r h)))
  :hints (("Goal" :in-theory (enable pobj pvec))))

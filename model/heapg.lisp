; clotran's heap under the model (PLAN step 33, stage 1a): THE COLLECTOR'S
; MARKING, at the level the Fortran is generated from (src/f/gen/heap_gen.f90
; by scripts/acl2-fortran -b heapg), guard-verified: every index in bounds,
; every integer inside 64 bits.
;
; The pools are GC.f90's, read through the runtime's accessors:
;   h-otag, h-oref   object i's slot k (0..4) is word 5i+k: its tag, its ref
;   h-omark          object i marked (1) or not (0)
;   h-voff, h-vlen   vector run i: its first word in the arena, its length
;   h-vmark          run i marked
;   h-atag, h-aref   the arena's words
;   h-smark          text i (a string, symbol, keyword, number text) marked
; and the marker's own state: its stack (h-mtag, h-mref, h-msp), the counts
; of what it marked (objects, runs, text marks, arena words live), and an
; error flag for a stack too small.
;
; A value is a pool reference when its ref is positive and its tag is one
; of the pools': 8 an object, 9 a run, 5 6 7 11 12 13 15 a text. Anything
; else holds nothing.
;
; THE MARK IS MADE AT THE PUSH: an object or run is marked when it is first
; pushed, so each is pushed at most once and the stack never needs more
; than the pools hold. A text is a leaf: marked, never pushed, and counted
; at every push as GC.f90's marker counts it (young collection reads that
; count). The set marked is the one GC.f90's mark-at-the-pop computes.
;
; Theorems (this book):
;   hpg-push-keeps, hpg-drain-keeps  the pools' contents are never written:
;                                    marking changes marks and its own state
;   hpg-drain-closed                 a drain that empties the stack leaves
;                                    every marked object's and run's
;                                    references marked
;   hpg-push-marks                   a pushed reference is marked

(in-package "ACL2")

(defconst *hb40* 1099511627776)

(defstobj hpg
  (h-err :type (signed-byte 64) :initially 0)
  (h-otag :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-oref :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-omark :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-voff :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vlen :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vmark :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-atag :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-aref :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-smark :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-mtag :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-mref :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-msp :type (signed-byte 64) :initially 0)
  (h-nobj :type (signed-byte 64) :initially 0)
  (h-nvec :type (signed-byte 64) :initially 0)
  (h-nstr :type (signed-byte 64) :initially 0)
  (h-alive :type (signed-byte 64) :initially 0)
  ;; THE SWEEP (stage 1b): each pool's free flags and free list, the
  ;; arena's words' third field (a free run's link) and its size classes'
  ;; heads, and the two things the runtime does as a slot is freed -- an
  ;; object's finalizer, a text's storage released -- as writes to h-ofin
  ;; and h-srel
  (h-okind :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-ofree :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-onext :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vfree :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-vnext :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-sfree :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-snext :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-aival :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-chead :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-ofin :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-srel :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-ohead :type (signed-byte 64) :initially 0)
  (h-vhead :type (signed-byte 64) :initially 0)
  (h-shead :type (signed-byte 64) :initially 0)
  (h-nswo :type (signed-byte 64) :initially 0)
  (h-nswv :type (signed-byte 64) :initially 0)
  (h-nsws :type (signed-byte 64) :initially 0)
  (h-afree :type (signed-byte 64) :initially 0)
  ;; ALLOCATION (stage 1b): how far each pool is used and how big it is,
  ;; and the calling thread's batch of free slots, 1-based as GC.f90's
  (h-oused :type (signed-byte 64) :initially 0)
  (h-ocap :type (signed-byte 64) :initially 0)
  (h-ob :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nob :type (signed-byte 64) :initially 0)
  (h-vused :type (signed-byte 64) :initially 0)
  (h-vcap :type (signed-byte 64) :initially 0)
  (h-vb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nvb :type (signed-byte 64) :initially 0)
  (h-sused :type (signed-byte 64) :initially 0)
  (h-scap :type (signed-byte 64) :initially 0)
  (h-sb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (h-nsb :type (signed-byte 64) :initially 0))

; ---- BOUNDS ---------------------------------------------------------------------------

(defun hpg-lens (hpg)
  (declare (xargs :stobjs hpg))
  (and (<= (h-otag-length hpg) *hb40*) (<= (h-oref-length hpg) *hb40*) (<= (h-omark-length hpg) *hb40*)
       (<= (h-voff-length hpg) *hb40*) (<= (h-vlen-length hpg) *hb40*) (<= (h-vmark-length hpg) *hb40*)
       (<= (h-atag-length hpg) *hb40*) (<= (h-aref-length hpg) *hb40*) (<= (h-smark-length hpg) *hb40*)
       (<= (h-mtag-length hpg) *hb40*) (<= (h-mtag-length hpg) (h-mref-length hpg))))

; the marker's registers in range: the stack's top inside it, the counts
; natural and under 2^40 (each count saturates there)
(defun hpg-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-lens hpg)
       (natp (h-msp hpg)) (<= (h-msp hpg) (h-mtag-length hpg))
       (natp (h-nobj hpg)) (<= (h-nobj hpg) *hb40*)
       (natp (h-nvec hpg)) (<= (h-nvec hpg) *hb40*)
       (natp (h-nstr hpg)) (<= (h-nstr hpg) *hb40*)
       (natp (h-alive hpg)) (<= (h-alive hpg) *hb40*)))

; a count up by k, saturating at 2^40
(defun hpg-add (n k)
  (declare (xargs :guard (and (natp n) (<= n *hb40*) (natp k) (<= k *hb40*))))
  (let ((s (+ (nfix n) (nfix k)))) (if (< s *hb40*) s *hb40*)))

(defun hpg-text-tag (tag)
  (declare (xargs :guard t))
  (or (equal tag 5) (equal tag 6) (equal tag 7) (equal tag 11) (equal tag 12) (equal tag 13) (equal tag 15)))

(defmacro sb64p (x) `(and (integerp ,x) (<= -9223372036854775808 ,x) (< ,x 9223372036854775808)))

; ---- THE PUSH -------------------------------------------------------------------------

; onto the stack, or the error flag when it is full
(defun hpg-spush (tag ref hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-ok hpg) (integerp tag) (integerp ref)
                                         (<= -9223372036854775808 tag) (< tag 9223372036854775808)
                                         (<= -9223372036854775808 ref) (< ref 9223372036854775808))))
  (let ((sp (h-msp hpg)))
    (if (< sp (h-mtag-length hpg))
        (let* ((hpg (update-h-mtagi sp tag hpg))
               (hpg (update-h-mrefi sp ref hpg)))
          (update-h-msp (+ 1 sp) hpg))
      (update-h-err 1 hpg))))

; a reference met: marked, and an object or a run pushed to be scanned
(defun hpg-push (tag ref hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-ok hpg) (sb64p tag) (sb64p ref))))
  (cond ((not (< 0 ref)) hpg)
        ((equal tag 8)
         (if (and (< ref (h-omark-length hpg)) (equal (h-omarki ref hpg) 0))
             (let* ((hpg (update-h-omarki ref 1 hpg))
                    (hpg (update-h-nobj (hpg-add (h-nobj hpg) 1) hpg)))
               (hpg-spush tag ref hpg))
           hpg))
        ((equal tag 9)
         (if (and (< ref (h-vmark-length hpg)) (< ref (h-vlen-length hpg)) (equal (h-vmarki ref hpg) 0))
             (let* ((hpg (update-h-vmarki ref 1 hpg))
                    (hpg (update-h-nvec (hpg-add (h-nvec hpg) 1) hpg))
                    (n (h-vleni ref hpg))
                    (hpg (update-h-alive (hpg-add (h-alive hpg) (if (and (<= 0 n) (<= n *hb40*)) n 0)) hpg)))
               (hpg-spush tag ref hpg))
           hpg))
        ((hpg-text-tag tag)
         (if (< ref (h-smark-length hpg))
             (let ((hpg (update-h-smarki ref 1 hpg)))
               (update-h-nstr (hpg-add (h-nstr hpg) 1) hpg))
           hpg))
        (t hpg)))

; ---- THE SCAN -------------------------------------------------------------------------

; object i's slots k .. 4
(defun hpg-scan-obj (i k hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- 5 (nfix k)))
                  :guard (and (hpg-ok hpg) (natp i) (< i *hb40*) (natp k) (<= k 5))))
  (if (or (not (natp k)) (<= 5 k))
      hpg
    (let ((j (+ (* 5 i) k)))
      (if (and (< j (h-otag-length hpg)) (< j (h-oref-length hpg)))
          (let ((hpg (hpg-push (h-otagi j hpg) (h-orefi j hpg) hpg)))
            (hpg-scan-obj i (+ 1 k) hpg))
        hpg))))

; run i's words from j to e
(defun hpg-scan-run (j e hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (nfix e) (nfix j)))
                  :guard (and (hpg-ok hpg) (natp j) (natp e) (<= e *hb40*))))
  (if (or (not (natp j)) (not (natp e)) (<= e j))
      hpg
    (if (and (< j (h-atag-length hpg)) (< j (h-aref-length hpg)))
        (let ((hpg (hpg-push (h-atagi j hpg) (h-arefi j hpg) hpg)))
          (hpg-scan-run (+ 1 j) e hpg))
      hpg)))

(defun hpg-scan-vec (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :guard (and (hpg-ok hpg) (natp i))))
  (if (and (< i (h-voff-length hpg)) (< i (h-vlen-length hpg)))
      (let ((off (nfix (h-voffi i hpg))) (n (nfix (h-vleni i hpg))))
        (if (and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*))
            (hpg-scan-run off (+ off n) hpg)
          hpg))
    hpg))

; ---- THE DRAIN ------------------------------------------------------------------------

; the stack popped and its entries scanned, at most fuel of them
(defun hpg-drain (fuel hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix fuel) :guard (and (hpg-ok hpg) (natp fuel))))
  (if (or (zp fuel) (zp (h-msp hpg)) (not (equal (h-err hpg) 0)))
      hpg
    (let* ((sp (- (h-msp hpg) 1))
           (tag (h-mtagi sp hpg))
           (ref (h-mrefi sp hpg))
           (hpg (update-h-msp sp hpg))
           (hpg (cond ((and (equal tag 8) (< 0 ref) (< ref *hb40*)) (hpg-scan-obj ref 0 hpg))
                      ((and (equal tag 9) (< 0 ref)) (hpg-scan-vec ref hpg))
                      (t hpg))))
      (hpg-drain (- fuel 1) hpg))))

; ---- GUARDS: THE REGISTERS STAY IN RANGE ------------------------------------------------

(defmacro hsb64-elems (p)
  `(defthm ,(intern-in-package-of-symbol (concatenate (quote string) (symbol-name p) "-NTH") p)
     (implies (and (,p l) (< (nfix i) (len l)))
              (and (integerp (nth i l)) (rationalp (nth i l)) (acl2-numberp (nth i l))
                   (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808)))
     :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (,p l) (< (nfix i) (len l))) (integerp (nth i l))))
                    (:linear :corollary (implies (and (,p l) (< (nfix i) (len l)))
                                                 (and (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808)))))))
(hsb64-elems h-otagp) (hsb64-elems h-orefp) (hsb64-elems h-omarkp) (hsb64-elems h-voffp) (hsb64-elems h-vlenp)
(hsb64-elems h-vmarkp) (hsb64-elems h-atagp) (hsb64-elems h-arefp) (hsb64-elems h-smarkp) (hsb64-elems h-mtagp)
(hsb64-elems h-mrefp)

; an element written in range keeps an array's type
(defmacro hsb64-update (p)
  `(defthm ,(intern-in-package-of-symbol (concatenate (quote string) (symbol-name p) "-UPDATE-NTH") p)
     (implies (and (,p l) (natp i) (< i (len l)) (integerp v) (<= -9223372036854775808 v) (< v 9223372036854775808))
              (,p (update-nth i v l)))
     :hints (("Goal" :in-theory (enable update-nth) :induct (update-nth i v l)))))
(hsb64-update h-otagp) (hsb64-update h-orefp) (hsb64-update h-omarkp) (hsb64-update h-voffp) (hsb64-update h-vlenp)
(hsb64-update h-vmarkp) (hsb64-update h-atagp) (hsb64-update h-arefp) (hsb64-update h-smarkp) (hsb64-update h-mtagp)
(hsb64-update h-mrefp)

(defthm hpg-add-bounds
  (and (natp (hpg-add n k)) (<= (hpg-add n k) *hb40*))
  :rule-classes ((:rewrite) (:linear :corollary (<= (hpg-add n k) *hb40*))
                 (:type-prescription :corollary (natp (hpg-add n k)))))
(in-theory (disable hpg-add))

; the stobj's type gives each array's, with the stobj's own closed
(defthm hpgp-fields
  (implies (hpgp hpg)
           (and (h-otagp (nth *h-otagi* hpg)) (h-orefp (nth *h-orefi* hpg)) (h-omarkp (nth *h-omarki* hpg))
                (h-voffp (nth *h-voffi* hpg)) (h-vlenp (nth *h-vleni* hpg)) (h-vmarkp (nth *h-vmarki* hpg))
                (h-atagp (nth *h-atagi* hpg)) (h-arefp (nth *h-arefi* hpg)) (h-smarkp (nth *h-smarki* hpg))
                (h-mtagp (nth *h-mtagi* hpg)) (h-mrefp (nth *h-mrefi* hpg))))
  :rule-classes :forward-chaining)

; an element of one of the stobj's arrays, read in range, is a 64-bit integer
(defmacro hpg-elem (fld)
  (let ((ix (intern-in-package-of-symbol (concatenate 'string "*H-" (symbol-name fld) "I*") 'hpg))
        (nm (intern-in-package-of-symbol (concatenate 'string "HPG-" (symbol-name fld) "-ELEM") 'hpg)))
    `(defthm ,nm
       (implies (and (hpgp hpg) (< (nfix j) (len (nth ,ix hpg))))
                (and (integerp (nth j (nth ,ix hpg))) (rationalp (nth j (nth ,ix hpg)))
                     (<= -9223372036854775808 (nth j (nth ,ix hpg))) (< (nth j (nth ,ix hpg)) 9223372036854775808)))
       :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (hpgp hpg) (< (nfix j) (len (nth ,ix hpg)))) (integerp (nth j (nth ,ix hpg))))))
       :hints (("Goal" :in-theory (enable hpgp))))))
(hpg-elem otag) (hpg-elem oref) (hpg-elem omark) (hpg-elem voff) (hpg-elem vlen) (hpg-elem vmark) (hpg-elem atag) (hpg-elem aref) (hpg-elem smark) (hpg-elem mtag) (hpg-elem mref)

(defthm hpg-spush-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (sb64p tag) (sb64p ref))
           (and (hpgp (hpg-spush tag ref hpg)) (hpg-ok (hpg-spush tag ref hpg))))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-spush)
(in-theory (disable hpg-spush))

(defthm hpg-push-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (sb64p tag) (sb64p ref))
           (and (hpgp (hpg-push tag ref hpg)) (hpg-ok (hpg-push tag ref hpg))))
  :hints (("Goal" :in-theory (e/d (hpg-spush) (nth update-nth)))))
(verify-guards hpg-push)
(in-theory (disable hpg-push))

; a slot's word pushed, as the scans push them
(defthm hpg-push-slot-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp j) (< j (len (nth *h-otagi* hpg))) (< j (len (nth *h-orefi* hpg))))
           (and (hpgp (hpg-push (nth j (nth *h-otagi* hpg)) (nth j (nth *h-orefi* hpg)) hpg))
                (hpg-ok (hpg-push (nth j (nth *h-otagi* hpg)) (nth j (nth *h-orefi* hpg)) hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok hpg-push-ok)
           :use ((:instance hpg-push-ok (tag (nth j (nth *h-otagi* hpg))) (ref (nth j (nth *h-orefi* hpg))))))))

(defthm hpg-push-word-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp j) (< j (len (nth *h-atagi* hpg))) (< j (len (nth *h-arefi* hpg))))
           (and (hpgp (hpg-push (nth j (nth *h-atagi* hpg)) (nth j (nth *h-arefi* hpg)) hpg))
                (hpg-ok (hpg-push (nth j (nth *h-atagi* hpg)) (nth j (nth *h-arefi* hpg)) hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok hpg-push-ok)
           :use ((:instance hpg-push-ok (tag (nth j (nth *h-atagi* hpg))) (ref (nth j (nth *h-arefi* hpg))))))))

(defthm hpg-scan-obj-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp i)) (and (hpgp (hpg-scan-obj i k hpg)) (hpg-ok (hpg-scan-obj i k hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth))))
(verify-guards hpg-scan-obj :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth))))

(defthm hpg-scan-run-ok
  (implies (and (hpgp hpg) (hpg-ok hpg)) (and (hpgp (hpg-scan-run j e hpg)) (hpg-ok (hpg-scan-run j e hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth))))
(verify-guards hpg-scan-run :hints (("Goal" :in-theory (disable hpg-ok hpgp nth update-nth))))

(defthm hpg-scan-vec-ok
  (implies (and (hpgp hpg) (hpg-ok hpg)) (and (hpgp (hpg-scan-vec i hpg)) (hpg-ok (hpg-scan-vec i hpg))))
  :hints (("Goal" :in-theory (disable hpg-ok hpgp hpg-scan-run nth update-nth))))
(verify-guards hpg-scan-vec :hints (("Goal" :in-theory (disable hpg-ok hpgp hpg-scan-run nth update-nth))))

; the stack's top lowered
(defthm hpg-pop-ok
  (implies (and (hpgp hpg) (hpg-ok hpg) (natp v) (<= v (nth *h-msp* hpg)))
           (and (hpgp (update-nth *h-msp* v hpg)) (hpg-ok (update-nth *h-msp* v hpg)))))

; what the drain reads of hpg-ok with it closed
(defthm hpg-ok-stack
  (implies (hpg-ok hpg)
           (and (natp (nth *h-msp* hpg)) (<= (nth *h-msp* hpg) (len (nth *h-mtagi* hpg)))
                (<= (len (nth *h-mtagi* hpg)) (len (nth *h-mrefi* hpg))) (<= (len (nth *h-mtagi* hpg)) *hb40*)))
  :rule-classes :forward-chaining)

; the entry on top of the stack
(defthm hpg-top-int
  (implies (and (hpgp hpg) (hpg-ok hpg) (< 0 (nth *h-msp* hpg)))
           (and (integerp (nth (+ -1 (nth *h-msp* hpg)) (nth *h-mrefi* hpg)))
                (integerp (nth (+ -1 (nth *h-msp* hpg)) (nth *h-mtagi* hpg)))))
  :hints (("Goal" :in-theory (disable hpgp nth update-nth))))

(defthm hpg-drain-ok
  (implies (and (hpgp hpg) (hpg-ok hpg)) (and (hpgp (hpg-drain fuel hpg)) (hpg-ok (hpg-drain fuel hpg))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok hpg-scan-obj hpg-scan-vec nth update-nth))))
(verify-guards hpg-drain :hints (("Goal" :in-theory (disable hpgp hpg-ok hpg-scan-obj hpg-scan-vec nth update-nth))))

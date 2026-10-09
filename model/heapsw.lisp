; clotran's heap under the model (PLAN step 33, stage 1b): THE SWEEP and the
; frees it and a young collection make, at the level the Fortran is
; generated from (src/f/gen/heap_gen.inc), guard-verified.
;
; Freeing an object: its finalizer (h-ofin, the runtime's: a native array's
; buffer, a regex handle), its kind cleared, on the free list. A run: the
; arena words it held back on their size class's free list -- the first
; word cleared and linked to the class's head through its third field, as
; GC.f90's slab_push does -- its place and length cleared, on the run free
; list. A text: its storage released (h-srel), on the text free list.
;
; The sweep frees every slot below `used` that is neither marked nor free
; already, in index order.
;
; Theorems (heapsw-proof.lisp): the sweep frees exactly the unmarked, and
; leaves every marked object's slots and kind, and every marked run's place
; and length, as they were.

(in-package "ACL2")

(include-book "heapg")

(defmacro sb64ip (x) `(and (integerp ,x) (<= -9223372036854775808 ,x) (< ,x 9223372036854775808)))

; a word read from one array, stored in another: itself, as every array
; holds 64-bit words; the guard proofs see a 64-bit word stored
(defun hpg-s64 (x)
  (declare (xargs :guard t))
  (if (sb64ip x) x 0))
(defthm hpg-s64-bounds
  (and (integerp (hpg-s64 x)) (<= -9223372036854775808 (hpg-s64 x)) (< (hpg-s64 x) 9223372036854775808))
  :rule-classes ((:rewrite) (:type-prescription :corollary (integerp (hpg-s64 x)))
                 (:linear :corollary (and (<= -9223372036854775808 (hpg-s64 x)) (< (hpg-s64 x) 9223372036854775808)))))
(in-theory (disable hpg-s64))

; a run's place or length as a natural under 2^40: itself, for every run
; the allocator made
(defun hpg-n40 (x)
  (declare (xargs :guard t))
  (if (and (natp x) (<= x *hb40*)) x 0))
(defthm hpg-n40-bounds
  (and (natp (hpg-n40 x)) (<= (hpg-n40 x) *hb40*))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (hpg-n40 x)))
                 (:linear :corollary (<= (hpg-n40 x) *hb40*))))
(in-theory (disable hpg-n40))

; the sweep's registers in range
(defun hpg-sw-ok (hpg)
  (declare (xargs :stobjs hpg))
  (and (hpg-ok hpg)
       (<= (h-okind-length hpg) *hb40*) (<= (h-ofree-length hpg) *hb40*) (<= (h-onext-length hpg) *hb40*)
       (<= (h-vfree-length hpg) *hb40*) (<= (h-vnext-length hpg) *hb40*)
       (<= (h-sfree-length hpg) *hb40*) (<= (h-snext-length hpg) *hb40*)
       (<= (h-aival-length hpg) *hb40*) (<= (h-chead-length hpg) *hb40*)
       (<= (h-ofin-length hpg) *hb40*) (<= (h-srel-length hpg) *hb40*)
       (natp (h-nswo hpg)) (<= (h-nswo hpg) *hb40*)
       (natp (h-nswv hpg)) (<= (h-nswv hpg) *hb40*)
       (natp (h-nsws hpg)) (<= (h-nsws hpg) *hb40*)
       (natp (h-afree hpg)) (<= (h-afree hpg) *hb40*)))

; the size class of a run of n words: the least c with 2^(c-1) >= n, from
; c and p = 2^(c-1); GC.f90's size_class from c = 1, p = 1
(defun hpg-size-class (n c p)
  (declare (xargs :measure (nfix (- (+ 1 *hb40*) (nfix p)))
                  :guard (and (natp n) (<= n *hb40*) (natp c) (<= c 64) (natp p) (<= 1 p) (<= p (* 2 *hb40*)))))
  (if (or (not (natp p)) (< p 1) (<= n p) (< *hb40* p) (not (natp c)) (<= 64 c))
      c
    (hpg-size-class n (+ 1 c) (* 2 p))))

; ---- THE FREES --------------------------------------------------------------------------

(defun hpg-free-obj (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-sw-ok hpg) (natp i) (< i (h-okind-length hpg)) (< i (h-ofree-length hpg))
                              (< i (h-onext-length hpg)) (< i (h-ofin-length hpg)))))
  (let* ((hpg (update-h-ofini i 1 hpg))
         (hpg (update-h-okindi i 0 hpg))
         (hpg (update-h-ofreei i 1 hpg))
         (hpg (update-h-onexti i (hpg-s64 (h-ohead hpg)) hpg))
         (hpg (update-h-ohead i hpg)))
    (update-h-nswo (hpg-add (h-nswo hpg) 1) hpg)))

; a run's words back on its size class's free list
(defun hpg-slab-free (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-sw-ok hpg) (natp i) (< i (h-voff-length hpg)) (< i (h-vlen-length hpg)))))
  (let ((len (hpg-n40 (h-vleni i hpg))))
    (if (< 0 len)
        (let ((off (hpg-n40 (h-voffi i hpg))) (c (hpg-size-class len 1 1)))
          (if (and (< off (h-atag-length hpg)) (< off (h-aref-length hpg)) (< off (h-aival-length hpg))
                   (< c (h-chead-length hpg)))
              (let* ((hpg (update-h-atagi off 0 hpg))
                     (hpg (update-h-arefi off 0 hpg))
                     (hpg (update-h-aivali off (hpg-s64 (h-cheadi c hpg)) hpg))
                     (hpg (update-h-cheadi c off hpg))
                     (hpg (update-h-voffi i 0 hpg)))
                (update-h-vleni i 0 hpg))
            hpg))
      hpg)))

(defun hpg-free-vec (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-sw-ok hpg) (natp i) (< i (h-voff-length hpg)) (< i (h-vlen-length hpg))
                              (< i (h-vfree-length hpg)) (< i (h-vnext-length hpg)))))
  (let* ((len (h-vleni i hpg))
         (hpg (update-h-afree (hpg-add (h-afree hpg) (hpg-n40 len)) hpg))
         (hpg (hpg-slab-free i hpg))
         (hpg (update-h-vfreei i 1 hpg))
         (hpg (update-h-vnexti i (hpg-s64 (h-vhead hpg)) hpg))
         (hpg (update-h-vhead i hpg)))
    (update-h-nswv (hpg-add (h-nswv hpg) 1) hpg)))

(defun hpg-free-str (i hpg)
  (declare (xargs :stobjs hpg :verify-guards nil
                  :guard (and (hpg-sw-ok hpg) (natp i) (< i (h-srel-length hpg)) (< i (h-sfree-length hpg))
                              (< i (h-snext-length hpg)))))
  (let* ((hpg (update-h-sreli i 1 hpg))
         (hpg (update-h-sfreei i 1 hpg))
         (hpg (update-h-snexti i (hpg-s64 (h-shead hpg)) hpg))
         (hpg (update-h-shead i hpg)))
    (update-h-nsws (hpg-add (h-nsws hpg) 1) hpg)))

; ---- THE SWEEP --------------------------------------------------------------------------

; objects i .. n: each neither marked nor free, freed
(defun hpg-sweep-objs (i n hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))
                  :guard (and (hpg-sw-ok hpg) (natp i) (natp n) (<= n *hb40*))))
  (if (or (not (natp i)) (not (natp n)) (< n i))
      hpg
    (let ((hpg (if (and (< i (h-omark-length hpg)) (< i (h-ofree-length hpg)) (< i (h-okind-length hpg))
                        (< i (h-onext-length hpg)) (< i (h-ofin-length hpg))
                        (equal (h-omarki i hpg) 0) (equal (h-ofreei i hpg) 0))
                   (hpg-free-obj i hpg)
                 hpg)))
      (hpg-sweep-objs (+ 1 i) n hpg))))

(defun hpg-sweep-vecs (i n hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))
                  :guard (and (hpg-sw-ok hpg) (natp i) (natp n) (<= n *hb40*))))
  (if (or (not (natp i)) (not (natp n)) (< n i))
      hpg
    (let ((hpg (if (and (< i (h-vmark-length hpg)) (< i (h-vfree-length hpg)) (< i (h-voff-length hpg))
                        (< i (h-vlen-length hpg)) (< i (h-vnext-length hpg))
                        (equal (h-vmarki i hpg) 0) (equal (h-vfreei i hpg) 0))
                   (hpg-free-vec i hpg)
                 hpg)))
      (hpg-sweep-vecs (+ 1 i) n hpg))))

(defun hpg-sweep-strs (i n hpg)
  (declare (xargs :stobjs hpg :verify-guards nil :measure (nfix (- (+ 1 (nfix n)) (nfix i)))
                  :guard (and (hpg-sw-ok hpg) (natp i) (natp n) (<= n *hb40*))))
  (if (or (not (natp i)) (not (natp n)) (< n i))
      hpg
    (let ((hpg (if (and (< i (h-smark-length hpg)) (< i (h-sfree-length hpg)) (< i (h-srel-length hpg))
                        (< i (h-snext-length hpg))
                        (equal (h-smarki i hpg) 0) (equal (h-sfreei i hpg) 0))
                   (hpg-free-str i hpg)
                 hpg)))
      (hpg-sweep-strs (+ 1 i) n hpg))))

; ---- GUARDS ------------------------------------------------------------------------------

(hsb64-elems h-okindp) (hsb64-elems h-ofreep) (hsb64-elems h-onextp) (hsb64-elems h-vfreep) (hsb64-elems h-vnextp)
(hsb64-elems h-sfreep) (hsb64-elems h-snextp) (hsb64-elems h-aivalp) (hsb64-elems h-cheadp) (hsb64-elems h-ofinp)
(hsb64-elems h-srelp)
(hsb64-update h-okindp) (hsb64-update h-ofreep) (hsb64-update h-onextp) (hsb64-update h-vfreep) (hsb64-update h-vnextp)
(hsb64-update h-sfreep) (hsb64-update h-snextp) (hsb64-update h-aivalp) (hsb64-update h-cheadp) (hsb64-update h-ofinp)
(hsb64-update h-srelp)
(hpg-elem okind) (hpg-elem ofree) (hpg-elem onext) (hpg-elem vfree) (hpg-elem vnext) (hpg-elem sfree) (hpg-elem snext)
(hpg-elem aival) (hpg-elem chead) (hpg-elem ofin) (hpg-elem srel)

(defthm hpg-size-class-bound
  (implies (and (natp c) (<= c 64)) (and (natp (hpg-size-class n c p)) (<= (hpg-size-class n c p) 64)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (and (natp c) (<= c 64)) (<= (hpg-size-class n c p) 64)))))

(defmacro sw-keeps-ok (call)
  `(implies (and (hpgp hpg) (hpg-sw-ok hpg)) (and (hpgp ,call) (hpg-sw-ok ,call))))

(defthm hpg-free-obj-ok
  (implies (and (natp i) (< i (len (nth *h-okindi* hpg))) (< i (len (nth *h-ofreei* hpg)))
                (< i (len (nth *h-onexti* hpg))) (< i (len (nth *h-ofini* hpg))))
           (sw-keeps-ok (hpg-free-obj i hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-free-obj)

(defthm hpg-slab-free-ok
  (implies (and (natp i) (< i (len (nth *h-voffi* hpg))) (< i (len (nth *h-vleni* hpg))))
           (sw-keeps-ok (hpg-slab-free i hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-slab-free)

(defthm hpg-free-vec-ok
  (implies (and (natp i) (< i (len (nth *h-voffi* hpg))) (< i (len (nth *h-vleni* hpg)))
                (< i (len (nth *h-vfreei* hpg))) (< i (len (nth *h-vnexti* hpg))))
           (sw-keeps-ok (hpg-free-vec i hpg)))
  :hints (("Goal" :in-theory (e/d (hpg-slab-free) (nth update-nth)))))
(verify-guards hpg-free-vec :hints (("Goal" :in-theory (e/d (hpg-slab-free) (nth update-nth)))))

(defthm hpg-free-str-ok
  (implies (and (natp i) (< i (len (nth *h-sreli* hpg))) (< i (len (nth *h-sfreei* hpg))) (< i (len (nth *h-snexti* hpg))))
           (sw-keeps-ok (hpg-free-str i hpg)))
  :hints (("Goal" :in-theory (disable nth update-nth))))
(verify-guards hpg-free-str)

(defthm hpg-sweep-objs-ok (sw-keeps-ok (hpg-sweep-objs i n hpg))
  :hints (("Goal" :in-theory (disable hpg-free-obj hpgp hpg-sw-ok))))
(verify-guards hpg-sweep-objs :hints (("Goal" :in-theory (disable hpg-free-obj hpgp hpg-sw-ok))))
(defthm hpg-sweep-vecs-ok (sw-keeps-ok (hpg-sweep-vecs i n hpg))
  :hints (("Goal" :in-theory (disable hpg-free-vec hpgp hpg-sw-ok))))
(verify-guards hpg-sweep-vecs :hints (("Goal" :in-theory (disable hpg-free-vec hpgp hpg-sw-ok))))
(defthm hpg-sweep-strs-ok (sw-keeps-ok (hpg-sweep-strs i n hpg))
  :hints (("Goal" :in-theory (disable hpg-free-str hpgp hpg-sw-ok))))
(verify-guards hpg-sweep-strs :hints (("Goal" :in-theory (disable hpg-free-str hpgp hpg-sw-ok))))

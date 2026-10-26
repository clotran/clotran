; THE VM'S RUNTIME on clotran's values (src/f/VmRuntime.f90): what each of
; the machine's runtime operations -- rt-truthy, rt-throwp, rt-thrown,
; rt-clop, rt-clo-f, rt-capt, rt-lt, rt-add (model/vmg.lisp) and the
; compiler's rt-consp, rt-car, rt-cdr, rt-nat (model/vmic.lisp) -- answers
; when the value is one of clotran's, on its heap. Written at the level the
; Fortran is GENERATED from (src/f/gen/vmrt_gen.inc, scripts/acl2-fortran
; -b vmrt), guard-verified: every index in bounds, every product of a
; reference under 2^40 first.
;
; A VALUE is GC.f90's: a tag, a ref and an ival. The heap is heapg's hpg
; (an object's slots as words 5o+k, its kind, its first integer field --
; a list's count) and two more arrays, vrx's: each word's ival and each
; object's second integer field (i2, a closure's call table).
;
; THE ANSWER IS A PLACE where it is a value already there, as heapsq's seq
; operations answer: 0 nil, 1 the argument itself, w >= 5 the object word
; w, w < 0 the arena word -w-1. The runtime copies what the place holds;
; nothing here is built, and nothing here writes the heap -- no function in
; this book answers a stobj, so every one leaves the heap, its invariants
; and its roots as they were.
;
; THE DECODING (vrt-dec): a clotran value as the model's value, to a depth
; d -- a closure's captures end with the closure itself, so a value is a
; graph, and two graphs agree when every finite depth of them does. nil is
; nil, true t, false :false, an integer its ival; a list (THROWN v), THROWN
; the runtime's private head, is (:throw . v); a list (CLO f caps) or a
; clotran closure the program compiled (its call table's function id f, its
; captures and then itself) is (:clo f caps); any other list the list of its
; elements; anything else one atom. A keyword is that atom too, so no
; Clojure value -- the keyword :throw, a list (:throw 5), :false -- decodes
; to a throw, a closure or false: the model's tags are keywords, and before
; this decoding nothing kept a program's own data from reading as one of
; them (vrt-dec-not-tag).
;
; Theorems (this book), each for every depth:
;   vrt-truthy-agrees    rt-truthy of the decoded value is vrt-truthy
;   vrt-throwp-agrees    rt-throwp is vrt-throwp: a throw only a THROWN pair
;   vrt-thrown-agrees    rt-thrown is the value vrt-thrown-place names
;   vrt-clop-agrees      rt-clop is vrt-clop
;   vrt-clo-f-agrees     rt-clo-f is vrt-clo-f, -1 where it is no integer
;   vrt-capt-agrees      rt-capt i is the value vrt-capt-place i names
;   vrt-lt-agrees, vrt-add-agrees   on integers, the sum when it fits
;   vrt-add-fits-representable, vrt-add-overflow-unrepresentable   it fits
;                        exactly when a 64-bit word holds the sum; else a throw
;   vrt-nat-agrees, vrt-consp-agrees, vrt-car-agrees, vrt-cdr-agrees
;                        the compiler's reads of a plain list
;   vrt-prim-kind-range, vrt-arg-slot-inside   the dispatch's choice, and
;                        an entry value read only inside the stack
;   (model/vmrt-frame.lisp: vrt-prim-frame-balance, rt_prim's frame leaves the
;                        value stack as it found it, heaprt's frame-balance)
; and their COST, counted in heap reads: vrt-unmeta-reads-bound (3 a META
; wrapper), vrt-walk-reads-bound (4 a list cell walked), vrt-capt-reads-bound
; and vrt-clop-reads-bound: linear in the wrappers and the index, every
; other function a constant.

(in-package "ACL2")

(include-book "heapsq")
(include-book "vmg")
(include-book "vmic")

; ---- THE SECOND HEAP ARRAYS --------------------------------------------------------------

(defstobj vrx
  (x-oival :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (x-oi2 :type (array (signed-byte 64) (0)) :initially 0 :resizable t))

(hsb64-elems x-oivalp) (hsb64-elems x-oi2p)

(defthm vrx-arrays
  (implies (vrxp vrx) (and (x-oivalp (nth *x-oivali* vrx)) (x-oi2p (nth *x-oi2i* vrx))))
  :hints (("Goal" :in-theory (enable vrxp))))
(in-theory (disable vrxp))

; ---- READS -------------------------------------------------------------------------------

(defun vrt-oiv (j vrx)
  (declare (xargs :stobjs vrx :guard (sb64p j)))
  (if (and (integerp j) (<= 0 j) (< j (x-oival-length vrx))) (x-oivali j vrx) 0))

(defun vrt-oi2 (o vrx)
  (declare (xargs :stobjs vrx :guard (sb64p o)))
  (if (and (integerp o) (<= 0 o) (< o (x-oi2-length vrx))) (x-oi2i o vrx) 0))

(defun vrt-voff (v hpg)
  (declare (xargs :stobjs hpg :guard (sb64p v)))
  (if (and (integerp v) (<= 0 v) (< v (h-voff-length hpg))) (h-voffi v hpg) -1))

(defun vrt-vlen (v hpg)
  (declare (xargs :stobjs hpg :guard (sb64p v)))
  (if (and (integerp v) (<= 0 v) (< v (h-vlen-length hpg))) (h-vleni v hpg) 0))

(defun vrt-at (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j)))
  (if (and (integerp j) (<= 0 j) (< j (h-atag-length hpg))) (h-atagi j hpg) -1))

(defun vrt-av (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j)))
  (if (and (integerp j) (<= 0 j) (< j (h-aival-length hpg))) (h-aivali j hpg) 0))

(defthm vrt-x-reads-sb64
  (implies (vrxp vrx) (and (sb64p (vrt-oiv j vrx)) (sb64p (vrt-oi2 j vrx))))
  :hints (("Goal" :in-theory (e/d (vrxp) (nth)))))

(defthm vrt-h-reads-sb64
  (implies (and (hpgp hpg) (integerp j))
           (and (sb64p (vrt-voff j hpg)) (sb64p (vrt-vlen j hpg)) (sb64p (vrt-at j hpg)) (sb64p (vrt-av j hpg))))
  :hints (("Goal" :in-theory (disable nth))))

(defthm vrt-oiv-int (implies (vrxp vrx) (integerp (vrt-oiv j vrx))) :rule-classes :type-prescription)
(defthm vrt-oi2-int (implies (vrxp vrx) (integerp (vrt-oi2 j vrx))) :rule-classes :type-prescription)
(defthm vrt-voff-int (implies (hpgp hpg) (integerp (vrt-voff j hpg))) :rule-classes :type-prescription)
(defthm vrt-vlen-int (implies (hpgp hpg) (integerp (vrt-vlen j hpg))) :rule-classes :type-prescription)
(defthm vrt-at-int (implies (hpgp hpg) (integerp (vrt-at j hpg))) :rule-classes :type-prescription)
(defthm vrt-av-int (implies (hpgp hpg) (integerp (vrt-av j hpg))) :rule-classes :type-prescription)

(in-theory (disable vrt-oiv vrt-oi2 vrt-voff vrt-vlen vrt-at vrt-av))

; ---- IMMEDIATES ---------------------------------------------------------------------------

; Clojure's truthiness: all but nil (tag 0) and false (tag 1, ival 0)
(defun vrt-truthy (tag ival)
  (declare (xargs :guard (and (sb64p tag) (sb64p ival))))
  (not (or (equal tag 0) (and (equal tag 1) (equal ival 0)))))

; a natural below 2^31, else -1 (the compiler's slot and arity numbers)
(defun vrt-nat (tag ival)
  (declare (xargs :guard (and (sb64p tag) (sb64p ival))))
  (if (and (equal tag 2) (<= 0 ival) (< ival 2147483648)) ival -1))

; the model's :lt and :add, on integers, anything else 0
(defun vrt-ifix (tag ival)
  (declare (xargs :guard (and (sb64p tag) (sb64p ival))))
  (if (equal tag 2) ival 0))

(defun vrt-lt (ta ia tb ib)
  (declare (xargs :guard (and (sb64p ta) (sb64p ia) (sb64p tb) (sb64p ib))))
  (< (vrt-ifix ta ia) (vrt-ifix tb ib)))

; a + b inside 64 bits, asked without computing it, and without negating
; anything that can be the least word: -b is UB in Fortran for b = -2^63, so
; b > 0 asks a <= MAX - b (-b in [-MAX, -1]) and b <= 0 asks a >= MIN - b
; written as -MAX - (b + 1) (b + 1 in [MIN + 1, 1], its negation in [-1, MAX])
(defun vrt-add-fits (a b)
  (declare (xargs :guard (and (sb64p a) (sb64p b))))
  (if (< 0 b) (<= a (- 9223372036854775807 b)) (<= (- -9223372036854775807 (+ b 1)) a)))

(defun vrt-add (ta ia tb ib)
  (declare (xargs :guard (and (sb64p ta) (sb64p ia) (sb64p tb) (sb64p ib))))
  (let ((a (vrt-ifix ta ia)) (b (vrt-ifix tb ib)))
    (if (vrt-add-fits a b) (+ a b) 0)))

; ---- LISTS ---------------------------------------------------------------------------------

; a list cell's count (gcl_count): kind 1, its first integer field
(defun vrt-lcount (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (if (and (integerp ref) (hpg-obj-at tag ref hpg) (equal (hpg-okd ref hpg) 1)) (hpg-oi ref hpg) 0))

(defthm vrt-lcount-not-obj (implies (not (equal tag 8)) (equal (vrt-lcount tag ref hpg) 0)))

(defthm vrt-lcount-sb64
  (implies (hpgp hpg) (sb64p (vrt-lcount tag ref hpg))))
(defthm vrt-lcount-int (implies (hpgp hpg) (integerp (vrt-lcount tag ref hpg))) :rule-classes :type-prescription)

; a place is an object word of an object under 2^40, or 0
(defmacro vrt-wordp (w) `(and (natp ,w) (< ,w (* 5 (+ 1 *hb40*)))))

(defun vrt-consp (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (< 0 (vrt-lcount tag ref hpg)))

(defun vrt-len (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (let ((n (vrt-lcount tag ref hpg))) (if (< 0 n) n 0)))

; the car's place, slot 1 (word 5ref); the cdr's, slot 2 while more follow
(defun vrt-car-place (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (if (vrt-consp tag ref hpg) (* 5 ref) 0))

(defun vrt-cdr-place (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (if (< 1 (vrt-lcount tag ref hpg)) (+ 1 (* 5 ref)) 0))

; the same of the value an object word holds; 0 (nil) has neither
(defun vrt-car-at (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (if (<= 5 w) (vrt-car-place (hpg-ot w hpg) (hpg-or w hpg) hpg) 0))

(defun vrt-cdr-at (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (if (<= 5 w) (vrt-cdr-place (hpg-ot w hpg) (hpg-or w hpg) hpg) 0))

(defthm vrt-places-words
  (and (vrt-wordp (vrt-car-place tag ref hpg)) (vrt-wordp (vrt-cdr-place tag ref hpg))
       (vrt-wordp (vrt-car-at w hpg)) (vrt-wordp (vrt-cdr-at w hpg))))
(defthm vrt-places-nat
  (and (natp (vrt-car-place tag ref hpg)) (natp (vrt-cdr-place tag ref hpg))
       (natp (vrt-car-at w hpg)) (natp (vrt-cdr-at w hpg)))
  :rule-classes ((:type-prescription :corollary (natp (vrt-car-place tag ref hpg)))
                 (:type-prescription :corollary (natp (vrt-cdr-place tag ref hpg)))
                 (:type-prescription :corollary (natp (vrt-car-at w hpg)))
                 (:type-prescription :corollary (natp (vrt-cdr-at w hpg)))))
(in-theory (disable vrt-car-place vrt-cdr-place vrt-car-at vrt-cdr-at))

; word w holds the value (htag, href) -- identity, as `same` tests it
(defun vrt-same-at (w htag href hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p w) (sb64p htag) (sb64p href))))
  (and (<= 5 w) (equal (hpg-ot w hpg) htag) (equal (hpg-or w hpg) href)))

; (THROWN v): two elements, the first the thrown head
(defun vrt-throwp (tag ref ttag tref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref) (sb64p ttag) (sb64p tref))))
  (and (equal (vrt-lcount tag ref hpg) 2) (vrt-same-at (vrt-car-place tag ref hpg) ttag tref hpg)))

; (CLO f caps): three, the first the closure head
(defun vrt-clol (tag ref ctag cref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref) (sb64p ctag) (sb64p cref))))
  (and (equal (vrt-lcount tag ref hpg) 3) (vrt-same-at (vrt-car-place tag ref hpg) ctag cref hpg)))

(defun vrt-cadr-place (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (vrt-car-at (vrt-cdr-place tag ref hpg) hpg))

(defun vrt-caddr-place (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (vrt-car-at (vrt-cdr-at (vrt-cdr-place tag ref hpg) hpg) hpg))

; rt_thrown: (cadr a)
(defun vrt-thrown-place (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (vrt-cadr-place tag ref hpg))

; the place of element i of the list word w holds: i cdrs, then the car
(defun vrt-walk (i w hpg)
  (declare (xargs :stobjs hpg :measure (nfix i) :guard (and (natp i) (sb64p i) (sb64p w))))
  (if (zp i) (vrt-car-at w hpg) (vrt-walk (1- i) (vrt-cdr-at w hpg) hpg)))

(defthm vrt-walk-word (vrt-wordp (vrt-walk i w hpg)))
(defthm vrt-walk-nat (natp (vrt-walk i w hpg)) :rule-classes :type-prescription)

; ---- CLOSURES ------------------------------------------------------------------------------

; the object under k META wrappers at most (OBJ_META 8, the value its slot
; 1), 0 when it is no object or the wrappers go deeper
(defun vrt-unmeta-k (tag ref k hpg)
  (declare (xargs :stobjs hpg :measure (nfix k) :guard (and (sb64p tag) (sb64p ref) (natp k) (sb64p k))))
  (cond ((not (and (integerp ref) (hpg-obj-at tag ref hpg))) 0)
        ((zp k) 0)
        ((equal (hpg-okd ref hpg) 8) (vrt-unmeta-k (hpg-ot (* 5 ref) hpg) (hpg-or (* 5 ref) hpg) (1- k) hpg))
        (t ref)))

; the object found, if any, is one hpg-obj-at accepted: under 2^40
(defthm vrt-unmeta-k-range
  (and (natp (vrt-unmeta-k tag ref k hpg)) (< (vrt-unmeta-k tag ref k hpg) *hb40*))
  :rule-classes ((:type-prescription :corollary (natp (vrt-unmeta-k tag ref k hpg)))
                 (:linear :corollary (< (vrt-unmeta-k tag ref k hpg) *hb40*))))

; no chain of wrappers is longer than the objects there are
(defun vrt-nobj (hpg)
  (declare (xargs :stobjs hpg))
  (let ((n (h-okind-length hpg))) (if (< n *hb40*) n *hb40*)))

(defun vrt-unmeta (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (vrt-unmeta-k tag ref (vrt-nobj hpg) hpg))

(defthm vrt-nobj-range (and (natp (vrt-nobj hpg)) (<= (vrt-nobj hpg) *hb40*))
  :rule-classes ((:type-prescription :corollary (natp (vrt-nobj hpg))) (:linear :corollary (<= (vrt-nobj hpg) *hb40*))))

; word w holds an environment (OBJ_ENV 7)
(defun vrt-env-at (w hpg)
  (declare (xargs :stobjs hpg :guard (sb64p w)))
  (and (equal (hpg-ot w hpg) 8) (< 0 (hpg-or w hpg)) (equal (hpg-okd (hpg-or w hpg) hpg) 7)))

; a compiled closure's call table: an OBJ_CLOSURE (4) whose i2 names one
; and whose slot 3 is no environment, else 0
(defun vrt-ctab (r hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :guard (sb64p r)))
  (if (and (integerp r) (< 0 r) (< r *hb40*) (equal (hpg-okd r hpg) 4))
      (let ((i2 (vrt-oi2 r vrx)))
        (if (and (< 0 i2) (not (vrt-env-at (+ 2 (* 5 r)) hpg))) i2 0))
    0))

(defthm vrt-ctab-sb64 (implies (vrxp vrx) (and (natp (vrt-ctab r hpg vrx)) (sb64p (vrt-ctab r hpg vrx))))
  :rule-classes ((:rewrite) (:type-prescription :corollary (implies (vrxp vrx) (natp (vrt-ctab r hpg vrx))))))

; the arena word of register k (1-based) of run ct (gc_reg), -1 outside
(defun vrt-reg (ct k hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ct) (sb64p k))))
  (let ((off (vrt-voff ct hpg)))
    (if (and (integerp ct) (integerp k) (< 0 ct) (< 0 off) (< off *hb40*) (< 0 k) (< k *hb40*)) (+ off (- k 1)) -1)))

(defthm vrt-reg-range
  (implies (hpgp hpg) (and (integerp (vrt-reg ct k hpg)) (<= -1 (vrt-reg ct k hpg)) (< (vrt-reg ct k hpg) (* 2 *hb40*))))
  :rule-classes ((:rewrite) (:linear :corollary (implies (hpgp hpg) (and (<= -1 (vrt-reg ct k hpg)) (< (vrt-reg ct k hpg) (* 2 *hb40*)))))
                 (:type-prescription :corollary (implies (hpgp hpg) (integerp (vrt-reg ct k hpg))))))

(defun vrt-reg-int (ct k hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ct) (sb64p k))))
  (let ((j (vrt-reg ct k hpg))) (if (<= 0 j) (vrt-av j hpg) 0)))

(defun vrt-reg-tag (ct k hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p ct) (sb64p k))))
  (let ((j (vrt-reg ct k hpg))) (if (<= 0 j) (vrt-at j hpg) -1)))

(defthm vrt-reg-reads-sb64
  (implies (hpgp hpg) (and (sb64p (vrt-reg-int ct k hpg)) (sb64p (vrt-reg-tag ct k hpg)))))
(defthm vrt-reg-int-int (implies (hpgp hpg) (integerp (vrt-reg-int ct k hpg))) :rule-classes :type-prescription)
(defthm vrt-reg-tag-int (implies (hpgp hpg) (integerp (vrt-reg-tag ct k hpg))) :rule-classes :type-prescription)

; flat.inc's call table: the captures' count in register 3, K in 4, the
; function id last, at 4 + 4(K+1) + ncap + 1
(defun vrt-tab-ok (ct hpg)
  (declare (xargs :stobjs hpg :guard (sb64p ct)))
  (let ((nc (vrt-reg-int ct 3 hpg)) (kk (vrt-reg-int ct 4 hpg)))
    (and (<= 0 nc) (< nc 2147483648) (<= 0 kk) (< kk 2147483648))))

(defun vrt-fid-of (ct hpg)
  (declare (xargs :stobjs hpg :guard (sb64p ct)))
  ; vrt-tab-ok and the registers it reads, each read once: register k is
  ; arena word off + k - 1
  (let ((off (vrt-voff ct hpg)))
    (if (and (integerp ct) (< 0 ct) (< 0 off) (< off *hb40*))
        (let ((nc (vrt-av (+ off 2) hpg)) (kk (vrt-av (+ off 3) hpg)))
          (if (and (<= 0 nc) (< nc 2147483648) (<= 0 kk) (< kk 2147483648))
              (let ((j (+ off 4 (* 4 (+ 1 kk)) nc)))
                (if (equal (vrt-at j hpg) 2) (vrt-av j hpg) -1))
            -1))
      -1)))

; the same as reading the registers one by one
(defthm vrt-fid-of-regs
  (implies (hpgp hpg)
           (equal (vrt-fid-of ct hpg)
                  (if (vrt-tab-ok ct hpg)
                      (let ((ix (+ 5 (* 4 (+ 1 (vrt-reg-int ct 4 hpg))) (vrt-reg-int ct 3 hpg))))
                        (if (equal (vrt-reg-tag ct ix hpg) 2) (vrt-reg-int ct ix hpg) -1))
                    -1)))
  :rule-classes nil)

(defthm vrt-fid-of-sb64 (implies (hpgp hpg) (sb64p (vrt-fid-of ct hpg))))
(defthm vrt-fid-of-int (implies (hpgp hpg) (integerp (vrt-fid-of ct hpg))) :rule-classes :type-prescription)

; the function id of a clotran closure the program compiled, else -1
(defun vrt-cfid (tag ref hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :guard (and (sb64p tag) (sb64p ref))))
  (let ((ct (vrt-ctab (vrt-unmeta tag ref hpg) hpg vrx)))
    (if (< 0 ct) (let ((f (vrt-fid-of ct hpg))) (if (<= 0 f) f -1)) -1)))

(defthm vrt-cfid-sb64 (implies (hpgp hpg) (and (sb64p (vrt-cfid tag ref hpg vrx)) (<= -1 (vrt-cfid tag ref hpg vrx))))
  :rule-classes ((:rewrite) (:linear :corollary (implies (hpgp hpg) (<= -1 (vrt-cfid tag ref hpg vrx))))))
(defthm vrt-cfid-int (implies (hpgp hpg) (integerp (vrt-cfid tag ref hpg vrx))) :rule-classes :type-prescription)
(defthm vrt-cfid-not-obj (implies (not (equal tag 8)) (equal (vrt-cfid tag ref hpg vrx) -1))
  :hints (("Goal" :expand ((vrt-unmeta-k tag ref (vrt-nobj hpg) hpg)))))

; its captures' count
(defun vrt-cncap (tag ref hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :guard (and (sb64p tag) (sb64p ref))))
  (vrt-reg-int (vrt-ctab (vrt-unmeta tag ref hpg) hpg vrx) 3 hpg))

(defun vrt-clop (tag ref ctag cref hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :guard (and (sb64p tag) (sb64p ref) (sb64p ctag) (sb64p cref))))
  (or (<= 0 (vrt-cfid tag ref hpg vrx)) (vrt-clol tag ref ctag cref hpg)))

; the function: the compiled closure's id, or (cadr c)'s integer, else -1
(defun vrt-clo-f (tag ref hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :guard (and (sb64p tag) (sb64p ref))))
  (let ((f (vrt-cfid tag ref hpg vrx)))
    (if (<= 0 f) f
      (let ((w (vrt-cadr-place tag ref hpg)))
        (if (and (<= 5 w) (equal (hpg-ot w hpg) 2)) (vrt-oiv w vrx) -1)))))

; capture i's place: a compiled closure's in its slots 2 and 4, or past two
; in the vector in slot 2; i = ncap the closure itself; past it nil. Of
; (CLO f caps), element i of caps.
(defun vrt-capt-place (i tag ref hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :guard (and (natp i) (sb64p i) (sb64p tag) (sb64p ref))))
  (if (<= 0 (vrt-cfid tag ref hpg vrx))
      (let ((n (vrt-cncap tag ref hpg vrx)) (r (vrt-unmeta tag ref hpg)))
        (cond ((< n i) 0)
              ((equal i n) 1)
              ((not (and (< 0 r) (< r *hb40*))) 0)
              ((< 2 n)
               (let* ((w (+ 1 (* 5 r))) (v (hpg-or w hpg)) (off (vrt-voff v hpg)))
                 (if (and (equal (hpg-ot w hpg) 9) (< 0 v) (< i (vrt-vlen v hpg)) (< 0 off) (< off *hb40*)
                          (< i *hb40*))
                     (- -1 (+ off i))
                   0)))
              ((equal i 0) (+ 1 (* 5 r)))
              (t (+ 3 (* 5 r)))))
    (vrt-walk i (vrt-caddr-place tag ref hpg) hpg)))

; ---- THE PRIMITIVES' DISPATCH --------------------------------------------------------------

; rt_prim's op: 6 a node of the program's own (OBJ_AST 30), 8 a builtin
; (OBJ_BUILTIN 13), and of the keywords, by identity: 1 arg, 2 arity, 3
; deref, 4 callw, 5 invoke (either name); 7 any other value, called
(defun vrt-prim-kind (tag ref karg kar kder kcw kinv kinvm hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref) (sb64p karg) (sb64p kar) (sb64p kder)
                                          (sb64p kcw) (sb64p kinv) (sb64p kinvm))))
  (cond ((and (equal tag 8) (< 0 ref)) (let ((k (hpg-okd ref hpg))) (cond ((equal k 30) 6) ((equal k 13) 8) (t 7))))
        ((not (equal tag 7)) 7)
        ((equal ref karg) 1)
        ((equal ref kar) 2)
        ((equal ref kder) 3)
        ((equal ref kcw) 4)
        ((or (equal ref kinv) (equal ref kinvm)) 5)
        (t 7)))

; (:prim arg (:const i)): the running body's entry value i, slot rb+i+1 of
; a stack of len slots; 0 when it is none
(defun vrt-arg-slot (n tag ival rb len)
  (declare (xargs :guard (and (sb64p n) (sb64p tag) (sb64p ival) (sb64p rb) (sb64p len))))
  (if (and (equal n 1) (equal tag 2) (<= 0 ival) (<= 0 rb) (< len *hb40*) (< ival len) (< rb len)
           (< (+ rb ival) len))
      (+ rb ival 1)
    0))

; ---- THE DECODING -------------------------------------------------------------------------
;
; hd is the runtime's two private heads, (thrown-tag thrown-ref clo-tag
; clo-ref); x = (tag ref ival) the value decoded, which a place 1 names.
; Not generated: it is what the generated code is proved against.

(defun vrt-ar (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j)))
  (if (and (integerp j) (<= 0 j) (< j (h-aref-length hpg))) (h-arefi j hpg) -1))

(defun vrt-caps-measure (k n d)
  (if (zp d) 0 (make-ord 1 d (+ 2 (nfix (- (+ 1 (nfix n)) (nfix k)))))))

(mutual-recursion
 (defun vrt-dec (tag ref ival d hd hpg vrx)
   (declare (xargs :stobjs (hpg vrx) :verify-guards nil
                   :measure (make-ord 1 (+ 1 (nfix d)) 0) :well-founded-relation o<))
   (cond ((zp d) 'vrt-deep)
         ((equal tag 0) nil)
         ((equal tag 1) (if (equal ival 0) :false t))
         ((equal tag 2) ival)
         ((<= 0 (vrt-cfid tag ref hpg vrx))
          (list :clo (vrt-cfid tag ref hpg vrx)
                (vrt-dec-caps 0 (vrt-cncap tag ref hpg vrx) tag ref ival d hd hpg vrx)))
         ((vrt-consp tag ref hpg)
          (cond ((vrt-throwp tag ref (nth 0 hd) (nth 1 hd) hpg)
                 (cons :throw (vrt-decp (vrt-thrown-place tag ref hpg) tag ref ival (1- d) hd hpg vrx)))
                ((vrt-clol tag ref (nth 2 hd) (nth 3 hd) hpg)
                 (list :clo (vrt-decp (vrt-cadr-place tag ref hpg) tag ref ival (1- d) hd hpg vrx)
                       (vrt-decp (vrt-caddr-place tag ref hpg) tag ref ival (1- d) hd hpg vrx)))
                (t (cons (vrt-decp (vrt-car-place tag ref hpg) tag ref ival (1- d) hd hpg vrx)
                         (vrt-decp (vrt-cdr-place tag ref hpg) tag ref ival (1- d) hd hpg vrx)))))
         (t 'vrt-opaque)))
 ; the value at place p
 (defun vrt-decp (p tag ref ival d hd hpg vrx)
   (declare (xargs :stobjs (hpg vrx) :measure (make-ord 1 (+ 1 (nfix d)) 1)))
   (cond ((equal p 1) (vrt-dec tag ref ival d hd hpg vrx))
         ((and (integerp p) (<= 5 p)) (vrt-dec (hpg-ot p hpg) (hpg-or p hpg) (vrt-oiv p vrx) d hd hpg vrx))
         ((and (integerp p) (< p 0)) (vrt-dec (vrt-at (- -1 p) hpg) (vrt-ar (- -1 p) hpg) (vrt-av (- -1 p) hpg)
                                              d hd hpg vrx))
         (t nil)))
 ; captures k .. n of the compiled closure x, capture k at depth d - 2 - k
 (defun vrt-dec-caps (k n tag ref ival d hd hpg vrx)
   (declare (xargs :stobjs (hpg vrx) :measure (vrt-caps-measure k n d)))
   (cond ((zp d) nil)
         ((< (nfix n) (nfix k)) nil)
         (t (cons (vrt-decp (vrt-capt-place (nfix k) tag ref hpg vrx) tag ref ival (nfix (- d (+ 2 (nfix k)))) hd hpg vrx)
                  (vrt-dec-caps (+ 1 (nfix k)) n tag ref ival d hd hpg vrx))))))

; ---- WHAT A DECODED VALUE CAN BE ------------------------------------------------------------

(defthm vrt-oiv-acl2-numberp (implies (vrxp vrx) (acl2-numberp (vrt-oiv j vrx)))
  :hints (("Goal" :use vrt-x-reads-sb64 :in-theory (disable vrt-x-reads-sb64))))
(defthm vrt-av-acl2-numberp (implies (hpgp hpg) (acl2-numberp (vrt-av j hpg)))
  :hints (("Goal" :use vrt-h-reads-sb64 :in-theory (disable vrt-h-reads-sb64))))

; never a bare tag: no value decodes to :throw, :clo or :false but false
(defthm vrt-dec-not-tag
  (implies (and (acl2-numberp ival) (hpgp hpg) (vrxp vrx))
           (and (not (equal (vrt-dec tag ref ival d hd hpg vrx) :throw))
                (not (equal (vrt-dec tag ref ival d hd hpg vrx) :clo))
                (implies (not (and (equal tag 1) (equal ival 0)))
                         (not (equal (vrt-dec tag ref ival d hd hpg vrx) :false)))))
  :hints (("Goal" :expand ((vrt-dec tag ref ival d hd hpg vrx)))))

(defthm vrt-decp-not-tag
  (implies (and (acl2-numberp ival) (hpgp hpg) (vrxp vrx))
           (and (not (equal (vrt-decp p tag ref ival d hd hpg vrx) :throw))
                (not (equal (vrt-decp p tag ref ival d hd hpg vrx) :clo))))
  :hints (("Goal" :expand ((vrt-decp p tag ref ival d hd hpg vrx)))))

; a compiled closure is no list cell: its object, or the one its wrappers hold, is an OBJ_CLOSURE
(defthm vrt-ctab-unmeta-not-list
  (implies (< 0 (vrt-ctab (vrt-unmeta-k tag ref k hpg) hpg vrx))
           (equal (vrt-lcount tag ref hpg) 0))
  :hints (("Goal" :expand ((vrt-unmeta-k tag ref k hpg)))))

(defthm vrt-cfid-not-list
  (implies (<= 0 (vrt-cfid tag ref hpg vrx)) (equal (vrt-lcount tag ref hpg) 0))
  :hints (("Goal" :in-theory (disable vrt-lcount vrt-ctab-unmeta-not-list)
           :use ((:instance vrt-ctab-unmeta-not-list (k (vrt-nobj hpg)))))))

(defthm vrt-fid-of-tab-ok
  (implies (and (hpgp hpg) (<= 0 (vrt-fid-of ct hpg))) (and (<= 0 (vrt-reg-int ct 3 hpg)) (integerp (vrt-reg-int ct 3 hpg))))
  :hints (("Goal" :in-theory (enable vrt-reg-int vrt-reg))))

(defthm vrt-cfid-cncap
  (implies (and (hpgp hpg) (<= 0 (vrt-cfid tag ref hpg vrx))) (natp (vrt-cncap tag ref hpg vrx)))
  :hints (("Goal" :in-theory (disable vrt-fid-of vrt-reg-int vrt-ctab vrt-unmeta)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (hpgp hpg) (<= 0 (vrt-cfid tag ref hpg vrx))) (natp (vrt-cncap tag ref hpg vrx))))))

; places are nil or object words
(defthm vrt-places-0-or-5
  (and (or (equal (vrt-car-place tag ref hpg) 0) (<= 5 (vrt-car-place tag ref hpg)))
       (or (equal (vrt-cdr-place tag ref hpg) 0) (<= 5 (vrt-cdr-place tag ref hpg)))
       (or (equal (vrt-car-at w hpg) 0) (<= 5 (vrt-car-at w hpg)))
       (or (equal (vrt-cdr-at w hpg) 0) (<= 5 (vrt-cdr-at w hpg))))
  :hints (("Goal" :in-theory (enable vrt-car-place vrt-cdr-place vrt-car-at vrt-cdr-at)))
  :rule-classes nil)

(defthm vrt-cxr-places
  (and (natp (vrt-cadr-place tag ref hpg)) (natp (vrt-caddr-place tag ref hpg)) (natp (vrt-thrown-place tag ref hpg))
       (or (equal (vrt-cadr-place tag ref hpg) 0) (<= 5 (vrt-cadr-place tag ref hpg)))
       (or (equal (vrt-caddr-place tag ref hpg) 0) (<= 5 (vrt-caddr-place tag ref hpg)))
       (or (equal (vrt-thrown-place tag ref hpg) 0) (<= 5 (vrt-thrown-place tag ref hpg))))
  :hints (("Goal" :use ((:instance vrt-places-0-or-5 (w (vrt-cdr-place tag ref hpg)))
                        (:instance vrt-places-0-or-5 (w (vrt-cdr-at (vrt-cdr-place tag ref hpg) hpg))))))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (vrt-cadr-place tag ref hpg)))
                 (:type-prescription :corollary (natp (vrt-caddr-place tag ref hpg)))
                 (:type-prescription :corollary (natp (vrt-thrown-place tag ref hpg)))))
(in-theory (disable vrt-cadr-place vrt-caddr-place vrt-thrown-place))

(defthm vrt-walk-0-or-5
  (or (equal (vrt-walk i w hpg) 0) (<= 5 (vrt-walk i w hpg)))
  :hints (("Goal" :in-theory (enable vrt-walk) :induct (vrt-walk i w hpg))
          ("Subgoal *1/1" :use ((:instance vrt-places-0-or-5 (tag 0) (ref 0)))))
  :rule-classes nil)

; ---- THE MACHINE'S OPERATIONS AGREE --------------------------------------------------------
;
; Each for every depth d: the model's operation on the decoded value is the
; generated one's answer, decoded.

(defmacro vrt-hyps () '(and (hpgp hpg) (vrxp vrx) (integerp ival) (natp d)))

(defthm vrt-truthy-agrees
  (implies (vrt-hyps)
           (equal (rt-truthy (vrt-dec tag ref ival (+ 1 d) hd hpg vrx)) (vrt-truthy tag ival)))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 1 d) hd hpg vrx)))))

(defthm vrt-throwp-agrees
  (implies (vrt-hyps)
           (iff (rt-throwp (vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
                (vrt-throwp tag ref (nth 0 hd) (nth 1 hd) hpg)))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-lcount))))

(defthm vrt-thrown-agrees
  (implies (and (vrt-hyps) (vrt-throwp tag ref (nth 0 hd) (nth 1 hd) hpg))
           (equal (rt-thrown (vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
                  (vrt-decp (vrt-thrown-place tag ref hpg) tag ref ival d hd hpg vrx)))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-lcount vrt-thrown-place))))

(defthm vrt-clop-agrees
  (implies (vrt-hyps)
           (iff (rt-clop (vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
                (vrt-clop tag ref (nth 2 hd) (nth 3 hd) hpg vrx)))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-lcount))))

; a place's value decodes to an integer exactly when its word holds one
(defthm vrt-decp-integerp
  (implies (and (hpgp hpg) (vrxp vrx) (posp d) (or (equal w 0) (<= 5 w)) (integerp w))
           (iff (integerp (vrt-decp w tag ref ival d hd hpg vrx))
                (and (<= 5 w) (equal (hpg-ot w hpg) 2))))
  :hints (("Goal" :expand ((vrt-decp w tag ref ival d hd hpg vrx)
                           (vrt-dec (hpg-ot w hpg) (hpg-or w hpg) (vrt-oiv w vrx) d hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-lcount))))

(defthm vrt-decp-int-value
  (implies (and (hpgp hpg) (vrxp vrx) (posp d) (integerp w) (<= 5 w) (equal (hpg-ot w hpg) 2))
           (equal (vrt-decp w tag ref ival d hd hpg vrx) (vrt-oiv w vrx)))
  :hints (("Goal" :expand ((vrt-decp w tag ref ival d hd hpg vrx)
                           (vrt-dec (hpg-ot w hpg) (hpg-or w hpg) (vrt-oiv w vrx) d hd hpg vrx)))))

(defthm vrt-clo-f-agrees
  (implies (and (vrt-hyps) (vrt-clop tag ref (nth 2 hd) (nth 3 hd) hpg vrx))
           (equal (vrt-clo-f tag ref hpg vrx)
                  (let ((f (rt-clo-f (vrt-dec tag ref ival (+ 2 d) hd hpg vrx)))) (if (integerp f) f -1))))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 2 d) hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-lcount vrt-cadr-place vrt-caddr-place)
           :use ((:instance vrt-decp-integerp (w (vrt-cadr-place tag ref hpg)) (d (+ 1 d)))
                 (:instance vrt-decp-int-value (w (vrt-cadr-place tag ref hpg)) (d (+ 1 d)))))))

; ---- CAPTURES -------------------------------------------------------------------------------

(defun vrt-caps-ind (k i n)
  (declare (xargs :measure (nfix i)))
  (if (or (zp i) (< (nfix n) (nfix k))) (list k i n) (vrt-caps-ind (+ 1 (nfix k)) (1- i) n)))

; element i of a compiled closure's captures, k on
(defthm vrt-nth-dec-caps
  (implies (and (natp k) (natp i) (posp dd) (natp n))
           (equal (nth i (vrt-dec-caps k n tag ref ival dd hd hpg vrx))
                  (if (<= (+ k i) (nfix n))
                      (vrt-decp (vrt-capt-place (+ k i) tag ref hpg vrx) tag ref ival (nfix (- dd (+ 2 k i))) hd hpg vrx)
                    nil)))
  :hints (("Goal" :induct (vrt-caps-ind k i n)
           :expand ((vrt-dec-caps k n tag ref ival dd hd hpg vrx))
           :in-theory (disable vrt-capt-place vrt-decp))))

; the walk sees only plain lists: no compiled closure, no marker list
(defun vrt-plain-at (w hd hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :verify-guards nil))
  (let ((tg (hpg-ot w hpg)) (rf (hpg-or w hpg)))
    (and (< (vrt-cfid tg rf hpg vrx) 0)
         (not (vrt-throwp tg rf (nth 0 hd) (nth 1 hd) hpg))
         (not (vrt-clol tg rf (nth 2 hd) (nth 3 hd) hpg)))))

(defun vrt-plain-walk (i w hd hpg vrx)
  (declare (xargs :stobjs (hpg vrx) :verify-guards nil :measure (nfix i)))
  (and (or (not (integerp w)) (< w 5) (vrt-plain-at w hd hpg vrx))
       (if (zp i) t (vrt-plain-walk (1- i) (vrt-cdr-at w hpg) hd hpg vrx))))

; only place 1 reads the value decoded: any other is the same whatever it is
(defthm vrt-decp-not-self
  (implies (and (syntaxp (not (and (equal tag ''0) (equal ref ''0) (equal ival ''0)))) (not (equal p 1)))
           (equal (vrt-decp p tag ref ival d hd hpg vrx) (vrt-decp p 0 0 0 d hd hpg vrx)))
  :hints (("Goal" :expand ((vrt-decp p tag ref ival d hd hpg vrx) (vrt-decp p 0 0 0 d hd hpg vrx)))))

; OPENERS: a word's value, and a plain value at a depth left
(defthm vrt-decp-word
  (implies (and (integerp w) (<= 5 w))
           (equal (vrt-decp w tag ref ival d hd hpg vrx)
                  (vrt-dec (hpg-ot w hpg) (hpg-or w hpg) (vrt-oiv w vrx) d hd hpg vrx)))
  :hints (("Goal" :expand ((vrt-decp w tag ref ival d hd hpg vrx)))))

(defthm vrt-decp-0 (equal (vrt-decp 0 tag ref ival d hd hpg vrx) nil)
  :hints (("Goal" :expand ((vrt-decp 0 tag ref ival d hd hpg vrx)))))

(defthm vrt-dec-plain
  (implies (and (posp d) (< (vrt-cfid tag ref hpg vrx) 0)
                (not (vrt-throwp tag ref (nth 0 hd) (nth 1 hd) hpg))
                (not (vrt-clol tag ref (nth 2 hd) (nth 3 hd) hpg)))
           (equal (vrt-dec tag ref ival d hd hpg vrx)
                  (cond ((equal tag 0) nil)
                        ((equal tag 1) (if (equal ival 0) :false t))
                        ((equal tag 2) ival)
                        ((vrt-consp tag ref hpg)
                         (cons (vrt-decp (vrt-car-place tag ref hpg) 0 0 0 (1- d) hd hpg vrx)
                               (vrt-decp (vrt-cdr-place tag ref hpg) 0 0 0 (1- d) hd hpg vrx)))
                        (t 'vrt-opaque))))
  :hints (("Goal" :expand ((vrt-dec tag ref ival d hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-throwp vrt-clol vrt-consp vrt-decp-word)
           :use ((:instance vrt-places-0-or-5)))))

(defthm vrt-car-at-0 (equal (vrt-car-at 0 hpg) 0) :hints (("Goal" :in-theory (enable vrt-car-at))))
(defthm vrt-cdr-at-0 (equal (vrt-cdr-at 0 hpg) 0) :hints (("Goal" :in-theory (enable vrt-cdr-at))))
(defthm vrt-walk-0 (equal (vrt-walk i 0 hpg) 0))

(defthm vrt-walk-agrees
  (implies (and (hpgp hpg) (vrxp vrx) (natp i) (natp d) (integerp w) (or (equal w 0) (<= 5 w))
                (vrt-plain-walk i w hd hpg vrx))
           (equal (nth i (vrt-decp w 0 0 0 (+ 1 i d) hd hpg vrx))
                  (vrt-decp (vrt-walk i w hpg) 0 0 0 d hd hpg vrx)))
  :hints (("Goal" :induct (vrt-walk i w hpg) :expand ((vrt-plain-walk i w hd hpg vrx))
           :in-theory (e/d (vrt-car-at vrt-cdr-at vrt-car-place vrt-cdr-place) (vrt-cfid vrt-throwp vrt-clol)))
          ("Subgoal *1/2" :use ((:instance vrt-places-0-or-5 (tag (hpg-ot w hpg)) (ref (hpg-or w hpg)))))))

(defthm vrt-capt-past
  (implies (and (<= 0 (vrt-cfid tag ref hpg vrx)) (< (vrt-cncap tag ref hpg vrx) i))
           (equal (vrt-capt-place i tag ref hpg vrx) 0))
  :hints (("Goal" :in-theory (disable vrt-cfid vrt-cncap vrt-unmeta))))

(defthm vrt-capt-compiled
  (implies (and (vrt-hyps) (natp i) (<= 0 (vrt-cfid tag ref hpg vrx)))
           (equal (rt-capt i (vrt-dec tag ref ival (+ 2 i d) hd hpg vrx))
                  (vrt-decp (vrt-capt-place i tag ref hpg vrx) tag ref ival d hd hpg vrx)))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 2 i d) hd hpg vrx))
           :in-theory (e/d (rt-capt clo-caps) (vrt-cfid vrt-cncap vrt-capt-place vrt-decp vrt-dec-caps
                                                vrt-decp-not-self vrt-nth-dec-caps vrt-dec-plain))
           :use ((:instance vrt-nth-dec-caps (k 0) (n (vrt-cncap tag ref hpg vrx)) (dd (+ 2 i d)))))))

(defthm vrt-dec-clol
  (implies (and (posp dd) (< (vrt-cfid tag ref hpg vrx) 0) (vrt-clol tag ref (nth 2 hd) (nth 3 hd) hpg))
           (equal (vrt-dec tag ref ival dd hd hpg vrx)
                  (list :clo (vrt-decp (vrt-cadr-place tag ref hpg) tag ref ival (1- dd) hd hpg vrx)
                        (vrt-decp (vrt-caddr-place tag ref hpg) tag ref ival (1- dd) hd hpg vrx))))
  :hints (("Goal" :expand ((vrt-dec tag ref ival dd hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-decp vrt-dec-plain vrt-decp-not-self))))

(defthm vrt-capt-list
  (implies (and (vrt-hyps) (natp i) (< (vrt-cfid tag ref hpg vrx) 0)
                (vrt-clol tag ref (nth 2 hd) (nth 3 hd) hpg)
                (vrt-plain-walk i (vrt-caddr-place tag ref hpg) hd hpg vrx))
           (equal (rt-capt i (vrt-dec tag ref ival (+ 2 i d) hd hpg vrx))
                  (vrt-decp (vrt-capt-place i tag ref hpg vrx) tag ref ival d hd hpg vrx)))
  :hints (("Goal"
           :in-theory (e/d (rt-capt clo-caps) (vrt-cfid vrt-cncap vrt-decp vrt-dec-caps vrt-walk-agrees
                                                vrt-dec-plain vrt-lcount vrt-throwp vrt-clol))
           :do-not-induct t :use (vrt-cxr-places (:instance vrt-walk-agrees (w (vrt-caddr-place tag ref hpg)))
                 (:instance vrt-walk-0-or-5 (w (vrt-caddr-place tag ref hpg)))
                 (:instance vrt-decp-not-self (p (vrt-walk i (vrt-caddr-place tag ref hpg) hpg)))
                 (:instance vrt-decp-not-self (p (vrt-caddr-place tag ref hpg)) (d (+ 1 i d)))))))

; rt-capt: a compiled closure's capture i, or element i of (CLO f caps)'s
; caps, walked through plain lists
(defthm vrt-capt-agrees
  (implies (and (vrt-hyps) (natp i) (vrt-clop tag ref (nth 2 hd) (nth 3 hd) hpg vrx)
                (or (<= 0 (vrt-cfid tag ref hpg vrx))
                    (vrt-plain-walk i (vrt-caddr-place tag ref hpg) hd hpg vrx)))
           (equal (rt-capt i (vrt-dec tag ref ival (+ 2 i d) hd hpg vrx))
                  (vrt-decp (vrt-capt-place i tag ref hpg vrx) tag ref ival d hd hpg vrx)))
  :hints (("Goal" :do-not-induct t :use (vrt-capt-compiled vrt-capt-list) :in-theory (e/d (vrt-clop) (vrt-capt-compiled vrt-capt-list vrt-cfid vrt-clol vrt-dec vrt-capt-place rt-capt vrt-decp)))))

; ---- THE ARITHMETIC AND THE COMPILER'S READS ------------------------------------------------

(defthm vrt-dec-number
  (implies (and (vrt-hyps) (not (equal tag 2)))
           (and (not (acl2-numberp (vrt-dec tag ref ival (+ 1 d) hd hpg vrx)))
                (not (rationalp (vrt-dec tag ref ival (+ 1 d) hd hpg vrx)))
                (not (integerp (vrt-dec tag ref ival (+ 1 d) hd hpg vrx)))))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 1 d) hd hpg vrx)))))

(defthm vrt-lt-agrees
  (implies (and (hpgp hpg) (vrxp vrx) (integerp ia) (integerp ib) (natp d))
           (equal (rt-lt (vrt-dec ta ra ia (+ 1 d) hd hpg vrx) (vrt-dec tb rb ib (+ 1 d) hd hpg vrx))
                  (if (vrt-lt ta ia tb ib) t :false)))
  :hints (("Goal" :cases ((equal ta 2) (equal tb 2))
           :expand ((vrt-dec 2 ra ia (+ 1 d) hd hpg vrx) (vrt-dec 2 rb ib (+ 1 d) hd hpg vrx))
           :use ((:instance vrt-dec-number (tag ta) (ref ra) (ival ia))
                 (:instance vrt-dec-number (tag tb) (ref rb) (ival ib))))))

(defthm vrt-add-agrees
  (implies (and (hpgp hpg) (vrxp vrx) (integerp ia) (integerp ib) (natp d)
                (vrt-add-fits (vrt-ifix ta ia) (vrt-ifix tb ib)))
           (equal (rt-add (vrt-dec ta ra ia (+ 1 d) hd hpg vrx) (vrt-dec tb rb ib (+ 1 d) hd hpg vrx))
                  (vrt-add ta ia tb ib)))
  :hints (("Goal" :cases ((equal ta 2) (equal tb 2))
           :expand ((vrt-dec 2 ra ia (+ 1 d) hd hpg vrx) (vrt-dec 2 rb ib (+ 1 d) hd hpg vrx))
           :use ((:instance vrt-dec-number (tag ta) (ref ra) (ival ia))
                 (:instance vrt-dec-number (tag tb) (ref rb) (ival ib))))))

;; THE OVERFLOW. rt-add is the sum in ACL2's unbounded integers; a 64-bit
;; word holds it exactly when vrt-add-fits says so (and vrt-add-agrees
;; holds). When it does not fit, no word holds the sum, so the runtime
;; (rt_add) answers a THROW -- an ArithmeticException "long overflow", as
;; clj's Numbers.add -- instead of a wrong word (it answered 0): the
;; theorems below are why the two branches of rt_add are the only two.
(defthm vrt-add-fits-representable
  (implies (and (sb64p a) (sb64p b) (vrt-add-fits a b)) (sb64p (+ a b))))

(defthm vrt-add-overflow-unrepresentable
  (implies (and (sb64p a) (sb64p b) (not (vrt-add-fits a b))) (not (sb64p (+ a b)))))

(defthm vrt-nat-agrees
  (implies (vrt-hyps)
           (equal (rt-nat (vrt-dec tag ref ival (+ 1 d) hd hpg vrx)) (vrt-nat tag ival)))
  :hints (("Goal" :cases ((equal tag 2)) :expand ((vrt-dec 2 ref ival (+ 1 d) hd hpg vrx))
           :use ((:instance vrt-dec-number)))))

(defthm vrt-consp-agrees
  (implies (and (vrt-hyps) (< (vrt-cfid tag ref hpg vrx) 0))
           (iff (rt-consp (vrt-dec tag ref ival (+ 1 d) hd hpg vrx)) (vrt-consp tag ref hpg)))
  :hints (("Goal" :expand ((vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
           :in-theory (disable vrt-cfid vrt-lcount vrt-dec-plain))))

; a plain value: no compiled closure, no marker list
(defmacro vrt-plain (tag ref)
  `(and (< (vrt-cfid ,tag ,ref hpg vrx) 0)
        (not (vrt-throwp ,tag ,ref (nth 0 hd) (nth 1 hd) hpg))
        (not (vrt-clol ,tag ,ref (nth 2 hd) (nth 3 hd) hpg))))

(defthm vrt-car-agrees
  (implies (and (vrt-hyps) (vrt-plain tag ref))
           (equal (rt-car (vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
                  (vrt-decp (vrt-car-place tag ref hpg) 0 0 0 d hd hpg vrx)))
  :hints (("Goal" :in-theory (e/d (vrt-car-place) (vrt-cfid vrt-throwp vrt-clol)))))

(defthm vrt-cdr-agrees
  (implies (and (vrt-hyps) (vrt-plain tag ref))
           (equal (rt-cdr (vrt-dec tag ref ival (+ 1 d) hd hpg vrx))
                  (vrt-decp (vrt-cdr-place tag ref hpg) 0 0 0 d hd hpg vrx)))
  :hints (("Goal" :in-theory (e/d (vrt-cdr-place vrt-car-place) (vrt-cfid vrt-throwp vrt-clol)))))

; ---- THE DISPATCH ---------------------------------------------------------------------------

(defthm vrt-prim-kind-range
  (and (integerp (vrt-prim-kind tag ref karg kar kder kcw kinv kinvm hpg))
       (<= 1 (vrt-prim-kind tag ref karg kar kder kcw kinv kinvm hpg))
       (<= (vrt-prim-kind tag ref karg kar kder kcw kinv kinvm hpg) 8)
       ; a keyword is chosen by identity alone, and only a keyword is
       (iff (member (vrt-prim-kind tag ref karg kar kder kcw kinv kinvm hpg) '(1 2 3 4 5))
            (and (equal tag 7) (member ref (list karg kar kder kcw kinv kinvm))))))

(defthm vrt-arg-slot-inside
  (implies (and (integerp rb) (integerp ival) (integerp len) (< 0 (vrt-arg-slot n tag ival rb len)))
           (and (<= 1 (vrt-arg-slot n tag ival rb len)) (<= (vrt-arg-slot n tag ival rb len) len)
                (equal (vrt-arg-slot n tag ival rb len) (+ rb ival 1)))))

; ---- COST, in heap reads -------------------------------------------------------------------
;
; Each read of a pool -- hpg-ot, hpg-or, hpg-okd, hpg-oi, an x- or arena
; read -- counts 1; hpg-obj-at and the lengths read nothing. Every function
; above not named here makes a constant number: vrt-lcount 2, a place 2 more
; at most, vrt-ctab 4, vrt-fid-of 12.

(defun-nx vrt-unmeta-reads (tag ref k hpg)
  (declare (xargs :measure (nfix k)))
  (cond ((not (and (integerp ref) (hpg-obj-at tag ref hpg))) 0)
        ((zp k) 0)
        ((equal (hpg-okd ref hpg) 8) (+ 3 (vrt-unmeta-reads (hpg-ot (* 5 ref) hpg) (hpg-or (* 5 ref) hpg) (1- k) hpg)))
        (t 1)))

; 3 a wrapper, so linear in the chain, at most the objects there are
(defthm vrt-unmeta-reads-bound
  (<= (vrt-unmeta-reads tag ref k hpg) (+ 1 (* 3 (nfix k))))
  :rule-classes (:rewrite :linear))

(defun-nx vrt-walk-reads (i w hpg)
  (declare (xargs :measure (nfix i)))
  (if (zp i) 4 (+ 4 (vrt-walk-reads (1- i) (vrt-cdr-at w hpg) hpg))))

; 4 a list cell walked: linear in the index
(defthm vrt-walk-reads-bound
  (equal (vrt-walk-reads i w hpg) (* 4 (+ 1 (nfix i)))))

(defun-nx vrt-cfid-reads (tag ref hpg) (+ (vrt-unmeta-reads tag ref (vrt-nobj hpg) hpg) 16))

(defun-nx vrt-clop-reads (tag ref hpg) (+ (vrt-cfid-reads tag ref hpg) 6))

; capture i: the closure's id, its count and its object (each an unmeta),
; then its slots or vector (4), or (CLO f caps)'s third (10) and the walk
(defun-nx vrt-capt-reads (i tag ref hpg vrx)
  (+ (vrt-cfid-reads tag ref hpg)
     (vrt-unmeta-reads tag ref (vrt-nobj hpg) hpg) 6
     (vrt-unmeta-reads tag ref (vrt-nobj hpg) hpg)
     (if (<= 0 (vrt-cfid tag ref hpg vrx)) 4 (+ 10 (vrt-walk-reads i (vrt-caddr-place tag ref hpg) hpg)))))

(defthm vrt-clop-reads-bound
  (<= (vrt-clop-reads tag ref hpg) (+ 23 (* 3 (vrt-nobj hpg))))
  :hints (("Goal" :in-theory (disable vrt-nobj))))

(defthm vrt-capt-reads-bound
  (implies (natp i)
           (<= (vrt-capt-reads i tag ref hpg vrx) (+ 43 (* 9 (vrt-nobj hpg)) (* 4 i))))
  :hints (("Goal" :in-theory (disable vrt-nobj vrt-cfid))))


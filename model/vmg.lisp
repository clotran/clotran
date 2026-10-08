; clotran's VM, formally (PLAN step 30): THE DEFINITIONS THE FORTRAN IS
; GENERATED FROM. vmi.lisp's machine, word for word, with guards, and
; every integer result declared (signed-byte 64). Verifying the guards
; proves what Fortran needs and ACL2's unbounded integers never asked:
; every array index in bounds, every value stored where it fits, and
; every intermediate result inside 64 bits -- Fortran's integer
; overflow being undefined.
;
;   vmg-X = vmi-X      each function is its vmi.lisp twin, so
;                      vmi-correct is about these
;   vmg-step-good      a step keeps the bounds, so a run stays in 64 bits
;
; THE BOUNDS. Array lengths are at most 2^40; registers and the words the
; code holds at most 2^40; the control stack's live records hold bounded
; fields and link below themselves; a function's clauses lie inside the
; clause arrays. 2^40 leaves room for the intermediate sums -- a frame
; base plus an operand, four times a pc -- far below 2^63.
;
; A value-level operation (truthy, the arithmetic on values, a closure's
; parts, the primitives) is the runtime's, hand-written Fortran; here it
; is called through ec-call and no Fortran is generated for it.

(in-package "ACL2")

(include-book "vmi")

(defconst *b40* 1099511627776)

(defmacro i64 (x) `(the (signed-byte 64) ,x))

(defun bnd40p (x) (declare (xargs :guard t)) (and (integerp x) (<= 0 x) (<= x *b40*)))

; an element of a 64-bit array is a 64-bit integer
(defmacro sb64-elems (p)
  `(defthm ,(intern-in-package-of-symbol (concatenate (quote string) (symbol-name p) "-NTH") p)
     (implies (and (,p l) (< (nfix i) (len l)))
              (and (integerp (nth i l)) (rationalp (nth i l)) (acl2-numberp (nth i l))
                   (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808)))
     :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (,p l) (< (nfix i) (len l))) (integerp (nth i l))))
                    (:linear :corollary (implies (and (,p l) (< (nfix i) (len l)))
                                                          (and (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808)))))))
(sb64-elems v-codep) (sb64-elems v-ckindp) (sb64-elems v-cap) (sb64-elems v-cbp) (sb64-elems v-ccp)
(sb64-elems v-cprevp) (sb64-elems v-fnfirstp) (sb64-elems v-fncountp) (sb64-elems v-clnp)
(sb64-elems v-clentp) (sb64-elems v-clrestp)

; ---- THE BOUNDS -----------------------------------------------------------------------------

(defun vmg-lens (vmi)
  (declare (xargs :stobjs vmi))
  (and (<= (v-code-length vmi) *b40*) (<= (v-pool-length vmi) *b40*) (<= (v-stk-length vmi) *b40*)
       (<= (v-ckind-length vmi) *b40*)
       (<= (v-ckind-length vmi) (v-ca-length vmi)) (<= (v-ckind-length vmi) (v-cb-length vmi))
       (<= (v-ckind-length vmi) (v-cc-length vmi)) (<= (v-ckind-length vmi) (v-cprev-length vmi))
       (<= (v-fnfirst-length vmi) *b40*) (<= (v-fnfirst-length vmi) (v-fncount-length vmi))
       (<= (v-cln-length vmi) *b40*) (<= (v-cln-length vmi) (v-clent-length vmi))
       (<= (v-cln-length vmi) (v-clrest-length vmi))))

; every code word below i bounded
(defun words-ok (i vmi)
  (declare (xargs :stobjs vmi :guard (and (natp i) (<= i (v-code-length vmi)))))
  (if (zp i) t (and (bnd40p (v-codei (1- i) vmi)) (words-ok (1- i) vmi))))

; every clause below c: its arity and entry bounded
(defun cls-ok (c vmi)
  (declare (xargs :stobjs vmi :guard (and (natp c) (<= c (v-cln-length vmi)) (<= (v-cln-length vmi) (v-clent-length vmi)))))
  (if (zp c) t (and (bnd40p (v-clni (1- c) vmi)) (bnd40p (v-clenti (1- c) vmi)) (cls-ok (1- c) vmi))))

; every function below f: its clauses inside the clause arrays
(defun fns-ok (f vmi)
  (declare (xargs :stobjs vmi :guard (and (natp f) (<= f (v-fnfirst-length vmi)) (<= (v-fnfirst-length vmi) (v-fncount-length vmi)))))
  (if (zp f)
      t
    (and (bnd40p (v-fnfirsti (1- f) vmi)) (bnd40p (v-fncounti (1- f) vmi))
         (<= (+ (v-fnfirsti (1- f) vmi) (v-fncounti (1- f) vmi)) (v-cln-length vmi))
         (fns-ok (1- f) vmi))))

; every live control record below j: bounded fields, linked below itself
(defun recs-ok (j vmi)
  (declare (xargs :stobjs vmi :guard (and (natp j) (<= j (v-ckind-length vmi)) (vmg-lens vmi))))
  (if (zp j)
      t
    (and (bnd40p (v-cai (1- j) vmi)) (bnd40p (v-cbi (1- j) vmi)) (bnd40p (v-cci (1- j) vmi))
         (integerp (v-cprevi (1- j) vmi)) (<= -1 (v-cprevi (1- j) vmi)) (< (v-cprevi (1- j) vmi) (1- j))
         (implies (equal (v-ckindi (1- j) vmi) 2)
                  (or (< (v-cprevi (1- j) vmi) 0) (equal (v-ckindi (v-cprevi (1- j) vmi) vmi) 2)))
         (recs-ok (1- j) vmi))))

(defun vmg-bnd (vmi)
  (declare (xargs :stobjs vmi))
  (and (vmg-lens vmi)
       (bnd40p (v-pc vmi)) (bnd40p (v-fb vmi)) (bnd40p (v-sp vmi))
       (natp (v-ctop vmi)) (<= (v-ctop vmi) (v-ckind-length vmi))
       (<= -1 (v-hidx vmi)) (< (v-hidx vmi) (v-ctop vmi))
       (or (< (v-hidx vmi) 0) (equal (v-ckindi (v-hidx vmi) vmi) 2))
       (words-ok (v-code-length vmi) vmi)
       (cls-ok (v-cln-length vmi) vmi)
       (fns-ok (v-fnfirst-length vmi) vmi)
       (recs-ok (v-ctop vmi) vmi)))

; a running machine is in bounds; a stopped one need not be
(defun vmg-good (vmi)
  (declare (xargs :stobjs vmi))
  (implies (equal (v-status vmi) 0) (vmg-bnd vmi)))

; ---- what the bounds give --------------------------------------------------------------------

(in-theory (disable bnd40p))
(defthm bnd40p-facts
  (implies (bnd40p x) (and (integerp x) (<= 0 x) (<= x *b40*)))
  :rule-classes ((:forward-chaining) (:rewrite)) :hints (("Goal" :in-theory (enable bnd40p))))

(defthm words-ok-nth
  (implies (and (words-ok i vmi) (natp j) (< j (nfix i))) (bnd40p (nth j (nth *v-codei* vmi))))
  :hints (("Goal" :induct (words-ok i vmi) :in-theory (disable nth bnd40p))))
(defthm cls-ok-nth
  (implies (and (cls-ok c vmi) (natp j) (< j (nfix c)))
           (and (bnd40p (nth j (nth *v-clni* vmi))) (bnd40p (nth j (nth *v-clenti* vmi)))))
  :hints (("Goal" :induct (cls-ok c vmi) :in-theory (disable nth bnd40p))))
(defthm fns-ok-nth
  (implies (and (fns-ok f vmi) (natp g) (< g (nfix f)))
           (and (bnd40p (nth g (nth *v-fnfirsti* vmi))) (bnd40p (nth g (nth *v-fncounti* vmi)))
                (<= (+ (nth g (nth *v-fnfirsti* vmi)) (nth g (nth *v-fncounti* vmi))) (len (nth *v-clni* vmi)))))
  :hints (("Goal" :induct (fns-ok f vmi) :in-theory (disable nth bnd40p))))
(defthm recs-ok-nth
  (implies (and (recs-ok j vmi) (natp i) (< i (nfix j)))
           (and (bnd40p (nth i (nth *v-cai* vmi))) (bnd40p (nth i (nth *v-cbi* vmi))) (bnd40p (nth i (nth *v-cci* vmi)))
                (<= -1 (nth i (nth *v-cprevi* vmi))) (< (nth i (nth *v-cprevi* vmi)) i)
                (implies (equal (nth i (nth *v-ckindi* vmi)) 2)
                         (or (< (nth i (nth *v-cprevi* vmi)) 0)
                             (equal (nth (nth i (nth *v-cprevi* vmi)) (nth *v-ckindi* vmi)) 2)))))
  :hints (("Goal" :induct (recs-ok j vmi) :in-theory (disable nth bnd40p))))

; ---- READING AND WRITING, bounded --------------------------------------------------------------

(defun vmg-w (pc k vmi)
  (declare (xargs :stobjs vmi :guard (and (natp pc) (<= pc *b40*) (natp k) (<= k 3))))
  (let ((i (i64 (+ (i64 (* 4 (nfix pc))) (nfix k)))))
    (if (< i (v-code-length vmi)) (v-codei i vmi) 0)))

(defun vmg-poolv (i vmi)
  (declare (xargs :stobjs vmi :guard (integerp i)))
  (if (< (nfix i) (v-pool-length vmi)) (v-pooli (nfix i) vmi) nil))

(defun vmg-sreg (i vmi)
  (declare (xargs :stobjs vmi :guard (integerp i)))
  (if (< (nfix i) (v-stk-length vmi)) (v-stki (nfix i) vmi) nil))

(defun vmg-sset (i v vmi)
  (declare (xargs :stobjs vmi :guard (integerp i)))
  (if (< (nfix i) (v-stk-length vmi))
      (update-v-stki (nfix i) v vmi)
    (update-v-status 2 vmi)))

; the slots a..a+k-1 as a list: the runtime builds it (rt_list_from)
(defun vmg-stk-from (a k vmi)
  (declare (xargs :stobjs vmi :guard (and (natp a) (natp k) (<= (+ a k) (* 2 *b40*))) :measure (nfix k)))
  (if (zp k) nil (cons (vmg-sreg a vmi) (vmg-stk-from (i64 (1+ (nfix a))) (1- k) vmi))))

(defun vmg-copy-down (src dst k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k)
                  :guard (and (natp src) (natp dst) (natp k) (<= (+ src k) (* 2 *b40*)) (<= (+ dst k) (* 2 *b40*)))))
  (if (zp k)
      vmi
    (let ((vmi (vmg-sset (nfix dst) (vmg-sreg (nfix src) vmi) vmi)))
      (vmg-copy-down (i64 (1+ (nfix src))) (i64 (1+ (nfix dst))) (1- k) vmi))))

(defthm vmg-w-is (equal (vmg-w pc k vmi) (vmi-w pc k vmi)))
(defthm vmg-poolv-is (equal (vmg-poolv i vmi) (vmi-poolv i vmi)))
(defthm vmg-sreg-is (equal (vmg-sreg i vmi) (vmi-sreg i vmi)))
(defthm vmg-sset-is (equal (vmg-sset i v vmi) (vmi-sset i v vmi)))
(defthm vmg-stk-from-is (equal (vmg-stk-from a k vmi) (vmi-stk-from a k vmi)))
(defthm vmg-copy-down-is (equal (vmg-copy-down src dst k vmi) (vmi-copy-down src dst k vmi)))
(in-theory (disable vmg-w-is vmg-poolv-is vmg-sreg-is vmg-sset-is vmg-stk-from-is vmg-copy-down-is))

; ---- THE RUNTIME'S OPERATIONS ON VALUES (hand-written Fortran, rt_*) ---------------------------

(defun rt-truthy (x) (declare (xargs :guard t)) (ec-call (truthy x)))
(defun rt-add (a b) (declare (xargs :guard t)) (+ (fix a) (fix b)))
(defun rt-lt (a b) (declare (xargs :guard t)) (ec-call (bool (< (rfix a) (rfix b)))))
(defun rt-clo (f caps) (declare (xargs :guard t)) (ec-call (clo f caps)))
(defun rt-clop (c) (declare (xargs :guard t)) (ec-call (clop c)))
(defun rt-clo-f (c) (declare (xargs :guard t)) (ec-call (clo-f c)))
(defun rt-capt (i c) (declare (xargs :guard t)) (ec-call (nth i (ec-call (clo-caps c)))))
(defun rt-prim (op args) (declare (xargs :guard t)) (prim op args))
(defun rt-throwp (a) (declare (xargs :guard t)) (ec-call (throwp a)))
(defun rt-thrown (a) (declare (xargs :guard t)) (ec-call (cdr a)))

; ---- what the code's words give -------------------------------------------------------------

(defthm vmg-w-bnd
  (implies (vmg-bnd vmi) (bnd40p (vmg-w pc k vmi)))
  :hints (("Goal" :in-theory (e/d (bnd40p) (nth words-ok-nth)) :do-not-induct t
                  :use ((:instance words-ok-nth (i (len (nth *v-codei* vmi))) (j (+ (* 4 (nfix pc)) (nfix k))))))))

(defthm vmg-w-linear
  (implies (vmg-bnd vmi) (and (<= 0 (vmg-w pc k vmi)) (<= (vmg-w pc k vmi) *b40*)))
  :rule-classes :linear
  :hints (("Goal" :use vmg-w-bnd :in-theory (e/d (bnd40p) (vmg-w-bnd)))))

(defthm vmg-w-integer
  (implies (v-codep (nth *v-codei* vmi))
           (and (integerp (vmg-w pc k vmi)) (rationalp (vmg-w pc k vmi)) (acl2-numberp (vmg-w pc k vmi))))
  :hints (("Goal" :in-theory (disable nth))))

; an instruction is there: its pc is a quarter of the code at most
(defthm vmg-w-integer-tp
  (implies (v-codep (nth *v-codei* vmi)) (integerp (vmg-w pc k vmi)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable nth))))

(defthm vmg-w-there
  (implies (and (natp pc) (not (equal (vmg-w pc 0 vmi) 0))) (< (* 4 pc) (len (nth *v-codei* vmi))))
  :rule-classes :linear)

(defthm vmg-w-frame
  (implies (not (equal k2 *v-codei*)) (equal (vmg-w pc k (update-nth k2 v vmi)) (vmg-w pc k vmi))))
(defthm vmg-w-copy-down (equal (vmg-w pc k (vmg-copy-down src dst n vmi)) (vmg-w pc k vmi))
  :hints (("Goal" :in-theory (disable vmg-w nth update-nth))))
(defthm vmg-w-sset (equal (vmg-w pc k (vmg-sset i v vmi)) (vmg-w pc k vmi)))

(in-theory (disable vmg-w))

; ---- THE CONTROL STACK ------------------------------------------------------------------------

(defmacro ctl-room () '(and (vmg-lens vmi) (natp (v-ctop vmi)) (<= (v-ctop vmi) (v-ckind-length vmi))))

(defun vmg-push-rec (kind a b c vmi)
  (declare (xargs :stobjs vmi :guard (and (ctl-room) (member kind '(1 2)) (bnd40p a) (bnd40p b) (bnd40p c))))
  (let ((j (nfix (v-ctop vmi))))
    (if (< j (v-ckind-length vmi))
        (let* ((vmi (update-v-ckindi j kind vmi))
               (vmi (update-v-cai j a vmi))
               (vmi (update-v-cbi j b vmi))
               (vmi (update-v-cci j c vmi))
               (vmi (update-v-cprevi j (v-hidx vmi) vmi))
               (vmi (if (equal kind 2) (update-v-hidx j vmi) vmi)))
          (update-v-ctop (i64 (1+ j)) vmi))
      (update-v-status 2 vmi))))

(defun vmg-pop-rec (vmi)
  (declare (xargs :stobjs vmi :guard (ctl-room)))
  (let ((j (i64 (1- (nfix (v-ctop vmi))))))
    (if (< j 0)
        vmi
      (let ((vmi (if (equal (v-ckindi j vmi) 2) (update-v-hidx (v-cprevi j vmi) vmi) vmi)))
        (update-v-ctop j vmi)))))

(defun vmg-unwind (v vmi)
  (declare (xargs :stobjs vmi :guard (vmg-bnd vmi)
                  :guard-hints (("Goal" :do-not-induct t :in-theory (disable recs-ok words-ok cls-ok fns-ok recs-ok-nth nth update-nth)
                                 :use ((:instance recs-ok-nth (j (v-ctop vmi)) (i (v-hidx vmi))))))))
  (let ((j (v-hidx vmi)))
    (if (or (not (integerp j)) (< j 0))
        (let* ((vmi (vmg-sset 0 v vmi))
               (vmi (if (equal (v-status vmi) 2) vmi (update-v-status 1 vmi)))
               (vmi (update-v-pc 0 vmi))
               (vmi (update-v-fb 0 vmi))
               (vmi (update-v-sp 1 vmi))
               (vmi (update-v-ctop 0 vmi)))
          (update-v-hidx -1 vmi))
      (let* ((h (nfix (v-cai j vmi))) (hfb (nfix (v-cbi j vmi))) (hd (nfix (v-cci j vmi)))
             (vmi (vmg-sset (i64 (+ hfb hd)) v vmi))
             (vmi (update-v-pc h vmi))
             (vmi (update-v-fb hfb vmi))
             (vmi (update-v-sp (i64 (+ hfb hd 1)) vmi))
             (vmi (update-v-ctop j vmi)))
        (update-v-hidx (v-cprevi j vmi) vmi)))))

(defthm vmg-push-rec-other
  (implies (member k '(6 7 8 14 15 16 17 18)) (equal (nth k (vmg-push-rec kind a b c vmi)) (nth k vmi)))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm vmg-w-push-pop-unwind
  (and (equal (vmg-w pc k (vmg-push-rec kind a b c vmi)) (vmg-w pc k vmi))
       (equal (vmg-w pc k (vmg-pop-rec vmi)) (vmg-w pc k vmi))
       (equal (vmg-w pc k (vmg-unwind x vmi)) (vmg-w pc k vmi)))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm vmg-push-rec-is (equal (vmg-push-rec kind a b c vmi) (vmi-push-rec kind a b c vmi)))
(defthm vmg-pop-rec-is (equal (vmg-pop-rec vmi) (vmi-pop-rec vmi)))
(defthm vmg-unwind-is (equal (vmg-unwind v vmi) (vmi-unwind v vmi)))
(in-theory (disable vmg-push-rec-is vmg-pop-rec-is vmg-unwind-is))

; ---- THE FUNCTION TABLE -----------------------------------------------------------------------

(defmacro cl-room2 (ci k)
  `(and (vmg-lens vmi) (natp ,ci) (natp ,k) (<= (+ ,ci ,k) (v-cln-length vmi))))

(defun vmg-pick-fixed (ci k m vmi)
  (declare (xargs :stobjs vmi :guard (and (cl-room2 ci k) (natp m)) :measure (nfix k)))
  (cond ((zp k) -1)
        ((and (not (equal (v-clresti (nfix ci) vmi) 1)) (equal (nfix (v-clni (nfix ci) vmi)) m)) (nfix ci))
        (t (vmg-pick-fixed (i64 (1+ (nfix ci))) (1- k) m vmi))))

(defun vmg-pick-rest (ci k m vmi)
  (declare (xargs :stobjs vmi :guard (and (cl-room2 ci k) (natp m)) :measure (nfix k)))
  (cond ((zp k) -1)
        ((and (equal (v-clresti (nfix ci) vmi) 1) (<= (nfix (v-clni (nfix ci) vmi)) m)) (nfix ci))
        (t (vmg-pick-rest (i64 (1+ (nfix ci))) (1- k) m vmi))))

(defun vmg-pick (f m vmi)
  (declare (xargs :stobjs vmi :guard (and (vmg-bnd vmi) (natp m))))
  (if (and (natp f) (< f (v-fnfirst-length vmi)))
      (let* ((ci (v-fnfirsti f vmi)) (k (v-fncounti f vmi)) (x (vmg-pick-fixed ci k m vmi)))
        (if (<= 0 x) x (vmg-pick-rest ci k m vmi)))
    -1))

(defthm vmg-pick-fixed-is (equal (vmg-pick-fixed ci k m vmi) (vmi-pick-fixed ci k m vmi))
  :hints (("Goal" :induct (vmg-pick-fixed ci k m vmi) :in-theory (disable nth))))
(defthm vmg-pick-rest-is (equal (vmg-pick-rest ci k m vmi) (vmi-pick-rest ci k m vmi))
  :hints (("Goal" :induct (vmg-pick-rest ci k m vmi) :in-theory (disable nth))))
(defthm vmg-pick-is (equal (vmg-pick f m vmi) (vmi-pick f m vmi)))
(in-theory (disable vmg-pick-fixed-is vmg-pick-rest-is vmg-pick-is))

; the clause a pick finds lies inside the clause arrays, its arity at
; most the count
(defthm vmg-pick-fixed-range
  (implies (and (natp ci) (natp m) (<= 0 (vmg-pick-fixed ci k m vmi)))
           (and (<= ci (vmg-pick-fixed ci k m vmi)) (< (vmg-pick-fixed ci k m vmi) (+ ci (nfix k)))
                (<= (nfix (nth (vmg-pick-fixed ci k m vmi) (nth *v-clni* vmi))) m)))
  :hints (("Goal" :induct (vmg-pick-fixed ci k m vmi) :in-theory (disable nth vmg-pick-fixed-is))))

(defthm vmg-pick-rest-range
  (implies (and (natp ci) (natp m) (<= 0 (vmg-pick-rest ci k m vmi)))
           (and (<= ci (vmg-pick-rest ci k m vmi)) (< (vmg-pick-rest ci k m vmi) (+ ci (nfix k)))
                (<= (nfix (nth (vmg-pick-rest ci k m vmi) (nth *v-clni* vmi))) m)))
  :hints (("Goal" :induct (vmg-pick-rest ci k m vmi) :in-theory (disable nth vmg-pick-rest-is))))

(defthm vmg-pick-fixed-int
  (and (integerp (vmg-pick-fixed ci k m vmi)) (<= -1 (vmg-pick-fixed ci k m vmi)))
  :hints (("Goal" :induct (vmg-pick-fixed ci k m vmi) :in-theory (disable nth vmg-pick-fixed-is))))
(defthm vmg-pick-rest-int
  (and (integerp (vmg-pick-rest ci k m vmi)) (<= -1 (vmg-pick-rest ci k m vmi)))
  :hints (("Goal" :induct (vmg-pick-rest ci k m vmi) :in-theory (disable nth vmg-pick-rest-is))))

(defthm vmg-pick-range
  (implies (and (vmg-bnd vmi) (natp m))
           (and (integerp (vmg-pick f m vmi)) (<= -1 (vmg-pick f m vmi))
                (implies (<= 0 (vmg-pick f m vmi))
                         (and (< (vmg-pick f m vmi) (v-cln-length vmi))
                              (<= (nfix (nth (vmg-pick f m vmi) (nth *v-clni* vmi))) m)))))
  :hints (("Goal" :in-theory (disable nth vmg-pick-fixed vmg-pick-rest fns-ok-nth fns-ok words-ok cls-ok recs-ok vmg-pick-is vmg-pick-fixed-is vmg-pick-rest-is)
                  :use ((:instance fns-ok-nth (f (len (nth *v-fnfirsti* vmi))) (g f))
                        (:instance vmg-pick-fixed-range (ci (nth f (nth *v-fnfirsti* vmi))) (k (nth f (nth *v-fncounti* vmi))))
                        (:instance vmg-pick-rest-range (ci (nth f (nth *v-fnfirsti* vmi))) (k (nth f (nth *v-fncounti* vmi))))))))

(defthm vmg-pick-linear
  (implies (and (vmg-bnd vmi) (natp m) (<= 0 (vmg-pick f m vmi)))
           (< (vmg-pick f m vmi) (len (nth *v-clni* vmi))))
  :rule-classes :linear
  :hints (("Goal" :use vmg-pick-range :in-theory (disable vmg-pick-range))))

(defthm vmg-pick-clause
  (implies (and (vmg-bnd vmi) (natp m) (<= 0 (vmg-pick f m vmi)))
           (and (integerp (nth (vmg-pick f m vmi) (nth *v-clni* vmi)))
                (<= 0 (nth (vmg-pick f m vmi) (nth *v-clni* vmi)))
                (<= (nth (vmg-pick f m vmi) (nth *v-clni* vmi)) m)
                (bnd40p (nth (vmg-pick f m vmi) (nth *v-clenti* vmi)))))
  :rule-classes ((:rewrite)
                 (:linear :corollary (implies (and (vmg-bnd vmi) (natp m) (<= 0 (vmg-pick f m vmi)))
                                              (and (<= 0 (nth (vmg-pick f m vmi) (nth *v-clni* vmi)))
                                                   (<= (nth (vmg-pick f m vmi) (nth *v-clni* vmi)) m)))))
  :hints (("Goal" :use (vmg-pick-range (:instance cls-ok-nth (c (len (nth *v-clni* vmi))) (j (vmg-pick f m vmi))))
                  :in-theory (e/d (bnd40p) (vmg-pick-range cls-ok-nth)))))

(in-theory (disable vmg-pick vmg-pick-fixed vmg-pick-rest))

; the bounds' facts, by forward chaining, and the bounds kept closed
(defthm vmg-bnd-fc
  (implies (vmg-bnd vmi)
           (and (vmg-lens vmi)
                (bnd40p (nth *v-pc* vmi)) (bnd40p (nth *v-fb* vmi)) (bnd40p (nth *v-sp* vmi))
                (natp (nth *v-ctop* vmi)) (<= (nth *v-ctop* vmi) (len (nth *v-ckindi* vmi)))
                (<= -1 (nth *v-hidx* vmi)) (< (nth *v-hidx* vmi) (nth *v-ctop* vmi))
                (or (< (nth *v-hidx* vmi) 0) (equal (nth (nth *v-hidx* vmi) (nth *v-ckindi* vmi)) 2))
                (words-ok (len (nth *v-codei* vmi)) vmi)
                (cls-ok (len (nth *v-clni* vmi)) vmi)
                (fns-ok (len (nth *v-fnfirsti* vmi)) vmi)
                (recs-ok (nth *v-ctop* vmi) vmi)))
  :rule-classes :forward-chaining)

(defthm vmg-lens-fc
  (implies (vmg-lens vmi)
           (and (<= (len (nth *v-codei* vmi)) *b40*) (<= (len (nth *v-pooli* vmi)) *b40*) (<= (len (nth *v-stki* vmi)) *b40*)
                (<= (len (nth *v-ckindi* vmi)) *b40*)
                (<= (len (nth *v-ckindi* vmi)) (len (nth *v-cai* vmi))) (<= (len (nth *v-ckindi* vmi)) (len (nth *v-cbi* vmi)))
                (<= (len (nth *v-ckindi* vmi)) (len (nth *v-cci* vmi))) (<= (len (nth *v-ckindi* vmi)) (len (nth *v-cprevi* vmi)))
                (<= (len (nth *v-fnfirsti* vmi)) *b40*) (<= (len (nth *v-fnfirsti* vmi)) (len (nth *v-fncounti* vmi)))
                (<= (len (nth *v-clni* vmi)) *b40*) (<= (len (nth *v-clni* vmi)) (len (nth *v-clenti* vmi)))
                (<= (len (nth *v-clni* vmi)) (len (nth *v-clresti* vmi)))))
  :rule-classes :forward-chaining)

(in-theory (disable vmg-bnd))

; ---- THE INSTRUCTIONS -------------------------------------------------------------------------
;
; each runs on a running machine in bounds, at an instruction that is there

(defmacro ins-guard ()
  '(and (equal (v-status vmi) 0) (vmg-bnd vmi) (not (equal (vmg-w (v-pc vmi) 0 vmi) 0))))

(defmacro defins (name &rest body)
  `(defun ,name (vmi)
     (declare (xargs :stobjs vmi :guard (ins-guard)
                     :guard-hints (("Goal" :do-not-induct t
                                    :in-theory (e/d (bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok))))))
     ,@body))

; the call's guard proof, given the picked clause's facts
(defmacro defins-call (name &rest body)
  `(defun ,name (vmi)
     (declare (xargs :stobjs vmi :guard (ins-guard)
                     :guard-hints (("Goal" :do-not-induct t
                                    :in-theory (e/d (bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-pick-clause))
                                    :use ((:instance vmg-pick-clause
                                                     (f (rt-clo-f (vmg-sreg (+ -1 (nfix (v-sp vmi))) vmi)))
                                                     (m (nfix (vmg-w (v-pc vmi) 1 vmi)))))))))
     ,@body))

(defmacro vmg-next (vmi) `(update-v-pc (i64 (1+ (nfix (v-pc ,vmi)))) ,vmi))

(defins vmg-push
  (let* ((sp (nfix (v-sp vmi)))
         (vmi (vmg-sset sp (vmg-poolv (vmg-w (v-pc vmi) 1 vmi) vmi) vmi))
         (vmi (update-v-sp (i64 (1+ sp)) vmi)))
    (vmg-next vmi)))

(defins vmg-load
  (let* ((sp (nfix (v-sp vmi)))
         (vmi (vmg-sset sp (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w (v-pc vmi) 1 vmi)))) vmi) vmi))
         (vmi (update-v-sp (i64 (1+ sp)) vmi)))
    (vmg-next vmi)))

(defins vmg-add
  (let ((sp (nfix (v-sp vmi))))
    (if (< sp 2)
        vmi
      (let* ((vmi (vmg-sset (i64 (- sp 2)) (rt-add (vmg-sreg (i64 (- sp 2)) vmi) (vmg-sreg (i64 (1- sp)) vmi)) vmi))
             (vmi (update-v-sp (i64 (1- sp)) vmi)))
        (vmg-next vmi)))))

(defins vmg-lt
  (let ((sp (nfix (v-sp vmi))))
    (if (< sp 2)
        vmi
      (let* ((vmi (vmg-sset (i64 (- sp 2)) (rt-lt (vmg-sreg (i64 (- sp 2)) vmi) (vmg-sreg (i64 (1- sp)) vmi)) vmi))
             (vmi (update-v-sp (i64 (1- sp)) vmi)))
        (vmg-next vmi)))))

(defins vmg-slide
  (let ((sp (nfix (v-sp vmi))))
    (if (< sp 2)
        vmi
      (let* ((vmi (vmg-sset (i64 (- sp 2)) (vmg-sreg (i64 (1- sp)) vmi) vmi))
             (vmi (update-v-sp (i64 (1- sp)) vmi)))
        (vmg-next vmi)))))

(defins vmg-jmpf
  (let ((sp (nfix (v-sp vmi))))
    (if (zp sp)
        vmi
      (let ((vmi (update-v-sp (i64 (1- sp)) vmi)))
        (if (rt-truthy (vmg-sreg (i64 (1- sp)) vmi))
            (vmg-next vmi)
          (update-v-pc (nfix (vmg-w (v-pc vmi) 1 vmi)) vmi))))))

(defins vmg-jmp
  (update-v-pc (nfix (vmg-w (v-pc vmi) 1 vmi)) vmi))

(defins vmg-mkclo
  (let ((sp (nfix (v-sp vmi))) (k (nfix (vmg-w (v-pc vmi) 2 vmi))))
    (if (< sp k)
        vmi
      (let* ((vmi (vmg-sset (i64 (- sp k)) (rt-clo (vmg-w (v-pc vmi) 1 vmi) (vmg-stk-from (i64 (- sp k)) k vmi)) vmi))
             (vmi (update-v-sp (i64 (1+ (- sp k))) vmi)))
        (vmg-next vmi)))))

(defins vmg-capt
  (let* ((sp (nfix (v-sp vmi)))
         (c (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w (v-pc vmi) 1 vmi)))) vmi))
         (vmi (vmg-sset sp (rt-capt (nfix (vmg-w (v-pc vmi) 2 vmi)) c) vmi))
         (vmi (update-v-sp (i64 (1+ sp)) vmi)))
    (vmg-next vmi)))

(defins-call vmg-callv
  (let ((sp (nfix (v-sp vmi))) (m (nfix (vmg-w (v-pc vmi) 1 vmi))))
    (if (< sp (i64 (1+ m)))
        vmi
      (let ((c (vmg-sreg (i64 (1- sp)) vmi)))
        (if (not (rt-clop c))
            (vmg-unwind :not-fn vmi)
          (let ((ci (vmg-pick (rt-clo-f c) m vmi)))
            (if (< ci 0)
                (vmg-unwind :arity vmi)
              (let* ((fb2 (i64 (- sp (i64 (1+ m))))) (n (nfix (v-clni ci vmi))) (ent (nfix (v-clenti ci vmi)))
                     (vmi (vmg-push-rec 1 (i64 (1+ (nfix (v-pc vmi)))) (nfix (v-fb vmi)) 0 vmi)))
                (if (equal (v-clresti ci vmi) 1)
                    (let* ((vmi (vmg-sset (i64 (+ fb2 n)) (vmg-stk-from (i64 (+ fb2 n)) (i64 (- m n)) vmi) vmi))
                           (vmi (vmg-sset (i64 (+ fb2 n 1)) c vmi))
                           (vmi (update-v-fb fb2 vmi))
                           (vmi (update-v-sp (i64 (+ fb2 n 2)) vmi)))
                      (update-v-pc ent vmi))
                  (let* ((vmi (update-v-fb fb2 vmi)))
                    (update-v-pc ent vmi)))))))))))

(defins vmg-ret
  (let ((sp (nfix (v-sp vmi))) (fb (nfix (v-fb vmi))))
    (if (zp sp)
        vmi
      (let ((v (vmg-sreg (i64 (1- sp)) vmi)))
        (if (zp (v-ctop vmi))
            (let* ((vmi (vmg-sset 0 v vmi)))
              (update-v-sp 1 vmi))
          (let* ((j (i64 (1- (v-ctop vmi))))
                 (hp (equal (v-ckindi j vmi) 2))
                 (npc (if hp 0 (nfix (v-cai j vmi))))
                 (nfb (if hp (nfix (v-cai j vmi)) (nfix (v-cbi j vmi))))
                 (vmi (vmg-sset fb v vmi))
                 (vmi (update-v-sp (i64 (1+ fb)) vmi))
                 (vmi (vmg-pop-rec vmi))
                 (vmi (update-v-fb nfb vmi)))
            (update-v-pc npc vmi)))))))

(defins vmg-recur
  (let* ((pc (v-pc vmi)) (k (nfix (vmg-w pc 1 vmi))) (b (nfix (vmg-w pc 2 vmi))) (l (nfix (vmg-w pc 3 vmi)))
         (fb (nfix (v-fb vmi))) (sp (nfix (v-sp vmi))))
    (if (< sp (i64 (+ fb b k)))
        vmi
      (let* ((vmi (vmg-copy-down (i64 (- sp k)) (i64 (+ fb b)) k vmi))
             (vmi (update-v-sp (i64 (+ fb b k)) vmi)))
        (update-v-pc l vmi)))))

(defins vmg-prim
  (let ((sp (nfix (v-sp vmi))) (n (nfix (vmg-w (v-pc vmi) 2 vmi))))
    (if (< sp n)
        vmi
      (let ((a (rt-prim (vmg-poolv (vmg-w (v-pc vmi) 1 vmi) vmi) (vmg-stk-from (i64 (- sp n)) n vmi))))
        (if (rt-throwp a)
            (vmg-unwind (rt-thrown a) vmi)
          (let* ((vmi (vmg-sset (i64 (- sp n)) a vmi))
                 (vmi (update-v-sp (i64 (1+ (- sp n))) vmi)))
            (vmg-next vmi)))))))

(defins vmg-throw
  (let ((sp (nfix (v-sp vmi))))
    (if (zp sp) vmi (vmg-unwind (vmg-sreg (i64 (1- sp)) vmi) vmi))))

(defins vmg-try
  (let* ((pc (v-pc vmi))
         (vmi (vmg-push-rec 2 (nfix (vmg-w pc 1 vmi)) (nfix (v-fb vmi)) (nfix (vmg-w pc 2 vmi)) vmi)))
    (vmg-next vmi)))

(defins vmg-endtry
  (let ((vmi (vmg-pop-rec vmi)))
    (vmg-next vmi)))

; ---- ONE STEP --------------------------------------------------------------------------------

(defun vmg-step (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-good vmi)
                  :guard-hints (("Goal" :do-not-induct t :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok)))))
  (if (not (equal (v-status vmi) 0))
      vmi
    (case (vmg-w (v-pc vmi) 0 vmi)
      (1 (vmg-push vmi)) (2 (vmg-load vmi)) (3 (vmg-add vmi)) (4 (vmg-lt vmi)) (5 (vmg-slide vmi))
      (6 (vmg-jmpf vmi)) (7 (vmg-jmp vmi)) (8 (vmg-mkclo vmi)) (9 (vmg-capt vmi)) (10 (vmg-callv vmi))
      (11 (vmg-ret vmi)) (12 (vmg-recur vmi)) (13 (vmg-prim vmi)) (14 (vmg-throw vmi)) (15 (vmg-try vmi))
      (16 (vmg-endtry vmi))
      (otherwise vmi))))

; ---- EACH IS ITS VMI TWIN --------------------------------------------------------------------

(defmacro def-is (g i)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name g) "-IS") g)
     (equal (,g vmi) (,i vmi))
     :hints (("Goal" :in-theory (enable vmg-w-is vmg-poolv-is vmg-sreg-is vmg-sset-is vmg-stk-from-is vmg-copy-down-is
                                        vmg-push-rec-is vmg-pop-rec-is vmg-unwind-is vmg-pick-is vmg-pick-fixed-is
                                        vmg-pick-rest-is vmi-pick vmg-pick)))))

(def-is vmg-push vmi-push) (def-is vmg-load vmi-load) (def-is vmg-add vmi-add) (def-is vmg-lt vmi-lt)
(def-is vmg-slide vmi-slide) (def-is vmg-jmpf vmi-jmpf) (def-is vmg-jmp vmi-jmp) (def-is vmg-mkclo vmi-mkclo)
(def-is vmg-capt vmi-capt) (def-is vmg-callv vmi-callv) (def-is vmg-ret vmi-ret) (def-is vmg-recur vmi-recur)
(def-is vmg-prim vmi-prim) (def-is vmg-throw vmi-throw) (def-is vmg-try vmi-try) (def-is vmg-endtry vmi-endtry)

; THE STEP THE FORTRAN IS GENERATED FROM IS VMI's, so vmi-correct is about it
(defthm vmg-step-is
  (equal (vmg-step vmi) (vmi-step vmi))
  :hints (("Goal" :in-theory (enable vmg-w-is))))

(in-theory (disable vmg-push-is vmg-load-is vmg-add-is vmg-lt-is vmg-slide-is vmg-jmpf-is vmg-jmp-is vmg-mkclo-is
                    vmg-capt-is vmg-callv-is vmg-ret-is vmg-recur-is vmg-prim-is vmg-throw-is vmg-try-is vmg-endtry-is
                    vmg-step-is))

; ---- A STEP KEEPS THE BOUNDS -----------------------------------------------------------------

(defthm len-update-nth-in-range
  (implies (< (nfix i) (len l)) (equal (len (update-nth i x l)) (len l))))

; what each bound reads
(defthm words-ok-frame
  (implies (not (equal k *v-codei*)) (equal (words-ok n (update-nth k v vmi)) (words-ok n vmi)))
  :hints (("Goal" :induct (words-ok n vmi) :in-theory (disable nth update-nth))))
(defthm cls-ok-frame
  (implies (not (member k (list *v-clni* *v-clenti*))) (equal (cls-ok n (update-nth k v vmi)) (cls-ok n vmi)))
  :hints (("Goal" :induct (cls-ok n vmi) :in-theory (disable nth update-nth))))
(defthm fns-ok-frame
  (implies (not (member k (list *v-fnfirsti* *v-fncounti* *v-clni*))) (equal (fns-ok n (update-nth k v vmi)) (fns-ok n vmi)))
  :hints (("Goal" :induct (fns-ok n vmi) :in-theory (disable nth update-nth))))
(defthm recs-ok-frame
  (implies (not (member k (list *v-ckindi* *v-cai* *v-cbi* *v-cci* *v-cprevi*))) (equal (recs-ok n (update-nth k v vmi)) (recs-ok n vmi)))
  :hints (("Goal" :induct (recs-ok n vmi) :in-theory (disable nth update-nth))))

; a record written at or above n leaves the records below n
(defthm recs-ok-above
  (implies (and (member k (list *v-cai* *v-cbi* *v-cci* *v-cprevi*)) (natp i) (<= (nfix n) i))
           (equal (recs-ok n (update-nth k (update-nth i x (nth k vmi)) vmi)) (recs-ok n vmi)))
  :hints (("Goal" :induct (recs-ok n vmi) :in-theory (disable nth update-nth))))

(defthm recs-ok-smaller
  (implies (and (recs-ok n vmi) (natp m) (<= m (nfix n))) (recs-ok m vmi))
  :hints (("Goal" :induct (recs-ok n vmi) :in-theory (disable nth update-nth))))

(defthm vmg-lens-frame
  (implies (and (member k '(0 1 2 3 4 5)))
           (equal (vmg-lens (update-nth k v vmi)) (vmg-lens vmi))))

(defthm vmg-lens-write
  (implies (and (member k (list *v-stki* *v-ckindi* *v-cai* *v-cbi* *v-cci* *v-cprevi*)) (equal (len l) (len (nth k vmi))))
           (equal (vmg-lens (update-nth k l vmi)) (vmg-lens vmi))))

(defthm update-nth-update-nth-same
  (equal (update-nth k a (update-nth k b x)) (update-nth k a x)))

; the control stack's operations, by their effect on each field
(defthm vmg-push-rec-fields
  (let ((p (vmg-push-rec kind a b c vmi)) (j (nfix (nth *v-ctop* vmi))) (ok (< (nfix (nth *v-ctop* vmi)) (len (nth *v-ckindi* vmi)))))
    (and (implies (member k '(0 1 2 6 7 8 14 15 16 17 18)) (equal (nth k p) (nth k vmi)))
         (equal (nth *v-status* p) (if ok (nth *v-status* vmi) 2))
         (equal (nth *v-ctop* p) (if ok (1+ j) (nth *v-ctop* vmi)))
         (equal (nth *v-hidx* p) (if (and ok (equal kind 2)) j (nth *v-hidx* vmi)))
         (equal (nth *v-ckindi* p) (if ok (update-nth j kind (nth *v-ckindi* vmi)) (nth *v-ckindi* vmi)))
         (equal (nth *v-cai* p) (if ok (update-nth j a (nth *v-cai* vmi)) (nth *v-cai* vmi)))
         (equal (nth *v-cbi* p) (if ok (update-nth j b (nth *v-cbi* vmi)) (nth *v-cbi* vmi)))
         (equal (nth *v-cci* p) (if ok (update-nth j c (nth *v-cci* vmi)) (nth *v-cci* vmi)))
         (equal (nth *v-cprevi* p) (if ok (update-nth j (nth *v-hidx* vmi) (nth *v-cprevi* vmi)) (nth *v-cprevi* vmi)))
         (implies (< 18 (len vmi)) (equal (len p) (len vmi)))
         (implies (true-listp vmi) (true-listp p))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm vmg-pop-rec-fields
  (let ((p (vmg-pop-rec vmi)) (i (nfix (nth *v-ctop* vmi))))
    (and (implies (not (member k (list *v-ctop* *v-hidx*))) (equal (nth k p) (nth k vmi)))
         (equal (nth *v-ctop* p) (if (zp i) (nth *v-ctop* vmi) (1- i)))
         (equal (nth *v-hidx* p) (if (and (not (zp i)) (equal (nth (1- i) (nth *v-ckindi* vmi)) 2))
                                     (nth (1- i) (nth *v-cprevi* vmi)) (nth *v-hidx* vmi)))
         (implies (< 18 (len vmi)) (equal (len p) (len vmi)))
         (implies (true-listp vmi) (true-listp p))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm vmg-lens-push-pop
  (implies (vmg-lens vmi)
           (and (vmg-lens (vmg-push-rec kind a b c vmi)) (vmg-lens (vmg-pop-rec vmi))))
  :hints (("Goal" :in-theory (e/d (vmg-lens) (nth update-nth vmg-push-rec vmg-pop-rec)))))

(defthm vmg-tables-push-pop
  (and (equal (words-ok n (vmg-push-rec kind a b c vmi)) (words-ok n vmi))
       (equal (cls-ok n (vmg-push-rec kind a b c vmi)) (cls-ok n vmi))
       (equal (fns-ok n (vmg-push-rec kind a b c vmi)) (fns-ok n vmi))
       (equal (words-ok n (vmg-pop-rec vmi)) (words-ok n vmi))
       (equal (cls-ok n (vmg-pop-rec vmi)) (cls-ok n vmi))
       (equal (fns-ok n (vmg-pop-rec vmi)) (fns-ok n vmi)))
  :hints (("Goal" :in-theory (e/d (vmg-push-rec vmg-pop-rec) (nth update-nth words-ok cls-ok fns-ok)))))

; the records' invariant over the field lists, so a push is a list fact
(defun rok (j kinds as bs cs prevs)
  (if (zp j)
      t
    (and (bnd40p (nth (1- j) as)) (bnd40p (nth (1- j) bs)) (bnd40p (nth (1- j) cs))
         (integerp (nth (1- j) prevs)) (<= -1 (nth (1- j) prevs)) (< (nth (1- j) prevs) (1- j))
         (implies (equal (nth (1- j) kinds) 2)
                  (or (< (nth (1- j) prevs) 0) (equal (nth (nth (1- j) prevs) kinds) 2)))
         (rok (1- j) kinds as bs cs prevs))))

(defthm recs-ok-is
  (equal (recs-ok j vmi)
         (rok j (nth *v-ckindi* vmi) (nth *v-cai* vmi) (nth *v-cbi* vmi) (nth *v-cci* vmi) (nth *v-cprevi* vmi)))
  :hints (("Goal" :induct (recs-ok j vmi) :in-theory (disable nth update-nth bnd40p))))

(defthm rok-above
  (implies (and (natp i) (<= (nfix j) i))
           (and (equal (rok j (update-nth i x kinds) as bs cs prevs) (rok j kinds as bs cs prevs))
                (equal (rok j kinds (update-nth i x as) bs cs prevs) (rok j kinds as bs cs prevs))
                (equal (rok j kinds as (update-nth i x bs) cs prevs) (rok j kinds as bs cs prevs))
                (equal (rok j kinds as bs (update-nth i x cs) prevs) (rok j kinds as bs cs prevs))
                (equal (rok j kinds as bs cs (update-nth i x prevs)) (rok j kinds as bs cs prevs))))
  :hints (("Goal" :induct (rok j kinds as bs cs prevs) :in-theory (disable bnd40p))))

(defthm rok-smaller
  (implies (and (rok j kinds as bs cs prevs) (natp m) (<= m (nfix j))) (rok m kinds as bs cs prevs))
  :hints (("Goal" :induct (rok j kinds as bs cs prevs) :in-theory (disable bnd40p))))

(defthm rok-nth
  (implies (and (rok j kinds as bs cs prevs) (natp i) (< i (nfix j)))
           (and (bnd40p (nth i as)) (bnd40p (nth i bs)) (bnd40p (nth i cs))
                (integerp (nth i prevs)) (<= -1 (nth i prevs)) (< (nth i prevs) i)
                (implies (equal (nth i kinds) 2) (or (< (nth i prevs) 0) (equal (nth (nth i prevs) kinds) 2)))))
  :hints (("Goal" :induct (rok j kinds as bs cs prevs) :in-theory (disable bnd40p))))

; a record pushed on top, bounded and linked to the nearest handler,
; keeps the records good
(defthm rok-push
  (implies (and (natp j) (rok j kinds as bs cs prevs)
                (bnd40p a) (bnd40p b) (bnd40p c) (integerp h) (<= -1 h) (< h j)
                (or (< h 0) (equal (nth h kinds) 2)))
           (rok (1+ j) (update-nth j kind kinds) (update-nth j a as) (update-nth j b bs) (update-nth j c cs)
                (update-nth j h prevs)))
  :hints (("Goal" :in-theory (disable bnd40p) :expand ((rok (+ 1 j) (update-nth j kind kinds) (update-nth j a as) (update-nth j b bs)
                                                           (update-nth j c cs) (update-nth j h prevs))))))

(in-theory (disable rok))

; an unwind that leaves the machine running leaves it in bounds
(defthm vmg-unwind-bnd
  (implies (and (vmip vmi) (vmg-bnd vmi) (equal (v-status (vmg-unwind v vmi)) 0))
           (vmg-bnd (vmg-unwind v vmi)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (vmg-unwind vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w recs-ok-nth))
                  :use ((:instance recs-ok-nth (j (v-ctop vmi)) (i (v-hidx vmi)))))))

(in-theory (disable vmg-push-rec vmg-pop-rec vmg-unwind))

; recur's copy writes the stack, or overflows; nothing else
(defthm vmg-copy-down-fields
  (and (implies (not (member k (list *v-status* *v-stki*))) (equal (nth k (vmg-copy-down src dst n vmi)) (nth k vmi)))
       (equal (len (nth *v-stki* (vmg-copy-down src dst n vmi))) (len (nth *v-stki* vmi))))
  :hints (("Goal" :induct (vmg-copy-down src dst n vmi) :in-theory (disable nth update-nth))))

(defthm vmg-copy-down-tables
  (and (equal (vmg-lens (vmg-copy-down src dst n vmi)) (vmg-lens vmi))
       (equal (words-ok m (vmg-copy-down src dst n vmi)) (words-ok m vmi))
       (equal (cls-ok m (vmg-copy-down src dst n vmi)) (cls-ok m vmi))
       (equal (fns-ok m (vmg-copy-down src dst n vmi)) (fns-ok m vmi)))
  :hints (("Goal" :induct (vmg-copy-down src dst n vmi) :in-theory (disable nth update-nth words-ok cls-ok fns-ok))))

(in-theory (disable vmg-copy-down))

(defmacro def-bnd (name f k &rest uses)
  `(defthm ,name
     (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-bnd vmi) (equal (vmg-w (v-pc vmi) 0 vmi) ,k)
                   (equal (v-status (,f vmi)) 0))
              (vmg-bnd (,f vmi)))
     :hints (("Goal" :do-not-induct t
                     :in-theory (e/d (,f vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth))
                     ,@(if uses (list :use uses) nil)))))

(def-bnd vmg-push-bnd vmg-push 1)
(def-bnd vmg-load-bnd vmg-load 2)
(def-bnd vmg-add-bnd vmg-add 3)
(def-bnd vmg-lt-bnd vmg-lt 4)
(def-bnd vmg-slide-bnd vmg-slide 5)
(def-bnd vmg-jmpf-bnd vmg-jmpf 6)
(def-bnd vmg-jmp-bnd vmg-jmp 7)
(def-bnd vmg-mkclo-bnd vmg-mkclo 8)
(def-bnd vmg-capt-bnd vmg-capt 9)
(defthm vmg-callv-bnd
  (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-bnd vmi) (equal (vmg-w (v-pc vmi) 0 vmi) 10)
                (equal (v-status (vmg-callv vmi)) 0))
           (vmg-bnd (vmg-callv vmi)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (vmg-callv vmg-bnd bnd40p)
                                  (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w vmg-pick-clause))
                  :use ((:instance vmg-pick-clause
                                   (f (rt-clo-f (vmg-sreg (+ -1 (nfix (v-sp vmi))) vmi)))
                                   (m (nfix (vmg-w (v-pc vmi) 1 vmi))))
                        (:instance vmg-unwind-bnd (v :not-fn))
                        (:instance vmg-unwind-bnd (v :arity))))))
(def-bnd vmg-ret-bnd vmg-ret 11 (:instance rok-nth (j (nth *v-ctop* vmi)) (i (+ -1 (nth *v-ctop* vmi))) (kinds (nth *v-ckindi* vmi))
                                   (as (nth *v-cai* vmi)) (bs (nth *v-cbi* vmi)) (cs (nth *v-cci* vmi)) (prevs (nth *v-cprevi* vmi))))
(def-bnd vmg-recur-bnd vmg-recur 12)
(defthm vmg-prim-bnd
  (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-bnd vmi) (equal (vmg-w (v-pc vmi) 0 vmi) 13)
                (equal (v-status (vmg-prim vmi)) 0))
           (vmg-bnd (vmg-prim vmi)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (vmg-prim vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w))
                  :use ((:instance vmg-unwind-bnd
                                   (v (rt-thrown (rt-prim (vmg-poolv (vmg-w (v-pc vmi) 1 vmi) vmi)
                                                          (vmg-stk-from (- (nfix (v-sp vmi)) (nfix (vmg-w (v-pc vmi) 2 vmi)))
                                                                        (nfix (vmg-w (v-pc vmi) 2 vmi)) vmi)))))))))
(defthm vmg-throw-bnd
  (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-bnd vmi) (equal (vmg-w (v-pc vmi) 0 vmi) 14)
                (equal (v-status (vmg-throw vmi)) 0))
           (vmg-bnd (vmg-throw vmi)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (vmg-throw) (nth update-nth vmg-w))
                  :use ((:instance vmg-unwind-bnd (v (vmg-sreg (+ -1 (nfix (v-sp vmi))) vmi)))))))
(def-bnd vmg-try-bnd vmg-try 15)
(def-bnd vmg-endtry-bnd vmg-endtry 16 (:instance rok-nth (j (nth *v-ctop* vmi)) (i (+ -1 (nth *v-ctop* vmi))) (kinds (nth *v-ckindi* vmi))
                                   (as (nth *v-cai* vmi)) (bs (nth *v-cbi* vmi)) (cs (nth *v-cci* vmi)) (prevs (nth *v-cprevi* vmi))))

; A STEP KEEPS THE BOUNDS: a machine that is still running after it is
; in bounds again
(defthm vmg-step-good
  (implies (and (vmip vmi) (vmg-good vmi)) (vmg-good (vmg-step vmi)))
  :hints (("Goal" :in-theory (union-theories '(vmg-step vmg-good member-equal
                                               vmg-push-bnd vmg-load-bnd vmg-add-bnd vmg-lt-bnd vmg-slide-bnd
                                               vmg-jmpf-bnd vmg-jmp-bnd vmg-mkclo-bnd vmg-capt-bnd vmg-callv-bnd
                                               vmg-ret-bnd vmg-recur-bnd vmg-prim-bnd vmg-throw-bnd vmg-try-bnd
                                               vmg-endtry-bnd)
                                             (theory 'minimal-theory)))))

; A RUN, step after step, every step in 64 bits
(defun vmg-run (n vmi)
  (declare (xargs :stobjs vmi :guard (and (natp n) (vmg-good vmi))
                  :guard-hints (("Goal" :in-theory (disable vmg-step vmg-good)))))
  (if (zp n) vmi (let ((vmi (vmg-step vmi))) (vmg-run (1- n) vmi))))

(defthm vmg-run-is
  (equal (vmg-run n vmi) (vmi-run n vmi))
  :hints (("Goal" :induct (vmg-run n vmi)
                  :in-theory (union-theories (quote (vmg-run vmi-run vmg-step-is zp)) (theory (quote minimal-theory))))))

; clotran's VM, formally (PLAN step 30): THE COMPILER'S DEFINITIONS THE
; FORTRAN IS GENERATED FROM. vmic.lisp's compiler, word for word, with
; guards, and every integer result declared (signed-byte 64), as vmg.lisp
; is vmi.lisp's machine. Verifying the guards proves every array index in
; bounds and every intermediate inside 64 bits.
;
;   vmicg-X = vmic-X   each function is its vmic.lisp twin
;   vmicg-correct      a program vmicg-program compiles without an error
;                      or an overflow runs to what it means
;
; THE BOUNDS. A program larger than 2^39 instructions, or with 2^40
; functions or clauses, is an overflow before anything is written: the
; sizes are counted first, saturating at 2^40 (vmicg-size), so the count
; itself cannot overflow. Under that, the cursor, the stack depth and the
; environment's length each stay below 2^40 -- each grows by at most the
; size of what is left to compile -- and a clause's arity is below 2^31.

(in-package "ACL2")

(include-book "vmic-correct")
(include-book "vmg")

(defconst *b39* 549755813888)

(defmacro sb64p (x) `(signed-byte-p 64 ,x))

; ---- THE SIZES, saturating at 2^40 ---------------------------------------------------------

(defun vmicg-sat (x)
  (declare (xargs :guard (natp x)))
  (if (< x *b40*) x *b40*))

; the length of a list, saturating
(defun vmicg-len-acc (x acc)
  (declare (xargs :guard (and (natp acc) (<= acc *b40*)) :measure (acl2-count x)))
  (if (and (rt-consp x) (< (nfix acc) *b40*)) (vmicg-len-acc (rt-cdr x) (i64 (1+ (nfix acc)))) (nfix acc)))

(defun vmicg-len (x) (declare (xargs :guard t)) (vmicg-len-acc x 0))

(mutual-recursion
 (defun vmicg-size (e)
   (declare (xargs :guard t :measure (acl2-count e) :verify-guards nil))
   (let ((op (rt-car e)))
     (cond ((rt-is op :if) (vmicg-sat (i64 (+ (vmicg-size (rcadr e)) 1 (vmicg-size (rcaddr e)) 1 (vmicg-size (rcadddr e))))))
           ((rt-is op :let) (vmicg-sat (i64 (+ (vmicg-size (rcadr e)) (vmicg-size (rcaddr e)) 1))))
           ((or (rt-is op :add) (rt-is op :lt)) (vmicg-sat (i64 (+ (vmicg-size (rcadr e)) (vmicg-size (rcaddr e)) 1))))
           ((rt-is op :mkclo) (vmicg-sat (i64 (+ (vmicg-size-args (rcddr e)) 1))))
           ((rt-is op :callv) (vmicg-sat (i64 (+ (vmicg-size-args (rcddr e)) (vmicg-size (rcadr e)) 1))))
           ((rt-is op :loop) (vmicg-sat (i64 (+ (vmicg-size-args (rcadr e)) (vmicg-size (rcaddr e)) (vmicg-len (rcadr e))))))
           ((rt-is op :recur) (vmicg-sat (i64 (+ (vmicg-size-args (rt-cdr e)) 1))))
           ((rt-is op :prim) (vmicg-sat (i64 (+ (vmicg-size-args (rcddr e)) 1))))
           ((rt-is op :throw) (vmicg-sat (i64 (+ (vmicg-size (rcadr e)) 1))))
           ((rt-is op :try) (vmicg-sat (i64 (+ 1 (vmicg-size (rcadr e)) 2 (vmicg-size (rcaddr e)) 1))))
           (t 1))))
 (defun vmicg-size-args (es)
   (declare (xargs :guard t :measure (acl2-count es)))
   (if (rt-consp es) (vmicg-sat (i64 (+ (vmicg-size (rt-car es)) (vmicg-size-args (rt-cdr es))))) 0)))

(defun vmicg-size-clauses (cls)
  (declare (xargs :guard t :verify-guards nil))
  (if (rt-consp cls) (vmicg-sat (i64 (+ (vmicg-size (rcadr (rt-car cls))) 1 (vmicg-size-clauses (rt-cdr cls))))) 0))
(defun vmicg-size-defs (defs)
  (declare (xargs :guard t :verify-guards nil))
  (if (rt-consp defs) (vmicg-sat (i64 (+ (vmicg-size-clauses (rt-cdr (rt-car defs))) (vmicg-size-defs (rt-cdr defs))))) 0))
(defun vmicg-nclauses (defs)
  (declare (xargs :guard t :verify-guards nil))
  (if (rt-consp defs) (vmicg-sat (i64 (+ (vmicg-len (rt-cdr (rt-car defs))) (vmicg-nclauses (rt-cdr defs))))) 0))

; ---- EMITTING ------------------------------------------------------------------------------

(defun vmicg-put (pc op a b c k vmi)
  (declare (xargs :stobjs vmi :guard (and (natp pc) (<= pc *b40*) (sb64p op) (sb64p a) (sb64p b) (sb64p c))
                  :verify-guards nil))
  (let ((i (i64 (* 4 (nfix pc)))))
    (if (and (< (i64 (+ i 3)) (v-code-length vmi)) (< (nfix pc) (v-pool-length vmi)))
        (let* ((vmi (update-v-codei i op vmi))
               (vmi (update-v-codei (i64 (+ i 1)) a vmi))
               (vmi (update-v-codei (i64 (+ i 2)) b vmi))
               (vmi (update-v-codei (i64 (+ i 3)) c vmi)))
          (update-v-pooli (nfix pc) k vmi))
      (update-v-status 2 vmi))))

(defun vmicg-fail (vce) (declare (xargs :stobjs vce)) (update-ce-err 1 vce))

(defun vmicg-set (n x vce)
  (declare (xargs :stobjs vce :guard (and (natp n) (sb64p x)) :verify-guards nil))
  (if (< (nfix n) (ce-env-length vce)) (update-ce-envi (nfix n) x vce) (vmicg-fail vce)))

(defun vmicg-get (i vce)
  (declare (xargs :stobjs vce :guard (integerp i) :verify-guards nil))
  (if (< (nfix i) (ce-env-length vce)) (ce-envi (nfix i) vce) 0))

(defun vmicg-count (n d k vce)
  (declare (xargs :stobjs vce :measure (nfix k) :verify-guards nil
                  :guard (and (natp n) (natp d) (natp k) (<= (+ n k) *b40*) (<= (+ d k) *b40*))))
  (if (zp k) vce (let ((vce (vmicg-set n d vce))) (vmicg-count (i64 (1+ (nfix n))) (i64 (1+ (nfix d))) (1- k) vce))))

(defun vmicg-slides (pc k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil
                  :guard (and (natp pc) (natp k) (<= (+ pc k) *b40*))))
  (if (zp k) vmi (let ((vmi (vmicg-put pc 5 0 0 0 nil vmi))) (vmicg-slides (i64 (1+ (nfix pc))) (1- k) vmi))))

; ---- THE COMPILER --------------------------------------------------------------------------

(defmacro cg-room (sz)
  `(and (natp pc) (natp depth) (natp n)
        (<= (+ pc ,sz) *b40*) (<= (+ depth ,sz) *b40*) (<= (+ n ,sz) *b40*)))

(defmacro loop-ok ()
  '(and (integerp self) (<= -1 self) (<= self *b40*)
        (integerp lch) (<= -1 lch) (<= lch *b40*) (natp lcb) (<= lcb *b40*) (natp lck) (<= lck *b40*)))

(mutual-recursion
 (defun vmicg-compile (e depth n self pc lch lcb lck vmi vce)
   (declare (xargs :stobjs (vmi vce) :measure (acl2-count e) :verify-guards nil
                   :guard (and (cg-room (vmic-size e)) (loop-ok))))
   (let ((op (rt-car e)) (pc (nfix pc)) (depth (nfix depth)) (n (nfix n)))
     (cond
      ((rt-is op :const) (let ((vmi (vmicg-put pc 1 pc 0 0 (rcadr e) vmi))) (mv (i64 (1+ pc)) vmi vce)))
      ((rt-is op :local)
       (let ((i (rt-nat (rcadr e))))
         (if (or (< i 0) (<= n i))
             (let ((vce (vmicg-fail vce))) (mv (i64 (1+ pc)) vmi vce))
           (let ((vmi (vmicg-put pc 2 (vmicg-get i vce) 0 0 nil vmi))) (mv (i64 (1+ pc)) vmi vce)))))
      ((rt-is op :capt)
       (if (<= 0 self)
           (let ((i (rt-nat (rcadr e))))
             (if (< i 0)
                 (let ((vce (vmicg-fail vce))) (mv (i64 (1+ pc)) vmi vce))
               (let ((vmi (vmicg-put pc 9 self i 0 nil vmi))) (mv (i64 (1+ pc)) vmi vce))))
         (let ((vmi (vmicg-put pc 1 pc 0 0 nil vmi))) (mv (i64 (1+ pc)) vmi vce))))
      ((rt-is op :if)
       (mv-let (pa vmi vce) (vmicg-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (mv-let (pb vmi vce) (vmicg-compile (rcaddr e) depth n self (i64 (1+ pa)) lch lcb lck vmi vce)
           (mv-let (pc2 vmi vce) (vmicg-compile (rcadddr e) depth n self (i64 (1+ pb)) lch lcb lck vmi vce)
             (let* ((vmi (vmicg-put pa 6 (i64 (1+ pb)) 0 0 nil vmi))
                    (vmi (vmicg-put pb 7 pc2 0 0 nil vmi)))
               (mv pc2 vmi vce))))))
      ((rt-is op :let)
       (mv-let (pa vmi vce) (vmicg-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (let ((vce (vmicg-set n depth vce)))
           (mv-let (pb vmi vce) (vmicg-compile (rcaddr e) (i64 (1+ depth)) (i64 (1+ n)) self pa lch lcb lck vmi vce)
             (let ((vmi (vmicg-put pb 5 0 0 0 nil vmi))) (mv (i64 (1+ pb)) vmi vce))))))
      ((or (rt-is op :add) (rt-is op :lt))
       (mv-let (pa vmi vce) (vmicg-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (mv-let (pb vmi vce) (vmicg-compile (rcaddr e) (i64 (1+ depth)) n self pa -1 0 0 vmi vce)
           (let ((vmi (vmicg-put pb (if (rt-is op :add) 3 4) 0 0 0 nil vmi))) (mv (i64 (1+ pb)) vmi vce)))))
      ((rt-is op :mkclo)
       (mv-let (pa vmi vce) (vmicg-compile-args (rcddr e) depth n self pc vmi vce)
         (let ((f (rt-nat (rcadr e))))
           (if (< f 0)
               (let ((vce (vmicg-fail vce))) (mv (i64 (1+ pa)) vmi vce))
             (let ((vmi (vmicg-put pa 8 f (rt-len (rcddr e)) 0 nil vmi))) (mv (i64 (1+ pa)) vmi vce))))))
      ((rt-is op :callv)
       (let ((k (rt-len (rcddr e))))
         (mv-let (pa vmi vce) (vmicg-compile-args (rcddr e) depth n self pc vmi vce)
           (mv-let (pb vmi vce) (vmicg-compile (rcadr e) (i64 (+ depth k)) n self pa -1 0 0 vmi vce)
             (let ((vmi (vmicg-put pb 10 k 0 0 nil vmi))) (mv (i64 (1+ pb)) vmi vce))))))
      ((rt-is op :loop)
       (let ((k (rt-len (rcadr e))))
         (mv-let (head vmi vce) (vmicg-compile-args (rcadr e) depth n self pc vmi vce)
           (let ((vce (vmicg-count n depth k vce)))
             (mv-let (pb vmi vce) (vmicg-compile (rcaddr e) (i64 (+ depth k)) (i64 (+ n k)) self head head depth k vmi vce)
               (let ((vmi (vmicg-slides pb k vmi))) (mv (i64 (+ pb k)) vmi vce)))))))
      ((rt-is op :recur)
       (mv-let (pa vmi vce) (vmicg-compile-args (rt-cdr e) depth n self pc vmi vce)
         (let ((vmi (if (< lch 0) (vmicg-put pa 12 0 0 0 nil vmi) (vmicg-put pa 12 (nfix lck) (nfix lcb) (nfix lch) nil vmi))))
           (mv (i64 (1+ pa)) vmi vce))))
      ((rt-is op :prim)
       (mv-let (pa vmi vce) (vmicg-compile-args (rcddr e) depth n self pc vmi vce)
         (let ((vmi (vmicg-put pa 13 pa (rt-len (rcddr e)) 0 (rcadr e) vmi))) (mv (i64 (1+ pa)) vmi vce))))
      ((rt-is op :throw)
       (mv-let (pa vmi vce) (vmicg-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (let ((vmi (vmicg-put pa 14 0 0 0 nil vmi))) (mv (i64 (1+ pa)) vmi vce))))
      ((rt-is op :try)
       (mv-let (pb vmi vce) (vmicg-compile (rcadr e) depth n self (i64 (1+ pc)) -1 0 0 vmi vce)
         (let ((vce (vmicg-set n depth vce)))
           (mv-let (ph vmi vce) (vmicg-compile (rcaddr e) (i64 (1+ depth)) (i64 (1+ n)) self (i64 (+ pb 2)) -1 0 0 vmi vce)
             (let* ((vmi (vmicg-put pc 15 (i64 (+ pb 2)) depth 0 nil vmi))
                    (vmi (vmicg-put pb 16 0 0 0 nil vmi))
                    (vmi (vmicg-put (i64 (1+ pb)) 7 (i64 (1+ ph)) 0 0 nil vmi))
                    (vmi (vmicg-put ph 5 0 0 0 nil vmi)))
               (mv (i64 (1+ ph)) vmi vce))))))
      (t (let ((vmi (vmicg-put pc 1 pc 0 0 nil vmi))) (mv (i64 (1+ pc)) vmi vce))))))
 (defun vmicg-compile-args (es depth n self pc vmi vce)
   (declare (xargs :stobjs (vmi vce) :measure (acl2-count es)
                   :guard (and (cg-room (vmic-size-args es)) (integerp self) (<= -1 self) (<= self *b40*))))
   (if (rt-consp es)
       (mv-let (pa vmi vce) (vmicg-compile (rt-car es) depth n self pc -1 0 0 vmi vce)
         (vmicg-compile-args (rt-cdr es) (i64 (1+ (nfix depth))) n self pa vmi vce))
     (mv (nfix pc) vmi vce))))

; ---- CLAUSES, FUNCTIONS, THE PROGRAM -------------------------------------------------------

(defun vmicg-body (cl pc vmi vce)
  (declare (xargs :stobjs (vmi vce) :verify-guards nil
                  :guard (and (natp pc) (<= (+ pc 1 (vmic-size (rcadr cl))) *b39*))))
  (let* ((n (rt-nat (rt-car cl))) (rest (rt-is (rcaddr cl) :rest)))
    (if (< n 0)
        (let ((vce (vmicg-fail vce))) (mv (nfix pc) vmi vce))
      (let* ((nl (if rest (i64 (1+ n)) n)) (vce (vmicg-count 0 0 nl vce)))
        (mv-let (pa vmi vce) (vmicg-compile (rcadr cl) (i64 (1+ nl)) nl nl pc -1 0 0 vmi vce)
          (let ((vmi (vmicg-put pa 11 0 0 0 nil vmi))) (mv (i64 (1+ pa)) vmi vce)))))))

(defun vmicg-clause-entry (ci n pc rest vmi)
  (declare (xargs :stobjs vmi :guard (and (natp ci) (sb64p n) (sb64p pc) (sb64p rest)) :verify-guards nil))
  (if (and (< (nfix ci) (v-cln-length vmi)) (< (nfix ci) (v-clent-length vmi)) (< (nfix ci) (v-clrest-length vmi)))
      (let* ((vmi (update-v-clni (nfix ci) n vmi))
             (vmi (update-v-clenti (nfix ci) pc vmi)))
        (update-v-clresti (nfix ci) rest vmi))
    (update-v-status 2 vmi)))

(defun vmicg-fn-entry (f ci count vmi)
  (declare (xargs :stobjs vmi :guard (and (natp f) (sb64p ci) (sb64p count)) :verify-guards nil))
  (if (and (< (nfix f) (v-fnfirst-length vmi)) (< (nfix f) (v-fncount-length vmi)))
      (let ((vmi (update-v-fnfirsti (nfix f) ci vmi)))
        (update-v-fncounti (nfix f) count vmi))
    (update-v-status 2 vmi)))

(defun vmicg-clauses (cls ci pc vmi vce)
  (declare (xargs :stobjs (vmi vce) :measure (acl2-count cls) :verify-guards nil
                  :guard (and (natp ci) (natp pc) (<= (+ ci (rt-len cls)) *b40*)
                              (<= (+ pc (vmic-size-clauses cls)) *b39*))))
  (if (rt-consp cls)
      (let* ((cl (rt-car cls)) (n (rt-nat (rt-car cl)))
             (vmi (vmicg-clause-entry ci (nfix n) (nfix pc) (if (rt-is (rcaddr cl) :rest) 1 0) vmi)))
        (mv-let (pa vmi vce) (vmicg-body cl pc vmi vce)
          (vmicg-clauses (rt-cdr cls) (i64 (1+ (nfix ci))) pa vmi vce)))
    (mv (nfix pc) vmi vce)))

(defun vmicg-defs (defs f ci pc vmi vce)
  (declare (xargs :stobjs (vmi vce) :measure (acl2-count defs) :verify-guards nil
                  :guard (and (natp f) (natp ci) (natp pc) (<= (+ f (rt-len defs)) *b40*)
                              (<= (+ ci (vmic-nclauses defs)) *b40*) (<= (+ pc (vmic-size-defs defs)) *b39*))))
  (if (rt-consp defs)
      (let* ((d (rt-car defs)) (cls (rt-cdr d))
             (vce (if (equal (rt-nat (rt-car d)) (nfix f)) vce (vmicg-fail vce)))
             (vmi (vmicg-fn-entry f (nfix ci) (rt-len cls) vmi)))
        (mv-let (pa vmi vce) (vmicg-clauses cls ci pc vmi vce)
          (vmicg-defs (rt-cdr defs) (i64 (1+ (nfix f))) (i64 (+ (nfix ci) (rt-len cls))) pa vmi vce)))
    (mv (nfix pc) vmi vce)))

(defun vmicg-resize (n nf nc nstk nctl vmi)
  (declare (xargs :stobjs vmi :verify-guards nil
                  :guard (and (natp n) (<= n *b40*) (natp nf) (natp nc) (natp nstk) (natp nctl))))
  (let* ((vmi (resize-v-stk 0 vmi)) (vmi (resize-v-ckind 0 vmi))
         (vmi (resize-v-code (i64 (* 4 n)) vmi)) (vmi (resize-v-pool n vmi)) (vmi (resize-v-stk nstk vmi))
         (vmi (resize-v-ckind nctl vmi)) (vmi (resize-v-ca nctl vmi)) (vmi (resize-v-cb nctl vmi))
         (vmi (resize-v-cc nctl vmi)) (vmi (resize-v-cprev nctl vmi))
         (vmi (resize-v-fnfirst nf vmi)) (vmi (resize-v-fncount nf vmi))
         (vmi (resize-v-cln nc vmi)) (vmi (resize-v-clent nc vmi)))
    (resize-v-clrest nc vmi)))

; too large a program: an overflow, nothing compiled
(defmacro vmicg-too-big (n nf nc) `(or (<= *b39* ,n) (<= *b40* ,nf) (<= *b40* ,nc)))

(defun vmicg-program (e defs nstk nctl vmi vce)
  (declare (xargs :stobjs (vmi vce) :verify-guards nil
                  :guard (and (natp nstk) (<= nstk *b40*) (natp nctl) (<= nctl *b40*))))
  (let ((n (i64 (+ (vmicg-size e) 1 (vmicg-size-defs defs)))) (nf (vmicg-len defs)) (nc (vmicg-nclauses defs)))
    (if (vmicg-too-big n nf nc)
        (let ((vmi (update-v-status 2 vmi))) (mv vmi vce))
      (let* ((vmi (vmicg-resize n nf nc nstk nctl vmi))
             (vmi (update-v-status 0 vmi))
             (vce (resize-ce-env 4096 vce)) (vce (update-ce-err 0 vce)))
        (mv-let (pa vmi vce) (vmicg-compile e 0 0 -1 0 -1 0 0 vmi vce)
          (let ((vmi (vmicg-put pa 11 0 0 0 nil vmi)))
            (mv-let (pb vmi vce) (vmicg-defs defs 0 0 (i64 (1+ pa)) vmi vce)
              (declare (ignore pb))
              (let* ((vmi (update-v-pc 0 vmi)) (vmi (update-v-fb 0 vmi)) (vmi (update-v-sp 0 vmi))
                     (vmi (update-v-ctop 0 vmi)) (vmi (update-v-hidx -1 vmi)))
                (mv vmi vce)))))))))

; ==== EACH IS ITS vmic TWIN ====================================================================

(in-theory (disable nth update-nth))

(defthm vmicg-len-acc-is
  (implies (and (natp acc) (<= acc *b40*)) (equal (vmicg-len-acc x acc) (vmicg-sat (+ acc (len x)))))
  :hints (("Goal" :induct (vmicg-len-acc x acc))))
(defthm vmicg-len-is (equal (vmicg-len x) (vmicg-sat (len x))))
(in-theory (disable vmicg-len))

(defthm vmicg-sat-sum
  (implies (and (natp a) (natp b)) (equal (vmicg-sat (+ (vmicg-sat a) b)) (vmicg-sat (+ a b)))))
(defthm vmicg-sat-sum2
  (implies (and (natp a) (natp b)) (equal (vmicg-sat (+ a (vmicg-sat b))) (vmicg-sat (+ a b)))))

(defthm vmicg-size-flag
  (if (eq flg :args)
      (equal (vmicg-size-args e) (vmicg-sat (s2code-len-args e)))
    (equal (vmicg-size e) (vmicg-sat (s2code-len e))))
  :rule-classes nil
  :hints (("Goal" :induct (size-ind flg e))))

(defthm vmicg-size-is (equal (vmicg-size e) (vmicg-sat (vmic-size e)))
  :hints (("Goal" :use ((:instance vmicg-size-flag (flg :m))))))
(defthm vmicg-size-args-is (equal (vmicg-size-args es) (vmicg-sat (vmic-size-args es)))
  :hints (("Goal" :use ((:instance vmicg-size-flag (flg :args) (e es))))))
(defthm vmicg-size-clauses-is (equal (vmicg-size-clauses cls) (vmicg-sat (vmic-size-clauses cls))))
(defthm vmicg-size-defs-is (equal (vmicg-size-defs defs) (vmicg-sat (vmic-size-defs defs))))
(defthm vmicg-nclauses-is (equal (vmicg-nclauses defs) (vmicg-sat (vmic-nclauses defs))))
(in-theory (disable vmicg-size vmicg-size-args vmicg-size-clauses vmicg-size-defs vmicg-nclauses))

(defthm vmicg-put-is (equal (vmicg-put pc op a b c k vmi) (vmic-put pc op a b c k vmi)) :hints (("Goal" :in-theory (enable vmic-put))))
(defthm vmicg-fail-is (equal (vmicg-fail vce) (vce-fail vce)) :hints (("Goal" :in-theory (enable vce-fail))))
(defthm vmicg-set-is (equal (vmicg-set n x vce) (vce-set n x vce)) :hints (("Goal" :in-theory (enable vce-set vce-fail))))
(defthm vmicg-get-is (equal (vmicg-get i vce) (vce-get i vce)) :hints (("Goal" :in-theory (enable vce-get))))
(defthm vmicg-count-is (equal (vmicg-count n d k vce) (vce-count n d k vce))
  :hints (("Goal" :induct (vmicg-count n d k vce) :in-theory (enable vce-count))))
(defthm vmicg-slides-is (equal (vmicg-slides pc k vmi) (vmic-slides pc k vmi))
  :hints (("Goal" :induct (vmicg-slides pc k vmi) :in-theory (e/d (vmic-slides) (vmic-put vmicg-put)))))
(in-theory (disable vmicg-put vmicg-fail vmicg-set vmicg-get vmicg-count vmicg-slides))

(defthm vmicg-compile-flag
  (if (eq flg :args)
      (equal (vmicg-compile-args e depth n self pc vmi vce) (vmic-compile-args e depth n self pc vmi vce))
    (equal (vmicg-compile e depth n self pc lch lcb lck vmi vce) (vmic-compile e depth n self pc lch lcb lck vmi vce)))
  :rule-classes nil
  :hints (("Goal" :induct (vmic-ind flg e depth n self pc lch lcb lck vmi vce)
                  :in-theory (disable vmic-compile vmic-compile-args vmicg-compile vmicg-compile-args vmic-put vce-set vce-count vmic-slides)
                  :expand ((vmicg-compile e depth n self pc lch lcb lck vmi vce) (vmic-compile e depth n self pc lch lcb lck vmi vce)
                           (vmicg-compile-args e depth n self pc vmi vce) (vmic-compile-args e depth n self pc vmi vce)))))

(defthm vmicg-compile-is
  (equal (vmicg-compile e depth n self pc lch lcb lck vmi vce) (vmic-compile e depth n self pc lch lcb lck vmi vce))
  :hints (("Goal" :use ((:instance vmicg-compile-flag (flg :m))))))
(defthm vmicg-compile-args-is
  (equal (vmicg-compile-args es depth n self pc vmi vce) (vmic-compile-args es depth n self pc vmi vce))
  :hints (("Goal" :use ((:instance vmicg-compile-flag (flg :args) (e es))))))
(in-theory (disable vmicg-compile vmicg-compile-args))

(defthm vmicg-body-is (equal (vmicg-body cl pc vmi vce) (vmic-body cl pc vmi vce))
  :hints (("Goal" :in-theory (enable vmic-body))))
(defthm vmicg-clause-entry-is (equal (vmicg-clause-entry ci n pc rest vmi) (vmic-clause-entry ci n pc rest vmi))
  :hints (("Goal" :in-theory (enable vmic-clause-entry))))
(defthm vmicg-fn-entry-is (equal (vmicg-fn-entry f ci count vmi) (vmic-fn-entry f ci count vmi))
  :hints (("Goal" :in-theory (enable vmic-fn-entry))))
(in-theory (disable vmicg-body vmicg-clause-entry vmicg-fn-entry))

(defthm vmicg-clauses-is (equal (vmicg-clauses cls ci pc vmi vce) (vmic-clauses cls ci pc vmi vce))
  :hints (("Goal" :induct (vmicg-clauses cls ci pc vmi vce)
                  :in-theory (e/d (cl-n cl-rest) (vmic-body vmic-clause-entry))
                  :expand ((vmicg-clauses cls ci pc vmi vce) (vmic-clauses cls ci pc vmi vce)))))
(defthm vmicg-defs-is (equal (vmicg-defs defs f ci pc vmi vce) (vmic-defs defs f ci pc vmi vce))
  :hints (("Goal" :induct (vmicg-defs defs f ci pc vmi vce)
                  :in-theory (e/d (def-vce) (vmic-clauses vmic-fn-entry vce-fail))
                  :expand ((vmicg-defs defs f ci pc vmi vce) (vmic-defs defs f ci pc vmi vce)))))
(defthm vmicg-resize-is (equal (vmicg-resize n nf nc nstk nctl vmi) (vmic-resize n nf nc nstk nctl vmi))
  :hints (("Goal" :in-theory (enable vmic-resize))))
(in-theory (disable vmicg-clauses vmicg-defs vmicg-resize))

; a program small enough is vmic-program's; one too large is an overflow
(defmacro vmicg-small ()
  '(and (< (+ (vmic-size e) 1 (vmic-size-defs defs)) *b39*) (< (len defs) *b40*) (< (vmic-nclauses defs) *b40*)))

(defthm vmicg-program-is
  (implies (vmicg-small) (equal (vmicg-program e defs nstk nctl vmi vce) (vmic-program e defs nstk nctl vmi vce)))
  :hints (("Goal" :in-theory (e/d (vmic-program) (vmic-compile vmic-defs vmic-put vmic-resize)))))

(defthm vmicg-program-big
  (implies (not (vmicg-small)) (equal (nth 3 (car (vmicg-program e defs nstk nctl vmi vce))) 2))
  :hints (("Goal" :in-theory (disable vmic-compile vmic-defs vmic-put vmic-resize))))

(in-theory (disable vmicg-program))

(defmacro gprog () '(car (vmicg-program e defs nstk nctl vmi vce)))

; A PROGRAM THE GENERATED COMPILER'S DEFINITIONS COMPILE without an error
; or an overflow, run on the arrays, answers what its meaning does --
; its value, or the value of a throw nothing caught -- unless an array
; overflowed while it ran.
(defthm vmicg-correct
  (implies (and (vmip vmi) (x2defs-ok defs) (x2wf e 0 nil) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl)
                (equal (nth 3 (gprog)) 0) (not (failed (mv-nth 1 (vmicg-program e defs nstk nctl vmi vce))))
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmi-run (+ (s2clk e nil nil defs fuel) k) (gprog))) 2)))
           (equal (vcs2-answer (vmi-abs (vmi-run (+ (s2clk e nil nil defs fuel) k) (gprog))))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :cases ((vmicg-small))
                  :in-theory (union-theories (quote (vmicg-program-is vmicg-program-big)) (theory (quote minimal-theory))))
          ("Subgoal 1" :use vmic-correct)))

; ==== THE GUARDS: every index in bounds, every integer inside 64 bits ==========================

(defthm vmicg-sat-bound
  (implies (natp x) (and (natp (vmicg-sat x)) (<= (vmicg-sat x) *b40*)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (natp x) (and (<= 0 (vmicg-sat x)) (<= (vmicg-sat x) *b40*))))))
(defthm vmicg-sat-small (implies (and (natp x) (< x *b40*)) (equal (vmicg-sat x) x)))
(in-theory (disable vmicg-sat))

(verify-guards vmic-size)
(verify-guards vmic-size-clauses)
(verify-guards vmic-size-defs)
(verify-guards vmic-nclauses)
(verify-guards vmicg-size)
(verify-guards vmicg-size-clauses)
(verify-guards vmicg-size-defs)
(verify-guards vmicg-nclauses)

; what the compiler's guards need: an expression is at least one
; instruction, a list of them at least as many as it is long, the
; environment's slots 64-bit, and the cursor after e is pc plus e's size
(defthm s2code-len-pos-flag
  (if (eq flg :args) (<= (len e) (s2code-len-args e)) (< 0 (s2code-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (size-ind flg e))))
(defthm s2code-len-pos (< 0 (s2code-len e)) :rule-classes :linear
  :hints (("Goal" :use ((:instance s2code-len-pos-flag (flg :m))))))
(defthm len-le-s2code-len-args (<= (len es) (s2code-len-args es)) :rule-classes :linear
  :hints (("Goal" :use ((:instance s2code-len-pos-flag (flg :args) (e es))))))

(defthm ce-envp-nth
  (implies (and (ce-envp l) (< (nfix i) (len l))) (sb64p (nth i l)))
  :hints (("Goal" :in-theory (enable nth))))
(defthm vce-get-sb64 (implies (vcep vce) (sb64p (vce-get i vce)))
  :hints (("Goal" :in-theory (e/d (vce-get) (ce-envp-nth)) :use ((:instance ce-envp-nth (l (nth 0 vce)) (i (nfix i)))))))

(defthm vmicg-sat-lt (implies (natp x) (equal (< (vmicg-sat x) *b40*) (< x *b40*)))
  :hints (("Goal" :in-theory (enable vmicg-sat))))

(defthm vmic-compile-pc-car
  (equal (car (vmic-compile e depth n self pc lch lcb lck vmi vce)) (+ (nfix pc) (s2code-len e)))
  :hints (("Goal" :use vmic-compile-pc :in-theory (disable vmic-compile-pc vmic-compile))))
(defthm vmic-compile-args-pc-car
  (equal (car (vmic-compile-args es depth n self pc vmi vce)) (+ (nfix pc) (s2code-len-args es)))
  :hints (("Goal" :use vmic-compile-args-pc :in-theory (disable vmic-compile-args-pc vmic-compile-args))))

(verify-guards vmicg-put)
(verify-guards vmicg-set)
(verify-guards vmicg-get)
(verify-guards vmicg-count)
(verify-guards vmicg-slides)
(verify-guards vmicg-compile
  :hints (("Goal" :in-theory (disable vmic-compile vmic-compile-args vmic-put vce-set vce-count vmic-slides vce-get vce-fail)
                  :expand ((s2code-len e) (s2code-len-args e)))))

; the cursor after a clause, and after a function's clauses, at most
; their size past where they began
(defthm vmic-body-pc-bound
  (<= (car (vmic-body cl pc vmi vce)) (+ (nfix pc) 1 (s2code-len (cadr cl)))) :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (vmic-body) (vmic-compile vmic-put vce-count vce-fail)))))

(defthm vmic-clauses-pc-bound
  (<= (car (vmic-clauses cls ci pc vmi vce)) (+ (nfix pc) (vmic-size-clauses cls))) :rule-classes :linear
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses vmic-body)
                  :expand ((vmic-clauses cls ci pc vmi vce) (vmic-size-clauses cls)))))

(verify-guards vmicg-body
  :hints (("Goal" :in-theory (disable vmic-compile vmic-put vce-count vce-fail))))
(verify-guards vmicg-clause-entry)
(verify-guards vmicg-fn-entry)
(verify-guards vmicg-clauses
  :hints (("Goal" :in-theory (disable vmic-body vmic-clause-entry vmic-clauses)
                  :expand ((vmic-size-clauses cls)))))
(verify-guards vmicg-defs
  :hints (("Goal" :in-theory (disable vmic-clauses vmic-fn-entry vce-fail vmic-defs)
                  :expand ((vmic-size-defs defs) (vmic-nclauses defs)))))
(verify-guards vmicg-resize)
(verify-guards vmicg-program
  :hints (("Goal" :in-theory (e/d (vmicg-sat) (vmic-compile vmic-put vmic-defs vmic-resize)))))

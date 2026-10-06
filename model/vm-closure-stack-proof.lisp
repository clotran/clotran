; clotran's VM, formally (PLAN step 30). The closure call on the ONE-
; STACK machine (model/vm-closure.lisp's vcs-step): the same theorem as
; the register machine's (vm-closure-correct.lisp), so the call protocol
; is proved for the machine clotran would run if it turns to a stack VM.
;
; THE PROPERTY: an expression's code, run for its clock from a state
; whose stack top is the frame's base plus depth, pushes exactly its
; value -- the top one higher, that slot holding the value, nothing
; below the old top changed, the frame and the return records as they
; were. A call's arguments are pushed where the callee's frame begins,
; its closure above them, and the callee's answer comes back to where
; the first argument was: one value pushed, as any expression.
;
; This book: the definitions and each kind of expression but the call;
; vm-closure-stack-correct.lisp the call and the theorem.

(in-package "ACL2")

(include-book "vm-closure-proof")

; ---- THE CLOCK ----------------------------------------------------------------
;
; as the register machine's, and a let's :slide

(mutual-recursion
 (defun sclk (e env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (c+ (sclk (cadr e) env caps defs fuel)
              (c+ 1 (if (truthy (val (mc (cadr e) env caps defs fuel)))
                        (c+ (sclk (caddr e) env caps defs fuel) 1)
                      (sclk (cadddr e) env caps defs fuel)))))
     (:let (c+ (sclk (cadr e) env caps defs fuel)
               (c+ (sclk (caddr e) (append env (list (val (mc (cadr e) env caps defs fuel)))) caps defs fuel)
                   1)))
     ((:add :lt) (c+ (sclk (cadr e) env caps defs fuel) (c+ (sclk (caddr e) env caps defs fuel) 1)))
     (:mkclo (c+ (sclk-args (cddr e) env caps defs fuel) 1))
     (:callv (if (zp fuel)
                 (c+ (sclk-args (cddr e) env caps defs fuel) (c+ (sclk (cadr e) env caps defs fuel) 1))
               (c+ (sclk-args (cddr e) env caps defs fuel)
                   (c+ (sclk (cadr e) env caps defs fuel)
                       (c+ 1 (c+ (sclk (cadr (cv-def)) (cv-vs) (clo-caps (val (cv-rf))) defs (1- fuel))
                                 1))))))
     (otherwise 1)))
 (defun sclk-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (c+ (sclk (car es) env caps defs fuel) (sclk-args (cdr es) env caps defs fuel)))))

(mutual-recursion
 (defun scode-len (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ (scode-len (cadr e)) 1 (scode-len (caddr e)) 1 (scode-len (cadddr e))))
     (:let (+ (scode-len (cadr e)) (scode-len (caddr e)) 1))
     ((:add :lt) (+ (scode-len (cadr e)) (scode-len (caddr e)) 1))
     (:mkclo (+ (scode-len-args (cddr e)) 1))
     (:callv (+ (scode-len-args (cddr e)) (scode-len (cadr e)) 1))
     (otherwise 1)))
 (defun scode-len-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (scode-len (car es)) (scode-len-args (cdr es))))))

; ---- WHAT THE THEOREM ASSUMES -----------------------------------------------

(defun-sk sfns-ok (prog defs)
  (forall name
          (implies (consp (assoc-equal name defs))
                   (let ((ent (cdr (assoc-equal name (cdr prog))))
                         (def (cdr (assoc-equal name defs))))
                     (and (consp ent) (natp (car ent))
                          (equal (nfix (cadr ent)) (nfix (car def)))
                          (ccode-at (car prog) (car ent) (vcs-body def (car ent))))))))
(in-theory (disable sfns-ok))

; a state: pc, frame base, stack top, the stack, the return records
(defun sstatep (s)
  (and (true-listp s) (equal (len s) 5) (natp (car s)) (natp (cadr s)) (natp (caddr s))))

(defmacro s-ctl (s) `(car (cddddr ,s)))

; THE PROPERTY
(defun sgood (e depth cenv self caps s env defs fuel prog)
  (implies (and (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
                (ccode-at (car prog) (car s) (vcs-compile e depth cenv self (car s)))
                (cwf e (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
                (cself-ok self caps (cadddr s) (cadr s) depth)
                (cdefs-ok defs) (sfns-ok prog defs))
           (let ((r (mc e env caps defs fuel)) (s2 (vcs-run prog s (sclk e env caps defs fuel))))
             (implies (valp r)
                      (and (sstatep s2)
                           (equal (car s2) (+ (car s) (scode-len e)))
                           (equal (cadr s2) (cadr s))
                           (equal (caddr s2) (1+ (caddr s)))
                           (equal (s-ctl s2) (s-ctl s))
                           (cagree (cadddr s2) (update-nth (caddr s) (val r) (cadddr s)) (1+ (caddr s))))))))

; a call's arguments: pushed, one after another
(defun sgood-args (es depth cenv self caps s env defs fuel prog)
  (implies (and (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
                (ccode-at (car prog) (car s) (vcs-compile-args es depth cenv self (car s)))
                (cwf-args es (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
                (cself-ok self caps (cadddr s) (cadr s) depth)
                (cdefs-ok defs) (sfns-ok prog defs))
           (let ((r (mc-args es env caps defs fuel)) (s2 (vcs-run prog s (sclk-args es env caps defs fuel))))
             (implies (valp r)
                      (and (sstatep s2)
                           (equal (car s2) (+ (car s) (scode-len-args es)))
                           (equal (cadr s2) (cadr s))
                           (equal (caddr s2) (+ (caddr s) (len es)))
                           (equal (s-ctl s2) (s-ctl s))
                           (cagree (cadddr s2) (cadddr s) (caddr s))
                           (cvals-at (caddr s) (val r) (cadddr s2)))))))

; ---- the machine's runs -------------------------------------------------------

(in-theory (disable vcs-step))

(defthm vcs-run-plus
  (implies (and (natp a) (natp b))
           (equal (vcs-run prog s (+ a b)) (vcs-run prog (vcs-run prog s a) b)))
  :hints (("Goal" :induct (vcs-run prog s a))))

(defthm vcs-run-c+
  (equal (vcs-run prog s (c+ a b)) (vcs-run prog (vcs-run prog s (nfix a)) (nfix b)))
  :hints (("Goal" :in-theory (enable c+) :use ((:instance vcs-run-plus (a (nfix a)) (b (nfix b)))))))

(defthm vcs-run-0 (equal (vcs-run prog s 0) s))
(defthm vcs-run-1 (equal (vcs-run prog s 1) (vcs-step prog s)))
(in-theory (disable vcs-run))

(defun svc-ind (flg e depth cenv self pc)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (svc-ind :m (car e) depth cenv self pc)
              (svc-ind :args (cdr e) (1+ depth) cenv self
                       (+ pc (len (vcs-compile (car e) depth cenv self pc))))))
    (case (car e)
      (:if (let* ((cc (vcs-compile (cadr e) depth cenv self pc))
                  (pc1 (+ pc (len cc) 1))
                  (tc (vcs-compile (caddr e) depth cenv self pc1))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (svc-ind :m (cadr e) depth cenv self pc)
                   (svc-ind :m (caddr e) depth cenv self pc1)
                   (svc-ind :m (cadddr e) depth cenv self pc2))))
      (:let (let ((ic (vcs-compile (cadr e) depth cenv self pc)))
              (list (svc-ind :m (cadr e) depth cenv self pc)
                    (svc-ind :m (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (len ic))))))
      ((:add :lt) (let ((ac (vcs-compile (cadr e) depth cenv self pc)))
                    (list (svc-ind :m (cadr e) depth cenv self pc)
                          (svc-ind :m (caddr e) (1+ depth) cenv self (+ pc (len ac))))))
      (:mkclo (svc-ind :args (cddr e) depth cenv self pc))
      (:callv (let ((ac (vcs-compile-args (cddr e) depth cenv self pc)))
                (list (svc-ind :args (cddr e) depth cenv self pc)
                      (svc-ind :m (cadr e) (+ depth (len (cddr e))) cenv self (+ pc (len ac))))))
      (otherwise (list depth cenv self pc)))))

(defthm len-vcs-compile-flag
  (if (eq flg :args)
      (equal (len (vcs-compile-args e depth cenv self pc)) (scode-len-args e))
    (equal (len (vcs-compile e depth cenv self pc)) (scode-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (svc-ind flg e depth cenv self pc))))

(defthm len-vcs-compile
  (equal (len (vcs-compile e depth cenv self pc)) (scode-len e))
  :hints (("Goal" :use ((:instance len-vcs-compile-flag (flg :m))))))

(defthm len-vcs-compile-args
  (equal (len (vcs-compile-args es depth cenv self pc)) (scode-len-args es))
  :hints (("Goal" :use ((:instance len-vcs-compile-flag (flg :args) (e es))))))

; ---- the machine, a step at a time ---------------------------------------

(in-theory (enable vcs-step))

(defmacro sins (s) `(nth (car ,s) (car prog)))

(defthm sstep-push
  (implies (and (sstatep s) (equal (car (sins s)) :push))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1+ (caddr s))
                        (update-nth (caddr s) (cadr (sins s)) (cadddr s)) (s-ctl s)))))
(defthm sstep-load
  (implies (and (sstatep s) (equal (car (sins s)) :load))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1+ (caddr s))
                        (update-nth (caddr s) (nth (+ (cadr s) (nfix (cadr (sins s)))) (cadddr s)) (cadddr s))
                        (s-ctl s)))))
(defthm sstep-add
  (implies (and (sstatep s) (equal (car (sins s)) :add) (<= 2 (caddr s)))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1- (caddr s))
                        (update-nth (- (caddr s) 2)
                                    (+ (fix (nth (- (caddr s) 2) (cadddr s))) (fix (nth (1- (caddr s)) (cadddr s))))
                                    (cadddr s))
                        (s-ctl s)))))
(defthm sstep-lt
  (implies (and (sstatep s) (equal (car (sins s)) :lt) (<= 2 (caddr s)))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1- (caddr s))
                        (update-nth (- (caddr s) 2)
                                    (bool (< (rfix (nth (- (caddr s) 2) (cadddr s))) (rfix (nth (1- (caddr s)) (cadddr s)))))
                                    (cadddr s))
                        (s-ctl s)))))
(defthm sstep-add-k
  (implies (and (sstatep s) (equal (car (sins s)) :add) (equal (caddr s) (+ 2 k)) (natp k))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1+ k)
                        (update-nth k (+ (fix (nth k (cadddr s))) (fix (nth (1+ k) (cadddr s)))) (cadddr s))
                        (s-ctl s))))
  :hints (("Goal" :in-theory (disable sstep-add) :use sstep-add)))
(defthm sstep-lt-k
  (implies (and (sstatep s) (equal (car (sins s)) :lt) (equal (caddr s) (+ 2 k)) (natp k))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1+ k)
                        (update-nth k (bool (< (rfix (nth k (cadddr s))) (rfix (nth (1+ k) (cadddr s))))) (cadddr s))
                        (s-ctl s))))
  :hints (("Goal" :in-theory (disable sstep-lt) :use sstep-lt)))

(defthm sstep-slide
  (implies (and (sstatep s) (equal (car (sins s)) :slide) (<= 2 (caddr s)))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1- (caddr s))
                        (update-nth (- (caddr s) 2) (nth (1- (caddr s)) (cadddr s)) (cadddr s))
                        (s-ctl s)))))
(defthm sstep-jmpf
  (implies (and (sstatep s) (equal (car (sins s)) :jmpf) (<= 1 (caddr s)))
           (equal (vcs-step prog s)
                  (if (truthy (nth (1- (caddr s)) (cadddr s)))
                      (list (1+ (car s)) (cadr s) (1- (caddr s)) (cadddr s) (s-ctl s))
                    (list (nfix (cadr (sins s))) (cadr s) (1- (caddr s)) (cadddr s) (s-ctl s))))))
(defthm sstep-jmp
  (implies (and (sstatep s) (equal (car (sins s)) :jmp))
           (equal (vcs-step prog s)
                  (list (nfix (cadr (sins s))) (cadr s) (caddr s) (cadddr s) (s-ctl s)))))
(defthm sstep-mkclo
  (implies (and (sstatep s) (equal (car (sins s)) :mkclo) (<= (nfix (caddr (sins s))) (caddr s)))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1+ (- (caddr s) (nfix (caddr (sins s)))))
                        (update-nth (- (caddr s) (nfix (caddr (sins s))))
                                    (clo (cadr (sins s))
                                         (stk-from (- (caddr s) (nfix (caddr (sins s)))) (nfix (caddr (sins s))) (cadddr s)))
                                    (cadddr s))
                        (s-ctl s)))))
(defthm sstep-capt
  (implies (and (sstatep s) (equal (car (sins s)) :capt))
           (equal (vcs-step prog s)
                  (list (1+ (car s)) (cadr s) (1+ (caddr s))
                        (update-nth (caddr s)
                                    (nth (nfix (caddr (sins s)))
                                         (clo-caps (nth (+ (cadr s) (nfix (cadr (sins s)))) (cadddr s))))
                                    (cadddr s))
                        (s-ctl s)))))
(defthm sstep-ret
  (implies (and (sstatep s) (equal (car (sins s)) :ret) (<= 1 (caddr s)) (consp (s-ctl s)))
           (equal (vcs-step prog s)
                  (list (nfix (car (car (s-ctl s)))) (nfix (cadr (car (s-ctl s)))) (1+ (cadr s))
                        (update-nth (cadr s) (nth (1- (caddr s)) (cadddr s)) (cadddr s))
                        (cdr (s-ctl s))))))
(defthm sstep-halt
  (implies (and (sstatep s) (equal (car (sins s)) :ret) (<= 1 (caddr s)) (not (consp (s-ctl s))))
           (equal (vcs-step prog s)
                  (list (car s) (cadr s) 1 (update-nth 0 (nth (1- (caddr s)) (cadddr s)) (cadddr s)) (s-ctl s)))))
(in-theory (disable vcs-step))

(defthm sstatep-fc
  (implies (sstatep s) (and (natp (car s)) (natp (cadr s)) (natp (caddr s))))
  :rule-classes :forward-chaining)
(defthm sstatep-list
  (equal (sstatep (list pc fb sp stk ctl)) (and (natp pc) (natp fb) (natp sp))))
(in-theory (disable sstatep))

; ---- values pushed --------------------------------------------------------

(defthm stk-from-vals
  (implies (and (natp a) (cvals-at a vs stk) (true-listp vs))
           (equal (stk-from a (len vs) stk) vs))
  :hints (("Goal" :induct (rf-ind a vs) :expand ((stk-from a (len vs) stk)))))

; ---- each kind of expression, given its parts --------------------------------

(defthm sgood-const
  (implies (equal (car e) :const) (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm sgood-local
  (implies (equal (car e) :local) (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm sgood-capt
  (implies (equal (car e) :capt) (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth) :cases ((natp self)))))

(defthm sgood-other
  (implies (not (member-equal (car e) '(:const :local :capt :if :let :add :lt :mkclo :callv)))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm update-nth-twice
  (equal (update-nth n x (update-nth n y l)) (update-nth n x l)))

; two pushes, then a write at the first: below it, the stack as it was
(defthm stwo-pushes
  (implies (and (cagree s2 (update-nth (1+ sp) vb s1) (+ 2 sp)) (cagree s1 (update-nth sp va s0) (1+ sp))
                (natp sp))
           (and (cagree (update-nth sp x s2) (update-nth sp x s0) (1+ sp))
                (equal (nth sp s2) va) (equal (nth (1+ sp) s2) vb)))
  :hints (("Goal" :in-theory (disable nth update-nth cagree-past-write cagree-trans cagree-same-write cagree-nth)
                  :use ((:instance cagree-past-write (a s2) (b s1) (g (1+ sp)) (w vb) (h (+ 2 sp)) (f (1+ sp)))
                        (:instance cagree-trans (a s2) (b s1) (c (update-nth sp va s0)) (h (1+ sp)))
                        (:instance cagree-same-write (a s2) (b (update-nth sp va s0)) (d sp) (v x) (h (1+ sp)))
                        (:instance cagree-nth (a s2) (b (update-nth (1+ sp) vb s1)) (h (+ 2 sp)) (r (1+ sp)))
                        (:instance cagree-nth (a s2) (b s1) (h (1+ sp)) (r sp))
                        (:instance cagree-nth (a s1) (b (update-nth sp va s0)) (h (1+ sp)) (r sp))))))

; what a binary operation that is a value says, as rewrites, so the
; meaning need not be opened inside every term
(defthm mc-binop-val
  (implies (and (member-equal (car e) '(:add :lt)) (valp (mc e env caps defs fuel)))
           (and (equal (car (mc (cadr e) env caps defs fuel)) :val)
                (equal (car (mc (caddr e) env caps defs fuel)) :val)
                (equal (cdr (mc e env caps defs fuel))
                       (if (eq (car e) :add)
                           (+ (fix (cdr (mc (cadr e) env caps defs fuel))) (fix (cdr (mc (caddr e) env caps defs fuel))))
                         (bool (< (rfix (cdr (mc (cadr e) env caps defs fuel)))
                                  (rfix (cdr (mc (caddr e) env caps defs fuel)))))))))
  :hints (("Goal" :expand ((mc e env caps defs fuel)))))

(defthm sgood-add
  (implies (and (equal (car e) :add)
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (caddr e) (1+ depth) cenv self caps (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                       env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth sstep-add sstep-lt mc cself-ok)
                  :expand ((vcs-compile e depth cenv self (car s)))
                  :use ((:instance stwo-pushes (sp (caddr s))
                                   (s0 (cadddr s))
                                   (s1 (cadddr (vcs-run prog s (sclk (cadr e) env caps defs fuel))))
                                   (s2 (cadddr (vcs-run prog (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                                                        (sclk (caddr e) env caps defs fuel))))
                                   (va (cdr (mc (cadr e) env caps defs fuel)))
                                   (vb (cdr (mc (caddr e) env caps defs fuel)))
                                   (x (+ (fix (cdr (mc (cadr e) env caps defs fuel))) (fix (cdr (mc (caddr e) env caps defs fuel))))))))))

(defthm sgood-lt
  (implies (and (equal (car e) :lt)
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (caddr e) (1+ depth) cenv self caps (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                       env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth sstep-add sstep-lt mc cself-ok)
                  :expand ((vcs-compile e depth cenv self (car s)))
                  :use ((:instance stwo-pushes (sp (caddr s))
                                   (s0 (cadddr s))
                                   (s1 (cadddr (vcs-run prog s (sclk (cadr e) env caps defs fuel))))
                                   (s2 (cadddr (vcs-run prog (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                                                        (sclk (caddr e) env caps defs fuel))))
                                   (va (cdr (mc (cadr e) env caps defs fuel)))
                                   (vb (cdr (mc (caddr e) env caps defs fuel)))
                                   (x (bool (< (rfix (cdr (mc (cadr e) env caps defs fuel))) (rfix (cdr (mc (caddr e) env caps defs fuel)))))))))))

(defthm sgood-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (caddr e) (1+ depth) cenv self caps (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                       env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable sgood sgood-add sgood-lt)
                  :use (sgood-add sgood-lt))))

(defthm sgood-let
  (implies (and (equal (car e) :let)
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (caddr e) (1+ depth) (append cenv (list depth)) self caps
                       (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                       (append env (list (cdr (mc (cadr e) env caps defs fuel)))) defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vcs-compile e depth cenv self (car s))))))

; a value pushed, popped, and another pushed in its place: below the
; top as before, at it the second
(defthm sif-combine
  (implies (and (cagree s3 (update-nth sp vb s1) (1+ sp)) (cagree s1 (update-nth sp va s0) (1+ sp))
                (natp sp))
           (cagree s3 (update-nth sp vb s0) (1+ sp)))
  :hints (("Goal" :in-theory (disable cagree-trans cagree-same-write nth update-nth)
                  :use ((:instance cagree-same-write (a s1) (b (update-nth sp va s0)) (d sp) (v vb) (h (1+ sp)))
                        (:instance cagree-trans (a s3) (b (update-nth sp vb s1))
                                   (c (update-nth sp vb (update-nth sp va s0))) (h (1+ sp)))))))

; what an if says, as rewrites, so the meaning need not be opened
(defthm mc-if-cond
  (implies (and (equal (car e) :if) (not (valp (mc (cadr e) env caps defs fuel))))
           (not (equal (car (mc e env caps defs fuel)) :val)))
  :hints (("Goal" :expand ((mc e env caps defs fuel)))))

; an if whose condition is not a value is not a value
(defthm sgood-if-noval
  (implies (and (equal (car e) :if) (not (valp (mc (cadr e) env caps defs fuel))))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable mc))))
(defthm mc-if-true
  (implies (and (equal (car e) :if) (valp (mc (cadr e) env caps defs fuel))
                (truthy (cdr (mc (cadr e) env caps defs fuel))))
           (equal (mc e env caps defs fuel) (mc (caddr e) env caps defs fuel)))
  :hints (("Goal" :expand ((mc e env caps defs fuel)))))
(defthm mc-if-false
  (implies (and (equal (car e) :if) (valp (mc (cadr e) env caps defs fuel))
                (not (truthy (cdr (mc (cadr e) env caps defs fuel)))))
           (equal (mc e env caps defs fuel) (mc (cadddr e) env caps defs fuel)))
  :hints (("Goal" :expand ((mc e env caps defs fuel)))))

(defthm sgood-if-true
  (implies (and (equal (car e) :if) (valp (mc (cadr e) env caps defs fuel))
                (truthy (cdr (mc (cadr e) env caps defs fuel)))
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (caddr e) depth cenv self caps (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))
                       env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth mc cself-ok)
                  :expand ((vcs-compile e depth cenv self (car s)))
                  :use ((:instance sif-combine (sp (caddr s)) (s0 (cadddr s))
                                   (s1 (cadddr (vcs-run prog s (sclk (cadr e) env caps defs fuel))))
                                   (s3 (cadddr (vcs-run prog (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))
                                                        (sclk (caddr e) env caps defs fuel))))
                                   (va (cdr (mc (cadr e) env caps defs fuel)))
                                   (vb (cdr (mc (caddr e) env caps defs fuel))))))))

(defthm sgood-if-false
  (implies (and (equal (car e) :if) (valp (mc (cadr e) env caps defs fuel))
                (not (truthy (cdr (mc (cadr e) env caps defs fuel))))
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (cadddr e) depth cenv self caps (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))
                       env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth mc cself-ok)
                  :expand ((vcs-compile e depth cenv self (car s)))
                  :use ((:instance sif-combine (sp (caddr s)) (s0 (cadddr s))
                                   (s1 (cadddr (vcs-run prog s (sclk (cadr e) env caps defs fuel))))
                                   (s3 (cadddr (vcs-run prog (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))
                                                        (sclk (cadddr e) env caps defs fuel))))
                                   (va (cdr (mc (cadr e) env caps defs fuel)))
                                   (vb (cdr (mc (cadddr e) env caps defs fuel))))))))

(defthm sgood-args-nil
  (implies (atom es) (sgood-args es depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm sgood-args-cons
  (implies (and (consp es)
                (sgood (car es) depth cenv self caps s env defs fuel prog)
                (sgood-args (cdr es) (1+ depth) cenv self caps (vcs-run prog s (sclk (car es) env caps defs fuel))
                            env defs fuel prog))
           (sgood-args es depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth mc cself-ok)
                  :expand ((vcs-compile-args es depth cenv self (car s))
                           (mc-args es env caps defs fuel)
                           (cvals-at (caddr s) (val (mc-args es env caps defs fuel))
                                     (cadddr (vcs-run prog s (sclk-args es env caps defs fuel))))))))

; two stacks that agree below n, each written the same value at n,
; agree below n+1
(defthm cagree-write-at
  (implies (and (cagree a b n) (natp n))
           (cagree (update-nth n x a) (update-nth n x b) (1+ n)))
  :hints (("Goal" :expand ((cagree (update-nth n x a) (update-nth n x b) (1+ n)))
                  :use ((:instance cagree-necc (r (cagree-witness (update-nth n x a) (update-nth n x b) (1+ n))) (h n))))))

(defthm sgood-mkclo
  (implies (and (equal (car e) :mkclo)
                (sgood-args (cddr e) depth cenv self caps s env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth sgood-args)
                  :expand ((vcs-compile e depth cenv self (car s)) (mc e env caps defs fuel)
                           (sclk e env caps defs fuel) (cwf e (len env)))
                  :use ((:instance (:definition sgood-args) (es (cddr e)))
                        (:instance mc-args-val-shape (es (cddr e)))
                        (:instance cagree-write-at (n (caddr s))
                                   (a (cadddr (vcs-run prog s (sclk-args (cddr e) env caps defs fuel))))
                                   (b (cadddr s))
                                   (x (clo (cadr e) (cdr (mc-args (cddr e) env caps defs fuel)))))
                        (:instance stk-from-vals (a (caddr s))
                                   (vs (cdr (mc-args (cddr e) env caps defs fuel)))
                                   (stk (cadddr (vcs-run prog s (sclk-args (cddr e) env caps defs fuel)))))))))

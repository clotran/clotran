; clotran's VM, formally (PLAN step 30): the extended stack machine
; (model/vmx.lisp) against the extended meaning.
;
; THE PROPERTY has two outcomes now. An expression whose meaning is a
; value pushes it, as vm-closure-stack-proof.lisp's sgood says. An
; expression in a loop body's tail whose meaning is (:recur . vs)
; arrives at the loop's head with vs in the loop's slots b .. b+k-1, the
; stack top just above them, and nothing below the loop's first slot
; changed -- so the next iteration starts where the first did. Every
; stack fact and every old instruction's step comes from the books on
; vcs-step: the extended machine IS vcs-step but for :recur.

(in-package "ACL2")

(include-book "vmx")
(include-book "vm-closure-stack-correct")

; ---- THE CLOCK ----------------------------------------------------------------
;
; sclk's, and: a branch, a let's body or a loop body that recurs takes
; no step after itself -- the recur jumped -- and a loop is its inits,
; its iterations, and k slides.

(defmacro xv-rf () '(mx (cadr e) env caps defs fuel))
(defmacro xv-def () '(cdr (assoc-equal (clo-f (val (xv-rf))) defs)))
(defmacro xv-vs () '(val (mx-args (cddr e) env caps defs fuel)))

(defun recurp (r) (eq (car r) :recur))

(mutual-recursion
 (defun sxclk (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (c+ (sxclk (cadr e) env caps defs fuel)
              (c+ 1 (if (truthy (val (mx (cadr e) env caps defs fuel)))
                        (c+ (sxclk (caddr e) env caps defs fuel)
                            (if (recurp (mx (caddr e) env caps defs fuel)) 0 1))
                      (sxclk (cadddr e) env caps defs fuel)))))
     (:let (let ((env2 (append env (list (val (mx (cadr e) env caps defs fuel))))))
             (c+ (sxclk (cadr e) env caps defs fuel)
                 (c+ (sxclk (caddr e) env2 caps defs fuel)
                     (if (recurp (mx (caddr e) env2 caps defs fuel)) 0 1)))))
     ((:add :lt) (c+ (sxclk (cadr e) env caps defs fuel) (c+ (sxclk (caddr e) env caps defs fuel) 1)))
     (:mkclo (c+ (sxclk-args (cddr e) env caps defs fuel) 1))
     (:callv (if (zp fuel)
                 (c+ (sxclk-args (cddr e) env caps defs fuel) (c+ (sxclk (cadr e) env caps defs fuel) 1))
               (c+ (sxclk-args (cddr e) env caps defs fuel)
                   (c+ (sxclk (cadr e) env caps defs fuel)
                       (c+ 1 (c+ (sxclk (cadr (xv-def)) (xv-vs) (clo-caps (val (xv-rf))) defs (1- fuel))
                                 1))))))
     (:loop (c+ (sxclk-args (cadr e) env caps defs fuel)
                (c+ (sxclk-loop e env (val (mx-args (cadr e) env caps defs fuel)) caps defs fuel)
                    (len (cadr e)))))
     (:recur (c+ (sxclk-args (cdr e) env caps defs fuel) 1))
     (otherwise 1)))
 (defun sxclk-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1))))
   (if (atom es)
       0
     (c+ (sxclk (car es) env caps defs fuel) (sxclk-args (cdr es) env caps defs fuel))))
 (defun sxclk-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0))))
   (cond ((not (consp e)) 0)
         ((and (recurp (mx (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
          (c+ (sxclk (caddr e) (append base vs) caps defs fuel)
              (sxclk-loop e base (cdr (mx (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))
         (t (sxclk (caddr e) (append base vs) caps defs fuel)))))

(mutual-recursion
 (defun sxcode-len (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1 (sxcode-len (cadddr e))))
     (:let (+ (sxcode-len (cadr e)) (sxcode-len (caddr e)) 1))
     ((:add :lt) (+ (sxcode-len (cadr e)) (sxcode-len (caddr e)) 1))
     (:mkclo (+ (sxcode-len-args (cddr e)) 1))
     (:callv (+ (sxcode-len-args (cddr e)) (sxcode-len (cadr e)) 1))
     (:loop (+ (sxcode-len-args (cadr e)) (sxcode-len (caddr e)) (len (cadr e))))
     (:recur (+ (sxcode-len-args (cdr e)) 1))
     (otherwise 1)))
 (defun sxcode-len-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (sxcode-len (car es)) (sxcode-len-args (cdr es))))))

(defthm len-slides (equal (len (slides k)) (nfix k)))

(defun sxc-ind (flg e depth cenv self pc lc)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (sxc-ind :m (car e) depth cenv self pc nil)
              (sxc-ind :args (cdr e) (1+ depth) cenv self
                       (+ pc (len (vcsx-compile (car e) depth cenv self pc nil))) nil)))
    (case (car e)
      (:if (let* ((cc (vcsx-compile (cadr e) depth cenv self pc nil))
                  (pc1 (+ pc (len cc) 1))
                  (tc (vcsx-compile (caddr e) depth cenv self pc1 lc))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (sxc-ind :m (cadr e) depth cenv self pc nil)
                   (sxc-ind :m (caddr e) depth cenv self pc1 lc)
                   (sxc-ind :m (cadddr e) depth cenv self pc2 lc))))
      (:let (let ((ic (vcsx-compile (cadr e) depth cenv self pc nil)))
              (list (sxc-ind :m (cadr e) depth cenv self pc nil)
                    (sxc-ind :m (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (len ic)) lc))))
      ((:add :lt) (let ((ac (vcsx-compile (cadr e) depth cenv self pc nil)))
                    (list (sxc-ind :m (cadr e) depth cenv self pc nil)
                          (sxc-ind :m (caddr e) (1+ depth) cenv self (+ pc (len ac)) nil))))
      (:mkclo (sxc-ind :args (cddr e) depth cenv self pc nil))
      (:callv (let ((ac (vcsx-compile-args (cddr e) depth cenv self pc)))
                (list (sxc-ind :args (cddr e) depth cenv self pc nil)
                      (sxc-ind :m (cadr e) (+ depth (len (cddr e))) cenv self (+ pc (len ac)) nil))))
      (:loop (let* ((k (len (cadr e)))
                    (ic (vcsx-compile-args (cadr e) depth cenv self pc))
                    (head (+ pc (len ic))))
               (list (sxc-ind :args (cadr e) depth cenv self pc nil)
                     (sxc-ind :m (caddr e) (+ depth k) (append cenv (count-from depth (+ depth k))) self head
                              (list head depth k)))))
      (:recur (sxc-ind :args (cdr e) depth cenv self pc nil))
      (otherwise (list depth cenv self pc lc)))))

(defthm len-vcsx-compile-flag
  (if (eq flg :args)
      (equal (len (vcsx-compile-args e depth cenv self pc)) (sxcode-len-args e))
    (equal (len (vcsx-compile e depth cenv self pc lc)) (sxcode-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (sxc-ind flg e depth cenv self pc lc))))

(defthm len-vcsx-compile
  (equal (len (vcsx-compile e depth cenv self pc lc)) (sxcode-len e))
  :hints (("Goal" :use ((:instance len-vcsx-compile-flag (flg :m))))))

(defthm len-vcsx-compile-args
  (equal (len (vcsx-compile-args es depth cenv self pc)) (sxcode-len-args es))
  :hints (("Goal" :use ((:instance len-vcsx-compile-flag (flg :args) (e es) (lc nil))))))

; ---- THE MACHINE: vcs-step but for :recur --------------------------------------

(defthm vcsx-step-old
  (implies (not (equal (car (nth (car s) (car prog))) :recur))
           (equal (vcsx-step prog s) (vcs-step prog s))))

(defthm sxstep-recur
  (implies (and (sstatep s) (equal (car (sins s)) :recur)
                (<= (+ (cadr s) (nfix (caddr (sins s))) (nfix (cadr (sins s)))) (caddr s)))
           (equal (vcsx-step prog s)
                  (list (nfix (cadddr (sins s))) (cadr s) (+ (cadr s) (nfix (caddr (sins s))) (nfix (cadr (sins s))))
                        (copy-down (- (caddr s) (nfix (cadr (sins s)))) (+ (cadr s) (nfix (caddr (sins s))))
                                   (nfix (cadr (sins s))) (cadddr s))
                        (s-ctl s))))
  :hints (("Goal" :in-theory (enable sstatep))))

(in-theory (disable vcsx-step))

(defthm vcsx-run-plus
  (implies (and (natp a) (natp b))
           (equal (vcsx-run prog s (+ a b)) (vcsx-run prog (vcsx-run prog s a) b)))
  :hints (("Goal" :induct (vcsx-run prog s a))))

(defthm vcsx-run-c+
  (equal (vcsx-run prog s (c+ a b)) (vcsx-run prog (vcsx-run prog s (nfix a)) (nfix b)))
  :hints (("Goal" :in-theory (enable c+) :use ((:instance vcsx-run-plus (a (nfix a)) (b (nfix b)))))))

(defthm vcsx-run-0 (equal (vcsx-run prog s 0) s))
(defthm vcsx-run-1 (equal (vcsx-run prog s 1) (vcsx-step prog s)))
(in-theory (disable vcsx-run))

; ---- the recur's copy ---------------------------------------------------------

(defthm copy-down-below
  (implies (and (natp r) (natp dst) (< r dst))
           (equal (nth r (copy-down src dst k stk)) (nth r stk))))

(defthm cagree-copy-down
  (implies (natp dst) (cagree (copy-down src dst k stk) stk dst))
  :hints (("Goal" :in-theory (enable cagree))))

(defthm cvals-at-update-below
  (implies (and (natp a) (natp d) (< d a))
           (equal (cvals-at a vs (update-nth d x stk)) (cvals-at a vs stk))))

(defun cd-ind (src dst vs stk)
  (if (atom vs) (list src dst stk) (cd-ind (1+ src) (1+ dst) (cdr vs) (update-nth dst (nth src stk) stk))))

(defthm copy-down-vals-len
  (implies (and (natp src) (natp dst) (<= dst src) (cvals-at src vs stk))
           (cvals-at dst vs (copy-down src dst (len vs) stk)))
  :hints (("Goal" :induct (cd-ind src dst vs stk)
                  :expand ((copy-down src dst (len vs) stk) (cvals-at src vs stk)
                           (cvals-at dst vs (copy-down (+ 1 src) (+ 1 dst) (len (cdr vs)) (update-nth dst (nth src stk) stk)))))))

(defthm copy-down-vals
  (implies (and (natp src) (natp dst) (<= dst src) (cvals-at src vs stk) (equal k (len vs)))
           (cvals-at dst vs (copy-down src dst k stk))))

; ---- WHAT THE THEOREM ASSUMES -----------------------------------------------

(defun-sk sxfns-ok (prog defs)
  (forall name
          (implies (consp (assoc-equal name defs))
                   (let ((ent (cdr (assoc-equal name (cdr prog))))
                         (def (cdr (assoc-equal name defs))))
                     (and (consp ent) (natp (car ent))
                          (equal (nfix (cadr ent)) (nfix (car def)))
                          (ccode-at (car prog) (car ent) (vcsx-body def (car ent))))))))
(in-theory (disable sxfns-ok))

; the loop a recur goes round: its head, its first slot, its arity
(defun lck (lc) (if (consp lc) (nfix (caddr lc)) nil))
(defun lc-ok (lc depth)
  (or (not (consp lc))
      (and (natp (car lc)) (natp (cadr lc)) (natp (caddr lc)) (<= (+ (cadr lc) (caddr lc)) (nfix depth)))))

; THE PROPERTY: a value pushed, or a recur at its loop's head -- its
; hypotheses and its two outcomes named apart, so a case can be proved
; one outcome at a time
(defun sx-hyps (e depth cenv self caps s env defs prog lc)
  (and (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
       (ccode-at (car prog) (car s) (vcsx-compile e depth cenv self (car s) lc))
       (xwf e (len env) (lck lc)) (lc-ok lc depth)
       (cenv-ok cenv env (cadddr s) (cadr s) depth)
       (cself-ok self caps (cadddr s) (cadr s) depth)
       (xdefs-ok defs) (sxfns-ok prog defs)))

(defun sx-val (e s r s2)
  (implies (valp r)
           (and (sstatep s2)
                (equal (car s2) (+ (car s) (sxcode-len e)))
                (equal (cadr s2) (cadr s))
                (equal (caddr s2) (1+ (caddr s)))
                (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (update-nth (caddr s) (val r) (cadddr s)) (1+ (caddr s))))))

(defun sx-rec (s r s2 lc)
  (implies (recurp r)
           (and (consp lc)
                (sstatep s2)
                (equal (car s2) (car lc))
                (equal (cadr s2) (cadr s))
                (equal (caddr s2) (+ (cadr s) (cadr lc) (caddr lc)))
                (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (cadddr s) (+ (cadr s) (cadr lc)))
                (cvals-at (+ (cadr s) (cadr lc)) (cdr r) (cadddr s2))
                (equal (len (cdr r)) (caddr lc)))))

(defun sxgood (e depth cenv self caps s env defs fuel prog lc)
  (implies (sx-hyps e depth cenv self caps s env defs prog lc)
           (and (sx-val e s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel)))
                (sx-rec s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel)) lc))))

; arguments: pushed one after another
(defun sxgood-args (es depth cenv self caps s env defs fuel prog)
  (implies (and (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
                (ccode-at (car prog) (car s) (vcsx-compile-args es depth cenv self (car s)))
                (xwf-args es (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
                (cself-ok self caps (cadddr s) (cadr s) depth)
                (xdefs-ok defs) (sxfns-ok prog defs))
           (let ((r (mx-args es env caps defs fuel)) (s2 (vcsx-run prog s (sxclk-args es env caps defs fuel))))
             (implies (valp r)
                      (and (sstatep s2)
                           (equal (car s2) (+ (car s) (sxcode-len-args es)))
                           (equal (cadr s2) (cadr s))
                           (equal (caddr s2) (+ (caddr s) (len es)))
                           (equal (s-ctl s2) (s-ctl s))
                           (cagree (cadddr s2) (cadddr s) (caddr s))
                           (cvals-at (caddr s) (val r) (cadddr s2)))))))

; ---- NEVER A RECUR outside a loop body's tail -------------------------------------
;
; a fact of the meaning alone: what is not in tail position, an argument,
; a function's body, a loop as a whole, answers anything but a recur

(defun mxl-ind (e base vs caps defs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (consp e)) (zp fuel))
      (list e base vs caps defs)
    (mxl-ind e base (cdr (mx (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))

(defthm mx-loop-not-recur
  (not (equal (car (mx-loop e base vs caps defs fuel)) :recur))
  :hints (("Goal" :induct (mxl-ind e base vs caps defs fuel) :in-theory (disable mx)
                  :expand ((mx-loop e base vs caps defs fuel)))))

(defun mx-ind (flg e env caps defs fuel)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (mx-ind :m (car e) env caps defs fuel) (mx-ind :args (cdr e) env caps defs fuel)))
    (case (car e)
      (:if (list (mx-ind :m (cadr e) env caps defs fuel) (mx-ind :m (caddr e) env caps defs fuel)
                 (mx-ind :m (cadddr e) env caps defs fuel)))
      (:let (list (mx-ind :m (cadr e) env caps defs fuel)
                  (mx-ind :m (caddr e) (append env (list (val (mx (cadr e) env caps defs fuel)))) caps defs fuel)))
      ((:add :lt) (list (mx-ind :m (cadr e) env caps defs fuel) (mx-ind :m (caddr e) env caps defs fuel)))
      (:mkclo (mx-ind :args (cddr e) env caps defs fuel))
      (:callv (list (mx-ind :args (cddr e) env caps defs fuel) (mx-ind :m (cadr e) env caps defs fuel)
                    (if (zp fuel) nil
                      (mx-ind :m (cadr (xv-def)) (xv-vs) (clo-caps (val (xv-rf))) defs (1- fuel)))))
      ((:loop :recur) (mx-ind :args (if (eq (car e) :loop) (cadr e) (cdr e)) env caps defs fuel))
      (otherwise nil))))

(defthm xdefs-ok-lookup
  (implies (and (xdefs-ok ds) (consp (assoc-equal name ds)))
           (and (natp (car (cdr (assoc-equal name ds))))
                (xwf (cadr (cdr (assoc-equal name ds))) (car (cdr (assoc-equal name ds))) nil))))

; the body a call runs, well formed at the arguments it was given
(defthm xdefs-ok-body-wf
  (implies (and (xdefs-ok ds) (consp (cdr (assoc-equal name ds)))
                (equal (len vs) (nfix (cadr (assoc-equal name ds)))))
           (xwf (caddr (assoc-equal name ds)) (len vs) nil))
  :hints (("Goal" :use xdefs-ok-lookup :in-theory (disable xdefs-ok-lookup))))

(defthm xdefs-ok-arity
  (implies (and (xdefs-ok ds) (consp (cdr (assoc-equal name ds))))
           (and (integerp (cadr (assoc-equal name ds))) (<= 0 (cadr (assoc-equal name ds)))))
  :hints (("Goal" :use xdefs-ok-lookup :in-theory (disable xdefs-ok-lookup))))

(defthm mx-args-not-recur-shape
  (or (valp (mx-args es env caps defs fuel)) (not (valp (mx-args es env caps defs fuel))))
  :rule-classes nil)

(defthm mx-not-recur-flag
  (if (eq flg :args)
      (implies (and (xwf-args e (len env)) (xdefs-ok defs)) (not (equal (car (mx-args e env caps defs fuel)) :recur)))
    (implies (and (xwf e (len env) nil) (xdefs-ok defs)) (not (equal (car (mx e env caps defs fuel)) :recur))))
  :rule-classes nil
  :hints (("Goal" :induct (mx-ind flg e env caps defs fuel)
                  :expand ((mx e env caps defs fuel) (mx-args e env caps defs fuel) (xwf e (len env) nil)))))

(defthm mx-not-recur
  (implies (and (xwf e (len env) nil) (xdefs-ok defs)) (not (equal (car (mx e env caps defs fuel)) :recur)))
  :hints (("Goal" :use ((:instance mx-not-recur-flag (flg :m))))))

(defthm mx-args-not-recur
  (implies (and (xwf-args es (len env)) (xdefs-ok defs)) (not (equal (car (mx-args es env caps defs fuel)) :recur)))
  :hints (("Goal" :use ((:instance mx-not-recur-flag (flg :args) (e es))))))

; ---- the leaves ---------------------------------------------------------------

(defthm sxgood-const
  (implies (equal (car e) :const) (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm sxgood-local
  (implies (equal (car e) :local) (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :use ((:instance cenv-ok-local-cenv (i (cadr e)) (regs (cadddr s)) (fb (cadr s)) (f depth))))))

(defthm sxgood-capt
  (implies (equal (car e) :capt) (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth) :cases ((natp self)))))

(defthm sxgood-other
  (implies (not (member-equal (car e) '(:const :local :capt :if :let :add :lt :mkclo :callv :loop :recur)))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth))))

; ---- the meaning's facts, as rewrites ---------------------------------------------

(defthm mx-binop-val
  (implies (and (member-equal (car e) '(:add :lt)) (valp (mx e env caps defs fuel)))
           (and (equal (car (mx (cadr e) env caps defs fuel)) :val)
                (equal (car (mx (caddr e) env caps defs fuel)) :val)
                (equal (cdr (mx e env caps defs fuel))
                       (if (eq (car e) :add)
                           (+ (fix (cdr (mx (cadr e) env caps defs fuel))) (fix (cdr (mx (caddr e) env caps defs fuel))))
                         (bool (< (rfix (cdr (mx (cadr e) env caps defs fuel)))
                                  (rfix (cdr (mx (caddr e) env caps defs fuel)))))))))
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

; what is not in a loop body's tail is never a recur, given its parts' wf
(defthm xwf-binop-parts
  (implies (and (member-equal (car e) '(:add :lt)) (xwf e n k))
           (and (xwf (cadr e) n nil) (xwf (caddr e) n nil))))

(defthm mx-binop-not-recur
  (implies (and (member-equal (car e) '(:add :lt)) (xwf e (len env) k) (xdefs-ok defs))
           (not (equal (car (mx e env caps defs fuel)) :recur)))
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

; an operator's code and well-formedness do not depend on the loop it is in
(defthm vcsx-compile-binop-lc
  (implies (and (syntaxp (not (equal lc ''nil))) (member-equal (car e) '(:add :lt :mkclo :callv)))
           (equal (vcsx-compile e depth cenv self pc lc) (vcsx-compile e depth cenv self pc nil)))
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc lc) (vcsx-compile e depth cenv self pc nil)))))

(defthm xwf-op-k
  (implies (and (syntaxp (not (equal k ''nil))) (member-equal (car e) '(:add :lt :mkclo :callv)))
           (equal (xwf e n k) (xwf e n nil)))
  :hints (("Goal" :expand ((xwf e n k) (xwf e n nil)))))

(defthm sx-hyps-op-nil
  (implies (and (member-equal (car e) '(:add :lt :mkclo :callv)) (sx-hyps e depth cenv self caps s env defs prog lc))
           (sx-hyps e depth cenv self caps s env defs prog nil))
  :hints (("Goal" :in-theory (disable vcsx-compile xwf))))

; ---- a binary operation, in stages ------------------------------------------------

(defthm binop-hyps-a
  (implies (and (member-equal (car e) '(:add :lt)) (sx-hyps e depth cenv self caps s env defs prog nil))
           (sx-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self (car s) nil) (xwf e (len env) nil)))))

(defthm binop-hyps-b
  (implies (and (member-equal (car e) '(:add :lt)) (sx-hyps e depth cenv self caps s env defs prog nil)
                (sx-val (cadr e) s ra s1) (valp ra))
           (sx-hyps (caddr e) (1+ depth) cenv self caps s1 env defs prog nil))
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self (car s) nil) (xwf e (len env) nil))
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ra)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ra)) (h (1+ (caddr s))) (k (1+ depth)))))))

; the operation's own step, after both operands, over plain states
(defmacro binop-states ()
  '(and (sstatep s) (sstatep s1) (sstatep s2) (natp sp) (equal (caddr s) sp)
        (equal (cadr s1) (cadr s)) (equal (caddr s1) (1+ sp)) (equal (s-ctl s1) (s-ctl s))
        (cagree (cadddr s1) (update-nth sp va (cadddr s)) (1+ sp))
        (equal (cadr s2) (cadr s)) (equal (caddr s2) (+ 2 sp)) (equal (s-ctl s2) (s-ctl s))
        (cagree (cadddr s2) (update-nth (1+ sp) vb (cadddr s1)) (+ 2 sp))))

(defthm add-step-abs
  (implies (and (binop-states) (equal (nth (car s2) (car prog)) (list :add)))
           (let ((s3 (vcsx-step prog s2)))
             (and (sstatep s3) (equal (car s3) (1+ (car s2))) (equal (cadr s3) (cadr s)) (equal (caddr s3) (1+ sp))
                  (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth sp (+ (fix va) (fix vb)) (cadddr s)) (1+ sp)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth sstep-add sstep-lt)
                  :use ((:instance sstep-add-k (s s2) (k sp))
                        (:instance stwo-pushes (s0 (cadddr s)) (s1 (cadddr s1)) (s2 (cadddr s2)) (x (+ (fix va) (fix vb))))))))

(defthm lt-step-abs
  (implies (and (binop-states) (equal (nth (car s2) (car prog)) (list :lt)))
           (let ((s3 (vcsx-step prog s2)))
             (and (sstatep s3) (equal (car s3) (1+ (car s2))) (equal (cadr s3) (cadr s)) (equal (caddr s3) (1+ sp))
                  (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth sp (bool (< (rfix va) (rfix vb))) (cadddr s)) (1+ sp)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth sstep-add sstep-lt)
                  :use ((:instance sstep-lt-k (s s2) (k sp))
                        (:instance stwo-pushes (s0 (cadddr s)) (s1 (cadddr s1)) (s2 (cadddr s2)) (x (bool (< (rfix va) (rfix vb)))))))))

; where an operation's code lies
(defthm binop-code
  (implies (and (member-equal (car e) '(:add :lt)) (ccode-at code pc (vcsx-compile e depth cenv self pc nil)) (natp pc))
           (and (equal (nth (+ pc (sxcode-len (cadr e)) (sxcode-len (caddr e))) code) (list (car e)))
                (equal (sxcode-len e) (+ (sxcode-len (cadr e)) (sxcode-len (caddr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc nil) (sxcode-len e)))))

(defthm natp-c+x (natp (c+ a b)) :rule-classes :type-prescription :hints (("Goal" :in-theory (enable c+))))

(defthm binop-clock
  (implies (member-equal (car e) '(:add :lt))
           (equal (vcsx-run prog s (sxclk e env caps defs fuel))
                  (vcsx-step prog (vcsx-run prog (vcsx-run prog s (sxclk (cadr e) env caps defs fuel))
                                            (sxclk (caddr e) env caps defs fuel)))))
  :hints (("Goal" :expand ((sxclk e env caps defs fuel)) :in-theory (disable c+))))

(defthm binop-rec
  (implies (and (member-equal (car e) '(:add :lt)) (sx-hyps e depth cenv self caps s env defs prog lc))
           (sx-rec s (mx e env caps defs fuel) s2 lc))
  :hints (("Goal" :in-theory (disable mx) :use ((:instance mx-binop-not-recur (k (lck lc)))))))

(defmacro bx-s1 () '(vcsx-run prog s (sxclk (cadr e) env caps defs fuel)))
(defmacro bx-s2 () '(vcsx-run prog (bx-s1) (sxclk (caddr e) env caps defs fuel)))
(defmacro bx-ra () '(mx (cadr e) env caps defs fuel))
(defmacro bx-rb () '(mx (caddr e) env caps defs fuel))

(defthm sxgood-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
                (sxgood (caddr e) (1+ depth) cenv self caps (bx-s1) env defs fuel prog nil))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood sx-val sx-hyps-op-nil binop-hyps-a binop-hyps-b binop-clock binop-rec
                                               mx-binop-val member-equal sstatep-fc valp val lck lc-ok)
                                             (set-difference-theories (theory 'ground-zero) '(update-nth nth)))
                  :do-not-induct t
                  :use ((:instance binop-code (code (car prog)) (pc (car s)))
                        (:instance binop-hyps-b (ra (bx-ra)) (s1 (bx-s1)))
                        (:instance (:definition sx-hyps) (lc nil))
                        (:instance add-step-abs (sp (caddr s)) (s1 (bx-s1)) (s2 (bx-s2)) (va (cdr (bx-ra))) (vb (cdr (bx-rb))))
                        (:instance lt-step-abs (sp (caddr s)) (s1 (bx-s1)) (s2 (bx-s2)) (va (cdr (bx-ra))) (vb (cdr (bx-rb))))))))

; ---- a part's outcome, extracted with nothing opened -------------------------------

(defthm sxgood-gives-val
  (implies (and (sxgood e depth cenv self caps s env defs fuel prog lc) (sx-hyps e depth cenv self caps s env defs prog lc))
           (sx-val e s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel))))
  :rule-classes nil)

(defthm sxgood-gives-rec
  (implies (and (sxgood e depth cenv self caps s env defs fuel prog lc) (sx-hyps e depth cenv self caps s env defs prog lc))
           (sx-rec s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel)) lc))
  :rule-classes nil)

(defthm sx-val-open
  (implies (and (sx-val e s r s2) (valp r))
           (and (sstatep s2) (equal (car s2) (+ (car s) (sxcode-len e))) (equal (cadr s2) (cadr s))
                (equal (caddr s2) (1+ (caddr s))) (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (update-nth (caddr s) (cdr r) (cadddr s)) (1+ (caddr s)))))
  :rule-classes nil)

(defthm sx-rec-open
  (implies (and (sx-rec s r s2 lc) (recurp r))
           (and (consp lc) (sstatep s2) (equal (car s2) (car lc)) (equal (cadr s2) (cadr s))
                (equal (caddr s2) (+ (cadr s) (cadr lc) (caddr lc))) (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (cadddr s) (+ (cadr s) (cadr lc)))
                (cvals-at (+ (cadr s) (cadr lc)) (cdr r) (cadddr s2))
                (equal (len (cdr r)) (caddr lc))))
  :rule-classes nil)

; agreeing below h through a push at or above h
(defthm cagree-through-push
  (implies (and (cagree a b h) (cagree b (update-nth sp v c) (1+ sp)) (natp h) (natp sp) (<= h sp))
           (cagree a c h))
  :hints (("Goal" :in-theory (disable cagree-past-write cagree-trans cagree-smaller)
                  :use ((:instance cagree-past-write (a b) (b c) (g sp) (w v) (h (1+ sp)) (f h))
                        (:instance cagree-trans (a a) (b b) (c c))))))

; ---- a let, in stages ---------------------------------------------------------------

(defthm mx-let
  (implies (equal (car e) :let)
           (equal (mx e env caps defs fuel)
                  (if (valp (mx (cadr e) env caps defs fuel))
                      (mx (caddr e) (append env (list (val (mx (cadr e) env caps defs fuel)))) caps defs fuel)
                    (mx (cadr e) env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

(defthm let-code
  (implies (and (equal (car e) :let) (ccode-at code pc (vcsx-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcsx-compile (cadr e) depth cenv self pc nil))
                (ccode-at code (+ pc (sxcode-len (cadr e)))
                          (vcsx-compile (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (sxcode-len (cadr e))) lc))
                (equal (nth (+ pc (sxcode-len (cadr e)) (sxcode-len (caddr e))) code) (list :slide))
                (equal (sxcode-len e) (+ (sxcode-len (cadr e)) (sxcode-len (caddr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc lc) (sxcode-len e)))))

(defmacro lx-ri () '(mx (cadr e) env caps defs fuel))
(defmacro lx-env () '(append env (list (cdr (mx (cadr e) env caps defs fuel)))))
(defmacro lx-rb () '(mx (caddr e) (lx-env) caps defs fuel))
(defmacro lx-s1 () '(vcsx-run prog s (sxclk (cadr e) env caps defs fuel)))
(defmacro lx-s2 () '(vcsx-run prog (lx-s1) (sxclk (caddr e) (lx-env) caps defs fuel)))

(defthm let-clock
  (implies (equal (car e) :let)
           (equal (vcsx-run prog s (sxclk e env caps defs fuel))
                  (if (recurp (lx-rb)) (lx-s2) (vcsx-step prog (lx-s2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((sxclk e env caps defs fuel)) :in-theory (disable c+ recurp))))

(defthm let-hyps-init
  (implies (and (equal (car e) :let) (sx-hyps e depth cenv self caps s env defs prog lc))
           (sx-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :use ((:instance let-code (code (car prog)) (pc (car s)))) :do-not-induct t
                  :expand ((xwf e (len env) (lck lc))))))

(defthm cenv-ok-one
  (equal (cenv-ok (list i) (list v) regs fb f)
         (and (natp i) (< i (nfix f)) (equal (nth (+ (nfix fb) i) regs) v)))
  :hints (("Goal" :expand ((cenv-ok (list i) (list v) regs fb f)))))

(defthm let-hyps-body
  (implies (and (equal (car e) :let) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sx-val (cadr e) s ri s1) (valp ri))
           (sx-hyps (caddr e) (1+ depth) (append cenv (list depth)) self caps s1 (append env (list (cdr ri))) defs prog lc))
  :hints (("Goal" :expand ((xwf e (len env) (lck lc))) :do-not-induct t
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance let-code (code (car prog)) (pc (car s)))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ri)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ri)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cagree-nth (a (cadddr s1)) (b (update-nth (caddr s) (cdr ri) (cadddr s)))
                                   (h (caddr s1)) (r (caddr s)))))))

; the let's slide, over plain states: its local drops from under the value
(defthm slide-step-abs
  (implies (and (sstatep s) (sstatep s1) (sstatep s2) (natp sp) (equal (caddr s) sp)
                (equal (cadr s1) (cadr s)) (equal (caddr s1) (1+ sp)) (equal (s-ctl s1) (s-ctl s))
                (cagree (cadddr s1) (update-nth sp va (cadddr s)) (1+ sp))
                (equal (cadr s2) (cadr s)) (equal (caddr s2) (+ 2 sp)) (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (update-nth (1+ sp) vb (cadddr s1)) (+ 2 sp))
                (equal (nth (car s2) (car prog)) (list :slide)))
           (let ((s3 (vcsx-step prog s2)))
             (and (sstatep s3) (equal (car s3) (1+ (car s2))) (equal (cadr s3) (cadr s)) (equal (caddr s3) (1+ sp))
                  (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth sp vb (cadddr s)) (1+ sp)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :use ((:instance stwo-pushes (s0 (cadddr s)) (s1 (cadddr s1)) (s2 (cadddr s2)) (x vb))))))

(defthm natp-sxcode-len (natp (sxcode-len e)) :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance len-vcsx-compile (depth 0) (cenv nil) (self nil) (pc 0) (lc nil))) :in-theory (disable len-vcsx-compile))))
(defthm natp-sxcode-len-args (natp (sxcode-len-args es)) :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance len-vcsx-compile-args (depth 0) (cenv nil) (self nil) (pc 0))) :in-theory (disable len-vcsx-compile-args))))

(defmacro let-thy ()
  '(union-theories '(valp val recurp lc-ok lck natp-c+x sstatep-fc sstatep-list natp-sxcode-len natp-sxcode-len-args
                     vcsx-step-old sstep-jmpf sstep-jmp)
                   (set-difference-theories (theory 'ground-zero) '(update-nth nth))))

; the init's outcome: a value, from its own property
(defthm let-init-val
  (implies (and (equal (car e) :let) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil) (valp (lx-ri)))
           (sx-val (cadr e) s (lx-ri) (lx-s1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance let-hyps-init) (:instance sxgood-gives-val (e (cadr e)) (lc nil))))))

; PATH 1: the body a value, then the slide
(defthm let-path-val
  (implies (and (equal (car e) :let) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
                (sxgood (caddr e) (1+ depth) (append cenv (list depth)) self caps (lx-s1) (lx-env) defs fuel prog lc)
                (valp (lx-ri)) (valp (lx-rb)))
           (let ((s3 (vcsx-step prog (lx-s2))))
             (and (sstatep s3) (equal (car s3) (+ (car s) (sxcode-len e))) (equal (cadr s3) (cadr s))
                  (equal (caddr s3) (1+ (caddr s))) (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth (caddr s) (cdr (lx-rb)) (cadddr s)) (1+ (caddr s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance (:definition sx-hyps))
                        (:instance let-init-val)
                        (:instance sx-val-open (e (cadr e)) (r (lx-ri)) (s2 (lx-s1)))
                        (:instance let-hyps-body (ri (lx-ri)) (s1 (lx-s1)))
                        (:instance sxgood-gives-val (e (caddr e)) (depth (1+ depth)) (cenv (append cenv (list depth)))
                                   (s (lx-s1)) (env (lx-env)))
                        (:instance sx-val-open (e (caddr e)) (s (lx-s1)) (r (lx-rb)) (s2 (lx-s2)))
                        (:instance let-code (code (car prog)) (pc (car s)))
                        (:instance slide-step-abs (sp (caddr s)) (s1 (lx-s1)) (s2 (lx-s2)) (va (cdr (lx-ri))) (vb (cdr (lx-rb))))))))

; PATH 2: the body a recur, nothing after it
(defthm let-path-rec
  (implies (and (equal (car e) :let) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
                (sxgood (caddr e) (1+ depth) (append cenv (list depth)) self caps (lx-s1) (lx-env) defs fuel prog lc)
                (valp (lx-ri)) (recurp (lx-rb)))
           (sx-rec s (lx-rb) (lx-s2) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sx-rec) (let-thy)) :do-not-induct t
                  :use ((:instance (:definition sx-hyps))
                        (:instance let-init-val)
                        (:instance sx-val-open (e (cadr e)) (r (lx-ri)) (s2 (lx-s1)))
                        (:instance let-hyps-body (ri (lx-ri)) (s1 (lx-s1)))
                        (:instance sxgood-gives-rec (e (caddr e)) (depth (1+ depth)) (cenv (append cenv (list depth)))
                                   (s (lx-s1)) (env (lx-env)))
                        (:instance sx-rec-open (s (lx-s1)) (r (lx-rb)) (s2 (lx-s2)))
                        (:instance cagree-through-push (a (cadddr (lx-s2))) (b (cadddr (lx-s1))) (c (cadddr s))
                                   (h (+ (cadr s) (cadr lc))) (sp (caddr s)) (v (cdr (lx-ri))))))))

; THE LET: its paths, joined
(defthm sxgood-let
  (implies (and (equal (car e) :let)
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
                (sxgood (caddr e) (1+ depth) (append cenv (list depth)) self caps (lx-s1) (lx-env) defs fuel prog lc))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood sx-val sx-rec) (let-thy)) :do-not-induct t
                  :use ((:instance let-path-val) (:instance let-path-rec)
                        (:instance let-clock) (:instance mx-let)
                        (:instance (:definition sx-hyps))
                        (:instance mx-not-recur (e (cadr e)))
                        (:instance let-hyps-init)
                        (:instance (:definition sx-hyps) (e (cadr e)) (lc nil))))))

; ---- an if, in stages ---------------------------------------------------------------

(defmacro ix-pc1 () '(+ pc (sxcode-len (cadr e)) 1))
(defmacro ix-pc2 () '(+ pc (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1))

(defthm if-code
  (implies (and (equal (car e) :if) (ccode-at code pc (vcsx-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcsx-compile (cadr e) depth cenv self pc nil))
                (equal (nth (+ pc (sxcode-len (cadr e))) code) (list :jmpf (ix-pc2)))
                (ccode-at code (ix-pc1) (vcsx-compile (caddr e) depth cenv self (ix-pc1) lc))
                (equal (nth (+ (ix-pc1) (sxcode-len (caddr e))) code) (list :jmp (+ (ix-pc2) (sxcode-len (cadddr e)))))
                (ccode-at code (ix-pc2) (vcsx-compile (cadddr e) depth cenv self (ix-pc2) lc))
                (equal (sxcode-len e) (+ (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1 (sxcode-len (cadddr e))))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc lc) (sxcode-len e)))))

(defthm mx-if
  (implies (equal (car e) :if)
           (equal (mx e env caps defs fuel)
                  (cond ((not (valp (mx (cadr e) env caps defs fuel))) (mx (cadr e) env caps defs fuel))
                        ((truthy (val (mx (cadr e) env caps defs fuel))) (mx (caddr e) env caps defs fuel))
                        (t (mx (cadddr e) env caps defs fuel)))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

(defmacro ix-rc () '(mx (cadr e) env caps defs fuel))
(defmacro ix-rt () '(mx (caddr e) env caps defs fuel))
(defmacro ix-re () '(mx (cadddr e) env caps defs fuel))
(defmacro ix-s1 () '(vcsx-run prog s (sxclk (cadr e) env caps defs fuel)))
(defmacro ix-s1b () '(vcsx-step prog (ix-s1)))
(defmacro ix-st () '(vcsx-run prog (ix-s1b) (sxclk (caddr e) env caps defs fuel)))
(defmacro ix-se () '(vcsx-run prog (ix-s1b) (sxclk (cadddr e) env caps defs fuel)))

(defthm if-clock
  (implies (equal (car e) :if)
           (equal (vcsx-run prog s (sxclk e env caps defs fuel))
                  (if (truthy (val (ix-rc)))
                      (if (recurp (ix-rt)) (ix-st) (vcsx-step prog (ix-st)))
                    (ix-se))))
  :rule-classes nil
  :hints (("Goal" :expand ((sxclk e env caps defs fuel)) :in-theory (disable c+ recurp))))

; the test's jump, over plain states: popped, and on to the branch
(defthm jmpf-step-abs
  (implies (and (sstatep s1) (equal (caddr s1) (1+ sp)) (natp sp)
                (equal (nth (car s1) (car prog)) (list :jmpf tgt)) (natp tgt))
           (equal (vcsx-step prog s1)
                  (if (truthy (nth sp (cadddr s1)))
                      (list (1+ (car s1)) (cadr s1) sp (cadddr s1) (s-ctl s1))
                    (list tgt (cadr s1) sp (cadddr s1) (s-ctl s1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth) :use ((:instance sstep-jmpf (s s1))))))

(defthm jmp-step-abs
  (implies (and (sstatep s2) (equal (nth (car s2) (car prog)) (list :jmp tgt)) (natp tgt))
           (equal (vcsx-step prog s2) (list tgt (cadr s2) (caddr s2) (cadddr s2) (s-ctl s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth) :use ((:instance sstep-jmp (s s2))))))

(defthm if-hyps-test
  (implies (and (equal (car e) :if) (sx-hyps e depth cenv self caps s env defs prog lc))
           (sx-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :do-not-induct t :expand ((xwf e (len env) (lck lc)))
                  :use ((:instance if-code (code (car prog)) (pc (car s)))))))

; a branch starts where the test's value was, the stack below as it was
(defthm if-hyps-branch
  (implies (and (equal (car e) :if) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sstatep s1b) (equal (cadr s1b) (cadr s)) (equal (caddr s1b) (caddr s))
                (cagree (cadddr s1b) (update-nth (caddr s) v (cadddr s)) (1+ (caddr s)))
                (equal (car s1b) (if th (+ (car s) (sxcode-len (cadr e)) 1)
                                   (+ (car s) (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1))))
           (sx-hyps (if th (caddr e) (cadddr e)) depth cenv self caps s1b env defs prog lc))
  :hints (("Goal" :do-not-induct t :expand ((xwf e (len env) (lck lc)))
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance if-code (code (car prog)) (pc (car s)))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1b)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (h (1+ (caddr s))) (k depth))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1b)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (h (1+ (caddr s))) (k depth))))))

; the test's outcome and the jump after it
(defthm if-test-facts
  (implies (and (equal (car e) :if) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil) (valp (ix-rc)))
           (and (sstatep (ix-s1)) (equal (cadr (ix-s1)) (cadr s)) (equal (caddr (ix-s1)) (1+ (caddr s)))
                (equal (s-ctl (ix-s1)) (s-ctl s))
                (cagree (cadddr (ix-s1)) (update-nth (caddr s) (cdr (ix-rc)) (cadddr s)) (1+ (caddr s)))
                (sstatep (ix-s1b))
                (equal (car (ix-s1b))
                       (if (truthy (cdr (ix-rc)))
                           (+ (car s) (sxcode-len (cadr e)) 1)
                         (+ (car s) (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1)))
                (equal (cadr (ix-s1b)) (cadr s)) (equal (caddr (ix-s1b)) (caddr s))
                (equal (cadddr (ix-s1b)) (cadddr (ix-s1))) (equal (s-ctl (ix-s1b)) (s-ctl s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance (:definition sx-hyps))
                        (:instance if-hyps-test)
                        (:instance sxgood-gives-val (e (cadr e)) (lc nil))
                        (:instance sx-val-open (e (cadr e)) (r (ix-rc)) (s2 (ix-s1)))
                        (:instance if-code (code (car prog)) (pc (car s)))
                        (:instance jmpf-step-abs (s1 (ix-s1)) (sp (caddr s))
                                   (tgt (+ (car s) (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1)))
                        (:instance cagree-nth (a (cadddr (ix-s1))) (b (update-nth (caddr s) (cdr (ix-rc)) (cadddr s)))
                                   (h (1+ (caddr s))) (r (caddr s)))))))

(defmacro if-branch-hyps (x)
  `(and (equal (car e) :if) (sx-hyps e depth cenv self caps s env defs prog lc)
        (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
        (sxgood ,x depth cenv self caps (ix-s1b) env defs fuel prog lc)
        (valp (ix-rc))))

; THEN, a value: the jump past the else
(defthm if-path-then-val
  (implies (and (if-branch-hyps (caddr e)) (truthy (cdr (ix-rc))) (valp (ix-rt)))
           (let ((s3 (vcsx-step prog (ix-st))))
             (and (sstatep s3) (equal (car s3) (+ (car s) (sxcode-len e))) (equal (cadr s3) (cadr s))
                  (equal (caddr s3) (1+ (caddr s))) (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth (caddr s) (cdr (ix-rt)) (cadddr s)) (1+ (caddr s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance if-test-facts)
                        (:instance if-code (code (car prog)) (pc (car s)))
                        (:instance (:definition sx-hyps))
                        (:instance if-hyps-branch (th t) (s1b (ix-s1b)) (v (cdr (ix-rc))))
                        (:instance sxgood-gives-val (e (caddr e)) (s (ix-s1b)))
                        (:instance sx-val-open (e (caddr e)) (s (ix-s1b)) (r (ix-rt)) (s2 (ix-st)))
                        (:instance jmp-step-abs (s2 (ix-st)) (tgt (+ (car s) (sxcode-len (cadr e)) 1 (sxcode-len (caddr e)) 1
                                                                     (sxcode-len (cadddr e)))))
                        (:instance sif-combine (sp (caddr s)) (s3 (cadddr (ix-st))) (s1 (cadddr (ix-s1))) (s0 (cadddr s))
                                   (va (cdr (ix-rc))) (vb (cdr (ix-rt))))))))

; ELSE, a value: it ends where the if does
(defthm if-path-else-val
  (implies (and (if-branch-hyps (cadddr e)) (not (truthy (cdr (ix-rc)))) (valp (ix-re)))
           (let ((s3 (ix-se)))
             (and (sstatep s3) (equal (car s3) (+ (car s) (sxcode-len e))) (equal (cadr s3) (cadr s))
                  (equal (caddr s3) (1+ (caddr s))) (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth (caddr s) (cdr (ix-re)) (cadddr s)) (1+ (caddr s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance if-test-facts)
                        (:instance if-code (code (car prog)) (pc (car s)))
                        (:instance (:definition sx-hyps))
                        (:instance if-hyps-branch (th nil) (s1b (ix-s1b)) (v (cdr (ix-rc))))
                        (:instance sxgood-gives-val (e (cadddr e)) (s (ix-s1b)))
                        (:instance sx-val-open (e (cadddr e)) (s (ix-s1b)) (r (ix-re)) (s2 (ix-se)))
                        (:instance sif-combine (sp (caddr s)) (s3 (cadddr (ix-se))) (s1 (cadddr (ix-s1))) (s0 (cadddr s))
                                   (va (cdr (ix-rc))) (vb (cdr (ix-re))))))))

; a branch's recur: at the loop's head, nothing below its slots changed
(defthm if-path-rec
  (implies (and (if-branch-hyps x) (equal x (if th (caddr e) (cadddr e)))
                (iff (truthy (cdr (ix-rc))) th)
                (recurp (mx x env caps defs fuel)))
           (sx-rec s (mx x env caps defs fuel) (vcsx-run prog (ix-s1b) (sxclk x env caps defs fuel)) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sx-rec) (let-thy)) :do-not-induct t
                  :use ((:instance if-test-facts)
                        (:instance (:definition sx-hyps))
                        (:instance if-hyps-branch (s1b (ix-s1b)) (v (cdr (ix-rc))))
                        (:instance sxgood-gives-rec (e x) (s (ix-s1b)))
                        (:instance sx-rec-open (s (ix-s1b)) (r (mx x env caps defs fuel))
                                   (s2 (vcsx-run prog (ix-s1b) (sxclk x env caps defs fuel))))
                        (:instance cagree-through-push (a (cadddr (vcsx-run prog (ix-s1b) (sxclk x env caps defs fuel))))
                                   (b (cadddr (ix-s1))) (c (cadddr s))
                                   (h (+ (cadr s) (cadr lc))) (sp (caddr s)) (v (cdr (ix-rc))))))))

(defmacro if-join-hyps ()
  '(and (equal (car e) :if) (sx-hyps e depth cenv self caps s env defs prog lc)
        (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
        (sxgood (caddr e) depth cenv self caps (ix-s1b) env defs fuel prog lc)
        (sxgood (cadddr e) depth cenv self caps (ix-s1b) env defs fuel prog lc)))

; the test is never a recur: what is not a value is neither outcome
(defthm if-test-not-recur
  (implies (and (equal (car e) :if) (sx-hyps e depth cenv self caps s env defs prog lc))
           (not (recurp (ix-rc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance if-hyps-test) (:instance (:definition sx-hyps) (e (cadr e)) (lc nil))
                        (:instance mx-not-recur (e (cadr e)))))))

(defthm if-join-val
  (implies (if-join-hyps)
           (sx-val e s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sx-val) (let-thy)) :do-not-induct t
                  :cases ((not (valp (ix-rc))) (truthy (cdr (ix-rc))))
                  :use ((:instance if-path-then-val) (:instance if-path-else-val)
                        (:instance if-clock) (:instance mx-if)))))

(defthm if-join-rec
  (implies (if-join-hyps)
           (sx-rec s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel)) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sx-rec) (let-thy)) :do-not-induct t
                  :cases ((not (valp (ix-rc))) (truthy (cdr (ix-rc))))
                  :use ((:instance if-path-rec (x (caddr e)) (th t))
                        (:instance if-path-rec (x (cadddr e)) (th nil))
                        (:instance if-test-not-recur)
                        (:instance if-clock) (:instance mx-if)))))

; THE IF
(defthm sxgood-if
  (implies (and (equal (car e) :if)
                (sxgood (cadr e) depth cenv self caps s env defs fuel prog nil)
                (sxgood (caddr e) depth cenv self caps (ix-s1b) env defs fuel prog lc)
                (sxgood (cadddr e) depth cenv self caps (ix-s1b) env defs fuel prog lc))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood) (theory 'minimal-theory)) :do-not-induct t
                  :use ((:instance if-join-val) (:instance if-join-rec)))))

; ---- arguments, and a closure made of them ----------------------------------------

(defthm sxgood-args-nil
  (implies (atom es) (sxgood-args es depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm sxgood-args-cons
  (implies (and (consp es)
                (sxgood (car es) depth cenv self caps s env defs fuel prog nil)
                (sxgood-args (cdr es) (1+ depth) cenv self caps (vcsx-run prog s (sxclk (car es) env caps defs fuel))
                             env defs fuel prog))
           (sxgood-args es depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth mx cself-ok sx-rec)
                  :expand ((vcsx-compile-args es depth cenv self (car s))
                           (mx-args es env caps defs fuel)
                           (cvals-at (caddr s) (val (mx-args es env caps defs fuel))
                                     (cadddr (vcsx-run prog s (sxclk-args es env caps defs fuel))))))))

(defthm mx-args-val-shape
  (implies (valp (mx-args es env caps defs fuel))
           (and (equal (len (val (mx-args es env caps defs fuel))) (len es))
                (true-listp (val (mx-args es env caps defs fuel)))))
  :hints (("Goal" :induct (len es) :expand ((mx-args es env caps defs fuel)))))

(defthm mx-mkclo
  (implies (equal (car e) :mkclo)
           (equal (mx e env caps defs fuel)
                  (if (valp (mx-args (cddr e) env caps defs fuel))
                      (cons :val (clo (cadr e) (val (mx-args (cddr e) env caps defs fuel))))
                    (mx-args (cddr e) env caps defs fuel))))
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

(defthm sxgood-mkclo
  (implies (and (equal (car e) :mkclo)
                (sxgood-args (cddr e) depth cenv self caps s env defs fuel prog))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth sxgood-args mx mx-args)
                  :expand ((vcsx-compile e depth cenv self (car s) lc) (sxclk e env caps defs fuel)
                           (xwf e (len env) (lck lc)) (sxcode-len e))
                  :use ((:instance (:definition sxgood-args) (es (cddr e)))
                        (:instance mx-args-not-recur (es (cddr e)))
                        (:instance mx-args-val-shape (es (cddr e)))
                        (:instance cagree-write-at (n (caddr s))
                                   (a (cadddr (vcsx-run prog s (sxclk-args (cddr e) env caps defs fuel))))
                                   (b (cadddr s))
                                   (x (clo (cadr e) (cdr (mx-args (cddr e) env caps defs fuel)))))
                        (:instance stk-from-vals (a (caddr s))
                                   (vs (cdr (mx-args (cddr e) env caps defs fuel)))
                                   (stk (cadddr (vcsx-run prog s (sxclk-args (cddr e) env caps defs fuel)))))))))

; ---- a recur: its values down into the loop's slots, and back to the head ----------

(defthm mx-recur
  (implies (equal (car e) :recur)
           (equal (mx e env caps defs fuel)
                  (if (valp (mx-args (cdr e) env caps defs fuel))
                      (cons :recur (val (mx-args (cdr e) env caps defs fuel)))
                    (mx-args (cdr e) env caps defs fuel))))
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

(defthm recur-code
  (implies (and (equal (car e) :recur) (ccode-at code pc (vcsx-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcsx-compile-args (cdr e) depth cenv self pc))
                (equal (car (nth (+ pc (sxcode-len-args (cdr e))) code)) :recur)
                (equal (cadr (nth (+ pc (sxcode-len-args (cdr e))) code)) (nfix (caddr lc)))
                (equal (caddr (nth (+ pc (sxcode-len-args (cdr e))) code)) (nfix (cadr lc)))
                (equal (cadddr (nth (+ pc (sxcode-len-args (cdr e))) code)) (nfix (car lc)))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc lc)))))

(defthm recur-clock
  (implies (equal (car e) :recur)
           (equal (vcsx-run prog s (sxclk e env caps defs fuel))
                  (vcsx-step prog (vcsx-run prog s (sxclk-args (cdr e) env caps defs fuel)))))
  :rule-classes nil
  :hints (("Goal" :expand ((sxclk e env caps defs fuel)) :in-theory (disable c+))))

(defmacro rx-s1 () '(vcsx-run prog s (sxclk-args (cdr e) env caps defs fuel)))
(defmacro rx-vs () '(val (mx-args (cdr e) env caps defs fuel)))

; the recur's step, over plain states: the k values pushed at sp copied to fb+b
(defthm recur-step-abs
  (implies (and (sstatep s1) (natp sp) (natp b) (natp k) (natp tgt)
                (equal (caddr s1) (+ sp k)) (<= (+ (cadr s1) b) sp)
                (equal (car (nth (car s1) (car prog))) :recur) (equal (cadr (nth (car s1) (car prog))) k)
                (equal (caddr (nth (car s1) (car prog))) b) (equal (cadddr (nth (car s1) (car prog))) tgt)
                (cagree (cadddr s1) stk0 sp) (cvals-at sp vs (cadddr s1)) (equal (len vs) k))
           (let ((s2 (vcsx-step prog s1)))
             (and (sstatep s2) (equal (car s2) tgt) (equal (cadr s2) (cadr s1))
                  (equal (caddr s2) (+ (cadr s1) b k)) (equal (s-ctl s2) (s-ctl s1))
                  (cagree (cadddr s2) stk0 (+ (cadr s1) b))
                  (cvals-at (+ (cadr s1) b) vs (cadddr s2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth cagree-copy-down cagree-trans cagree-smaller) :do-not-induct t
                  :use ((:instance copy-down-vals (src (- (caddr s1) (len vs))) (dst (+ (cadr s1) b)) (k (len vs)) (stk (cadddr s1)))
                        (:instance cagree-copy-down (src sp) (dst (+ (cadr s1) b)) (stk (cadddr s1)))
                        (:instance cagree-smaller (a (cadddr s1)) (b stk0) (h sp) (g (+ (cadr s1) b)))
                        (:instance cagree-trans (a (copy-down sp (+ (cadr s1) b) k (cadddr s1))) (b (cadddr s1)) (c stk0)
                                   (h (+ (cadr s1) b)))))))

(defthm recur-hyps-args
  (implies (and (equal (car e) :recur) (sx-hyps e depth cenv self caps s env defs prog lc))
           (and (consp lc) (natp (car lc)) (natp (cadr lc)) (natp (caddr lc))
                (<= (+ (cadr lc) (caddr lc)) depth)
                (equal (len (cdr e)) (caddr lc))
                (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
                (ccode-at (car prog) (car s) (vcsx-compile-args (cdr e) depth cenv self (car s)))
                (xwf-args (cdr e) (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
                (cself-ok self caps (cadddr s) (cadr s) depth)
                (xdefs-ok defs) (sxfns-ok prog defs)))
  :rule-classes nil
  :hints (("Goal" :expand ((xwf e (len env) (lck lc)))
                  :use ((:instance recur-code (code (car prog)) (pc (car s)))))))

(defthm recur-rec
  (implies (and (equal (car e) :recur) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood-args (cdr e) depth cenv self caps s env defs fuel prog))
           (sx-rec s (mx e env caps defs fuel) (vcsx-run prog s (sxclk e env caps defs fuel)) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sx-rec sxgood-args mx-recur) (let-thy)) :do-not-induct t
                  :use ((:instance recur-hyps-args)
                        (:instance (:definition sx-hyps))
                        (:instance mx-args-not-recur (es (cdr e)))
                        (:instance recur-code (code (car prog)) (pc (car s)))
                        (:instance recur-clock)
                        (:instance mx-args-val-shape (es (cdr e)))
                        (:instance recur-step-abs (s1 (rx-s1)) (sp (caddr s)) (b (cadr lc)) (k (caddr lc)) (tgt (car lc))
                                   (stk0 (cadddr s)) (vs (rx-vs)))))))

(defthm recur-val
  (implies (equal (car e) :recur)
           (sx-val e s (mx e env caps defs fuel) s2))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sx-val mx-recur) (let-thy)) :do-not-induct t
                  :use ((:instance mx-args-not-recur-shape (es (cdr e)))))))

(defthm sxgood-recur
  (implies (and (equal (car e) :recur)
                (sxgood-args (cdr e) depth cenv self caps s env defs fuel prog))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood) (theory 'minimal-theory)) :do-not-induct t
                  :use ((:instance recur-rec) (:instance recur-val (s2 (vcsx-run prog s (sxclk e env caps defs fuel))))))))

; ---- the loop's slides: its locals dropped from under its value -------------------

(defthm ccode-at-slides
  (implies (and (ccode-at code pc (slides k)) (not (zp k)))
           (and (equal (nth pc code) (list :slide)) (ccode-at code (1+ pc) (slides (1- k)))))
  :rule-classes nil
  :hints (("Goal" :expand ((slides k) (ccode-at code pc (slides k))))))

(defun slides-ind (prog s2 k base)
  (if (zp k) (list s2 base) (slides-ind prog (vcsx-step prog s2) (1- k) base)))

(defthm slides-run
  (implies (and (sstatep s2) (natp k) (natp base) (ccode-at (car prog) (car s2) (slides k))
                (equal (caddr s2) (+ base k 1)))
           (let ((s3 (vcsx-run prog s2 k)))
             (and (sstatep s3) (equal (car s3) (+ (car s2) k)) (equal (cadr s3) (cadr s2))
                  (equal (caddr s3) (1+ base)) (equal (s-ctl s3) (s-ctl s2))
                  (equal (nth base (cadddr s3)) (nth (+ base k) (cadddr s2)))
                  (cagree (cadddr s3) (cadddr s2) base))))
  :hints (("Goal" :induct (slides-ind prog s2 k base)
                  :in-theory (e/d (vcsx-run) (nth update-nth))
                  :expand ((vcsx-run prog s2 k)))
          ("Subgoal *1/2" :use ((:instance ccode-at-slides (code (car prog)) (pc (car s2)))
                                (:instance cagree-trans (a (cadddr (vcsx-run prog (vcsx-step prog s2) (1- k))))
                                           (b (cadddr (vcsx-step prog s2))) (c (cadddr s2)) (h base))))))

; ---- THE LOOP'S ITERATIONS ----------------------------------------------------------
;
; at the loop's head: its k values in their slots, nothing above them;
; the iterations end with the loop's value just above its slots, and
; nothing below its first slot changed

(defmacro lp-k () '(len (cadr e)))
(defmacro lp-cenv () '(append cenv (count-from depth (+ depth (len (cadr e))))))
(defmacro lp-lc () '(list (car s) depth (len (cadr e))))
(defmacro lp-rb () '(mx (caddr e) (append env vs) caps defs fuel))
(defmacro lp-s2 () '(vcsx-run prog s (sxclk (caddr e) (append env vs) caps defs fuel)))

(defun loopit-hyps (e depth cenv self caps s env vs defs prog)
  (and (equal (car e) :loop) (consp e)
       (sstatep s) (natp depth) (equal (len vs) (len (cadr e)))
       (equal (caddr s) (+ (cadr s) depth (len (cadr e))))
       (ccode-at (car prog) (car s) (vcsx-compile (caddr e) (+ depth (len (cadr e))) (lp-cenv) self (car s) (lp-lc)))
       (xwf (caddr e) (+ (len env) (len (cadr e))) (len (cadr e)))
       (cenv-ok cenv env (cadddr s) (cadr s) depth)
       (cself-ok self caps (cadddr s) (cadr s) depth)
       (cvals-at (+ (cadr s) depth) vs (cadddr s))
       (xdefs-ok defs) (sxfns-ok prog defs)))

(defun sxgood-loopit (e depth cenv self caps s env vs defs fuel prog)
  (implies (loopit-hyps e depth cenv self caps s env vs defs prog)
           (let ((r (mx-loop e env vs caps defs fuel)) (s2 (vcsx-run prog s (sxclk-loop e env vs caps defs fuel))))
             (implies (valp r)
                      (and (sstatep s2)
                           (equal (car s2) (+ (car s) (sxcode-len (caddr e))))
                           (equal (cadr s2) (cadr s))
                           (equal (caddr s2) (+ 1 (caddr s)))
                           (equal (s-ctl s2) (s-ctl s))
                           (cagree (cadddr s2) (cadddr s) (+ (cadr s) depth))
                           (equal (nth (caddr s) (cadddr s2)) (cdr r)))))))

(defthm mx-loop-open
  (implies (consp e)
           (equal (mx-loop e base vs caps defs fuel)
                  (let ((r (mx (caddr e) (append base vs) caps defs fuel)))
                    (cond ((not (equal (car r) :recur)) r)
                          ((zp fuel) (list :out))
                          (t (mx-loop e base (cdr r) caps defs (1- fuel)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx-loop e base vs caps defs fuel)))))

(defthm sxclk-loop-open
  (implies (consp e)
           (equal (sxclk-loop e base vs caps defs fuel)
                  (if (and (recurp (mx (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
                      (c+ (sxclk (caddr e) (append base vs) caps defs fuel)
                          (sxclk-loop e base (cdr (mx (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel)))
                    (sxclk (caddr e) (append base vs) caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :expand ((sxclk-loop e base vs caps defs fuel)) :in-theory (disable c+ recurp))))

; the body's hypotheses at the head
(defthm loopit-body-hyps
  (implies (loopit-hyps e depth cenv self caps s env vs defs prog)
           (sx-hyps (caddr e) (+ depth (len (cadr e))) (lp-cenv) self caps s (append env vs) defs prog (lp-lc)))
  :hints (("Goal" :in-theory (disable cenv-ok cself-ok cenv-ok-count-from cenv-ok-bigger-f cself-ok-bigger-f)
                  :use ((:instance cenv-ok-count-from (i depth) (n (+ depth (len (cadr e)))) (base (cadr s))
                                   (regs (cadddr s)) (g (+ depth (len (cadr e)))))
                        (:instance cenv-ok-bigger-f (regs (cadddr s)) (fb (cadr s)) (f depth) (g (+ depth (len (cadr e)))))
                        (:instance cself-ok-bigger-f (regs (cadddr s)) (fb (cadr s)) (f depth) (g (+ depth (len (cadr e)))))
                        (:instance cenv-ok-len (regs (cadddr s)) (fb (cadr s)) (f depth))))))

(defmacro loopit-thy () '(union-theories '(loopit-hyps) (let-thy)))

; the body a value: the loop's value just above its slots
(defthm loopit-path-val
  (implies (and (loopit-hyps e depth cenv self caps s env vs defs prog)
                (sxgood (caddr e) (+ depth (len (cadr e))) (lp-cenv) self caps s (append env vs) defs fuel prog (lp-lc))
                (valp (lp-rb)))
           (and (sstatep (lp-s2))
                (equal (car (lp-s2)) (+ (car s) (sxcode-len (caddr e))))
                (equal (cadr (lp-s2)) (cadr s))
                (equal (caddr (lp-s2)) (+ 1 (caddr s)))
                (equal (s-ctl (lp-s2)) (s-ctl s))
                (cagree (cadddr (lp-s2)) (cadddr s) (+ (cadr s) depth))
                (equal (nth (caddr s) (cadddr (lp-s2))) (cdr (lp-rb)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (loopit-thy) :do-not-induct t
                  :use ((:instance loopit-body-hyps)
                        (:instance sxgood-gives-val (e (caddr e)) (depth (+ depth (len (cadr e)))) (cenv (lp-cenv))
                                   (env (append env vs)) (lc (lp-lc)))
                        (:instance sx-val-open (e (caddr e)) (r (lp-rb)) (s2 (lp-s2)))
                        (:instance cagree-past-write (a (cadddr (lp-s2))) (b (cadddr s)) (g (caddr s)) (w (cdr (lp-rb)))
                                   (h (1+ (caddr s))) (f (+ (cadr s) depth)))
                        (:instance cagree-nth (a (cadddr (lp-s2))) (b (update-nth (caddr s) (cdr (lp-rb)) (cadddr s)))
                                   (h (1+ (caddr s))) (r (caddr s)))))))

; the body a recur: back at the head, its hypotheses again, the new values in the slots
(defthm loopit-path-rec
  (implies (and (loopit-hyps e depth cenv self caps s env vs defs prog)
                (sxgood (caddr e) (+ depth (len (cadr e))) (lp-cenv) self caps s (append env vs) defs fuel prog (lp-lc))
                (recurp (lp-rb)))
           (and (loopit-hyps e depth cenv self caps (lp-s2) env (cdr (lp-rb)) defs prog)
                (equal (car (lp-s2)) (car s)) (equal (cadr (lp-s2)) (cadr s))
                (equal (caddr (lp-s2)) (caddr s)) (equal (s-ctl (lp-s2)) (s-ctl s))
                (cagree (cadddr (lp-s2)) (cadddr s) (+ (cadr s) depth))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(cenv-ok-agree cself-ok-agree) (loopit-thy)) :do-not-induct t
                  :use ((:instance loopit-body-hyps)
                        (:instance sxgood-gives-rec (e (caddr e)) (depth (+ depth (len (cadr e)))) (cenv (lp-cenv))
                                   (env (append env vs)) (lc (lp-lc)))
                        (:instance sx-rec-open (r (lp-rb)) (s2 (lp-s2)) (lc (lp-lc)))
                        (:instance cagree-sym (a (cadddr (lp-s2))) (b (cadddr s)) (h (+ (cadr s) depth)))))))

(defmacro lp-s3 () '(vcsx-run prog (lp-s2) (sxclk-loop e env (cdr (lp-rb)) caps defs (1- fuel))))

; ONE ITERATION, given the body's property here and the iterations' after it
(defthm sxgood-loopit-step
  (implies (and (consp e)
                (sxgood (caddr e) (+ depth (len (cadr e))) (lp-cenv) self caps s (append env vs) defs fuel prog (lp-lc))
                (implies (and (recurp (lp-rb)) (not (zp fuel)))
                         (sxgood-loopit e depth cenv self caps (lp-s2) env (cdr (lp-rb)) defs (1- fuel) prog)))
           (sxgood-loopit e depth cenv self caps s env vs defs fuel prog))
  :hints (("Goal" :in-theory (union-theories '(sxgood-loopit vcsx-run-c+ (:type-prescription sxclk) (:type-prescription sxclk-loop))
                                             (loopit-thy))
                  :do-not-induct t
                  :cases ((valp (lp-rb)) (and (recurp (lp-rb)) (not (zp fuel))))
                  :use ((:instance loopit-path-val)
                        (:instance loopit-path-rec)
                        (:instance mx-loop-open (base env))
                        (:instance sxclk-loop-open (base env))
                        (:instance cagree-trans (a (cadddr (lp-s3))) (b (cadddr (lp-s2))) (c (cadddr s))
                                   (h (+ (cadr s) depth)))))))

; ---- THE LOOP ------------------------------------------------------------------------

(defmacro lpe-ri () '(mx-args (cadr e) env caps defs fuel))
(defmacro lpe-vs () '(cdr (mx-args (cadr e) env caps defs fuel)))
(defmacro lpe-s1 () '(vcsx-run prog s (sxclk-args (cadr e) env caps defs fuel)))
(defmacro lpe-s2 () '(vcsx-run prog (lpe-s1) (sxclk-loop e env (lpe-vs) caps defs fuel)))
(defmacro lpe-head () '(+ pc (sxcode-len-args (cadr e))))

(defthm loop-code
  (implies (and (equal (car e) :loop) (ccode-at code pc (vcsx-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcsx-compile-args (cadr e) depth cenv self pc))
                (ccode-at code (lpe-head)
                          (vcsx-compile (caddr e) (+ depth (len (cadr e))) (append cenv (count-from depth (+ depth (len (cadr e)))))
                                        self (lpe-head) (list (lpe-head) depth (len (cadr e)))))
                (ccode-at code (+ (lpe-head) (sxcode-len (caddr e))) (slides (len (cadr e))))
                (equal (sxcode-len e) (+ (sxcode-len-args (cadr e)) (sxcode-len (caddr e)) (len (cadr e))))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc lc) (sxcode-len e)))))

(defthm mx-loop-expr
  (implies (equal (car e) :loop)
           (equal (mx e env caps defs fuel)
                  (if (valp (lpe-ri)) (mx-loop e env (lpe-vs) caps defs fuel) (lpe-ri))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

(defthm loop-clock
  (implies (equal (car e) :loop)
           (equal (vcsx-run prog s (sxclk e env caps defs fuel))
                  (vcsx-run prog (lpe-s2) (len (cadr e)))))
  :rule-classes nil
  :hints (("Goal" :expand ((sxclk e env caps defs fuel)) :in-theory (disable c+))))

; after the inits: the loop's head, its iteration hypotheses
(defthm loop-iter-hyps
  (implies (and (equal (car e) :loop) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood-args (cadr e) depth cenv self caps s env defs fuel prog) (valp (lpe-ri)))
           (and (loopit-hyps e depth cenv self caps (lpe-s1) env (lpe-vs) defs prog)
                (equal (car (lpe-s1)) (+ (car s) (sxcode-len-args (cadr e))))
                (equal (cadr (lpe-s1)) (cadr s)) (equal (caddr (lpe-s1)) (+ (caddr s) (len (cadr e))))
                (equal (s-ctl (lpe-s1)) (s-ctl s))
                (cagree (cadddr (lpe-s1)) (cadddr s) (caddr s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable cenv-ok cself-ok mx-args)
                  :expand ((xwf e (len env) (lck lc)))
                  :use ((:instance loop-code (code (car prog)) (pc (car s)))
                        (:instance mx-args-val-shape (es (cadr e)))
                        (:instance cenv-ok-agree (a (cadddr s)) (b (cadddr (lpe-s1))) (fb (cadr s)) (f depth))
                        (:instance cself-ok-agree (a (cadddr s)) (b (cadddr (lpe-s1))) (fb (cadr s)) (f depth))
                        (:instance cagree-sym (a (cadddr (lpe-s1))) (b (cadddr s)) (h (caddr s)))))))

; the loop a value: iterated, then slid down to its own slot
(defthm loop-path-val
  (implies (and (equal (car e) :loop) (sx-hyps e depth cenv self caps s env defs prog lc)
                (sxgood-args (cadr e) depth cenv self caps s env defs fuel prog)
                (sxgood-loopit e depth cenv self caps (lpe-s1) env (lpe-vs) defs fuel prog)
                (valp (lpe-ri)) (valp (mx-loop e env (lpe-vs) caps defs fuel)))
           (let ((s3 (vcsx-run prog (lpe-s2) (len (cadr e)))))
             (and (sstatep s3) (equal (car s3) (+ (car s) (sxcode-len e))) (equal (cadr s3) (cadr s))
                  (equal (caddr s3) (1+ (caddr s))) (equal (s-ctl s3) (s-ctl s))
                  (cagree (cadddr s3) (update-nth (caddr s) (cdr (mx-loop e env (lpe-vs) caps defs fuel)) (cadddr s))
                          (1+ (caddr s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sxgood-loopit sx-hyps) (let-thy)) :do-not-induct t
                  :use ((:instance loop-iter-hyps)
                        (:instance loop-code (code (car prog)) (pc (car s)))
                        (:instance slides-run (s2 (lpe-s2)) (k (len (cadr e))) (base (caddr s)))
                        (:instance cagree-trans (a (cadddr (vcsx-run prog (lpe-s2) (len (cadr e))))) (b (cadddr (lpe-s2)))
                                   (c (cadddr (lpe-s1))) (h (caddr s)))
                        (:instance cagree-trans (a (cadddr (vcsx-run prog (lpe-s2) (len (cadr e))))) (b (cadddr (lpe-s1)))
                                   (c (cadddr s)) (h (caddr s)))
                        (:instance cagree-extend (a (cadddr (vcsx-run prog (lpe-s2) (len (cadr e))))) (b (cadddr s))
                                   (n (caddr s)) (v (cdr (mx-loop e env (lpe-vs) caps defs fuel))))))))

(defthm xwf-loop-args
  (implies (and (equal (car e) :loop) (xwf e n k)) (xwf-args (cadr e) n))
  :rule-classes nil)

(defthm sxgood-loop
  (implies (and (equal (car e) :loop)
                (sxgood-args (cadr e) depth cenv self caps s env defs fuel prog)
                (sxgood-loopit e depth cenv self caps (lpe-s1) env (lpe-vs) defs fuel prog))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood sx-val sx-rec) (let-thy)) :do-not-induct t
                  :use ((:instance loop-path-val) (:instance mx-loop-expr) (:instance loop-clock)
                        (:instance mx-loop-not-recur (base env) (vs (lpe-vs)))
                        (:instance (:definition sx-hyps))
                        (:instance mx-args-not-recur (es (cadr e)))
                        (:instance xwf-loop-args (n (len env)) (k (lck lc)))))))

; ---- THE CALL ------------------------------------------------------------------------

(defmacro cx-n () '(len (cddr e)))
(defmacro cx-s1 () '(vcsx-run prog s (sxclk-args (cddr e) env caps defs fuel)))
(defmacro cx-s2 () '(vcsx-run prog (cx-s1) (sxclk (cadr e) env caps defs fuel)))
(defmacro cx-c () '(cdr (mx (cadr e) env caps defs fuel)))
(defmacro cx-vs () '(cdr (mx-args (cddr e) env caps defs fuel)))
(defmacro cx-def () '(cdr (assoc-equal (clo-f (cx-c)) defs)))
(defmacro cx-ent () '(cdr (assoc-equal (clo-f (cx-c)) (cdr prog))))
(defmacro cx-s3 () '(vcsx-step prog (cx-s2)))
(defmacro cx-r () '(mx (cadr (cx-def)) (cx-vs) (clo-caps (cx-c)) defs (1- fuel)))
(defmacro cx-s4 () '(vcsx-run prog (cx-s3) (sxclk (cadr (cx-def)) (cx-vs) (clo-caps (cx-c)) defs (1- fuel))))
(defmacro cx-s5 () '(vcsx-step prog (cx-s4)))

; what a call that is a value says about its parts
(defthm callv-facts
  (implies (and (equal (car e) :callv) (valp (mx e env caps defs fuel)))
           (and (valp (mx-args (cddr e) env caps defs fuel))
                (valp (mx (cadr e) env caps defs fuel))
                (clop (cx-c))
                (consp (assoc-equal (clo-f (cx-c)) defs))
                (equal (len (cx-vs)) (nfix (car (cx-def))))
                (not (zp fuel))
                (equal (mx e env caps defs fuel) (cx-r))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx e env caps defs fuel)))))

(defthm callv-xcode
  (implies (and (equal (car e) :callv) (ccode-at code pc (vcsx-compile e depth cenv self pc nil)) (natp pc))
           (and (ccode-at code pc (vcsx-compile-args (cddr e) depth cenv self pc))
                (ccode-at code (+ pc (sxcode-len-args (cddr e)))
                          (vcsx-compile (cadr e) (+ depth (cx-n)) cenv self (+ pc (sxcode-len-args (cddr e))) nil))
                (equal (car (nth (+ pc (sxcode-len-args (cddr e)) (sxcode-len (cadr e))) code)) :callv)
                (equal (cadr (nth (+ pc (sxcode-len-args (cddr e)) (sxcode-len (cadr e))) code)) (cx-n))
                (equal (sxcode-len e) (+ (sxcode-len-args (cddr e)) (sxcode-len (cadr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-compile e depth cenv self pc nil) (sxcode-len e)))))

(defthm callv-xclock
  (implies (and (equal (car e) :callv) (not (zp fuel)))
           (equal (vcsx-run prog s (sxclk e env caps defs fuel)) (cx-s5)))
  :rule-classes nil
  :hints (("Goal" :expand ((sxclk e env caps defs fuel)) :in-theory (disable c+))))

(defthm callv-wf-parts
  (implies (and (equal (car e) :callv) (xwf e n k))
           (and (xwf (cadr e) n nil) (xwf-args (cddr e) n)))
  :rule-classes nil)

; a function's body and its return, where the table says
(defthm vcsx-body-code
  (implies (and (ccode-at code pc (vcsx-body def pc)) (natp pc))
           (and (ccode-at code pc (vcsx-compile (cadr def) (1+ (nfix (car def))) (count-from 0 (nfix (car def)))
                                                (nfix (car def)) pc nil))
                (equal (nth (+ pc (sxcode-len (cadr def))) code) (list :ret))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcsx-body def pc)))))

(defmacro cx-hyps ()
  '(and (equal (car e) :callv) (sx-hyps e depth cenv self caps s env defs prog lc)
        (sxgood-args (cddr e) depth cenv self caps s env defs fuel prog)
        (valp (mx e env caps defs fuel))))

(defthm cx-stage-args
  (implies (cx-hyps)
           (and (sstatep (cx-s1)) (equal (car (cx-s1)) (+ (car s) (sxcode-len-args (cddr e))))
                (equal (cadr (cx-s1)) (cadr s)) (equal (caddr (cx-s1)) (+ (caddr s) (cx-n)))
                (equal (s-ctl (cx-s1)) (s-ctl s))
                (cagree (cadddr (cx-s1)) (cadddr s) (caddr s))
                (cvals-at (caddr s) (cx-vs) (cadddr (cx-s1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable mx mx-args cenv-ok cself-ok) :do-not-induct t
                  :use ((:instance sx-hyps-op-nil)
                        (:instance callv-facts)
                        (:instance callv-xcode (code (car prog)) (pc (car s)))
                        (:instance callv-wf-parts (n (len env)) (k nil))))))

(defthm cx-fn-hyps
  (implies (cx-hyps)
           (sx-hyps (cadr e) (+ depth (cx-n)) cenv self caps (cx-s1) env defs prog nil))
  :hints (("Goal" :in-theory (disable mx mx-args cenv-ok cself-ok cenv-ok-agree cself-ok-agree
                                      cenv-ok-bigger-f cself-ok-bigger-f)
                  :do-not-induct t
                  :use ((:instance cx-stage-args)
                        (:instance sx-hyps-op-nil)
                        (:instance callv-xcode (code (car prog)) (pc (car s)))
                        (:instance callv-wf-parts (n (len env)) (k nil))
                        (:instance cagree-sym (a (cadddr (cx-s1))) (b (cadddr s)) (h (caddr s)))
                        (:instance cenv-ok-agree (a (cadddr s)) (b (cadddr (cx-s1))) (fb (cadr s)) (f depth))
                        (:instance cself-ok-agree (a (cadddr s)) (b (cadddr (cx-s1))) (fb (cadr s)) (f depth))
                        (:instance cenv-ok-bigger-f (regs (cadddr (cx-s1))) (fb (cadr s)) (f depth) (g (+ depth (cx-n))))
                        (:instance cself-ok-bigger-f (regs (cadddr (cx-s1))) (fb (cadr s)) (f depth) (g (+ depth (cx-n))))))))

(defthm cx-stage-fn
  (implies (and (cx-hyps) (sxgood (cadr e) (+ depth (cx-n)) cenv self caps (cx-s1) env defs fuel prog nil))
           (and (sstatep (cx-s2))
                (equal (car (cx-s2)) (+ (car s) (sxcode-len-args (cddr e)) (sxcode-len (cadr e))))
                (equal (cadr (cx-s2)) (cadr s)) (equal (caddr (cx-s2)) (+ (caddr s) (cx-n) 1))
                (equal (s-ctl (cx-s2)) (s-ctl s))
                (cagree (cadddr (cx-s2)) (update-nth (+ (caddr s) (cx-n)) (cx-c) (cadddr (cx-s1))) (+ (caddr s) (cx-n) 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sxgood-args) (let-thy)) :do-not-induct t
                  :use ((:instance cx-stage-args)
                        (:instance cx-fn-hyps)
                        (:instance callv-facts)
                        (:instance sxgood-gives-val (e (cadr e)) (depth (+ depth (cx-n))) (s (cx-s1)) (lc nil))
                        (:instance sx-val-open (e (cadr e)) (s (cx-s1)) (r (mx (cadr e) env caps defs fuel)) (s2 (cx-s2)))))))

(defmacro cx-hyps-fn ()
  '(and (cx-hyps) (sxgood (cadr e) (+ depth (cx-n)) cenv self caps (cx-s1) env defs fuel prog nil)))

; the call: the callee's frame where the first argument is, a return record
(defthm cx-stage-call
  (implies (cx-hyps-fn)
           (and (sstatep (cx-s3)) (equal (car (cx-s3)) (car (cx-ent)))
                (equal (cadr (cx-s3)) (caddr s)) (equal (caddr (cx-s3)) (+ (caddr s) (cx-n) 1))
                (equal (cadddr (cx-s3)) (cadddr (cx-s2)))
                (equal (s-ctl (cx-s3)) (cons (list (1+ (car (cx-s2))) (cadr s)) (s-ctl s)))
                (natp (car (cx-ent)))
                (ccode-at (car prog) (car (cx-ent)) (vcsx-body (cx-def) (car (cx-ent))))
                (cvals-at (caddr s) (cx-vs) (cadddr (cx-s2)))
                (equal (nth (+ (caddr s) (cx-n)) (cadddr (cx-s2))) (cx-c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sstep-callv-rw sx-hyps) (let-thy)) :do-not-induct t
                  :use ((:instance cx-stage-args)
                        (:instance cx-stage-fn)
                        (:instance callv-facts)
                        (:instance callv-xcode (code (car prog)) (pc (car s)))
                        (:instance sx-hyps-op-nil)
                        (:instance mx-args-val-shape (es (cddr e)))
                        (:instance sxfns-ok-necc (name (clo-f (cx-c))))
                        (:instance callv-args-stay (r2 (cadddr (cx-s2))) (r1 (cadddr (cx-s1)))
                                   (g (+ (caddr s) (cx-n))) (w (cx-c)) (k (caddr s)) (vs (cx-vs)))))))

(defmacro cx-n2 () '(nfix (car (cx-def))))

; the body's hypotheses in the frame the call made
(defthm cx-body-hyps
  (implies (cx-hyps-fn)
           (sx-hyps (cadr (cx-def)) (1+ (cx-n2)) (count-from 0 (cx-n2)) (cx-n2) (clo-caps (cx-c)) (cx-s3) (cx-vs)
                    defs prog nil))
  :hints (("Goal" :in-theory (union-theories (quote (sx-hyps cself-ok lc-ok lck (:executable-counterpart xwf))) (let-thy))
                  :do-not-induct t
                  :use ((:instance cx-stage-call)
                        (:instance callv-facts)
                        (:instance sx-hyps-op-nil)
                        (:instance mx-args-val-shape (es (cddr e)))
                        (:instance vcsx-body-code (code (car prog)) (pc (car (cx-ent))) (def (cx-def)))
                        (:instance xdefs-ok-body-wf (ds defs) (name (clo-f (cx-c))) (vs (cx-vs)))
                        (:instance cenv-ok-count-from (i 0) (n (cx-n2)) (base (caddr s)) (vs (cx-vs))
                                   (regs (cadddr (cx-s2))) (g (1+ (cx-n2))))))))

(defmacro cx-hyps-body ()
  '(and (cx-hyps-fn)
        (sxgood (cadr (cx-def)) (1+ (cx-n2)) (count-from 0 (cx-n2)) (cx-n2) (clo-caps (cx-c)) (cx-s3) (cx-vs)
                defs (1- fuel) prog nil)))

; the body, run in that frame: its answer pushed just above the closure
(defthm cx-stage-body
  (implies (cx-hyps-body)
           (and (sstatep (cx-s4))
                (equal (car (cx-s4)) (+ (car (cx-ent)) (sxcode-len (cadr (cx-def)))))
                (equal (cadr (cx-s4)) (caddr s)) (equal (caddr (cx-s4)) (+ (caddr s) (cx-n) 2))
                (equal (s-ctl (cx-s4)) (cons (list (1+ (car (cx-s2))) (cadr s)) (s-ctl s)))
                (cagree (cadddr (cx-s4)) (update-nth (+ (caddr s) (cx-n) 1) (cdr (cx-r)) (cadddr (cx-s2)))
                        (+ (caddr s) (cx-n) 2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance cx-stage-call)
                        (:instance cx-body-hyps)
                        (:instance callv-facts)
                        (:instance mx-args-val-shape (es (cddr e)))
                        (:instance sxgood-gives-val (e (cadr (cx-def))) (depth (1+ (cx-n2))) (cenv (count-from 0 (cx-n2)))
                                   (self (cx-n2)) (caps (clo-caps (cx-c))) (s (cx-s3)) (env (cx-vs)) (fuel (1- fuel)) (lc nil))
                        (:instance sx-val-open (e (cadr (cx-def))) (s (cx-s3)) (r (cx-r)) (s2 (cx-s4)))))))

; the return, and the call as one push
(defthm callv-path-val
  (implies (cx-hyps-body)
           (and (sstatep (cx-s5))
                (equal (car (cx-s5)) (+ (car s) (sxcode-len e)))
                (equal (cadr (cx-s5)) (cadr s)) (equal (caddr (cx-s5)) (1+ (caddr s)))
                (equal (s-ctl (cx-s5)) (s-ctl s))
                (cagree (cadddr (cx-s5)) (update-nth (caddr s) (cdr (mx e env caps defs fuel)) (cadddr s)) (1+ (caddr s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sstep-ret) (let-thy)) :do-not-induct t
                  :use ((:instance cx-stage-args) (:instance cx-stage-fn) (:instance cx-stage-call) (:instance cx-stage-body)
                        (:instance callv-facts)
                        (:instance sx-hyps-op-nil) (:instance (:definition sx-hyps) (lc nil))
                        (:instance callv-xcode (code (car prog)) (pc (car s)))
                        (:instance vcsx-body-code (code (car prog)) (pc (car (cx-ent))) (def (cx-def)))
                        (:instance cagree-nth (a (cadddr (cx-s4))) (b (update-nth (+ (caddr s) (cx-n) 1) (cdr (cx-r)) (cadddr (cx-s2))))
                                   (h (+ (caddr s) (cx-n) 2)) (r (+ (caddr s) (cx-n) 1)))
                        (:instance cagree-past-write (a (cadddr (cx-s4))) (b (cadddr (cx-s2))) (g (+ (caddr s) (cx-n) 1))
                                   (w (cdr (cx-r))) (h (+ (caddr s) (cx-n) 2)) (f (caddr s)))
                        (:instance cagree-same-write (a (cadddr (cx-s4))) (b (cadddr (cx-s2))) (d (caddr s)) (v (cdr (cx-r)))
                                   (h (caddr s)))
                        (:instance scall-combine (s5 (cadddr (cx-s5))) (s2 (cadddr (cx-s2))) (s1 (cadddr (cx-s1)))
                                   (s0 (cadddr s)) (sp (caddr s)) (v (cdr (cx-r)))
                                   (g (+ (caddr s) (cx-n))) (w (cx-c)) (h2 (+ (caddr s) (cx-n) 1)))))))

(defthm callv-not-recur
  (implies (and (equal (car e) :callv) (sx-hyps e depth cenv self caps s env defs prog lc))
           (not (recurp (mx e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :in-theory (let-thy) :do-not-induct t
                  :use ((:instance sx-hyps-op-nil) (:instance (:definition sx-hyps) (lc nil))
                        (:instance mx-not-recur)))))

; THE CALL
(defthm sxgood-callv
  (implies (and (equal (car e) :callv)
                (sxgood-args (cddr e) depth cenv self caps s env defs fuel prog)
                (sxgood (cadr e) (+ depth (cx-n)) cenv self caps (cx-s1) env defs fuel prog nil)
                (sxgood (cadr (cx-def)) (1+ (cx-n2)) (count-from 0 (cx-n2)) (cx-n2) (clo-caps (cx-c)) (cx-s3) (cx-vs)
                        defs (1- fuel) prog nil))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood sx-val sx-rec val valp) (theory 'minimal-theory)) :do-not-induct t
                  :use ((:instance callv-path-val) (:instance callv-facts) (:instance callv-xclock)
                        (:instance callv-not-recur)))))

(defthm sxgood-callv-no-fuel
  (implies (and (equal (car e) :callv) (zp fuel))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(sxgood sx-val sx-rec val valp) (theory 'minimal-theory)) :do-not-induct t
                  :use ((:instance callv-facts) (:instance callv-not-recur)))))

; ---- THE THEOREM ------------------------------------------------------------------

(defthm sxgood-loopit-atom
  (implies (not (consp e)) (sxgood-loopit e depth cenv self caps s env vs defs fuel prog))
  :hints (("Goal" :in-theory (enable loopit-hyps))))

(defthm sxgood-leaf
  (implies (not (member-equal (car e) (quote (:if :let :add :lt :mkclo :callv :loop :recur))))
           (sxgood e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local) (equal (car e) :capt))
                  :in-theory (union-theories (quote (sxgood-const sxgood-local sxgood-capt sxgood-other member-equal))
                                             (theory (quote minimal-theory))))))

(defun sxind (flg e depth cenv self caps s env defs fuel prog lc vs)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) (if (eq flg :loop) 0 1)))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (cond
   ((eq flg :args)
    (if (atom e)
        (list depth cenv self caps s env defs fuel prog lc vs)
      (list (sxind :m (car e) depth cenv self caps s env defs fuel prog nil nil)
            (sxind :args (cdr e) (1+ depth) cenv self caps (vcsx-run prog s (sxclk (car e) env caps defs fuel))
                   env defs fuel prog nil nil))))
   ((eq flg :loop)
    (if (not (consp e))
        nil
      (list (sxind :m (caddr e) (+ depth (lp-k)) (lp-cenv) self caps s (append env vs) defs fuel prog (lp-lc) nil)
            (if (and (recurp (lp-rb)) (not (zp fuel)))
                (sxind :loop e depth cenv self caps (lp-s2) env defs (1- fuel) prog nil (cdr (lp-rb)))
              nil))))
   (t
    (case (car e)
      (:if (list (sxind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                 (sxind :m (caddr e) depth cenv self caps (ix-s1b) env defs fuel prog lc nil)
                 (sxind :m (cadddr e) depth cenv self caps (ix-s1b) env defs fuel prog lc nil)))
      (:let (list (sxind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                  (sxind :m (caddr e) (1+ depth) (append cenv (list depth)) self caps (lx-s1) (lx-env) defs fuel prog lc nil)))
      ((:add :lt) (list (sxind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                        (sxind :m (caddr e) (1+ depth) cenv self caps (bx-s1) env defs fuel prog nil nil)))
      (:mkclo (sxind :args (cddr e) depth cenv self caps s env defs fuel prog nil nil))
      (:callv (list (sxind :args (cddr e) depth cenv self caps s env defs fuel prog nil nil)
                    (sxind :m (cadr e) (+ depth (cx-n)) cenv self caps (cx-s1) env defs fuel prog nil nil)
                    (if (zp fuel)
                        nil
                      (sxind :m (cadr (cx-def)) (1+ (cx-n2)) (count-from 0 (cx-n2)) (cx-n2) (clo-caps (cx-c)) (cx-s3) (cx-vs)
                             defs (1- fuel) prog nil nil))))
      (:loop (list (sxind :args (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                   (sxind :loop e depth cenv self caps (lpe-s1) env defs fuel prog nil (lpe-vs))))
      (:recur (sxind :args (cdr e) depth cenv self caps s env defs fuel prog nil nil))
      (otherwise (list depth cenv self caps s env defs fuel prog lc vs))))))

(defthm vcsx-good-flag
  (cond ((eq flg :args) (sxgood-args e depth cenv self caps s env defs fuel prog))
        ((eq flg :loop) (sxgood-loopit e depth cenv self caps s env vs defs fuel prog))
        (t (sxgood e depth cenv self caps s env defs fuel prog lc)))
  :rule-classes nil
  :hints (("Goal" :induct (sxind flg e depth cenv self caps s env defs fuel prog lc vs)
                  :in-theory (union-theories '(sxgood-if sxgood-let sxgood-binop sxgood-mkclo sxgood-callv
                                               sxgood-callv-no-fuel sxgood-loop sxgood-recur
                                               sxgood-leaf
                                               sxgood-args-nil sxgood-args-cons
                                               sxgood-loopit-step sxgood-loopit-atom
                                               member-equal car-cons cdr-cons (:induction sxind))
                                             (theory 'minimal-theory)))))

; RUNNING AN EXPRESSION'S CODE ON THE EXTENDED MACHINE PUSHES WHAT THE
; MEANING ANSWERS -- or, in a loop body's tail, arrives at the loop's
; head with the recur's values in place: loops, recur, closures and
; calls, recursion included
(defthm vcsx-good
  (sxgood e depth cenv self caps s env defs fuel prog lc)
  :hints (("Goal" :use ((:instance vcsx-good-flag (flg :m))))))

; ---- WHOLE PROGRAMS -----------------------------------------------------------

(defthm len-vcsx-body
  (equal (len (vcsx-body def pc)) (1+ (sxcode-len (cadr def)))))
(in-theory (disable vcsx-body))

(defthm vcsx-defs-places
  (implies (and (alistp ds) (natp pc) (ccode-at code pc (car (vcsx-defs ds pc)))
                (consp (assoc-equal name ds)))
           (let ((ent (cdr (assoc-equal name (cdr (vcsx-defs ds pc))))))
             (and (consp ent) (natp (car ent))
                  (equal (nfix (cadr ent)) (nfix (car (cdr (assoc-equal name ds)))))
                  (ccode-at code (car ent) (vcsx-body (cdr (assoc-equal name ds)) (car ent))))))
  :hints (("Goal" :induct (vcsx-defs ds pc))))

(defmacro sxv-main () '(append (vcsx-compile e 0 nil nil 0 nil) (list (list :ret))))

(defthm vcsx-program-fns-ok
  (implies (alistp defs) (sxfns-ok (vcsx-program e defs) defs))
  :hints (("Goal" :in-theory (enable sxfns-ok)
                  :use ((:instance vcsx-defs-places (ds defs) (pc (len (sxv-main)))
                                   (code (car (vcsx-program e defs)))
                                   (name (sxfns-ok-witness (vcsx-program e defs) defs)))
                        (:instance ccode-at-self-gen (p (sxv-main)) (x (car (vcsx-defs defs (len (sxv-main))))))))))

(defthm sxhalted-stays
  (implies (and (sstatep s) (equal (cadr s) 0) (equal (caddr s) 1) (not (consp (s-ctl s)))
                (ccode-at (car prog) (car s) (list (list :ret))))
           (let ((s2 (vcsx-run prog s k)))
             (and (sstatep s2) (equal (car s2) (car s)) (equal (cadr s2) 0) (equal (caddr s2) 1)
                  (not (consp (s-ctl s2)))
                  (equal (nth 0 (cadddr s2)) (nth 0 (cadddr s))))))
  :hints (("Goal" :induct (vcsx-run prog s k)
                  :in-theory (enable vcsx-run)
                  :expand ((vcsx-run prog s k)))))

; A COMPILED PROGRAM ON THE EXTENDED MACHINE answers what its meaning does
(defthm vcsx-correct
  (implies (and (alistp defs) (xdefs-ok defs) (xwf e 0 nil)
                (valp (mx e nil nil defs fuel)) (natp k))
           (equal (vcsx-run-program e defs (+ (sxclk e nil nil defs fuel) k))
                  (mx e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable sxgood vcsx-good sxhalted-stays vcsx-program vcsx-program-fns-ok vcsx-run-plus
                                      sx-val sx-rec sx-hyps)
                  :use ((:instance vcsx-program-fns-ok)
                        (:instance vcsx-run-plus (prog (vcsx-program e defs)) (s (list 0 0 0 nil nil))
                                   (a (sxclk e nil nil defs fuel)) (b k))
                        (:instance vcsx-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 nil nil)) (env nil)
                                   (prog (vcsx-program e defs)) (lc nil))
                        (:instance (:definition sxgood) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (vcsx-program e defs)) (lc nil))
                        (:instance (:definition sx-hyps) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (vcsx-program e defs)) (lc nil))
                        (:instance (:definition sx-val) (s (list 0 0 0 nil nil)) (r (mx e nil nil defs fuel))
                                   (s2 (vcsx-run (vcsx-program e defs) (list 0 0 0 nil nil) (sxclk e nil nil defs fuel))))
                        (:instance sxhalted-stays (prog (vcsx-program e defs))
                                   (s (vcsx-run (vcsx-program e defs) (list 0 0 0 nil nil) (sxclk e nil nil defs fuel))))
                        (:instance cagree-nth (r 0) (h 1)
                                   (a (cadddr (vcsx-run (vcsx-program e defs) (list 0 0 0 nil nil) (sxclk e nil nil defs fuel))))
                                   (b (update-nth 0 (cdr (mx e nil nil defs fuel)) nil)))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcsx-compile e 0 nil nil 0 nil))
                                   (b (cons '(:ret) (car (vcsx-defs defs (len (sxv-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcsx-program))))

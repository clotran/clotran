; clotran's VM, formally (PLAN step 28). The register machine's second
; compiler (model/vm-call-opt.lisp: operands read in place) proved
; correct on the same machine, with the same theorems as the first
; (model/vm-call-proof.lisp, whose machine lemmas this book reuses):
;
;   vm-opt-correct  compiled programs answer what the meaning does
;   vm-opt-rooted   and still do with every register above the caller's
;                   frame top wiped at each return
;
; and its clock is never more than the plain compiler's (vm-opt-faster).

(in-package "ACL2")

(include-book "vm-call-proof")
(include-book "vm-call-opt")

; an operand read in place: a local the environment has
(defun local-op-p (e n)
  (and (eq (car e) :local) (natp (cadr e)) (< (cadr e) (nfix n))))

; ---- THE CLOCK AND THE CODE'S LENGTH ------------------------------------------
;
; the plain compiler's, but an operand read in place takes no step and
; no instruction

(mutual-recursion
 (defun clk-o (e env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local) 1)
     (:if (c+ (if (local-op-p (cadr e) (len env)) 0 (clk-o (cadr e) env defs fuel))
              (c+ 1 (if (truthy (val (m (cadr e) env defs fuel)))
                        (c+ (clk-o (caddr e) env defs fuel) 1)
                      (clk-o (cadddr e) env defs fuel)))))
     (:let (c+ (clk-o (cadr e) env defs fuel)
               (clk-o (caddr e) (append env (list (val (m (cadr e) env defs fuel)))) defs fuel)))
     ((:add :lt) (c+ (if (local-op-p (cadr e) (len env)) 0 (clk-o (cadr e) env defs fuel))
                     (c+ (if (local-op-p (caddr e) (len env)) 0 (clk-o (caddr e) env defs fuel)) 1)))
     (:call (if (zp fuel)
                (clk-o-args (cddr e) env defs fuel)
              (c+ (clk-o-args (cddr e) env defs fuel)
                  (c+ 1 (c+ (clk-o (cadr (cdr (assoc-equal (cadr e) defs)))
                                   (val (m-args (cddr e) env defs fuel)) defs (1- fuel))
                            1)))))
     (otherwise 1)))
 (defun clk-o-args (es env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (c+ (clk-o (car es) env defs fuel) (clk-o-args (cdr es) env defs fuel)))))

(defthm natp-clk-o
  (natp (clk-o e env defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((clk-o e env defs fuel))))
  :rule-classes :type-prescription)
(defthm natp-clk-o-args
  (natp (clk-o-args es env defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((clk-o-args es env defs fuel))))
  :rule-classes :type-prescription)

(mutual-recursion
 (defun code-len-o (e n)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local) 1)
     (:if (+ (if (local-op-p (cadr e) n) 0 (code-len-o (cadr e) n))
             1 (code-len-o (caddr e) n) 1 (code-len-o (cadddr e) n)))
     (:let (+ (code-len-o (cadr e) n) (code-len-o (caddr e) (1+ (nfix n)))))
     ((:add :lt) (+ (if (local-op-p (cadr e) n) 0 (code-len-o (cadr e) n))
                    (if (local-op-p (caddr e) n) 0 (code-len-o (caddr e) n)) 1))
     (:call (+ (code-len-o-args (cddr e) n) 1))
     (otherwise 1)))
 (defun code-len-o-args (es n)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (code-len-o (car es) n) (code-len-o-args (cdr es) n)))))

(defthm in-place-is
  (equal (in-place e cenv)
         (if (local-op-p e (len cenv)) (nfix (nth (cadr e) cenv)) nil)))
(in-theory (disable in-place))

(defun vco-ind (flg e d f cenv pc fnpcs)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          (list d f cenv pc fnpcs)
        (list (vco-ind :m (car e) f (1+ f) cenv pc fnpcs)
              (vco-ind :args (cdr e) d (1+ f) cenv
                       (+ pc (len (vm-compile-o (car e) f (1+ f) cenv pc fnpcs))) fnpcs)))
    (case (car e)
      (:if (let* ((cc (if (in-place (cadr e) cenv) nil (vm-compile-o (cadr e) f (1+ f) cenv pc fnpcs)))
                  (pc1 (+ pc (len cc) 1))
                  (tc (vm-compile-o (caddr e) d f cenv pc1 fnpcs))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (vco-ind :m (cadr e) f (1+ f) cenv pc fnpcs)
                   (vco-ind :m (caddr e) d f cenv pc1 fnpcs)
                   (vco-ind :m (cadddr e) d f cenv pc2 fnpcs))))
      (:let (let ((ic (vm-compile-o (cadr e) f (1+ f) cenv pc fnpcs)))
              (list (vco-ind :m (cadr e) f (1+ f) cenv pc fnpcs)
                    (vco-ind :m (caddr e) d (1+ f) (append cenv (list f)) (+ pc (len ic)) fnpcs))))
      ((:add :lt) (let ((ac (if (in-place (cadr e) cenv) nil (vm-compile-o (cadr e) f (1+ f) cenv pc fnpcs))))
                    (list (vco-ind :m (cadr e) f (1+ f) cenv pc fnpcs)
                          (vco-ind :m (caddr e) (1+ f) (+ 2 f) cenv (+ pc (len ac)) fnpcs))))
      (:call (vco-ind :args (cddr e) d f cenv pc fnpcs))
      (otherwise (list d f cenv pc fnpcs)))))

(defthm len-vm-compile-o-flag
  (if (eq flg :args)
      (equal (len (vm-compile-args-o e f cenv pc fnpcs)) (code-len-o-args e (len cenv)))
    (equal (len (vm-compile-o e d f cenv pc fnpcs)) (code-len-o e (len cenv))))
  :rule-classes nil
  :hints (("Goal" :induct (vco-ind flg e d f cenv pc fnpcs))))

(defthm len-vm-compile-o
  (equal (len (vm-compile-o e d f cenv pc fnpcs)) (code-len-o e (len cenv)))
  :hints (("Goal" :use ((:instance len-vm-compile-o-flag (flg :m))))))

(defthm len-vm-compile-args-o
  (equal (len (vm-compile-args-o es f cenv pc fnpcs)) (code-len-o-args es (len cenv)))
  :hints (("Goal" :use ((:instance len-vm-compile-o-flag (flg :args) (e es))))))

; ---- WHAT THE THEOREM ASSUMES, AND THE PROPERTY ------------------------------
;
; defs-ok and top-ok are the plain compiler's: reading an operand in
; place changes no register a call's frame is placed by

(defun-sk fns-ok-o (prog defs fnpcs)
  (forall name
          (implies (consp (assoc-equal name defs))
                   (and (natp (cdr (assoc-equal name fnpcs)))
                        (code-at prog (cdr (assoc-equal name fnpcs))
                                 (body-code-o (cdr (assoc-equal name defs))
                                              (cdr (assoc-equal name fnpcs)) fnpcs))))))
(in-theory (disable fns-ok-o))

(defun good3-o (e d f cenv s env defs fuel prog fnpcs top)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile-o e d f cenv (car s) fnpcs))
                (natp d) (natp f) (< d f)
                (wf3 e (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
                (defs-ok defs defs top) (fns-ok-o prog defs fnpcs)
                (or (not top) (top-ok e f top)))
           (let ((r (m e env defs fuel)) (s2 (vm-run-wiping prog s (clk-o e env defs fuel) top)))
             (implies (valp r)
                      (and (equal (car s2) (+ (car s) (code-len-o e (len env))))
                           (equal (cadr s2) (cadr s))
                           (equal (cadddr s2) (cadddr s))
                           (agree-below (caddr s2) (update-nth (+ (cadr s) d) (val r) (caddr s))
                                        (+ (cadr s) f)))))))

(defun good-args-o (es f cenv s env defs fuel prog fnpcs top)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile-args-o es f cenv (car s) fnpcs))
                (natp f)
                (wf3-args es (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
                (defs-ok defs defs top) (fns-ok-o prog defs fnpcs)
                (or (not top) (top-ok-args es f top)))
           (let ((r (m-args es env defs fuel)) (s2 (vm-run-wiping prog s (clk-o-args es env defs fuel) top)))
             (implies (valp r)
                      (and (equal (car s2) (+ (car s) (code-len-o-args es (len env))))
                           (equal (cadr s2) (cadr s))
                           (equal (cadddr s2) (cadddr s))
                           (agree-below (caddr s2) (caddr s) (+ (cadr s) f))
                           (vals-at (+ (cadr s) f) (val r) (caddr s2)))))))

; an operand's clock: none when it is read in place
(defmacro op-clk (x) `(if (local-op-p ,x (len env)) 0 (clk-o ,x env defs fuel)))

; ---- each kind of expression, given its parts --------------------------------

; a local read in place: its register, below the first free one, holds
; its value after any run that changed nothing below there
(defthm in-place-value
  (implies (and (env-ok cenv env regs fb f) (local-op-p e (len env)) (natp fb)
                (agree-below regs2 regs (+ fb f)))
           (and (equal (nth (+ fb (nth (cadr e) cenv)) regs2) (nth (cadr e) env))
                (natp (nth (cadr e) cenv))
                (< (nth (cadr e) cenv) (nfix f))))
  :hints (("Goal" :use ((:instance env-ok-local-cenv (i (cadr e)))
                        (:instance agree-nth (a regs2) (b regs) (h (+ fb f))
                                   (r (+ fb (nth (cadr e) cenv)))))
                  :in-theory (disable env-ok-local-cenv agree-nth))))

; a local's register is a natural, so never nil: an operand in place
; always has its register
(defthm env-ok-entry-true
  (implies (and (env-ok cenv env regs fb f) (natp i) (< i (len cenv)))
           (nth i cenv))
  :hints (("Goal" :use ((:instance env-ok-local-cenv)) :in-theory (disable env-ok-local-cenv))))

(defthm in-place-value-here
  (implies (and (env-ok cenv env regs fb f) (local-op-p e (len env)) (natp fb))
           (equal (nth (+ fb (nth (cadr e) cenv)) regs) (nth (cadr e) env)))
  :hints (("Goal" :use ((:instance in-place-value (regs2 regs))))))

(defthm good3-o-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :call)))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

; an operator, by where its operands are: both locals in place, one, or
; neither -- each case with only the parts it compiles

; an operator's value, and its one step over a plain state
(defun opval (op a b)
  (if (eq op :add) (+ (fix a) (fix b)) (bool (< (rfix a) (rfix b)))))

(defthm binop-step
  (implies (and (statep s1) (member-equal op '(:add :lt))
                (code-at prog (car s1) (list (list op d ra rb)))
                (natp d) (natp ra) (natp rb))
           (equal (w-step prog s1 top)
                  (list (1+ (car s1)) (cadr s1)
                        (update-nth (+ (cadr s1) d)
                                    (opval op (nth (+ (cadr s1) ra) (caddr s1)) (nth (+ (cadr s1) rb) (caddr s1)))
                                    (caddr s1))
                        (cadddr s1))))
  :hints (("Goal" :cases ((equal op :add)))))

(defthm m-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (valp (m (cadr e) env defs fuel)) (valp (m (caddr e) env defs fuel)))
           (equal (m e env defs fuel)
                  (cons :val (opval (car e) (val (m (cadr e) env defs fuel)) (val (m (caddr e) env defs fuel))))))
  :hints (("Goal" :expand ((m e env defs fuel)))))

(defthm m-local
  (implies (equal (car e) :local)
           (equal (m e env defs fuel) (cons :val (nth (nfix (cadr e)) env))))
  :hints (("Goal" :expand ((m e env defs fuel)))))

; the operator's last step over plain variables: one operand in a
; register below f that nothing changed (va), the other just computed
; into its temporary (vb at f+1, or at f with the first at ra)
(defthm binop-tail
  (implies (and (statep s) (statep s1) (member-equal op '(:add :lt))
                (natp d) (natp f) (< d f) (natp ra) (natp rb)
                (equal (cadr s1) (cadr s)) (equal (cadddr s1) (cadddr s))
                (equal (nth (+ (cadr s) ra) (caddr s1)) va)
                (equal (nth (+ (cadr s) rb) (caddr s1)) vb)
                (agree-below (caddr s1) (caddr s) (+ (cadr s) f))
                (code-at prog (car s1) (list (list op d ra rb))))
           (let ((s2 (w-step prog s1 top)))
             (and (statep s2) (equal (car s2) (1+ (car s1))) (equal (cadr s2) (cadr s))
                  (equal (cadddr s2) (cadddr s))
                  (agree-below (caddr s2) (update-nth (+ (cadr s) d) (opval op va vb) (caddr s))
                               (+ (cadr s) f)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :use ((:instance binop-step)
                        (:instance agree-below-same-write (a (caddr s1)) (b (caddr s))
                                   (d (+ (cadr s) d)) (h (+ (cadr s) f))
                                   (v (opval op va vb)))))))

(defthm good3-o-let
  (implies (and (equal (car e) :let)
                (good3-o (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3-o (caddr e) d (1+ f) (append cenv (list f))
                         (vm-run-wiping prog s (clk-o (cadr e) env defs fuel) top)
                         (append env (list (cdr (m (cadr e) env defs fuel)))) defs fuel prog fnpcs top))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile-o e d f cenv (car s) fnpcs)))))

(defthm env-ok-entry-number
  (implies (and (env-ok cenv env regs fb f) (natp i) (< i (len cenv)))
           (and (acl2-numberp (nth i cenv)) (natp (nth i cenv))))
  :hints (("Goal" :use ((:instance env-ok-local-cenv)) :in-theory (disable env-ok-local-cenv))))

(defthm local-op-p-fc
  (implies (local-op-p e n)
           (and (equal (car e) :local) (natp (cadr e)) (< (cadr e) (nfix n))))
  :rule-classes :forward-chaining)

(defthm local-op-p-len-fc
  (implies (local-op-p e (len x))
           (and (natp (cadr e)) (< (cadr e) (len x))))
  :rule-classes :forward-chaining)

; an operator with a value has operands with values
(defthm m-binop-valp
  (implies (and (member-equal (car e) '(:add :lt)) (equal (car (m e env defs fuel)) :val))
           (and (equal (car (m (cadr e) env defs fuel)) :val)
                (equal (car (m (caddr e) env defs fuel)) :val)))
  :hints (("Goal" :expand ((m e env defs fuel)))))

; ---- AN OPERAND: in place, or compiled into its temporary ----------------
;
; either way its value ends in register (op-reg x), at or below f, and
; nothing below f changes -- the one fact the operator and the test use.
; Functions, kept closed, so the cases do not multiply in every term.

(defun op-reg (x cenv f) (if (local-op-p x (len cenv)) (nfix (nth (cadr x) cenv)) f))
(defun op-code (x f cenv pc fnpcs)
  (if (local-op-p x (len cenv)) nil (vm-compile-o x f (1+ f) cenv pc fnpcs)))
(defun op-len (x n) (if (local-op-p x n) 0 (code-len-o x n)))
(defun op-clk-f (x env defs fuel) (if (local-op-p x (len env)) 0 (clk-o x env defs fuel)))

(defthm len-op-code
  (equal (len (op-code x f cenv pc fnpcs)) (op-len x (len cenv))))

; an operator's code, clock and length, in its operands' terms
(defthm vm-compile-o-binop
  (implies (member-equal (car e) '(:add :lt))
           (equal (vm-compile-o e d f cenv pc fnpcs)
                  (append (op-code (cadr e) f cenv pc fnpcs)
                          (op-code (caddr e) (1+ f) cenv (+ pc (op-len (cadr e) (len cenv))) fnpcs)
                          (list (list (car e) d (op-reg (cadr e) cenv f) (op-reg (caddr e) cenv (1+ f)))))))
  :hints (("Goal" :expand ((vm-compile-o e d f cenv pc fnpcs)))))

(defthm clk-o-binop
  (implies (member-equal (car e) '(:add :lt))
           (equal (clk-o e env defs fuel)
                  (c+ (op-clk-f (cadr e) env defs fuel) (c+ (op-clk-f (caddr e) env defs fuel) 1))))
  :hints (("Goal" :expand ((clk-o e env defs fuel)))))

(defthm code-len-o-binop
  (implies (member-equal (car e) '(:add :lt))
           (equal (code-len-o e n) (+ (op-len (cadr e) n) (op-len (caddr e) n) 1)))
  :hints (("Goal" :expand ((code-len-o e n)))))

; what an operand's code needs, and what it leaves
(defun op-pre (x f cenv s env defs prog fnpcs top)
  (and (statep s)
       (code-at prog (car s) (op-code x f cenv (car s) fnpcs))
       (natp f)
       (wf3 x (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
       (defs-ok defs defs top) (fns-ok-o prog defs fnpcs)
       (or (not top) (top-ok x (1+ f) top))))

(defun op-post (x f cenv s env defs fuel prog top)
  (let ((r (m x env defs fuel)) (s2 (vm-run-wiping prog s (op-clk-f x env defs fuel) top)))
    (and (statep s2)
         (equal (car s2) (+ (car s) (op-len x (len env))))
         (equal (cadr s2) (cadr s))
         (equal (cadddr s2) (cadddr s))
         (agree-below (caddr s2) (caddr s) (+ (cadr s) f))
         (natp (op-reg x cenv f)) (<= (op-reg x cenv f) f)
         (equal (nth (+ (cadr s) (op-reg x cenv f)) (caddr s2)) (val r)))))

(defun good-op (x f cenv s env defs fuel prog fnpcs top)
  (implies (and (op-pre x f cenv s env defs prog fnpcs top) (valp (m x env defs fuel)))
           (op-post x f cenv s env defs fuel prog top)))

(defthm good-op-from
  (implies (or (local-op-p x (len env)) (good3-o x f (1+ f) cenv s env defs fuel prog fnpcs top))
           (good-op x f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (e/d (op-reg op-code op-len op-clk-f) (nth update-nth))
                  :cases ((local-op-p x (len env)))
                  :use ((:instance env-ok-local-cenv (i (cadr x)) (regs (caddr s)) (fb (cadr s)))))))

(in-theory (disable op-reg op-code op-len op-clk-f))

; ---- the operator, from its operands ------------------------------------------

(defmacro bo-s1 () '(vm-run-wiping prog s (op-clk-f (cadr e) env defs fuel) top))
(defmacro bo-s2 () '(vm-run-wiping prog (bo-s1) (op-clk-f (caddr e) env defs fuel) top))

; the operator's hypotheses, as good3-o states them
(defmacro bo-hyps ()
  '(and (member-equal (car e) '(:add :lt))
        (statep s)
        (code-at prog (car s) (vm-compile-o e d f cenv (car s) fnpcs))
        (natp d) (natp f) (< d f)
        (wf3 e (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
        (defs-ok defs defs top) (fns-ok-o prog defs fnpcs)
        (or (not top) (top-ok e f top))))

; an operator's parts are well formed and under top when it is
(defthm wf3-binop-parts
  (implies (and (member-equal (car e) '(:add :lt)) (wf3 e n defs))
           (and (wf3 (cadr e) n defs) (wf3 (caddr e) n defs)))
  :hints (("Goal" :expand ((wf3 e n defs)))))

(defthm top-ok-binop-parts
  (implies (and (member-equal (car e) '(:add :lt)) (top-ok e f top) (natp f))
           (and (top-ok (cadr e) (1+ f) top) (top-ok (caddr e) (+ 2 f) top)))
  :hints (("Goal" :expand ((top-ok e f top)))))

; the first operand can run
(defthm bo-pre-a
  (implies (bo-hyps) (op-pre (cadr e) f cenv s env defs prog fnpcs top))
  :hints (("Goal" :expand ((wf3 e (len env) defs) (top-ok e f top)))))

; once it has, the second can
(defthm bo-pre-b
  (implies (and (bo-hyps) (op-post (cadr e) f cenv s env defs fuel prog top))
           (op-pre (caddr e) (1+ f) cenv (bo-s1) env defs prog fnpcs top))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable op-code m m-args clk-o clk-o-args vm-compile-o vm-compile-args-o
                                      code-len-o code-len-o-args wf3 wf3-args top-ok top-ok-args
                                      local-op-p nth update-nth)
                  :use ((:instance env-ok-after-args (regs (caddr s)) (fb (cadr s))
                                   (regs1 (caddr (bo-s1))))
                        (:instance env-ok-bigger-f (regs (caddr (bo-s1))) (fb (cadr s)) (g (1+ f)))))))

; both done: the operator's step, and what good3-o concludes
(defthm bo-post
  (implies (and (bo-hyps)
                (op-post (cadr e) f cenv s env defs fuel prog top)
                (op-post (caddr e) (1+ f) cenv (bo-s1) env defs fuel prog top)
                (valp (m (cadr e) env defs fuel)) (valp (m (caddr e) env defs fuel)))
           (let ((s3 (vm-run-wiping prog s (clk-o e env defs fuel) top)))
             (and (equal (car s3) (+ (car s) (code-len-o e (len env))))
                  (equal (cadr s3) (cadr s))
                  (equal (cadddr s3) (cadddr s))
                  (agree-below (caddr s3)
                               (update-nth (+ (cadr s) d)
                                           (opval (car e) (cdr (m (cadr e) env defs fuel))
                                                  (cdr (m (caddr e) env defs fuel)))
                                           (caddr s))
                               (+ (cadr s) f)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable nth update-nth opval agree-below-sym agree-nth agree-below-smaller
                                      agree-below-trans op-code m m-args clk-o clk-o-args vm-compile-o
                                      vm-compile-args-o code-len-o code-len-o-args wf3 wf3-args top-ok
                                      top-ok-args local-op-p)
                  :use ((:instance agree-below-smaller (a (caddr (bo-s2))) (b (caddr (bo-s1)))
                                   (h (+ 1 f (cadr s))) (g (+ f (cadr s))))
                        (:instance agree-below-trans (a (caddr (bo-s2))) (b (caddr (bo-s1))) (c (caddr s))
                                   (h (+ f (cadr s))))
                        (:instance agree-nth (a (caddr (bo-s2))) (b (caddr (bo-s1))) (h (+ 1 f (cadr s)))
                                   (r (+ (cadr s) (op-reg (cadr e) cenv f))))
                        (:instance binop-tail (op (car e)) (s1 (bo-s2))
                                   (ra (op-reg (cadr e) cenv f)) (rb (op-reg (caddr e) cenv (1+ f)))
                                   (va (cdr (m (cadr e) env defs fuel))) (vb (cdr (m (caddr e) env defs fuel))))))))

(in-theory (disable op-pre op-post))

(defthm good3-o-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (good3-o (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3-o (caddr e) (1+ f) (+ 2 f) cenv (bo-s1) env defs fuel prog fnpcs top))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable good-op good3-o good-op-from bo-pre-a bo-pre-b bo-post)
                  :use ((:instance (:definition good3-o))
                        (:instance bo-pre-a)
                        (:instance bo-pre-b)
                        (:instance bo-post)
                        (:instance good-op-from (x (cadr e)))
                        (:instance good-op-from (x (caddr e)) (f (1+ f)) (s (bo-s1)))
                        (:instance (:definition good-op) (x (cadr e)))
                        (:instance (:definition good-op) (x (caddr e)) (f (1+ f)) (s (bo-s1)))
                        (:instance m-binop-valp)
                        (:instance m-binop)))))

; an operand's postcondition, read off by rewriting
(defthm op-post-facts
  (implies (op-post x f cenv s env defs fuel prog top)
           (let ((s2 (vm-run-wiping prog s (op-clk-f x env defs fuel) top)))
             (and (statep s2)
                  (equal (car s2) (+ (car s) (op-len x (len env))))
                  (equal (cadr s2) (cadr s))
                  (equal (cadddr s2) (cadddr s))
                  (agree-below (caddr s2) (caddr s) (+ (cadr s) f))
                  (natp (op-reg x cenv f)) (<= (op-reg x cenv f) f)
                  (equal (nth (+ (cadr s) (op-reg x cenv f)) (caddr s2)) (val (m x env defs fuel))))))
  :hints (("Goal" :in-theory (enable op-post))))

; ---- if, its test in place or computed ------------------------------------------

(defthm vm-compile-o-if
  (implies (equal (car e) :if)
           (equal (vm-compile-o e d f cenv pc fnpcs)
                  (let* ((cc (op-code (cadr e) f cenv pc fnpcs))
                         (pc1 (+ pc (op-len (cadr e) (len cenv)) 1))
                         (tc (vm-compile-o (caddr e) d f cenv pc1 fnpcs))
                         (pc2 (+ pc1 (code-len-o (caddr e) (len cenv)) 1))
                         (ec (vm-compile-o (cadddr e) d f cenv pc2 fnpcs)))
                    (append cc (list (list :jmpf (op-reg (cadr e) cenv f) pc2)) tc
                            (list (list :jmp (+ pc2 (code-len-o (cadddr e) (len cenv))))) ec))))
  :hints (("Goal" :expand ((vm-compile-o e d f cenv pc fnpcs))
                  :in-theory (enable op-code op-len op-reg))))

(defthm clk-o-if
  (implies (equal (car e) :if)
           (equal (clk-o e env defs fuel)
                  (c+ (op-clk-f (cadr e) env defs fuel)
                      (c+ 1 (if (truthy (val (m (cadr e) env defs fuel)))
                                (c+ (clk-o (caddr e) env defs fuel) 1)
                              (clk-o (cadddr e) env defs fuel))))))
  :hints (("Goal" :expand ((clk-o e env defs fuel)) :in-theory (enable op-clk-f))))

(defthm code-len-o-if
  (implies (equal (car e) :if)
           (equal (code-len-o e n)
                  (+ (op-len (cadr e) n) 1 (code-len-o (caddr e) n) 1 (code-len-o (cadddr e) n))))
  :hints (("Goal" :expand ((code-len-o e n)) :in-theory (enable op-len))))

(defthm wf3-if-parts
  (implies (and (equal (car e) :if) (wf3 e n defs))
           (and (wf3 (cadr e) n defs) (wf3 (caddr e) n defs) (wf3 (cadddr e) n defs)))
  :hints (("Goal" :expand ((wf3 e n defs)))))

(defthm top-ok-if-parts
  (implies (and (equal (car e) :if) (top-ok e f top) (natp f))
           (and (top-ok (cadr e) (1+ f) top) (top-ok (caddr e) f top) (top-ok (cadddr e) f top)))
  :hints (("Goal" :expand ((top-ok e f top)))))

(defthm m-if-valp
  (implies (and (equal (car e) :if) (equal (car (m e env defs fuel)) :val))
           (equal (car (m (cadr e) env defs fuel)) :val))
  :hints (("Goal" :expand ((m e env defs fuel)))))

(defthm m-if-value
  (implies (and (equal (car e) :if) (equal (car (m (cadr e) env defs fuel)) :val))
           (equal (m e env defs fuel)
                  (if (truthy (cdr (m (cadr e) env defs fuel)))
                      (m (caddr e) env defs fuel)
                    (m (cadddr e) env defs fuel))))
  :hints (("Goal" :expand ((m e env defs fuel)))))

(defmacro if-hyps ()
  '(and (equal (car e) :if)
        (statep s)
        (code-at prog (car s) (vm-compile-o e d f cenv (car s) fnpcs))
        (natp d) (natp f) (< d f)
        (wf3 e (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
        (defs-ok defs defs top) (fns-ok-o prog defs fnpcs)
        (or (not top) (top-ok e f top))))

(defthm if-pre-c
  (implies (if-hyps) (op-pre (cadr e) f cenv s env defs prog fnpcs top))
  :hints (("Goal" :do-not-induct t :in-theory (enable op-pre))))

(defmacro if-s2 () '(w-step prog (vm-run-wiping prog s (op-clk-f (cadr e) env defs fuel) top) top))

(defthm good3-o-if-true
  (implies (and (equal (car e) :if)
                (truthy (cdr (m (cadr e) env defs fuel)))
                (good-op (cadr e) f cenv s env defs fuel prog fnpcs top)
                (good3-o (caddr e) d f cenv (if-s2) env defs fuel prog fnpcs top))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (op-post)
                                  (nth update-nth m m-args clk-o clk-o-args vm-compile-o vm-compile-args-o
                                   code-len-o code-len-o-args wf3 wf3-args top-ok top-ok-args local-op-p
                                   if-pre-c agree-below-sym op-post-facts))
                  :use ((:instance if-pre-c)
                        (:instance m-if-valp)
                        (:instance m-if-value)
                        (:instance env-ok-after-args (regs (caddr s)) (fb (cadr s))
                                   (regs1 (caddr (vm-run-wiping prog s (op-clk-f (cadr e) env defs fuel) top))))))))

(defthm good3-o-if-false
  (implies (and (equal (car e) :if)
                (not (truthy (cdr (m (cadr e) env defs fuel))))
                (good-op (cadr e) f cenv s env defs fuel prog fnpcs top)
                (good3-o (cadddr e) d f cenv (if-s2) env defs fuel prog fnpcs top))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (op-post)
                                  (nth update-nth m m-args clk-o clk-o-args vm-compile-o vm-compile-args-o
                                   code-len-o code-len-o-args wf3 wf3-args top-ok top-ok-args local-op-p
                                   if-pre-c agree-below-sym op-post-facts))
                  :use ((:instance if-pre-c)
                        (:instance m-if-valp)
                        (:instance m-if-value)
                        (:instance env-ok-after-args (regs (caddr s)) (fb (cadr s))
                                   (regs1 (caddr (vm-run-wiping prog s (op-clk-f (cadr e) env defs fuel) top))))))))

(defthm good3-o-if
  (implies (and (equal (car e) :if)
                (good3-o (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3-o (caddr e) d f cenv (if-s2) env defs fuel prog fnpcs top)
                (good3-o (cadddr e) d f cenv (if-s2) env defs fuel prog fnpcs top))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :cases ((truthy (cdr (m (cadr e) env defs fuel))))
                  :in-theory (disable good3-o good-op good-op-from)
                  :use ((:instance good-op-from (x (cadr e)))))))

; ---- a call's arguments -----------------------------------------------------------

(defthm good-args-o-nil
  (implies (atom es) (good-args-o es f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good-args-o-cons
  (implies (and (consp es)
                (good3-o (car es) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good-args-o (cdr es) (1+ f) cenv (vm-run-wiping prog s (clk-o (car es) env defs fuel) top)
                             env defs fuel prog fnpcs top))
           (good-args-o es f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile-args-o es f cenv (car s) fnpcs)
                           (m-args es env defs fuel)
                           (vals-at (+ (cadr s) f) (val (m-args es env defs fuel))
                                    (caddr (vm-run-wiping prog s (clk-o-args es env defs fuel) top)))))))

; ---- a call ---------------------------------------------------------------------

(defthm len-count-from
  (implies (and (natp i) (natp n)) (equal (len (count-from i n)) (nfix (- n i))))
  :hints (("Goal" :induct (count-from i n))))

(defthm call-abstract-o
  (implies (and (statep s1) (natp d) (natp f) (< d f) (natp entry) (equal (len vs) n) (equal k n)
                (vals-at (+ (cadr s1) f) vs (caddr s1))
                (code-at prog (car s1) (list (list :call d entry f k (+ f k))))
                (code-at prog entry (vm-compile-o body n (1+ n) (count-from 0 n) entry fnpcs))
                (code-at prog (+ entry (code-len-o body n)) (list (list :ret n)))
                (wf3 body n defs) (defs-ok defs defs top) (fns-ok-o prog defs fnpcs)
                (or (not top) (top-ok body (1+ n) top))
                (or (not top) (<= f (nfix top)))
                (good3-o body n (1+ n) (count-from 0 n) (w-step prog s1 top) vs defs fuel2 prog fnpcs top)
                (valp (m body vs defs fuel2)))
           (let ((s4 (w-step prog (vm-run-wiping prog (w-step prog s1 top) (clk-o body vs defs fuel2) top) top)))
             (and (statep s4)
                  (equal (car s4) (+ 1 (car s1))) (equal (cadr s4) (cadr s1))
                  (equal (cadddr s4) (cadddr s1))
                  (agree-below (caddr s4) (update-nth (+ (cadr s1) d) (val (m body vs defs fuel2)) (caddr s1))
                               (+ (cadr s1) f)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth call-tail env-ok-callee good3-o m m-args clk-o clk-o-args
                                      vm-compile-o code-len-o wf3 top-ok defs-ok copy-args count-from
                                      vals-at env-ok)
                  :use ((:instance (:definition good3-o) (e body) (d (len vs)) (f (1+ (len vs)))
                                   (cenv (count-from 0 (len vs)))
                                   (s (w-step prog s1 top)) (env vs) (fuel fuel2))
                        (:instance env-ok-callee (fb (cadr s1)) (a f) (nb (+ f (len vs))) (regs (caddr s1)))
                        (:instance call-tail (n (len vs)) (r0 (caddr s1)) (pc3 (+ entry (code-len-o body (len vs))))
                                   (s3 (vm-run-wiping prog (w-step prog s1 top) (clk-o body vs defs fuel2) top))
                                   (v (val (m body vs defs fuel2))))))))

(defmacro co-def () '(cdr (assoc-equal (cadr e) defs)))
(defmacro co-entry () '(cdr (assoc-equal (cadr e) fnpcs)))
(defmacro co-vs () '(val (m-args (cddr e) env defs fuel)))
(defmacro co-s1 () '(vm-run-wiping prog s (clk-o-args (cddr e) env defs fuel) top))

(defthm good3-o-call
  (implies (and (equal (car e) :call)
                (good-args-o (cddr e) f cenv s env defs fuel prog fnpcs top)
                (good3-o (cadr (co-def)) (nfix (car (co-def))) (1+ (nfix (car (co-def))))
                         (count-from 0 (nfix (car (co-def))))
                         (w-step prog (co-s1) top)
                         (co-vs) defs (1- fuel) prog fnpcs top))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth good3-o good-args-o body-code-o)
                  :expand ((vm-compile-o e d f cenv (car s) fnpcs) (m e env defs fuel) (clk-o e env defs fuel)
                           (code-len-o e (len env)) (wf3 e (len env) defs) (top-ok e f top)
                           (body-code-o (co-def) (co-entry) fnpcs))
                  :use ((:instance (:definition good3-o))
                        (:instance (:definition good-args-o) (es (cddr e)))
                        (:instance fns-ok-o-necc (name (cadr e)))
                        (:instance defs-ok-lookup (ds defs) (name (cadr e)))
                        (:instance call-abstract-o (s1 (co-s1)) (vs (co-vs)) (n (nfix (car (co-def))))
                                   (k (len (cddr e)))
                                   (entry (co-entry)) (body (cadr (co-def))) (fuel2 (1- fuel)))))))

(defthm good3-o-call-no-fuel
  (implies (and (equal (car e) :call) (zp fuel))
           (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :expand ((m e env defs fuel)))))

; ---- THE THEOREM --------------------------------------------------------------------

(defun ind3-o (flg e d f cenv s env defs fuel prog fnpcs top)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o<
                  :ruler-extenders :all
                  :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list d f cenv s env defs fuel prog fnpcs top)
        (list (ind3-o :m (car e) f (1+ f) cenv s env defs fuel prog fnpcs top)
              (ind3-o :args (cdr e) d (1+ f) cenv (vm-run-wiping prog s (clk-o (car e) env defs fuel) top)
                      env defs fuel prog fnpcs top)))
    (case (car e)
      (:if (list (ind3-o :m (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                 (ind3-o :m (caddr e) d f cenv (if-s2) env defs fuel prog fnpcs top)
                 (ind3-o :m (cadddr e) d f cenv (if-s2) env defs fuel prog fnpcs top)))
      (:let (list (ind3-o :m (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                  (ind3-o :m (caddr e) d (1+ f) (append cenv (list f))
                          (vm-run-wiping prog s (clk-o (cadr e) env defs fuel) top)
                          (append env (list (cdr (m (cadr e) env defs fuel)))) defs fuel prog fnpcs top)))
      ((:add :lt) (list (ind3-o :m (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                        (ind3-o :m (caddr e) (1+ f) (+ 2 f) cenv (bo-s1) env defs fuel prog fnpcs top)))
      (:call (list (ind3-o :args (cddr e) d f cenv s env defs fuel prog fnpcs top)
                   (if (zp fuel)
                       nil
                     (ind3-o :m (cadr (co-def)) (nfix (car (co-def))) (1+ (nfix (car (co-def))))
                             (count-from 0 (nfix (car (co-def))))
                             (w-step prog (co-s1) top)
                             (co-vs) defs (1- fuel) prog fnpcs top))))
      (otherwise (list d f cenv s env defs fuel prog fnpcs top)))))

(defthm vm-opt-correct-flag
  (if (eq flg :args)
      (good-args-o e f cenv s env defs fuel prog fnpcs top)
    (good3-o e d f cenv s env defs fuel prog fnpcs top))
  :rule-classes nil
  :hints (("Goal" :induct (ind3-o flg e d f cenv s env defs fuel prog fnpcs top)
                  :in-theory (union-theories '(good3-o-if good3-o-let good3-o-binop good3-o-call good3-o-call-no-fuel
                                               good3-o-leaf good-args-o-nil good-args-o-cons
                                               member-equal car-cons cdr-cons
                                               (:induction ind3-o))
                                             (theory 'minimal-theory)))))

(defthm vm-opt-good
  (good3-o e d f cenv s env defs fuel prog fnpcs top)
  :hints (("Goal" :use ((:instance vm-opt-correct-flag (flg :m))))))

; ---- WHOLE PROGRAMS -------------------------------------------------------------------

(defthm len-body-code-o
  (equal (len (body-code-o def pc fnpcs)) (1+ (code-len-o (cadr def) (nfix (car def))))))

(defthm lay-out-o-any-fnpcs
  (implies (and (syntaxp (not (equal y ''nil))) (alistp ds))
           (equal (lay-out-o ds pc y) (lay-out-o ds pc nil)))
  :hints (("Goal" :in-theory (enable body-code-o))))

(defthm compile-defs-o-places
  (implies (and (alistp ds) (natp pc) (code-at prog pc (compile-defs-o ds fnpcs pc))
                (consp (assoc-equal name ds)))
           (and (natp (cdr (assoc-equal name (lay-out-o ds pc nil))))
                (code-at prog (cdr (assoc-equal name (lay-out-o ds pc nil)))
                         (body-code-o (cdr (assoc-equal name ds))
                                      (cdr (assoc-equal name (lay-out-o ds pc nil))) fnpcs))))
  :hints (("Goal" :induct (compile-defs-o ds fnpcs pc) :in-theory (disable body-code-o))))

(defthm compile-program-o-fns-ok
  (implies (alistp defs)
           (fns-ok-o (compile-program-o e defs) defs
                     (lay-out-o defs (1+ (code-len-o e 0)) nil)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fns-ok-o) (vm-compile-o vm-compile-args-o code-len-o code-len-o-args
                                              body-code-o compile-defs-o-places))
                  :use ((:instance compile-defs-o-places
                                   (ds defs) (pc (1+ (code-len-o e 0)))
                                   (prog (compile-program-o e defs))
                                   (fnpcs (lay-out-o defs (1+ (code-len-o e 0)) nil))
                                   (name (fns-ok-o-witness (compile-program-o e defs) defs
                                                           (lay-out-o defs (1+ (code-len-o e 0)) nil))))
                        (:instance code-at-shift (pc 1)
                                   (a (vm-compile-o e 0 1 nil 0 (lay-out-o defs (1+ (code-len-o e 0)) nil)))
                                   (b (cons '(:ret 0)
                                            (compile-defs-o defs (lay-out-o defs (1+ (code-len-o e 0)) nil)
                                                            (1+ (code-len-o e 0)))))
                                   (code (compile-defs-o defs (lay-out-o defs (1+ (code-len-o e 0)) nil)
                                                         (1+ (code-len-o e 0)))))))))

(defthm program-answer-o
  (implies (and (alistp defs) (defs-ok defs defs top) (wf3 e 0 defs)
                (or (not top) (top-ok e 1 top))
                (valp (m e nil defs fuel)) (natp k))
           (equal (answer (vm-run-wiping (compile-program-o e defs) (list 0 0 nil nil)
                                         (+ (clk-o e nil defs fuel) k) top))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable good3-o vm-opt-good halted-stays compile-program-o compile-program-o-fns-ok
                                      run-plus)
                  :use ((:instance compile-program-o-fns-ok)
                        (:instance run-plus (prog (compile-program-o e defs)) (s (list 0 0 nil nil))
                                   (a (clk-o e nil defs fuel)) (b k))
                        (:instance vm-opt-good (d 0) (f 1) (cenv nil) (s (list 0 0 nil nil)) (env nil)
                                   (prog (compile-program-o e defs))
                                   (fnpcs (lay-out-o defs (1+ (code-len-o e 0)) nil)))
                        (:instance (:definition good3-o) (d 0) (f 1) (cenv nil) (s (list 0 0 nil nil)) (env nil)
                                   (prog (compile-program-o e defs))
                                   (fnpcs (lay-out-o defs (1+ (code-len-o e 0)) nil)))
                        (:instance halted-stays (prog (compile-program-o e defs))
                                   (s (vm-run-wiping (compile-program-o e defs) (list 0 0 nil nil)
                                                     (clk-o e nil defs fuel) top)))
                        (:instance agree-nth (r 0) (h 1)
                                   (a (caddr (vm-run-wiping (compile-program-o e defs) (list 0 0 nil nil)
                                                            (clk-o e nil defs fuel) top)))
                                   (b (update-nth 0 (cdr (m e nil defs fuel)) nil)))
                        (:instance code-at-shift (pc 0)
                                   (a (vm-compile-o e 0 1 nil 0 (lay-out-o defs (1+ (code-len-o e 0)) nil)))
                                   (b (cons '(:ret 0)
                                            (compile-defs-o defs (lay-out-o defs (1+ (code-len-o e 0)) nil)
                                                            (1+ (code-len-o e 0)))))
                                   (code '((:ret 0))))))
          ("Goal'" :in-theory (enable compile-program-o))))

; THE SECOND COMPILER: a compiled program, operands read in place, calls
; and recursion included, answers what its meaning does
(defthm vm-opt-correct
  (implies (and (alistp defs) (defs-ok defs defs nil) (wf3 e 0 defs)
                (valp (m e nil defs fuel)) (natp k))
           (equal (answer (vm-run (compile-program-o e defs) (list 0 0 nil nil) (+ (clk-o e nil defs fuel) k)))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable program-answer-o compile-program-o)
                  :use ((:instance program-answer-o (top nil))))))

; ROOTING: the same answer with every register above the caller's frame
; top wiped at each return
(defthm vm-opt-rooted
  (implies (and (alistp defs) (defs-ok defs defs top) (wf3 e 0 defs) top (top-ok e 1 top)
                (valp (m e nil defs fuel)) (natp k))
           (equal (answer (vm-run-wiping (compile-program-o e defs) (list 0 0 nil nil)
                                         (+ (clk-o e nil defs fuel) k) top))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable program-answer-o compile-program-o)
                  :use ((:instance program-answer-o)))))

; ---- NEVER SLOWER -----------------------------------------------------------------
;
; the second compiler's clock is at most the first's: an operand read in
; place saves its step, and nothing costs more

(defun cl-ind (flg e env defs fuel)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list env defs fuel)
        (list (cl-ind :m (car e) env defs fuel) (cl-ind :args (cdr e) env defs fuel)))
    (case (car e)
      ((:if :add :lt) (list (cl-ind :m (cadr e) env defs fuel)
                            (cl-ind :m (caddr e) env defs fuel)
                            (cl-ind :m (cadddr e) env defs fuel)))
      (:let (list (cl-ind :m (cadr e) env defs fuel)
                  (cl-ind :m (caddr e) (append env (list (val (m (cadr e) env defs fuel)))) defs fuel)))
      (:call (list (cl-ind :args (cddr e) env defs fuel)
                   (if (zp fuel)
                       nil
                     (cl-ind :m (cadr (cdr (assoc-equal (cadr e) defs)))
                             (val (m-args (cddr e) env defs fuel)) defs (1- fuel)))))
      (otherwise (list env defs fuel)))))

(defthm clk-o-faster-flag
  (if (eq flg :args)
      (<= (clk-o-args e env defs fuel) (clk-args e env defs fuel))
    (<= (clk-o e env defs fuel) (clk e env defs fuel)))
  :rule-classes nil
  :hints (("Goal" :induct (cl-ind flg e env defs fuel)
                  :in-theory (e/d (c+ op-clk-f) (clk-o-binop clk-o-if)))))

(defthm vm-opt-faster
  (<= (clk-o e env defs fuel) (clk e env defs fuel))
  :hints (("Goal" :use ((:instance clk-o-faster-flag (flg :m))))))

; the examples meet the hypotheses (vm-call-proof checks the same defs-ok
; and top-ok; the second compiler adds none)
(assert-event (and (alistp *bench-defs*) (defs-ok *bench-defs* *bench-defs* nil)
                   (all-ok *bench-exprs* *bench-defs* nil)))

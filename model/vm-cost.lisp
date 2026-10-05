; clotran's VM, formally (PLAN step 28). The cost theorems for both
; machines (James, 2026-10-04: "not just our data structures, but also
; our algorithms follow correct big O"), by step counting:
;
;   compiling is linear     code-len e <= 3 size(e), for each compiler
;   running is linear       each machine's clock <= 2 evals, the number
;                           of evaluation steps the meaning itself takes
;                           -- recursion and every call included
;
; so a compiled program does at most a constant factor more steps than
; the language says it must, on either machine. Each step is O(1) but a
; call, which copies its n arguments (copy-args on the register machine,
; take and reverse on the stack one): the model's registers and locals
; are arrays, read and written by index, which nth and update-nth
; stand for (their list walk is the logic's, not the cost of the thing
; modelled).

(in-package "ACL2")

(include-book "vm-call-proof")
(include-book "vm-stack-proof")

; ---- THE LANGUAGE's OWN COST ------------------------------------------------
;
; evals: how many expressions the meaning evaluates -- one for each node
; m visits, a call's body once per call, at one less fuel

(mutual-recursion
 (defun evals (e env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local) 1)
     (:if (+ 1 (evals (cadr e) env defs fuel)
             (if (truthy (val (m (cadr e) env defs fuel)))
                 (evals (caddr e) env defs fuel)
               (evals (cadddr e) env defs fuel))))
     (:let (+ 1 (evals (cadr e) env defs fuel)
              (evals (caddr e) (append env (list (val (m (cadr e) env defs fuel)))) defs fuel)))
     ((:add :lt) (+ 1 (evals (cadr e) env defs fuel) (evals (caddr e) env defs fuel)))
     (:call (if (zp fuel)
                (+ 1 (evals-args (cddr e) env defs fuel))
              (+ 1 (evals-args (cddr e) env defs fuel)
                 (evals (cadr (cdr (assoc-equal (cadr e) defs)))
                        (val (m-args (cddr e) env defs fuel)) defs (1- fuel)))))
     (otherwise 1)))
 (defun evals-args (es env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (+ (evals (car es) env defs fuel) (evals-args (cdr es) env defs fuel)))))

; the meaning's own recursion, an expression or an argument list
(defun ev-ind (flg e env defs fuel)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list env defs fuel)
        (list (ev-ind :m (car e) env defs fuel) (ev-ind :args (cdr e) env defs fuel)))
    (case (car e)
      (:if (list (ev-ind :m (cadr e) env defs fuel)
                 (ev-ind :m (caddr e) env defs fuel)
                 (ev-ind :m (cadddr e) env defs fuel)))
      (:let (list (ev-ind :m (cadr e) env defs fuel)
                  (ev-ind :m (caddr e) (append env (list (val (m (cadr e) env defs fuel)))) defs fuel)))
      ((:add :lt) (list (ev-ind :m (cadr e) env defs fuel) (ev-ind :m (caddr e) env defs fuel)))
      (:call (list (ev-ind :args (cddr e) env defs fuel)
                   (if (zp fuel)
                       nil
                     (ev-ind :m (cadr (cdr (assoc-equal (cadr e) defs)))
                             (val (m-args (cddr e) env defs fuel)) defs (1- fuel)))))
      (otherwise (list env defs fuel)))))

; ---- RUNNING IS LINEAR ----------------------------------------------------------

(defthm clk-linear-flag
  (if (eq flg :args)
      (<= (clk-args e env defs fuel) (* 2 (evals-args e env defs fuel)))
    (<= (clk e env defs fuel) (* 2 (evals e env defs fuel))))
  :rule-classes nil
  :hints (("Goal" :induct (ev-ind flg e env defs fuel) :in-theory (enable c+))))

; THE REGISTER MACHINE: at most two steps per expression the meaning
; evaluates
(defthm clk-linear
  (<= (clk e env defs fuel) (* 2 (evals e env defs fuel)))
  :hints (("Goal" :use ((:instance clk-linear-flag (flg :m))))))

(defthm s-clk-linear-flag
  (if (eq flg :args)
      (<= (s-clk-args e env defs fuel) (* 2 (evals-args e env defs fuel)))
    (<= (s-clk e env defs fuel) (* 2 (evals e env defs fuel))))
  :rule-classes nil
  :hints (("Goal" :induct (ev-ind flg e env defs fuel) :in-theory (enable c+))))

; THE STACK MACHINE: the same bound
(defthm s-clk-linear
  (<= (s-clk e env defs fuel) (* 2 (evals e env defs fuel)))
  :hints (("Goal" :use ((:instance s-clk-linear-flag (flg :m))))))

; ---- COMPILING IS LINEAR ----------------------------------------------------------
;
; size: the expression's nodes

(mutual-recursion
 (defun size (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:if (+ 1 (size (cadr e)) (size (caddr e)) (size (cadddr e))))
     ((:let :add :lt) (+ 1 (size (cadr e)) (size (caddr e))))
     (:call (+ 1 (size-args (cddr e))))
     (otherwise 1)))
 (defun size-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (size (car es)) (size-args (cdr es))))))

(defun size-ind (flg e)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e) nil (list (size-ind :m (car e)) (size-ind :args (cdr e))))
    (case (car e)
      (:if (list (size-ind :m (cadr e)) (size-ind :m (caddr e)) (size-ind :m (cadddr e))))
      ((:let :add :lt) (list (size-ind :m (cadr e)) (size-ind :m (caddr e))))
      (:call (size-ind :args (cddr e)))
      (otherwise nil))))

(defthm code-len-linear-flag
  (if (eq flg :args)
      (and (<= (code-len-args e) (* 3 (size-args e)))
           (<= (s-code-len-args e) (* 3 (size-args e))))
    (and (<= (code-len e) (* 3 (size e)))
         (<= (s-code-len e) (* 3 (size e)))))
  :rule-classes nil
  :hints (("Goal" :induct (size-ind flg e))))

; BOTH COMPILERS: at most three instructions per node
(defthm code-len-linear
  (and (<= (code-len e) (* 3 (size e)))
       (<= (s-code-len e) (* 3 (size e))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance code-len-linear-flag (flg :m))))))

; and a program is its main expression and every body, one return each
(defun size-defs (defs)
  (if (atom defs) 0 (+ 1 (size (cadr (cdar defs))) (size-defs (cdr defs)))))

(defthm len-compile-defs-linear
  (<= (len (compile-defs ds fnpcs pc)) (* 3 (size-defs ds)))
  :hints (("Goal" :induct (compile-defs ds fnpcs pc))))

(defthm len-s-compile-defs-linear
  (<= (len (s-compile-defs ds fnpcs pc)) (* 3 (size-defs ds)))
  :hints (("Goal" :induct (s-compile-defs ds fnpcs pc))))

; A WHOLE PROGRAM, on either machine: linear in its main expression and
; its functions' bodies together
(defthm compile-program-linear
  (and (<= (len (compile-program e defs)) (+ 1 (* 3 (+ (size e) (size-defs defs)))))
       (<= (len (s-compile-program e defs)) (+ 1 (* 3 (+ (size e) (size-defs defs))))))
  :hints (("Goal" :in-theory (disable len-compile-defs-linear len-s-compile-defs-linear)
                  :use ((:instance len-compile-defs-linear (ds defs) (pc (1+ (code-len e)))
                                   (fnpcs (lay-out defs (1+ (code-len e)) nil)))
                        (:instance len-s-compile-defs-linear (ds defs) (pc (1+ (s-code-len e)))
                                   (fnpcs (s-lay-out defs (1+ (s-code-len e)) nil)))))))

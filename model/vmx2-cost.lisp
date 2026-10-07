; clotran's VM, formally (PLAN step 30): the cost of the machine with
; arities, primitives and throws (model/vmx2.lisp), by step counting,
; as vmx-cost.lisp's:
;
;   s2clk-linear   the clock <= 2 x2evals, the number of expressions the
;                  meaning itself evaluates -- every loop iteration, every
;                  call's body, every handler run counted; an expression a
;                  throw cut short is not
;
; A try counts twice: beside its parts it is two pieces of bookkeeping,
; the handler record pushed, and popped with the jump past the handler
; (or, on a throw, the handler's local slid out from under its value).
; A throw itself costs one step to unwind however many call records it
; passes -- unwind is one step of the machine. The Fortran owes the same:
; it keeps the nearest handler's index in the control stack, so a throw
; truncates the stack to it rather than walking the records above it.
; Walking them would make a throw cost the call depth, and this bound
; would not be what the Fortran runs.
;
; As in vmx-cost the induction proves the stronger clock + 1 <= 2
; x2evals; an argument list that answers a value has its length to
; spare, which pays for a loop's slides.

(in-package "ACL2")

(include-book "vmx2-proof")

(mutual-recursion
 (defun x2evals (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ 1 (x2evals (cadr e) env caps defs fuel)
             (if (valp (mx2 (cadr e) env caps defs fuel))
                 (if (truthy (val (mx2 (cadr e) env caps defs fuel)))
                     (x2evals (caddr e) env caps defs fuel)
                   (x2evals (cadddr e) env caps defs fuel))
               0)))
     (:let (+ 1 (x2evals (cadr e) env caps defs fuel)
              (if (valp (mx2 (cadr e) env caps defs fuel))
                  (x2evals (caddr e) (append env (list (val (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)
                0)))
     ((:add :lt) (+ 1 (x2evals (cadr e) env caps defs fuel)
                    (if (valp (mx2 (cadr e) env caps defs fuel)) (x2evals (caddr e) env caps defs fuel) 0)))
     ((:mkclo :prim) (+ 1 (x2evals-args (cddr e) env caps defs fuel)))
     (:callv (+ 1 (x2evals-args (cddr e) env caps defs fuel)
                (if (valp (mx2-args (cddr e) env caps defs fuel))
                    (+ (x2evals (cadr e) env caps defs fuel)
                       (if (and (valp (x2-rf)) (clop (val (x2-rf))) (consp (x2-cl)) (not (zp fuel)))
                           (x2evals (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel))
                         0))
                  0)))
     (:loop (+ 1 (x2evals-args (cadr e) env caps defs fuel)
               (if (valp (mx2-args (cadr e) env caps defs fuel))
                   (x2evals-loop e env (val (mx2-args (cadr e) env caps defs fuel)) caps defs fuel)
                 0)))
     (:recur (+ 1 (x2evals-args (cdr e) env caps defs fuel)))
     (:throw (+ 1 (x2evals (cadr e) env caps defs fuel)))
     (:try (+ 2 (x2evals (cadr e) env caps defs fuel)
              (if (thrownp (mx2 (cadr e) env caps defs fuel))
                  (x2evals (caddr e) (append env (list (cdr (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)
                0)))
     (otherwise 1)))
 (defun x2evals-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1))))
   (if (atom es)
       0
     (+ (x2evals (car es) env caps defs fuel)
        (if (valp (mx2 (car es) env caps defs fuel)) (x2evals-args (cdr es) env caps defs fuel) 0))))
 (defun x2evals-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0))))
   (cond ((not (consp e)) 0)
         ((and (recurp (mx2 (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
          (+ (x2evals (caddr e) (append base vs) caps defs fuel)
             (x2evals-loop e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))
         (t (x2evals (caddr e) (append base vs) caps defs fuel)))))

(defun x2ev-ind (flg e env caps defs fuel vs)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) (if (eq flg :loop) 0 1)))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (cond
   ((eq flg :args)
    (if (atom e)
        (list env caps defs fuel vs)
      (list (x2ev-ind :m (car e) env caps defs fuel nil) (x2ev-ind :args (cdr e) env caps defs fuel nil))))
   ((eq flg :loop)
    (if (not (consp e))
        nil
      (list (x2ev-ind :m (caddr e) (append env vs) caps defs fuel nil)
            (if (and (recurp (mx2 (caddr e) (append env vs) caps defs fuel)) (not (zp fuel)))
                (x2ev-ind :loop e env caps defs (1- fuel) (cdr (mx2 (caddr e) (append env vs) caps defs fuel)))
              nil))))
   (t
    (case (car e)
      (:if (list (x2ev-ind :m (cadr e) env caps defs fuel nil)
                 (x2ev-ind :m (caddr e) env caps defs fuel nil)
                 (x2ev-ind :m (cadddr e) env caps defs fuel nil)))
      (:let (list (x2ev-ind :m (cadr e) env caps defs fuel nil)
                  (x2ev-ind :m (caddr e) (append env (list (val (mx2 (cadr e) env caps defs fuel)))) caps defs fuel nil)))
      ((:add :lt) (list (x2ev-ind :m (cadr e) env caps defs fuel nil) (x2ev-ind :m (caddr e) env caps defs fuel nil)))
      ((:mkclo :prim) (x2ev-ind :args (cddr e) env caps defs fuel nil))
      (:callv (list (x2ev-ind :args (cddr e) env caps defs fuel nil)
                    (x2ev-ind :m (cadr e) env caps defs fuel nil)
                    (if (zp fuel)
                        nil
                      (x2ev-ind :m (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel) nil))))
      (:loop (list (x2ev-ind :args (cadr e) env caps defs fuel nil)
                   (x2ev-ind :loop e env caps defs fuel (val (mx2-args (cadr e) env caps defs fuel)))))
      (:recur (x2ev-ind :args (cdr e) env caps defs fuel nil))
      (:throw (x2ev-ind :m (cadr e) env caps defs fuel nil))
      (:try (list (x2ev-ind :m (cadr e) env caps defs fuel nil)
                  (x2ev-ind :m (caddr e) (append env (list (cdr (mx2 (cadr e) env caps defs fuel)))) caps defs fuel nil)))
      (otherwise (list env caps defs fuel vs))))))

; the stronger statement the induction needs: a step to spare per
; expression, an argument list that answers a value its length to spare
(defthm s2clk-linear-flag
  (cond ((eq flg :args)
         (and (<= (s2clk-args e env caps defs fuel) (* 2 (x2evals-args e env caps defs fuel)))
              (implies (valp (mx2-args e env caps defs fuel))
                       (<= (+ (s2clk-args e env caps defs fuel) (len e)) (* 2 (x2evals-args e env caps defs fuel))))))
        ((eq flg :loop)
         (implies (consp e)
                  (<= (+ 1 (s2clk-loop e env vs caps defs fuel)) (* 2 (x2evals-loop e env vs caps defs fuel)))))
        (t (<= (+ 1 (s2clk e env caps defs fuel)) (* 2 (x2evals e env caps defs fuel)))))
  :rule-classes nil
  :hints (("Goal" :induct (x2ev-ind flg e env caps defs fuel vs)
                  :in-theory (e/d (c+ mx2-args-cons) (pick-arity split-rest mx2 mx2-args mx2-loop)))))

; RUNNING IS LINEAR: at most two steps per expression the meaning
; evaluates, every loop iteration, call and handler counted
(defthm s2clk-linear
  (<= (s2clk e env caps defs fuel) (* 2 (x2evals e env caps defs fuel)))
  :hints (("Goal" :use ((:instance s2clk-linear-flag (flg :m))))))

; clotran's VM, formally (PLAN step 30): the extended machine's cost
; (model/vmx.lisp), by step counting, as vm-closure-cost.lisp's:
;
;   sxclk-linear   the clock <= 2 xevals, the number of expressions the
;                  meaning itself evaluates -- every iteration of every
;                  loop counted, closures made and called, recursion
;                  included
;
; A loop's iterations are counted by the meaning (each runs its body),
; so a loop costs what its iterations evaluate. Its k slides, the steps
; that drop its locals from under its value, are paid for by its k
; inits: the proof's statement is the stronger clock + 1 <= 2 xevals,
; one step to spare per expression, and an argument list has its
; length to spare.

(in-package "ACL2")

(include-book "vmx-proof")

(mutual-recursion
 (defun xevals (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ 1 (xevals (cadr e) env caps defs fuel)
             (if (truthy (val (mx (cadr e) env caps defs fuel)))
                 (xevals (caddr e) env caps defs fuel)
               (xevals (cadddr e) env caps defs fuel))))
     (:let (+ 1 (xevals (cadr e) env caps defs fuel)
              (xevals (caddr e) (append env (list (val (mx (cadr e) env caps defs fuel)))) caps defs fuel)))
     ((:add :lt) (+ 1 (xevals (cadr e) env caps defs fuel) (xevals (caddr e) env caps defs fuel)))
     (:mkclo (+ 1 (xevals-args (cddr e) env caps defs fuel)))
     (:callv (if (zp fuel)
                 (+ 1 (xevals-args (cddr e) env caps defs fuel) (xevals (cadr e) env caps defs fuel))
               (+ 1 (xevals-args (cddr e) env caps defs fuel) (xevals (cadr e) env caps defs fuel)
                  (xevals (cadr (xv-def)) (xv-vs) (clo-caps (val (xv-rf))) defs (1- fuel)))))
     (:loop (+ 1 (xevals-args (cadr e) env caps defs fuel)
               (xevals-loop e env (val (mx-args (cadr e) env caps defs fuel)) caps defs fuel)))
     (:recur (+ 1 (xevals-args (cdr e) env caps defs fuel)))
     (otherwise 1)))
 (defun xevals-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1))))
   (if (atom es)
       0
     (+ (xevals (car es) env caps defs fuel) (xevals-args (cdr es) env caps defs fuel))))
 (defun xevals-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0))))
   (cond ((not (consp e)) 0)
         ((and (recurp (mx (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
          (+ (xevals (caddr e) (append base vs) caps defs fuel)
             (xevals-loop e base (cdr (mx (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))
         (t (xevals (caddr e) (append base vs) caps defs fuel)))))

(defun xev-ind (flg e env caps defs fuel vs)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) (if (eq flg :loop) 0 1)))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (cond
   ((eq flg :args)
    (if (atom e)
        (list env caps defs fuel vs)
      (list (xev-ind :m (car e) env caps defs fuel nil) (xev-ind :args (cdr e) env caps defs fuel nil))))
   ((eq flg :loop)
    (if (not (consp e))
        nil
      (list (xev-ind :m (caddr e) (append env vs) caps defs fuel nil)
            (if (and (recurp (mx (caddr e) (append env vs) caps defs fuel)) (not (zp fuel)))
                (xev-ind :loop e env caps defs (1- fuel) (cdr (mx (caddr e) (append env vs) caps defs fuel)))
              nil))))
   (t
    (case (car e)
      (:if (list (xev-ind :m (cadr e) env caps defs fuel nil)
                 (xev-ind :m (caddr e) env caps defs fuel nil)
                 (xev-ind :m (cadddr e) env caps defs fuel nil)))
      (:let (list (xev-ind :m (cadr e) env caps defs fuel nil)
                  (xev-ind :m (caddr e) (append env (list (val (mx (cadr e) env caps defs fuel)))) caps defs fuel nil)))
      ((:add :lt) (list (xev-ind :m (cadr e) env caps defs fuel nil) (xev-ind :m (caddr e) env caps defs fuel nil)))
      (:mkclo (xev-ind :args (cddr e) env caps defs fuel nil))
      (:callv (list (xev-ind :args (cddr e) env caps defs fuel nil)
                    (xev-ind :m (cadr e) env caps defs fuel nil)
                    (if (zp fuel)
                        nil
                      (xev-ind :m (cadr (xv-def)) (xv-vs) (clo-caps (val (xv-rf))) defs (1- fuel) nil))))
      (:loop (list (xev-ind :args (cadr e) env caps defs fuel nil)
                   (xev-ind :loop e env caps defs fuel (val (mx-args (cadr e) env caps defs fuel)))))
      (:recur (xev-ind :args (cdr e) env caps defs fuel nil))
      (otherwise (list env caps defs fuel vs))))))

; the stronger statement the induction needs: a step to spare per
; expression, an argument list's length to spare
(defthm sxclk-linear-flag
  (cond ((eq flg :args)
         (<= (+ (sxclk-args e env caps defs fuel) (len e)) (* 2 (xevals-args e env caps defs fuel))))
        ((eq flg :loop)
         (implies (consp e)
                  (<= (+ 1 (sxclk-loop e env vs caps defs fuel)) (* 2 (xevals-loop e env vs caps defs fuel)))))
        (t (<= (+ 1 (sxclk e env caps defs fuel)) (* 2 (xevals e env caps defs fuel)))))
  :rule-classes nil
  :hints (("Goal" :induct (xev-ind flg e env caps defs fuel vs) :in-theory (enable c+))))

; RUNNING IS LINEAR: at most two steps per expression the meaning
; evaluates, every loop iteration counted
(defthm sxclk-linear
  (<= (sxclk e env caps defs fuel) (* 2 (xevals e env caps defs fuel)))
  :hints (("Goal" :use ((:instance sxclk-linear-flag (flg :m))))))

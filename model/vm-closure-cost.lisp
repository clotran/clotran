; clotran's VM, formally (PLAN step 30). The closure call's cost, by
; step counting, for both machines (James, 2026-10-04: algorithms as
; well as data structures follow correct big O):
;
;   running is linear   each machine's clock <= 2 cevals, the number of
;                       expressions the meaning itself evaluates --
;                       closures made and called, recursion included
;
; and each step is O(1): a :callv is one step whatever its arity -- it
; moves no value (callv-moves-no-value, vcs-callv-moves-no-value), where
; model/vm-call.lisp's :call copies its n arguments. The one step that
; is not O(1) is :mkclo, which copies its k captures into the closure;
; the k values were computed by k expressions just before it, so the
; copy is paid for by evaluation the meaning counts.

(in-package "ACL2")

(include-book "vm-closure-stack-proof")

; ---- THE LANGUAGE's OWN COST ------------------------------------------------

(mutual-recursion
 (defun cevals (e env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ 1 (cevals (cadr e) env caps defs fuel)
             (if (truthy (val (mc (cadr e) env caps defs fuel)))
                 (cevals (caddr e) env caps defs fuel)
               (cevals (cadddr e) env caps defs fuel))))
     (:let (+ 1 (cevals (cadr e) env caps defs fuel)
              (cevals (caddr e) (append env (list (val (mc (cadr e) env caps defs fuel)))) caps defs fuel)))
     ((:add :lt) (+ 1 (cevals (cadr e) env caps defs fuel) (cevals (caddr e) env caps defs fuel)))
     (:mkclo (+ 1 (cevals-args (cddr e) env caps defs fuel)))
     (:callv (if (zp fuel)
                 (+ 1 (cevals-args (cddr e) env caps defs fuel) (cevals (cadr e) env caps defs fuel))
               (+ 1 (cevals-args (cddr e) env caps defs fuel) (cevals (cadr e) env caps defs fuel)
                  (cevals (cadr (cv-def)) (cv-vs) (clo-caps (val (cv-rf))) defs (1- fuel)))))
     (otherwise 1)))
 (defun cevals-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (+ (cevals (car es) env caps defs fuel) (cevals-args (cdr es) env caps defs fuel)))))

(defun cev-ind (flg e env caps defs fuel)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list env caps defs fuel)
        (list (cev-ind :m (car e) env caps defs fuel) (cev-ind :args (cdr e) env caps defs fuel)))
    (case (car e)
      (:if (list (cev-ind :m (cadr e) env caps defs fuel)
                 (cev-ind :m (caddr e) env caps defs fuel)
                 (cev-ind :m (cadddr e) env caps defs fuel)))
      (:let (list (cev-ind :m (cadr e) env caps defs fuel)
                  (cev-ind :m (caddr e) (append env (list (val (mc (cadr e) env caps defs fuel)))) caps defs fuel)))
      ((:add :lt) (list (cev-ind :m (cadr e) env caps defs fuel) (cev-ind :m (caddr e) env caps defs fuel)))
      (:mkclo (cev-ind :args (cddr e) env caps defs fuel))
      (:callv (list (cev-ind :args (cddr e) env caps defs fuel)
                    (cev-ind :m (cadr e) env caps defs fuel)
                    (if (zp fuel)
                        nil
                      (cev-ind :m (cadr (cv-def)) (cv-vs) (clo-caps (val (cv-rf))) defs (1- fuel)))))
      (otherwise (list env caps defs fuel)))))

; ---- RUNNING IS LINEAR ----------------------------------------------------------

(defthm cclk-linear-flag
  (if (eq flg :args)
      (<= (cclk-args e env caps defs fuel) (* 2 (cevals-args e env caps defs fuel)))
    (<= (cclk e env caps defs fuel) (* 2 (cevals e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :induct (cev-ind flg e env caps defs fuel) :in-theory (enable c+))))

; THE REGISTER MACHINE: at most two steps per expression the meaning evaluates
(defthm cclk-linear
  (<= (cclk e env caps defs fuel) (* 2 (cevals e env caps defs fuel)))
  :hints (("Goal" :use ((:instance cclk-linear-flag (flg :m))))))

(defthm sclk-linear-flag
  (if (eq flg :args)
      (<= (sclk-args e env caps defs fuel) (* 2 (cevals-args e env caps defs fuel)))
    (<= (sclk e env caps defs fuel) (* 2 (cevals e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :induct (cev-ind flg e env caps defs fuel) :in-theory (enable c+))))

; THE ONE-STACK MACHINE: the same bound
(defthm sclk-linear
  (<= (sclk e env caps defs fuel) (* 2 (cevals e env caps defs fuel)))
  :hints (("Goal" :use ((:instance sclk-linear-flag (flg :m))))))

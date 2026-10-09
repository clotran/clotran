; clotran's VM, timed (PLAN step 34): the cost of the machine with
; arities, primitives and throws (model/vmx2.lisp) in WEIGHTED steps.
; James, 2026-10-09: "include timing in your proofs".
;
; ACL2 counts steps; time is steps by weights. Two kinds of step weigh
; differently on the machine: a PRIM step leaves for the runtime (the
; boundary, ~25 ns besides the operation's own work, measured by
; scripts/calibrate) and every other step is the machine's own (~6 ns).
; So the clock is split by kind:
;
;   s2pclk-prims   the machine's prim steps are at most x2prims, the
;                  prims the meaning itself evaluates -- the compiled code
;                  never crosses the boundary more often than the language
;                  says it must
;   vm-time-bound  for ANY weights ws (a step) and wp (a prim step's extra),
;                  ws x s2clk + wp x s2pclk <= 2 ws x2evals + wp x2prims
;
; The machine runs s2clk steps (vmx2-proof). Which of those steps are prim
; instructions is read off the clock's own structure: s2pclk counts the
; :prim case's step, the one the compiler emits as the prim instruction
; (s2code-len's :prim case, its 1). The weights are scripts/calibrate's.

(in-package "ACL2")

(include-book "vmx2-cost")

; ---- THE PRIM STEPS THE MACHINE TAKES ------------------------------------------------

(mutual-recursion
 (defun s2pclk (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 0)
     (:if (c+ (s2pclk (cadr e) env caps defs fuel)
              (if (valp (mx2 (cadr e) env caps defs fuel))
                  (if (truthy (val (mx2 (cadr e) env caps defs fuel)))
                      (s2pclk (caddr e) env caps defs fuel)
                    (s2pclk (cadddr e) env caps defs fuel))
                0)))
     (:let (let ((env2 (append env (list (val (mx2 (cadr e) env caps defs fuel))))))
             (c+ (s2pclk (cadr e) env caps defs fuel)
                 (if (valp (mx2 (cadr e) env caps defs fuel)) (s2pclk (caddr e) env2 caps defs fuel) 0))))
     ((:add :lt) (c+ (s2pclk (cadr e) env caps defs fuel)
                     (if (valp (mx2 (cadr e) env caps defs fuel)) (s2pclk (caddr e) env caps defs fuel) 0)))
     (:mkclo (s2pclk-args (cddr e) env caps defs fuel))
     (:callv (c+ (s2pclk-args (cddr e) env caps defs fuel)
                 (if (valp (mx2-args (cddr e) env caps defs fuel))
                     (c+ (s2pclk (cadr e) env caps defs fuel)
                         (if (and (valp (x2-rf)) (clop (val (x2-rf))) (consp (x2-cl)) (not (zp fuel)))
                             (s2pclk (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel))
                           0))
                   0)))
     (:loop (c+ (s2pclk-args (cadr e) env caps defs fuel)
                (if (valp (mx2-args (cadr e) env caps defs fuel))
                    (s2pclk-loop e env (val (mx2-args (cadr e) env caps defs fuel)) caps defs fuel)
                  0)))
     (:recur (s2pclk-args (cdr e) env caps defs fuel))
     ;; the prim's own step: the one instruction that leaves for the runtime
     (:prim (c+ (s2pclk-args (cddr e) env caps defs fuel)
                (if (valp (mx2-args (cddr e) env caps defs fuel)) 1 0)))
     (:throw (s2pclk (cadr e) env caps defs fuel))
     (:try (let ((rb (mx2 (cadr e) env caps defs fuel))
                 (env2 (append env (list (cdr (mx2 (cadr e) env caps defs fuel))))))
             (c+ (s2pclk (cadr e) env caps defs fuel)
                 (if (thrownp rb) (s2pclk (caddr e) env2 caps defs fuel) 0))))
     (otherwise 0)))
 (defun s2pclk-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1)) :ruler-extenders :all))
   (if (atom es)
       0
     (c+ (s2pclk (car es) env caps defs fuel)
         (if (valp (mx2 (car es) env caps defs fuel)) (s2pclk-args (cdr es) env caps defs fuel) 0))))
 (defun s2pclk-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0)) :ruler-extenders :all))
   (cond ((not (consp e)) 0)
         ((and (recurp (mx2 (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
          (c+ (s2pclk (caddr e) (append base vs) caps defs fuel)
              (s2pclk-loop e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))
         (t (s2pclk (caddr e) (append base vs) caps defs fuel)))))

; ---- THE PRIMS THE MEANING EVALUATES ------------------------------------------------

(mutual-recursion
 (defun x2prims (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 0)
     (:if (+ (x2prims (cadr e) env caps defs fuel)
             (if (valp (mx2 (cadr e) env caps defs fuel))
                 (if (truthy (val (mx2 (cadr e) env caps defs fuel)))
                     (x2prims (caddr e) env caps defs fuel)
                   (x2prims (cadddr e) env caps defs fuel))
               0)))
     (:let (+ (x2prims (cadr e) env caps defs fuel)
              (if (valp (mx2 (cadr e) env caps defs fuel))
                  (x2prims (caddr e) (append env (list (val (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)
                0)))
     ((:add :lt) (+ (x2prims (cadr e) env caps defs fuel)
                    (if (valp (mx2 (cadr e) env caps defs fuel)) (x2prims (caddr e) env caps defs fuel) 0)))
     (:mkclo (x2prims-args (cddr e) env caps defs fuel))
     (:prim (+ 1 (x2prims-args (cddr e) env caps defs fuel)))
     (:callv (+ (x2prims-args (cddr e) env caps defs fuel)
                (if (valp (mx2-args (cddr e) env caps defs fuel))
                    (+ (x2prims (cadr e) env caps defs fuel)
                       (if (and (valp (x2-rf)) (clop (val (x2-rf))) (consp (x2-cl)) (not (zp fuel)))
                           (x2prims (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel))
                         0))
                  0)))
     (:loop (+ (x2prims-args (cadr e) env caps defs fuel)
               (if (valp (mx2-args (cadr e) env caps defs fuel))
                   (x2prims-loop e env (val (mx2-args (cadr e) env caps defs fuel)) caps defs fuel)
                 0)))
     (:recur (x2prims-args (cdr e) env caps defs fuel))
     (:throw (x2prims (cadr e) env caps defs fuel))
     (:try (+ (x2prims (cadr e) env caps defs fuel)
              (if (thrownp (mx2 (cadr e) env caps defs fuel))
                  (x2prims (caddr e) (append env (list (cdr (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)
                0)))
     (otherwise 0)))
 (defun x2prims-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1))))
   (if (atom es)
       0
     (+ (x2prims (car es) env caps defs fuel)
        (if (valp (mx2 (car es) env caps defs fuel)) (x2prims-args (cdr es) env caps defs fuel) 0))))
 (defun x2prims-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0))))
   (cond ((not (consp e)) 0)
         ((and (recurp (mx2 (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
          (+ (x2prims (caddr e) (append base vs) caps defs fuel)
             (x2prims-loop e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))
         (t (x2prims (caddr e) (append base vs) caps defs fuel)))))

; ---- THE BOUNDARY IS CROSSED NO MORE OFTEN THAN THE LANGUAGE SAYS --------------------

(defthm s2pclk-prims-flag
  (cond ((eq flg :args) (<= (s2pclk-args e env caps defs fuel) (x2prims-args e env caps defs fuel)))
        ((eq flg :loop) (<= (s2pclk-loop e env vs caps defs fuel) (x2prims-loop e env vs caps defs fuel)))
        (t (<= (s2pclk e env caps defs fuel) (x2prims e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :induct (x2ev-ind flg e env caps defs fuel vs)
                  :in-theory (e/d (c+ mx2-args-cons) (pick-arity split-rest mx2 mx2-args mx2-loop)))))

(defthm s2pclk-prims
  (<= (s2pclk e env caps defs fuel) (x2prims e env caps defs fuel))
  :hints (("Goal" :use ((:instance s2pclk-prims-flag (flg :m))))))

; ---- TIME ---------------------------------------------------------------------------------

; THE MACHINE'S TIME, any weights: a step ws, a prim step wp more
(defthm vm-time-bound
  (implies (and (natp ws) (natp wp))
           (<= (+ (* ws (s2clk e env caps defs fuel)) (* wp (s2pclk e env caps defs fuel)))
               (+ (* 2 ws (x2evals e env caps defs fuel)) (* wp (x2prims e env caps defs fuel)))))
  :hints (("Goal" :in-theory (disable s2clk s2pclk x2evals x2prims)
           :use (s2clk-linear s2pclk-prims
                 (:instance (:theorem (implies (and (natp w) (<= a b)) (<= (* w a) (* w b))))
                            (w ws) (a (s2clk e env caps defs fuel)) (b (* 2 (x2evals e env caps defs fuel))))
                 (:instance (:theorem (implies (and (natp w) (<= a b)) (<= (* w a) (* w b))))
                            (w wp) (a (s2pclk e env caps defs fuel)) (b (x2prims e env caps defs fuel)))))))

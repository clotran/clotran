; clotran's JIT, stage 2 (PLAN step 31 and 34; James, 2026-10-09: the
; seq operations, then the JIT, then the heap): THE PRIMS COMPILED. Stage 1
; (vmj.lisp) did the moves and the branches in native code and left every
; prim to the step, so a loop's `<` and `inc` still went through the runtime
; -- ~85% of a loop's time. Here a prim whose operator is a builtin with an
; integer fast case -- the cases flat_int_op answers in place -- is done
; natively when its arguments are integers and the answer fits, and is the
; step otherwise.
;
; The operator is a pool constant, so which builtin it is is known when the
; block is translated: (builtin-id op), the runtime's id of a builtin value
; (Eval.f90's B_*), 0 for anything else. THE NATIVE OP:
;
;   (:fast id n)   the n arguments at sp-n .. sp-1: if each is an integer
;                  and the answer fits (fast-dom), slot sp-n := fast-val
;                  and sp := sp-n+1; otherwise the step
;
; WHAT THE RUNTIME MUST DO, stated: prim is unconstrained in the model
; (vmx2.lisp's encapsulate), so a prim's meaning on these cases is a
; property of the runtime, (prim-fast-ok) below -- the builtin answers
; fast-val on fast-dom. scripts/fuzz -m jit checks it against clj on every
; program it runs, and its control (CLOTRAN_JIT_BREAK=2, an addition one
; off) is caught.
;
; Theorems:
;   vmj2-block-is  under prim-fast-ok, a block run from its pc is one
;                  vmi-step
;   vmj2-run-is    under prim-fast-ok, the native machine, its blocks
;                  translated once, is vmi-run step for step
;   vmj2-ops       a block is at most 5 native ops: a prim compiled costs a
;                  constant, where the step it replaces costs the runtime's
;                  boundary (model/vmx2-time.lisp's wp)

(in-package "ACL2")

(include-book "vmj")

; ---- WHAT A BUILTIN IS ----------------------------------------------------------------

; the runtime's id of a builtin value; anything else 0
(encapsulate (((builtin-id *) => *))
  (local (defun builtin-id (x) (declare (ignore x)) 0)))

(defconst *i64-lo* -9223372036854775808)
(defconst *i64-hi* 9223372036854775807)
(defun i64p (x) (and (integerp x) (<= *i64-lo* x) (<= x *i64-hi*)))

; the arity of id's fast case, 0 when it has none (Eval.f90: B_ADD 1, B_SUB
; 2, B_EQ 4, B_LT 5, B_GT 45, B_LTE 46, B_GTE 47; B_INC 49, B_DEC 50,
; B_ZERO 59, B_POS 60, B_NEG 61)
(defun fast-n (id)
  (cond ((member id '(1 2 4 5 45 46 47)) 2)
        ((member id '(49 50 59 60 61)) 1)
        (t 0)))

; its domain: integers, and an answer that fits 64 bits
(defun fast-dom (id a b)
  (and (i64p a)
       (or (equal (fast-n id) 1) (i64p b))
       (case id
         (1 (i64p (+ a b)))
         (2 (i64p (- a b)))
         (49 (i64p (+ a 1)))
         (50 (i64p (- a 1)))
         (otherwise t))))

; its answer there
(defun fast-val (id a b)
  (case id
    (1 (+ a b))
    (2 (- a b))
    (4 (bool (equal a b)))
    (5 (bool (< a b)))
    (45 (bool (> a b)))
    (46 (bool (<= a b)))
    (47 (bool (>= a b)))
    (49 (+ a 1))
    (50 (- a 1))
    (59 (bool (equal a 0)))
    (60 (bool (> a 0)))
    (61 (bool (< a 0)))
    (otherwise nil)))

; THE RUNTIME'S PROPERTY: a builtin with a fast case, on its domain,
; answers its fast value
(defun-sk prim-fast-ok ()
  (forall (op a b)
    (implies (and (< 0 (fast-n (builtin-id op))) (fast-dom (builtin-id op) a b))
             (equal (prim op (if (equal (fast-n (builtin-id op)) 2) (list a b) (list a)))
                    (fast-val (builtin-id op) a b)))))

; ---- THE NATIVE MACHINE, WITH (:fast id n) ------------------------------------------------

(defun vmj2-exec (ops vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (atom ops)
      vmi
    (let ((op (car ops)))
      (case (car op)
        (:chk-ix (if (< (vmj-ix (cadr op) (caddr op) vmi) (v-stk-length vmi))
                     (vmj2-exec (cdr ops) vmi)
                   (vmi-step vmi)))
        (:chk-sp (if (<= (nfix (cadr op)) (nfix (v-sp vmi)))
                     (vmj2-exec (cdr ops) vmi)
                   (vmi-step vmi)))
        (:mov (let ((vmi (vmi-sset (vmj-ix (cadr op) (caddr op) vmi)
                                   (vmi-sreg (vmj-ix (cadddr op) (car (cddddr op)) vmi) vmi) vmi)))
                (vmj2-exec (cdr ops) vmi)))
        (:movc (let ((vmi (vmi-sset (vmj-ix (cadr op) (caddr op) vmi) (vmi-poolv (cadddr op) vmi) vmi)))
                 (vmj2-exec (cdr ops) vmi)))
        (:addsp (let ((vmi (update-v-sp (nfix (+ (nfix (v-sp vmi)) (ifix (cadr op)))) vmi)))
                  (vmj2-exec (cdr ops) vmi)))
        (:cbf (if (truthy (vmi-sreg (vmj-ix (cadr op) (caddr op) vmi) vmi))
                  (vmj2-exec (cdr ops) vmi)
                (update-v-pc (nfix (cadddr op)) vmi)))
        (:fast (let* ((id (cadr op)) (n (nfix (caddr op))) (sp (nfix (v-sp vmi)))
                      (a (vmi-sreg (- sp n) vmi)) (b (vmi-sreg (- sp 1) vmi)))
                 (if (fast-dom id a b)
                     (let* ((vmi (vmi-sset (- sp n) (fast-val id a b) vmi))
                            (vmi (update-v-sp (1+ (- sp n)) vmi)))
                       (vmj2-exec (cdr ops) vmi))
                   (vmi-step vmi))))
        (:goto (update-v-pc (nfix (cadr op)) vmi))
        (:slow (vmi-step vmi))
        (otherwise vmi)))))

; the block of the instruction at p: a prim of a builtin with a fast case of
; its arity compiled, anything else stage 1's block
(defun vmj2-block (p vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((op (vmi-w p 0 vmi)) (a (nfix (vmi-w p 1 vmi))) (n (nfix (vmi-w p 2 vmi)))
         (id (builtin-id (vmi-poolv a vmi))))
    (if (and (equal op 13) (< 0 n) (equal (fast-n id) n))
        (list (list :chk-sp n) '(:chk-ix :sp -1) (list :fast id n) (list :goto (1+ (nfix p))))
      (vmj-block p vmi))))

(defun vmj2-translate (p n vmi)
  (declare (xargs :stobjs vmi :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (cons (vmj2-block p vmi) (vmj2-translate (1+ (nfix p)) (1- n) vmi))))

(defun vmj2-run (tab n vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (zp n)
      vmi
    (let ((vmi (if (equal (v-status vmi) 0) (vmj2-exec (nth (nfix (v-pc vmi)) tab) vmi) vmi)))
      (vmj2-run tab (1- n) vmi))))

; ---- STAGE 1'S BLOCKS RUN THE SAME ---------------------------------------------------------

; vmj2-exec is vmj-exec on any list without a :fast op, as stage 1's are
(defun no-fast (ops)
  (if (atom ops) t (and (not (eq (car (car ops)) :fast)) (no-fast (cdr ops)))))

(defthm vmj2-exec-is-vmj-exec
  (implies (no-fast ops) (equal (vmj2-exec ops vmi) (vmj-exec ops vmi)))
  :hints (("Goal" :induct (vmj2-exec ops vmi) :in-theory (disable vmi-step))))

(defthm vmj-block-no-fast
  (no-fast (vmj-block p vmi))
  :hints (("Goal" :in-theory (enable vmj-block))))

; ---- A COMPILED PRIM IS THE STEP ------------------------------------------------------------

(defthm vmj2-step-prim
  (implies (and (equal (v-status vmi) 0) (equal (vmi-w (v-pc vmi) 0 vmi) 13))
           (equal (vmi-step vmi) (vmi-prim vmi)))
  :hints (("Goal" :in-theory (enable vmi-step))))

(defthm vmi-stk-from-0 (equal (vmi-stk-from a 0 vmi) nil) :hints (("Goal" :expand ((vmi-stk-from a 0 vmi)))))
(defthm vmi-stk-from-1
  (equal (vmi-stk-from a 1 vmi) (list (vmi-sreg a vmi)))
  :hints (("Goal" :expand ((vmi-stk-from a 1 vmi)))))

(defthm vmi-stk-from-2
  (equal (vmi-stk-from a 2 vmi) (list (vmi-sreg a vmi) (vmi-sreg (1+ (nfix a)) vmi)))
  :hints (("Goal" :expand ((vmi-stk-from a 2 vmi)))))

(defthm fast-val-not-throw
  (not (throwp (fast-val id a b))))

(in-theory (disable fast-dom fast-val))

; the fast case, where its domain holds, is the prim's step
(defthm vmj2-fast-is
  (implies (and (prim-fast-ok) (equal (v-status vmi) 0) (equal (vmi-w (v-pc vmi) 0 vmi) 13)
                (< 0 (nfix (vmi-w (v-pc vmi) 2 vmi)))
                (equal (fast-n (builtin-id (vmi-poolv (nfix (vmi-w (v-pc vmi) 1 vmi)) vmi)))
                       (nfix (vmi-w (v-pc vmi) 2 vmi))))
           (equal (vmj2-exec (vmj2-block (nfix (v-pc vmi)) vmi) vmi) (vmi-step vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-prim fast-n vmi-sset vmi-poolv) (prim-fast-ok prim-fast-ok-necc vmj-block))
           :use ((:instance prim-fast-ok-necc
                            (op (vmi-poolv (nfix (vmi-w (v-pc vmi) 1 vmi)) vmi))
                            (a (vmi-sreg (- (nfix (v-sp vmi)) (nfix (vmi-w (v-pc vmi) 2 vmi))) vmi))
                            (b (vmi-sreg (- (nfix (v-sp vmi)) 1) vmi)))))))

; ---- A BLOCK IS ONE STEP --------------------------------------------------------------------

(defthm vmj2-block-is
  (implies (and (prim-fast-ok) (equal (v-status vmi) 0))
           (equal (vmj2-exec (vmj2-block (nfix (v-pc vmi)) vmi) vmi) (vmi-step vmi)))
  :hints (("Goal" :in-theory (disable vmj2-exec vmj-block vmj-exec prim-fast-ok)
           :cases ((and (equal (vmi-w (v-pc vmi) 0 vmi) 13)
                        (< 0 (nfix (vmi-w (v-pc vmi) 2 vmi)))
                        (equal (fast-n (builtin-id (vmi-poolv (nfix (vmi-w (v-pc vmi) 1 vmi)) vmi)))
                               (nfix (vmi-w (v-pc vmi) 2 vmi)))))
           :use (vmj2-fast-is vmj-block-is (:instance vmj-block-no-fast (p (nfix (v-pc vmi))))))))

(defthm nth-vmj2-translate
  (implies (and (natp p) (natp i) (< i (nfix n)))
           (equal (nth i (vmj2-translate p n vmi)) (vmj2-block (+ p i) vmi)))
  :hints (("Goal" :induct (vmj-ind i p n) :in-theory (disable vmj2-block) :expand ((vmj2-translate p n vmi)))))

(defthm nth-vmj2-translate-past
  (implies (and (natp i) (<= (nfix n) i))
           (equal (nth i (vmj2-translate p n vmi)) nil))
  :hints (("Goal" :induct (vmj-ind i p n) :in-theory (disable vmj2-block) :expand ((vmj2-translate p n vmi)))))

(defthm vmj2-block-same
  (implies (and (equal (nth *v-codei* a) (nth *v-codei* b)) (equal (nth *v-pooli* a) (nth *v-pooli* b)))
           (equal (equal (vmj2-block p a) (vmj2-block p b)) t))
  :hints (("Goal" :in-theory (e/d (vmi-w vmi-poolv) (vmj-block))
           :use (vmj-block-same))))

(defthm vmj2-tab-step
  (implies (and (prim-fast-ok) (equal (v-status vmi) 0)
                (equal (nth *v-codei* vmi) (nth *v-codei* vmi0))
                (equal (nth *v-pooli* vmi) (nth *v-pooli* vmi0)))
           (equal (vmj2-exec (nth (nfix (v-pc vmi)) (vmj2-translate 0 (vmj-ncode vmi0) vmi0)) vmi)
                  (vmi-step vmi)))
  :hints (("Goal" :in-theory (disable vmj2-exec vmj2-block vmj-ncode vmj2-block-same vmj-ncode-same prim-fast-ok)
           :cases ((< (nfix (v-pc vmi)) (vmj-ncode vmi0)))
           :use (vmj2-block-is vmj-step-past-code
                 (:instance vmj2-block-same (p (nfix (v-pc vmi))) (a vmi) (b vmi0))
                 (:instance vmj-ncode-same (a vmi) (b vmi0))))
          ("Subgoal 2" :in-theory (e/d (vmj2-exec) (vmj2-block vmj-ncode vmj2-block-same vmj-ncode-same prim-fast-ok)))))

; THE NATIVE MACHINE, prims compiled, IS THE INTERPRETER -- given the
; runtime's property
(defthm vmj2-run-is
  (implies (and (prim-fast-ok)
                (equal (nth *v-codei* vmi) (nth *v-codei* vmi0))
                (equal (nth *v-pooli* vmi) (nth *v-pooli* vmi0)))
           (equal (vmj2-run (vmj2-translate 0 (vmj-ncode vmi0) vmi0) n vmi) (vmi-run n vmi)))
  :hints (("Goal" :induct (vmi-run n vmi)
           :in-theory (e/d (vmi-run) (vmj2-exec vmj2-block vmj-ncode vmj2-translate nth update-nth nfix prim-fast-ok))
           :expand ((vmj2-run (vmj2-translate 0 (vmj-ncode vmi0) vmi0) n vmi)))
          ("Subgoal *1/2" :cases ((equal (v-status vmi) 0)) :use vmj2-tab-step)
          ("Subgoal *1/2.2" :in-theory (e/d (vmi-run vmi-step) (vmj2-exec vmj2-block vmj-ncode vmj2-translate nth update-nth prim-fast-ok)))))

; ---- COST -----------------------------------------------------------------------------------

; a block is at most 5 native ops, each a constant number of machine
; instructions: a compiled prim is O(1) native work, no boundary crossed
(defthm vmj2-ops
  (<= (len (vmj2-block p vmi)) 5)
  :hints (("Goal" :in-theory (enable vmj-block)))
  :rule-classes (:rewrite :linear))

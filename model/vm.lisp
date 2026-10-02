; clotran's VM, formally (PLAN step 28). Stage 1: the core without
; functions -- constants, locals, if, let, two builtins.
;
; Three things, and a theorem tying them:
;
;   THE MEANING   meaning: an expression's value in an environment of local
;                 values, the tree executor's semantics in miniature
;   THE MACHINE   a register machine: a state is (pc registers), one
;                 step runs the instruction at pc
;   THE COMPILER  vm-compile: an expression to instructions that leave its
;                 value in a target register, temporaries above a
;                 first free register, locals where the register map
;                 says they are
;
; THE THEOREM (vm-compile-correct): running the compiled code for vm-clock steps
; from its first instruction reaches its last, with the expression's
; value in the target register and every register below the first
; free one -- the locals -- as they were. The method is J Moore's for
; ACL2 machine proofs: running a + b steps is running a, then b
; (run-plus), and a clock function says how many steps code takes.
;
; Values are ACL2 objects; Clojure's false is the symbol :false, nil is
; nil, and only those two are falsey.

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defun truthy (x) (not (or (null x) (eq x :false))))

(defun bool (b) (if b t :false))

; ---- THE MEANING ----------------------------------------------------------
;
; (:const v) (:local i) (:if c then else) (:let init body) (:add a b)
; (:lt a b); a let's value is the next local, (:local (len env))

(defun meaning (e env)
  (declare (xargs :measure (acl2-count e)))
  (case (car e)
    (:const (cadr e))
    (:local (nth (nfix (cadr e)) env))
    (:if (if (truthy (meaning (cadr e) env)) (meaning (caddr e) env) (meaning (cadddr e) env)))
    (:let (meaning (caddr e) (append env (list (meaning (cadr e) env)))))
    (:add (+ (fix (meaning (cadr e) env)) (fix (meaning (caddr e) env))))
    (:lt (bool (< (rfix (meaning (cadr e) env)) (rfix (meaning (caddr e) env)))))
    (otherwise nil)))

; ---- THE MACHINE ----------------------------------------------------------
;
; (:loadk d v) (:move d s) (:add d a b) (:lt d a b) (:jmpf s target)
; (:jmp target); anything else, or a pc past the program, halts

(defun vm-step (prog s)
  (let* ((pc (nfix (car s))) (regs (cadr s)) (ins (nth pc prog)))
    (case (car ins)
      (:loadk (list (1+ pc) (update-nth (nfix (cadr ins)) (caddr ins) regs)))
      (:move (list (1+ pc) (update-nth (nfix (cadr ins)) (nth (nfix (caddr ins)) regs) regs)))
      (:add (list (1+ pc) (update-nth (nfix (cadr ins))
                                      (+ (fix (nth (nfix (caddr ins)) regs))
                                         (fix (nth (nfix (cadddr ins)) regs)))
                                      regs)))
      (:lt (list (1+ pc) (update-nth (nfix (cadr ins))
                                     (bool (< (rfix (nth (nfix (caddr ins)) regs))
                                              (rfix (nth (nfix (cadddr ins)) regs))))
                                     regs)))
      (:jmpf (if (truthy (nth (nfix (cadr ins)) regs))
                 (list (1+ pc) regs)
               (list (nfix (caddr ins)) regs)))
      (:jmp (list (nfix (cadr ins)) regs))
      (otherwise s))))

(defun vm-run (prog s n)
  (if (zp n) s (vm-run prog (vm-step prog s) (1- n))))

(defthm run-plus
  (implies (and (natp a) (natp b))
           (equal (vm-run prog s (+ a b)) (vm-run prog (vm-run prog s a) b))))

; ---- THE COMPILER ---------------------------------------------------------
;
; vm-compile e d f cenv pc: code placed at pc leaving e's value in register d,
; using registers f, f+1, ... for temporaries; local i lives in register
; (nth i cenv); a let's value goes in f and becomes the next local

(defun vm-compile (e d f cenv pc)
  (declare (xargs :measure (acl2-count e)))
  (let ((d (nfix d)) (f (nfix f)) (pc (nfix pc)))
    (case (car e)
      (:const (list (list :loadk d (cadr e))))
      (:local (list (list :move d (nth (nfix (cadr e)) cenv))))
      (:if (let* ((cc (vm-compile (cadr e) f (1+ f) cenv pc))
                  (pc1 (+ pc (len cc)))
                  (tc (vm-compile (caddr e) d f cenv (1+ pc1)))
                  (pc2 (+ 1 pc1 (len tc)))
                  (ec (vm-compile (cadddr e) d f cenv (1+ pc2))))
             (append cc (list (list :jmpf f (1+ pc2))) tc
                     (list (list :jmp (+ 1 pc2 (len ec)))) ec)))
      (:let (let* ((ic (vm-compile (cadr e) f (1+ f) cenv pc))
                   (bc (vm-compile (caddr e) d (1+ f) (append cenv (list f)) (+ pc (len ic)))))
              (append ic bc)))
      ((:add :lt)
       (let* ((ac (vm-compile (cadr e) f (1+ f) cenv pc))
              (bc (vm-compile (caddr e) (1+ f) (+ 2 f) cenv (+ pc (len ac)))))
         (append ac bc (list (list (car e) d f (1+ f))))))
      (otherwise (list (list :loadk d nil))))))

; clock arithmetic that keeps its order: running (c+ a b) steps is
; running a, then b, and the prover may not reorder the sum first
(defun c+ (a b) (+ (nfix a) (nfix b)))

; how many steps e's code takes, which an if decides at run time
(defun vm-clock (e env)
  (declare (xargs :measure (acl2-count e)))
  (case (car e)
    ((:const :local) 1)
    (:if (c+ (vm-clock (cadr e) env)
             (c+ 1 (if (truthy (meaning (cadr e) env))
                       (c+ (vm-clock (caddr e) env) 1)
                     (vm-clock (cadddr e) env)))))
    (:let (c+ (vm-clock (cadr e) env) (vm-clock (caddr e) (append env (list (meaning (cadr e) env))))))
    ((:add :lt) (c+ (vm-clock (cadr e) env) (c+ (vm-clock (caddr e) env) 1)))
    (otherwise 1)))

(defthm vm-clock-natp (natp (vm-clock e env)) :rule-classes :type-prescription)

; ---- what the theorem assumes ----------------------------------------------

; every local an expression names is bound
(defun wf (e n)
  (declare (xargs :measure (acl2-count e)))
  (case (car e)
    (:const t)
    (:local (and (natp (cadr e)) (< (cadr e) (nfix n))))
    (:if (and (wf (cadr e) n) (wf (caddr e) n) (wf (cadddr e) n)))
    (:let (and (wf (cadr e) n) (wf (caddr e) (1+ (nfix n)))))
    ((:add :lt) (and (wf (cadr e) n) (wf (caddr e) n)))
    (otherwise t)))

; local i's register holds its value, and every local's register is
; below the first free one
(defun env-ok (cenv env regs f)
  (if (endp cenv)
      (endp env)
    (and (consp env)
         (natp (car cenv)) (< (car cenv) (nfix f))
         (equal (nth (car cenv) regs) (car env))
         (env-ok (cdr cenv) (cdr env) regs f))))

; code sits in prog at pc
(defun code-at (prog pc code)
  (declare (xargs :measure (acl2-count code)))
  (if (endp code)
      t
    (and (equal (nth pc prog) (car code))
         (code-at prog (1+ pc) (cdr code)))))

; ---- the machine, a step at a time ---------------------------------------

(defthm run-c+
  (equal (vm-run prog s (c+ a b)) (vm-run prog (vm-run prog s (nfix a)) (nfix b)))
  :hints (("Goal" :use ((:instance run-plus (a (nfix a)) (b (nfix b)))))))
(in-theory (disable c+))

(defthm len-of-append (equal (len (append a b)) (+ (len a) (len b))))
(defthm append-assoc (equal (append (append a b) c) (append a (append b c))))

(defthm run-0 (equal (vm-run prog s 0) s))
(defthm run-1 (equal (vm-run prog s 1) (vm-step prog s)))
(in-theory (disable vm-run))

(defthm code-at-append
  (equal (code-at prog pc (append a b))
         (and (code-at prog pc a) (code-at prog (+ pc (len a)) b))))

; ---- registers that agree below h ----------------------------------------

(defun-sk agree-below (a b h)
  (forall r (implies (and (natp r) (< r (nfix h))) (equal (nth r a) (nth r b)))))

(in-theory (disable agree-below))

(defthm agree-below-refl (agree-below a a h)
  :hints (("Goal" :in-theory (enable agree-below))))

(defthm agree-below-trans
  (implies (and (agree-below a b h) (agree-below b c h)) (agree-below a c h))
  :hints (("Goal" :use ((:instance agree-below-necc (r (agree-below-witness a c h)))
                        (:instance agree-below-necc (a b) (b c) (r (agree-below-witness a c h))))
                  :expand ((agree-below a c h)))))

(defthm agree-below-smaller
  (implies (and (agree-below a b h) (<= (nfix g) (nfix h))) (agree-below a b g))
  :hints (("Goal" :use ((:instance agree-below-necc (r (agree-below-witness a b g))))
                  :expand ((agree-below a b g)))))

; a write at or above h is not seen below it
(defthm agree-below-write-above
  (implies (and (natp d) (<= (nfix h) d)) (agree-below (update-nth d v a) a h))
  :hints (("Goal" :expand ((agree-below (update-nth d v a) a h)))))

; the same write on both sides keeps them agreeing
(defthm agree-below-same-write
  (implies (and (natp d) (agree-below a b h)) (agree-below (update-nth d v a) (update-nth d v b) h))
  :hints (("Goal" :use ((:instance agree-below-necc
                         (r (agree-below-witness (update-nth d v a) (update-nth d v b) h))))
                  :expand ((agree-below (update-nth d v a) (update-nth d v b) h)))))

(defthm agree-below-sym
  (implies (agree-below a b h) (agree-below b a h))
  :hints (("Goal" :use ((:instance agree-below-necc (r (agree-below-witness b a h))))
                  :expand ((agree-below b a h)))))

; locals live below f, so registers that agree below f hold the same locals
(defthm env-ok-agree
  (implies (and (env-ok cenv env a f) (agree-below a b f))
           (env-ok cenv env b f))
  :hints (("Goal" :induct (env-ok cenv env a f))
          ("Subgoal *1/2" :use ((:instance agree-below-necc (r (car cenv)) (h f))))))

(defthm env-ok-local
  (implies (and (env-ok cenv env regs f) (natp i) (< i (len env)))
           (and (equal (nth (nth i cenv) regs) (nth i env))
                (natp (nth i cenv))
                (< (nth i cenv) (nfix f)))))

(defthm env-ok-bigger-f
  (implies (and (env-ok cenv env regs f) (<= (nfix f) (nfix g)))
           (env-ok cenv env regs g)))

(defthm env-ok-len
  (implies (env-ok cenv env regs f) (equal (len cenv) (len env)))
  :rule-classes :forward-chaining)

; ---- how one subexpression's run hands over to the next -------------
;
; A subexpression writes its target, at or above the first free
; register, and temporaries above that: below the first free register
; nothing changes. These say so for the shapes the compiler sequences.

(defthm agree-past-write
  (implies (and (agree-below a (update-nth g w b) h) (natp g)
                (<= (nfix f) g) (<= (nfix f) (nfix h)))
           (agree-below a b f))
  :hints (("Goal" :use ((:instance agree-below-smaller (b (update-nth g w b)) (g f))
                        (:instance agree-below-write-above (d g) (v w) (a b) (h f))
                        (:instance agree-below-trans (b (update-nth g w b)) (c b) (h f))))))

(defthm agree-past-two-writes
  (implies (and (agree-below a (update-nth g1 w1 b) h1) (agree-below b (update-nth g2 w2 c) h2)
                (natp g1) (natp g2) (<= (nfix f) g1) (<= (nfix f) g2)
                (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (agree-below a c f))
  :hints (("Goal" :use ((:instance agree-past-write (g g1) (w w1) (h h1))
                        (:instance agree-past-write (a b) (b c) (g g2) (w w2) (h h2))
                        (:instance agree-below-trans (a a) (b b) (c c) (h f))))))

; then a write at d, below: x agrees with r0, d set, below f
(defthm agree-compose
  (implies (and (agree-below x (update-nth d v r1) h1) (agree-below r1 (update-nth g w r0) h2)
                (natp d) (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (agree-below x (update-nth d v r0) f))
  :hints (("Goal" :use ((:instance agree-past-write (a r1) (b r0) (h h2))
                        (:instance agree-below-same-write (a r1) (b r0) (h f))
                        (:instance agree-below-smaller (a x) (b (update-nth d v r1)) (h h1) (g f))
                        (:instance agree-below-trans (a x) (b (update-nth d v r1)) (c (update-nth d v r0)) (h f))))))

(defthm env-ok-after-run
  (implies (and (env-ok cenv env regs f) (agree-below regs1 (update-nth g v regs) h)
                (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h)) (<= (nfix f) (nfix k)))
           (env-ok cenv env regs1 k))
  :hints (("Goal" :use ((:instance agree-past-write (a regs1) (b regs) (w v))
                        (:instance agree-below-sym (a regs1) (b regs) (h f))
                        (:instance env-ok-agree (a regs) (b regs1))
                        (:instance env-ok-bigger-f (regs regs1) (g k))))))

(defthm env-ok-append
  (implies (equal (len c1) (len e1))
           (equal (env-ok (append c1 c2) (append e1 e2) regs f)
                  (and (env-ok c1 e1 regs f) (env-ok c2 e2 regs f)))))

(defthm agree-nth
  (implies (and (agree-below a b h) (natp r) (< r (nfix h)))
           (equal (nth r a) (nth r b)))
  :hints (("Goal" :use agree-below-necc)))

; ---- THE THEOREM -----------------------------------------------------------

; a machine state: a pc and registers
(defun statep (s) (and (consp s) (consp (cdr s)) (null (cddr s)) (natp (car s))))

(defthm statep-step (implies (statep s) (statep (vm-step prog s))))

(defthm statep-run
  (implies (statep s) (statep (vm-run prog s n)))
  :hints (("Goal" :in-theory (enable vm-run))))

; one step, by the instruction at pc
(defthm step-loadk
  (implies (and (statep s) (equal (nth (car s) prog) (list :loadk d v)) (natp d))
           (equal (vm-step prog s) (list (1+ (car s)) (update-nth d v (cadr s))))))
(defthm step-move
  (implies (and (statep s) (equal (nth (car s) prog) (list :move d src)) (natp d) (natp src))
           (equal (vm-step prog s) (list (1+ (car s)) (update-nth d (nth src (cadr s)) (cadr s))))))
(defthm step-add
  (implies (and (statep s) (equal (nth (car s) prog) (list :add d a b)) (natp d) (natp a) (natp b))
           (equal (vm-step prog s)
                  (list (1+ (car s)) (update-nth d (+ (fix (nth a (cadr s))) (fix (nth b (cadr s)))) (cadr s))))))
(defthm step-lt
  (implies (and (statep s) (equal (nth (car s) prog) (list :lt d a b)) (natp d) (natp a) (natp b))
           (equal (vm-step prog s)
                  (list (1+ (car s))
                        (update-nth d (bool (< (rfix (nth a (cadr s))) (rfix (nth b (cadr s))))) (cadr s))))))
(defthm step-jmpf
  (implies (and (statep s) (equal (nth (car s) prog) (list :jmpf src tgt)) (natp src) (natp tgt))
           (equal (vm-step prog s)
                  (if (truthy (nth src (cadr s)))
                      (list (1+ (car s)) (cadr s))
                    (list tgt (cadr s))))))
(defthm step-jmp
  (implies (and (statep s) (equal (nth (car s) prog) (list :jmp tgt)) (natp tgt))
           (equal (vm-step prog s) (list tgt (cadr s)))))
(in-theory (disable vm-step))

; the induction: each subexpression from the state the one before left
(defun vm-ind (e d f cenv s env prog)
  (declare (xargs :measure (acl2-count e)))
  (let ((d (nfix d)) (f (nfix f)) (pc (nfix (car s))))
    (case (car e)
      (:if (let* ((cc (vm-compile (cadr e) f (1+ f) cenv pc))
                  (pc1 (+ pc (len cc)))
                  (s1 (vm-run prog s (vm-clock (cadr e) env)))
                  (s2 (vm-step prog s1))
                  (tc (vm-compile (caddr e) d f cenv (1+ pc1))))
             (list (vm-ind (cadr e) f (1+ f) cenv s env prog)
                   (vm-ind (caddr e) d f cenv s2 env prog)
                   (vm-ind (cadddr e) d f cenv s2 env prog)
                   tc)))
      (:let (let ((s1 (vm-run prog s (vm-clock (cadr e) env))))
              (list (vm-ind (cadr e) f (1+ f) cenv s env prog)
                    (vm-ind (caddr e) d (1+ f) (append cenv (list f)) s1
                            (append env (list (meaning (cadr e) env))) prog))))
      ((:add :lt) (let ((s1 (vm-run prog s (vm-clock (cadr e) env))))
                    (list (vm-ind (cadr e) f (1+ f) cenv s env prog)
                          (vm-ind (caddr e) (1+ f) (+ 2 f) cenv s1 env prog))))
      (otherwise nil))))

; THE PROPERTY, for one expression: from its first instruction its
; clock's worth of steps reaches its last, every register below the
; first free one as it was but the target, which holds the value
(defun good (e d f cenv s env prog)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile e d f cenv (car s)))
                (natp d) (natp f) (< d f)
                (wf e (len env)) (env-ok cenv env (cadr s) f))
           (let ((s2 (vm-run prog s (vm-clock e env))))
             (and (equal (car s2) (+ (car s) (len (vm-compile e d f cenv (car s)))))
                  (agree-below (cadr s2) (update-nth d (meaning e env) (cadr s)) f)))))

; ---- one construct at a time, each from its parts' property ------------

(defthm good-const
  (implies (equal (car e) :const) (good e d f cenv s env prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good-local
  (implies (equal (car e) :local) (good e d f cenv s env prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (good (cadr e) f (1+ f) cenv s env prog)
                (good (caddr e) (1+ f) (+ 2 f) cenv (vm-run prog s (vm-clock (cadr e) env)) env prog))
           (good e d f cenv s env prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good-let
  (implies (and (equal (car e) :let)
                (good (cadr e) f (1+ f) cenv s env prog)
                (good (caddr e) d (1+ f) (append cenv (list f))
                      (vm-run prog s (vm-clock (cadr e) env))
                      (append env (list (meaning (cadr e) env))) prog))
           (good e d f cenv s env prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good-if
  (implies (and (equal (car e) :if)
                (good (cadr e) f (1+ f) cenv s env prog)
                (good (caddr e) d f cenv (vm-step prog (vm-run prog s (vm-clock (cadr e) env))) env prog)
                (good (cadddr e) d f cenv (vm-step prog (vm-run prog s (vm-clock (cadr e) env))) env prog))
           (good e d f cenv s env prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s))))))

(defthm good-other
  (implies (not (member-equal (car e) '(:const :local :if :let :add :lt)))
           (good e d f cenv s env prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

; register numbers that are not naturals: nothing to show
(defthm good-unnatural
  (implies (not (and (natp d) (natp f))) (good e d f cenv s env prog)))

; a leaf: a constant, a local, or nothing the compiler knows
(defthm good-leaf
  (implies (not (member-equal (car e) (quote (:if :let :add :lt))))
           (good e d f cenv s env prog))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local))
                  :in-theory (disable good))))

; RUNNING THE COMPILED CODE ANSWERS WHAT THE MEANING DOES, for every
; expression: the constructs, composed
(defthm vm-compile-correct
  (good e d f cenv s env prog)
  :hints (("Goal" :induct (vm-ind e d f cenv s env prog)
                  :in-theory (disable good))))

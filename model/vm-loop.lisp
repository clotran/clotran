; clotran's VM, formally (PLAN step 28). Stage 2: loop and recur, on top
; of stage 1's core (model/vm.lisp), with one loop binding; several
; follow.
;
; A loop may not end, so the MEANING now takes fuel and answers one of
;   (:val . v)     the value
;   (:recur . v)   a tail position asks to go round again with v
;   (:out)         the fuel ran out
; and the COMPILER takes a loop context -- the loop's register and the
; pc of its head -- which a recur compiles against: its argument into a
; temporary, moved into the loop's register, then a jump to the head.
;
; THE THEOREM keeps stage 1's shape for a value, and adds the other way
; code can finish: when the meaning is a recur, running the code's clock
; arrives at the loop's head with the loop register holding the recur's
; value, every other register below the first free one untouched. A
; recur is a jump, so a loop runs in constant registers whatever its
; iterations -- recur does not grow anything.

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defun truthy (x) (not (or (null x) (eq x :false))))
(defun bool (b) (if b t :false))

; ---- THE MEANING ----------------------------------------------------------
;
; stage 1's (:const v) (:local i) (:if c then else) (:let init body)
; (:add a b) (:lt a b), and (:loop init body) -- init the next local,
; the body run until it gives a value -- and (:recur arg), only in a
; loop body's tail position (wf)

(defun val (r) (cdr r))
(defun valp (r) (eq (car r) :val))

(mutual-recursion
 (defun m (e env fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (* 2 (acl2-count e)))
                   :well-founded-relation o<))
   (case (car e)
     (:const (cons :val (cadr e)))
     (:local (cons :val (nth (nfix (cadr e)) env)))
     (:if (let ((rc (m (cadr e) env fuel)))
            (cond ((not (valp rc)) (list :out))
                  ((truthy (val rc)) (m (caddr e) env fuel))
                  (t (m (cadddr e) env fuel)))))
     (:let (let ((ri (m (cadr e) env fuel)))
             (if (valp ri) (m (caddr e) (append env (list (val ri))) fuel) (list :out))))
     ((:add :lt)
      (let ((ra (m (cadr e) env fuel)) (rb (m (caddr e) env fuel)))
        (cond ((not (and (valp ra) (valp rb))) (list :out))
              ((eq (car e) :add) (cons :val (+ (fix (val ra)) (fix (val rb)))))
              (t (cons :val (bool (< (rfix (val ra)) (rfix (val rb)))))))))
     (:loop (let ((ri (m (cadr e) env fuel)))
              (if (valp ri) (m-iter (caddr e) env (val ri) fuel) (list :out))))
     (:recur (let ((ra (m (cadr e) env fuel)))
               (if (valp ra) (cons :recur (val ra)) (list :out))))
     (otherwise (cons :val nil))))
 ; the loop's body with its local at v, round again on a recur, a unit of
 ; fuel a time
 (defun m-iter (body env v fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (1+ (* 2 (acl2-count body))))
                   :well-founded-relation o<))
   (let ((r (m body (append env (list v)) fuel)))
     (if (eq (car r) :recur)
         (if (zp fuel) (list :out) (m-iter body env (cdr r) (1- fuel)))
       r))))

; ---- THE MACHINE: stage 1's, unchanged ------------------------------------

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

; ---- THE COMPILER ---------------------------------------------------------
;
; lc, the loop context: nil outside a loop body's tail, else (reg . head)

(defun vm-compile (e d f cenv pc lc)
  (declare (xargs :measure (acl2-count e)))
  (let ((d (nfix d)) (f (nfix f)) (pc (nfix pc)))
    (case (car e)
      (:const (list (list :loadk d (cadr e))))
      (:local (list (list :move d (nth (nfix (cadr e)) cenv))))
      (:if (let* ((cc (vm-compile (cadr e) f (1+ f) cenv pc nil))
                  (pc1 (+ pc (len cc)))
                  (tc (vm-compile (caddr e) d f cenv (1+ pc1) lc))
                  (pc2 (+ 1 pc1 (len tc)))
                  (ec (vm-compile (cadddr e) d f cenv (1+ pc2) lc)))
             (append cc (list (list :jmpf f (1+ pc2))) tc
                     (list (list :jmp (+ 1 pc2 (len ec)))) ec)))
      (:let (let* ((ic (vm-compile (cadr e) f (1+ f) cenv pc nil))
                   (bc (vm-compile (caddr e) d (1+ f) (append cenv (list f)) (+ pc (len ic)) lc)))
              (append ic bc)))
      ((:add :lt)
       (let* ((ac (vm-compile (cadr e) f (1+ f) cenv pc nil))
              (bc (vm-compile (caddr e) (1+ f) (+ 2 f) cenv (+ pc (len ac)) nil)))
         (append ac bc (list (list (car e) d f (1+ f))))))
      ; the loop's register is f, its head the body's first instruction
      (:loop (let* ((ic (vm-compile (cadr e) f (1+ f) cenv pc nil))
                    (head (+ pc (len ic)))
                    (bc (vm-compile (caddr e) d (1+ f) (append cenv (list f)) head (cons f head))))
               (append ic bc)))
      ; the argument into a temporary, into the loop's register, back to the head
      (:recur (let ((ac (vm-compile (cadr e) f (1+ f) cenv pc nil)))
                (append ac (list (list :move (nfix (car lc)) f) (list :jmp (nfix (cdr lc)))))))
      (otherwise (list (list :loadk d nil))))))

; ---- THE CLOCK ------------------------------------------------------------
;
; steps until the code's end, or, for a recur, until the jump lands on
; the head; a loop's is its init's and every iteration's

(defun c+ (a b) (+ (nfix a) (nfix b)))

(mutual-recursion
 (defun clk (e env fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (* 2 (acl2-count e)))
                   :well-founded-relation o<))
   (case (car e)
     ((:const :local) 1)
     (:if (c+ (clk (cadr e) env fuel)
              (c+ 1 (if (truthy (val (m (cadr e) env fuel)))
                        (let ((r (m (caddr e) env fuel)))
                          (if (eq (car r) :recur) (clk (caddr e) env fuel) (c+ (clk (caddr e) env fuel) 1)))
                      (clk (cadddr e) env fuel)))))
     (:let (c+ (clk (cadr e) env fuel)
               (clk (caddr e) (append env (list (val (m (cadr e) env fuel)))) fuel)))
     ((:add :lt) (c+ (clk (cadr e) env fuel) (c+ (clk (caddr e) env fuel) 1)))
     (:loop (c+ (clk (cadr e) env fuel) (clk-iter (caddr e) env (val (m (cadr e) env fuel)) fuel)))
     (:recur (c+ (clk (cadr e) env fuel) (c+ 1 1)))
     (otherwise 1)))
 (defun clk-iter (body env v fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (1+ (* 2 (acl2-count body))))
                   :well-founded-relation o<))
   (let ((r (m body (append env (list v)) fuel)))
     (if (and (eq (car r) :recur) (not (zp fuel)))
         (c+ (clk body (append env (list v)) fuel) (clk-iter body env (cdr r) (1- fuel)))
       (clk body (append env (list v)) fuel)))))


; ---- stage 1s machinery, as model/vm.lisp proves it ----------------------

(defthm run-plus
  (implies (and (natp a) (natp b))
           (equal (vm-run prog s (+ a b)) (vm-run prog (vm-run prog s a) b))))

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
(defthm run-2 (equal (vm-run prog s 2) (vm-step prog (vm-step prog s)))
  :hints (("Goal" :in-theory (disable vm-step)
                  :expand ((vm-run prog s 2) (vm-run prog (vm-step prog s) 1) (vm-run prog (vm-step prog (vm-step prog s)) 0)))))
(in-theory (disable vm-run))

(defthm code-at-append
  (equal (code-at prog pc (append a b))
         (and (code-at prog pc a) (code-at prog (+ pc (len a)) b))))

; the instruction at pc is the first of the code placed there
(defthm code-at-first
  (implies (and (code-at prog pc code) (consp code))
           (equal (nth pc prog) (car code))))

; code beginning with one instruction: that instruction placed alone, then
; the rest -- kept as placements, which code-at-first reads
(defthm code-at-cons-split
  (implies (syntaxp (not (equal rest (quote (quote nil)))))
           (equal (code-at prog pc (cons i rest))
                  (and (code-at prog pc (list i)) (code-at prog (1+ pc) rest))))
  :hints (("Goal" :expand ((code-at prog pc (cons i rest)) (code-at prog pc (list i))))))

(in-theory (disable code-at))

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
                (integerp (nth i cenv))
                (<= 0 (nth i cenv))
                (< (nth i cenv) (nfix f)))))

; the same, the bound stated by the register map's length
(defthm env-ok-local-cenv
  (implies (and (env-ok cenv env regs f) (natp i) (< i (len cenv)))
           (and (equal (nth (nth i cenv) regs) (nth i env))
                (natp (nth i cenv))
                (integerp (nth i cenv))
                (<= 0 (nth i cenv))
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

; a machine state: a pc and registers
(defun statep (s) (and (consp s) (consp (cdr s)) (null (cddr s)) (natp (car s))))

(defthm statep-step (implies (statep s) (statep (vm-step prog s))))

(defthm statep-run
  (implies (statep s) (statep (vm-run prog s n)))
  :hints (("Goal" :in-theory (enable vm-run))))

; one step, by the instruction at pc
; one step, by the opcode at pc: the operands read from the instruction,
; no free variable to be matched before the pc is rewritten
(defthm step-loadk
  (implies (and (statep s) (equal (car (nth (car s) prog)) :loadk))
           (equal (vm-step prog s)
                  (list (1+ (car s)) (update-nth (nfix (cadr (nth (car s) prog))) (caddr (nth (car s) prog)) (cadr s))))))
(defthm step-move
  (implies (and (statep s) (equal (car (nth (car s) prog)) :move))
           (equal (vm-step prog s)
                  (list (1+ (car s))
                        (update-nth (nfix (cadr (nth (car s) prog))) (nth (nfix (caddr (nth (car s) prog))) (cadr s)) (cadr s))))))
(defthm step-add
  (implies (and (statep s) (equal (car (nth (car s) prog)) :add))
           (equal (vm-step prog s)
                  (list (1+ (car s))
                        (update-nth (nfix (cadr (nth (car s) prog)))
                                    (+ (fix (nth (nfix (caddr (nth (car s) prog))) (cadr s)))
                                       (fix (nth (nfix (cadddr (nth (car s) prog))) (cadr s))))
                                    (cadr s))))))
(defthm step-lt
  (implies (and (statep s) (equal (car (nth (car s) prog)) :lt))
           (equal (vm-step prog s)
                  (list (1+ (car s))
                        (update-nth (nfix (cadr (nth (car s) prog)))
                                    (bool (< (rfix (nth (nfix (caddr (nth (car s) prog))) (cadr s)))
                                             (rfix (nth (nfix (cadddr (nth (car s) prog))) (cadr s)))))
                                    (cadr s))))))
(defthm step-jmpf
  (implies (and (statep s) (equal (car (nth (car s) prog)) :jmpf))
           (equal (vm-step prog s)
                  (if (truthy (nth (nfix (cadr (nth (car s) prog))) (cadr s)))
                      (list (1+ (car s)) (cadr s))
                    (list (nfix (caddr (nth (car s) prog))) (cadr s))))))
(defthm step-jmp
  (implies (and (statep s) (equal (car (nth (car s) prog)) :jmp))
           (equal (vm-step prog s) (list (nfix (cadr (nth (car s) prog))) (cadr s)))))
(in-theory (disable vm-step))


; ---- what stage 2 assumes --------------------------------------------------

; well formed, with tail true where a recur may stand: a loop body's tail
(defun wf2 (e n tail)
  (declare (xargs :measure (acl2-count e)))
  (case (car e)
    (:const t)
    (:local (and (natp (cadr e)) (< (cadr e) (nfix n))))
    (:if (and (wf2 (cadr e) n nil) (wf2 (caddr e) n tail) (wf2 (cadddr e) n tail)))
    (:let (and (wf2 (cadr e) n nil) (wf2 (caddr e) (1+ (nfix n)) tail)))
    ((:add :lt) (and (wf2 (cadr e) n nil) (wf2 (caddr e) n nil)))
    (:loop (and (wf2 (cadr e) n nil) (wf2 (caddr e) (1+ (nfix n)) t)))
    (:recur (and tail (wf2 (cadr e) n nil)))
    (otherwise t)))

; in a tail position the loop context names a register below the first
; free one and the head's pc
(defun lc-ok (lc f tail)
  (or (not tail)
      (and (consp lc) (natp (car lc)) (< (car lc) (nfix f)) (natp (cdr lc)))))

; THE PROPERTY: a value as stage 1's; a recur, landing on the head with
; the loop register set and nothing else below the first free one changed
(defun good2 (e d f cenv s env fuel prog lc tail)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile e d f cenv (car s) lc))
                (natp d) (natp f) (< d f)
                (wf2 e (len env) tail) (env-ok cenv env (cadr s) f) (lc-ok lc f tail))
           (let ((r (m e env fuel)) (s2 (vm-run prog s (clk e env fuel))))
             (and (implies (eq (car r) :val)
                           (and (equal (car s2) (+ (car s) (len (vm-compile e d f cenv (car s) lc))))
                                (agree-below (cadr s2) (update-nth d (cdr r) (cadr s)) f)))
                  (implies (eq (car r) :recur)
                           (and (equal (car s2) (cdr lc))
                                (agree-below (cadr s2) (update-nth (car lc) (cdr r) (cadr s)) f)))))))

; outside a loop body's tail no recur comes out: an iteration consumes its own
(defun iter-ind (body env v fuel)
  (if (zp fuel)
      (list body env v)
    (iter-ind body env (cdr (m body (append env (list v)) fuel)) (1- fuel))))

(defthm m-iter-no-recur
  (not (equal (car (m-iter body env v fuel)) :recur))
  :hints (("Goal" :induct (iter-ind body env v fuel) :expand ((m-iter body env v fuel)))))

; an expression's own structure, its environment growing under a let
(defun m-ind (e env fuel n)
  (declare (xargs :measure (acl2-count e)))
  (case (car e)
    (:if (list (m-ind (cadr e) env fuel n) (m-ind (caddr e) env fuel n) (m-ind (cadddr e) env fuel n)))
    (:let (list (m-ind (cadr e) env fuel n)
                (m-ind (caddr e) (append env (list (cdr (m (cadr e) env fuel)))) fuel (1+ (nfix n)))))
    ((:add :lt) (list (m-ind (cadr e) env fuel n) (m-ind (caddr e) env fuel n)))
    (:recur (m-ind (cadr e) env fuel n))
    (otherwise (list env fuel n))))

(defthm m-no-recur
  (implies (wf2 e n nil) (not (equal (car (m e env fuel)) :recur)))
  :hints (("Goal" :induct (m-ind e env fuel n) :expand ((m e env fuel)))))

; how long code is depends on the expression alone -- not where it is
; put, which loop it is in, or which registers it uses -- so lengths
; computed at different places are the one length
(defun code-len (e)
  (declare (xargs :measure (acl2-count e)))
  (case (car e)
    ((:const :local) 1)
    (:if (+ (code-len (cadr e)) 1 (code-len (caddr e)) 1 (code-len (cadddr e))))
    ((:let :loop) (+ (code-len (cadr e)) (code-len (caddr e))))
    ((:add :lt) (+ (code-len (cadr e)) (code-len (caddr e)) 1))
    (:recur (+ (code-len (cadr e)) 2))
    (otherwise 1)))

(defthm len-vm-compile
  (equal (len (vm-compile e d f cenv pc lc)) (code-len e))
  :hints (("Goal" :induct (vm-compile e d f cenv pc lc))))

(defthm good2-const
  (implies (equal (car e) :const) (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good2-local
  (implies (equal (car e) :local) (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good2-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil)
                (good2 (caddr e) (1+ f) (+ 2 f) cenv (vm-run prog s (clk (cadr e) env fuel)) env fuel prog nil nil))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) lc)))))

(defthm good2-let
  (implies (and (equal (car e) :let)
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil)
                (good2 (caddr e) d (1+ f) (append cenv (list f))
                       (vm-run prog s (clk (cadr e) env fuel))
                       (append env (list (cdr (m (cadr e) env fuel)))) fuel prog lc tail))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) lc)))))

(defthm good2-if-true
  (implies (and (equal (car e) :if)
                (truthy (cdr (m (cadr e) env fuel)))
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil)
                (good2 (caddr e) d f cenv (vm-step prog (vm-run prog s (clk (cadr e) env fuel)))
                       env fuel prog lc tail))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) lc)))))

(defthm good2-if-false
  (implies (and (equal (car e) :if)
                (not (truthy (cdr (m (cadr e) env fuel))))
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil)
                (good2 (cadddr e) d f cenv (vm-step prog (vm-run prog s (clk (cadr e) env fuel)))
                       env fuel prog lc tail))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) lc)))))

(defthm good2-recur
  (implies (and (equal (car e) :recur)
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) lc)))))

; ---- loops: the iteration's property, then the loop's -------------------

; from the loop's head with its register at v: the iterations' clock
; reaches the loop's end with its value, nothing below the loop's
; register changed but the target
(defun good-iter (body d f cenv s env v fuel prog)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile body d (1+ f) (append cenv (list f)) (car s) (cons f (car s))))
                (natp d) (natp f) (< d f)
                (wf2 body (1+ (len env)) t) (env-ok cenv env (cadr s) f)
                (equal (nth f (cadr s)) v))
           (let ((r (m-iter body env v fuel)) (s2 (vm-run prog s (clk-iter body env v fuel))))
             (implies (eq (car r) :val)
                      (and (equal (car s2) (+ (car s) (code-len body)))
                           (agree-below (cadr s2) (update-nth d (cdr r) (cadr s)) f))))))

; one iteration: the body's property at this state, and the iteration's
; from where a recur lands
(defthm good-iter-step
  (implies (and (good2 body d (1+ f) (append cenv (list f)) s (append env (list v)) fuel prog
                       (cons f (car s)) t)
                (good-iter body d f cenv
                           (vm-run prog s (clk body (append env (list v)) fuel))
                           env (cdr (m body (append env (list v)) fuel)) (1- fuel) prog))
           (good-iter body d f cenv s env v fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((m-iter body env v fuel) (clk-iter body env v fuel)))))

; the last iteration: the body gives a value, or the fuel is spent
(defthm good-iter-last
  (implies (and (good2 body d (1+ f) (append cenv (list f)) s (append env (list v)) fuel prog
                       (cons f (car s)) t)
                (or (not (equal (car (m body (append env (list v)) fuel)) :recur)) (zp fuel)))
           (good-iter body d f cenv s env v fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((m-iter body env v fuel) (clk-iter body env v fuel)))))

(defthm good2-loop
  (implies (and (equal (car e) :loop)
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil)
                (good-iter (caddr e) d f cenv (vm-run prog s (clk (cadr e) env fuel))
                           env (cdr (m (cadr e) env fuel)) fuel prog))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) lc)))))

; ---- STAGE 2's THEOREM -------------------------------------------------

(defthm good2-unnatural
  (implies (not (and (natp d) (natp f))) (good2 e d f cenv s env fuel prog lc tail)))

(defthm good-iter-unnatural
  (implies (not (and (natp d) (natp f))) (good-iter body d f cenv s env v fuel prog)))

; anything else compiles to a load of nil, which is its meaning
(defthm good2-other
  (implies (not (member-equal (car e) (quote (:const :local :if :let :add :lt :loop :recur))))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good2-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :loop :recur)))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local))
                  :in-theory (disable good2))))

(defthm good2-if
  (implies (and (equal (car e) :if)
                (good2 (cadr e) f (1+ f) cenv s env fuel prog nil nil)
                (good2 (caddr e) d f cenv (vm-step prog (vm-run prog s (clk (cadr e) env fuel))) env fuel prog lc tail)
                (good2 (cadddr e) d f cenv (vm-step prog (vm-run prog s (clk (cadr e) env fuel))) env fuel prog lc tail))
           (good2 e d f cenv s env fuel prog lc tail))
  :hints (("Goal" :cases ((truthy (cdr (m (cadr e) env fuel))))
                  :in-theory (disable good2))))

; the induction the meaning makes: an expression from the state its
; predecessor left, and a loop's iterations each from where the last
; landed, a unit of fuel each
(defun ind2 (flg e d f cenv s env v fuel prog lc tail)
  (declare (xargs :measure (if (eq flg :iter)
                               (make-ord 1 (1+ (nfix fuel)) (1+ (* 2 (acl2-count e))))
                             (make-ord 1 (1+ (nfix fuel)) (* 2 (acl2-count e))))
                  :well-founded-relation o<
                  :ruler-extenders :all))
  (if (eq flg :iter)
      (let* ((env2 (append env (list v)))
             (r (m e env2 fuel))
             (s1 (vm-run prog s (clk e env2 fuel))))
        (list (ind2 :m e d (1+ f) (append cenv (list f)) s env2 v fuel prog (cons f (car s)) t)
              (if (and (eq (car r) :recur) (not (zp fuel)))
                  (ind2 :iter e d f cenv s1 env (cdr r) (1- fuel) prog nil nil)
                nil)))
    (case (car e)
      (:if (let ((s2 (vm-step prog (vm-run prog s (clk (cadr e) env fuel)))))
             (list (ind2 :m (cadr e) f (1+ f) cenv s env v fuel prog nil nil)
                   (ind2 :m (caddr e) d f cenv s2 env v fuel prog lc tail)
                   (ind2 :m (cadddr e) d f cenv s2 env v fuel prog lc tail))))
      (:let (let ((s1 (vm-run prog s (clk (cadr e) env fuel))))
              (list (ind2 :m (cadr e) f (1+ f) cenv s env v fuel prog nil nil)
                    (ind2 :m (caddr e) d (1+ f) (append cenv (list f)) s1
                          (append env (list (cdr (m (cadr e) env fuel)))) v fuel prog lc tail))))
      ((:add :lt) (let ((s1 (vm-run prog s (clk (cadr e) env fuel))))
                    (list (ind2 :m (cadr e) f (1+ f) cenv s env v fuel prog nil nil)
                          (ind2 :m (caddr e) (1+ f) (+ 2 f) cenv s1 env v fuel prog nil nil))))
      (:loop (let ((s1 (vm-run prog s (clk (cadr e) env fuel))))
               (list (ind2 :m (cadr e) f (1+ f) cenv s env v fuel prog nil nil)
                     (ind2 :iter (caddr e) d f cenv s1 env (cdr (m (cadr e) env fuel)) fuel prog nil nil))))
      (:recur (ind2 :m (cadr e) f (1+ f) cenv s env v fuel prog nil nil))
      (otherwise (list d f cenv s env v fuel prog lc tail)))))

(defthm vm-loop-correct-flag
  (if (eq flg :iter)
      (good-iter e d f cenv s env v fuel prog)
    (good2 e d f cenv s env fuel prog lc tail))
  :rule-classes nil
  :hints (("Goal" :induct (ind2 flg e d f cenv s env v fuel prog lc tail)
                  :in-theory (union-theories '(good2-if good2-let good2-binop good2-loop good2-recur
                                               good2-leaf good2-unnatural good-iter-step good-iter-last good-iter-unnatural
                                               member-equal car-cons cdr-cons nfix natp zp
                                               (:induction ind2))
                                             (theory 'minimal-theory)))))

; RUNNING THE COMPILED CODE ANSWERS WHAT THE MEANING DOES, loops and
; recurs included: a value at the code's end, a recur at the loop's head
(defthm vm-loop-correct
  (good2 e d f cenv s env fuel prog lc tail)
  :hints (("Goal" :use ((:instance vm-loop-correct-flag (flg :m) (v nil))))))

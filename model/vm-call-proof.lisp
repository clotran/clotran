; clotran's VM, formally (PLAN step 28). Stage 3's theorems, about the
; design model/vm-call.lisp states and checks: calls and frames on one
; value stack.
;
; THE THEOREM keeps stage 1's shape -- running an expression's code for
; its clock leaves its value in the target register and nothing below
; the first free register changed -- in frame-relative registers, and
; adds that the frame base and the return records come back as they
; were: a call is invisible to its caller but for its answer. It is
; proved for the wiping machine with any top the compiler's frames fit
; under, and top nil is the plain machine, so the same proof says both:
;
;   vm-call-correct   compiled programs answer what the meaning does
;   vm-call-rooted    and still do with every register above the live
;                     frame's top wiped at each return -- nothing a
;                     computation needs is held anywhere else

(in-package "ACL2")

(include-book "vm-call")
(include-book "arithmetic-5/top" :dir :system)

(defun c+ (a b) (+ (nfix a) (nfix b)))

; ---- THE CLOCK --------------------------------------------------------------
;
; steps an expression's code takes: a call's arguments, the call, the
; callee's body, its return

(mutual-recursion
 (defun clk (e env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local) 1)
     (:if (c+ (clk (cadr e) env defs fuel)
              (c+ 1 (if (truthy (val (m (cadr e) env defs fuel)))
                        (c+ (clk (caddr e) env defs fuel) 1)
                      (clk (cadddr e) env defs fuel)))))
     (:let (c+ (clk (cadr e) env defs fuel)
               (clk (caddr e) (append env (list (val (m (cadr e) env defs fuel)))) defs fuel)))
     ((:add :lt) (c+ (clk (cadr e) env defs fuel) (c+ (clk (caddr e) env defs fuel) 1)))
     (:call (if (zp fuel)
                (clk-args (cddr e) env defs fuel)
              (c+ (clk-args (cddr e) env defs fuel)
                  (c+ 1 (c+ (clk (cadr (cdr (assoc-equal (cadr e) defs)))
                                 (val (m-args (cddr e) env defs fuel)) defs (1- fuel))
                            1)))))
     (otherwise 1)))
 (defun clk-args (es env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (c+ (clk (car es) env defs fuel) (clk-args (cdr es) env defs fuel)))))

; ---- WHAT THE THEOREM ASSUMES -----------------------------------------------

; locals below n, and every call names a function defs has
(mutual-recursion
 (defun wf3 (e n defs)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:const t)
     (:local (and (natp (cadr e)) (< (cadr e) (nfix n))))
     (:if (and (wf3 (cadr e) n defs) (wf3 (caddr e) n defs) (wf3 (cadddr e) n defs)))
     (:let (and (wf3 (cadr e) n defs) (wf3 (caddr e) (1+ (nfix n)) defs)))
     ((:add :lt) (and (wf3 (cadr e) n defs) (wf3 (caddr e) n defs)))
     (:call (and (consp (assoc-equal (cadr e) defs)) (wf3-args (cddr e) n defs)))
     (otherwise t)))
 (defun wf3-args (es n defs)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) t (and (wf3 (car es) n defs) (wf3-args (cdr es) n defs)))))

; THE FRAME'S TOP: every call in e, compiled with first free register f,
; finds its first free register at or below top -- so the caller holds
; nothing live from top up while the callee runs
(mutual-recursion
 (defun top-ok (e f top)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:if (and (top-ok (cadr e) (1+ (nfix f)) top) (top-ok (caddr e) f top) (top-ok (cadddr e) f top)))
     (:let (and (top-ok (cadr e) (1+ (nfix f)) top) (top-ok (caddr e) (1+ (nfix f)) top)))
     ((:add :lt) (and (top-ok (cadr e) (1+ (nfix f)) top) (top-ok (caddr e) (+ 2 (nfix f)) top)))
     (:call (and (<= (nfix f) (nfix top)) (top-ok-args (cddr e) f top)))
     (otherwise t)))
 (defun top-ok-args (es f top)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) t (and (top-ok (car es) (1+ (nfix f)) top) (top-ok-args (cdr es) (1+ (nfix f)) top)))))

; every function's body well formed for its arity, and under top
(defun defs-ok (ds defs top)
  (if (atom ds)
      t
    (and (consp (car ds)) (consp (cdar ds)) (natp (car (cdar ds)))
         (wf3 (cadr (cdar ds)) (nfix (car (cdar ds))) defs)
         (or (not top) (top-ok (cadr (cdar ds)) (1+ (nfix (car (cdar ds)))) top))
         (defs-ok (cdr ds) defs top))))

(defthm defs-ok-lookup
  (implies (and (defs-ok ds defs top) (consp (assoc-equal name ds)))
           (and (natp (car (cdr (assoc-equal name ds))))
                (wf3 (cadr (cdr (assoc-equal name ds))) (nfix (car (cdr (assoc-equal name ds)))) defs)
                (implies top (top-ok (cadr (cdr (assoc-equal name ds)))
                                     (1+ (nfix (car (cdr (assoc-equal name ds))))) top)))))

; code sits in prog at pc
(defun code-at (prog pc code)
  (declare (xargs :measure (acl2-count code)))
  (if (endp code)
      t
    (and (equal (nth pc prog) (car code))
         (code-at prog (1+ pc) (cdr code)))))

; every function's code sits at its entry
(defun-sk fns-ok (prog defs fnpcs)
  (forall name
          (implies (consp (assoc-equal name defs))
                   (and (natp (cdr (assoc-equal name fnpcs)))
                        (code-at prog (cdr (assoc-equal name fnpcs))
                                 (body-code* (cdr (assoc-equal name defs))
                                             (cdr (assoc-equal name fnpcs)) fnpcs))))))

(in-theory (disable fns-ok))

; local i's register, in the frame at fb, holds its value, and every
; local's register is below the first free one
(defun env-ok (cenv env regs fb f)
  (if (endp cenv)
      (endp env)
    (and (consp env)
         (natp (car cenv)) (< (car cenv) (nfix f))
         (equal (nth (+ (nfix fb) (car cenv)) regs) (car env))
         (env-ok (cdr cenv) (cdr env) regs fb f))))

; a machine state: pc, frame base, registers, return records
(defun statep (s)
  (and (true-listp s) (equal (len s) 4) (natp (car s)) (natp (cadr s))))

; vals at k, k+1, ..
(defun vals-at (k vs regs)
  (declare (xargs :measure (acl2-count vs)))
  (if (atom vs)
      t
    (and (equal (nth k regs) (car vs)) (vals-at (1+ k) (cdr vs) regs))))

; how long code is depends on the expression alone
(mutual-recursion
 (defun code-len (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local) 1)
     (:if (+ (code-len (cadr e)) 1 (code-len (caddr e)) 1 (code-len (cadddr e))))
     (:let (+ (code-len (cadr e)) (code-len (caddr e))))
     ((:add :lt) (+ (code-len (cadr e)) (code-len (caddr e)) 1))
     (:call (+ (code-len-args (cddr e)) 1))
     (otherwise 1)))
 (defun code-len-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (code-len (car es)) (code-len-args (cdr es))))))

; registers that agree below h
(defun-sk agree-below (a b h)
  (forall r (implies (and (natp r) (< r (nfix h))) (equal (nth r a) (nth r b)))))

; THE PROPERTY. An expression's code, run for its clock from s: the pc
; at its end, the frame and the return records as they were, the value
; in the target, nothing below the first free register otherwise changed.
(defun good3 (e d f cenv s env defs fuel prog fnpcs top)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile e d f cenv (car s) fnpcs))
                (natp d) (natp f) (< d f)
                (wf3 e (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
                (defs-ok defs defs top) (fns-ok prog defs fnpcs)
                (or (not top) (top-ok e f top)))
           (let ((r (m e env defs fuel)) (s2 (vm-run-wiping prog s (clk e env defs fuel) top)))
             (implies (valp r)
                      (and (equal (car s2) (+ (car s) (code-len e)))
                           (equal (cadr s2) (cadr s))
                           (equal (cadddr s2) (cadddr s))
                           (agree-below (caddr s2) (update-nth (+ (cadr s) d) (val r) (caddr s))
                                        (+ (cadr s) f)))))))

; a call's arguments: the values in f, f+1, .., nothing below f changed
(defun good-args (es f cenv s env defs fuel prog fnpcs top)
  (implies (and (statep s)
                (code-at prog (car s) (vm-compile-args es f cenv (car s) fnpcs))
                (natp f)
                (wf3-args es (len env) defs) (env-ok cenv env (caddr s) (cadr s) f)
                (defs-ok defs defs top) (fns-ok prog defs fnpcs)
                (or (not top) (top-ok-args es f top)))
           (let ((r (m-args es env defs fuel)) (s2 (vm-run-wiping prog s (clk-args es env defs fuel) top)))
             (implies (valp r)
                      (and (equal (car s2) (+ (car s) (code-len-args es)))
                           (equal (cadr s2) (cadr s))
                           (equal (cadddr s2) (cadddr s))
                           (agree-below (caddr s2) (caddr s) (+ (cadr s) f))
                           (vals-at (+ (cadr s) f) (val r) (caddr s2)))))))

; ---- the machine's runs ---------------------------------------------------

(in-theory (disable w-step))

(defthm run-plus
  (implies (and (natp a) (natp b))
           (equal (vm-run-wiping prog s (+ a b) top)
                  (vm-run-wiping prog (vm-run-wiping prog s a top) b top)))
  :hints (("Goal" :induct (vm-run-wiping prog s a top))))

(defthm run-c+
  (equal (vm-run-wiping prog s (c+ a b) top)
         (vm-run-wiping prog (vm-run-wiping prog s (nfix a) top) (nfix b) top))
  :hints (("Goal" :use ((:instance run-plus (a (nfix a)) (b (nfix b)))))))
(in-theory (disable c+))

(defthm len-of-append (equal (len (append a b)) (+ (len a) (len b))))
(defthm append-assoc (equal (append (append a b) c) (append a (append b c))))

(defthm run-0 (equal (vm-run-wiping prog s 0 top) s))
(defthm run-1 (equal (vm-run-wiping prog s 1 top) (w-step prog s top)))
(in-theory (disable vm-run-wiping))

(defthm code-at-append
  (equal (code-at prog pc (append a b))
         (and (code-at prog pc a) (code-at prog (+ pc (len a)) b))))

(defthm code-at-first
  (implies (and (code-at prog pc code) (consp code))
           (equal (nth pc prog) (car code))))

(defthm code-at-cons-split
  (implies (syntaxp (not (equal rest (quote (quote nil)))))
           (equal (code-at prog pc (cons i rest))
                  (and (code-at prog pc (list i)) (code-at prog (1+ pc) rest))))
  :hints (("Goal" :expand ((code-at prog pc (cons i rest)) (code-at prog pc (list i))))))

(in-theory (disable code-at))

; the compiler's own recursion, an expression or an argument list
(defun vc-ind (flg e d f cenv pc fnpcs)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (vc-ind :m (car e) f (1+ f) cenv pc fnpcs)
              (vc-ind :args (cdr e) d (1+ f) cenv
                      (+ pc (len (vm-compile (car e) f (1+ f) cenv pc fnpcs))) fnpcs)))
    (case (car e)
      (:if (let* ((cc (vm-compile (cadr e) f (1+ f) cenv pc fnpcs))
                  (pc1 (+ pc (len cc) 1))
                  (tc (vm-compile (caddr e) d f cenv pc1 fnpcs))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (vc-ind :m (cadr e) f (1+ f) cenv pc fnpcs)
                   (vc-ind :m (caddr e) d f cenv pc1 fnpcs)
                   (vc-ind :m (cadddr e) d f cenv pc2 fnpcs))))
      (:let (let ((ic (vm-compile (cadr e) f (1+ f) cenv pc fnpcs)))
              (list (vc-ind :m (cadr e) f (1+ f) cenv pc fnpcs)
                    (vc-ind :m (caddr e) d (1+ f) (append cenv (list f)) (+ pc (len ic)) fnpcs))))
      ((:add :lt) (let ((ac (vm-compile (cadr e) f (1+ f) cenv pc fnpcs)))
                    (list (vc-ind :m (cadr e) f (1+ f) cenv pc fnpcs)
                          (vc-ind :m (caddr e) (1+ f) (+ 2 f) cenv (+ pc (len ac)) fnpcs))))
      (:call (vc-ind :args (cddr e) d f cenv pc fnpcs))
      (otherwise (list d f cenv pc fnpcs)))))

(defthm len-vm-compile-flag
  (if (eq flg :args)
      (equal (len (vm-compile-args e f cenv pc fnpcs)) (code-len-args e))
    (equal (len (vm-compile e d f cenv pc fnpcs)) (code-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (vc-ind flg e d f cenv pc fnpcs))))

(defthm len-vm-compile
  (equal (len (vm-compile e d f cenv pc fnpcs)) (code-len e))
  :hints (("Goal" :use ((:instance len-vm-compile-flag (flg :m))))))

(defthm len-vm-compile-args
  (equal (len (vm-compile-args es f cenv pc fnpcs)) (code-len-args es))
  :hints (("Goal" :use ((:instance len-vm-compile-flag (flg :args) (e es))))))

; ---- registers that agree below h ----------------------------------------

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

(defthm agree-below-write-above
  (implies (and (natp d) (<= (nfix h) d)) (agree-below (update-nth d v a) a h))
  :hints (("Goal" :expand ((agree-below (update-nth d v a) a h)))))

(defthm agree-below-same-write
  (implies (and (natp d) (agree-below a b h)) (agree-below (update-nth d v a) (update-nth d v b) h))
  :hints (("Goal" :use ((:instance agree-below-necc
                         (r (agree-below-witness (update-nth d v a) (update-nth d v b) h))))
                  :expand ((agree-below (update-nth d v a) (update-nth d v b) h)))))

(defthm agree-below-sym
  (implies (agree-below a b h) (agree-below b a h))
  :hints (("Goal" :use ((:instance agree-below-necc (r (agree-below-witness b a h))))
                  :expand ((agree-below b a h)))))

(defthm agree-nth
  (implies (and (agree-below a b h) (natp r) (< r (nfix h)))
           (equal (nth r a) (nth r b)))
  :hints (("Goal" :use agree-below-necc)))

; wiping from k up is not seen below k
(defthm nth-wipe-above
  (equal (nth r (wipe-above k regs))
         (if (< (nfix r) (nfix k)) (nth r regs) (if (< (nfix r) (len regs)) nil (nth r regs))))
  :hints (("Goal" :induct (list (wipe-above k regs) (nth r regs)))))

(defthm agree-below-wipe
  (implies (<= (nfix h) (nfix k)) (agree-below (wipe-above k regs) regs h))
  :hints (("Goal" :expand ((agree-below (wipe-above k regs) regs h)))))

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

(defthm agree-then-write
  (implies (and (agree-below a b h1) (agree-below b (update-nth g w c) h2)
                (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (agree-below a c f))
  :hints (("Goal" :use ((:instance agree-past-write (a b) (b c) (h h2))
                        (:instance agree-below-smaller (a a) (b b) (h h1) (g f))
                        (:instance agree-below-trans (a a) (b b) (c c) (h f))))))

(defthm agree-compose
  (implies (and (agree-below x (update-nth d v r1) h1) (agree-below r1 (update-nth g w r0) h2)
                (natp d) (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (agree-below x (update-nth d v r0) f))
  :hints (("Goal" :use ((:instance agree-past-write (a r1) (b r0) (h h2))
                        (:instance agree-below-same-write (a r1) (b r0) (h f))
                        (:instance agree-below-smaller (a x) (b (update-nth d v r1)) (h h1) (g f))
                        (:instance agree-below-trans (a x) (b (update-nth d v r1)) (c (update-nth d v r0)) (h f))))))

; ---- locals in a frame ----------------------------------------------------

(defthm env-ok-agree
  (implies (and (env-ok cenv env a fb f) (agree-below a b (+ (nfix fb) (nfix f))))
           (env-ok cenv env b fb f))
  :hints (("Goal" :induct (env-ok cenv env a fb f))
          ("Subgoal *1/2" :use ((:instance agree-below-necc (r (+ (nfix fb) (car cenv)))
                                           (h (+ (nfix fb) (nfix f))))))))

(defthm env-ok-local-cenv
  (implies (and (env-ok cenv env regs fb f) (natp fb) (natp i) (< i (len cenv)))
           (and (equal (nth (+ fb (nth i cenv)) regs) (nth i env))
                (natp (nth i cenv))
                (integerp (nth i cenv))
                (<= 0 (nth i cenv))
                (< (nth i cenv) (nfix f)))))

(defthm env-ok-bigger-f
  (implies (and (env-ok cenv env regs fb f) (<= (nfix f) (nfix g)))
           (env-ok cenv env regs fb g)))

(defthm env-ok-len
  (implies (env-ok cenv env regs fb f) (equal (len cenv) (len env)))
  :rule-classes :forward-chaining)

(defthm env-ok-append
  (implies (equal (len c1) (len e1))
           (equal (env-ok (append c1 c2) (append e1 e2) regs fb f)
                  (and (env-ok c1 e1 regs fb f) (env-ok c2 e2 regs fb f)))))

(defthm env-ok-after-run
  (implies (and (env-ok cenv env regs fb f) (agree-below regs1 (update-nth g v regs) h)
                (natp g) (<= (+ (nfix fb) (nfix f)) g) (<= (+ (nfix fb) (nfix f)) (nfix h))
                (<= (nfix f) (nfix k)))
           (env-ok cenv env regs1 fb k))
  :hints (("Goal" :use ((:instance agree-past-write (a regs1) (b regs) (w v) (f (+ (nfix fb) (nfix f))))
                        (:instance agree-below-sym (a regs1) (b regs) (h (+ (nfix fb) (nfix f))))
                        (:instance env-ok-agree (a regs) (b regs1))
                        (:instance env-ok-bigger-f (regs regs1) (g k))))))

(defthm env-ok-after-args
  (implies (and (env-ok cenv env regs fb f) (agree-below regs1 regs (+ (nfix fb) (nfix f))))
           (env-ok cenv env regs1 fb f))
  :hints (("Goal" :use ((:instance agree-below-sym (a regs1) (b regs) (h (+ (nfix fb) (nfix f))))
                        (:instance env-ok-agree (a regs) (b regs1))))))

; ---- the machine, a step at a time ---------------------------------------

(in-theory (enable w-step))

(defthm statep-wstep (implies (statep s) (statep (w-step prog s top))))

(defthm statep-run
  (implies (statep s) (statep (vm-run-wiping prog s n top)))
  :hints (("Goal" :induct (vm-run-wiping prog s n top) :in-theory (e/d (vm-run-wiping) (w-step statep)))))

(defmacro ins-of (s) `(nth (car ,s) prog))

(defthm wstep-loadk
  (implies (and (statep s) (equal (car (ins-of s)) :loadk))
           (equal (w-step prog s top)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (ins-of s)))) (caddr (ins-of s)) (caddr s))
                        (cadddr s)))))
(defthm wstep-move
  (implies (and (statep s) (equal (car (ins-of s)) :move))
           (equal (w-step prog s top)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (ins-of s))))
                                    (nth (+ (cadr s) (nfix (caddr (ins-of s)))) (caddr s)) (caddr s))
                        (cadddr s)))))
(defthm wstep-add
  (implies (and (statep s) (equal (car (ins-of s)) :add))
           (equal (w-step prog s top)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (ins-of s))))
                                    (+ (fix (nth (+ (cadr s) (nfix (caddr (ins-of s)))) (caddr s)))
                                       (fix (nth (+ (cadr s) (nfix (cadddr (ins-of s)))) (caddr s))))
                                    (caddr s))
                        (cadddr s)))))
(defthm wstep-lt
  (implies (and (statep s) (equal (car (ins-of s)) :lt))
           (equal (w-step prog s top)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (ins-of s))))
                                    (bool (< (rfix (nth (+ (cadr s) (nfix (caddr (ins-of s)))) (caddr s)))
                                             (rfix (nth (+ (cadr s) (nfix (cadddr (ins-of s)))) (caddr s)))))
                                    (caddr s))
                        (cadddr s)))))
(defthm wstep-jmpf
  (implies (and (statep s) (equal (car (ins-of s)) :jmpf))
           (equal (w-step prog s top)
                  (if (truthy (nth (+ (cadr s) (nfix (cadr (ins-of s)))) (caddr s)))
                      (list (1+ (car s)) (cadr s) (caddr s) (cadddr s))
                    (list (nfix (caddr (ins-of s))) (cadr s) (caddr s) (cadddr s))))))
(defthm wstep-jmp
  (implies (and (statep s) (equal (car (ins-of s)) :jmp))
           (equal (w-step prog s top)
                  (list (nfix (cadr (ins-of s))) (cadr s) (caddr s) (cadddr s)))))
(defthm wstep-call
  (implies (and (statep s) (equal (car (ins-of s)) :call))
           (equal (w-step prog s top)
                  (list (nfix (caddr (ins-of s))) (+ (cadr s) (nfix (cadr (cddddr (ins-of s)))))
                        (copy-args (cadr s) (cadddr (ins-of s)) (cadr (cddddr (ins-of s))) 0
                                   (car (cddddr (ins-of s))) (caddr s))
                        (cons (list (1+ (car s)) (cadr s) (cadr (ins-of s))) (cadddr s))))))
; a return to a caller: the answer into its destination, then the wipe
(defthm wstep-ret
  (implies (and (statep s) (equal (car (ins-of s)) :ret) (consp (cadddr s)))
           (equal (w-step prog s top)
                  (list (nfix (car (car (cadddr s)))) (nfix (cadr (car (cadddr s))))
                        (if top
                            (wipe-above (+ (nfix (cadr (car (cadddr s)))) (nfix top))
                                        (update-nth (+ (nfix (cadr (car (cadddr s)))) (nfix (caddr (car (cadddr s)))))
                                                    (nth (+ (cadr s) (nfix (cadr (ins-of s)))) (caddr s))
                                                    (caddr s)))
                          (update-nth (+ (nfix (cadr (car (cadddr s)))) (nfix (caddr (car (cadddr s)))))
                                      (nth (+ (cadr s) (nfix (cadr (ins-of s)))) (caddr s))
                                      (caddr s)))
                        (cdr (cadddr s))))))
(in-theory (disable w-step vm-step))

(defthm statep-fc
  (implies (statep s) (and (natp (car s)) (natp (cadr s))))
  :rule-classes :forward-chaining)
(defthm statep-list
  (equal (statep (list pc fb regs ctl)) (and (natp pc) (natp fb))))
(in-theory (disable statep))

; ---- a call's arguments, copied into the callee's frame ------------------

(defthm m-args-len
  (implies (equal (car (m-args es env defs fuel)) :val)
           (equal (len (cdr (m-args es env defs fuel))) (len es)))
  :hints (("Goal" :induct (len es) :expand ((m-args es env defs fuel)))))

(defun va-ind (k vs j)
  (if (or (atom vs) (zp j)) (list k vs j) (va-ind (1+ k) (cdr vs) (1- j))))

(defthm vals-at-nth
  (implies (and (vals-at k vs regs) (natp k) (natp j) (< j (len vs)))
           (equal (nth (+ k j) regs) (nth j vs)))
  :hints (("Goal" :induct (va-ind k vs j))))

; the copy writes from the callee's base + i up only
(defthm copy-args-below
  (implies (and (natp fb) (natp nb) (natp i))
           (agree-below (copy-args fb a nb i n regs) regs (+ fb nb i)))
  :hints (("Goal" :induct (copy-args fb a nb i n regs))
          ("Subgoal *1/2" :use ((:instance agree-below-write-above
                                 (d (+ fb nb i)) (h (+ fb nb i))
                                 (v (nth (+ fb (nfix a) i) regs)) (a regs))
                                (:instance agree-below-smaller
                                 (a (copy-args fb a nb (1+ i) n
                                               (update-nth (+ fb nb i) (nth (+ fb (nfix a) i) regs) regs)))
                                 (b (update-nth (+ fb nb i) (nth (+ fb (nfix a) i) regs) regs))
                                 (h (+ 1 fb nb i)) (g (+ fb nb i)))
                                (:instance agree-below-trans
                                 (a (copy-args fb a nb (1+ i) n
                                               (update-nth (+ fb nb i) (nth (+ fb (nfix a) i) regs) regs)))
                                 (b (update-nth (+ fb nb i) (nth (+ fb (nfix a) i) regs) regs))
                                 (c regs) (h (+ fb nb i)))))))

(defthm nth-copy-args-below
  (implies (and (natp fb) (natp nb) (natp i) (natp r) (< r (+ fb nb i)))
           (equal (nth r (copy-args fb a nb i n regs)) (nth r regs)))
  :hints (("Goal" :use ((:instance agree-nth (a (copy-args fb a nb i n regs)) (b regs)
                                     (h (+ fb nb i))))
                  :in-theory (disable agree-nth))))

; argument j lands in the callee's register j, the sources below the
; destinations so no copy overwrites one still to be read
(defthm copy-args-nth
  (implies (and (natp fb) (natp a) (natp nb) (natp i) (natp n) (natp j)
                (<= i j) (< j n) (<= (+ a n) nb))
           (equal (nth (+ fb nb j) (copy-args fb a nb i n regs))
                  (nth (+ fb a j) regs)))
  :hints (("Goal" :induct (copy-args fb a nb i n regs))))

(defun up-ind (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) i (up-ind (1+ i) n)))

(defthm consp-nthcdr
  (implies (natp i) (equal (consp (nthcdr i x)) (< i (len x))))
  :hints (("Goal" :induct (nthcdr i x))))
(defthm car-nthcdr (equal (car (nthcdr i x)) (nth i x))
  :hints (("Goal" :induct (nthcdr i x))))
(defthm cdr-nthcdr
  (implies (natp i) (equal (cdr (nthcdr i x)) (nthcdr (1+ i) x)))
  :hints (("Goal" :induct (nthcdr i x))))

; the callee's register i, its base a variable so the sum stays as written
(defthm nth-callee-arg
  (implies (and (natp fb) (natp a) (natp nb) (natp i) (equal base (+ fb nb))
                (< i (len vs)) (<= (+ a (len vs)) nb) (vals-at (+ fb a) vs regs))
           (equal (nth (+ base i) (copy-args fb a nb 0 (len vs) regs)) (nth i vs)))
  :hints (("Goal" :use ((:instance vals-at-nth (k (+ fb a)) (j i))
                        (:instance copy-args-nth (i 0) (n (len vs)) (j i)))
                  :in-theory (disable copy-args-nth vals-at-nth))))

; the callee's locals: register i of its frame holds argument i
(defthm env-ok-callee-from
  (implies (and (natp fb) (natp a) (natp nb) (natp i) (equal n (len vs)) (<= (+ a n) nb)
                (equal base (+ fb nb)) (vals-at (+ fb a) vs regs))
           (env-ok (count-from i n) (nthcdr i vs) (copy-args fb a nb 0 n regs) base (1+ n)))
  :hints (("Goal" :induct (up-ind i n) :in-theory (disable nthcdr))
          ("Subgoal *1/2.1" :use ((:instance nth-callee-arg (base (+ fb nb)))))))

(defthm env-ok-callee
  (implies (and (natp fb) (natp a) (natp nb) (<= (+ a (len vs)) nb) (vals-at (+ fb a) vs regs))
           (env-ok (count-from 0 (len vs)) vs (copy-args fb a nb 0 (len vs) regs) (+ fb nb) (1+ (len vs))))
  :hints (("Goal" :use ((:instance env-ok-callee-from (i 0) (n (len vs)) (base (+ fb nb)))))))

; ---- each kind of expression, given its parts --------------------------------

(defthm good3-const
  (implies (equal (car e) :const) (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good3-local
  (implies (equal (car e) :local) (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good3-other
  (implies (not (member-equal (car e) '(:const :local :if :let :add :lt :call)))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good3-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (good3 (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3 (caddr e) (1+ f) (+ 2 f) cenv (vm-run-wiping prog s (clk (cadr e) env defs fuel) top)
                       env defs fuel prog fnpcs top))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) fnpcs)))))

(defthm good3-let
  (implies (and (equal (car e) :let)
                (good3 (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3 (caddr e) d (1+ f) (append cenv (list f))
                       (vm-run-wiping prog s (clk (cadr e) env defs fuel) top)
                       (append env (list (cdr (m (cadr e) env defs fuel)))) defs fuel prog fnpcs top))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) fnpcs)))))

(defthm good3-if-true
  (implies (and (equal (car e) :if)
                (truthy (cdr (m (cadr e) env defs fuel)))
                (good3 (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3 (caddr e) d f cenv (w-step prog (vm-run-wiping prog s (clk (cadr e) env defs fuel) top) top)
                       env defs fuel prog fnpcs top))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) fnpcs)))))

(defthm good3-if-false
  (implies (and (equal (car e) :if)
                (not (truthy (cdr (m (cadr e) env defs fuel))))
                (good3 (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3 (cadddr e) d f cenv (w-step prog (vm-run-wiping prog s (clk (cadr e) env defs fuel) top) top)
                       env defs fuel prog fnpcs top))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile e d f cenv (car s) fnpcs)))))

(defthm good-args-nil
  (implies (atom es) (good-args es f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm good-args-cons
  (implies (and (consp es)
                (good3 (car es) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good-args (cdr es) (1+ f) cenv (vm-run-wiping prog s (clk (car es) env defs fuel) top)
                           env defs fuel prog fnpcs top))
           (good-args es f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vm-compile-args es f cenv (car s) fnpcs)
                           (m-args es env defs fuel)
                           (vals-at (+ (cadr s) f) (val (m-args es env defs fuel))
                                    (caddr (vm-run-wiping prog s (clk-args es env defs fuel) top)))))))

; ---- a call -------------------------------------------------------------------

(defthm natp-clk
  (natp (clk e env defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((clk e env defs fuel))))
  :rule-classes :type-prescription)
(defthm natp-clk-args
  (natp (clk-args es env defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((clk-args es env defs fuel))))
  :rule-classes :type-prescription)

; the return: the answer the callee left in its register n goes into the
; caller's destination, the caller's frame and records come back, and
; below the caller's first free register only the destination changed
(defthm ret-to-caller
  (implies (and (natp pc) (equal (nth pc prog) (list :ret n))
                (natp rpc) (natp fb) (natp d) (natp n) (natp f) (< d f)
                (natp cb) (<= (+ fb f) cb)
                (agree-below regs (update-nth (+ cb n) v ca) (+ 1 cb n))
                (agree-below ca r0 (+ fb f))
                (or (not top) (<= f (nfix top))))
           (let ((s4 (w-step prog (list pc cb regs (cons (list rpc fb d) ctl)) top)))
             (and (equal (car s4) rpc) (equal (cadr s4) fb) (equal (cadddr s4) ctl)
                  (statep s4)
                  (agree-below (caddr s4) (update-nth (+ fb d) v r0) (+ fb f)))))
  :hints (("Goal" :in-theory (disable nth update-nth agree-nth agree-past-write)
                  :use ((:instance agree-nth (a regs) (b (update-nth (+ cb n) v ca))
                                   (h (+ 1 cb n)) (r (+ cb n)))
                        (:instance agree-past-write (a regs) (b ca) (g (+ cb n)) (w v)
                                   (h (+ 1 cb n)) (f (+ fb f)))
                        (:instance agree-below-trans (a regs) (b ca) (c r0) (h (+ fb f)))
                        (:instance agree-below-same-write (a regs) (b r0) (d (+ fb d)) (h (+ fb f)))
                        (:instance agree-below-wipe (h (+ fb f)) (k (+ fb (nfix top)))
                                   (regs (update-nth (+ fb d) v regs)))
                        (:instance agree-below-trans
                                   (a (wipe-above (+ fb (nfix top)) (update-nth (+ fb d) v regs)))
                                   (b (update-nth (+ fb d) v regs))
                                   (c (update-nth (+ fb d) v r0)) (h (+ fb f)))))))

(defthm list-of-one
  (implies (and (true-listp x) (equal (len x) 1)) (equal x (list (car x))))
  :rule-classes nil
  :hints (("Goal" :expand ((len x) (len (cdr x)) (true-listp x) (true-listp (cdr x))))))

; a state is its parts
(defthm statep-parts
  (implies (and (statep s) (equal (car s) a) (equal (cadr s) b) (equal (cadddr s) c))
           (equal s (list a b (caddr s) c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable statep) :use ((:instance list-of-one (x (cdddr s)))))))

; after the arguments: the call, the callee's body (whatever state it
; ends in, given what its property says), the return
(defthm call-tail
  (implies (and (statep s1) (natp f) (natp d) (< d f) (natp n) (natp entry)
                (equal (nth (car s1) prog) (list :call d entry f n (+ f n)))
                (agree-below (caddr s1) r0 (+ (cadr s1) f))
                (statep s3)
                (equal (car s3) pc3) (natp pc3) (equal (nth pc3 prog) (list :ret n))
                (equal (cadr s3) (+ (cadr s1) f n))
                (equal (cadddr s3) (cons (list (1+ (car s1)) (cadr s1) d) (cadddr s1)))
                (agree-below (caddr s3)
                             (update-nth (+ (cadr s1) f n n) v (copy-args (cadr s1) f (+ f n) 0 n (caddr s1)))
                             (+ 1 (cadr s1) f n n))
                (or (not top) (<= f (nfix top))))
           (let ((s4 (w-step prog s3 top)))
             (and (statep s4)
                  (equal (car s4) (1+ (car s1))) (equal (cadr s4) (cadr s1)) (equal (cadddr s4) (cadddr s1))
                  (agree-below (caddr s4) (update-nth (+ (cadr s1) d) v r0) (+ (cadr s1) f)))))
  :hints (("Goal" :in-theory (disable nth update-nth ret-to-caller copy-args-below w-step)
                  :use ((:instance statep-parts (s s3) (a pc3) (b (+ (cadr s1) f n))
                                   (c (cons (list (1+ (car s1)) (cadr s1) d) (cadddr s1))))
                        (:instance copy-args-below (fb (cadr s1)) (a f) (nb (+ f n)) (i 0) (regs (caddr s1)))
                        (:instance agree-below-smaller (a (copy-args (cadr s1) f (+ f n) 0 n (caddr s1)))
                                   (b (caddr s1)) (h (+ (cadr s1) f n)) (g (+ (cadr s1) f)))
                        (:instance agree-below-trans (a (copy-args (cadr s1) f (+ f n) 0 n (caddr s1)))
                                   (b (caddr s1)) (c r0) (h (+ (cadr s1) f)))
                        (:instance ret-to-caller (pc pc3) (cb (+ (cadr s1) f n)) (regs (caddr s3))
                                   (ca (copy-args (cadr s1) f (+ f n) 0 n (caddr s1)))
                                   (rpc (1+ (car s1))) (fb (cadr s1)) (ctl (cadddr s1)))))))

; the call over plain variables, from s1, where the arguments are done:
; the callee's property at its entry, and what the machine does from there
(defthm call-abstract
  (implies (and (statep s1) (natp d) (natp f) (< d f) (natp entry) (equal (len vs) n) (equal k n)
                (vals-at (+ (cadr s1) f) vs (caddr s1))
                (code-at prog (car s1) (list (list :call d entry f k (+ f k))))
                (code-at prog entry (vm-compile body n (1+ n) (count-from 0 n) entry fnpcs))
                (code-at prog (+ entry (code-len body)) (list (list :ret n)))
                (wf3 body n defs) (defs-ok defs defs top) (fns-ok prog defs fnpcs)
                (or (not top) (top-ok body (1+ n) top))
                (or (not top) (<= f (nfix top)))
                (good3 body n (1+ n) (count-from 0 n) (w-step prog s1 top) vs defs fuel2 prog fnpcs top)
                (valp (m body vs defs fuel2)))
           (let ((s4 (w-step prog (vm-run-wiping prog (w-step prog s1 top) (clk body vs defs fuel2) top) top)))
             (and (statep s4)
                  (equal (car s4) (+ 1 (car s1))) (equal (cadr s4) (cadr s1))
                  (equal (cadddr s4) (cadddr s1))
                  (agree-below (caddr s4) (update-nth (+ (cadr s1) d) (val (m body vs defs fuel2)) (caddr s1))
                               (+ (cadr s1) f)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth call-tail env-ok-callee good3 m m-args clk clk-args
                                      vm-compile code-len wf3 top-ok defs-ok copy-args count-from
                                      vals-at env-ok)
                  :use ((:instance (:definition good3) (e body) (d (len vs)) (f (1+ (len vs)))
                                   (cenv (count-from 0 (len vs)))
                                   (s (w-step prog s1 top)) (env vs) (fuel fuel2))
                        (:instance env-ok-callee (fb (cadr s1)) (a f) (nb (+ f (len vs))) (regs (caddr s1)))
                        (:instance call-tail (n (len vs)) (r0 (caddr s1)) (pc3 (+ entry (code-len body)))
                                   (s3 (vm-run-wiping prog (w-step prog s1 top) (clk body vs defs fuel2) top))
                                   (v (val (m body vs defs fuel2))))))))

; the call's parts, named
(defmacro c-def () '(cdr (assoc-equal (cadr e) defs)))
(defmacro c-entry () '(cdr (assoc-equal (cadr e) fnpcs)))
(defmacro c-vs () '(val (m-args (cddr e) env defs fuel)))
(defmacro c-s1 () '(vm-run-wiping prog s (clk-args (cddr e) env defs fuel) top))

(defthm good3-call
  (implies (and (equal (car e) :call)
                (good-args (cddr e) f cenv s env defs fuel prog fnpcs top)
                (good3 (cadr (c-def)) (nfix (car (c-def))) (1+ (nfix (car (c-def))))
                       (count-from 0 (nfix (car (c-def))))
                       (w-step prog (c-s1) top)
                       (c-vs) defs (1- fuel) prog fnpcs top))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth good3 good-args body-code*)
                  :expand ((vm-compile e d f cenv (car s) fnpcs) (m e env defs fuel) (clk e env defs fuel)
                           (wf3 e (len env) defs) (top-ok e f top)
                           (body-code* (c-def) (c-entry) fnpcs))
                  :use ((:instance (:definition good3))
                        (:instance (:definition good-args) (es (cddr e)))
                        (:instance fns-ok-necc (name (cadr e)))
                        (:instance defs-ok-lookup (ds defs) (name (cadr e)))
                        (:instance call-abstract (s1 (c-s1)) (vs (c-vs)) (n (nfix (car (c-def)))) (k (len (cddr e)))
                                   (entry (c-entry)) (body (cadr (c-def))) (fuel2 (1- fuel)))))))

(defthm good3-if
  (implies (and (equal (car e) :if)
                (good3 (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                (good3 (caddr e) d f cenv (w-step prog (vm-run-wiping prog s (clk (cadr e) env defs fuel) top) top)
                       env defs fuel prog fnpcs top)
                (good3 (cadddr e) d f cenv (w-step prog (vm-run-wiping prog s (clk (cadr e) env defs fuel) top) top)
                       env defs fuel prog fnpcs top))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :cases ((truthy (cdr (m (cadr e) env defs fuel))))
                  :in-theory (disable good3))))

(defthm good3-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :call)))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local))
                  :in-theory (disable good3))))

; ---- STAGE 3's THEOREM --------------------------------------------------------

; the induction the meaning makes: each part from the state its
; predecessor left, and a call's body, in the callee's frame, at one less
; fuel
(defun ind3 (flg e d f cenv s env defs fuel prog fnpcs top)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o<
                  :ruler-extenders :all
                  :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list d f cenv s env defs fuel prog fnpcs top)
        (list (ind3 :m (car e) f (1+ f) cenv s env defs fuel prog fnpcs top)
              (ind3 :args (cdr e) d (1+ f) cenv (vm-run-wiping prog s (clk (car e) env defs fuel) top)
                    env defs fuel prog fnpcs top)))
    (case (car e)
      (:if (let ((s2 (w-step prog (vm-run-wiping prog s (clk (cadr e) env defs fuel) top) top)))
             (list (ind3 :m (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                   (ind3 :m (caddr e) d f cenv s2 env defs fuel prog fnpcs top)
                   (ind3 :m (cadddr e) d f cenv s2 env defs fuel prog fnpcs top))))
      (:let (list (ind3 :m (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                  (ind3 :m (caddr e) d (1+ f) (append cenv (list f))
                        (vm-run-wiping prog s (clk (cadr e) env defs fuel) top)
                        (append env (list (cdr (m (cadr e) env defs fuel)))) defs fuel prog fnpcs top)))
      ((:add :lt) (list (ind3 :m (cadr e) f (1+ f) cenv s env defs fuel prog fnpcs top)
                        (ind3 :m (caddr e) (1+ f) (+ 2 f) cenv
                              (vm-run-wiping prog s (clk (cadr e) env defs fuel) top)
                              env defs fuel prog fnpcs top)))
      (:call (list (ind3 :args (cddr e) d f cenv s env defs fuel prog fnpcs top)
                   (if (zp fuel)
                       nil
                     (ind3 :m (cadr (c-def)) (nfix (car (c-def))) (1+ (nfix (car (c-def))))
                           (count-from 0 (nfix (car (c-def))))
                           (w-step prog (c-s1) top)
                           (c-vs) defs (1- fuel) prog fnpcs top))))
      (otherwise (list d f cenv s env defs fuel prog fnpcs top)))))

; with no fuel a call means :out, so there is nothing to show
(defthm good3-call-no-fuel
  (implies (and (equal (car e) :call) (zp fuel))
           (good3 e d f cenv s env defs fuel prog fnpcs top))
  :hints (("Goal" :expand ((m e env defs fuel)))))

(defthm vm-call-correct-flag
  (if (eq flg :args)
      (good-args e f cenv s env defs fuel prog fnpcs top)
    (good3 e d f cenv s env defs fuel prog fnpcs top))
  :rule-classes nil
  :hints (("Goal" :induct (ind3 flg e d f cenv s env defs fuel prog fnpcs top)
                  :in-theory (union-theories '(good3-if good3-let good3-binop good3-call good3-call-no-fuel
                                               good3-leaf
                                               good-args-nil good-args-cons
                                               member-equal car-cons cdr-cons
                                               (:induction ind3))
                                             (theory 'minimal-theory)))))

; RUNNING AN EXPRESSION'S CODE ANSWERS WHAT THE MEANING DOES, calls and
; recursion included, with or without wiping above the frame's top
(defthm vm-call-good
  (good3 e d f cenv s env defs fuel prog fnpcs top)
  :hints (("Goal" :use ((:instance vm-call-correct-flag (flg :m))))))

; ---- WHOLE PROGRAMS -----------------------------------------------------------
;
; compile-program's layout puts every function's code at its entry, and
; the main expression's code first, so a program's answer is its
; meaning's -- on the plain machine, and on the wiping one with a top
; every frame fits under

(defthm vm-run-is-wiping-nil
  (equal (vm-run prog s n) (vm-run-wiping prog s n nil))
  :hints (("Goal" :induct (vm-run prog s n)
                  :in-theory (enable vm-run-wiping w-step)
                  :expand ((vm-run-wiping prog s n nil)))))

(defthm len-body-code
  (equal (len (body-code* def pc fnpcs)) (1+ (code-len (cadr def)))))
(in-theory (disable body-code*))

; where lay-out puts the entries depends on the code's lengths alone
(defthm lay-out-any-fnpcs
  (implies (syntaxp (not (equal y ''nil)))
           (equal (lay-out ds pc y) (lay-out ds pc nil))))

(defthm nth-len-append
  (equal (nth (+ (len a) (nfix i)) (append a b)) (nth i b))
  :hints (("Goal" :induct (len a))))

(defthm nth-len-append-2
  (implies (natp i) (equal (nth (+ i (len a)) (append a b)) (nth i b)))
  :hints (("Goal" :use nth-len-append :in-theory (disable nth-len-append))))

; code placed after a is placed in b, shifted
(defthm code-at-shift
  (implies (natp pc)
           (equal (code-at (append a b) (+ (len a) pc) code) (code-at b pc code)))
  :hints (("Goal" :induct (code-at b pc code) :in-theory (enable code-at)
                  :expand ((code-at (append a b) (+ pc (len a)) code)))))

(defthm nth-len-append-0
  (equal (nth (len a) (append a b)) (car b))
  :hints (("Goal" :induct (len a))))

(defun prefix-ind (p a)
  (if (endp a) p (prefix-ind (append p (list (car a))) (cdr a))))

(defthm code-at-prefix-gen
  (code-at (append p a b) (len p) a)
  :hints (("Goal" :induct (prefix-ind p a) :in-theory (enable code-at))))

(defthm code-at-prefix
  (code-at (append a b) 0 a)
  :hints (("Goal" :use ((:instance code-at-prefix-gen (p nil))))))

(defthm code-at-self-gen
  (code-at (append p x) (len p) x)
  :hints (("Goal" :induct (prefix-ind p x) :in-theory (enable code-at))))

(defthm code-at-self
  (code-at x 0 x)
  :hints (("Goal" :use ((:instance code-at-self-gen (p nil))))))

(defthm code-at-cons-shift
  (implies (natp pc) (equal (code-at (cons x d) (+ 1 pc) code) (code-at d pc code)))
  :hints (("Goal" :induct (code-at d pc code) :in-theory (enable code-at)
                  :expand ((code-at (cons x d) (+ 1 pc) code)))))

; the functions' code, laid out from pc: each name's first definition
; at the entry lay-out gives it
(defthm compile-defs-places
  (implies (and (alistp ds) (natp pc) (code-at prog pc (compile-defs ds fnpcs pc))
                (consp (assoc-equal name ds)))
           (and (natp (cdr (assoc-equal name (lay-out ds pc nil))))
                (code-at prog (cdr (assoc-equal name (lay-out ds pc nil)))
                         (body-code* (cdr (assoc-equal name ds))
                                     (cdr (assoc-equal name (lay-out ds pc nil))) fnpcs))))
  :hints (("Goal" :induct (compile-defs ds fnpcs pc))))

(defthm compile-program-fns-ok
  (implies (alistp defs)
           (fns-ok (compile-program e defs) defs
                   (lay-out defs (1+ (code-len e)) nil)))
  :hints (("Goal" :in-theory (enable fns-ok)
                  :use ((:instance compile-defs-places
                                   (ds defs) (pc (1+ (code-len e)))
                                   (prog (compile-program e defs))
                                   (fnpcs (lay-out defs (1+ (code-len e)) nil))
                                   (name (fns-ok-witness (compile-program e defs) defs
                                                         (lay-out defs (1+ (code-len e)) nil))))
                        (:instance code-at-shift (pc 1)
                                   (a (vm-compile e 0 1 nil 0 (lay-out defs (1+ (code-len e)) nil)))
                                   (b (cons '(:ret 0)
                                            (compile-defs defs (lay-out defs (1+ (code-len e)) nil) (1+ (code-len e)))))
                                   (code (compile-defs defs (lay-out defs (1+ (code-len e)) nil) (1+ (code-len e)))))))))

; the main expression's return, with no caller, halts: it writes register
; 0 of frame 0 into itself and stays where it is
(defthm wstep-halt
  (implies (and (statep s) (equal (car (ins-of s)) :ret) (not (consp (cadddr s))))
           (equal (w-step prog s top)
                  (list (car s) (cadr s)
                        (update-nth 0 (nth (+ (cadr s) (nfix (cadr (ins-of s)))) (caddr s)) (caddr s))
                        (cadddr s))))
  :hints (("Goal" :in-theory (enable w-step vm-step statep))))

(defthm halted-stays
  (implies (and (statep s) (equal (cadr s) 0) (not (consp (cadddr s)))
                (code-at prog (car s) (list (list :ret 0))))
           (let ((s2 (vm-run-wiping prog s k top)))
             (and (statep s2) (equal (car s2) (car s)) (equal (cadr s2) 0) (not (consp (cadddr s2)))
                  (equal (nth 0 (caddr s2)) (nth 0 (caddr s))))))
  :hints (("Goal" :induct (vm-run-wiping prog s k top)
                  :in-theory (enable vm-run-wiping)
                  :expand ((vm-run-wiping prog s k top)))))

(defthm code-at-head
  (code-at (cons x d) 0 (list x))
  :hints (("Goal" :in-theory (enable code-at))))

(defthm program-answer
  (implies (and (alistp defs) (defs-ok defs defs top) (wf3 e 0 defs)
                (or (not top) (top-ok e 1 top))
                (valp (m e nil defs fuel)) (natp k))
           (equal (answer (vm-run-wiping (compile-program e defs) (list 0 0 nil nil)
                                         (+ (clk e nil defs fuel) k) top))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable good3 vm-call-good halted-stays compile-program compile-program-fns-ok run-plus)
                  :use ((:instance compile-program-fns-ok)
                        (:instance run-plus (prog (compile-program e defs)) (s (list 0 0 nil nil))
                                   (a (clk e nil defs fuel)) (b k))
                        (:instance vm-call-good (d 0) (f 1) (cenv nil) (s (list 0 0 nil nil)) (env nil)
                                   (prog (compile-program e defs))
                                   (fnpcs (lay-out defs (1+ (code-len e)) nil)))
                        (:instance (:definition good3) (d 0) (f 1) (cenv nil) (s (list 0 0 nil nil)) (env nil)
                                   (prog (compile-program e defs))
                                   (fnpcs (lay-out defs (1+ (code-len e)) nil)))
                        (:instance halted-stays (prog (compile-program e defs))
                                   (s (vm-run-wiping (compile-program e defs) (list 0 0 nil nil)
                                                     (clk e nil defs fuel) top)))
                        (:instance agree-nth (r 0) (h 1)
                                   (a (caddr (vm-run-wiping (compile-program e defs) (list 0 0 nil nil)
                                                            (clk e nil defs fuel) top)))
                                   (b (update-nth 0 (cdr (m e nil defs fuel)) nil)))
                        (:instance code-at-shift (pc 0)
                                   (a (vm-compile e 0 1 nil 0 (lay-out defs (1+ (code-len e)) nil)))
                                   (b (cons '(:ret 0)
                                            (compile-defs defs (lay-out defs (1+ (code-len e)) nil) (1+ (code-len e)))))
                                   (code '((:ret 0))))))
          ("Goal'" :in-theory (enable compile-program))))

; STAGE 3: a compiled program, calls and recursion included, answers what
; its meaning does, once its clock has run -- and keeps answering
(defthm vm-call-correct
  (implies (and (alistp defs) (defs-ok defs defs nil) (wf3 e 0 defs)
                (valp (m e nil defs fuel)) (natp k))
           (equal (answer (run-program e defs (+ (clk e nil defs fuel) k)))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable program-answer compile-program)
                  :use ((:instance program-answer (top nil))))))

; ROOTING: the same answer when every register from the caller's frame
; top up is wiped at each return, for any top every frame's calls fit
; under -- the machine holds nothing a computation still needs anywhere
; a collector scanning the value stack below the live top would miss
(defthm vm-call-rooted
  (implies (and (alistp defs) (defs-ok defs defs top) (wf3 e 0 defs) top (top-ok e 1 top)
                (valp (m e nil defs fuel)) (natp k))
           (equal (answer (vm-run-wiping (compile-program e defs) (list 0 0 nil nil)
                                         (+ (clk e nil defs fuel) k) top))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable program-answer compile-program)
                  :use ((:instance program-answer)))))

; ---- THE HYPOTHESES ARE NOT VACUOUS ----------------------------------------
;
; the design's examples meet them: well formed, natural arities, every
; frame's calls under top 12 -- and top-ok refuses top 1, the top the
; design book's negative control shows changes an answer, so the
; rooting theorem's bound is the one that matters

(defun all-ok (es defs top)
  (if (atom es)
      t
    (and (wf3 (car es) 0 defs) (or (not top) (top-ok (car es) 1 top))
         (all-ok (cdr es) defs top))))

(assert-event (and (alistp *defs*) (defs-ok *defs* *defs* nil) (all-ok *exprs* *defs* nil)))
(assert-event (and (defs-ok *defs* *defs* 12) (all-ok *exprs* *defs* 12)))
(assert-event (not (and (defs-ok *defs* *defs* 1) (all-ok *exprs* *defs* 1))))

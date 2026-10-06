; clotran's VM, formally (PLAN step 30). The theorems about the call
; model/vm-closure.lisp designs: a closure called through a register,
; its arguments already where the callee's frame begins.
;
; THE THEOREM keeps model/vm-call-proof.lisp's shape: running an
; expression's code for its clock leaves its value in the target
; register, nothing below the first free register otherwise changed,
; and the frame base and the return records as they were -- a call is
; invisible to its caller but for its answer. What is new: the callee
; is whatever closure a register holds, a body reads its captures
; through its own closure, which the call leaves in the callee's frame
; at register n, and nothing is copied into the frame. So the callee's
; locals are the caller's argument registers, read in place.
;
;   vc-correct   a compiled program answers what the meaning does
;
; This book proves the register machine; the one-stack machine
; (vcs-step) is fuzzed against the same meaning by
; scripts/fuzz-vm-closure, and its proof follows the same steps.

(in-package "ACL2")

(include-book "vm-closure")
(include-book "arithmetic-5/top" :dir :system)

(defun c+ (a b) (+ (nfix a) (nfix b)))

; ---- THE CLOCK --------------------------------------------------------------
;
; steps an expression's code takes. A call: its arguments, its callee,
; the call, the callee's body, the return.

(defmacro cv-rf () '(mc (cadr e) env caps defs fuel))
(defmacro cv-def () '(cdr (assoc-equal (clo-f (val (cv-rf))) defs)))
(defmacro cv-vs () '(val (mc-args (cddr e) env caps defs fuel)))

(mutual-recursion
 (defun cclk (e env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (c+ (cclk (cadr e) env caps defs fuel)
              (c+ 1 (if (truthy (val (mc (cadr e) env caps defs fuel)))
                        (c+ (cclk (caddr e) env caps defs fuel) 1)
                      (cclk (cadddr e) env caps defs fuel)))))
     (:let (c+ (cclk (cadr e) env caps defs fuel)
               (cclk (caddr e) (append env (list (val (mc (cadr e) env caps defs fuel)))) caps defs fuel)))
     ((:add :lt) (c+ (cclk (cadr e) env caps defs fuel) (c+ (cclk (caddr e) env caps defs fuel) 1)))
     (:mkclo (c+ (cclk-args (cddr e) env caps defs fuel) 1))
     (:callv (if (zp fuel)
                 (c+ (cclk-args (cddr e) env caps defs fuel) (c+ (cclk (cadr e) env caps defs fuel) 1))
               (c+ (cclk-args (cddr e) env caps defs fuel)
                   (c+ (cclk (cadr e) env caps defs fuel)
                       (c+ 1 (c+ (cclk (cadr (cv-def)) (cv-vs) (clo-caps (val (cv-rf))) defs (1- fuel))
                                 1))))))
     (otherwise 1)))
 (defun cclk-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (c+ (cclk (car es) env caps defs fuel) (cclk-args (cdr es) env caps defs fuel)))))

; ---- WHAT THE THEOREM ASSUMES -----------------------------------------------

; locals below n. A capture or a call needs nothing static: the callee
; is a value, and a call of the wrong thing is an error, not a val.
(mutual-recursion
 (defun cwf (e n)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:local (and (natp (cadr e)) (< (cadr e) (nfix n))))
     (:if (and (cwf (cadr e) n) (cwf (caddr e) n) (cwf (cadddr e) n)))
     (:let (and (cwf (cadr e) n) (cwf (caddr e) (1+ (nfix n)))))
     ((:add :lt) (and (cwf (cadr e) n) (cwf (caddr e) n)))
     ((:mkclo) (cwf-args (cddr e) n))
     (:callv (and (cwf (cadr e) n) (cwf-args (cddr e) n)))
     (otherwise t)))
 (defun cwf-args (es n)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) t (and (cwf (car es) n) (cwf-args (cdr es) n)))))

; every function's body well formed for its arity
(defun cdefs-ok (ds)
  (if (atom ds)
      t
    (and (consp (car ds)) (consp (cdar ds)) (natp (car (cdar ds)))
         (cwf (cadr (cdar ds)) (car (cdar ds)))
         (cdefs-ok (cdr ds)))))

(defthm cdefs-ok-lookup
  (implies (and (cdefs-ok ds) (consp (assoc-equal name ds)))
           (and (natp (car (cdr (assoc-equal name ds))))
                (cwf (cadr (cdr (assoc-equal name ds))) (car (cdr (assoc-equal name ds)))))))

; code sits in the code at pc
(defun ccode-at (code pc c)
  (declare (xargs :measure (acl2-count c)))
  (if (endp c)
      t
    (and (equal (nth pc code) (car c))
         (ccode-at code (1+ pc) (cdr c)))))

; every function's entry in the table: its arity, and its body's code there
(defun-sk cfns-ok (prog defs)
  (forall name
          (implies (consp (assoc-equal name defs))
                   (let ((ent (cdr (assoc-equal name (cdr prog))))
                         (def (cdr (assoc-equal name defs))))
                     (and (consp ent) (natp (car ent))
                          (equal (nfix (cadr ent)) (nfix (car def)))
                          (ccode-at (car prog) (car ent) (vc-body def (car ent))))))))

(in-theory (disable cfns-ok))

; local i's register holds its value, below the first free register
(defun cenv-ok (cenv env regs fb f)
  (if (endp cenv)
      (endp env)
    (and (consp env)
         (natp (car cenv)) (< (car cenv) (nfix f))
         (equal (nth (+ (nfix fb) (car cenv)) regs) (car env))
         (cenv-ok (cdr cenv) (cdr env) regs fb f))))

; the body's own closure, which its captures are read through, in
; register self below the first free one; main has none, and no captures
(defun cself-ok (self caps regs fb f)
  (if (natp self)
      (and (< self (nfix f))
           (equal (clo-caps (nth (+ (nfix fb) self) regs)) caps))
    (and (null self) (null caps))))

(defun cstatep (s)
  (and (true-listp s) (equal (len s) 4) (natp (car s)) (natp (cadr s))))

(defun cvals-at (k vs regs)
  (declare (xargs :measure (acl2-count vs)))
  (if (atom vs)
      t
    (and (equal (nth k regs) (car vs)) (cvals-at (1+ k) (cdr vs) regs))))

(mutual-recursion
 (defun ccode-len (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ (ccode-len (cadr e)) 1 (ccode-len (caddr e)) 1 (ccode-len (cadddr e))))
     (:let (+ (ccode-len (cadr e)) (ccode-len (caddr e))))
     ((:add :lt) (+ (ccode-len (cadr e)) (ccode-len (caddr e)) 1))
     (:mkclo (+ (ccode-len-args (cddr e)) 1))
     (:callv (+ (ccode-len-args (cddr e)) (ccode-len (cadr e)) 1))
     (otherwise 1)))
 (defun ccode-len-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (ccode-len (car es)) (ccode-len-args (cdr es))))))

(defun-sk cagree (a b h)
  (forall r (implies (and (natp r) (< r (nfix h))) (equal (nth r a) (nth r b)))))

; THE PROPERTY
(defun cgood (e d f cenv self caps s env defs fuel prog)
  (implies (and (cstatep s)
                (ccode-at (car prog) (car s) (vc-compile e d f cenv self (car s)))
                (natp d) (natp f) (< d f)
                (cwf e (len env)) (cenv-ok cenv env (caddr s) (cadr s) f)
                (cself-ok self caps (caddr s) (cadr s) f)
                (cdefs-ok defs) (cfns-ok prog defs))
           (let ((r (mc e env caps defs fuel)) (s2 (vc-run prog s (cclk e env caps defs fuel))))
             (implies (valp r)
                      (and (cstatep s2)
                           (equal (car s2) (+ (car s) (ccode-len e)))
                           (equal (cadr s2) (cadr s))
                           (equal (cadddr s2) (cadddr s))
                           (cagree (caddr s2) (update-nth (+ (cadr s) d) (val r) (caddr s))
                                   (+ (cadr s) f)))))))

(defun cgood-args (es f cenv self caps s env defs fuel prog)
  (implies (and (cstatep s)
                (ccode-at (car prog) (car s) (vc-compile-args es f cenv self (car s)))
                (natp f)
                (cwf-args es (len env)) (cenv-ok cenv env (caddr s) (cadr s) f)
                (cself-ok self caps (caddr s) (cadr s) f)
                (cdefs-ok defs) (cfns-ok prog defs))
           (let ((r (mc-args es env caps defs fuel)) (s2 (vc-run prog s (cclk-args es env caps defs fuel))))
             (implies (valp r)
                      (and (cstatep s2)
                           (equal (car s2) (+ (car s) (ccode-len-args es)))
                           (equal (cadr s2) (cadr s))
                           (equal (cadddr s2) (cadddr s))
                           (cagree (caddr s2) (caddr s) (+ (cadr s) f))
                           (cvals-at (+ (cadr s) f) (val r) (caddr s2)))))))

; ---- the machine's runs -------------------------------------------------------

(in-theory (disable vc-step))

(defthm vc-run-plus
  (implies (and (natp a) (natp b))
           (equal (vc-run prog s (+ a b)) (vc-run prog (vc-run prog s a) b)))
  :hints (("Goal" :induct (vc-run prog s a))))

(defthm vc-run-c+
  (equal (vc-run prog s (c+ a b)) (vc-run prog (vc-run prog s (nfix a)) (nfix b)))
  :hints (("Goal" :use ((:instance vc-run-plus (a (nfix a)) (b (nfix b)))))))
(in-theory (disable c+))

(defthm len-of-append (equal (len (append a b)) (+ (len a) (len b))))
(defthm append-assoc (equal (append (append a b) c) (append a (append b c))))

(defthm vc-run-0 (equal (vc-run prog s 0) s))
(defthm vc-run-1 (equal (vc-run prog s 1) (vc-step prog s)))
(in-theory (disable vc-run))

(defthm ccode-at-append
  (equal (ccode-at code pc (append a b))
         (and (ccode-at code pc a) (ccode-at code (+ pc (len a)) b))))

(defthm ccode-at-first
  (implies (and (ccode-at code pc c) (consp c))
           (equal (nth pc code) (car c))))

(defthm ccode-at-cons-split
  (implies (syntaxp (not (equal rest (quote (quote nil)))))
           (equal (ccode-at code pc (cons i rest))
                  (and (ccode-at code pc (list i)) (ccode-at code (1+ pc) rest))))
  :hints (("Goal" :expand ((ccode-at code pc (cons i rest)) (ccode-at code pc (list i))))))

(in-theory (disable ccode-at))

(defun cvc-ind (flg e d f cenv self pc)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (cvc-ind :m (car e) f (1+ f) cenv self pc)
              (cvc-ind :args (cdr e) d (1+ f) cenv self
                       (+ pc (len (vc-compile (car e) f (1+ f) cenv self pc))))))
    (case (car e)
      (:if (let* ((cc (vc-compile (cadr e) f (1+ f) cenv self pc))
                  (pc1 (+ pc (len cc) 1))
                  (tc (vc-compile (caddr e) d f cenv self pc1))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (cvc-ind :m (cadr e) f (1+ f) cenv self pc)
                   (cvc-ind :m (caddr e) d f cenv self pc1)
                   (cvc-ind :m (cadddr e) d f cenv self pc2))))
      (:let (let ((ic (vc-compile (cadr e) f (1+ f) cenv self pc)))
              (list (cvc-ind :m (cadr e) f (1+ f) cenv self pc)
                    (cvc-ind :m (caddr e) d (1+ f) (append cenv (list f)) self (+ pc (len ic))))))
      ((:add :lt) (let ((ac (vc-compile (cadr e) f (1+ f) cenv self pc)))
                    (list (cvc-ind :m (cadr e) f (1+ f) cenv self pc)
                          (cvc-ind :m (caddr e) (1+ f) (+ 2 f) cenv self (+ pc (len ac))))))
      (:mkclo (cvc-ind :args (cddr e) d f cenv self pc))
      (:callv (let ((ac (vc-compile-args (cddr e) f cenv self pc)))
                (list (cvc-ind :args (cddr e) d f cenv self pc)
                      (cvc-ind :m (cadr e) (+ f (len (cddr e))) (+ f (len (cddr e)) 1) cenv self
                               (+ pc (len ac))))))
      (otherwise (list d f cenv self pc)))))

(defthm len-vc-compile-flag
  (if (eq flg :args)
      (equal (len (vc-compile-args e f cenv self pc)) (ccode-len-args e))
    (equal (len (vc-compile e d f cenv self pc)) (ccode-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (cvc-ind flg e d f cenv self pc))))

(defthm len-vc-compile
  (equal (len (vc-compile e d f cenv self pc)) (ccode-len e))
  :hints (("Goal" :use ((:instance len-vc-compile-flag (flg :m))))))

(defthm len-vc-compile-args
  (equal (len (vc-compile-args es f cenv self pc)) (ccode-len-args es))
  :hints (("Goal" :use ((:instance len-vc-compile-flag (flg :args) (e es))))))

; ---- registers that agree below h ----------------------------------------

(in-theory (disable cagree))

(defthm cagree-refl (cagree a a h)
  :hints (("Goal" :in-theory (enable cagree))))

(defthm cagree-trans
  (implies (and (cagree a b h) (cagree b c h)) (cagree a c h))
  :hints (("Goal" :use ((:instance cagree-necc (r (cagree-witness a c h)))
                        (:instance cagree-necc (a b) (b c) (r (cagree-witness a c h))))
                  :expand ((cagree a c h)))))

(defthm cagree-smaller
  (implies (and (cagree a b h) (<= (nfix g) (nfix h))) (cagree a b g))
  :hints (("Goal" :use ((:instance cagree-necc (r (cagree-witness a b g))))
                  :expand ((cagree a b g)))))

(defthm cagree-write-above
  (implies (and (natp d) (<= (nfix h) d)) (cagree (update-nth d v a) a h))
  :hints (("Goal" :expand ((cagree (update-nth d v a) a h)))))

(defthm cagree-same-write
  (implies (and (natp d) (cagree a b h)) (cagree (update-nth d v a) (update-nth d v b) h))
  :hints (("Goal" :use ((:instance cagree-necc
                         (r (cagree-witness (update-nth d v a) (update-nth d v b) h))))
                  :expand ((cagree (update-nth d v a) (update-nth d v b) h)))))

(defthm cagree-sym
  (implies (cagree a b h) (cagree b a h))
  :hints (("Goal" :use ((:instance cagree-necc (r (cagree-witness b a h))))
                  :expand ((cagree b a h)))))

(defthm cagree-nth
  (implies (and (cagree a b h) (natp r) (< r (nfix h)))
           (equal (nth r a) (nth r b)))
  :hints (("Goal" :use cagree-necc)))

(defthm cagree-past-write
  (implies (and (cagree a (update-nth g w b) h) (natp g)
                (<= (nfix f) g) (<= (nfix f) (nfix h)))
           (cagree a b f))
  :hints (("Goal" :use ((:instance cagree-smaller (b (update-nth g w b)) (g f))
                        (:instance cagree-write-above (d g) (v w) (a b) (h f))
                        (:instance cagree-trans (b (update-nth g w b)) (c b) (h f))))))

(defthm cagree-past-two-writes
  (implies (and (cagree a (update-nth g1 w1 b) h1) (cagree b (update-nth g2 w2 c) h2)
                (natp g1) (natp g2) (<= (nfix f) g1) (<= (nfix f) g2)
                (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (cagree a c f))
  :hints (("Goal" :use ((:instance cagree-past-write (g g1) (w w1) (h h1))
                        (:instance cagree-past-write (a b) (b c) (g g2) (w w2) (h h2))
                        (:instance cagree-trans (a a) (b b) (c c) (h f))))))

(defthm cagree-then-write
  (implies (and (cagree a b h1) (cagree b (update-nth g w c) h2)
                (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (cagree a c f))
  :hints (("Goal" :use ((:instance cagree-past-write (a b) (b c) (h h2))
                        (:instance cagree-smaller (a a) (b b) (h h1) (g f))
                        (:instance cagree-trans (a a) (b b) (c c) (h f))))))

(defthm cagree-compose
  (implies (and (cagree x (update-nth d v r1) h1) (cagree r1 (update-nth g w r0) h2)
                (natp d) (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (cagree x (update-nth d v r0) f))
  :hints (("Goal" :use ((:instance cagree-past-write (a r1) (b r0) (h h2))
                        (:instance cagree-same-write (a r1) (b r0) (h f))
                        (:instance cagree-smaller (a x) (b (update-nth d v r1)) (h h1) (g f))
                        (:instance cagree-trans (a x) (b (update-nth d v r1)) (c (update-nth d v r0)) (h f))))))

; ---- locals and the closure in a frame --------------------------------------

(defthm cenv-ok-agree
  (implies (and (cenv-ok cenv env a fb f) (cagree a b (+ (nfix fb) (nfix f))))
           (cenv-ok cenv env b fb f))
  :hints (("Goal" :induct (cenv-ok cenv env a fb f))
          ("Subgoal *1/2" :use ((:instance cagree-necc (r (+ (nfix fb) (car cenv)))
                                           (h (+ (nfix fb) (nfix f))))))))

(defthm cenv-ok-local-cenv
  (implies (and (cenv-ok cenv env regs fb f) (natp fb) (natp i) (< i (len cenv)))
           (and (equal (nth (+ fb (nth i cenv)) regs) (nth i env))
                (natp (nth i cenv))
                (integerp (nth i cenv))
                (<= 0 (nth i cenv))
                (< (nth i cenv) (nfix f)))))

(defthm cenv-ok-bigger-f
  (implies (and (cenv-ok cenv env regs fb f) (<= (nfix f) (nfix g)))
           (cenv-ok cenv env regs fb g)))

(defthm cenv-ok-len
  (implies (cenv-ok cenv env regs fb f) (equal (len cenv) (len env)))
  :rule-classes :forward-chaining)

(defthm cenv-ok-append
  (implies (equal (len c1) (len e1))
           (equal (cenv-ok (append c1 c2) (append e1 e2) regs fb f)
                  (and (cenv-ok c1 e1 regs fb f) (cenv-ok c2 e2 regs fb f)))))

(defthm cenv-ok-after-run
  (implies (and (cenv-ok cenv env regs fb f) (cagree regs1 (update-nth g v regs) h)
                (natp g) (<= (+ (nfix fb) (nfix f)) g) (<= (+ (nfix fb) (nfix f)) (nfix h))
                (<= (nfix f) (nfix k)))
           (cenv-ok cenv env regs1 fb k))
  :hints (("Goal" :use ((:instance cagree-past-write (a regs1) (b regs) (w v) (f (+ (nfix fb) (nfix f))))
                        (:instance cagree-sym (a regs1) (b regs) (h (+ (nfix fb) (nfix f))))
                        (:instance cenv-ok-agree (a regs) (b regs1))
                        (:instance cenv-ok-bigger-f (regs regs1) (g k))))))

(defthm cenv-ok-after-args
  (implies (and (cenv-ok cenv env regs fb f) (cagree regs1 regs (+ (nfix fb) (nfix f))))
           (cenv-ok cenv env regs1 fb f))
  :hints (("Goal" :use ((:instance cagree-sym (a regs1) (b regs) (h (+ (nfix fb) (nfix f))))
                        (:instance cenv-ok-agree (a regs) (b regs1))))))

(defthm cself-ok-agree
  (implies (and (cself-ok self caps a fb f) (cagree a b (+ (nfix fb) (nfix f))))
           (cself-ok self caps b fb f))
  :hints (("Goal" :use ((:instance cagree-necc (r (+ (nfix fb) self)) (h (+ (nfix fb) (nfix f))))))))

(defthm cself-ok-bigger-f
  (implies (and (cself-ok self caps regs fb f) (<= (nfix f) (nfix g)))
           (cself-ok self caps regs fb g)))

(defthm cself-ok-after-run
  (implies (and (cself-ok self caps regs fb f) (cagree regs1 (update-nth g v regs) h)
                (natp g) (<= (+ (nfix fb) (nfix f)) g) (<= (+ (nfix fb) (nfix f)) (nfix h))
                (<= (nfix f) (nfix k)))
           (cself-ok self caps regs1 fb k))
  :hints (("Goal" :in-theory (disable cself-ok)
                  :use ((:instance cagree-past-write (a regs1) (b regs) (w v) (f (+ (nfix fb) (nfix f))))
                        (:instance cagree-sym (a regs1) (b regs) (h (+ (nfix fb) (nfix f))))
                        (:instance cself-ok-agree (a regs) (b regs1))
                        (:instance cself-ok-bigger-f (regs regs1) (g k))))))

(defthm cself-ok-after-args
  (implies (and (cself-ok self caps regs fb f) (cagree regs1 regs (+ (nfix fb) (nfix f))))
           (cself-ok self caps regs1 fb f))
  :hints (("Goal" :in-theory (disable cself-ok)
                  :use ((:instance cagree-sym (a regs1) (b regs) (h (+ (nfix fb) (nfix f))))
                        (:instance cself-ok-agree (a regs) (b regs1))))))

; ---- the machine, a step at a time ---------------------------------------

(in-theory (enable vc-step))

(defmacro cins (s) `(nth (car ,s) (car prog)))

(defthm vstep-loadk
  (implies (and (cstatep s) (equal (car (cins s)) :loadk))
           (equal (vc-step prog s)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (cins s)))) (caddr (cins s)) (caddr s))
                        (cadddr s)))))
(defthm vstep-move
  (implies (and (cstatep s) (equal (car (cins s)) :move))
           (equal (vc-step prog s)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (cins s))))
                                    (nth (+ (cadr s) (nfix (caddr (cins s)))) (caddr s)) (caddr s))
                        (cadddr s)))))
(defthm vstep-add
  (implies (and (cstatep s) (equal (car (cins s)) :add))
           (equal (vc-step prog s)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (cins s))))
                                    (+ (fix (nth (+ (cadr s) (nfix (caddr (cins s)))) (caddr s)))
                                       (fix (nth (+ (cadr s) (nfix (cadddr (cins s)))) (caddr s))))
                                    (caddr s))
                        (cadddr s)))))
(defthm vstep-lt
  (implies (and (cstatep s) (equal (car (cins s)) :lt))
           (equal (vc-step prog s)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (cins s))))
                                    (bool (< (rfix (nth (+ (cadr s) (nfix (caddr (cins s)))) (caddr s)))
                                             (rfix (nth (+ (cadr s) (nfix (cadddr (cins s)))) (caddr s)))))
                                    (caddr s))
                        (cadddr s)))))
(defthm vstep-jmpf
  (implies (and (cstatep s) (equal (car (cins s)) :jmpf))
           (equal (vc-step prog s)
                  (if (truthy (nth (+ (cadr s) (nfix (cadr (cins s)))) (caddr s)))
                      (list (1+ (car s)) (cadr s) (caddr s) (cadddr s))
                    (list (nfix (caddr (cins s))) (cadr s) (caddr s) (cadddr s))))))
(defthm vstep-jmp
  (implies (and (cstatep s) (equal (car (cins s)) :jmp))
           (equal (vc-step prog s)
                  (list (nfix (cadr (cins s))) (cadr s) (caddr s) (cadddr s)))))
(defthm vstep-mkclo
  (implies (and (cstatep s) (equal (car (cins s)) :mkclo))
           (equal (vc-step prog s)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (cins s))))
                                    (clo (caddr (cins s))
                                         (regs-from (cadr s) (cadddr (cins s)) (car (cddddr (cins s))) (caddr s)))
                                    (caddr s))
                        (cadddr s)))))
(defthm vstep-capt
  (implies (and (cstatep s) (equal (car (cins s)) :capt))
           (equal (vc-step prog s)
                  (list (1+ (car s)) (cadr s)
                        (update-nth (+ (cadr s) (nfix (cadr (cins s))))
                                    (nth (nfix (cadddr (cins s)))
                                         (clo-caps (nth (+ (cadr s) (nfix (caddr (cins s)))) (caddr s))))
                                    (caddr s))
                        (cadddr s)))))
; a call of a closure of the right arity: the record, the base, the jump
(defthm vstep-callv
  (implies (and (cstatep s) (equal (car (cins s)) :callv)
                (clop (nth (+ (cadr s) (nfix (caddr (cins s))) (nfix (car (cddddr (cins s))))) (caddr s)))
                (consp (cdr (assoc-equal (clo-f (nth (+ (cadr s) (nfix (caddr (cins s))) (nfix (car (cddddr (cins s))))) (caddr s)))
                                         (cdr prog))))
                (equal (nfix (cadddr (cins s)))
                       (nfix (cadr (cdr (assoc-equal (clo-f (nth (+ (cadr s) (nfix (caddr (cins s))) (nfix (car (cddddr (cins s))))) (caddr s)))
                                                     (cdr prog)))))))
           (equal (vc-step prog s)
                  (list (nfix (car (cdr (assoc-equal (clo-f (nth (+ (cadr s) (nfix (caddr (cins s))) (nfix (car (cddddr (cins s))))) (caddr s)))
                                                     (cdr prog)))))
                        (+ (cadr s) (nfix (caddr (cins s))))
                        (caddr s)
                        (cons (list (1+ (car s)) (cadr s) (cadr (cins s))) (cadddr s))))))
(defthm vstep-ret
  (implies (and (cstatep s) (equal (car (cins s)) :ret) (consp (cadddr s)))
           (equal (vc-step prog s)
                  (list (nfix (car (car (cadddr s)))) (nfix (cadr (car (cadddr s))))
                        (update-nth (+ (nfix (cadr (car (cadddr s)))) (nfix (caddr (car (cadddr s)))))
                                    (nth (+ (cadr s) (nfix (cadr (cins s)))) (caddr s))
                                    (caddr s))
                        (cdr (cadddr s))))))
(in-theory (disable vc-step))

(defthm cstatep-fc
  (implies (cstatep s) (and (natp (car s)) (natp (cadr s))))
  :rule-classes :forward-chaining)
(defthm cstatep-list
  (equal (cstatep (list pc fb regs ctl)) (and (natp pc) (natp fb))))
(in-theory (disable cstatep))

; ---- values a call's arguments leave --------------------------------------

(defthm mc-args-val-shape
  (implies (valp (mc-args es env caps defs fuel))
           (and (equal (len (val (mc-args es env caps defs fuel))) (len es))
                (true-listp (val (mc-args es env caps defs fuel)))))
  :hints (("Goal" :induct (len es) :expand ((mc-args es env caps defs fuel)))))

(defthm cvals-at-agree
  (implies (and (cvals-at k vs a) (cagree b a h) (natp k) (<= (+ k (len vs)) (nfix h)))
           (cvals-at k vs b))
  :hints (("Goal" :induct (cvals-at k vs a))
          ("Subgoal *1/2" :use ((:instance cagree-necc (a b) (b a) (r k))))))

(defun rf-ind (a vs)
  (if (atom vs) a (rf-ind (1+ a) (cdr vs))))

(defthm regs-from-vals
  (implies (and (natp fb) (natp a) (cvals-at (+ fb a) vs regs) (true-listp vs))
           (equal (regs-from fb a (len vs) regs) vs))
  :hints (("Goal" :induct (rf-ind a vs) :expand ((regs-from fb a (len vs) regs)))))

(defun cfi-ind (i vs)
  (if (atom vs) i (cfi-ind (1+ i) (cdr vs))))

; the callee's locals ARE the caller's argument registers: local i of
; the frame at base is register base+i, which holds argument i
(defthm cenv-ok-count-from
  (implies (and (natp i) (natp n) (natp base) (equal (+ i (len vs)) n) (<= n (nfix g))
                (cvals-at (+ base i) vs regs))
           (cenv-ok (count-from i n) vs regs base g))
  :hints (("Goal" :induct (cfi-ind i vs) :expand ((count-from i n)))))

; ---- each kind of expression, given its parts --------------------------------

(defthm cgood-const
  (implies (equal (car e) :const) (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm cgood-local
  (implies (equal (car e) :local) (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm nth-of-nil (equal (nth i nil) nil))

(defthm cgood-capt
  (implies (equal (car e) :capt) (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :cases ((natp self)))))

(defthm cgood-other
  (implies (not (member-equal (car e) '(:const :local :capt :if :let :add :lt :mkclo :callv)))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm cgood-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (cgood (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                (cgood (caddr e) (1+ f) (+ 2 f) cenv self caps (vc-run prog s (cclk (cadr e) env caps defs fuel))
                       env defs fuel prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vc-compile e d f cenv self (car s))))))

(defthm cgood-let
  (implies (and (equal (car e) :let)
                (cgood (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                (cgood (caddr e) d (1+ f) (append cenv (list f)) self caps
                       (vc-run prog s (cclk (cadr e) env caps defs fuel))
                       (append env (list (cdr (mc (cadr e) env caps defs fuel)))) defs fuel prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vc-compile e d f cenv self (car s))))))

(defthm cgood-if-true
  (implies (and (equal (car e) :if)
                (truthy (cdr (mc (cadr e) env caps defs fuel)))
                (cgood (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                (cgood (caddr e) d f cenv self caps (vc-step prog (vc-run prog s (cclk (cadr e) env caps defs fuel)))
                       env defs fuel prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vc-compile e d f cenv self (car s))))))

(defthm cgood-if-false
  (implies (and (equal (car e) :if)
                (not (truthy (cdr (mc (cadr e) env caps defs fuel))))
                (cgood (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                (cgood (cadddr e) d f cenv self caps (vc-step prog (vc-run prog s (cclk (cadr e) env caps defs fuel)))
                       env defs fuel prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vc-compile e d f cenv self (car s))))))

(defthm cgood-args-nil
  (implies (atom es) (cgood-args es f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm cgood-args-cons
  (implies (and (consp es)
                (cgood (car es) f (1+ f) cenv self caps s env defs fuel prog)
                (cgood-args (cdr es) (1+ f) cenv self caps (vc-run prog s (cclk (car es) env caps defs fuel))
                            env defs fuel prog))
           (cgood-args es f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((vc-compile-args es f cenv self (car s))
                           (mc-args es env caps defs fuel)
                           (cvals-at (+ (cadr s) f) (val (mc-args es env caps defs fuel))
                                     (caddr (vc-run prog s (cclk-args es env caps defs fuel))))))))

(defthm cgood-mkclo
  (implies (and (equal (car e) :mkclo)
                (cgood-args (cddr e) f cenv self caps s env defs fuel prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth cgood-args)
                  :expand ((vc-compile e d f cenv self (car s)) (mc e env caps defs fuel)
                           (cclk e env caps defs fuel) (cwf e (len env)))
                  :use ((:instance (:definition cgood-args) (es (cddr e)))
                        (:instance mc-args-val-shape (es (cddr e)))
                        (:instance regs-from-vals (fb (cadr s)) (a f)
                                   (vs (cdr (mc-args (cddr e) env caps defs fuel)))
                                   (regs (caddr (vc-run prog s (cclk-args (cddr e) env caps defs fuel)))))
                        (:instance cagree-same-write (d (+ d (cadr s)))
                                   (v (clo (cadr e) (cdr (mc-args (cddr e) env caps defs fuel))))
                                   (a (caddr (vc-run prog s (cclk-args (cddr e) env caps defs fuel))))
                                   (b (caddr s)) (h (+ f (cadr s))))))))

; ---- a call -------------------------------------------------------------------

(defthm natp-cclk
  (natp (cclk e env caps defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((cclk e env caps defs fuel))))
  :rule-classes :type-prescription)
(defthm natp-cclk-args
  (natp (cclk-args es env caps defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((cclk-args es env caps defs fuel))))
  :rule-classes :type-prescription)

; the return: the callee's answer, in its register m, into the caller's
; destination; below the caller's first free register only that changed
(defthm cret-to-caller
  (implies (and (natp pc) (equal (nth pc (car prog)) (list :ret m)) (natp m)
                (natp rpc) (natp fb) (natp d) (natp f) (< d f)
                (natp cb) (<= (+ fb f) cb)
                (cagree regs (update-nth (+ cb m) v ca) (+ 1 cb m))
                (cagree ca r0 (+ fb f)))
           (let ((s4 (vc-step prog (list pc cb regs (cons (list rpc fb d) ctl)))))
             (and (equal (car s4) rpc) (equal (cadr s4) fb) (equal (cadddr s4) ctl)
                  (cstatep s4)
                  (cagree (caddr s4) (update-nth (+ fb d) v r0) (+ fb f)))))
  :hints (("Goal" :in-theory (disable nth update-nth cagree-nth cagree-past-write)
                  :use ((:instance cagree-nth (a regs) (b (update-nth (+ cb m) v ca))
                                   (h (+ 1 cb m)) (r (+ cb m)))
                        (:instance cagree-past-write (a regs) (b ca) (g (+ cb m)) (w v)
                                   (h (+ 1 cb m)) (f (+ fb f)))
                        (:instance cagree-trans (a regs) (b ca) (c r0) (h (+ fb f)))
                        (:instance cagree-same-write (a regs) (b r0) (d (+ fb d)) (h (+ fb f)))))))

(defthm clist-of-one
  (implies (and (true-listp x) (equal (len x) 1)) (equal x (list (car x))))
  :rule-classes nil
  :hints (("Goal" :expand ((len x) (len (cdr x)) (true-listp x) (true-listp (cdr x))))))

(defthm cstatep-parts
  (implies (and (cstatep s) (equal (car s) a) (equal (cadr s) b) (equal (cadddr s) c))
           (equal s (list a b (caddr s) c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable cstatep) :use ((:instance clist-of-one (x (cdddr s)))))))

; THE CALL over plain variables, from s2 where the arguments and the
; callee are done: the arguments in f..f+n-1 and the closure in f+n are
; the callee's frame as they stand; its body, given its property, then
; the return
(defthm callv-abstract
  (implies (and (cstatep s2) (natp d) (natp f) (< d f) (equal n (len vs)) (true-listp vs)
                (cvals-at (+ (cadr s2) f) vs (caddr s2))
                (equal c (nth (+ (cadr s2) f n) (caddr s2)))
                (clop c)
                (ccode-at (car prog) (car s2) (list (list :callv d f n n)))
                (equal ent (cdr (assoc-equal (clo-f c) (cdr prog))))
                (consp ent) (natp (car ent)) (equal (nfix (cadr ent)) n)
                (equal (nfix (car def)) n)
                (ccode-at (car prog) (car ent) (vc-body def (car ent)))
                (cwf (cadr def) n) (cdefs-ok defs) (cfns-ok prog defs)
                (cgood (cadr def) (1+ n) (+ 2 n) (count-from 0 n) n (clo-caps c)
                       (vc-step prog s2) vs defs fuel2 prog)
                (valp (mc (cadr def) vs (clo-caps c) defs fuel2)))
           (let ((s5 (vc-step prog (vc-run prog (vc-step prog s2) (cclk (cadr def) vs (clo-caps c) defs fuel2)))))
             (and (cstatep s5)
                  (equal (car s5) (1+ (car s2))) (equal (cadr s5) (cadr s2))
                  (equal (cadddr s5) (cadddr s2))
                  (cagree (caddr s5) (update-nth (+ (cadr s2) d) (val (mc (cadr def) vs (clo-caps c) defs fuel2))
                                                 (caddr s2))
                          (+ (cadr s2) f)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth cgood mc mc-args cclk cclk-args vc-compile ccode-len
                                      cwf cdefs-ok count-from cvals-at cenv-ok cret-to-caller cfns-ok)
                  :expand ((vc-body def (car ent)))
                  :use ((:instance (:definition cgood) (e (cadr def)) (d (1+ n)) (f (+ 2 n))
                                   (cenv (count-from 0 n)) (self n) (caps (clo-caps c))
                                   (s (vc-step prog s2)) (env vs) (fuel fuel2))
                        (:instance cenv-ok-count-from (i 0) (base (+ (cadr s2) f)) (g (+ 2 n)) (regs (caddr s2)))
                        (:instance cstatep-parts
                                   (s (vc-run prog (vc-step prog s2) (cclk (cadr def) vs (clo-caps c) defs fuel2)))
                                   (a (+ (car ent) (ccode-len (cadr def)))) (b (+ (cadr s2) f))
                                   (c (cons (list (1+ (car s2)) (cadr s2) d) (cadddr s2))))
                        (:instance cret-to-caller (pc (+ (car ent) (ccode-len (cadr def)))) (m (1+ n))
                                   (cb (+ (cadr s2) f))
                                   (regs (caddr (vc-run prog (vc-step prog s2) (cclk (cadr def) vs (clo-caps c) defs fuel2))))
                                   (v (val (mc (cadr def) vs (clo-caps c) defs fuel2)))
                                   (ca (caddr s2)) (r0 (caddr s2))
                                   (rpc (1+ (car s2))) (fb (cadr s2)) (ctl (cadddr s2)))))))


; clotran's VM, formally (PLAN step 28). The stack machine's theorems,
; about the design model/vm-stack.lisp states, in the shape of the
; register machine's (model/vm-call-proof.lisp, whose general lemmas --
; registers that agree, code placed in a program -- this book reuses):
;
;   vm-stack-correct  compiled programs answer what the meaning does
;   vm-stack-rooted   and still do with every local slot from the
;                     caller's scope up wiped at each return
;
; An expression's code pushes its value on the operand stack, leaves the
; stack beneath it and the return records as they were, and changes no
; local in scope.

(in-package "ACL2")

(include-book "vm-call-proof")
(include-book "vm-stack")

; ---- THE CLOCK --------------------------------------------------------------
;
; the register machine's but for let, whose store is a step of its own

(mutual-recursion
 (defun s-clk (e env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     ((:const :local) 1)
     (:if (c+ (s-clk (cadr e) env defs fuel)
              (c+ 1 (if (truthy (val (m (cadr e) env defs fuel)))
                        (c+ (s-clk (caddr e) env defs fuel) 1)
                      (s-clk (cadddr e) env defs fuel)))))
     (:let (c+ (s-clk (cadr e) env defs fuel)
               (c+ 1 (s-clk (caddr e) (append env (list (val (m (cadr e) env defs fuel)))) defs fuel))))
     ((:add :lt) (c+ (s-clk (cadr e) env defs fuel) (c+ (s-clk (caddr e) env defs fuel) 1)))
     (:call (if (zp fuel)
                (s-clk-args (cddr e) env defs fuel)
              (c+ (s-clk-args (cddr e) env defs fuel)
                  (c+ 1 (c+ (s-clk (cadr (cdr (assoc-equal (cadr e) defs)))
                                   (val (m-args (cddr e) env defs fuel)) defs (1- fuel))
                            1)))))
     (otherwise 1)))
 (defun s-clk-args (es env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       0
     (c+ (s-clk (car es) env defs fuel) (s-clk-args (cdr es) env defs fuel)))))

(defthm natp-s-clk
  (natp (s-clk e env defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((s-clk e env defs fuel))))
  :rule-classes :type-prescription)
(defthm natp-s-clk-args
  (natp (s-clk-args es env defs fuel))
  :hints (("Goal" :in-theory (enable c+) :expand ((s-clk-args es env defs fuel))))
  :rule-classes :type-prescription)

(mutual-recursion
 (defun s-code-len (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local) 1)
     (:if (+ (s-code-len (cadr e)) 1 (s-code-len (caddr e)) 1 (s-code-len (cadddr e))))
     (:let (+ (s-code-len (cadr e)) 1 (s-code-len (caddr e))))
     ((:add :lt) (+ (s-code-len (cadr e)) (s-code-len (caddr e)) 1))
     (:call (+ (s-code-len-args (cddr e)) 1))
     (otherwise 1)))
 (defun s-code-len-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (s-code-len (car es)) (s-code-len-args (cdr es))))))

(defun sc-ind (flg e n pc fnpcs)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (sc-ind :m (car e) n pc fnpcs)
              (sc-ind :args (cdr e) n (+ pc (len (s-compile (car e) n pc fnpcs))) fnpcs)))
    (case (car e)
      (:if (let* ((cc (s-compile (cadr e) n pc fnpcs))
                  (pc1 (+ pc (len cc) 1))
                  (tc (s-compile (caddr e) n pc1 fnpcs))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (sc-ind :m (cadr e) n pc fnpcs)
                   (sc-ind :m (caddr e) n pc1 fnpcs)
                   (sc-ind :m (cadddr e) n pc2 fnpcs))))
      (:let (let ((ic (s-compile (cadr e) n pc fnpcs)))
              (list (sc-ind :m (cadr e) n pc fnpcs)
                    (sc-ind :m (caddr e) (1+ (nfix n)) (+ pc (len ic) 1) fnpcs))))
      ((:add :lt) (let ((ac (s-compile (cadr e) n pc fnpcs)))
                    (list (sc-ind :m (cadr e) n pc fnpcs)
                          (sc-ind :m (caddr e) n (+ pc (len ac)) fnpcs))))
      (:call (sc-ind :args (cddr e) n pc fnpcs))
      (otherwise (list n pc fnpcs)))))

(defthm len-s-compile-flag
  (if (eq flg :args)
      (equal (len (s-compile-args e n pc fnpcs)) (s-code-len-args e))
    (equal (len (s-compile e n pc fnpcs)) (s-code-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (sc-ind flg e n pc fnpcs))))

(defthm len-s-compile
  (equal (len (s-compile e n pc fnpcs)) (s-code-len e))
  :hints (("Goal" :use ((:instance len-s-compile-flag (flg :m))))))

(defthm len-s-compile-args
  (equal (len (s-compile-args es n pc fnpcs)) (s-code-len-args es))
  :hints (("Goal" :use ((:instance len-s-compile-flag (flg :args) (e es))))))

; ---- WHAT THE THEOREM ASSUMES -----------------------------------------------

; THE SCOPE'S TOP: every call in e, with n locals in scope, finds its
; locals in scope below top
(mutual-recursion
 (defun s-top-ok (e n top)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:if (and (s-top-ok (cadr e) n top) (s-top-ok (caddr e) n top) (s-top-ok (cadddr e) n top)))
     (:let (and (s-top-ok (cadr e) n top) (s-top-ok (caddr e) (1+ (nfix n)) top)))
     ((:add :lt) (and (s-top-ok (cadr e) n top) (s-top-ok (caddr e) n top)))
     (:call (and (<= (nfix n) (nfix top)) (s-top-ok-args (cddr e) n top)))
     (otherwise t)))
 (defun s-top-ok-args (es n top)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) t (and (s-top-ok (car es) n top) (s-top-ok-args (cdr es) n top)))))

(defun s-defs-ok (ds defs top)
  (if (atom ds)
      t
    (and (consp (car ds)) (consp (cdar ds)) (natp (car (cdar ds)))
         (wf3 (cadr (cdar ds)) (car (cdar ds)) defs)
         (or (not top) (s-top-ok (cadr (cdar ds)) (car (cdar ds)) top))
         (s-defs-ok (cdr ds) defs top))))

(defthm s-defs-ok-lookup
  (implies (and (s-defs-ok ds defs top) (consp (assoc-equal name ds)))
           (and (natp (car (cdr (assoc-equal name ds))))
                (wf3 (cadr (cdr (assoc-equal name ds))) (car (cdr (assoc-equal name ds))) defs)
                (implies top (s-top-ok (cadr (cdr (assoc-equal name ds)))
                                       (car (cdr (assoc-equal name ds))) top)))))

(defun-sk s-fns-ok (prog defs fnpcs)
  (forall name
          (implies (consp (assoc-equal name defs))
                   (and (natp (cdr (assoc-equal name fnpcs)))
                        (code-at prog (cdr (assoc-equal name fnpcs))
                                 (s-body-code (cdr (assoc-equal name defs))
                                              (cdr (assoc-equal name fnpcs)) fnpcs))))))
(in-theory (disable s-fns-ok))

(defun s-statep (s)
  (and (true-listp s) (equal (len s) 4) (natp (car s))))

; THE PROPERTY. An expression's code, run for its clock from s: the pc at
; its end, its value pushed on the operand stack, the records as they
; were, no local in scope changed.
(defun s-good (e s env defs fuel prog fnpcs top)
  (implies (and (s-statep s)
                (code-at prog (car s) (s-compile e (len env) (car s) fnpcs))
                (wf3 e (len env) defs) (vals-at 0 env (cadr s))
                (s-defs-ok defs defs top) (s-fns-ok prog defs fnpcs)
                (or (not top) (s-top-ok e (len env) top)))
           (let ((r (m e env defs fuel)) (s2 (s-run-wiping prog s (s-clk e env defs fuel) top)))
             (implies (valp r)
                      (and (equal (car s2) (+ (car s) (s-code-len e)))
                           (equal (caddr s2) (cons (val r) (caddr s)))
                           (equal (cadddr s2) (cadddr s))
                           (agree-below (cadr s2) (cadr s) (len env)))))))

; a call's arguments: their values pushed, the first deepest
(defun s-good-args (es s env defs fuel prog fnpcs top)
  (implies (and (s-statep s)
                (code-at prog (car s) (s-compile-args es (len env) (car s) fnpcs))
                (wf3-args es (len env) defs) (vals-at 0 env (cadr s))
                (s-defs-ok defs defs top) (s-fns-ok prog defs fnpcs)
                (or (not top) (s-top-ok-args es (len env) top)))
           (let ((r (m-args es env defs fuel)) (s2 (s-run-wiping prog s (s-clk-args es env defs fuel) top)))
             (implies (valp r)
                      (and (equal (car s2) (+ (car s) (s-code-len-args es)))
                           (equal (caddr s2) (revappend (val r) (caddr s)))
                           (equal (cadddr s2) (cadddr s))
                           (agree-below (cadr s2) (cadr s) (len env)))))))

; ---- the machine's runs --------------------------------------------------------

(in-theory (disable s-w-step))

(defthm s-run-plus
  (implies (and (natp a) (natp b))
           (equal (s-run-wiping prog s (+ a b) top)
                  (s-run-wiping prog (s-run-wiping prog s a top) b top)))
  :hints (("Goal" :induct (s-run-wiping prog s a top))))

(defthm s-run-c+
  (equal (s-run-wiping prog s (c+ a b) top)
         (s-run-wiping prog (s-run-wiping prog s (nfix a) top) (nfix b) top))
  :hints (("Goal" :use ((:instance s-run-plus (a (nfix a)) (b (nfix b))))
                  :in-theory (enable c+))))

(defthm s-run-0 (equal (s-run-wiping prog s 0 top) s))
(defthm s-run-1 (equal (s-run-wiping prog s 1 top) (s-w-step prog s top)))
(in-theory (disable s-run-wiping))

; ---- the machine, a step at a time ---------------------------------------------

(in-theory (enable s-w-step))

(defthm s-statep-step (implies (s-statep s) (s-statep (s-w-step prog s top))))

(defthm s-statep-list
  (equal (s-statep (list pc locals ops ctl)) (natp pc)))

(defthm s-statep-run
  (implies (s-statep s) (s-statep (s-run-wiping prog s n top)))
  :hints (("Goal" :induct (s-run-wiping prog s n top)
                  :in-theory (e/d (s-run-wiping) (s-w-step s-statep)))))

(defthm sstep-push
  (implies (and (s-statep s) (equal (car (ins-of s)) :push))
           (equal (s-w-step prog s top)
                  (list (1+ (car s)) (cadr s) (cons (cadr (ins-of s)) (caddr s)) (cadddr s)))))
(defthm sstep-load
  (implies (and (s-statep s) (equal (car (ins-of s)) :load))
           (equal (s-w-step prog s top)
                  (list (1+ (car s)) (cadr s) (cons (nth (nfix (cadr (ins-of s))) (cadr s)) (caddr s))
                        (cadddr s)))))
(defthm sstep-store
  (implies (and (s-statep s) (equal (car (ins-of s)) :store))
           (equal (s-w-step prog s top)
                  (list (1+ (car s)) (update-nth (nfix (cadr (ins-of s))) (car (caddr s)) (cadr s))
                        (cdr (caddr s)) (cadddr s)))))
(defthm sstep-add
  (implies (and (s-statep s) (equal (car (ins-of s)) :add))
           (equal (s-w-step prog s top)
                  (list (1+ (car s)) (cadr s)
                        (cons (+ (fix (cadr (caddr s))) (fix (car (caddr s)))) (cddr (caddr s)))
                        (cadddr s)))))
(defthm sstep-lt
  (implies (and (s-statep s) (equal (car (ins-of s)) :lt))
           (equal (s-w-step prog s top)
                  (list (1+ (car s)) (cadr s)
                        (cons (bool (< (rfix (cadr (caddr s))) (rfix (car (caddr s))))) (cddr (caddr s)))
                        (cadddr s)))))
(defthm sstep-jmpf
  (implies (and (s-statep s) (equal (car (ins-of s)) :jmpf))
           (equal (s-w-step prog s top)
                  (if (truthy (car (caddr s)))
                      (list (1+ (car s)) (cadr s) (cdr (caddr s)) (cadddr s))
                    (list (nfix (cadr (ins-of s))) (cadr s) (cdr (caddr s)) (cadddr s))))))
(defthm sstep-jmp
  (implies (and (s-statep s) (equal (car (ins-of s)) :jmp))
           (equal (s-w-step prog s top)
                  (list (nfix (cadr (ins-of s))) (cadr s) (caddr s) (cadddr s)))))
(defthm sstep-call
  (implies (and (s-statep s) (equal (car (ins-of s)) :call))
           (equal (s-w-step prog s top)
                  (list (nfix (cadr (ins-of s)))
                        (reverse (take (nfix (caddr (ins-of s))) (caddr s))) nil
                        (cons (list (1+ (car s)) (cadr s) (nthcdr (nfix (caddr (ins-of s))) (caddr s)))
                              (cadddr s))))))
(defthm sstep-ret
  (implies (and (s-statep s) (equal (car (ins-of s)) :ret) (consp (cadddr s)))
           (equal (s-w-step prog s top)
                  (list (nfix (car (car (cadddr s))))
                        (if top (wipe-above (nfix top) (cadr (car (cadddr s)))) (cadr (car (cadddr s))))
                        (cons (car (caddr s)) (caddr (car (cadddr s))))
                        (cdr (cadddr s))))))
(defthm sstep-halt
  (implies (and (s-statep s) (equal (car (ins-of s)) :ret) (not (consp (cadddr s))))
           (equal (s-w-step prog s top)
                  (list (car s) (cadr s) (list (car (caddr s))) (cadddr s)))))
(in-theory (disable s-w-step s-step))

(defthm s-statep-fc
  (implies (s-statep s) (natp (car s)))
  :rule-classes :forward-chaining)
(in-theory (disable s-statep))

; ---- locals and operand stacks ------------------------------------------------

(defthm vals-at-0-nth
  (implies (and (vals-at 0 vs regs) (natp j) (< j (len vs)))
           (equal (nth j regs) (nth j vs)))
  :hints (("Goal" :use ((:instance vals-at-nth (k 0))) :in-theory (disable vals-at-nth))))

(defun va-ind2 (k vs a b)
  (if (atom vs) (list k a b) (va-ind2 (1+ k) (cdr vs) a b)))

(defthm vals-at-agree
  (implies (and (vals-at k vs a) (natp k) (agree-below a b (+ k (len vs))))
           (vals-at k vs b))
  :hints (("Goal" :induct (va-ind2 k vs a b))
          ("Subgoal *1/2" :use ((:instance agree-nth (r k) (h (+ k (len vs))))
                                (:instance agree-below-smaller (h (+ k (len vs))) (g (+ 1 k (len (cdr vs))))))
                          :in-theory (disable agree-nth agree-below-smaller))))

; a let's store: the new local in the slot after the others
(defthm vals-at-store
  (implies (and (vals-at k vs a) (natp k))
           (vals-at k (append vs (list v)) (update-nth (+ k (len vs)) v a)))
  :hints (("Goal" :induct (va-ind2 k vs a v) :in-theory (disable update-nth))))

(defthm vals-at-0-store
  (implies (vals-at 0 vs a)
           (vals-at 0 (append vs (list v)) (update-nth (len vs) v a)))
  :hints (("Goal" :use ((:instance vals-at-store (k 0))) :in-theory (disable vals-at-store))))

(defun prefix-ind2 (p x)
  (if (endp x) p (prefix-ind2 (append p (list (car x))) (cdr x))))

(defthm vals-at-self-gen
  (vals-at (len p) x (append p x))
  :hints (("Goal" :induct (prefix-ind2 p x))))

; a callee's locals are its arguments
(defthm vals-at-self
  (vals-at 0 x x)
  :hints (("Goal" :use ((:instance vals-at-self-gen (p nil))))))

(defthm true-listp-m-args
  (true-listp (cdr (m-args es env defs fuel)))
  :hints (("Goal" :induct (len es) :expand ((m-args es env defs fuel)))))

; the operand stack after the arguments: their values, reversed, on
; top of what was there; a call takes them back off in order
(defthm revappend-append-gen
  (equal (revappend a (append y x)) (append (revappend a y) x)))

(defthm revappend-split
  (implies (syntaxp (not (equal x ''nil)))
           (equal (revappend a x) (append (revappend a nil) x)))
  :hints (("Goal" :use ((:instance revappend-append-gen (y nil)))
                  :in-theory (disable revappend-append-gen))))

(defthm len-revappend (equal (len (revappend a x)) (+ (len a) (len x))))
(defthm true-listp-revappend-nil (true-listp (revappend a nil)))

(defthm take-len-append
  (implies (true-listp r) (equal (take (len r) (append r x)) r)))

(defthm nthcdr-len-append
  (equal (nthcdr (len r) (append r x)) x))

(defthm take-append-exact
  (implies (and (true-listp r) (equal k (len r))) (equal (take k (append r x)) r)))

(defthm nthcdr-append-exact
  (implies (equal k (len r)) (equal (nthcdr k (append r x)) x)))

(defthm revappend-of-append
  (equal (revappend (append p q) z) (revappend q (revappend p z)))
  :hints (("Goal" :induct (revappend p z) :in-theory (disable revappend-split))))

(defthm revappend-revappend-gen
  (implies (true-listp a) (equal (revappend (revappend a y) z) (revappend y (append a z))))
  :hints (("Goal" :induct (revappend a y))))

(defthm append-nil-true-list
  (implies (true-listp a) (equal (append a nil) a)))

(defthm revappend-revappend
  (implies (true-listp a) (equal (revappend (revappend a nil) nil) a))
  :hints (("Goal" :in-theory (disable revappend-split))))

; a write at or above f, then registers that agreed: below f, the first
; agrees with the last
(defthm agree-write-then
  (implies (and (agree-below a (update-nth g w b) h1) (agree-below b c h2)
                (natp g) (<= (nfix f) g) (<= (nfix f) (nfix h1)) (<= (nfix f) (nfix h2)))
           (agree-below a c f))
  :hints (("Goal" :use ((:instance agree-past-write (h h1))
                        (:instance agree-below-smaller (a b) (b c) (h h2) (g f))
                        (:instance agree-below-trans (h f)))
                  :in-theory (disable agree-past-write agree-below-smaller agree-below-trans))))

; ---- each kind of expression, given its parts --------------------------------

(defthm s-good-const
  (implies (equal (car e) :const) (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm s-good-local
  (implies (equal (car e) :local) (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm s-good-other
  (implies (not (member-equal (car e) '(:const :local :if :let :add :lt :call)))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm s-good-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (s-good (cadr e) s env defs fuel prog fnpcs top)
                (s-good (caddr e) (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top)
                        env defs fuel prog fnpcs top))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((s-compile e (len env) (car s) fnpcs)))))

(defthm s-good-let
  (implies (and (equal (car e) :let)
                (s-good (cadr e) s env defs fuel prog fnpcs top)
                (s-good (caddr e)
                        (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)
                        (append env (list (cdr (m (cadr e) env defs fuel)))) defs fuel prog fnpcs top))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((s-compile e (len env) (car s) fnpcs)))))

(defthm s-good-if-true
  (implies (and (equal (car e) :if)
                (truthy (cdr (m (cadr e) env defs fuel)))
                (s-good (cadr e) s env defs fuel prog fnpcs top)
                (s-good (caddr e) (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)
                        env defs fuel prog fnpcs top))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((s-compile e (len env) (car s) fnpcs)))))

(defthm s-good-if-false
  (implies (and (equal (car e) :if)
                (not (truthy (cdr (m (cadr e) env defs fuel))))
                (s-good (cadr e) s env defs fuel prog fnpcs top)
                (s-good (cadddr e) (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)
                        env defs fuel prog fnpcs top))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :expand ((s-compile e (len env) (car s) fnpcs)))))

(defthm s-good-args-nil
  (implies (atom es) (s-good-args es s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm s-good-args-cons
  (implies (and (consp es)
                (s-good (car es) s env defs fuel prog fnpcs top)
                (s-good-args (cdr es) (s-run-wiping prog s (s-clk (car es) env defs fuel) top)
                             env defs fuel prog fnpcs top))
           (s-good-args es s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth revappend-split)
                  :expand ((s-compile-args es (len env) (car s) fnpcs)
                           (m-args es env defs fuel)))))

; ---- a call -------------------------------------------------------------------

(defthm len-take (equal (len (take n x)) (nfix n)))
(defthm true-listp-take (true-listp (take n x)))

; the call over plain variables, from s1, where the arguments are on the
; stack: the callee's property at its entry, and what the machine does
; from there. The caller's locals come back as they were saved -- wiped
; from top up, and top is at or above the caller's scope.
(defthm s-call-abstract
  (implies (and (s-statep s1) (natp entry) (natp k) (equal (len vs) n) (equal k n)
                (equal vs (reverse (take k (caddr s1))))
                (code-at prog (car s1) (list (list :call entry k)))
                (code-at prog entry (s-compile body n entry fnpcs))
                (code-at prog (+ entry (s-code-len body)) (list (list :ret)))
                (wf3 body n defs) (s-defs-ok defs defs top) (s-fns-ok prog defs fnpcs)
                (or (not top) (s-top-ok body n top))
                (or (not top) (<= (nfix nloc) (nfix top)))
                (s-good body (s-w-step prog s1 top) vs defs fuel2 prog fnpcs top)
                (valp (m body vs defs fuel2)))
           (let ((s4 (s-w-step prog (s-run-wiping prog (s-w-step prog s1 top) (s-clk body vs defs fuel2) top) top)))
             (and (s-statep s4) (equal (car s4) (1+ (car s1)))
                  (equal (caddr s4) (cons (val (m body vs defs fuel2)) (nthcdr k (caddr s1))))
                  (equal (cadddr s4) (cadddr s1))
                  (agree-below (cadr s4) (cadr s1) nloc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth s-good m m-args s-clk s-clk-args
                                      s-compile s-code-len wf3 s-top-ok s-defs-ok vals-at revappend-split)
                  :use ((:instance (:definition s-good) (e body) (s (s-w-step prog s1 top)) (env vs) (fuel fuel2))
                        (:instance agree-below-wipe (h nloc) (k (nfix top)) (regs (cadr s1)))))))

; the call's parts, named
(defmacro sc-def () '(cdr (assoc-equal (cadr e) defs)))
(defmacro sc-entry () '(cdr (assoc-equal (cadr e) fnpcs)))
(defmacro sc-vs () '(val (m-args (cddr e) env defs fuel)))
(defmacro sc-s1 () '(s-run-wiping prog s (s-clk-args (cddr e) env defs fuel) top))

(defthm s-good-call
  (implies (and (equal (car e) :call)
                (s-good-args (cddr e) s env defs fuel prog fnpcs top)
                (s-good (cadr (sc-def)) (s-w-step prog (sc-s1) top) (sc-vs) defs (1- fuel) prog fnpcs top))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :in-theory (disable nth update-nth s-good s-good-args s-body-code)
                  :expand ((s-compile e (len env) (car s) fnpcs) (m e env defs fuel) (s-clk e env defs fuel)
                           (wf3 e (len env) defs) (s-top-ok e (len env) top)
                           (s-body-code (sc-def) (sc-entry) fnpcs))
                  :use ((:instance (:definition s-good))
                        (:instance (:definition s-good-args) (es (cddr e)))
                        (:instance s-fns-ok-necc (name (cadr e)))
                        (:instance s-defs-ok-lookup (ds defs) (name (cadr e)))
                        (:instance s-call-abstract (s1 (sc-s1)) (vs (sc-vs)) (n (car (sc-def)))
                                   (k (len (cddr e))) (entry (sc-entry)) (body (cadr (sc-def)))
                                   (fuel2 (1- fuel)) (nloc (len env)))))))

(defthm s-good-call-no-fuel
  (implies (and (equal (car e) :call) (zp fuel))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :expand ((m e env defs fuel)))))

(defthm s-good-if
  (implies (and (equal (car e) :if)
                (s-good (cadr e) s env defs fuel prog fnpcs top)
                (s-good (caddr e) (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)
                        env defs fuel prog fnpcs top)
                (s-good (cadddr e) (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)
                        env defs fuel prog fnpcs top))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :cases ((truthy (cdr (m (cadr e) env defs fuel))))
                  :in-theory (disable s-good))))

(defthm s-good-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :call)))
           (s-good e s env defs fuel prog fnpcs top))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local))
                  :in-theory (disable s-good))))

; ---- THE STACK MACHINE's THEOREM ---------------------------------------------

(defun s-ind (flg e s env defs fuel prog fnpcs top)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o<
                  :ruler-extenders :all
                  :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list s env defs fuel prog fnpcs top)
        (list (s-ind :m (car e) s env defs fuel prog fnpcs top)
              (s-ind :args (cdr e) (s-run-wiping prog s (s-clk (car e) env defs fuel) top)
                     env defs fuel prog fnpcs top)))
    (case (car e)
      (:if (let ((s2 (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)))
             (list (s-ind :m (cadr e) s env defs fuel prog fnpcs top)
                   (s-ind :m (caddr e) s2 env defs fuel prog fnpcs top)
                   (s-ind :m (cadddr e) s2 env defs fuel prog fnpcs top))))
      (:let (list (s-ind :m (cadr e) s env defs fuel prog fnpcs top)
                  (s-ind :m (caddr e)
                         (s-w-step prog (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top) top)
                         (append env (list (cdr (m (cadr e) env defs fuel)))) defs fuel prog fnpcs top)))
      ((:add :lt) (list (s-ind :m (cadr e) s env defs fuel prog fnpcs top)
                        (s-ind :m (caddr e) (s-run-wiping prog s (s-clk (cadr e) env defs fuel) top)
                               env defs fuel prog fnpcs top)))
      (:call (list (s-ind :args (cddr e) s env defs fuel prog fnpcs top)
                   (if (zp fuel)
                       nil
                     (s-ind :m (cadr (sc-def)) (s-w-step prog (sc-s1) top) (sc-vs) defs (1- fuel)
                            prog fnpcs top))))
      (otherwise (list s env defs fuel prog fnpcs top)))))

(defthm vm-stack-correct-flag
  (if (eq flg :args)
      (s-good-args e s env defs fuel prog fnpcs top)
    (s-good e s env defs fuel prog fnpcs top))
  :rule-classes nil
  :hints (("Goal" :induct (s-ind flg e s env defs fuel prog fnpcs top)
                  :in-theory (union-theories '(s-good-if s-good-let s-good-binop s-good-call s-good-call-no-fuel
                                               s-good-leaf s-good-args-nil s-good-args-cons
                                               member-equal car-cons cdr-cons
                                               (:induction s-ind))
                                             (theory 'minimal-theory)))))

(defthm vm-stack-good
  (s-good e s env defs fuel prog fnpcs top)
  :hints (("Goal" :use ((:instance vm-stack-correct-flag (flg :m))))))

; ---- WHOLE PROGRAMS -------------------------------------------------------------

(defthm s-run-is-wiping-nil
  (equal (s-run prog s n) (s-run-wiping prog s n nil))
  :hints (("Goal" :induct (s-run prog s n)
                  :in-theory (enable s-run-wiping s-w-step)
                  :expand ((s-run-wiping prog s n nil)))))

(defthm len-s-body-code
  (equal (len (s-body-code def pc fnpcs)) (1+ (s-code-len (cadr def)))))
(in-theory (disable s-body-code))

(defthm s-lay-out-any-fnpcs
  (implies (syntaxp (not (equal y ''nil)))
           (equal (s-lay-out ds pc y) (s-lay-out ds pc nil))))

(defthm s-compile-defs-places
  (implies (and (alistp ds) (natp pc) (code-at prog pc (s-compile-defs ds fnpcs pc))
                (consp (assoc-equal name ds)))
           (and (natp (cdr (assoc-equal name (s-lay-out ds pc nil))))
                (code-at prog (cdr (assoc-equal name (s-lay-out ds pc nil)))
                         (s-body-code (cdr (assoc-equal name ds))
                                      (cdr (assoc-equal name (s-lay-out ds pc nil))) fnpcs))))
  :hints (("Goal" :induct (s-compile-defs ds fnpcs pc))))

(defthm s-compile-program-fns-ok
  (implies (alistp defs)
           (s-fns-ok (s-compile-program e defs) defs
                     (s-lay-out defs (1+ (s-code-len e)) nil)))
  :hints (("Goal" :in-theory (enable s-fns-ok)
                  :use ((:instance s-compile-defs-places
                                   (ds defs) (pc (1+ (s-code-len e)))
                                   (prog (s-compile-program e defs))
                                   (fnpcs (s-lay-out defs (1+ (s-code-len e)) nil))
                                   (name (s-fns-ok-witness (s-compile-program e defs) defs
                                                           (s-lay-out defs (1+ (s-code-len e)) nil))))
                        (:instance code-at-shift (pc 1)
                                   (a (s-compile e 0 0 (s-lay-out defs (1+ (s-code-len e)) nil)))
                                   (b (cons '(:ret)
                                            (s-compile-defs defs (s-lay-out defs (1+ (s-code-len e)) nil)
                                                            (1+ (s-code-len e)))))
                                   (code (s-compile-defs defs (s-lay-out defs (1+ (s-code-len e)) nil)
                                                         (1+ (s-code-len e)))))))))

; the main expression's return, with no caller, halts with its answer
; alone on the stack, and stays
(defthm s-halted-stays
  (implies (and (s-statep s) (not (consp (cadddr s))) (consp (caddr s)) (null (cdr (caddr s)))
                (code-at prog (car s) (list (list :ret))))
           (equal (s-run-wiping prog s k top) s))
  :hints (("Goal" :induct (s-run-wiping prog s k top)
                  :in-theory (enable s-run-wiping s-statep)
                  :expand ((s-run-wiping prog s k top)))))

(defthm s-program-answer
  (implies (and (alistp defs) (s-defs-ok defs defs top) (wf3 e 0 defs)
                (or (not top) (s-top-ok e 0 top))
                (valp (m e nil defs fuel)) (natp k))
           (equal (s-answer (s-run-wiping (s-compile-program e defs) (list 0 nil nil nil)
                                          (+ (s-clk e nil defs fuel) k) top))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable s-good vm-stack-good s-halted-stays s-compile-program
                                      s-compile-program-fns-ok s-run-plus)
                  :use ((:instance s-compile-program-fns-ok)
                        (:instance s-run-plus (prog (s-compile-program e defs)) (s (list 0 nil nil nil))
                                   (a (s-clk e nil defs fuel)) (b k))
                        (:instance vm-stack-good (s (list 0 nil nil nil)) (env nil)
                                   (prog (s-compile-program e defs))
                                   (fnpcs (s-lay-out defs (1+ (s-code-len e)) nil)))
                        (:instance (:definition s-good) (s (list 0 nil nil nil)) (env nil)
                                   (prog (s-compile-program e defs))
                                   (fnpcs (s-lay-out defs (1+ (s-code-len e)) nil)))
                        (:instance s-halted-stays (prog (s-compile-program e defs))
                                   (s (s-run-wiping (s-compile-program e defs) (list 0 nil nil nil)
                                                    (s-clk e nil defs fuel) top)))
                        (:instance code-at-shift (pc 0)
                                   (a (s-compile e 0 0 (s-lay-out defs (1+ (s-code-len e)) nil)))
                                   (b (cons '(:ret)
                                            (s-compile-defs defs (s-lay-out defs (1+ (s-code-len e)) nil)
                                                            (1+ (s-code-len e)))))
                                   (code '((:ret))))))
          ("Goal'" :in-theory (enable s-compile-program))))

; THE STACK MACHINE: a compiled program, calls and recursion included,
; answers what its meaning does once its clock has run, and keeps
; answering
(defthm vm-stack-correct
  (implies (and (alistp defs) (s-defs-ok defs defs nil) (wf3 e 0 defs)
                (valp (m e nil defs fuel)) (natp k))
           (equal (s-answer (s-run-program e defs (+ (s-clk e nil defs fuel) k)))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable s-program-answer s-compile-program)
                  :use ((:instance s-program-answer (top nil))))))

; ROOTING: the same answer when every local slot from top up is wiped at
; each return, for any top every call's scope fits under
(defthm vm-stack-rooted
  (implies (and (alistp defs) (s-defs-ok defs defs top) (wf3 e 0 defs) top (s-top-ok e 0 top)
                (valp (m e nil defs fuel)) (natp k))
           (equal (s-answer (s-run-wiping (s-compile-program e defs) (list 0 nil nil nil)
                                          (+ (s-clk e nil defs fuel) k) top))
                  (val (m e nil defs fuel))))
  :hints (("Goal" :in-theory (disable s-program-answer s-compile-program)
                  :use ((:instance s-program-answer)))))

; ---- THE HYPOTHESES ARE NOT VACUOUS ----------------------------------------
;
; the examples meet them, with every call's scope under top 2; s-top-ok
; refuses top 0, the top the design book's negative control shows
; changes an answer

(defun s-all-ok (es defs top)
  (if (atom es)
      t
    (and (wf3 (car es) 0 defs) (or (not top) (s-top-ok (car es) 0 top))
         (s-all-ok (cdr es) defs top))))

(assert-event (and (alistp *defs*) (s-defs-ok *defs* *defs* nil) (s-all-ok *all-exprs* *defs* nil)))
(assert-event (and (s-defs-ok *defs* *defs* 2) (s-all-ok *all-exprs* *defs* 2)))
(assert-event (not (and (s-defs-ok *defs* *defs* 0) (s-all-ok *all-exprs* *defs* 0))))

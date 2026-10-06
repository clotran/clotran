; clotran's VM, formally (PLAN step 30). The closure call's theorem,
; from model/vm-closure-proof.lisp's lemmas (split there because the
; abstract call's proof is long, and a book is re-proved whole).
;
;   vc-good      every expression's code answers what the meaning does
;   vc-correct   and so does a whole compiled program

(in-package "ACL2")

(include-book "vm-closure-proof")

; ---- the call's register bookkeeping, over plain variables ------------------

; computing the callee leaves the arguments where they were, and the
; closure in the register above them
(defthm callv-args-stay
  (implies (and (cagree r2 (update-nth g w r1) (1+ g)) (cvals-at k vs r1)
                (natp k) (natp g) (<= (+ k (len vs)) g))
           (and (cvals-at k vs r2) (equal (nth g r2) w)))
  :hints (("Goal" :in-theory (disable cagree-nth cvals-at-agree cagree-past-write)
                  :use ((:instance cagree-nth (a r2) (b (update-nth g w r1)) (h (1+ g)) (r g))
                        (:instance cagree-past-write (a r2) (b r1) (h (1+ g)) (f g))
                        (:instance cvals-at-agree (a r1) (b r2) (h g))))))

; the arguments', the callee's and the call's changes, below the
; caller's first free register: only the destination
(defthm callv-combine
  (implies (and (cagree r2 (update-nth g w r1) h2) (cagree r1 r0 fbf)
                (natp g) (natp fbf) (<= fbf g) (<= fbf (nfix h2)) (natp fbd)
                (cagree r5 (update-nth fbd v r2) fbf))
           (cagree r5 (update-nth fbd v r0) fbf))
  :hints (("Goal" :in-theory (disable cagree-past-write cagree-trans cagree-same-write)
                  :use ((:instance cagree-past-write (a r2) (b r1) (h h2) (f fbf))
                        (:instance cagree-trans (a r2) (b r1) (c r0) (h fbf))
                        (:instance cagree-same-write (a r2) (b r0) (d fbd) (h fbf))
                        (:instance cagree-trans (a r5) (b (update-nth fbd v r2)) (c (update-nth fbd v r0)) (h fbf))))))

; ---- the call -------------------------------------------------------------------

(defmacro cv-n () '(len (cddr e)))
(defmacro cv-s1 () '(vc-run prog s (cclk-args (cddr e) env caps defs fuel)))
(defmacro cv-s2 () '(vc-run prog (cv-s1) (cclk (cadr e) env caps defs fuel)))
(defmacro cv-c () '(val (cv-rf)))
(defmacro cv-v () '(val (mc (cadr (cv-def)) (cv-vs) (clo-caps (cv-c)) defs (1- fuel))))

; what a call that is a value says about its parts
(defthm callv-val-facts
  (implies (and (equal (car e) :callv) (valp (mc e env caps defs fuel)))
           (and (valp (mc-args (cddr e) env caps defs fuel))
                (valp (cv-rf))
                (clop (cv-c))
                (consp (assoc-equal (clo-f (cv-c)) defs))
                (equal (len (cv-vs)) (nfix (car (cv-def))))
                (not (zp fuel))
                (equal (mc e env caps defs fuel)
                       (mc (cadr (cv-def)) (cv-vs) (clo-caps (cv-c)) defs (1- fuel)))))
  :rule-classes nil
  :hints (("Goal" :expand ((mc e env caps defs fuel)))))

; a call's run: its arguments, its callee, the call, the body, the return
(defthm callv-clock
  (implies (and (equal (car e) :callv) (not (zp fuel)))
           (equal (vc-run prog s (cclk e env caps defs fuel))
                  (vc-step prog (vc-run prog (vc-step prog (cv-s2))
                                        (cclk (cadr (cv-def)) (cv-vs) (clo-caps (cv-c)) defs (1- fuel))))))
  :rule-classes nil
  :hints (("Goal" :expand ((cclk e env caps defs fuel)))))

; a call's code: its arguments', its callee's, the call
(defthm callv-code
  (implies (equal (car e) :callv)
           (equal (ccode-at code pc (vc-compile e d f cenv self pc))
                  (and (ccode-at code pc (vc-compile-args (cddr e) f cenv self pc))
                       (ccode-at code (+ pc (ccode-len-args (cddr e)))
                                 (vc-compile (cadr e) (+ f (cv-n)) (+ f (cv-n) 1) cenv self
                                             (+ pc (ccode-len-args (cddr e)))))
                       (ccode-at code (+ pc (ccode-len-args (cddr e)) (ccode-len (cadr e)))
                                 (list (list :callv d f (cv-n) (cv-n)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((vc-compile e d f cenv self pc)))))

(defthm callv-len
  (implies (equal (car e) :callv)
           (equal (ccode-len e) (+ (ccode-len-args (cddr e)) (ccode-len (cadr e)) 1)))
  :rule-classes nil)

(defthm callv-wf
  (implies (and (equal (car e) :callv) (cwf e n))
           (and (cwf (cadr e) n) (cwf-args (cddr e) n)))
  :rule-classes nil)

; the hypotheses of a call's property, and that it is a value
(defmacro cv-hyps ()
  '(and (equal (car e) :callv) (valp (mc e env caps defs fuel))
        (cstatep s) (ccode-at (car prog) (car s) (vc-compile e d f cenv self (car s)))
        (natp d) (natp f) (< d f)
        (cwf e (len env)) (cenv-ok cenv env (caddr s) (cadr s) f)
        (cself-ok self caps (caddr s) (cadr s) f)
        (cdefs-ok defs) (cfns-ok prog defs)))

(defmacro cv-thy ()
  '(disable nth update-nth cgood cgood-args vc-body mc mc-args cclk cclk-args
            vc-compile ccode-len cwf cwf-args
            cvals-at-agree cfns-ok-necc cdefs-ok-lookup mc-args-val-shape
            cagree-past-write cagree-nth cagree-smaller cagree-trans
            cagree-same-write cagree-compose cagree-then-write cagree-past-two-writes
            callv-args-stay callv-combine vc-step))

; STAGE 1: the arguments, in f .. f+n-1
(defthm callv-stage-args
  (implies (and (cv-hyps) (cgood-args (cddr e) f cenv self caps s env defs fuel prog))
           (and (cstatep (cv-s1))
                (equal (car (cv-s1)) (+ (car s) (ccode-len-args (cddr e))))
                (equal (cadr (cv-s1)) (cadr s))
                (equal (cadddr (cv-s1)) (cadddr s))
                (cagree (caddr (cv-s1)) (caddr s) (+ (cadr s) f))
                (cvals-at (+ (cadr s) f) (cv-vs) (caddr (cv-s1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (cv-thy)
                  :use ((:instance (:definition cgood-args) (es (cddr e)))
                        (:instance callv-val-facts)
                        (:instance callv-code (code (car prog)) (pc (car s)))
                        (:instance callv-wf (n (len env)))))))

; STAGE 2: the callee, into f+n, the arguments where they were
(defthm callv-stage-callee
  (implies (and (cv-hyps) (cgood-args (cddr e) f cenv self caps s env defs fuel prog)
                (cgood (cadr e) (+ f (cv-n)) (+ f (cv-n) 1) cenv self caps (cv-s1) env defs fuel prog))
           (and (cstatep (cv-s2))
                (equal (car (cv-s2)) (+ (car s) (ccode-len-args (cddr e)) (ccode-len (cadr e))))
                (equal (cadr (cv-s2)) (cadr s))
                (equal (cadddr (cv-s2)) (cadddr s))
                (cagree (caddr (cv-s2)) (update-nth (+ (cadr s) f (cv-n)) (cv-c) (caddr (cv-s1)))
                        (+ (cadr s) f (cv-n) 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (cv-thy)
                  :use ((:instance callv-stage-args)
                        (:instance (:definition cgood) (e (cadr e)) (d (+ f (cv-n))) (f (+ f (cv-n) 1)) (s (cv-s1)))
                        (:instance callv-val-facts)
                        (:instance callv-code (code (car prog)) (pc (car s)))
                        (:instance callv-wf (n (len env)))
                        (:instance cenv-ok-after-args (regs (caddr s)) (regs1 (caddr (cv-s1))) (fb (cadr s)))
                        (:instance cenv-ok-bigger-f (regs (caddr (cv-s1))) (fb (cadr s)) (g (+ f (cv-n) 1)))
                        (:instance cself-ok-after-args (regs (caddr s)) (regs1 (caddr (cv-s1))) (fb (cadr s)))
                        (:instance cself-ok-bigger-f (regs (caddr (cv-s1))) (fb (cadr s)) (g (+ f (cv-n) 1)))))))

(defmacro cv-s5 ()
  '(vc-step prog (vc-run prog (vc-step prog (cv-s2))
                         (cclk (cadr (cv-def)) (cv-vs) (clo-caps (cv-c)) defs (1- fuel)))))

; STAGE 3: the call, the body, the return
(defthm callv-stage-call
  (implies (and (cv-hyps) (cgood-args (cddr e) f cenv self caps s env defs fuel prog)
                (cgood (cadr e) (+ f (cv-n)) (+ f (cv-n) 1) cenv self caps (cv-s1) env defs fuel prog)
                (cgood (cadr (cv-def)) (1+ (nfix (car (cv-def)))) (+ 2 (nfix (car (cv-def))))
                       (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (cv-c))
                       (vc-step prog (cv-s2)) (cv-vs) defs (1- fuel) prog))
           (and (cstatep (cv-s5))
                (equal (car (cv-s5)) (+ 1 (car s) (ccode-len-args (cddr e)) (ccode-len (cadr e))))
                (equal (cadr (cv-s5)) (cadr s))
                (equal (cadddr (cv-s5)) (cadddr s))
                (cagree (caddr (cv-s5)) (update-nth (+ (cadr s) d) (cv-v) (caddr (cv-s2))) (+ (cadr s) f))))
  :rule-classes nil
  :hints (("Goal" :in-theory (cv-thy)
                  :use ((:instance callv-stage-args)
                        (:instance callv-stage-callee)
                        (:instance callv-val-facts)
                        (:instance callv-code (code (car prog)) (pc (car s)))
                        (:instance mc-args-val-shape (es (cddr e)))
                        (:instance cfns-ok-necc (name (clo-f (cv-c))))
                        (:instance cdefs-ok-lookup (ds defs) (name (clo-f (cv-c))))
                        (:instance callv-args-stay (r2 (caddr (cv-s2))) (r1 (caddr (cv-s1)))
                                   (g (+ (cadr s) f (cv-n))) (w (cv-c)) (k (+ (cadr s) f)) (vs (cv-vs)))
                        (:instance callv-abstract (s2 (cv-s2)) (vs (cv-vs)) (n (cv-n)) (c (cv-c))
                                   (ent (cdr (assoc-equal (clo-f (cv-c)) (cdr prog))))
                                   (def (cv-def)) (fuel2 (1- fuel)))))))

; STAGE 3b: the whole call's run, from the stages, in the property's terms
(defthm callv-stage-whole
  (implies (and (cv-hyps) (cgood-args (cddr e) f cenv self caps s env defs fuel prog)
                (cgood (cadr e) (+ f (cv-n)) (+ f (cv-n) 1) cenv self caps (cv-s1) env defs fuel prog)
                (cgood (cadr (cv-def)) (1+ (nfix (car (cv-def)))) (+ 2 (nfix (car (cv-def))))
                       (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (cv-c))
                       (vc-step prog (cv-s2)) (cv-vs) defs (1- fuel) prog))
           (let ((s5 (vc-run prog s (cclk e env caps defs fuel))))
             (and (cstatep s5)
                  (equal (car s5) (+ (car s) (ccode-len e)))
                  (equal (cadr s5) (cadr s))
                  (equal (cadddr s5) (cadddr s))
                  (cagree (caddr s5) (update-nth (+ (cadr s) d) (val (mc e env caps defs fuel)) (caddr s))
                          (+ (cadr s) f)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (cv-thy)
                  :use ((:instance callv-stage-args)
                        (:instance callv-stage-callee)
                        (:instance callv-stage-call)
                        (:instance callv-val-facts)
                        (:instance callv-clock)
                        (:instance callv-len)
                        (:instance callv-combine (r2 (caddr (cv-s2))) (r1 (caddr (cv-s1))) (r0 (caddr s))
                                   (g (+ (cadr s) f (cv-n))) (w (cv-c)) (h2 (+ (cadr s) f (cv-n) 1))
                                   (fbf (+ (cadr s) f)) (fbd (+ (cadr s) d)) (v (cv-v))
                                   (r5 (caddr (cv-s5))))))))

; STAGE 4: the call's property
(defthm cgood-callv
  (implies (and (equal (car e) :callv)
                (cgood-args (cddr e) f cenv self caps s env defs fuel prog)
                (cgood (cadr e) (+ f (cv-n)) (+ f (cv-n) 1) cenv self caps (cv-s1) env defs fuel prog)
                (cgood (cadr (cv-def)) (1+ (nfix (car (cv-def)))) (+ 2 (nfix (car (cv-def))))
                       (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (cv-c))
                       (vc-step prog (cv-s2)) (cv-vs) defs (1- fuel) prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (union-theories '(cgood) (theory 'minimal-theory))
                  :use ((:instance callv-stage-whole)))))

; with no fuel a call is not a value
(defthm cgood-callv-no-fuel
  (implies (and (equal (car e) :callv) (zp fuel))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable cgood-callv) :use ((:instance callv-val-facts)))))

(defthm cgood-if
  (implies (and (equal (car e) :if)
                (cgood (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                (cgood (caddr e) d f cenv self caps (vc-step prog (vc-run prog s (cclk (cadr e) env caps defs fuel)))
                       env defs fuel prog)
                (cgood (cadddr e) d f cenv self caps (vc-step prog (vc-run prog s (cclk (cadr e) env caps defs fuel)))
                       env defs fuel prog))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :cases ((truthy (cdr (mc (cadr e) env caps defs fuel))))
                  :in-theory (disable cgood))))

(defthm cgood-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :mkclo :callv)))
           (cgood e d f cenv self caps s env defs fuel prog))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local) (equal (car e) :capt))
                  :in-theory (disable cgood))))

; ---- THE THEOREM ------------------------------------------------------------------

; the induction the meaning makes: each part from the state its
; predecessor left, and a call's body, in the callee's frame, from the
; state the call made, at one less fuel
(defun cind (flg e d f cenv self caps s env defs fuel prog)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o<
                  :ruler-extenders :all
                  :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list d f cenv self caps s env defs fuel prog)
        (list (cind :m (car e) f (1+ f) cenv self caps s env defs fuel prog)
              (cind :args (cdr e) d (1+ f) cenv self caps (vc-run prog s (cclk (car e) env caps defs fuel))
                    env defs fuel prog)))
    (case (car e)
      (:if (let ((s2 (vc-step prog (vc-run prog s (cclk (cadr e) env caps defs fuel)))))
             (list (cind :m (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                   (cind :m (caddr e) d f cenv self caps s2 env defs fuel prog)
                   (cind :m (cadddr e) d f cenv self caps s2 env defs fuel prog))))
      (:let (list (cind :m (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                  (cind :m (caddr e) d (1+ f) (append cenv (list f)) self caps
                        (vc-run prog s (cclk (cadr e) env caps defs fuel))
                        (append env (list (cdr (mc (cadr e) env caps defs fuel)))) defs fuel prog)))
      ((:add :lt) (list (cind :m (cadr e) f (1+ f) cenv self caps s env defs fuel prog)
                        (cind :m (caddr e) (1+ f) (+ 2 f) cenv self caps
                              (vc-run prog s (cclk (cadr e) env caps defs fuel))
                              env defs fuel prog)))
      (:mkclo (cind :args (cddr e) d f cenv self caps s env defs fuel prog))
      (:callv (list (cind :args (cddr e) d f cenv self caps s env defs fuel prog)
                    (cind :m (cadr e) (+ f (cv-n)) (+ f (cv-n) 1) cenv self caps (cv-s1) env defs fuel prog)
                    (if (zp fuel)
                        nil
                      (cind :m (cadr (cv-def)) (1+ (nfix (car (cv-def)))) (+ 2 (nfix (car (cv-def))))
                            (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (cv-c))
                            (vc-step prog (cv-s2)) (cv-vs) defs (1- fuel) prog))))
      (otherwise (list d f cenv self caps s env defs fuel prog)))))

(defthm vc-good-flag
  (if (eq flg :args)
      (cgood-args e f cenv self caps s env defs fuel prog)
    (cgood e d f cenv self caps s env defs fuel prog))
  :rule-classes nil
  :hints (("Goal" :induct (cind flg e d f cenv self caps s env defs fuel prog)
                  :in-theory (union-theories '(cgood-if cgood-let cgood-binop cgood-mkclo cgood-callv
                                               cgood-callv-no-fuel cgood-leaf
                                               cgood-args-nil cgood-args-cons
                                               member-equal car-cons cdr-cons
                                               (:induction cind))
                                             (theory 'minimal-theory)))))

; RUNNING AN EXPRESSION'S CODE ANSWERS WHAT THE MEANING DOES: closures
; made, kept, passed and called through registers, recursion included
(defthm vc-good
  (cgood e d f cenv self caps s env defs fuel prog)
  :hints (("Goal" :use ((:instance vc-good-flag (flg :m))))))

; ---- WHOLE PROGRAMS -----------------------------------------------------------
;
; vc-program puts every function's code where its table entry says and
; the main expression's first, so a program answers what it means

(defthm len-vc-body
  (equal (len (vc-body def pc)) (1+ (ccode-len (cadr def)))))
(in-theory (disable vc-body))

(defthm cnth-len-append
  (equal (nth (+ (len a) (nfix i)) (append a b)) (nth i b))
  :hints (("Goal" :induct (len a))))

(defthm cnth-len-append-2
  (implies (natp i) (equal (nth (+ i (len a)) (append a b)) (nth i b)))
  :hints (("Goal" :use cnth-len-append :in-theory (disable cnth-len-append))))

(defthm ccode-at-shift
  (implies (natp pc)
           (equal (ccode-at (append a b) (+ (len a) pc) c) (ccode-at b pc c)))
  :hints (("Goal" :induct (ccode-at b pc c) :in-theory (enable ccode-at)
                  :expand ((ccode-at (append a b) (+ pc (len a)) c)))))

(defthm cnth-len-append-0
  (equal (nth (len a) (append a b)) (car b))
  :hints (("Goal" :induct (len a))))

(defun cprefix-ind (p a)
  (if (endp a) p (cprefix-ind (append p (list (car a))) (cdr a))))

(defthm ccode-at-prefix-gen
  (ccode-at (append p a b) (len p) a)
  :hints (("Goal" :induct (cprefix-ind p a) :in-theory (enable ccode-at))))

(defthm ccode-at-prefix
  (ccode-at (append a b) 0 a)
  :hints (("Goal" :use ((:instance ccode-at-prefix-gen (p nil))))))

(defthm ccode-at-self-gen
  (ccode-at (append p x) (len p) x)
  :hints (("Goal" :induct (cprefix-ind p x) :in-theory (enable ccode-at))))

; each function's code, laid out from pc, at the entry the table gives
(defthm vc-defs-places
  (implies (and (alistp ds) (natp pc) (ccode-at code pc (car (vc-defs ds pc)))
                (consp (assoc-equal name ds)))
           (let ((ent (cdr (assoc-equal name (cdr (vc-defs ds pc))))))
             (and (consp ent) (natp (car ent))
                  (equal (nfix (cadr ent)) (nfix (car (cdr (assoc-equal name ds)))))
                  (ccode-at code (car ent) (vc-body (cdr (assoc-equal name ds)) (car ent))))))
  :hints (("Goal" :induct (vc-defs ds pc))))

(defmacro cv-main () '(append (vc-compile e 0 1 nil nil 0) (list (list :ret 0))))

(defthm vc-program-fns-ok
  (implies (alistp defs) (cfns-ok (vc-program e defs) defs))
  :hints (("Goal" :in-theory (enable cfns-ok)
                  :use ((:instance vc-defs-places (ds defs) (pc (len (cv-main)))
                                   (code (car (vc-program e defs)))
                                   (name (cfns-ok-witness (vc-program e defs) defs)))
                        (:instance ccode-at-self-gen (p (cv-main)) (x (car (vc-defs defs (len (cv-main))))))))))

; the main expression's return, with no caller, halts and stays halted
(defthm vstep-halt
  (implies (and (cstatep s) (equal (car (cins s)) :ret) (not (consp (cadddr s))))
           (equal (vc-step prog s)
                  (list (car s) (cadr s)
                        (update-nth 0 (nth (+ (cadr s) (nfix (cadr (cins s)))) (caddr s)) (caddr s))
                        (cadddr s))))
  :hints (("Goal" :in-theory (enable vc-step cstatep))))

(defthm chalted-stays
  (implies (and (cstatep s) (equal (cadr s) 0) (not (consp (cadddr s)))
                (ccode-at (car prog) (car s) (list (list :ret 0))))
           (let ((s2 (vc-run prog s k)))
             (and (cstatep s2) (equal (car s2) (car s)) (equal (cadr s2) 0) (not (consp (cadddr s2)))
                  (equal (nth 0 (caddr s2)) (nth 0 (caddr s))))))
  :hints (("Goal" :induct (vc-run prog s k)
                  :in-theory (enable vc-run)
                  :expand ((vc-run prog s k)))))

(defthm ccode-at-head
  (ccode-at (cons x d) 0 (list x))
  :hints (("Goal" :in-theory (enable ccode-at))))

; A COMPILED PROGRAM -- closures made, kept, passed and called through
; registers, recursion included -- answers what its meaning does, once
; its clock has run, and keeps answering
(defthm vc-correct
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (vc-run-program e defs (+ (cclk e nil nil defs fuel) k))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable cgood vc-good chalted-stays vc-program vc-program-fns-ok vc-run-plus)
                  :use ((:instance vc-program-fns-ok)
                        (:instance vc-run-plus (prog (vc-program e defs)) (s (list 0 0 nil nil))
                                   (a (cclk e nil nil defs fuel)) (b k))
                        (:instance vc-good (d 0) (f 1) (cenv nil) (self nil) (caps nil) (s (list 0 0 nil nil)) (env nil)
                                   (prog (vc-program e defs)))
                        (:instance (:definition cgood) (d 0) (f 1) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 nil nil)) (env nil) (prog (vc-program e defs)))
                        (:instance chalted-stays (prog (vc-program e defs))
                                   (s (vc-run (vc-program e defs) (list 0 0 nil nil) (cclk e nil nil defs fuel))))
                        (:instance cagree-nth (r 0) (h 1)
                                   (a (caddr (vc-run (vc-program e defs) (list 0 0 nil nil) (cclk e nil nil defs fuel))))
                                   (b (update-nth 0 (cdr (mc e nil nil defs fuel)) nil)))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vc-compile e 0 1 nil nil 0))
                                   (b (cons '(:ret 0) (car (vc-defs defs (len (cv-main))))))
                                   (c '((:ret 0))))))
          ("Goal'" :in-theory (enable vc-program))))

; ---- THE HYPOTHESES ARE NOT VACUOUS ----------------------------------------

(assert-event (and (alistp *clo-defs*) (cdefs-ok *clo-defs*)))

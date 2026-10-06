; clotran's VM, formally (PLAN step 30). The closure call on the one-
; stack machine, and its theorem: vm-closure-stack-proof.lisp's property
; for the call, then every expression and every program.
;
;   vcs-good      every expression's code pushes what the meaning answers
;   vcs-correct   and a whole compiled program answers it
;
; With vm-closure-correct.lisp's vc-correct, the call protocol is
; proved for both machines: the arguments where the callee's frame
; begins, the closure above them, a return record, nothing copied.

(in-package "ACL2")

(include-book "vm-closure-stack-proof")
(include-book "vm-closure-correct")

; ---- the call's parts, named (the stack machine's) --------------------------

(defmacro sv-n () '(len (cddr e)))
(defmacro sv-s1 () '(vcs-run prog s (sclk-args (cddr e) env caps defs fuel)))
(defmacro sv-s2 () '(vcs-run prog (sv-s1) (sclk (cadr e) env caps defs fuel)))
(defmacro sv-c () '(val (cv-rf)))
(defmacro sv-v () '(val (mc (cadr (cv-def)) (cv-vs) (clo-caps (sv-c)) defs (1- fuel))))
(defmacro sv-s5 ()
  '(vcs-step prog (vcs-run prog (vcs-step prog (sv-s2))
                           (sclk (cadr (cv-def)) (cv-vs) (clo-caps (sv-c)) defs (1- fuel)))))

(defthm scallv-clock
  (implies (and (equal (car e) :callv) (not (zp fuel)))
           (equal (vcs-run prog s (sclk e env caps defs fuel)) (sv-s5)))
  :rule-classes nil
  :hints (("Goal" :expand ((sclk e env caps defs fuel)))))

(defthm scallv-code
  (implies (equal (car e) :callv)
           (and (equal (ccode-at code pc (vcs-compile e depth cenv self pc))
                       (and (ccode-at code pc (vcs-compile-args (cddr e) depth cenv self pc))
                            (ccode-at code (+ pc (scode-len-args (cddr e)))
                                      (vcs-compile (cadr e) (+ depth (sv-n)) cenv self (+ pc (scode-len-args (cddr e)))))
                            (ccode-at code (+ pc (scode-len-args (cddr e)) (scode-len (cadr e)))
                                      (list (list :callv (sv-n))))))
                (equal (scode-len e) (+ (scode-len-args (cddr e)) (scode-len (cadr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs-compile e depth cenv self pc) (scode-len e)))))

; ---- the call over plain variables ---------------------------------------------

(defthm sstep-callv
  (implies (and (sstatep s) (equal (car (sins s)) :callv)
                (equal (caddr s) (+ fb2 (nfix (cadr (sins s))) 1)) (natp fb2)
                (clop (nth (1- (caddr s)) (cadddr s)))
                (consp (cdr (assoc-equal (clo-f (nth (1- (caddr s)) (cadddr s))) (cdr prog))))
                (equal (nfix (cadr (sins s)))
                       (nfix (cadr (cdr (assoc-equal (clo-f (nth (1- (caddr s)) (cadddr s))) (cdr prog)))))))
           (equal (vcs-step prog s)
                  (list (nfix (car (cdr (assoc-equal (clo-f (nth (1- (caddr s)) (cadddr s))) (cdr prog)))))
                        fb2 (caddr s) (cadddr s)
                        (cons (list (1+ (car s)) (cadr s)) (s-ctl s)))))
  :hints (("Goal" :in-theory (enable vcs-step sstatep))))

; the same step with no free variable: the callee's base is the top less
; the arguments and the closure
(defthm sstep-callv-rw
  (implies (and (sstatep s) (equal (car (sins s)) :callv)
                (<= (+ (nfix (cadr (sins s))) 1) (caddr s))
                (clop (nth (1- (caddr s)) (cadddr s)))
                (consp (cdr (assoc-equal (clo-f (nth (1- (caddr s)) (cadddr s))) (cdr prog))))
                (equal (nfix (cadr (sins s)))
                       (nfix (cadr (cdr (assoc-equal (clo-f (nth (1- (caddr s)) (cadddr s))) (cdr prog)))))))
           (equal (vcs-step prog s)
                  (list (nfix (car (cdr (assoc-equal (clo-f (nth (1- (caddr s)) (cadddr s))) (cdr prog)))))
                        (- (caddr s) (+ (nfix (cadr (sins s))) 1)) (caddr s) (cadddr s)
                        (cons (list (1+ (car s)) (cadr s)) (s-ctl s)))))
  :hints (("Goal" :in-theory (enable vcs-step sstatep))))

(defthm slist-of-one
  (implies (and (true-listp x) (equal (len x) 1)) (equal x (list (car x))))
  :rule-classes nil
  :hints (("Goal" :expand ((len x) (len (cdr x)) (true-listp x) (true-listp (cdr x))))))

(defthm sstatep-parts
  (implies (and (sstatep s) (equal (car s) a) (equal (cadr s) b) (equal (caddr s) c) (equal (s-ctl s) d))
           (equal s (list a b c (cadddr s) d)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable sstatep) :use ((:instance slist-of-one (x (cddddr s)))))))

; the call over plain variables, in stages: the body from the frame the
; call made, then the return

(defmacro sc-s3 () '(vcs-step prog s2))
(defmacro sc-s4 () '(vcs-run prog (vcs-step prog s2) (sclk (cadr def) vs (clo-caps c) defs fuel2)))
(defmacro sc-v () '(val (mc (cadr def) vs (clo-caps c) defs fuel2)))

(defthm cenv-ok-of-nil (equal (cenv-ok nil env regs fb f) (not (consp env))))
(defthm len-zero-not-consp (equal (equal (len x) 0) (not (consp x))))

(defmacro sc-hyps ()
  '(and (sstatep s2) (natp sp) (equal n (len vs)) (true-listp vs)
        (equal (caddr s2) (+ sp n 1))
        (cvals-at sp vs (cadddr s2))
        (equal c (nth (+ sp n) (cadddr s2)))
        (clop c)
        (ccode-at (car prog) (car s2) (list (list :callv n)))
        (equal ent (cdr (assoc-equal (clo-f c) (cdr prog))))
        (consp ent) (natp (car ent)) (equal (nfix (cadr ent)) n)
        (equal (nfix (car def)) n)
        (ccode-at (car prog) (car ent) (vcs-body def (car ent)))
        (cwf (cadr def) n) (cdefs-ok defs) (sfns-ok prog defs)
        (sgood (cadr def) (1+ n) (count-from 0 n) n (clo-caps c) (sc-s3) vs defs fuel2 prog)
        (valp (mc (cadr def) vs (clo-caps c) defs fuel2))))

(defmacro sc-thy ()
  '(disable nth update-nth sgood mc mc-args sclk sclk-args vcs-compile scode-len
            cwf cdefs-ok count-from cvals-at cenv-ok sfns-ok vcs-step
            cagree-past-write cagree-nth cagree-smaller cagree-trans cagree-same-write
            cagree-compose cagree-then-write cagree-past-two-writes))

; THE BODY, in the frame the call made: its answer pushed at sp+n+1
(defthm scall-body
  (implies (sc-hyps)
           (and (sstatep (sc-s4))
                (equal (car (sc-s4)) (+ (car ent) (scode-len (cadr def))))
                (equal (cadr (sc-s4)) sp)
                (equal (caddr (sc-s4)) (+ sp n 2))
                (equal (s-ctl (sc-s4)) (cons (list (1+ (car s2)) (cadr s2)) (s-ctl s2)))
                (cagree (cadddr (sc-s4)) (update-nth (+ sp n 1) (sc-v) (cadddr s2)) (+ sp n 2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sc-thy) :do-not-induct t
                  :expand ((vcs-body def (car ent)))
                  :use ((:instance (:definition sgood) (e (cadr def)) (depth (1+ n))
                                   (cenv (count-from 0 n)) (self n) (caps (clo-caps c))
                                   (s (sc-s3)) (env vs) (fuel fuel2))
                        (:instance cenv-ok-count-from (i 0) (base sp) (g (1+ n)) (regs (cadddr s2)))))))

; THE RETURN: the answer where the frame began, the caller's frame back
(defthm scall-return
  (implies (sc-hyps)
           (let ((s5 (vcs-step prog (sc-s4))))
             (and (sstatep s5)
                  (equal (car s5) (1+ (car s2))) (equal (cadr s5) (cadr s2))
                  (equal (caddr s5) (1+ sp))
                  (equal (s-ctl s5) (s-ctl s2))
                  (equal (cadddr s5) (update-nth sp (nth (+ sp n 1) (cadddr (sc-s4))) (cadddr (sc-s4)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sc-thy)
                  :expand ((vcs-body def (car ent)))
                  :use ((:instance scall-body)
                        (:instance sstep-ret (s (sc-s4)))))))

(defthm scallv-abstract
  (implies (sc-hyps)
           (let ((s5 (vcs-step prog (sc-s4))))
             (and (sstatep s5)
                  (equal (car s5) (1+ (car s2))) (equal (cadr s5) (cadr s2))
                  (equal (caddr s5) (1+ sp))
                  (equal (s-ctl s5) (s-ctl s2))
                  (cagree (cadddr s5) (update-nth sp (sc-v) (cadddr s2)) sp)
                  (equal (nth sp (cadddr s5)) (sc-v)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sc-thy)
                  :use ((:instance scall-body)
                        (:instance scall-return)
                        (:instance cagree-nth (a (cadddr (sc-s4))) (b (update-nth (+ sp n 1) (sc-v) (cadddr s2)))
                                   (h (+ sp n 2)) (r (+ sp n 1)))
                        (:instance cagree-past-write (a (cadddr (sc-s4))) (b (cadddr s2)) (g (+ sp n 1)) (w (sc-v))
                                   (h (+ sp n 2)) (f sp))
                        (:instance cagree-same-write (a (cadddr (sc-s4))) (b (cadddr s2)) (d sp) (v (sc-v)) (h sp))))))

; ---- the call's stack bookkeeping, over plain variables ----------------------

(defthm cagree-extend
  (implies (and (cagree a b n) (natp n) (equal (nth n a) v))
           (cagree a (update-nth n v b) (1+ n)))
  :hints (("Goal" :in-theory (e/d (cagree) (cagree-necc)) :do-not-induct t
                  :use ((:instance cagree-necc (r (cagree-witness a (update-nth n v b) (1+ n))) (h n))))))

; the arguments', the callee's and the call's changes: below the old top
; the stack as it was, at it the answer
(defthm scall-combine
  (implies (and (cagree s5 (update-nth sp v s2) sp) (equal (nth sp s5) v)
                (cagree s2 (update-nth g w s1) h2) (natp g) (<= sp g) (<= sp (nfix h2))
                (cagree s1 s0 sp) (natp sp))
           (cagree s5 (update-nth sp v s0) (1+ sp)))
  :hints (("Goal" :in-theory (disable cagree-past-write cagree-trans cagree-extend nth update-nth)
                  :use ((:instance cagree-past-write (a s5) (b s2) (g sp) (w v) (h sp) (f sp))
                        (:instance cagree-past-write (a s2) (b s1) (h h2) (f sp))
                        (:instance cagree-trans (a s5) (b s2) (c s1) (h sp))
                        (:instance cagree-trans (a s5) (b s1) (c s0) (h sp))
                        (:instance cagree-extend (a s5) (b s0) (n sp))))))

; ---- the call, in stages ---------------------------------------------------------

(defmacro sv-hyps ()
  '(and (equal (car e) :callv) (valp (mc e env caps defs fuel))
        (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
        (ccode-at (car prog) (car s) (vcs-compile e depth cenv self (car s)))
        (cwf e (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
        (cself-ok self caps (cadddr s) (cadr s) depth)
        (cdefs-ok defs) (sfns-ok prog defs)))

(defmacro sv-thy ()
  '(disable nth update-nth sgood sgood-args vcs-body mc mc-args sclk sclk-args
            vcs-compile scode-len cwf cwf-args
            cvals-at-agree sfns-ok-necc cdefs-ok-lookup mc-args-val-shape
            cagree-past-write cagree-nth cagree-smaller cagree-trans
            cagree-same-write cagree-compose cagree-then-write cagree-past-two-writes
            callv-args-stay callv-combine scall-combine cagree-extend vcs-step))

(defthm scallv-stage-args
  (implies (and (sv-hyps) (sgood-args (cddr e) depth cenv self caps s env defs fuel prog))
           (and (sstatep (sv-s1))
                (equal (car (sv-s1)) (+ (car s) (scode-len-args (cddr e))))
                (equal (cadr (sv-s1)) (cadr s))
                (equal (caddr (sv-s1)) (+ (caddr s) (sv-n)))
                (equal (s-ctl (sv-s1)) (s-ctl s))
                (cagree (cadddr (sv-s1)) (cadddr s) (caddr s))
                (cvals-at (caddr s) (cv-vs) (cadddr (sv-s1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sv-thy)
                  :use ((:instance (:definition sgood-args) (es (cddr e)))
                        (:instance callv-val-facts)
                        (:instance scallv-code (code (car prog)) (pc (car s)))
                        (:instance callv-wf (n (len env)))))))

(defthm scallv-stage-callee
  (implies (and (sv-hyps) (sgood-args (cddr e) depth cenv self caps s env defs fuel prog)
                (sgood (cadr e) (+ depth (sv-n)) cenv self caps (sv-s1) env defs fuel prog))
           (and (sstatep (sv-s2))
                (equal (car (sv-s2)) (+ (car s) (scode-len-args (cddr e)) (scode-len (cadr e))))
                (equal (cadr (sv-s2)) (cadr s))
                (equal (caddr (sv-s2)) (+ (caddr s) (sv-n) 1))
                (equal (s-ctl (sv-s2)) (s-ctl s))
                (cagree (cadddr (sv-s2)) (update-nth (+ (caddr s) (sv-n)) (sv-c) (cadddr (sv-s1)))
                        (+ (caddr s) (sv-n) 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sv-thy)
                  :use ((:instance scallv-stage-args)
                        (:instance (:definition sgood) (e (cadr e)) (depth (+ depth (sv-n))) (s (sv-s1)))
                        (:instance callv-val-facts)
                        (:instance scallv-code (code (car prog)) (pc (car s)))
                        (:instance callv-wf (n (len env)))
                        (:instance cenv-ok-after-args (regs (cadddr s)) (regs1 (cadddr (sv-s1))) (fb (cadr s)) (f depth))
                        (:instance cenv-ok-bigger-f (regs (cadddr (sv-s1))) (fb (cadr s)) (f depth) (g (+ depth (sv-n))))
                        (:instance cself-ok-after-args (regs (cadddr s)) (regs1 (cadddr (sv-s1))) (fb (cadr s)) (f depth))
                        (:instance cself-ok-bigger-f (regs (cadddr (sv-s1))) (fb (cadr s)) (f depth) (g (+ depth (sv-n))))))))

(defthm scallv-stage-call
  (implies (and (sv-hyps) (sgood-args (cddr e) depth cenv self caps s env defs fuel prog)
                (sgood (cadr e) (+ depth (sv-n)) cenv self caps (sv-s1) env defs fuel prog)
                (sgood (cadr (cv-def)) (1+ (nfix (car (cv-def))))
                       (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (sv-c))
                       (vcs-step prog (sv-s2)) (cv-vs) defs (1- fuel) prog))
           (and (sstatep (sv-s5))
                (equal (car (sv-s5)) (+ 1 (car s) (scode-len-args (cddr e)) (scode-len (cadr e))))
                (equal (cadr (sv-s5)) (cadr s))
                (equal (caddr (sv-s5)) (1+ (caddr s)))
                (equal (s-ctl (sv-s5)) (s-ctl s))
                (cagree (cadddr (sv-s5)) (update-nth (caddr s) (sv-v) (cadddr (sv-s2))) (caddr s))
                (equal (nth (caddr s) (cadddr (sv-s5))) (sv-v))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sv-thy)
                  :use ((:instance scallv-stage-args)
                        (:instance scallv-stage-callee)
                        (:instance callv-val-facts)
                        (:instance scallv-code (code (car prog)) (pc (car s)))
                        (:instance mc-args-val-shape (es (cddr e)))
                        (:instance sfns-ok-necc (name (clo-f (sv-c))))
                        (:instance cdefs-ok-lookup (ds defs) (name (clo-f (sv-c))))
                        (:instance callv-args-stay (r2 (cadddr (sv-s2))) (r1 (cadddr (sv-s1)))
                                   (g (+ (caddr s) (sv-n))) (w (sv-c)) (k (caddr s)) (vs (cv-vs)))
                        (:instance scallv-abstract (s2 (sv-s2)) (sp (caddr s)) (vs (cv-vs)) (n (sv-n)) (c (sv-c))
                                   (ent (cdr (assoc-equal (clo-f (sv-c)) (cdr prog))))
                                   (def (cv-def)) (fuel2 (1- fuel)))))))

(defthm scallv-stage-whole
  (implies (and (sv-hyps) (sgood-args (cddr e) depth cenv self caps s env defs fuel prog)
                (sgood (cadr e) (+ depth (sv-n)) cenv self caps (sv-s1) env defs fuel prog)
                (sgood (cadr (cv-def)) (1+ (nfix (car (cv-def))))
                       (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (sv-c))
                       (vcs-step prog (sv-s2)) (cv-vs) defs (1- fuel) prog))
           (let ((s5 (vcs-run prog s (sclk e env caps defs fuel))))
             (and (sstatep s5)
                  (equal (car s5) (+ (car s) (scode-len e)))
                  (equal (cadr s5) (cadr s))
                  (equal (caddr s5) (1+ (caddr s)))
                  (equal (s-ctl s5) (s-ctl s))
                  (cagree (cadddr s5) (update-nth (caddr s) (val (mc e env caps defs fuel)) (cadddr s))
                          (1+ (caddr s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (sv-thy)
                  :use ((:instance scallv-stage-args)
                        (:instance scallv-stage-callee)
                        (:instance scallv-stage-call)
                        (:instance callv-val-facts)
                        (:instance scallv-clock)
                        (:instance scallv-code (code (car prog)) (pc (car s)))
                        (:instance scall-combine (s5 (cadddr (sv-s5))) (s2 (cadddr (sv-s2))) (s1 (cadddr (sv-s1)))
                                   (s0 (cadddr s)) (sp (caddr s)) (v (sv-v))
                                   (g (+ (caddr s) (sv-n))) (w (sv-c)) (h2 (+ (caddr s) (sv-n) 1)))))))

(defthm sgood-callv
  (implies (and (equal (car e) :callv)
                (sgood-args (cddr e) depth cenv self caps s env defs fuel prog)
                (sgood (cadr e) (+ depth (sv-n)) cenv self caps (sv-s1) env defs fuel prog)
                (sgood (cadr (cv-def)) (1+ (nfix (car (cv-def))))
                       (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (sv-c))
                       (vcs-step prog (sv-s2)) (cv-vs) defs (1- fuel) prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (union-theories '(sgood) (theory 'minimal-theory))
                  :use ((:instance scallv-stage-whole)))))

(defthm sgood-callv-no-fuel
  (implies (and (equal (car e) :callv) (zp fuel))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable sgood-callv) :use ((:instance callv-val-facts)))))

(defthm sgood-if
  (implies (and (equal (car e) :if)
                (sgood (cadr e) depth cenv self caps s env defs fuel prog)
                (sgood (caddr e) depth cenv self caps (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))
                       env defs fuel prog)
                (sgood (cadddr e) depth cenv self caps (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))
                       env defs fuel prog))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :cases ((and (valp (mc (cadr e) env caps defs fuel)) (truthy (cdr (mc (cadr e) env caps defs fuel))))
                           (and (valp (mc (cadr e) env caps defs fuel)) (not (truthy (cdr (mc (cadr e) env caps defs fuel))))))
                  :in-theory (disable sgood))))

(defthm sgood-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :mkclo :callv)))
           (sgood e depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local) (equal (car e) :capt))
                  :in-theory (disable sgood))))

; ---- THE THEOREM ------------------------------------------------------------------

(defun sind (flg e depth cenv self caps s env defs fuel prog)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                  :well-founded-relation o<
                  :ruler-extenders :all
                  :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          (list depth cenv self caps s env defs fuel prog)
        (list (sind :m (car e) depth cenv self caps s env defs fuel prog)
              (sind :args (cdr e) (1+ depth) cenv self caps (vcs-run prog s (sclk (car e) env caps defs fuel))
                    env defs fuel prog)))
    (case (car e)
      (:if (let ((s2 (vcs-step prog (vcs-run prog s (sclk (cadr e) env caps defs fuel)))))
             (list (sind :m (cadr e) depth cenv self caps s env defs fuel prog)
                   (sind :m (caddr e) depth cenv self caps s2 env defs fuel prog)
                   (sind :m (cadddr e) depth cenv self caps s2 env defs fuel prog))))
      (:let (list (sind :m (cadr e) depth cenv self caps s env defs fuel prog)
                  (sind :m (caddr e) (1+ depth) (append cenv (list depth)) self caps
                        (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                        (append env (list (cdr (mc (cadr e) env caps defs fuel)))) defs fuel prog)))
      ((:add :lt) (list (sind :m (cadr e) depth cenv self caps s env defs fuel prog)
                        (sind :m (caddr e) (1+ depth) cenv self caps
                              (vcs-run prog s (sclk (cadr e) env caps defs fuel))
                              env defs fuel prog)))
      (:mkclo (sind :args (cddr e) depth cenv self caps s env defs fuel prog))
      (:callv (list (sind :args (cddr e) depth cenv self caps s env defs fuel prog)
                    (sind :m (cadr e) (+ depth (sv-n)) cenv self caps (sv-s1) env defs fuel prog)
                    (if (zp fuel)
                        nil
                      (sind :m (cadr (cv-def)) (1+ (nfix (car (cv-def))))
                            (count-from 0 (nfix (car (cv-def)))) (nfix (car (cv-def))) (clo-caps (sv-c))
                            (vcs-step prog (sv-s2)) (cv-vs) defs (1- fuel) prog))))
      (otherwise (list depth cenv self caps s env defs fuel prog)))))

(defthm vcs-good-flag
  (if (eq flg :args)
      (sgood-args e depth cenv self caps s env defs fuel prog)
    (sgood e depth cenv self caps s env defs fuel prog))
  :rule-classes nil
  :hints (("Goal" :induct (sind flg e depth cenv self caps s env defs fuel prog)
                  :in-theory (union-theories '(sgood-if sgood-let sgood-binop sgood-mkclo sgood-callv
                                               sgood-callv-no-fuel sgood-leaf
                                               sgood-args-nil sgood-args-cons
                                               member-equal car-cons cdr-cons
                                               (:induction sind))
                                             (theory 'minimal-theory)))))

; RUNNING AN EXPRESSION'S CODE ON THE STACK MACHINE PUSHES WHAT THE
; MEANING ANSWERS: closures made, kept, passed and called, recursion included
(defthm vcs-good
  (sgood e depth cenv self caps s env defs fuel prog)
  :hints (("Goal" :use ((:instance vcs-good-flag (flg :m))))))

; ---- WHOLE PROGRAMS -----------------------------------------------------------

(defthm len-vcs-body
  (equal (len (vcs-body def pc)) (1+ (scode-len (cadr def)))))
(in-theory (disable vcs-body))

(defthm vcs-defs-places
  (implies (and (alistp ds) (natp pc) (ccode-at code pc (car (vcs-defs ds pc)))
                (consp (assoc-equal name ds)))
           (let ((ent (cdr (assoc-equal name (cdr (vcs-defs ds pc))))))
             (and (consp ent) (natp (car ent))
                  (equal (nfix (cadr ent)) (nfix (car (cdr (assoc-equal name ds)))))
                  (ccode-at code (car ent) (vcs-body (cdr (assoc-equal name ds)) (car ent))))))
  :hints (("Goal" :induct (vcs-defs ds pc))))

(defmacro sv-main () '(append (vcs-compile e 0 nil nil 0) (list (list :ret))))

(defthm vcs-program-fns-ok
  (implies (alistp defs) (sfns-ok (vcs-program e defs) defs))
  :hints (("Goal" :in-theory (enable sfns-ok)
                  :use ((:instance vcs-defs-places (ds defs) (pc (len (sv-main)))
                                   (code (car (vcs-program e defs)))
                                   (name (sfns-ok-witness (vcs-program e defs) defs)))
                        (:instance ccode-at-self-gen (p (sv-main)) (x (car (vcs-defs defs (len (sv-main))))))))))

(defthm shalted-stays
  (implies (and (sstatep s) (equal (cadr s) 0) (equal (caddr s) 1) (not (consp (s-ctl s)))
                (ccode-at (car prog) (car s) (list (list :ret))))
           (let ((s2 (vcs-run prog s k)))
             (and (sstatep s2) (equal (car s2) (car s)) (equal (cadr s2) 0) (equal (caddr s2) 1)
                  (not (consp (s-ctl s2)))
                  (equal (nth 0 (cadddr s2)) (nth 0 (cadddr s))))))
  :hints (("Goal" :induct (vcs-run prog s k)
                  :in-theory (enable vcs-run)
                  :expand ((vcs-run prog s k)))))

; A COMPILED PROGRAM ON THE STACK MACHINE answers what its meaning does
(defthm vcs-correct
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (vcs-run-program e defs (+ (sclk e nil nil defs fuel) k))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable sgood vcs-good shalted-stays vcs-program vcs-program-fns-ok vcs-run-plus)
                  :use ((:instance vcs-program-fns-ok)
                        (:instance vcs-run-plus (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (a (sclk e nil nil defs fuel)) (b k))
                        (:instance vcs-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 nil nil)) (env nil)
                                   (prog (vcs-program e defs)))
                        (:instance (:definition sgood) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (vcs-program e defs)))
                        (:instance shalted-stays (prog (vcs-program e defs))
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (sclk e nil nil defs fuel))))
                        (:instance cagree-nth (r 0) (h 1)
                                   (a (cadddr (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (sclk e nil nil defs fuel))))
                                   (b (update-nth 0 (cdr (mc e nil nil defs fuel)) nil)))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcs-compile e 0 nil nil 0))
                                   (b (cons '(:ret) (car (vcs-defs defs (len (sv-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcs-program))))

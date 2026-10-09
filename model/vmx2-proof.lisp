; clotran's VM, formally (PLAN step 30): the whole language's machine
; (model/vmx2.lisp) against its meaning.
;
; THE PROPERTY has three outcomes. A value is pushed (vmx-proof.lisp's);
; a recur arrives at its loop's head (vmx-proof.lisp's); and now a THROW
; arrives where unwinding the starting control stack lands -- the
; nearest handler's pc and frame, its stack top just above the handler's
; local, the thrown value in that local, nothing below it changed -- or,
; with no handler, the machine stopped at :thrown with the value at slot
; 0. What makes "nothing below it changed" true is an invariant: every
; handler record's slot is at or below the stack top where the
; expression starts, so whatever the expression pushes lies above it.
;
;   vcs2-good      every expression, in every frame: its value, its
;                  recur, or its throw, as above -- closures, variadic
;                  calls, runtime calls, loops, try and throw, a throw
;                  out of a call passing over the call records
;   vcs2-correct   a whole compiled program answers its meaning: its
;                  value, or the value of a throw nothing caught
;
; The method is vmx-proof.lisp's, one path at a time from a few facts. A
; call's frame (fixed or variadic) is named by call-frame, call-nl and
; call-benv and kept closed: opened in the hints, its if multiplied
; across every instance and the prover spent ten minutes before starting.

(in-package "ACL2")

(include-book "vmx2")
(include-book "vmx-proof")

; ---- THE CLOCK ----------------------------------------------------------------
;
; sxclk's, and a part that is not a value stops the count there: a throw
; ends an expression at the step that throws.

(defmacro x2-rf () '(mx2 (cadr e) env caps defs fuel))
(defmacro x2-vs () '(val (mx2-args (cddr e) env caps defs fuel)))
(defmacro x2-cl () '(pick-arity (cdr (assoc-equal (clo-f (val (x2-rf))) defs)) (len (x2-vs))))
(defmacro x2-benv () '(if (restp (x2-cl)) (split-rest (nfix (car (x2-cl))) (x2-vs)) (x2-vs)))

(mutual-recursion
 (defun s2clk (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (c+ (s2clk (cadr e) env caps defs fuel)
              (if (valp (mx2 (cadr e) env caps defs fuel))
                  (c+ 1 (if (truthy (val (mx2 (cadr e) env caps defs fuel)))
                            (c+ (s2clk (caddr e) env caps defs fuel)
                                (if (valp (mx2 (caddr e) env caps defs fuel)) 1 0))
                          (s2clk (cadddr e) env caps defs fuel)))
                0)))
     (:let (let ((env2 (append env (list (val (mx2 (cadr e) env caps defs fuel))))))
             (c+ (s2clk (cadr e) env caps defs fuel)
                 (if (valp (mx2 (cadr e) env caps defs fuel))
                     (c+ (s2clk (caddr e) env2 caps defs fuel)
                         (if (valp (mx2 (caddr e) env2 caps defs fuel)) 1 0))
                   0))))
     ((:add :lt) (c+ (s2clk (cadr e) env caps defs fuel)
                     (if (valp (mx2 (cadr e) env caps defs fuel))
                         (c+ (s2clk (caddr e) env caps defs fuel)
                             (if (valp (mx2 (caddr e) env caps defs fuel)) 1 0))
                       0)))
     (:mkclo (c+ (s2clk-args (cddr e) env caps defs fuel)
                 (if (valp (mx2-args (cddr e) env caps defs fuel)) 1 0)))
     (:callv (c+ (s2clk-args (cddr e) env caps defs fuel)
                 (if (valp (mx2-args (cddr e) env caps defs fuel))
                     (c+ (s2clk (cadr e) env caps defs fuel)
                         (if (valp (x2-rf))
                             (c+ 1 (if (and (clop (val (x2-rf))) (consp (x2-cl)) (not (zp fuel)))
                                       (c+ (s2clk (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel))
                                           (if (valp (mx2 (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel)))
                                               1 0))
                                     0))
                           0))
                   0)))
     (:loop (c+ (s2clk-args (cadr e) env caps defs fuel)
                (if (valp (mx2-args (cadr e) env caps defs fuel))
                    (c+ (s2clk-loop e env (val (mx2-args (cadr e) env caps defs fuel)) caps defs fuel)
                        (if (valp (mx2-loop e env (val (mx2-args (cadr e) env caps defs fuel)) caps defs fuel))
                            (len (cadr e)) 0))
                  0)))
     (:recur (c+ (s2clk-args (cdr e) env caps defs fuel)
                 (if (valp (mx2-args (cdr e) env caps defs fuel)) 1 0)))
     (:prim (c+ (s2clk-args (cddr e) env caps defs fuel)
                (if (valp (mx2-args (cddr e) env caps defs fuel)) 1 0)))
     (:throw (c+ (s2clk (cadr e) env caps defs fuel) (if (valp (mx2 (cadr e) env caps defs fuel)) 1 0)))
     (:try (let ((rb (mx2 (cadr e) env caps defs fuel))
                 (env2 (append env (list (cdr (mx2 (cadr e) env caps defs fuel))))))
             (c+ 1 (c+ (s2clk (cadr e) env caps defs fuel)
                       (cond ((valp rb) 2)
                             ((thrownp rb) (c+ (s2clk (caddr e) env2 caps defs fuel)
                                               (if (valp (mx2 (caddr e) env2 caps defs fuel)) 1 0)))
                             (t 0))))))
     (otherwise 1)))
 (defun s2clk-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1)) :ruler-extenders :all))
   (if (atom es)
       0
     (c+ (s2clk (car es) env caps defs fuel)
         (if (valp (mx2 (car es) env caps defs fuel)) (s2clk-args (cdr es) env caps defs fuel) 0))))
 (defun s2clk-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0)) :ruler-extenders :all))
   (cond ((not (consp e)) 0)
         ((and (recurp (mx2 (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
          (c+ (s2clk (caddr e) (append base vs) caps defs fuel)
              (s2clk-loop e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))
         (t (s2clk (caddr e) (append base vs) caps defs fuel)))))

(mutual-recursion
 (defun s2code-len (e)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     ((:const :local :capt) 1)
     (:if (+ (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1 (s2code-len (cadddr e))))
     (:let (+ (s2code-len (cadr e)) (s2code-len (caddr e)) 1))
     ((:add :lt) (+ (s2code-len (cadr e)) (s2code-len (caddr e)) 1))
     (:mkclo (+ (s2code-len-args (cddr e)) 1))
     (:callv (+ (s2code-len-args (cddr e)) (s2code-len (cadr e)) 1))
     (:loop (+ (s2code-len-args (cadr e)) (s2code-len (caddr e)) (len (cadr e))))
     (:recur (+ (s2code-len-args (cdr e)) 1))
     (:prim (+ (s2code-len-args (cddr e)) 1))
     (:throw (+ (s2code-len (cadr e)) 1))
     (:try (+ 1 (s2code-len (cadr e)) 2 (s2code-len (caddr e)) 1))
     (otherwise 1)))
 (defun s2code-len-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) 0 (+ (s2code-len (car es)) (s2code-len-args (cdr es))))))

(defun s2c-ind (flg e depth cenv self pc lc)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (s2c-ind :m (car e) depth cenv self pc nil)
              (s2c-ind :args (cdr e) (1+ depth) cenv self
                       (+ pc (len (vcs2-compile (car e) depth cenv self pc nil))) nil)))
    (case (car e)
      (:if (let* ((cc (vcs2-compile (cadr e) depth cenv self pc nil))
                  (pc1 (+ pc (len cc) 1))
                  (tc (vcs2-compile (caddr e) depth cenv self pc1 lc))
                  (pc2 (+ pc1 (len tc) 1)))
             (list (s2c-ind :m (cadr e) depth cenv self pc nil)
                   (s2c-ind :m (caddr e) depth cenv self pc1 lc)
                   (s2c-ind :m (cadddr e) depth cenv self pc2 lc))))
      (:let (let ((ic (vcs2-compile (cadr e) depth cenv self pc nil)))
              (list (s2c-ind :m (cadr e) depth cenv self pc nil)
                    (s2c-ind :m (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (len ic)) lc))))
      ((:add :lt) (let ((ac (vcs2-compile (cadr e) depth cenv self pc nil)))
                    (list (s2c-ind :m (cadr e) depth cenv self pc nil)
                          (s2c-ind :m (caddr e) (1+ depth) cenv self (+ pc (len ac)) nil))))
      ((:mkclo :prim) (s2c-ind :args (cddr e) depth cenv self pc nil))
      (:callv (let ((ac (vcs2-compile-args (cddr e) depth cenv self pc)))
                (list (s2c-ind :args (cddr e) depth cenv self pc nil)
                      (s2c-ind :m (cadr e) (+ depth (len (cddr e))) cenv self (+ pc (len ac)) nil))))
      (:loop (let* ((k (len (cadr e)))
                    (ic (vcs2-compile-args (cadr e) depth cenv self pc))
                    (head (+ pc (len ic))))
               (list (s2c-ind :args (cadr e) depth cenv self pc nil)
                     (s2c-ind :m (caddr e) (+ depth k) (append cenv (count-from depth (+ depth k))) self head
                              (list head depth k)))))
      (:recur (s2c-ind :args (cdr e) depth cenv self pc nil))
      (:throw (s2c-ind :m (cadr e) depth cenv self pc nil))
      (:try (let* ((bc (vcs2-compile (cadr e) depth cenv self (1+ pc) nil))
                   (h (+ pc 1 (len bc) 2)))
              (list (s2c-ind :m (cadr e) depth cenv self (1+ pc) nil)
                    (s2c-ind :m (caddr e) (1+ depth) (append cenv (list depth)) self h nil))))
      (otherwise (list depth cenv self pc lc)))))

(defthm len-vcs2-compile-flag
  (if (eq flg :args)
      (equal (len (vcs2-compile-args e depth cenv self pc)) (s2code-len-args e))
    (equal (len (vcs2-compile e depth cenv self pc lc)) (s2code-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (s2c-ind flg e depth cenv self pc lc))))

(defthm len-vcs2-compile
  (equal (len (vcs2-compile e depth cenv self pc lc)) (s2code-len e))
  :hints (("Goal" :use ((:instance len-vcs2-compile-flag (flg :m))))))

(defthm len-vcs2-compile-args
  (equal (len (vcs2-compile-args es depth cenv self pc)) (s2code-len-args es))
  :hints (("Goal" :use ((:instance len-vcs2-compile-flag (flg :args) (e es) (lc nil))))))

(defthm natp-s2code-len (natp (s2code-len e)) :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance len-vcs2-compile (depth 0) (cenv nil) (self nil) (pc 0) (lc nil)))
                  :in-theory (disable len-vcs2-compile))))
(defthm natp-s2code-len-args (natp (s2code-len-args es)) :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance len-vcs2-compile-args (depth 0) (cenv nil) (self nil) (pc 0)))
                  :in-theory (disable len-vcs2-compile-args))))

; ---- THE MACHINE: vcsx-step but for the new instructions -------------------------

(defthm vcs2-step-old
  (implies (and (natp (car s))
                (not (member-equal (car (nth (car s) (car prog))) '(:callv :prim :throw :try :endtry))))
           (equal (vcs2-step prog s) (vcsx-step prog s))))

(defthm vcs2-step-nopc
  (implies (not (natp (car s))) (equal (vcs2-step prog s) s)))

(defthm s2step-try
  (implies (and (sstatep s) (equal (car (sins s)) :try))
           (equal (vcs2-step prog s)
                  (list (1+ (car s)) (cadr s) (caddr s) (cadddr s)
                        (cons (list :h (nfix (cadr (sins s))) (cadr s) (nfix (caddr (sins s)))) (s-ctl s)))))
  :hints (("Goal" :in-theory (enable sstatep))))

(defthm s2step-endtry
  (implies (and (sstatep s) (equal (car (sins s)) :endtry))
           (equal (vcs2-step prog s) (list (1+ (car s)) (cadr s) (caddr s) (cadddr s) (cdr (s-ctl s)))))
  :hints (("Goal" :in-theory (enable sstatep))))

(defthm s2step-throw
  (implies (and (sstatep s) (equal (car (sins s)) :throw) (<= 1 (caddr s)))
           (equal (vcs2-step prog s) (unwind (nth (1- (caddr s)) (cadddr s)) (s-ctl s) (cadddr s))))
  :hints (("Goal" :in-theory (enable sstatep))))

(defthm s2step-prim
  (implies (and (sstatep s) (equal (car (sins s)) :prim) (<= (nfix (caddr (sins s))) (caddr s)))
           (equal (vcs2-step prog s)
                  (let* ((n (nfix (caddr (sins s))))
                         (a (prim (cadr (sins s)) (stk-from (- (caddr s) n) n (cadddr s)))))
                    (if (throwp a)
                        (unwind (cdr a) (s-ctl s) (cadddr s))
                      (list (1+ (car s)) (cadr s) (1+ (- (caddr s) n)) (update-nth (- (caddr s) n) a (cadddr s))
                            (s-ctl s))))))
  :hints (("Goal" :in-theory (enable sstatep ssetreg))))

(in-theory (disable vcs2-step))

(defthm vcs2-run-plus
  (implies (and (natp a) (natp b))
           (equal (vcs2-run prog s (+ a b)) (vcs2-run prog (vcs2-run prog s a) b)))
  :hints (("Goal" :induct (vcs2-run prog s a))))

(defthm vcs2-run-c+
  (equal (vcs2-run prog s (c+ a b)) (vcs2-run prog (vcs2-run prog s (nfix a)) (nfix b)))
  :hints (("Goal" :in-theory (enable c+) :use ((:instance vcs2-run-plus (a (nfix a)) (b (nfix b)))))))

(defthm vcs2-run-0 (equal (vcs2-run prog s 0) s))
(defthm vcs2-run-1 (equal (vcs2-run prog s 1) (vcs2-step prog s)))
(in-theory (disable vcs2-run))

; ---- UNWINDING ------------------------------------------------------------------
;
; where a throw lands depends on the control stack alone, but for the
; value written into the handler's local

(defun hfind (ctl)
  (cond ((atom ctl) nil) ((eq (car (car ctl)) :h) ctl) (t (hfind (cdr ctl)))))

(defthm unwind-is
  (equal (unwind v ctl stk)
         (let ((tl (hfind ctl)))
           (if (consp tl)
               (let ((h (nfix (cadr (car tl)))) (hfb (nfix (caddr (car tl)))) (hd (nfix (cadddr (car tl)))))
                 (list h hfb (+ hfb hd 1) (update-nth (+ hfb hd) v stk) (cdr tl)))
             (list :thrown 0 1 (update-nth 0 v stk) nil)))))

(in-theory (disable unwind))

; a call record is passed over
(defthm hfind-call-record
  (implies (not (equal x :h)) (equal (hfind (cons (cons x r) ctl)) (hfind ctl))))

; every handler record's slot at or below sp
(defun handlers-ok (ctl sp)
  (cond ((atom ctl) t)
        ((eq (car (car ctl)) :h)
         (and (<= (+ (nfix (caddr (car ctl))) (nfix (cadddr (car ctl)))) (nfix sp)) (handlers-ok (cdr ctl) sp)))
        (t (handlers-ok (cdr ctl) sp))))

(defthm handlers-ok-bigger
  (implies (and (handlers-ok ctl sp) (<= (nfix sp) (nfix sp2))) (handlers-ok ctl sp2)))

(defthm handlers-ok-hfind
  (implies (and (handlers-ok ctl sp) (consp (hfind ctl)))
           (<= (+ (nfix (caddr (car (hfind ctl)))) (nfix (cadddr (car (hfind ctl))))) (nfix sp)))
  :rule-classes :linear)

(defthm handlers-ok-hfind-rest
  (implies (and (handlers-ok ctl sp) (consp (hfind ctl))) (handlers-ok (cdr (hfind ctl)) sp)))

; ---- THE CALL'S STEP, by clause ---------------------------------------------------

(defthm s2step-callv
  (implies (and (sstatep s) (equal (car (sins s)) :callv) (<= (1+ (nfix (cadr (sins s)))) (caddr s)))
           (equal (vcs2-step prog s)
                  (let* ((m (nfix (cadr (sins s)))) (c (nth (1- (caddr s)) (cadddr s))) (fb2 (- (caddr s) (1+ m)))
                         (cl (pick-arity (cdr (assoc-equal (clo-f c) (cdr prog))) m)))
                    (cond ((not (clop c))
                           (let ((a (prim :invoke (cons c (stk-from fb2 m (cadddr s))))))
                             (if (throwp a)
                                 (unwind (cdr a) (s-ctl s) (cadddr s))
                               (list (1+ (car s)) (cadr s) (1+ fb2) (ssetreg fb2 a (cadddr s)) (s-ctl s)))))
                          ((not (consp cl)) (unwind :arity (s-ctl s) (cadddr s)))
                          ((not (restp cl)) (list (nfix (cadr cl)) fb2 (caddr s) (cadddr s)
                                                  (cons (list (1+ (car s)) (cadr s)) (s-ctl s))))
                          (t (let ((n (nfix (car cl))))
                               (list (nfix (cadr cl)) fb2 (+ fb2 n 2)
                                     (update-nth (+ fb2 n 1) c
                                                 (update-nth (+ fb2 n) (stk-from (+ fb2 n) (- m n) (cadddr s)) (cadddr s)))
                                     (cons (list (1+ (car s)) (cadr s)) (s-ctl s)))))))))
  :hints (("Goal" :in-theory (enable vcs2-step sstatep sreg))))

; ---- THE FUNCTION TABLE: an entry per clause, its code where it says -----------

(defun entries-ok (cls ents code)
  (if (atom cls)
      (atom ents)
    (and (consp ents) (consp (car cls)) (consp (car ents))
         (equal (nfix (car (car ents))) (nfix (car (car cls))))
         (iff (restp (car ents)) (restp (car cls)))
         (natp (cadr (car ents)))
         (ccode-at code (cadr (car ents)) (vcs2-body (car cls) (cadr (car ents))))
         (entries-ok (cdr cls) (cdr ents) code))))

(defmacro pick-corr (pick)
  `(let ((cl (,pick cls m)) (en (,pick ents m)))
     (and (iff (consp en) (consp cl))
          (implies (consp cl)
                   (and (equal (nfix (car en)) (nfix (car cl)))
                        (iff (restp en) (restp cl))
                        (natp (cadr en))
                        (ccode-at code (cadr en) (vcs2-body cl (cadr en))))))))

(defun ents-ind (cls ents) (if (atom cls) (list ents) (ents-ind (cdr cls) (cdr ents))))

(defthm pick-fixed-corr
  (implies (entries-ok cls ents code) (pick-corr pick-fixed))
  :hints (("Goal" :induct (ents-ind cls ents) :in-theory (disable vcs2-body ccode-at))))

(defthm pick-rest-corr
  (implies (entries-ok cls ents code) (pick-corr pick-rest))
  :hints (("Goal" :induct (ents-ind cls ents) :in-theory (disable vcs2-body ccode-at))))

; a pick is nothing or a clause
(defthm pick-fixed-nil-or-cons
  (implies (entries-ok cls ents code)
           (and (iff (pick-fixed cls m) (consp (pick-fixed cls m))) (iff (pick-fixed ents m) (consp (pick-fixed ents m)))))
  :hints (("Goal" :induct (ents-ind cls ents) :in-theory (disable vcs2-body ccode-at))))

; THE ARITY THE MACHINE PICKS is the clause the meaning picks
(defthm pick-arity-corr
  (implies (entries-ok cls ents code) (pick-corr pick-arity))
  :hints (("Goal" :in-theory (union-theories (quote (pick-arity)) (theory (quote minimal-theory))) :do-not-induct t
                  :use (pick-fixed-corr pick-rest-corr pick-fixed-nil-or-cons))))

(defun-sk s2fns-ok (prog defs)
  (forall name (entries-ok (cdr (assoc-equal name defs)) (cdr (assoc-equal name (cdr prog))) (car prog))))
(in-theory (disable s2fns-ok))

; ---- THE PROPERTY -------------------------------------------------------------------

(defun s2-hyps (e depth cenv self caps s env defs prog lc)
  (and (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
       (ccode-at (car prog) (car s) (vcs2-compile e depth cenv self (car s) lc))
       (x2wf e (len env) (lck lc)) (lc-ok lc depth)
       (cenv-ok cenv env (cadddr s) (cadr s) depth)
       (cself-ok self caps (cadddr s) (cadr s) depth)
       (x2defs-ok defs) (s2fns-ok prog defs)
       (handlers-ok (s-ctl s) (caddr s))))

(defun s2-val (e s r s2)
  (implies (valp r)
           (and (sstatep s2)
                (equal (car s2) (+ (car s) (s2code-len e)))
                (equal (cadr s2) (cadr s))
                (equal (caddr s2) (1+ (caddr s)))
                (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (update-nth (caddr s) (val r) (cadddr s)) (1+ (caddr s))))))

(defun s2-rec (s r s2 lc)
  (implies (recurp r)
           (and (consp lc)
                (sstatep s2)
                (equal (car s2) (car lc))
                (equal (cadr s2) (cadr s))
                (equal (caddr s2) (+ (cadr s) (cadr lc) (caddr lc)))
                (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (cadddr s) (+ (cadr s) (cadr lc)))
                (cvals-at (+ (cadr s) (cadr lc)) (cdr r) (cadddr s2))
                (equal (len (cdr r)) (caddr lc)))))

; a throw: at the nearest handler, its local the value, nothing below it
; changed; with none, stopped at :thrown with the value at slot 0
(defun thrown-at (s v s2)
  (let ((tl (hfind (s-ctl s))))
    (if (consp tl)
        (let ((hfb (nfix (caddr (car tl)))) (hd (nfix (cadddr (car tl)))))
          (and (sstatep s2) (equal (car s2) (nfix (cadr (car tl)))) (equal (cadr s2) hfb)
               (equal (caddr s2) (+ hfb hd 1)) (equal (s-ctl s2) (cdr tl))
               (cagree (cadddr s2) (update-nth (+ hfb hd) v (cadddr s)) (+ hfb hd 1))))
      (and (equal (car s2) :thrown) (equal (nth 0 (cadddr s2)) v)))))

(defun s2-thr (s r s2) (implies (thrownp r) (thrown-at s (cdr r) s2)))

(defun s2good (e depth cenv self caps s env defs fuel prog lc)
  (implies (s2-hyps e depth cenv self caps s env defs prog lc)
           (let ((r (mx2 e env caps defs fuel)) (s2 (vcs2-run prog s (s2clk e env caps defs fuel))))
             (and (s2-val e s r s2) (s2-rec s r s2 lc) (s2-thr s r s2)))))

(defun s2good-args (es depth cenv self caps s env defs fuel prog)
  (implies (and (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
                (ccode-at (car prog) (car s) (vcs2-compile-args es depth cenv self (car s)))
                (x2wf-args es (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
                (cself-ok self caps (cadddr s) (cadr s) depth)
                (x2defs-ok defs) (s2fns-ok prog defs) (handlers-ok (s-ctl s) (caddr s)))
           (let ((r (mx2-args es env caps defs fuel)) (s2 (vcs2-run prog s (s2clk-args es env caps defs fuel))))
             (and (implies (valp r)
                           (and (sstatep s2)
                                (equal (car s2) (+ (car s) (s2code-len-args es)))
                                (equal (cadr s2) (cadr s))
                                (equal (caddr s2) (+ (caddr s) (len es)))
                                (equal (s-ctl s2) (s-ctl s))
                                (cagree (cadddr s2) (cadddr s) (caddr s))
                                (cvals-at (caddr s) (val r) (cadddr s2))))
                  (s2-thr s r s2)))))

; ---- NEVER A RECUR outside a loop body's tail ---------------------------------------

(defun mx2l-ind (e base vs caps defs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (consp e)) (zp fuel))
      (list e base vs caps defs)
    (mx2l-ind e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))

(defthm mx2-loop-not-recur
  (not (equal (car (mx2-loop e base vs caps defs fuel)) :recur))
  :hints (("Goal" :induct (mx2l-ind e base vs caps defs fuel) :in-theory (disable mx2)
                  :expand ((mx2-loop e base vs caps defs fuel)))))

(defun mx2-ind (flg e env caps defs fuel)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (if (eq flg :args)
      (if (atom e)
          nil
        (list (mx2-ind :m (car e) env caps defs fuel) (mx2-ind :args (cdr e) env caps defs fuel)))
    (case (car e)
      (:if (list (mx2-ind :m (cadr e) env caps defs fuel) (mx2-ind :m (caddr e) env caps defs fuel)
                 (mx2-ind :m (cadddr e) env caps defs fuel)))
      (:let (list (mx2-ind :m (cadr e) env caps defs fuel)
                  (mx2-ind :m (caddr e) (append env (list (val (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)))
      ((:add :lt) (list (mx2-ind :m (cadr e) env caps defs fuel) (mx2-ind :m (caddr e) env caps defs fuel)))
      ((:mkclo :prim) (mx2-ind :args (cddr e) env caps defs fuel))
      (:callv (list (mx2-ind :args (cddr e) env caps defs fuel) (mx2-ind :m (cadr e) env caps defs fuel)
                    (if (zp fuel) nil
                      (mx2-ind :m (cadr (x2-cl)) (x2-benv) (clo-caps (val (x2-rf))) defs (1- fuel)))))
      ((:loop :recur) (mx2-ind :args (if (eq (car e) :loop) (cadr e) (cdr e)) env caps defs fuel))
      (:throw (mx2-ind :m (cadr e) env caps defs fuel))
      (:try (list (mx2-ind :m (cadr e) env caps defs fuel)
                  (mx2-ind :m (caddr e) (append env (list (cdr (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)))
      (otherwise nil))))

; the clause a call picks is well formed for the locals it gets
(defthm clauses-ok-pick
  (implies (and (clauses-ok cls) (consp (pick-arity cls m)))
           (and (natp (car (pick-arity cls m)))
                (x2wf (cadr (pick-arity cls m))
                      (if (restp (pick-arity cls m)) (1+ (car (pick-arity cls m))) (car (pick-arity cls m))) nil))))

(defthm x2defs-ok-clauses
  (implies (x2defs-ok ds) (clauses-ok (cdr (assoc-equal name ds)))))

(defthm len-split-rest
  (implies (<= (nfix n) (len vs)) (equal (len (split-rest n vs)) (1+ (nfix n)))))

(defthm pick-fixed-not-rest
  (implies (pick-fixed cls m) (and (not (restp (pick-fixed cls m))) (equal (nfix (car (pick-fixed cls m))) m))))

(defthm pick-rest-is-rest
  (implies (pick-rest cls m) (and (restp (pick-rest cls m)) (<= (nfix (car (pick-rest cls m))) m)))
  :rule-classes (:rewrite (:linear :corollary (implies (pick-rest cls m) (<= (nfix (car (pick-rest cls m))) m)))))

; a variadic clause is picked only with at least its arity
(defthm pick-arity-rest-len
  (implies (and (natp m) (consp (pick-arity cls m)) (restp (pick-arity cls m)))
           (<= (nfix (car (pick-arity cls m))) m))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance pick-rest-is-rest) (:instance pick-fixed-not-rest)))))

(defthm pick-arity-fixed-len
  (implies (and (natp m) (consp (pick-arity cls m)) (not (restp (pick-arity cls m))))
           (equal (nfix (car (pick-arity cls m))) m))
  :hints (("Goal" :use ((:instance pick-rest-is-rest) (:instance pick-fixed-not-rest)))))

; the clause a call runs is well formed for the locals the call gives it
(defmacro pk () (quote (pick-arity (cdr (assoc-equal name defs)) (len vs))))

(defthm pick-arity-natp
  (implies (and (x2defs-ok defs) (consp (pk))) (and (integerp (car (pk))) (<= 0 (car (pk)))))
  :hints (("Goal" :in-theory (disable pick-arity clauses-ok-pick)
                  :use ((:instance clauses-ok-pick (cls (cdr (assoc-equal name defs))) (m (len vs)))))))

(defthm pick-body-wf-fixed
  (implies (and (x2defs-ok defs) (consp (pk)) (not (restp (pk)))) (x2wf (cadr (pk)) (len vs) nil))
  :hints (("Goal" :in-theory (disable pick-arity clauses-ok-pick pick-arity-fixed-len)
                  :use ((:instance clauses-ok-pick (cls (cdr (assoc-equal name defs))) (m (len vs)))
                        (:instance pick-arity-fixed-len (cls (cdr (assoc-equal name defs))) (m (len vs)))))))

(defthm pick-body-wf-rest
  (implies (and (x2defs-ok defs) (consp (pk)) (restp (pk))) (x2wf (cadr (pk)) (len (split-rest (car (pk)) vs)) nil))
  :hints (("Goal" :in-theory (disable pick-arity clauses-ok-pick pick-arity-rest-len split-rest)
                  :use ((:instance clauses-ok-pick (cls (cdr (assoc-equal name defs))) (m (len vs)))
                        (:instance pick-arity-rest-len (cls (cdr (assoc-equal name defs))) (m (len vs)))))))

(defthm mx2-not-recur-flag
  (if (eq flg :args)
      (implies (and (x2wf-args e (len env)) (x2defs-ok defs)) (not (equal (car (mx2-args e env caps defs fuel)) :recur)))
    (implies (and (x2wf e (len env) nil) (x2defs-ok defs)) (not (equal (car (mx2 e env caps defs fuel)) :recur))))
  :rule-classes nil
  :hints (("Goal" :induct (mx2-ind flg e env caps defs fuel) :in-theory (disable pick-arity split-rest)
                  :expand ((mx2 e env caps defs fuel) (mx2-args e env caps defs fuel) (x2wf e (len env) nil)))))

(defthm mx2-not-recur
  (implies (and (x2wf e (len env) nil) (x2defs-ok defs)) (not (equal (car (mx2 e env caps defs fuel)) :recur)))
  :hints (("Goal" :use ((:instance mx2-not-recur-flag (flg :m))))))

(defthm mx2-args-not-recur
  (implies (and (x2wf-args es (len env)) (x2defs-ok defs)) (not (equal (car (mx2-args es env caps defs fuel)) :recur)))
  :hints (("Goal" :use ((:instance mx2-not-recur-flag (flg :args) (e es))))))

; ---- A PART'S THROW IS THE WHOLE'S ------------------------------------------------
;
; a part that throws from a state with the same control stack, its
; stack as the whole's below the whole's start: the handler's slot is at
; or below that start (handlers-ok), so the part's pushes never reach it

(defthm thrown-at-transfer
  (implies (and (thrown-at s1 v s2) (equal (s-ctl s1) (s-ctl s))
                (handlers-ok (s-ctl s) (caddr s)) (natp (caddr s))
                (cagree (cadddr s1) (cadddr s) (caddr s)))
           (thrown-at s v s2))
  :hints (("Goal" :in-theory (disable cagree-trans cagree-same-write cagree-smaller handlers-ok-hfind)
                  :use ((:instance handlers-ok-hfind (ctl (s-ctl s)) (sp (caddr s)))
                        (:instance cagree-smaller (a (cadddr s1)) (b (cadddr s)) (h (caddr s))
                                   (g (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-same-write (a (cadddr s1)) (b (cadddr s))
                                   (d (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s)))))))
                                   (h (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-write-at (a (cadddr s1)) (b (cadddr s)) (x v)
                                   (n (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-trans (a (cadddr s2))
                                   (b (update-nth (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))
                                                  v (cadddr s1)))
                                   (c (update-nth (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))
                                                  v (cadddr s)))
                                   (h (+ 1 (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))))))

; a stack pushed on at sp agrees with the old one below sp
(defthm cagree-below-push
  (implies (and (cagree a (update-nth sp v b) (1+ sp)) (natp sp)) (cagree a b sp))
  :hints (("Goal" :use ((:instance cagree-past-write (b b) (g sp) (w v) (h (1+ sp)) (f sp))))))

; ---- the leaves -----------------------------------------------------------------------

(defthm s2good-const
  (implies (equal (car e) :const) (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (e/d (vcsx-step-old) (nth update-nth)))))

(defthm s2good-local
  (implies (equal (car e) :local) (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth)
                  :use ((:instance cenv-ok-local-cenv (i (cadr e)) (regs (cadddr s)) (fb (cadr s)) (f depth))))))

(defthm s2good-capt
  (implies (equal (car e) :capt) (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth) :cases ((natp self)))))

(defthm s2good-other
  (implies (not (member-equal (car e) '(:const :local :capt :if :let :add :lt :mkclo :callv :loop :recur
                                        :prim :throw :try)))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm s2good-leaf
  (implies (not (member-equal (car e) '(:if :let :add :lt :mkclo :callv :loop :recur :prim :throw :try)))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :cases ((equal (car e) :const) (equal (car e) :local) (equal (car e) :capt))
                  :in-theory (union-theories '(s2good-const s2good-local s2good-capt s2good-other member-equal)
                                             (theory 'minimal-theory)))))

; ---- a part's outcome, extracted ---------------------------------------------------

(defthm s2good-gives
  (implies (and (s2good e depth cenv self caps s env defs fuel prog lc) (s2-hyps e depth cenv self caps s env defs prog lc))
           (and (s2-val e s (mx2 e env caps defs fuel) (vcs2-run prog s (s2clk e env caps defs fuel)))
                (s2-rec s (mx2 e env caps defs fuel) (vcs2-run prog s (s2clk e env caps defs fuel)) lc)
                (s2-thr s (mx2 e env caps defs fuel) (vcs2-run prog s (s2clk e env caps defs fuel)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (quote (s2good)) (theory (quote minimal-theory))))))

(defthm s2-val-open
  (implies (and (s2-val e s r s2) (valp r))
           (and (sstatep s2) (equal (car s2) (+ (car s) (s2code-len e))) (equal (cadr s2) (cadr s))
                (equal (caddr s2) (1+ (caddr s))) (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (update-nth (caddr s) (cdr r) (cadddr s)) (1+ (caddr s)))))
  :rule-classes nil)

(defthm s2-rec-open
  (implies (and (s2-rec s r s2 lc) (recurp r))
           (and (consp lc) (sstatep s2) (equal (car s2) (car lc)) (equal (cadr s2) (cadr s))
                (equal (caddr s2) (+ (cadr s) (cadr lc) (caddr lc))) (equal (s-ctl s2) (s-ctl s))
                (cagree (cadddr s2) (cadddr s) (+ (cadr s) (cadr lc)))
                (cvals-at (+ (cadr s) (cadr lc)) (cdr r) (cadddr s2))
                (equal (len (cdr r)) (caddr lc))))
  :rule-classes nil)

(defthm s2-thr-open
  (implies (and (s2-thr s r s2) (thrownp r)) (thrown-at s (cdr r) s2))
  :rule-classes nil)

(defmacro l2-thy ()
  '(union-theories '(valp val recurp thrownp lc-ok lck natp-c+x sstatep-fc sstatep-list natp-s2code-len natp-s2code-len-args
                     vcs2-step-old vcs2-step-nopc vcsx-step-old sstep-jmpf sstep-jmp)
                   (set-difference-theories (theory 'ground-zero) '(update-nth nth))))

; ---- a binary operation -------------------------------------------------------------

(defthm mx2-binop
  (implies (member-equal (car e) '(:add :lt))
           (equal (mx2 e env caps defs fuel)
                  (cond ((not (valp (mx2 (cadr e) env caps defs fuel))) (mx2 (cadr e) env caps defs fuel))
                        ((not (valp (mx2 (caddr e) env caps defs fuel))) (mx2 (caddr e) env caps defs fuel))
                        ((eq (car e) :add) (cons :val (+ (fix (cdr (mx2 (cadr e) env caps defs fuel)))
                                                         (fix (cdr (mx2 (caddr e) env caps defs fuel))))))
                        (t (cons :val (bool (< (rfix (cdr (mx2 (cadr e) env caps defs fuel)))
                                               (rfix (cdr (mx2 (caddr e) env caps defs fuel))))))))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))

(defmacro b2-s1 () '(vcs2-run prog s (s2clk (cadr e) env caps defs fuel)))
(defmacro b2-s2 () '(vcs2-run prog (b2-s1) (s2clk (caddr e) env caps defs fuel)))
(defmacro b2-ra () '(mx2 (cadr e) env caps defs fuel))
(defmacro b2-rb () '(mx2 (caddr e) env caps defs fuel))

(defthm binop2-clock
  (implies (member-equal (car e) '(:add :lt))
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (cond ((not (valp (b2-ra))) (b2-s1))
                        ((not (valp (b2-rb))) (b2-s2))
                        (t (vcs2-step prog (b2-s2))))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm binop2-code
  (implies (and (member-equal (car e) '(:add :lt)) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile (cadr e) depth cenv self pc nil))
                (ccode-at code (+ pc (s2code-len (cadr e))) (vcs2-compile (caddr e) (1+ depth) cenv self (+ pc (s2code-len (cadr e))) nil))
                (equal (nth (+ pc (s2code-len (cadr e)) (s2code-len (caddr e))) code) (list (car e)))
                (equal (s2code-len e) (+ (s2code-len (cadr e)) (s2code-len (caddr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defthm binop2-hyps-a
  (implies (and (member-equal (car e) '(:add :lt)) (s2-hyps e depth cenv self caps s env defs prog lc))
           (s2-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :do-not-induct t :expand ((x2wf e (len env) (lck lc)))
                  :use ((:instance binop2-code (code (car prog)) (pc (car s)))))))

(defthm binop2-hyps-b
  (implies (and (member-equal (car e) '(:add :lt)) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2-val (cadr e) s ra s1) (valp ra))
           (s2-hyps (caddr e) (1+ depth) cenv self caps s1 env defs prog nil))
  :hints (("Goal" :do-not-induct t :expand ((x2wf e (len env) (lck lc)))
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance binop2-code (code (car prog)) (pc (car s)))
                        (:instance handlers-ok-bigger (ctl (s-ctl s)) (sp (caddr s)) (sp2 (caddr s1)))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ra)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ra)) (h (1+ (caddr s))) (k (1+ depth)))))))

(defmacro binop2-hyps ()
  '(and (member-equal (car e) '(:add :lt)) (s2-hyps e depth cenv self caps s env defs prog lc)
        (s2good (cadr e) depth cenv self caps s env defs fuel prog nil)
        (s2good (caddr e) (1+ depth) cenv self caps (b2-s1) env defs fuel prog nil)))

; the first operand's outcome
(defthm binop2-a
  (implies (binop2-hyps)
           (and (s2-val (cadr e) s (b2-ra) (b2-s1)) (s2-thr s (b2-ra) (b2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance binop2-hyps-a) (:instance s2good-gives (e (cadr e)) (lc nil))))))

; the second operand's, from where the first left off
(defthm binop2-b
  (implies (and (binop2-hyps) (valp (b2-ra)))
           (and (s2-val (caddr e) (b2-s1) (b2-rb) (b2-s2)) (s2-thr (b2-s1) (b2-rb) (b2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance binop2-a) (:instance binop2-hyps-b (ra (b2-ra)) (s1 (b2-s1)))
                        (:instance s2good-gives (e (caddr e)) (depth (1+ depth)) (s (b2-s1)) (lc nil))))))

; THE VALUE: both operands, then the operation
(defthm binop2-path-val
  (implies (and (binop2-hyps) (valp (b2-ra)) (valp (b2-rb)))
           (s2-val e s (mx2 e env caps defs fuel) (vcs2-step prog (b2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (l2-thy)) :do-not-induct t
                  :use ((:instance binop2-a) (:instance binop2-b) (:instance mx2-binop)
                        (:instance (:definition s2-hyps))
                        (:instance binop2-code (code (car prog)) (pc (car s)))
                        (:instance s2-val-open (e (cadr e)) (r (b2-ra)) (s2 (b2-s1)))
                        (:instance s2-val-open (e (caddr e)) (s (b2-s1)) (r (b2-rb)) (s2 (b2-s2)))
                        (:instance add-step-abs (sp (caddr s)) (s1 (b2-s1)) (s2 (b2-s2)) (va (cdr (b2-ra))) (vb (cdr (b2-rb))))
                        (:instance lt-step-abs (sp (caddr s)) (s1 (b2-s1)) (s2 (b2-s2)) (va (cdr (b2-ra))) (vb (cdr (b2-rb))))))))

; THE THROW: from the first operand, or from the second after the first
(defthm binop2-path-thr
  (implies (and (binop2-hyps) (thrownp (mx2 e env caps defs fuel)))
           (s2-thr s (mx2 e env caps defs fuel) (vcs2-run prog s (s2clk e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-thr) (l2-thy)) :do-not-induct t
                  :cases ((not (valp (b2-ra))))
                  :use ((:instance binop2-a) (:instance binop2-b) (:instance mx2-binop) (:instance binop2-clock)
                        (:instance (:definition s2-hyps))
                        (:instance s2-val-open (e (cadr e)) (r (b2-ra)) (s2 (b2-s1)))
                        (:instance s2-thr-open (r (b2-ra)) (s2 (b2-s1)))
                        (:instance s2-thr-open (s (b2-s1)) (r (b2-rb)) (s2 (b2-s2)))
                        (:instance cagree-below-push (a (cadddr (b2-s1))) (b (cadddr s)) (sp (caddr s)) (v (cdr (b2-ra))))
                        (:instance thrown-at-transfer (s1 (b2-s1)) (v (cdr (b2-rb))) (s2 (b2-s2)))))))

(defthm x2wf-binop-parts
  (implies (and (member-equal (car e) (quote (:add :lt))) (x2wf e n k))
           (and (x2wf (cadr e) n nil) (x2wf (caddr e) n nil)))
  :rule-classes nil)

(defthm mx2-binop-rw
  (implies (member-equal (car e) (quote (:add :lt)))
           (equal (mx2 e env caps defs fuel)
                  (cond ((not (valp (mx2 (cadr e) env caps defs fuel))) (mx2 (cadr e) env caps defs fuel))
                        ((not (valp (mx2 (caddr e) env caps defs fuel))) (mx2 (caddr e) env caps defs fuel))
                        ((eq (car e) :add) (cons :val (+ (fix (cdr (mx2 (cadr e) env caps defs fuel)))
                                                         (fix (cdr (mx2 (caddr e) env caps defs fuel))))))
                        (t (cons :val (bool (< (rfix (cdr (mx2 (cadr e) env caps defs fuel)))
                                               (rfix (cdr (mx2 (caddr e) env caps defs fuel))))))))))
  :hints (("Goal" :use mx2-binop)))
(in-theory (disable mx2-binop-rw))

(defthm sxgood2-binop-norec
  (implies (and (member-equal (car e) (quote (:add :lt))) (s2-hyps e depth cenv self caps s env defs prog lc))
           (not (recurp (mx2 e env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories (quote (recurp s2-hyps mx2-binop-rw car-cons)) (theory (quote minimal-theory)))
                  :use ((:instance x2wf-binop-parts (n (len env)) (k (lck lc)))
                        (:instance mx2-not-recur (e (cadr e)))
                        (:instance mx2-not-recur (e (caddr e)))))))

(defthm binop2-val-parts
  (implies (and (member-equal (car e) (quote (:add :lt))) (valp (mx2 e env caps defs fuel)))
           (and (valp (b2-ra)) (valp (b2-rb))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (quote (valp mx2-binop-rw car-cons)) (theory (quote minimal-theory))))))

(defthm s2good-binop
  (implies (and (member-equal (car e) '(:add :lt))
                (s2good (cadr e) depth cenv self caps s env defs fuel prog nil)
                (s2good (caddr e) (1+ depth) cenv self caps (b2-s1) env defs fuel prog nil))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp) (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance binop2-path-val) (:instance binop2-path-thr) (:instance binop2-clock) (:instance binop2-val-parts)
                        (:instance sxgood2-binop-norec)))))

; ---- a let ----------------------------------------------------------------------------

(defthm mx2-let
  (implies (equal (car e) :let)
           (equal (mx2 e env caps defs fuel)
                  (if (valp (mx2 (cadr e) env caps defs fuel))
                      (mx2 (caddr e) (append env (list (cdr (mx2 (cadr e) env caps defs fuel)))) caps defs fuel)
                    (mx2 (cadr e) env caps defs fuel))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-let))

(defthm let2-code
  (implies (and (equal (car e) :let) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile (cadr e) depth cenv self pc nil))
                (ccode-at code (+ pc (s2code-len (cadr e)))
                          (vcs2-compile (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (s2code-len (cadr e))) lc))
                (equal (nth (+ pc (s2code-len (cadr e)) (s2code-len (caddr e))) code) (list :slide))
                (equal (s2code-len e) (+ (s2code-len (cadr e)) (s2code-len (caddr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defmacro l2-ri () '(mx2 (cadr e) env caps defs fuel))
(defmacro l2-env () '(append env (list (cdr (mx2 (cadr e) env caps defs fuel)))))
(defmacro l2-rb () '(mx2 (caddr e) (l2-env) caps defs fuel))
(defmacro l2-s1 () '(vcs2-run prog s (s2clk (cadr e) env caps defs fuel)))
(defmacro l2-s2 () '(vcs2-run prog (l2-s1) (s2clk (caddr e) (l2-env) caps defs fuel)))

(defthm let2-clock
  (implies (equal (car e) :let)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (cond ((not (valp (l2-ri))) (l2-s1))
                        ((valp (l2-rb)) (vcs2-step prog (l2-s2)))
                        (t (l2-s2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm let2-hyps-init
  (implies (and (equal (car e) :let) (s2-hyps e depth cenv self caps s env defs prog lc))
           (s2-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :use ((:instance let2-code (code (car prog)) (pc (car s)))) :do-not-induct t
                  :expand ((x2wf e (len env) (lck lc))))))

(defthm let2-hyps-body
  (implies (and (equal (car e) :let) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2-val (cadr e) s ri s1) (valp ri))
           (s2-hyps (caddr e) (1+ depth) (append cenv (list depth)) self caps s1 (append env (list (cdr ri))) defs prog lc))
  :hints (("Goal" :expand ((x2wf e (len env) (lck lc))) :do-not-induct t
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance let2-code (code (car prog)) (pc (car s)))
                        (:instance handlers-ok-bigger (ctl (s-ctl s)) (sp (caddr s)) (sp2 (caddr s1)))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ri)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr ri)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cagree-nth (a (cadddr s1)) (b (update-nth (caddr s) (cdr ri) (cadddr s)))
                                   (h (caddr s1)) (r (caddr s)))))))

(defmacro let2-hyps ()
  '(and (equal (car e) :let) (s2-hyps e depth cenv self caps s env defs prog lc)
        (s2good (cadr e) depth cenv self caps s env defs fuel prog nil)
        (s2good (caddr e) (1+ depth) (append cenv (list depth)) self caps (l2-s1) (l2-env) defs fuel prog lc)))

(defthm let2-a
  (implies (let2-hyps)
           (and (s2-val (cadr e) s (l2-ri) (l2-s1)) (s2-thr s (l2-ri) (l2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance let2-hyps-init) (:instance s2good-gives (e (cadr e)) (lc nil))))))

(defthm let2-b
  (implies (and (let2-hyps) (valp (l2-ri)))
           (and (s2-val (caddr e) (l2-s1) (l2-rb) (l2-s2)) (s2-rec (l2-s1) (l2-rb) (l2-s2) lc)
                (s2-thr (l2-s1) (l2-rb) (l2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance let2-a) (:instance let2-hyps-body (ri (l2-ri)) (s1 (l2-s1)))
                        (:instance s2good-gives (e (caddr e)) (depth (1+ depth)) (cenv (append cenv (list depth)))
                                   (s (l2-s1)) (env (l2-env)))))))

(defthm let2-path-val
  (implies (and (let2-hyps) (valp (l2-ri)) (valp (l2-rb)))
           (s2-val e s (l2-rb) (vcs2-step prog (l2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (l2-thy)) :do-not-induct t
                  :use ((:instance let2-a) (:instance let2-b) (:instance (:definition s2-hyps))
                        (:instance s2-val-open (e (cadr e)) (r (l2-ri)) (s2 (l2-s1)))
                        (:instance s2-val-open (e (caddr e)) (s (l2-s1)) (r (l2-rb)) (s2 (l2-s2)))
                        (:instance let2-code (code (car prog)) (pc (car s)))
                        (:instance slide-step-abs (sp (caddr s)) (s1 (l2-s1)) (s2 (l2-s2)) (va (cdr (l2-ri))) (vb (cdr (l2-rb))))))))

(defthm let2-path-rec
  (implies (and (let2-hyps) (valp (l2-ri)) (recurp (l2-rb)))
           (s2-rec s (l2-rb) (l2-s2) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-rec) (l2-thy)) :do-not-induct t
                  :use ((:instance let2-a) (:instance let2-b) (:instance (:definition s2-hyps))
                        (:instance s2-val-open (e (cadr e)) (r (l2-ri)) (s2 (l2-s1)))
                        (:instance s2-rec-open (s (l2-s1)) (r (l2-rb)) (s2 (l2-s2)))
                        (:instance cagree-through-push (a (cadddr (l2-s2))) (b (cadddr (l2-s1))) (c (cadddr s))
                                   (h (+ (cadr s) (cadr lc))) (sp (caddr s)) (v (cdr (l2-ri))))))))

(defthm let2-path-thr
  (implies (and (let2-hyps) (valp (l2-ri)) (thrownp (l2-rb)))
           (s2-thr s (l2-rb) (l2-s2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-thr) (l2-thy)) :do-not-induct t
                  :use ((:instance let2-a) (:instance let2-b) (:instance (:definition s2-hyps))
                        (:instance s2-val-open (e (cadr e)) (r (l2-ri)) (s2 (l2-s1)))
                        (:instance s2-thr-open (s (l2-s1)) (r (l2-rb)) (s2 (l2-s2)))
                        (:instance cagree-below-push (a (cadddr (l2-s1))) (b (cadddr s)) (sp (caddr s)) (v (cdr (l2-ri))))
                        (:instance thrown-at-transfer (s1 (l2-s1)) (v (cdr (l2-rb))) (s2 (l2-s2)))))))

(defthm s2good-let
  (implies (and (equal (car e) :let)
                (s2good (cadr e) depth cenv self caps s env defs fuel prog nil)
                (s2good (caddr e) (1+ depth) (append cenv (list depth)) self caps (l2-s1) (l2-env) defs fuel prog lc))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-let car-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance let2-a) (:instance let2-path-val) (:instance let2-path-rec) (:instance let2-path-thr)
                        (:instance let2-clock) (:instance let2-hyps-init)
                        (:instance (:definition s2-hyps) (e (cadr e)) (lc nil))
                        (:instance mx2-not-recur (e (cadr e)))))))

; ---- an if ----------------------------------------------------------------------------

(defmacro i2-pc1 () '(+ pc (s2code-len (cadr e)) 1))
(defmacro i2-pc2 () '(+ pc (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1))

(defthm if2-code
  (implies (and (equal (car e) :if) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile (cadr e) depth cenv self pc nil))
                (equal (nth (+ pc (s2code-len (cadr e))) code) (list :jmpf (i2-pc2)))
                (ccode-at code (i2-pc1) (vcs2-compile (caddr e) depth cenv self (i2-pc1) lc))
                (equal (nth (+ (i2-pc1) (s2code-len (caddr e))) code) (list :jmp (+ (i2-pc2) (s2code-len (cadddr e)))))
                (ccode-at code (i2-pc2) (vcs2-compile (cadddr e) depth cenv self (i2-pc2) lc))
                (equal (s2code-len e) (+ (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1 (s2code-len (cadddr e))))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defthm mx2-if
  (implies (equal (car e) :if)
           (equal (mx2 e env caps defs fuel)
                  (cond ((not (valp (mx2 (cadr e) env caps defs fuel))) (mx2 (cadr e) env caps defs fuel))
                        ((truthy (cdr (mx2 (cadr e) env caps defs fuel))) (mx2 (caddr e) env caps defs fuel))
                        (t (mx2 (cadddr e) env caps defs fuel)))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-if))

(defmacro i2-rc () '(mx2 (cadr e) env caps defs fuel))
(defmacro i2-rt () '(mx2 (caddr e) env caps defs fuel))
(defmacro i2-re () '(mx2 (cadddr e) env caps defs fuel))
(defmacro i2-s1 () '(vcs2-run prog s (s2clk (cadr e) env caps defs fuel)))
(defmacro i2-s1b () '(vcs2-step prog (i2-s1)))
(defmacro i2-st () '(vcs2-run prog (i2-s1b) (s2clk (caddr e) env caps defs fuel)))
(defmacro i2-se () '(vcs2-run prog (i2-s1b) (s2clk (cadddr e) env caps defs fuel)))

(defthm if2-clock
  (implies (equal (car e) :if)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (cond ((not (valp (i2-rc))) (i2-s1))
                        ((truthy (cdr (i2-rc))) (if (valp (i2-rt)) (vcs2-step prog (i2-st)) (i2-st)))
                        (t (i2-se)))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm if2-hyps-test
  (implies (and (equal (car e) :if) (s2-hyps e depth cenv self caps s env defs prog lc))
           (s2-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :do-not-induct t :expand ((x2wf e (len env) (lck lc)))
                  :use ((:instance if2-code (code (car prog)) (pc (car s)))))))

(defthm if2-hyps-branch
  (implies (and (equal (car e) :if) (s2-hyps e depth cenv self caps s env defs prog lc)
                (sstatep s1b) (equal (cadr s1b) (cadr s)) (equal (caddr s1b) (caddr s)) (equal (s-ctl s1b) (s-ctl s))
                (cagree (cadddr s1b) (update-nth (caddr s) v (cadddr s)) (1+ (caddr s)))
                (equal (car s1b) (if th (+ (car s) (s2code-len (cadr e)) 1)
                                   (+ (car s) (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1))))
           (s2-hyps (if th (caddr e) (cadddr e)) depth cenv self caps s1b env defs prog lc))
  :hints (("Goal" :do-not-induct t :expand ((x2wf e (len env) (lck lc)))
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance if2-code (code (car prog)) (pc (car s)))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1b)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (h (1+ (caddr s))) (k depth))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1b)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (h (1+ (caddr s))) (k depth))))))

(defthm if2-test
  (implies (and (equal (car e) :if) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good (cadr e) depth cenv self caps s env defs fuel prog nil))
           (and (s2-val (cadr e) s (i2-rc) (i2-s1)) (s2-thr s (i2-rc) (i2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance if2-hyps-test) (:instance s2good-gives (e (cadr e)) (lc nil))))))

(defthm if2-test-facts
  (implies (and (equal (car e) :if) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good (cadr e) depth cenv self caps s env defs fuel prog nil) (valp (i2-rc)))
           (and (sstatep (i2-s1)) (equal (cadr (i2-s1)) (cadr s)) (equal (caddr (i2-s1)) (1+ (caddr s)))
                (equal (s-ctl (i2-s1)) (s-ctl s))
                (cagree (cadddr (i2-s1)) (update-nth (caddr s) (cdr (i2-rc)) (cadddr s)) (1+ (caddr s)))
                (sstatep (i2-s1b))
                (equal (car (i2-s1b))
                       (if (truthy (cdr (i2-rc)))
                           (+ (car s) (s2code-len (cadr e)) 1)
                         (+ (car s) (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1)))
                (equal (cadr (i2-s1b)) (cadr s)) (equal (caddr (i2-s1b)) (caddr s))
                (equal (cadddr (i2-s1b)) (cadddr (i2-s1))) (equal (s-ctl (i2-s1b)) (s-ctl s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance (:definition s2-hyps))
                        (:instance if2-test)
                        (:instance s2-val-open (e (cadr e)) (r (i2-rc)) (s2 (i2-s1)))
                        (:instance if2-code (code (car prog)) (pc (car s)))
                        (:instance jmpf-step-abs (s1 (i2-s1)) (sp (caddr s))
                                   (tgt (+ (car s) (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1)))
                        (:instance cagree-nth (a (cadddr (i2-s1))) (b (update-nth (caddr s) (cdr (i2-rc)) (cadddr s)))
                                   (h (1+ (caddr s))) (r (caddr s)))))))

(defmacro if2-branch-hyps (x)
  `(and (equal (car e) :if) (s2-hyps e depth cenv self caps s env defs prog lc)
        (s2good (cadr e) depth cenv self caps s env defs fuel prog nil)
        (s2good ,x depth cenv self caps (i2-s1b) env defs fuel prog lc)
        (valp (i2-rc))))

; a branch's outcome, from the state after the jump
(defthm if2-branch
  (implies (and (if2-branch-hyps x) (equal x (if th (caddr e) (cadddr e))) (iff (truthy (cdr (i2-rc))) th))
           (let ((r (mx2 x env caps defs fuel)) (s3 (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel))))
             (and (s2-val x (i2-s1b) r s3) (s2-rec (i2-s1b) r s3 lc) (s2-thr (i2-s1b) r s3))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance if2-test-facts)
                        (:instance if2-hyps-branch (s1b (i2-s1b)) (v (cdr (i2-rc))))
                        (:instance s2good-gives (e x) (s (i2-s1b)))))))

(defthm if2-path-then-val
  (implies (and (if2-branch-hyps (caddr e)) (truthy (cdr (i2-rc))) (valp (i2-rt)))
           (s2-val e s (i2-rt) (vcs2-step prog (i2-st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (l2-thy)) :do-not-induct t
                  :use ((:instance if2-test-facts)
                        (:instance if2-code (code (car prog)) (pc (car s)))
                        (:instance (:definition s2-hyps))
                        (:instance if2-branch (x (caddr e)) (th t))
                        (:instance s2-val-open (e (caddr e)) (s (i2-s1b)) (r (i2-rt)) (s2 (i2-st)))
                        (:instance jmp-step-abs (s2 (i2-st)) (tgt (+ (car s) (s2code-len (cadr e)) 1 (s2code-len (caddr e)) 1
                                                                     (s2code-len (cadddr e)))))
                        (:instance sif-combine (sp (caddr s)) (s3 (cadddr (i2-st))) (s1 (cadddr (i2-s1))) (s0 (cadddr s))
                                   (va (cdr (i2-rc))) (vb (cdr (i2-rt))))))))

(defthm if2-path-else-val
  (implies (and (if2-branch-hyps (cadddr e)) (not (truthy (cdr (i2-rc)))) (valp (i2-re)))
           (s2-val e s (i2-re) (i2-se)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (l2-thy)) :do-not-induct t
                  :use ((:instance if2-test-facts)
                        (:instance if2-code (code (car prog)) (pc (car s)))
                        (:instance (:definition s2-hyps))
                        (:instance if2-branch (x (cadddr e)) (th nil))
                        (:instance s2-val-open (e (cadddr e)) (s (i2-s1b)) (r (i2-re)) (s2 (i2-se)))
                        (:instance sif-combine (sp (caddr s)) (s3 (cadddr (i2-se))) (s1 (cadddr (i2-s1))) (s0 (cadddr s))
                                   (va (cdr (i2-rc))) (vb (cdr (i2-re))))))))

(defthm if2-path-rec
  (implies (and (if2-branch-hyps x) (equal x (if th (caddr e) (cadddr e))) (iff (truthy (cdr (i2-rc))) th)
                (recurp (mx2 x env caps defs fuel)))
           (s2-rec s (mx2 x env caps defs fuel) (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel)) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-rec) (l2-thy)) :do-not-induct t
                  :use ((:instance if2-test-facts)
                        (:instance (:definition s2-hyps))
                        (:instance if2-branch)
                        (:instance s2-rec-open (s (i2-s1b)) (r (mx2 x env caps defs fuel))
                                   (s2 (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel))))
                        (:instance cagree-through-push (a (cadddr (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel))))
                                   (b (cadddr (i2-s1))) (c (cadddr s))
                                   (h (+ (cadr s) (cadr lc))) (sp (caddr s)) (v (cdr (i2-rc))))))))

(defthm if2-path-thr
  (implies (and (if2-branch-hyps x) (equal x (if th (caddr e) (cadddr e))) (iff (truthy (cdr (i2-rc))) th)
                (thrownp (mx2 x env caps defs fuel)))
           (s2-thr s (mx2 x env caps defs fuel) (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-thr) (l2-thy)) :do-not-induct t
                  :use ((:instance if2-test-facts)
                        (:instance (:definition s2-hyps))
                        (:instance if2-branch)
                        (:instance s2-thr-open (s (i2-s1b)) (r (mx2 x env caps defs fuel))
                                   (s2 (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel))))
                        (:instance cagree-below-push (a (cadddr (i2-s1))) (b (cadddr s)) (sp (caddr s)) (v (cdr (i2-rc))))
                        (:instance thrown-at-transfer (s1 (i2-s1b)) (v (cdr (mx2 x env caps defs fuel)))
                                   (s2 (vcs2-run prog (i2-s1b) (s2clk x env caps defs fuel))))))))

(defmacro if2-join-hyps ()
  '(and (equal (car e) :if)
        (s2good (cadr e) depth cenv self caps s env defs fuel prog nil)
        (s2good (caddr e) depth cenv self caps (i2-s1b) env defs fuel prog lc)
        (s2good (cadddr e) depth cenv self caps (i2-s1b) env defs fuel prog lc)))

(defthm s2good-if
  (implies (if2-join-hyps)
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-if car-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :cases ((not (valp (i2-rc))) (truthy (cdr (i2-rc))))
                  :use ((:instance if2-test)
                        (:instance if2-path-then-val) (:instance if2-path-else-val)
                        (:instance if2-path-rec (x (caddr e)) (th t)) (:instance if2-path-rec (x (cadddr e)) (th nil))
                        (:instance if2-path-thr (x (caddr e)) (th t)) (:instance if2-path-thr (x (cadddr e)) (th nil))
                        (:instance if2-clock) (:instance if2-hyps-test)
                        (:instance (:definition s2-hyps) (e (cadr e)) (lc nil))
                        (:instance mx2-not-recur (e (cadr e)))))))

; ---- arguments --------------------------------------------------------------------------

(defthm s2good-args-nil
  (implies (atom es) (s2good-args es depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defmacro a2-s1 () '(vcs2-run prog s (s2clk (car es) env caps defs fuel)))
(defmacro a2-r () '(mx2 (car es) env caps defs fuel))
(defmacro a2-rs () '(mx2-args (cdr es) env caps defs fuel))
(defmacro a2-s2 () '(vcs2-run prog (a2-s1) (s2clk-args (cdr es) env caps defs fuel)))

(defthm mx2-args-cons
  (implies (consp es)
           (equal (mx2-args es env caps defs fuel)
                  (cond ((not (valp (a2-r))) (a2-r))
                        ((valp (a2-rs)) (cons :val (cons (cdr (a2-r)) (cdr (a2-rs)))))
                        (t (a2-rs)))))
  :hints (("Goal" :expand ((mx2-args es env caps defs fuel)))))
(in-theory (disable mx2-args-cons))

(defthm s2clk-args-cons
  (implies (consp es)
           (equal (vcs2-run prog s (s2clk-args es env caps defs fuel))
                  (if (valp (a2-r)) (a2-s2) (a2-s1))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk-args es env caps defs fuel)) :in-theory (disable c+))))

(defthm args2-code
  (implies (and (consp es) (ccode-at code pc (vcs2-compile-args es depth cenv self pc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile (car es) depth cenv self pc nil))
                (ccode-at code (+ pc (s2code-len (car es))) (vcs2-compile-args (cdr es) (1+ depth) cenv self (+ pc (s2code-len (car es)))))
                (equal (s2code-len-args es) (+ (s2code-len (car es)) (s2code-len-args (cdr es))))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile-args es depth cenv self pc) (s2code-len-args es)))))

(defmacro args2-hyps ()
  '(and (consp es) (sstatep s) (natp depth) (equal (caddr s) (+ (cadr s) depth))
        (ccode-at (car prog) (car s) (vcs2-compile-args es depth cenv self (car s)))
        (x2wf-args es (len env)) (cenv-ok cenv env (cadddr s) (cadr s) depth)
        (cself-ok self caps (cadddr s) (cadr s) depth)
        (x2defs-ok defs) (s2fns-ok prog defs) (handlers-ok (s-ctl s) (caddr s))
        (s2good (car es) depth cenv self caps s env defs fuel prog nil)
        (s2good-args (cdr es) (1+ depth) cenv self caps (a2-s1) env defs fuel prog)))

(defthm args2-first
  (implies (args2-hyps)
           (and (s2-val (car es) s (a2-r) (a2-s1)) (s2-thr s (a2-r) (a2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-hyps x2wf-args) (l2-thy)) :do-not-induct t
                  :use ((:instance args2-code (code (car prog)) (pc (car s)))
                        (:instance s2good-gives (e (car es)) (lc nil))))))

(defthm args2-rest
  (implies (and (args2-hyps) (valp (a2-r)))
           (let ((r (a2-rs)) (s2 (a2-s2)))
             (and (implies (valp r)
                           (and (sstatep s2)
                                (equal (car s2) (+ (car (a2-s1)) (s2code-len-args (cdr es))))
                                (equal (cadr s2) (cadr s))
                                (equal (caddr s2) (+ (caddr (a2-s1)) (len (cdr es))))
                                (equal (s-ctl s2) (s-ctl s))
                                (cagree (cadddr s2) (cadddr (a2-s1)) (caddr (a2-s1)))
                                (cvals-at (caddr (a2-s1)) (cdr r) (cadddr s2))))
                  (s2-thr (a2-s1) r s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(x2wf-args) (l2-thy)) :do-not-induct t
                  :use ((:instance args2-first)
                        (:instance s2-val-open (e (car es)) (r (a2-r)) (s2 (a2-s1)))
                        (:instance args2-code (code (car prog)) (pc (car s)))
                        (:instance (:definition s2good-args) (es (cdr es)) (depth (1+ depth)) (s (a2-s1)))
                        (:instance handlers-ok-bigger (ctl (s-ctl s)) (sp (caddr s)) (sp2 (caddr (a2-s1))))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr (a2-s1))) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr (a2-r))) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr (a2-s1))) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (v (cdr (a2-r))) (h (1+ (caddr s))) (k (1+ depth)))))))

(defthm args2-path-val
  (implies (and (args2-hyps) (valp (a2-r)) (valp (a2-rs)))
           (let ((s2 (a2-s2)))
             (and (sstatep s2)
                  (equal (car s2) (+ (car s) (s2code-len-args es)))
                  (equal (cadr s2) (cadr s))
                  (equal (caddr s2) (+ (caddr s) (len es)))
                  (equal (s-ctl s2) (s-ctl s))
                  (cagree (cadddr s2) (cadddr s) (caddr s))
                  (cvals-at (caddr s) (cons (cdr (a2-r)) (cdr (a2-rs))) (cadddr s2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(len) (l2-thy)) :do-not-induct t
                  :expand ((cvals-at (caddr s) (cons (cdr (a2-r)) (cdr (a2-rs))) (cadddr (a2-s2))))
                  :use ((:instance args2-first) (:instance args2-rest)
                        (:instance s2-val-open (e (car es)) (r (a2-r)) (s2 (a2-s1)))
                        (:instance args2-code (code (car prog)) (pc (car s)))
                        (:instance cagree-below-push (a (cadddr (a2-s1))) (b (cadddr s)) (sp (caddr s)) (v (cdr (a2-r))))
                        (:instance cagree-smaller (a (cadddr (a2-s2))) (b (cadddr (a2-s1))) (h (1+ (caddr s))) (g (caddr s)))
                        (:instance cagree-trans (a (cadddr (a2-s2))) (b (cadddr (a2-s1))) (c (cadddr s)) (h (caddr s)))
                        (:instance cagree-nth (a (cadddr (a2-s2))) (b (cadddr (a2-s1))) (h (1+ (caddr s))) (r (caddr s)))
                        (:instance cagree-nth (a (cadddr (a2-s1))) (b (update-nth (caddr s) (cdr (a2-r)) (cadddr s)))
                                   (h (1+ (caddr s))) (r (caddr s)))))))

(defthm args2-path-thr
  (implies (and (args2-hyps) (valp (a2-r)) (thrownp (a2-rs)))
           (s2-thr s (a2-rs) (a2-s2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-thr) (l2-thy)) :do-not-induct t
                  :use ((:instance args2-first) (:instance args2-rest)
                        (:instance s2-val-open (e (car es)) (r (a2-r)) (s2 (a2-s1)))
                        (:instance cagree-below-push (a (cadddr (a2-s1))) (b (cadddr s)) (sp (caddr s)) (v (cdr (a2-r))))
                        (:instance thrown-at-transfer (s1 (a2-s1)) (v (cdr (a2-rs))) (s2 (a2-s2)))))))

(defthm s2good-args-cons
  (implies (and (consp es)
                (s2good (car es) depth cenv self caps s env defs fuel prog nil)
                (s2good-args (cdr es) (1+ depth) cenv self caps (a2-s1) env defs fuel prog))
           (s2good-args es depth cenv self caps s env defs fuel prog))
  :hints (("Goal" :in-theory (union-theories '(s2good-args s2-thr valp val thrownp mx2-args-cons car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance args2-first) (:instance args2-path-val) (:instance args2-path-thr)
                        (:instance s2clk-args-cons)))))

(defthm mx2-args-val-shape
  (implies (valp (mx2-args es env caps defs fuel))
           (and (equal (len (val (mx2-args es env caps defs fuel))) (len es))
                (true-listp (val (mx2-args es env caps defs fuel)))))
  :hints (("Goal" :induct (len es) :expand ((mx2-args es env caps defs fuel)))))

; ---- a throw ------------------------------------------------------------------------------

; unwinding from a state lands where thrown-at says
(defthm unwind-thrown-at
  (thrown-at s v (unwind v (s-ctl s) (cadddr s)))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm mx2-throw
  (implies (equal (car e) :throw)
           (equal (mx2 e env caps defs fuel)
                  (if (valp (mx2 (cadr e) env caps defs fuel))
                      (cons :thrown (cdr (mx2 (cadr e) env caps defs fuel)))
                    (mx2 (cadr e) env caps defs fuel))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-throw))

(defthm throw2-code
  (implies (and (equal (car e) :throw) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile (cadr e) depth cenv self pc nil))
                (equal (nth (+ pc (s2code-len (cadr e))) code) (list :throw))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc)))))

(defmacro t2-r () '(mx2 (cadr e) env caps defs fuel))
(defmacro t2-s1 () '(vcs2-run prog s (s2clk (cadr e) env caps defs fuel)))

(defthm throw2-clock
  (implies (equal (car e) :throw)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (if (valp (t2-r)) (vcs2-step prog (t2-s1)) (t2-s1))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm throw2-hyps
  (implies (and (equal (car e) :throw) (s2-hyps e depth cenv self caps s env defs prog lc))
           (s2-hyps (cadr e) depth cenv self caps s env defs prog nil))
  :hints (("Goal" :do-not-induct t :expand ((x2wf e (len env) (lck lc)))
                  :use ((:instance throw2-code (code (car prog)) (pc (car s)))))))

(defthm throw2-part
  (implies (and (equal (car e) :throw) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good (cadr e) depth cenv self caps s env defs fuel prog nil))
           (and (s2-val (cadr e) s (t2-r) (t2-s1)) (s2-thr s (t2-r) (t2-s1)) (not (recurp (t2-r)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance throw2-hyps) (:instance s2good-gives (e (cadr e)) (lc nil))
                        (:instance (:definition s2-hyps) (e (cadr e)) (lc nil))
                        (:instance mx2-not-recur (e (cadr e)))))))

(defthm throw2-path-val
  (implies (and (equal (car e) :throw) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good (cadr e) depth cenv self caps s env defs fuel prog nil) (valp (t2-r)))
           (thrown-at s (cdr (t2-r)) (vcs2-step prog (t2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance throw2-part) (:instance (:definition s2-hyps))
                        (:instance s2-val-open (e (cadr e)) (r (t2-r)) (s2 (t2-s1)))
                        (:instance throw2-code (code (car prog)) (pc (car s)))
                        (:instance s2step-throw (s (t2-s1)))
                        (:instance cagree-nth (a (cadddr (t2-s1))) (b (update-nth (caddr s) (cdr (t2-r)) (cadddr s)))
                                   (h (1+ (caddr s))) (r (caddr s)))
                        (:instance unwind-thrown-at (s (t2-s1)) (v (cdr (t2-r))))
                        (:instance cagree-below-push (a (cadddr (t2-s1))) (b (cadddr s)) (sp (caddr s)) (v (cdr (t2-r))))
                        (:instance thrown-at-transfer (s1 (t2-s1)) (v (cdr (t2-r))) (s2 (vcs2-step prog (t2-s1))))))))

(defthm s2good-throw
  (implies (and (equal (car e) :throw) (s2good (cadr e) depth cenv self caps s env defs fuel prog nil))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-throw car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance throw2-part) (:instance throw2-path-val) (:instance throw2-clock)))))

; ---- a closure made, a recur, a primitive: arguments, then one instruction --------------

(defmacro m2-s1 () '(vcs2-run prog s (s2clk-args (cddr e) env caps defs fuel)))
(defmacro m2-rs () '(mx2-args (cddr e) env caps defs fuel))

(defthm mkclo2-code
  (implies (and (equal (car e) :mkclo) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile-args (cddr e) depth cenv self pc))
                (equal (nth (+ pc (s2code-len-args (cddr e))) code) (list :mkclo (cadr e) (len (cddr e))))
                (equal (s2code-len e) (+ (s2code-len-args (cddr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defthm x2wf-args-parts
  (implies (x2wf e n k)
           (and (implies (member-equal (car e) (quote (:mkclo :prim))) (x2wf-args (cddr e) n))
                (implies (equal (car e) :recur) (x2wf-args (cdr e) n))))
  :rule-classes nil)

(defthm mkclo2-args
  (implies (and (equal (car e) :mkclo) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog))
           (and (implies (valp (m2-rs))
                         (and (sstatep (m2-s1))
                              (equal (car (m2-s1)) (+ (car s) (s2code-len-args (cddr e))))
                              (equal (cadr (m2-s1)) (cadr s))
                              (equal (caddr (m2-s1)) (+ (caddr s) (len (cddr e))))
                              (equal (s-ctl (m2-s1)) (s-ctl s))
                              (cagree (cadddr (m2-s1)) (cadddr s) (caddr s))
                              (cvals-at (caddr s) (cdr (m2-rs)) (cadddr (m2-s1)))))
                (s2-thr s (m2-rs) (m2-s1))
                (not (recurp (m2-rs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2good-args s2-hyps) (l2-thy)) :do-not-induct t
                  :use ((:instance x2wf-args-parts (n (len env)) (k (lck lc)))
                        (:instance mkclo2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-not-recur (es (cddr e)))))))

(defthm mx2-mkclo
  (implies (equal (car e) :mkclo)
           (equal (mx2 e env caps defs fuel)
                  (if (valp (m2-rs)) (cons :val (clo (cadr e) (cdr (m2-rs)))) (m2-rs))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-mkclo))

(defthm mkclo2-clock
  (implies (equal (car e) :mkclo)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (if (valp (m2-rs)) (vcs2-step prog (m2-s1)) (m2-s1))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm mkclo2-path-val
  (implies (and (equal (car e) :mkclo) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog) (valp (m2-rs)))
           (s2-val e s (mx2 e env caps defs fuel) (vcs2-step prog (m2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (mx2-mkclo vcs2-step-old) (nth update-nth s2good-args mx2 mx2-args s2-hyps))
                  :do-not-induct t
                  :use ((:instance mkclo2-args) (:instance (:definition s2-hyps))
                        (:instance mkclo2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-val-shape (es (cddr e)))
                        (:instance cagree-write-at (n (caddr s)) (a (cadddr (m2-s1))) (b (cadddr s))
                                   (x (clo (cadr e) (cdr (m2-rs)))))
                        (:instance stk-from-vals (a (caddr s)) (vs (cdr (m2-rs))) (stk (cadddr (m2-s1))))))))

(defthm s2good-mkclo
  (implies (and (equal (car e) :mkclo) (s2good-args (cddr e) depth cenv self caps s env defs fuel prog))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-mkclo car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance mkclo2-args) (:instance mkclo2-path-val) (:instance mkclo2-clock)))))

(defmacro r2-s1 () '(vcs2-run prog s (s2clk-args (cdr e) env caps defs fuel)))
(defmacro r2-rs () '(mx2-args (cdr e) env caps defs fuel))

(defthm mx2-recur
  (implies (equal (car e) :recur)
           (equal (mx2 e env caps defs fuel)
                  (if (valp (r2-rs)) (cons :recur (cdr (r2-rs))) (r2-rs))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-recur))

(defthm recur2-code
  (implies (and (equal (car e) :recur) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile-args (cdr e) depth cenv self pc))
                (equal (car (nth (+ pc (s2code-len-args (cdr e))) code)) :recur)
                (equal (cadr (nth (+ pc (s2code-len-args (cdr e))) code)) (nfix (caddr lc)))
                (equal (caddr (nth (+ pc (s2code-len-args (cdr e))) code)) (nfix (cadr lc)))
                (equal (cadddr (nth (+ pc (s2code-len-args (cdr e))) code)) (nfix (car lc)))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc)))))

(defthm recur2-clock
  (implies (equal (car e) :recur)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (if (valp (r2-rs)) (vcs2-step prog (r2-s1)) (r2-s1))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm recur2-lc
  (implies (and (equal (car e) :recur) (s2-hyps e depth cenv self caps s env defs prog lc))
           (and (consp lc) (natp (car lc)) (natp (cadr lc)) (natp (caddr lc))
                (<= (+ (cadr lc) (caddr lc)) depth)
                (equal (len (cdr e)) (caddr lc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable x2wf) :expand ((x2wf e (len env) (lck lc))))))

(defthm recur2-args
  (implies (and (equal (car e) :recur) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cdr e) depth cenv self caps s env defs fuel prog))
           (and (implies (valp (r2-rs))
                         (and (sstatep (r2-s1))
                              (equal (car (r2-s1)) (+ (car s) (s2code-len-args (cdr e))))
                              (equal (cadr (r2-s1)) (cadr s))
                              (equal (caddr (r2-s1)) (+ (caddr s) (len (cdr e))))
                              (equal (s-ctl (r2-s1)) (s-ctl s))
                              (cagree (cadddr (r2-s1)) (cadddr s) (caddr s))
                              (cvals-at (caddr s) (cdr (r2-rs)) (cadddr (r2-s1)))))
                (s2-thr s (r2-rs) (r2-s1))
                (not (recurp (r2-rs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2good-args s2-hyps) (l2-thy)) :do-not-induct t
                  :use ((:instance x2wf-args-parts (n (len env)) (k (lck lc)))
                        (:instance recur2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-not-recur (es (cdr e)))))))

(defthm recur2-path-rec
  (implies (and (equal (car e) :recur) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cdr e) depth cenv self caps s env defs fuel prog) (valp (r2-rs)))
           (s2-rec s (cons :recur (cdr (r2-rs))) (vcs2-step prog (r2-s1)) lc))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-rec) (l2-thy)) :do-not-induct t
                  :use ((:instance recur2-lc) (:instance recur2-args)
                        (:instance (:definition s2-hyps))
                        (:instance recur2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-val-shape (es (cdr e)))
                        (:instance recur-step-abs (s1 (r2-s1)) (sp (caddr s)) (b (cadr lc)) (k (caddr lc)) (tgt (car lc))
                                   (stk0 (cadddr s)) (vs (cdr (r2-rs))))))))

(defthm s2good-recur
  (implies (and (equal (car e) :recur) (s2good-args (cdr e) depth cenv self caps s env defs fuel prog))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-recur car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance recur2-args) (:instance recur2-path-rec) (:instance recur2-clock)))))

(defmacro p2-a () '(prim (cadr e) (cdr (m2-rs))))

(defthm mx2-prim
  (implies (equal (car e) :prim)
           (equal (mx2 e env caps defs fuel)
                  (cond ((not (valp (m2-rs))) (m2-rs))
                        ((throwp (p2-a)) (cons :thrown (cdr (p2-a))))
                        (t (cons :val (p2-a))))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-prim))

(defthm prim2-code
  (implies (and (equal (car e) :prim) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile-args (cddr e) depth cenv self pc))
                (equal (nth (+ pc (s2code-len-args (cddr e))) code) (list :prim (cadr e) (len (cddr e))))
                (equal (s2code-len e) (+ (s2code-len-args (cddr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defthm prim2-clock
  (implies (equal (car e) :prim)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (if (valp (m2-rs)) (vcs2-step prog (m2-s1)) (m2-s1))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm prim2-args
  (implies (and (equal (car e) :prim) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog))
           (and (implies (valp (m2-rs))
                         (and (sstatep (m2-s1))
                              (equal (car (m2-s1)) (+ (car s) (s2code-len-args (cddr e))))
                              (equal (cadr (m2-s1)) (cadr s))
                              (equal (caddr (m2-s1)) (+ (caddr s) (len (cddr e))))
                              (equal (s-ctl (m2-s1)) (s-ctl s))
                              (cagree (cadddr (m2-s1)) (cadddr s) (caddr s))
                              (cvals-at (caddr s) (cdr (m2-rs)) (cadddr (m2-s1)))))
                (s2-thr s (m2-rs) (m2-s1))
                (not (recurp (m2-rs)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2good-args s2-hyps) (l2-thy)) :do-not-induct t
                  :use ((:instance x2wf-args-parts (n (len env)) (k (lck lc)))
                        (:instance prim2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-not-recur (es (cddr e)))))))

; the primitive's step, after its arguments: its operands the argument values
(defthm prim2-step
  (implies (and (equal (car e) :prim) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog) (valp (m2-rs)))
           (equal (vcs2-step prog (m2-s1))
                  (if (throwp (p2-a))
                      (unwind (cdr (p2-a)) (s-ctl (m2-s1)) (cadddr (m2-s1)))
                    (list (+ 1 (car s) (s2code-len-args (cddr e))) (cadr s) (1+ (caddr s))
                          (update-nth (caddr s) (p2-a) (cadddr (m2-s1))) (s-ctl s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2step-prim) (l2-thy)) :do-not-induct t
                  :use ((:instance prim2-args) (:instance (:definition s2-hyps))
                        (:instance prim2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-val-shape (es (cddr e)))
                        (:instance stk-from-vals (a (caddr s)) (vs (cdr (m2-rs))) (stk (cadddr (m2-s1))))))))

(defthm prim2-path-val
  (implies (and (equal (car e) :prim) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog) (valp (m2-rs)) (not (throwp (p2-a))))
           (s2-val e s (cons :val (p2-a)) (vcs2-step prog (m2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (l2-thy)) :do-not-induct t
                  :use ((:instance prim2-step) (:instance prim2-args) (:instance (:definition s2-hyps))
                        (:instance prim2-code (code (car prog)) (pc (car s)))
                        (:instance cagree-write-at (n (caddr s)) (a (cadddr (m2-s1))) (b (cadddr s)) (x (p2-a)))))))

(defthm prim2-path-thr
  (implies (and (equal (car e) :prim) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog) (valp (m2-rs)) (throwp (p2-a)))
           (thrown-at s (cdr (p2-a)) (vcs2-step prog (m2-s1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance prim2-step) (:instance prim2-args) (:instance (:definition s2-hyps))
                        (:instance unwind-thrown-at (s (m2-s1)) (v (cdr (p2-a))))
                        (:instance thrown-at-transfer (s1 (m2-s1)) (v (cdr (p2-a))) (s2 (vcs2-step prog (m2-s1))))))))

(defthm s2good-prim
  (implies (and (equal (car e) :prim) (s2good-args (cddr e) depth cenv self caps s env defs fuel prog))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-prim car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance prim2-args) (:instance prim2-path-val) (:instance prim2-path-thr) (:instance prim2-clock)))))

; ---- a try: the handler record pushed, the body, then popped -- or the handler ----------

(defthm vcs2-run-2 (equal (vcs2-run prog s 2) (vcs2-step prog (vcs2-step prog s)))
  :hints (("Goal" :use ((:instance vcs2-run-plus (a 1) (b 1))))))

(defmacro y2-lb () '(s2code-len (cadr e)))
(defmacro y2-lh () '(s2code-len (caddr e)))
(defmacro y2-h () '(+ (car s) 1 (y2-lb) 2))
(defmacro y2-rec () '(list :h (y2-h) (cadr s) depth))
(defmacro y2-s0 () '(list (1+ (car s)) (cadr s) (caddr s) (cadddr s) (cons (y2-rec) (s-ctl s))))
(defmacro y2-rb () '(mx2 (cadr e) env caps defs fuel))
(defmacro y2-sb () '(vcs2-run prog (y2-s0) (s2clk (cadr e) env caps defs fuel)))
(defmacro y2-env () '(append env (list (cdr (mx2 (cadr e) env caps defs fuel)))))
(defmacro y2-rh () '(mx2 (caddr e) (y2-env) caps defs fuel))
(defmacro y2-sh () '(vcs2-run prog (y2-sb) (s2clk (caddr e) (y2-env) caps defs fuel)))

(defthm mx2-try
  (implies (equal (car e) :try)
           (equal (mx2 e env caps defs fuel) (if (thrownp (y2-rb)) (y2-rh) (y2-rb))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-try))

(defthm ccode-at-one
  (equal (ccode-at code pc (list x)) (equal (nth pc code) x))
  :hints (("Goal" :in-theory (enable ccode-at))))

(defthm try2-code
  (implies (and (equal (car e) :try) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (equal (nth pc code) (list :try (+ pc 1 (y2-lb) 2) depth))
                (ccode-at code (1+ pc) (vcs2-compile (cadr e) depth cenv self (1+ pc) nil))
                (equal (nth (+ pc 1 (y2-lb)) code) (list :endtry)) (equal (car (nth (+ pc 1 (y2-lb)) code)) :endtry)
                (equal (nth (+ pc 2 (y2-lb)) code) (list :jmp (+ pc 3 (y2-lb) (y2-lh) 1)))
                (ccode-at code (+ pc 1 (y2-lb) 2)
                          (vcs2-compile (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc 1 (y2-lb) 2) nil))
                (equal (nth (+ pc 3 (y2-lb) (y2-lh)) code) (list :slide))
                (equal (s2code-len e) (+ 1 (y2-lb) 2 (y2-lh) 1))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defthm try2-ins
  (implies (and (equal (car e) :try) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (equal (car (nth pc code)) :try) (equal (cadr (nth pc code)) (+ pc 1 (y2-lb) 2))
                (equal (caddr (nth pc code)) depth)))
  :rule-classes nil
  :hints (("Goal" :use try2-code :in-theory (disable vcs2-compile s2code-len))))

(defthm try2-s0
  (implies (and (equal (car e) :try) (s2-hyps e depth cenv self caps s env defs prog lc))
           (equal (vcs2-step prog s) (y2-s0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (quote (s2-hyps)) (l2-thy)) :do-not-induct t
                  :use ((:instance try2-ins (code (car prog)) (pc (car s))) (:instance s2step-try)))))

; the clock from any state after the try's step, then from the one it is
(defthm try2-clock-gen
  (implies (and (equal (car e) :try) (equal (vcs2-step prog s) s0))
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (let ((sb (vcs2-run prog s0 (s2clk (cadr e) env caps defs fuel))))
                    (cond ((valp (y2-rb)) (vcs2-step prog (vcs2-step prog sb)))
                          ((thrownp (y2-rb))
                           (if (valp (y2-rh))
                               (vcs2-step prog (vcs2-run prog sb (s2clk (caddr e) (y2-env) caps defs fuel)))
                             (vcs2-run prog sb (s2clk (caddr e) (y2-env) caps defs fuel))))
                          (t sb)))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm try2-clock
  (implies (and (equal (car e) :try) (s2-hyps e depth cenv self caps s env defs prog lc))
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (cond ((valp (y2-rb)) (vcs2-step prog (vcs2-step prog (y2-sb))))
                        ((thrownp (y2-rb)) (if (valp (y2-rh)) (vcs2-step prog (y2-sh)) (y2-sh)))
                        (t (y2-sb)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory) :do-not-induct t
                  :use ((:instance try2-s0) (:instance try2-clock-gen (s0 (y2-s0)))))))

(defthm try2-hyps-body
  (implies (and (equal (car e) :try) (s2-hyps e depth cenv self caps s env defs prog lc))
           (s2-hyps (cadr e) depth cenv self caps (y2-s0) env defs prog nil))
  :hints (("Goal" :do-not-induct t :expand ((x2wf e (len env) (lck lc)))
                  :in-theory (disable vcs2-step)
                  :use ((:instance try2-code (code (car prog)) (pc (car s)))))))

(defthm try2-hyps-handler
  (implies (and (equal (car e) :try) (s2-hyps e depth cenv self caps s env defs prog lc)
                (sstatep s1) (equal (car s1) (y2-h)) (equal (cadr s1) (cadr s)) (equal (caddr s1) (1+ (caddr s)))
                (equal (s-ctl s1) (s-ctl s)) (cagree (cadddr s1) (update-nth (caddr s) v (cadddr s)) (1+ (caddr s))))
           (s2-hyps (caddr e) (1+ depth) (append cenv (list depth)) self caps s1 (append env (list v)) defs prog nil))
  :hints (("Goal" :expand ((x2wf e (len env) (lck lc))) :do-not-induct t
                  :in-theory (disable cenv-ok cself-ok cenv-ok-after-run cself-ok-after-run)
                  :use ((:instance try2-code (code (car prog)) (pc (car s)))
                        (:instance handlers-ok-bigger (ctl (s-ctl s)) (sp (caddr s)) (sp2 (caddr s1)))
                        (:instance cenv-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cself-ok-after-run (regs (cadddr s)) (regs1 (cadddr s1)) (fb (cadr s)) (f depth)
                                   (g (caddr s)) (h (1+ (caddr s))) (k (1+ depth)))
                        (:instance cagree-nth (a (cadddr s1)) (b (update-nth (caddr s) v (cadddr s)))
                                   (h (caddr s1)) (r (caddr s)))))))

(defmacro try2-hyps ()
  '(and (equal (car e) :try) (s2-hyps e depth cenv self caps s env defs prog lc)
        (s2good (cadr e) depth cenv self caps (y2-s0) env defs fuel prog nil)))

(defthm try2-body
  (implies (try2-hyps)
           (and (s2-val (cadr e) (y2-s0) (y2-rb) (y2-sb)) (s2-thr (y2-s0) (y2-rb) (y2-sb)) (not (recurp (y2-rb)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance try2-hyps-body) (:instance s2good-gives (e (cadr e)) (s (y2-s0)) (lc nil))
                        (:instance (:definition s2-hyps) (e (cadr e)) (s (y2-s0)) (lc nil))
                        (:instance mx2-not-recur (e (cadr e)))))))

; a jump, over plain states, stated by component
(defthm jmp2-step-parts
  (implies (and (sstatep s2) (equal (nth (car s2) (car prog)) (list :jmp tgt)) (natp tgt))
           (let ((s3 (vcs2-step prog s2)))
             (and (sstatep s3) (equal (car s3) tgt) (equal (cadr s3) (cadr s2)) (equal (caddr s3) (caddr s2))
                  (equal (cadddr s3) (cadddr s2)) (equal (s-ctl s3) (s-ctl s2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable nth update-nth) :use ((:instance jmp-step-abs) (:instance vcs2-step-old (s s2))))))

; THE BODY A VALUE: the record popped, and a jump past the handler
(defthm try2-path-val
  (implies (and (try2-hyps) (valp (y2-rb)))
           (s2-val e s (y2-rb) (vcs2-step prog (vcs2-step prog (y2-sb)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val s2step-endtry) (l2-thy)) :do-not-induct t
                  :use ((:instance try2-body) (:instance (:definition s2-hyps))
                        (:instance try2-code (code (car prog)) (pc (car s)))
                        (:instance s2-val-open (e (cadr e)) (s (y2-s0)) (r (y2-rb)) (s2 (y2-sb)))
                        (:instance jmp2-step-parts
                                   (s2 (list (+ (car s) 2 (y2-lb)) (cadr s) (1+ (caddr s)) (cadddr (y2-sb)) (s-ctl s)))
                                   (tgt (+ (car s) 3 (y2-lb) (y2-lh) 1)))))))

; THE BODY THROWS: at the handler, its record gone, the value its local
(defthm try2-at-handler
  (implies (and (try2-hyps) (thrownp (y2-rb)))
           (and (sstatep (y2-sb)) (equal (car (y2-sb)) (y2-h)) (equal (cadr (y2-sb)) (cadr s))
                (equal (caddr (y2-sb)) (1+ (caddr s))) (equal (s-ctl (y2-sb)) (s-ctl s))
                (cagree (cadddr (y2-sb)) (update-nth (caddr s) (cdr (y2-rb)) (cadddr s)) (1+ (caddr s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-thr thrown-at hfind) (l2-thy)) :do-not-induct t
                  :use ((:instance try2-body) (:instance (:definition s2-hyps))))))

(defmacro try2-hhyps ()
  '(and (try2-hyps) (thrownp (y2-rb))
        (s2good (caddr e) (1+ depth) (append cenv (list depth)) self caps (y2-sb) (y2-env) defs fuel prog nil)))

(defthm try2-handler
  (implies (try2-hhyps)
           (and (s2-val (caddr e) (y2-sb) (y2-rh) (y2-sh)) (s2-thr (y2-sb) (y2-rh) (y2-sh)) (not (recurp (y2-rh)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance try2-at-handler)
                        (:instance try2-hyps-handler (s1 (y2-sb)) (v (cdr (y2-rb))))
                        (:instance s2good-gives (e (caddr e)) (depth (1+ depth)) (cenv (append cenv (list depth)))
                                   (s (y2-sb)) (env (y2-env)) (lc nil))
                        (:instance (:definition s2-hyps) (e (caddr e)) (depth (1+ depth)) (cenv (append cenv (list depth)))
                                   (s (y2-sb)) (env (y2-env)) (lc nil))
                        (:instance mx2-not-recur (e (caddr e)) (env (y2-env)))))))

(defthm try2-path-handler-val
  (implies (and (try2-hhyps) (valp (y2-rh)))
           (s2-val e s (y2-rh) (vcs2-step prog (y2-sh))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (l2-thy)) :do-not-induct t
                  :use ((:instance try2-at-handler) (:instance try2-handler) (:instance (:definition s2-hyps))
                        (:instance try2-code (code (car prog)) (pc (car s)))
                        (:instance s2-val-open (e (caddr e)) (s (y2-sb)) (r (y2-rh)) (s2 (y2-sh)))
                        (:instance slide-step-abs (sp (caddr s)) (s1 (y2-sb)) (s2 (y2-sh))
                                   (va (cdr (y2-rb))) (vb (cdr (y2-rh))))))))

(defthm try2-path-handler-thr
  (implies (and (try2-hhyps) (thrownp (y2-rh)))
           (thrown-at s (cdr (y2-rh)) (y2-sh)))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance try2-at-handler) (:instance try2-handler) (:instance (:definition s2-hyps))
                        (:instance s2-thr-open (s (y2-sb)) (r (y2-rh)) (s2 (y2-sh)))
                        (:instance cagree-below-push (a (cadddr (y2-sb))) (b (cadddr s)) (sp (caddr s)) (v (cdr (y2-rb))))
                        (:instance thrown-at-transfer (s1 (y2-sb)) (v (cdr (y2-rh))) (s2 (y2-sh)))))))

(defthm s2good-try
  (implies (and (equal (car e) :try)
                (s2good (cadr e) depth cenv self caps (y2-s0) env defs fuel prog nil)
                (s2good (caddr e) (1+ depth) (append cenv (list depth)) self caps (y2-sb) (y2-env) defs fuel prog nil))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-try)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance try2-body) (:instance try2-path-val) (:instance try2-handler)
                        (:instance try2-path-handler-val) (:instance try2-path-handler-thr)
                        (:instance try2-clock)))))

; ---- a throw seen from further down: only the stack below a bound matters ---------------

(defthm thrown-at-transfer-h
  (implies (and (thrown-at s1 v s2) (equal (s-ctl s1) (s-ctl s))
                (handlers-ok (s-ctl s) h) (natp h)
                (cagree (cadddr s1) (cadddr s) h))
           (thrown-at s v s2))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable cagree-trans cagree-same-write cagree-smaller handlers-ok-hfind)
                  :use ((:instance handlers-ok-hfind (ctl (s-ctl s)) (sp h))
                        (:instance cagree-smaller (a (cadddr s1)) (b (cadddr s)) (h h)
                                   (g (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-same-write (a (cadddr s1)) (b (cadddr s))
                                   (d (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s)))))))
                                   (h (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-write-at (a (cadddr s1)) (b (cadddr s)) (x v)
                                   (n (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-trans (a (cadddr s2))
                                   (b (update-nth (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))
                                                  v (cadddr s1)))
                                   (c (update-nth (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))
                                                  v (cadddr s)))
                                   (h (+ 1 (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))))))

; ---- the loop's slides ------------------------------------------------------------------

(defun slides2-ind (prog s2 k base)
  (if (zp k) (list s2 base) (slides2-ind prog (vcs2-step prog s2) (1- k) base)))

(defthm slides2-run
  (implies (and (sstatep s2) (natp k) (natp base) (ccode-at (car prog) (car s2) (slides k))
                (equal (caddr s2) (+ base k 1)))
           (let ((s3 (vcs2-run prog s2 k)))
             (and (sstatep s3) (equal (car s3) (+ (car s2) k)) (equal (cadr s3) (cadr s2))
                  (equal (caddr s3) (1+ base)) (equal (s-ctl s3) (s-ctl s2))
                  (equal (nth base (cadddr s3)) (nth (+ base k) (cadddr s2)))
                  (cagree (cadddr s3) (cadddr s2) base))))
  :hints (("Goal" :induct (slides2-ind prog s2 k base)
                  :in-theory (e/d (vcs2-run) (nth update-nth))
                  :expand ((vcs2-run prog s2 k)))
          ("Subgoal *1/2" :use ((:instance ccode-at-slides (code (car prog)) (pc (car s2)))
                                (:instance cagree-trans (a (cadddr (vcs2-run prog (vcs2-step prog s2) (1- k))))
                                           (b (cadddr (vcs2-step prog s2))) (c (cadddr s2)) (h base))))))

; ---- THE LOOP'S ITERATIONS -----------------------------------------------------------------

(defmacro lp2-cenv () '(append cenv (count-from depth (+ depth (len (cadr e))))))
(defmacro lp2-lc () '(list (car s) depth (len (cadr e))))
(defmacro lp2-rb () '(mx2 (caddr e) (append env vs) caps defs fuel))
(defmacro lp2-s2 () '(vcs2-run prog s (s2clk (caddr e) (append env vs) caps defs fuel)))

(defun loopit2-hyps (e depth cenv self caps s env vs defs prog)
  (and (equal (car e) :loop) (consp e)
       (sstatep s) (natp depth) (equal (len vs) (len (cadr e)))
       (equal (caddr s) (+ (cadr s) depth (len (cadr e))))
       (ccode-at (car prog) (car s) (vcs2-compile (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self (car s) (lp2-lc)))
       (x2wf (caddr e) (+ (len env) (len (cadr e))) (len (cadr e)))
       (cenv-ok cenv env (cadddr s) (cadr s) depth)
       (cself-ok self caps (cadddr s) (cadr s) depth)
       (cvals-at (+ (cadr s) depth) vs (cadddr s))
       (x2defs-ok defs) (s2fns-ok prog defs)
       (handlers-ok (s-ctl s) (+ (cadr s) depth))))

(defun s2good-loopit (e depth cenv self caps s env vs defs fuel prog)
  (implies (loopit2-hyps e depth cenv self caps s env vs defs prog)
           (let ((r (mx2-loop e env vs caps defs fuel)) (s2 (vcs2-run prog s (s2clk-loop e env vs caps defs fuel))))
             (and (implies (valp r)
                           (and (sstatep s2)
                                (equal (car s2) (+ (car s) (s2code-len (caddr e))))
                                (equal (cadr s2) (cadr s))
                                (equal (caddr s2) (+ 1 (caddr s)))
                                (equal (s-ctl s2) (s-ctl s))
                                (cagree (cadddr s2) (cadddr s) (+ (cadr s) depth))
                                (equal (nth (caddr s) (cadddr s2)) (cdr r))))
                  (s2-thr s r s2)))))

(defthm mx2-loop-open
  (implies (consp e)
           (equal (mx2-loop e base vs caps defs fuel)
                  (let ((r (mx2 (caddr e) (append base vs) caps defs fuel)))
                    (cond ((not (equal (car r) :recur)) r)
                          ((zp fuel) (list :out))
                          (t (mx2-loop e base (cdr r) caps defs (1- fuel)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((mx2-loop e base vs caps defs fuel)))))

(defthm s2clk-loop-open
  (implies (consp e)
           (equal (s2clk-loop e base vs caps defs fuel)
                  (if (and (recurp (mx2 (caddr e) (append base vs) caps defs fuel)) (not (zp fuel)))
                      (c+ (s2clk (caddr e) (append base vs) caps defs fuel)
                          (s2clk-loop e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel)))
                    (s2clk (caddr e) (append base vs) caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk-loop e base vs caps defs fuel)) :in-theory (disable c+ recurp))))

(defthm loopit2-body-hyps
  (implies (loopit2-hyps e depth cenv self caps s env vs defs prog)
           (s2-hyps (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs prog (lp2-lc)))
  :hints (("Goal" :in-theory (disable cenv-ok cself-ok cenv-ok-count-from cenv-ok-bigger-f cself-ok-bigger-f)
                  :use ((:instance cenv-ok-count-from (i depth) (n (+ depth (len (cadr e)))) (base (cadr s))
                                   (regs (cadddr s)) (g (+ depth (len (cadr e)))))
                        (:instance cenv-ok-bigger-f (regs (cadddr s)) (fb (cadr s)) (f depth) (g (+ depth (len (cadr e)))))
                        (:instance cself-ok-bigger-f (regs (cadddr s)) (fb (cadr s)) (f depth) (g (+ depth (len (cadr e)))))
                        (:instance cenv-ok-len (regs (cadddr s)) (fb (cadr s)) (f depth))
                        (:instance handlers-ok-bigger (ctl (s-ctl s)) (sp (+ (cadr s) depth)) (sp2 (caddr s)))))))

(defmacro loopit2-thy () '(union-theories '(loopit2-hyps) (l2-thy)))

(defthm loopit2-body
  (implies (and (loopit2-hyps e depth cenv self caps s env vs defs prog)
                (s2good (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs fuel prog (lp2-lc)))
           (and (s2-val (caddr e) s (lp2-rb) (lp2-s2)) (s2-rec s (lp2-rb) (lp2-s2) (lp2-lc)) (s2-thr s (lp2-rb) (lp2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (loopit2-thy) :do-not-induct t
                  :use ((:instance loopit2-body-hyps)
                        (:instance s2good-gives (e (caddr e)) (depth (+ depth (len (cadr e)))) (cenv (lp2-cenv))
                                   (env (append env vs)) (lc (lp2-lc)))))))

(defthm loopit2-path-val
  (implies (and (loopit2-hyps e depth cenv self caps s env vs defs prog)
                (s2good (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs fuel prog (lp2-lc))
                (valp (lp2-rb)))
           (and (sstatep (lp2-s2))
                (equal (car (lp2-s2)) (+ (car s) (s2code-len (caddr e))))
                (equal (cadr (lp2-s2)) (cadr s))
                (equal (caddr (lp2-s2)) (+ 1 (caddr s)))
                (equal (s-ctl (lp2-s2)) (s-ctl s))
                (cagree (cadddr (lp2-s2)) (cadddr s) (+ (cadr s) depth))
                (equal (nth (caddr s) (cadddr (lp2-s2))) (cdr (lp2-rb)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (loopit2-thy) :do-not-induct t
                  :use ((:instance loopit2-body)
                        (:instance s2-val-open (e (caddr e)) (r (lp2-rb)) (s2 (lp2-s2)))
                        (:instance cagree-past-write (a (cadddr (lp2-s2))) (b (cadddr s)) (g (caddr s)) (w (cdr (lp2-rb)))
                                   (h (1+ (caddr s))) (f (+ (cadr s) depth)))
                        (:instance cagree-nth (a (cadddr (lp2-s2))) (b (update-nth (caddr s) (cdr (lp2-rb)) (cadddr s)))
                                   (h (1+ (caddr s))) (r (caddr s)))))))

(defthm loopit2-path-rec
  (implies (and (loopit2-hyps e depth cenv self caps s env vs defs prog)
                (s2good (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs fuel prog (lp2-lc))
                (recurp (lp2-rb)))
           (and (loopit2-hyps e depth cenv self caps (lp2-s2) env (cdr (lp2-rb)) defs prog)
                (equal (car (lp2-s2)) (car s)) (equal (cadr (lp2-s2)) (cadr s))
                (equal (caddr (lp2-s2)) (caddr s)) (equal (s-ctl (lp2-s2)) (s-ctl s))
                (cagree (cadddr (lp2-s2)) (cadddr s) (+ (cadr s) depth))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(cenv-ok-agree cself-ok-agree) (loopit2-thy)) :do-not-induct t
                  :use ((:instance loopit2-body)
                        (:instance s2-rec-open (r (lp2-rb)) (s2 (lp2-s2)) (lc (lp2-lc)))
                        (:instance cagree-sym (a (cadddr (lp2-s2))) (b (cadddr s)) (h (+ (cadr s) depth)))))))

(defmacro lp2-s3 () '(vcs2-run prog (lp2-s2) (s2clk-loop e env (cdr (lp2-rb)) caps defs (1- fuel))))

; a later iteration's throw, seen from this one
(defthm loopit2-later-thr
  (implies (and (loopit2-hyps e depth cenv self caps s env vs defs prog)
                (s2good (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs fuel prog (lp2-lc))
                (recurp (lp2-rb))
                (thrown-at (lp2-s2) v s3))
           (thrown-at s v s3))
  :rule-classes nil
  :hints (("Goal" :in-theory (loopit2-thy) :do-not-induct t
                  :use ((:instance loopit2-path-rec)
                        (:instance thrown-at-transfer-h (s1 (lp2-s2)) (s2 s3) (h (+ (cadr s) depth)))))))

(defthm s2good-loopit-step
  (implies (and (consp e)
                (s2good (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs fuel prog (lp2-lc))
                (implies (and (recurp (lp2-rb)) (not (zp fuel)))
                         (s2good-loopit e depth cenv self caps (lp2-s2) env (cdr (lp2-rb)) defs (1- fuel) prog)))
           (s2good-loopit e depth cenv self caps s env vs defs fuel prog))
  :hints (("Goal" :in-theory (union-theories '(s2good-loopit s2-thr vcs2-run-c+ (:type-prescription s2clk) (:type-prescription s2clk-loop))
                                             (loopit2-thy))
                  :do-not-induct t
                  :cases ((valp (lp2-rb)) (thrownp (lp2-rb)) (and (recurp (lp2-rb)) (not (zp fuel))))
                  :use ((:instance loopit2-path-val)
                        (:instance loopit2-path-rec)
                        (:instance loopit2-body)
                        (:instance loopit2-later-thr (v (cdr (mx2-loop e env (cdr (lp2-rb)) caps defs (1- fuel)))) (s3 (lp2-s3)))
                        (:instance mx2-loop-open (base env))
                        (:instance s2clk-loop-open (base env))
                        (:instance cagree-trans (a (cadddr (lp2-s3))) (b (cadddr (lp2-s2))) (c (cadddr s))
                                   (h (+ (cadr s) depth)))))))

; ---- THE LOOP --------------------------------------------------------------------------------

(defmacro lq-ri () '(mx2-args (cadr e) env caps defs fuel))
(defmacro lq-vs () '(cdr (mx2-args (cadr e) env caps defs fuel)))
(defmacro lq-s1 () '(vcs2-run prog s (s2clk-args (cadr e) env caps defs fuel)))
(defmacro lq-r () '(mx2-loop e env (lq-vs) caps defs fuel))
(defmacro lq-s2 () '(vcs2-run prog (lq-s1) (s2clk-loop e env (lq-vs) caps defs fuel)))
(defmacro lq-head () '(+ pc (s2code-len-args (cadr e))))

(defthm loop2-code
  (implies (and (equal (car e) :loop) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile-args (cadr e) depth cenv self pc))
                (ccode-at code (lq-head)
                          (vcs2-compile (caddr e) (+ depth (len (cadr e))) (append cenv (count-from depth (+ depth (len (cadr e)))))
                                        self (lq-head) (list (lq-head) depth (len (cadr e)))))
                (ccode-at code (+ (lq-head) (s2code-len (caddr e))) (slides (len (cadr e))))
                (equal (s2code-len e) (+ (s2code-len-args (cadr e)) (s2code-len (caddr e)) (len (cadr e))))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

(defthm mx2-loop-expr
  (implies (equal (car e) :loop)
           (equal (mx2 e env caps defs fuel) (if (valp (lq-ri)) (lq-r) (lq-ri))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)))))
(in-theory (disable mx2-loop-expr))

(defthm loop2-clock
  (implies (equal (car e) :loop)
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (cond ((not (valp (lq-ri))) (lq-s1))
                        ((valp (lq-r)) (vcs2-run prog (lq-s2) (len (cadr e))))
                        (t (lq-s2)))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (disable c+))))

(defthm x2wf-loop-parts
  (implies (and (equal (car e) :loop) (x2wf e n k))
           (and (x2wf-args (cadr e) n) (consp (cadr e)) (true-listp (cadr e))))
  :rule-classes nil)

(defthm loop2-args
  (implies (and (equal (car e) :loop) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cadr e) depth cenv self caps s env defs fuel prog))
           (and (implies (valp (lq-ri))
                         (and (sstatep (lq-s1))
                              (equal (car (lq-s1)) (+ (car s) (s2code-len-args (cadr e))))
                              (equal (cadr (lq-s1)) (cadr s))
                              (equal (caddr (lq-s1)) (+ (caddr s) (len (cadr e))))
                              (equal (s-ctl (lq-s1)) (s-ctl s))
                              (cagree (cadddr (lq-s1)) (cadddr s) (caddr s))
                              (cvals-at (caddr s) (lq-vs) (cadddr (lq-s1)))))
                (s2-thr s (lq-ri) (lq-s1))
                (not (recurp (lq-ri)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2good-args s2-hyps) (l2-thy)) :do-not-induct t
                  :use ((:instance x2wf-loop-parts (n (len env)) (k (lck lc)))
                        (:instance loop2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-not-recur (es (cadr e)))))))

(defthm loop2-iter-hyps
  (implies (and (equal (car e) :loop) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cadr e) depth cenv self caps s env defs fuel prog) (valp (lq-ri)))
           (loopit2-hyps e depth cenv self caps (lq-s1) env (lq-vs) defs prog))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable cenv-ok cself-ok mx2-args s2good-args)
                  :expand ((x2wf e (len env) (lck lc)))
                  :use ((:instance loop2-args)
                        (:instance loop2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-val-shape (es (cadr e)))
                        (:instance cenv-ok-agree (a (cadddr s)) (b (cadddr (lq-s1))) (fb (cadr s)) (f depth))
                        (:instance cself-ok-agree (a (cadddr s)) (b (cadddr (lq-s1))) (fb (cadr s)) (f depth))
                        (:instance cagree-sym (a (cadddr (lq-s1))) (b (cadddr s)) (h (caddr s)))))))

(defthm loop2-path-val
  (implies (and (equal (car e) :loop) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cadr e) depth cenv self caps s env defs fuel prog)
                (s2good-loopit e depth cenv self caps (lq-s1) env (lq-vs) defs fuel prog)
                (valp (lq-ri)) (valp (lq-r)))
           (s2-val e s (lq-r) (vcs2-run prog (lq-s2) (len (cadr e)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val s2good-loopit s2-hyps) (l2-thy)) :do-not-induct t
                  :use ((:instance loop2-iter-hyps) (:instance loop2-args)
                        (:instance loop2-code (code (car prog)) (pc (car s)))
                        (:instance slides2-run (s2 (lq-s2)) (k (len (cadr e))) (base (caddr s)))
                        (:instance cagree-trans (a (cadddr (vcs2-run prog (lq-s2) (len (cadr e))))) (b (cadddr (lq-s2)))
                                   (c (cadddr (lq-s1))) (h (caddr s)))
                        (:instance cagree-trans (a (cadddr (vcs2-run prog (lq-s2) (len (cadr e))))) (b (cadddr (lq-s1)))
                                   (c (cadddr s)) (h (caddr s)))
                        (:instance cagree-extend (a (cadddr (vcs2-run prog (lq-s2) (len (cadr e))))) (b (cadddr s))
                                   (n (caddr s)) (v (cdr (lq-r))))))))

(defthm loop2-path-thr
  (implies (and (equal (car e) :loop) (s2-hyps e depth cenv self caps s env defs prog lc)
                (s2good-args (cadr e) depth cenv self caps s env defs fuel prog)
                (s2good-loopit e depth cenv self caps (lq-s1) env (lq-vs) defs fuel prog)
                (valp (lq-ri)) (thrownp (lq-r)))
           (thrown-at s (cdr (lq-r)) (lq-s2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-thr s2good-loopit s2-hyps) (l2-thy)) :do-not-induct t
                  :use ((:instance loop2-iter-hyps) (:instance loop2-args)
                        (:instance thrown-at-transfer-h (s1 (lq-s1)) (v (cdr (lq-r))) (s2 (lq-s2)) (h (caddr s)))))))

(defthm s2good-loop
  (implies (and (equal (car e) :loop)
                (s2good-args (cadr e) depth cenv self caps s env defs fuel prog)
                (s2good-loopit e depth cenv self caps (lq-s1) env (lq-vs) defs fuel prog))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-loop-expr)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance loop2-args) (:instance loop2-path-val) (:instance loop2-path-thr) (:instance loop2-clock)
                        (:instance mx2-loop-not-recur (base env) (vs (lq-vs)))))))

; ---- THE CALL ---------------------------------------------------------------------------------
;
; a throw from inside a call: the call's record is passed over, so a
; state whose control stack has the same nearest handler sees it the same
(defthm thrown-at-transfer-hf
  (implies (and (thrown-at s1 v s2) (equal (hfind (s-ctl s1)) (hfind (s-ctl s)))
                (handlers-ok (s-ctl s) h) (natp h)
                (cagree (cadddr s1) (cadddr s) h))
           (thrown-at s v s2))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable cagree-trans cagree-same-write cagree-smaller handlers-ok-hfind)
                  :use ((:instance handlers-ok-hfind (ctl (s-ctl s)) (sp h))
                        (:instance cagree-smaller (a (cadddr s1)) (b (cadddr s)) (h h)
                                   (g (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-same-write (a (cadddr s1)) (b (cadddr s))
                                   (d (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s)))))))
                                   (h (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-write-at (a (cadddr s1)) (b (cadddr s)) (x v)
                                   (n (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))
                        (:instance cagree-trans (a (cadddr s2))
                                   (b (update-nth (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))
                                                  v (cadddr s1)))
                                   (c (update-nth (+ (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))
                                                  v (cadddr s)))
                                   (h (+ 1 (nfix (caddr (car (hfind (s-ctl s))))) (nfix (cadddr (car (hfind (s-ctl s))))))))))))

; a call record has no handler in it
(defthm handlers-ok-call-record
  (implies (not (equal x :h)) (equal (handlers-ok (cons (cons x r) ctl) sp) (handlers-ok ctl sp))))

; a variadic call's frame: the first n0 values where they were, the
; rest packed into one list in the slot after them, the closure above
(defun srf-ind (k n0 vs) (if (zp n0) (list k vs) (srf-ind (1+ k) (1- n0) (cdr vs))))

(defthm split-rest-cons
  (implies (and (not (zp n0)) (consp vs))
           (equal (split-rest n0 vs) (cons (car vs) (split-rest (1- n0) (cdr vs))))))

(defthm split-rest-0 (equal (split-rest 0 vs) (list vs)))

(defthm rest-frame-vals
  (implies (and (natp k) (natp n0) (<= n0 (len vs)) (true-listp vs) (cvals-at k vs stk))
           (cvals-at k (split-rest n0 vs)
                     (update-nth (+ k n0 1) c (update-nth (+ k n0) (stk-from (+ k n0) (- (len vs) n0) stk) stk))))
  :hints (("Goal" :induct (srf-ind k n0 vs) :in-theory (disable split-rest stk-from nth update-nth))
          ("Subgoal *1/1" :use ((:instance stk-from-vals (a k))))))

(defthm mx2-args-len
  (implies (equal (car (mx2-args es env caps defs fuel)) :val)
           (equal (len (cdr (mx2-args es env caps defs fuel))) (len es)))
  :hints (("Goal" :use mx2-args-val-shape)))
(in-theory (disable mx2-args-len))

(defmacro c2-thy () '(union-theories '(mx2-args-len) (l2-thy)))

(defmacro c2-n () '(len (cddr e)))
(defmacro c2-ra () '(mx2-args (cddr e) env caps defs fuel))
(defmacro c2-vs () '(cdr (mx2-args (cddr e) env caps defs fuel)))
(defmacro c2-s1 () '(vcs2-run prog s (s2clk-args (cddr e) env caps defs fuel)))
(defmacro c2-rf () '(mx2 (cadr e) env caps defs fuel))
(defmacro c2-c () '(cdr (mx2 (cadr e) env caps defs fuel)))
(defmacro c2-s2 () '(vcs2-run prog (c2-s1) (s2clk (cadr e) env caps defs fuel)))
(defmacro c2-cls () '(cdr (assoc-equal (clo-f (c2-c)) defs)))
(defmacro c2-ents () '(cdr (assoc-equal (clo-f (c2-c)) (cdr prog))))
(defmacro c2-cl () '(pick-arity (c2-cls) (len (c2-vs))))
(defmacro c2-en () '(pick-arity (c2-ents) (len (c2-vs))))
(defmacro c2-n0 () '(nfix (car (c2-cl))))
(defmacro c2-nl () '(call-nl (c2-cl)))
(defmacro c2-benv () '(call-benv (c2-cl) (c2-vs)))
(defmacro c2-pc2 () '(+ (car s) (s2code-len-args (cddr e)) (s2code-len (cadr e))))
(defmacro c2-crec () '(list (1+ (c2-pc2)) (cadr s)))
; the callee's locals, how many, and the frame the call makes: named, so
; the clause's kind is one case split where it matters and none elsewhere
(defun call-nl (cl) (if (restp cl) (1+ (nfix (car cl))) (nfix (car cl))))
(defun call-benv (cl vs) (if (restp cl) (split-rest (nfix (car cl)) vs) vs))
(defun call-frame (cl en c n sp stk crec ctl)
  (if (restp cl)
      (list (nfix (cadr en)) sp (+ sp (nfix (car cl)) 2)
            (update-nth (+ sp (nfix (car cl)) 1) c
                        (update-nth (+ sp (nfix (car cl))) (stk-from (+ sp (nfix (car cl))) (- n (nfix (car cl))) stk) stk))
            (cons crec ctl))
    (list (nfix (cadr en)) sp (+ sp n 1) stk (cons crec ctl))))
(in-theory (disable call-nl call-benv call-frame))

(defmacro c2-s3 () '(call-frame (c2-cl) (c2-en) (c2-c) (c2-n) (caddr s) (cadddr (c2-s2)) (c2-crec) (s-ctl s)))
(defmacro c2-bclk () '(s2clk (cadr (c2-cl)) (c2-benv) (clo-caps (c2-c)) defs (1- fuel)))
(defmacro c2-r () '(mx2 (cadr (c2-cl)) (c2-benv) (clo-caps (c2-c)) defs (1- fuel)))
(defmacro c2-s4 () '(vcs2-run prog (c2-s3) (c2-bclk)))

(defthm mx2-callv
  (implies (equal (car e) :callv)
           (equal (mx2 e env caps defs fuel)
                  (cond ((not (valp (c2-ra))) (c2-ra))
                        ((not (valp (c2-rf))) (c2-rf))
                        ((not (clop (c2-c)))
                         (let ((a (prim :invoke (cons (c2-c) (c2-vs)))))
                           (if (throwp a) (cons :thrown (cdr a)) (cons :val a))))
                        ((not (consp (c2-cl))) (cons :thrown :arity))
                        ((zp fuel) (list :out))
                        (t (c2-r)))))
  :hints (("Goal" :expand ((mx2 e env caps defs fuel)) :in-theory (e/d (call-benv) (pick-arity split-rest)))))
(in-theory (disable mx2-callv))

(defthm callv2-code
  (implies (and (equal (car e) :callv) (ccode-at code pc (vcs2-compile e depth cenv self pc lc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile-args (cddr e) depth cenv self pc))
                (ccode-at code (+ pc (s2code-len-args (cddr e)))
                          (vcs2-compile (cadr e) (+ depth (c2-n)) cenv self (+ pc (s2code-len-args (cddr e))) nil))
                (equal (car (nth (+ pc (s2code-len-args (cddr e)) (s2code-len (cadr e))) code)) :callv)
                (equal (cadr (nth (+ pc (s2code-len-args (cddr e)) (s2code-len (cadr e))) code)) (c2-n))
                (equal (s2code-len e) (+ (s2code-len-args (cddr e)) (s2code-len (cadr e)) 1))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-compile e depth cenv self pc lc) (s2code-len e)))))

; the clock, from whatever state the call's step makes
(defthm callv2-clock-gen
  (implies (and (equal (car e) :callv) (equal (vcs2-step prog (c2-s2)) s3))
           (equal (vcs2-run prog s (s2clk e env caps defs fuel))
                  (cond ((not (valp (c2-ra))) (c2-s1))
                        ((not (valp (c2-rf))) (c2-s2))
                        ((or (not (clop (c2-c))) (not (consp (c2-cl))) (zp fuel)) s3)
                        ((valp (c2-r)) (vcs2-step prog (vcs2-run prog s3 (c2-bclk))))
                        (t (vcs2-run prog s3 (c2-bclk))))))
  :rule-classes nil
  :hints (("Goal" :expand ((s2clk e env caps defs fuel)) :in-theory (e/d (call-benv) (c+ pick-arity split-rest)))))

(defthm callv2-wf-parts
  (implies (and (equal (car e) :callv) (x2wf e n k))
           (and (x2wf (cadr e) n nil) (x2wf-args (cddr e) n)))
  :rule-classes nil)

(defmacro c2-hyps ()
  '(and (equal (car e) :callv) (s2-hyps e depth cenv self caps s env defs prog lc)
        (s2good-args (cddr e) depth cenv self caps s env defs fuel prog)))

(defthm callv2-args
  (implies (c2-hyps)
           (and (implies (valp (c2-ra))
                         (and (sstatep (c2-s1))
                              (equal (car (c2-s1)) (+ (car s) (s2code-len-args (cddr e))))
                              (equal (cadr (c2-s1)) (cadr s))
                              (equal (caddr (c2-s1)) (+ (caddr s) (c2-n)))
                              (equal (s-ctl (c2-s1)) (s-ctl s))
                              (cagree (cadddr (c2-s1)) (cadddr s) (caddr s))
                              (cvals-at (caddr s) (c2-vs) (cadddr (c2-s1)))
                              (equal (len (c2-vs)) (c2-n)) (true-listp (c2-vs))))
                (s2-thr s (c2-ra) (c2-s1))
                (not (recurp (c2-ra)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2good-args s2-hyps) (c2-thy)) :do-not-induct t
                  :use ((:instance callv2-wf-parts (n (len env)) (k (lck lc)))
                        (:instance callv2-code (code (car prog)) (pc (car s)))
                        (:instance mx2-args-val-shape (es (cddr e)))
                        (:instance mx2-args-not-recur (es (cddr e)))))))

(defthm callv2-fn-hyps
  (implies (and (c2-hyps) (valp (c2-ra)))
           (s2-hyps (cadr e) (+ depth (c2-n)) cenv self caps (c2-s1) env defs prog nil))
  :hints (("Goal" :in-theory (disable mx2 mx2-args cenv-ok cself-ok cenv-ok-agree cself-ok-agree
                                      cenv-ok-bigger-f cself-ok-bigger-f s2good-args)
                  :do-not-induct t
                  :use ((:instance callv2-args)
                        (:instance callv2-code (code (car prog)) (pc (car s)))
                        (:instance callv2-wf-parts (n (len env)) (k (lck lc)))
                        (:instance handlers-ok-bigger (ctl (s-ctl s)) (sp (caddr s)) (sp2 (caddr (c2-s1))))
                        (:instance cagree-sym (a (cadddr (c2-s1))) (b (cadddr s)) (h (caddr s)))
                        (:instance cenv-ok-agree (a (cadddr s)) (b (cadddr (c2-s1))) (fb (cadr s)) (f depth))
                        (:instance cself-ok-agree (a (cadddr s)) (b (cadddr (c2-s1))) (fb (cadr s)) (f depth))
                        (:instance cenv-ok-bigger-f (regs (cadddr (c2-s1))) (fb (cadr s)) (f depth) (g (+ depth (c2-n))))
                        (:instance cself-ok-bigger-f (regs (cadddr (c2-s1))) (fb (cadr s)) (f depth) (g (+ depth (c2-n))))))))

(defmacro c2-hyps-fn ()
  '(and (c2-hyps) (s2good (cadr e) (+ depth (c2-n)) cenv self caps (c2-s1) env defs fuel prog nil)))

(defthm callv2-fn
  (implies (and (c2-hyps-fn) (valp (c2-ra)))
           (and (s2-val (cadr e) (c2-s1) (c2-rf) (c2-s2)) (s2-thr (c2-s1) (c2-rf) (c2-s2)) (not (recurp (c2-rf)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (c2-thy) :do-not-induct t
                  :use ((:instance callv2-fn-hyps)
                        (:instance s2good-gives (e (cadr e)) (depth (+ depth (c2-n))) (s (c2-s1)) (lc nil))
                        (:instance (:definition s2-hyps) (e (cadr e)) (depth (+ depth (c2-n))) (s (c2-s1)) (lc nil))
                        (:instance mx2-not-recur (e (cadr e)))))))

; at the call instruction: the arguments, the closure above them
(defthm callv2-at-call
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)))
           (and (sstatep (c2-s2))
                (equal (car (c2-s2)) (c2-pc2))
                (equal (cadr (c2-s2)) (cadr s)) (equal (caddr (c2-s2)) (+ (caddr s) (c2-n) 1))
                (equal (s-ctl (c2-s2)) (s-ctl s))
                (cagree (cadddr (c2-s2)) (cadddr s) (caddr s))
                (cvals-at (caddr s) (c2-vs) (cadddr (c2-s2)))
                (equal (nth (+ (caddr s) (c2-n)) (cadddr (c2-s2))) (c2-c))
                (equal (car (nth (c2-pc2) (car prog))) :callv)
                (equal (cadr (nth (c2-pc2) (car prog))) (c2-n))))
  :rule-classes nil
  :hints (("Goal" :in-theory (c2-thy) :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-fn) (:instance (:definition s2-hyps))
                        (:instance callv2-code (code (car prog)) (pc (car s)))
                        (:instance s2-val-open (e (cadr e)) (s (c2-s1)) (r (c2-rf)) (s2 (c2-s2)))
                        (:instance cagree-below-push (a (cadddr (c2-s2))) (b (cadddr (c2-s1))) (sp (+ (caddr s) (c2-n))) (v (c2-c)))
                        (:instance cagree-smaller (a (cadddr (c2-s2))) (b (cadddr (c2-s1))) (h (+ (caddr s) (c2-n))) (g (caddr s)))
                        (:instance cagree-trans (a (cadddr (c2-s2))) (b (cadddr (c2-s1))) (c (cadddr s)) (h (caddr s)))
                        (:instance callv-args-stay (r2 (cadddr (c2-s2))) (r1 (cadddr (c2-s1)))
                                   (g (+ (caddr s) (c2-n))) (w (c2-c)) (k (caddr s)) (vs (c2-vs)))))))

; NOT ONE OF THE MACHINE'S CLOSURES: the runtime's call, (prim :invoke
; (c . args)), its answer where the arguments began -- or its throw
(defmacro c2-a () '(prim :invoke (cons (c2-c) (c2-vs))))

(defthm callv2-step-invoke
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (not (clop (c2-c))))
           (equal (vcs2-step prog (c2-s2))
                  (if (throwp (c2-a))
                      (unwind (cdr (c2-a)) (s-ctl s) (cadddr (c2-s2)))
                    (list (1+ (c2-pc2)) (cadr s) (1+ (caddr s)) (update-nth (caddr s) (c2-a) (cadddr (c2-s2))) (s-ctl s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2step-callv ssetreg) (c2-thy)) :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-at-call) (:instance (:definition s2-hyps))
                        (:instance stk-from-vals (a (caddr s)) (vs (c2-vs)) (stk (cadddr (c2-s2))))))))

(defthm callv2-invoke-val
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (not (clop (c2-c))) (not (throwp (c2-a))))
           (s2-val e s (cons :val (c2-a)) (vcs2-step prog (c2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val) (c2-thy)) :do-not-induct t
                  :use ((:instance callv2-step-invoke) (:instance callv2-args) (:instance callv2-at-call)
                        (:instance (:definition s2-hyps))
                        (:instance callv2-code (code (car prog)) (pc (car s)))
                        (:instance cagree-write-at (n (caddr s)) (a (cadddr (c2-s2))) (b (cadddr s)) (x (c2-a)))))))

(defthm callv2-invoke-thr
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (not (clop (c2-c))) (throwp (c2-a)))
           (thrown-at s (cdr (c2-a)) (vcs2-step prog (c2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (c2-thy) :do-not-induct t
                  :use ((:instance callv2-step-invoke) (:instance callv2-at-call) (:instance (:definition s2-hyps))
                        (:instance unwind-thrown-at (s (c2-s2)) (v (cdr (c2-a))))
                        (:instance thrown-at-transfer (s1 (c2-s2)) (v (cdr (c2-a))) (s2 (vcs2-step prog (c2-s2))))))))

; NO CLAUSE FOR THE COUNT: the call's step throws
(defthm callv2-step-throw
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (not (consp (c2-cl))))
           (thrown-at s (cdr (mx2 e env caps defs fuel)) (vcs2-step prog (c2-s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2step-callv mx2-callv) (c2-thy)) :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-at-call) (:instance (:definition s2-hyps))
                        (:instance pick-arity-corr (cls (cdr (assoc-equal (clo-f (cdr (mx2 (cadr e) env caps defs fuel))) defs))) (ents (cdr (assoc-equal (clo-f (cdr (mx2 (cadr e) env caps defs fuel))) (cdr prog)))) (code (car prog)) (m (len (cdr (mx2-args (cddr e) env caps defs fuel))))) (:instance s2fns-ok-necc (name (clo-f (cdr (mx2 (cadr e) env caps defs fuel)))))
                        (:instance unwind-thrown-at (s (c2-s2)) (v :arity))
                        (:instance thrown-at-transfer (s1 (c2-s2)) (v (cdr (mx2 e env caps defs fuel)))
                                   (s2 (vcs2-step prog (c2-s2))))))))

; A CLAUSE: its frame where the first argument is, a return record
(defthm callv2-s3
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)))
           (equal (vcs2-step prog (c2-s2)) (c2-s3)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2step-callv call-frame) (c2-thy)) :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-at-call) (:instance (:definition s2-hyps))
                        (:instance pick-arity-corr (cls (cdr (assoc-equal (clo-f (cdr (mx2 (cadr e) env caps defs fuel))) defs))) (ents (cdr (assoc-equal (clo-f (cdr (mx2 (cadr e) env caps defs fuel))) (cdr prog)))) (code (car prog)) (m (len (cdr (mx2-args (cddr e) env caps defs fuel))))) (:instance s2fns-ok-necc (name (clo-f (cdr (mx2 (cadr e) env caps defs fuel)))))))))

(defthm vcs2-body-code
  (implies (and (ccode-at code pc (vcs2-body cl pc)) (natp pc))
           (and (ccode-at code pc (vcs2-compile (cadr cl) (1+ (if (restp cl) (1+ (nfix (car cl))) (nfix (car cl))))
                                                (count-from 0 (if (restp cl) (1+ (nfix (car cl))) (nfix (car cl))))
                                                (if (restp cl) (1+ (nfix (car cl))) (nfix (car cl))) pc nil))
                (equal (nth (+ pc (s2code-len (cadr cl))) code) (list :ret))))
  :rule-classes nil
  :hints (("Goal" :expand ((vcs2-body cl pc)) :in-theory (disable restp))))

; the clause the call runs: what the table and the definitions say of it
(defthm callv2-clause
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)))
           (and (implies (not (restp (c2-cl))) (equal (c2-n0) (c2-n)))
                (implies (restp (c2-cl)) (<= (c2-n0) (c2-n)))
                (natp (cadr (c2-en)))
                (ccode-at (car prog) (cadr (c2-en)) (vcs2-body (c2-cl) (cadr (c2-en))))
                (x2wf (cadr (c2-cl)) (len (c2-benv)) nil)
                (equal (len (c2-benv)) (c2-nl))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(pick-arity-fixed-len pick-arity-rest-len len-split-rest pick-arity-natp call-benv call-nl)
                                             (c2-thy))
                  :do-not-induct t
                  :use ((:instance callv2-args) (:instance (:definition s2-hyps)) (:instance pick-arity-corr (cls (cdr (assoc-equal (clo-f (cdr (mx2 (cadr e) env caps defs fuel))) defs))) (ents (cdr (assoc-equal (clo-f (cdr (mx2 (cadr e) env caps defs fuel))) (cdr prog)))) (code (car prog)) (m (len (cdr (mx2-args (cddr e) env caps defs fuel))))) (:instance s2fns-ok-necc (name (clo-f (cdr (mx2 (cadr e) env caps defs fuel)))))
                        (:instance pick-body-wf-fixed (name (clo-f (c2-c))) (vs (c2-vs)))
                        (:instance pick-body-wf-rest (name (clo-f (c2-c))) (vs (c2-vs)))
                        (:instance pick-arity-natp (name (clo-f (c2-c))) (vs (c2-vs)))
                        (:instance pick-arity-fixed-len (cls (c2-cls)) (m (len (c2-vs))))
                        (:instance pick-arity-rest-len (cls (c2-cls)) (m (len (c2-vs))))))))

; the callee's hypotheses in the frame the call made: a fixed clause
(defthm callv2-body-hyps-fixed
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)) (not (restp (c2-cl))))
           (s2-hyps (cadr (c2-cl)) (1+ (c2-n)) (count-from 0 (c2-n)) (c2-n) (clo-caps (c2-c))
                    (list (nfix (cadr (c2-en))) (caddr s) (+ (caddr s) (c2-n) 1) (cadddr (c2-s2)) (cons (c2-crec) (s-ctl s)))
                    (c2-vs) defs prog nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-hyps cself-ok lc-ok lck handlers-ok-call-record handlers-ok-bigger call-benv call-nl)
                                             (c2-thy))
                  :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-at-call) (:instance callv2-clause)
                        (:instance (:definition s2-hyps))
                        (:instance vcs2-body-code (code (car prog)) (pc (cadr (c2-en))) (cl (c2-cl)))
                        (:instance cenv-ok-count-from (i 0) (n (c2-n)) (base (caddr s)) (vs (c2-vs))
                                   (regs (cadddr (c2-s2))) (g (1+ (c2-n))))))))

(defmacro c2-stk3r ()
  '(update-nth (+ (caddr s) (c2-n0) 1) (c2-c)
               (update-nth (+ (caddr s) (c2-n0)) (stk-from (+ (caddr s) (c2-n0)) (- (c2-n) (c2-n0)) (cadddr (c2-s2)))
                           (cadddr (c2-s2)))))

; a variadic clause: the rest packed
(defthm callv2-body-hyps-rest
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)) (restp (c2-cl)))
           (s2-hyps (cadr (c2-cl)) (+ 2 (c2-n0)) (count-from 0 (1+ (c2-n0))) (1+ (c2-n0)) (clo-caps (c2-c))
                    (list (nfix (cadr (c2-en))) (caddr s) (+ (caddr s) (c2-n0) 2) (c2-stk3r) (cons (c2-crec) (s-ctl s)))
                    (split-rest (c2-n0) (c2-vs)) defs prog nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-hyps cself-ok lc-ok lck handlers-ok-call-record handlers-ok-bigger call-benv call-nl)
                                             (c2-thy))
                  :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-at-call) (:instance callv2-clause)
                        (:instance (:definition s2-hyps))
                        (:instance vcs2-body-code (code (car prog)) (pc (cadr (c2-en))) (cl (c2-cl)))
                        (:instance rest-frame-vals (k (caddr s)) (n0 (c2-n0)) (vs (c2-vs)) (stk (cadddr (c2-s2))) (c (c2-c)))
                        (:instance cenv-ok-count-from (i 0) (n (1+ (c2-n0))) (base (caddr s)) (vs (split-rest (c2-n0) (c2-vs)))
                                   (regs (c2-stk3r)) (g (+ 2 (c2-n0))))))))

(defmacro c2-call-hyps ()
  '(and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)) (not (zp fuel))
        (s2good (cadr (c2-cl)) (1+ (c2-nl)) (count-from 0 (c2-nl)) (c2-nl) (clo-caps (c2-c)) (c2-s3) (c2-benv)
                defs (1- fuel) prog nil)))

(defthm cagree-update-above
  (implies (and (cagree a b h) (natp g) (<= (nfix h) g)) (cagree (update-nth g w a) b h))
  :hints (("Goal" :use ((:instance cagree-write-above (d g) (v w)) (:instance cagree-trans (a (update-nth g w a)) (b a) (c b)))
                  :in-theory (disable cagree-write-above cagree-trans))))

; the frame, whichever kind: the stack below the call's start as it was
(defthm callv2-s3-facts
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)))
           (and (sstatep (c2-s3)) (equal (cadr (c2-s3)) (caddr s)) (equal (caddr (c2-s3)) (+ (caddr s) (c2-nl) 1))
                (equal (s-ctl (c2-s3)) (cons (c2-crec) (s-ctl s)))
                (equal (car (c2-s3)) (cadr (c2-en)))
                (cagree (cadddr (c2-s3)) (cadddr s) (caddr s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(call-frame call-nl) (c2-thy)) :do-not-induct t
                  :cases ((restp (c2-cl)))
                  :use ((:instance callv2-at-call) (:instance callv2-clause) (:instance (:definition s2-hyps))
                        (:instance cagree-update-above (a (cadddr (c2-s2))) (b (cadddr s)) (g (+ (caddr s) (c2-n0))) (h (caddr s))
                                   (w (stk-from (+ (caddr s) (c2-n0)) (- (c2-n) (c2-n0)) (cadddr (c2-s2)))))
                        (:instance cagree-update-above
                                   (a (update-nth (+ (caddr s) (c2-n0)) (stk-from (+ (caddr s) (c2-n0)) (- (c2-n) (c2-n0)) (cadddr (c2-s2)))
                                                  (cadddr (c2-s2))))
                                   (b (cadddr s)) (g (+ (caddr s) (c2-n0) 1)) (h (caddr s)) (w (c2-c)))))))

; the callee's outcome, in the frame
(defthm callv2-body
  (implies (c2-call-hyps)
           (and (s2-val (cadr (c2-cl)) (c2-s3) (c2-r) (c2-s4)) (s2-thr (c2-s3) (c2-r) (c2-s4)) (not (recurp (c2-r)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(call-frame call-nl call-benv) (c2-thy)) :do-not-induct t
                  :cases ((restp (c2-cl)))
                  :use ((:instance callv2-body-hyps-fixed) (:instance callv2-body-hyps-rest) (:instance callv2-clause)
                        (:instance (:definition s2-hyps))
                        (:instance s2good-gives (e (cadr (c2-cl))) (depth (1+ (c2-nl))) (cenv (count-from 0 (c2-nl)))
                                   (self (c2-nl)) (caps (clo-caps (c2-c))) (s (c2-s3)) (env (c2-benv)) (fuel (1- fuel)) (lc nil))
                        (:instance mx2-not-recur (e (cadr (c2-cl))) (env (c2-benv)) (caps (clo-caps (c2-c))) (fuel (1- fuel)))))))

; the return, over plain states: the callee's value to the frame's base,
; the caller's frame and control stack back
(defthm ret-abs
  (implies (and (sstatep s3) (natp sp) (natp k) (equal (cadr s3) sp) (equal (caddr s3) (+ sp k 1))
                (equal (s-ctl s3) (cons (list rpc fb) ctl)) (natp rpc) (natp fb)
                (cagree (cadddr s3) stk0 sp)
                (sstatep s4) (equal (cadr s4) sp) (equal (caddr s4) (+ sp k 2)) (equal (s-ctl s4) (s-ctl s3))
                (cagree (cadddr s4) (update-nth (+ sp k 1) v (cadddr s3)) (+ sp k 2))
                (equal (nth (car s4) (car prog)) (list :ret)))
           (let ((s5 (vcs2-step prog s4)))
             (and (sstatep s5) (equal (car s5) rpc) (equal (cadr s5) fb) (equal (caddr s5) (1+ sp)) (equal (s-ctl s5) ctl)
                  (cagree (cadddr s5) (update-nth sp v stk0) (1+ sp)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(sstep-ret) (l2-thy)) :do-not-induct t
                  :use ((:instance cagree-nth (a (cadddr s4)) (b (update-nth (+ sp k 1) v (cadddr s3))) (h (+ sp k 2)) (r (+ sp k 1)))
                        (:instance cagree-below-push (a (cadddr s4)) (b (cadddr s3)) (sp (+ sp k 1)))
                        (:instance cagree-smaller (a (cadddr s4)) (b (cadddr s3)) (h (+ sp k 1)) (g sp))
                        (:instance cagree-trans (a (cadddr s4)) (b (cadddr s3)) (c stk0) (h sp))
                        (:instance cagree-write-at (a (cadddr s4)) (b stk0) (n sp) (x v))))))

; a call as one push, over plain states: the frame, the callee's value
; above it, the return
(defthm call-val-abs
  (implies (and (sstatep s) (natp la) (natp lf) (natp lb) (natp k) (natp ent)
                (sstatep s3) (equal (car s3) ent) (equal (cadr s3) (caddr s)) (equal (caddr s3) (+ (caddr s) k 1))
                (equal (s-ctl s3) (cons (list (+ 1 (car s) la lf) (cadr s)) (s-ctl s)))
                (cagree (cadddr s3) (cadddr s) (caddr s))
                (sstatep s4) (equal (car s4) (+ ent lb)) (equal (cadr s4) (cadr s3)) (equal (caddr s4) (1+ (caddr s3)))
                (equal (s-ctl s4) (s-ctl s3))
                (cagree (cadddr s4) (update-nth (caddr s3) v (cadddr s3)) (1+ (caddr s3)))
                (equal (nth (+ ent lb) (car prog)) (list :ret)))
           (let ((s5 (vcs2-step prog s4)))
             (and (sstatep s5) (equal (car s5) (+ (car s) la lf 1)) (equal (cadr s5) (cadr s))
                  (equal (caddr s5) (1+ (caddr s))) (equal (s-ctl s5) (s-ctl s))
                  (cagree (cadddr s5) (update-nth (caddr s) v (cadddr s)) (1+ (caddr s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (l2-thy) :do-not-induct t
                  :use ((:instance ret-abs (sp (caddr s)) (rpc (+ 1 (car s) la lf)) (fb (cadr s)) (ctl (s-ctl s))
                                   (stk0 (cadddr s)))))))

; where the callee's return is
(defthm callv2-ret-at
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)))
           (and (equal (nth (+ (car (c2-s3)) (s2code-len (cadr (c2-cl)))) (car prog)) (list :ret))
                (natp (car (c2-s3)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (c2-thy) :do-not-induct t
                  :use ((:instance callv2-s3-facts) (:instance callv2-clause)
                        (:instance vcs2-body-code (code (car prog)) (pc (cadr (c2-en))) (cl (c2-cl)))))))

; THE CALLEE'S VALUE: returned to the call's slot
(defthm callv2-path-val
  (implies (and (c2-call-hyps) (valp (c2-r)))
           (s2-val e s (c2-r) (vcs2-step prog (c2-s4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(s2-val valp val natp-s2code-len natp-s2code-len-args (:type-prescription call-nl) natp sstatep-fc commutativity-of-+ associativity-of-+ commutativity-2-of-+ fold-consts-in-+)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance callv2-s3-facts) (:instance callv2-body) (:instance callv2-ret-at)
                        (:instance (:definition s2-hyps)) (:instance sstatep-fc)
                        (:instance callv2-code (code (car prog)) (pc (car s)))
                        (:instance s2-val-open (e (cadr (c2-cl))) (s (c2-s3)) (r (c2-r)) (s2 (c2-s4)))
                        (:instance call-val-abs (s3 (c2-s3)) (s4 (c2-s4)) (k (c2-nl)) (v (cdr (c2-r)))
                                   (la (s2code-len-args (cddr e))) (lf (s2code-len (cadr e))) (lb (s2code-len (cadr (c2-cl))))
                                   (ent (car (c2-s3))))))))

; THE CALLEE THROWS: the call's record passed over
(defthm callv2-path-thr
  (implies (and (c2-call-hyps) (thrownp (c2-r)))
           (thrown-at s (cdr (c2-r)) (c2-s4)))
  :rule-classes nil
  :hints (("Goal" :in-theory (c2-thy) :do-not-induct t
                  :use ((:instance callv2-s3-facts) (:instance callv2-body) (:instance (:definition s2-hyps))
                        (:instance s2-thr-open (s (c2-s3)) (r (c2-r)) (s2 (c2-s4)))
                        (:instance hfind-call-record (x (1+ (c2-pc2))) (r (list (cadr s))) (ctl (s-ctl s)))
                        (:instance thrown-at-transfer-hf (s1 (c2-s3)) (v (cdr (c2-r))) (s2 (c2-s4)) (h (caddr s)))))))

; THE FUNCTION'S EXPRESSION THROWS
(defthm callv2-fn-thr
  (implies (and (c2-hyps-fn) (valp (c2-ra)) (thrownp (c2-rf)))
           (thrown-at s (cdr (c2-rf)) (c2-s2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (c2-thy) :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-fn) (:instance (:definition s2-hyps))
                        (:instance s2-thr-open (s (c2-s1)) (r (c2-rf)) (s2 (c2-s2)))
                        (:instance thrown-at-transfer (s1 (c2-s1)) (v (cdr (c2-rf))) (s2 (c2-s2)))))))

; THE CALL
(defthm s2good-callv
  (implies (and (equal (car e) :callv)
                (s2good-args (cddr e) depth cenv self caps s env defs fuel prog)
                (s2good (cadr e) (+ depth (c2-n)) cenv self caps (c2-s1) env defs fuel prog nil)
                (implies (and (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)) (not (zp fuel)))
                         (s2good (cadr (c2-cl)) (1+ (c2-nl)) (count-from 0 (c2-nl)) (c2-nl) (clo-caps (c2-c)) (c2-s3) (c2-benv)
                                 defs (1- fuel) prog nil)))
           (s2good e depth cenv self caps s env defs fuel prog lc))
  :hints (("Goal" :in-theory (union-theories '(s2good s2-val s2-rec s2-thr valp recurp thrownp mx2-callv car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :do-not-induct t
                  :use ((:instance callv2-args) (:instance callv2-fn) (:instance callv2-fn-thr)
                        (:instance callv2-step-throw) (:instance callv2-s3)
                        (:instance callv2-invoke-val) (:instance callv2-invoke-thr)
                        (:instance callv2-path-val) (:instance callv2-path-thr) (:instance callv2-body)
                        (:instance callv2-clock-gen (s3 (vcs2-step prog (c2-s2))))
                        (:instance callv2-clock-gen (s3 (c2-s3)))))))

; ---- THE THEOREM -----------------------------------------------------------------------------

(defthm s2good-loopit-atom
  (implies (not (consp e)) (s2good-loopit e depth cenv self caps s env vs defs fuel prog))
  :hints (("Goal" :in-theory (enable loopit2-hyps))))

(defun s2ind (flg e depth cenv self caps s env defs fuel prog lc vs)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) (if (eq flg :loop) 0 1)))
                  :well-founded-relation o< :ruler-extenders :all :verify-guards nil))
  (cond
   ((eq flg :args)
    (if (atom e)
        (list depth cenv self caps s env defs fuel prog lc vs)
      (list (s2ind :m (car e) depth cenv self caps s env defs fuel prog nil nil)
            (s2ind :args (cdr e) (1+ depth) cenv self caps (vcs2-run prog s (s2clk (car e) env caps defs fuel))
                   env defs fuel prog nil nil))))
   ((eq flg :loop)
    (if (not (consp e))
        nil
      (list (s2ind :m (caddr e) (+ depth (len (cadr e))) (lp2-cenv) self caps s (append env vs) defs fuel prog (lp2-lc) nil)
            (if (and (recurp (lp2-rb)) (not (zp fuel)))
                (s2ind :loop e depth cenv self caps (lp2-s2) env defs (1- fuel) prog nil (cdr (lp2-rb)))
              nil))))
   (t
    (case (car e)
      (:if (list (s2ind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                 (s2ind :m (caddr e) depth cenv self caps (i2-s1b) env defs fuel prog lc nil)
                 (s2ind :m (cadddr e) depth cenv self caps (i2-s1b) env defs fuel prog lc nil)))
      (:let (list (s2ind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                  (s2ind :m (caddr e) (1+ depth) (append cenv (list depth)) self caps (l2-s1) (l2-env) defs fuel prog lc nil)))
      ((:add :lt) (list (s2ind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                        (s2ind :m (caddr e) (1+ depth) cenv self caps (b2-s1) env defs fuel prog nil nil)))
      ((:mkclo :prim) (s2ind :args (cddr e) depth cenv self caps s env defs fuel prog nil nil))
      (:callv (list (s2ind :args (cddr e) depth cenv self caps s env defs fuel prog nil nil)
                    (s2ind :m (cadr e) (+ depth (c2-n)) cenv self caps (c2-s1) env defs fuel prog nil nil)
                    (if (and (valp (c2-ra)) (valp (c2-rf)) (clop (c2-c)) (consp (c2-cl)) (not (zp fuel)))
                        (s2ind :m (cadr (c2-cl)) (1+ (c2-nl)) (count-from 0 (c2-nl)) (c2-nl) (clo-caps (c2-c)) (c2-s3)
                               (c2-benv) defs (1- fuel) prog nil nil)
                      nil)))
      (:loop (list (s2ind :args (cadr e) depth cenv self caps s env defs fuel prog nil nil)
                   (s2ind :loop e depth cenv self caps (lq-s1) env defs fuel prog nil (lq-vs))))
      (:recur (s2ind :args (cdr e) depth cenv self caps s env defs fuel prog nil nil))
      (:throw (s2ind :m (cadr e) depth cenv self caps s env defs fuel prog nil nil))
      (:try (list (s2ind :m (cadr e) depth cenv self caps (y2-s0) env defs fuel prog nil nil)
                  (s2ind :m (caddr e) (1+ depth) (append cenv (list depth)) self caps (y2-sb) (y2-env) defs fuel prog nil nil)))
      (otherwise (list depth cenv self caps s env defs fuel prog lc vs))))))

(defthm vcs2-good-flag
  (cond ((eq flg :args) (s2good-args e depth cenv self caps s env defs fuel prog))
        ((eq flg :loop) (s2good-loopit e depth cenv self caps s env vs defs fuel prog))
        (t (s2good e depth cenv self caps s env defs fuel prog lc)))
  :rule-classes nil
  :hints (("Goal" :induct (s2ind flg e depth cenv self caps s env defs fuel prog lc vs)
                  :in-theory (union-theories '(s2good-if s2good-let s2good-binop s2good-mkclo s2good-callv
                                               s2good-loop s2good-recur s2good-prim s2good-throw s2good-try
                                               s2good-leaf
                                               s2good-args-nil s2good-args-cons
                                               s2good-loopit-step s2good-loopit-atom
                                               member-equal car-cons cdr-cons (:induction s2ind))
                                             (theory 'minimal-theory)))))

; RUNNING AN EXPRESSION'S CODE ON THE MACHINE WITH ARITIES, PRIMITIVES
; AND THROWS: a value pushed, a recur at its loop's head, or a throw at
; the nearest handler -- what the meaning answers
(defthm vcs2-good
  (s2good e depth cenv self caps s env defs fuel prog lc)
  :hints (("Goal" :use ((:instance vcs2-good-flag (flg :m))))))

; ---- WHOLE PROGRAMS --------------------------------------------------------------------------

(defthm len-vcs2-body
  (equal (len (vcs2-body cl pc)) (1+ (s2code-len (cadr cl)))))
(in-theory (disable vcs2-body))

(defthm vcs2-clauses-places
  (implies (and (natp pc) (clauses-ok cls) (ccode-at code pc (car (vcs2-clauses cls pc))))
           (entries-ok cls (cdr (vcs2-clauses cls pc)) code))
  :hints (("Goal" :induct (vcs2-clauses cls pc) :in-theory (disable s2code-len))))

(defthm vcs2-defs-places
  (implies (and (natp pc) (x2defs-ok ds) (ccode-at code pc (car (vcs2-defs ds pc))))
           (entries-ok (cdr (assoc-equal name ds)) (cdr (assoc-equal name (cdr (vcs2-defs ds pc)))) code))
  :hints (("Goal" :induct (vcs2-defs ds pc) :in-theory (disable vcs2-clauses entries-ok) :expand ((entries-ok nil nil code)))))

(defmacro s2v-main () '(append (vcs2-compile e 0 nil nil 0 nil) (list (list :ret))))

(defthm vcs2-program-fns-ok
  (implies (x2defs-ok defs) (s2fns-ok (vcs2-program e defs) defs))
  :hints (("Goal" :in-theory (e/d (s2fns-ok) (vcs2-defs entries-ok))
                  :use ((:instance vcs2-defs-places (ds defs) (pc (len (s2v-main)))
                                   (code (car (vcs2-program e defs)))
                                   (name (s2fns-ok-witness (vcs2-program e defs) defs)))
                        (:instance ccode-at-self-gen (p (s2v-main)) (x (car (vcs2-defs defs (len (s2v-main))))))))))

; a finished program stays finished: the main code's return with no caller
(defthm s2halted-stays
  (implies (and (sstatep s) (equal (cadr s) 0) (equal (caddr s) 1) (not (consp (s-ctl s)))
                (ccode-at (car prog) (car s) (list (list :ret))))
           (let ((s2 (vcs2-run prog s k)))
             (and (sstatep s2) (equal (car s2) (car s)) (equal (cadr s2) 0) (equal (caddr s2) 1)
                  (not (consp (s-ctl s2)))
                  (equal (nth 0 (cadddr s2)) (nth 0 (cadddr s))))))
  :hints (("Goal" :induct (vcs2-run prog s k)
                  :in-theory (enable vcs2-run)
                  :expand ((vcs2-run prog s k)))))

; a program stopped by a throw stays stopped
(defthm s2thrown-stays
  (implies (equal (car s) :thrown) (equal (vcs2-run prog s k) s))
  :hints (("Goal" :induct (vcs2-run prog s k) :in-theory (enable vcs2-run) :expand ((vcs2-run prog s k)))))

(defmacro s2c-prog () '(vcs2-program e defs))
(defmacro s2c-end () '(vcs2-run (vcs2-program e defs) (list 0 0 0 nil nil) (s2clk e nil nil defs fuel)))

; the program's start: the expression's hypotheses
(defthm vcs2-start-hyps
  (implies (and (x2defs-ok defs) (x2wf e 0 nil))
           (s2-hyps e 0 nil nil nil (list 0 0 0 nil nil) nil defs (s2c-prog) nil))
  :hints (("Goal" :in-theory (disable vcs2-compile vcs2-defs)
                  :use ((:instance vcs2-program-fns-ok)
                        (:instance ccode-at-shift (pc 0) (a (vcs2-compile e 0 nil nil 0 nil))
                                   (b (cons '(:ret) (car (vcs2-defs defs (len (s2v-main))))))
                                   (c (vcs2-compile e 0 nil nil 0 nil))))
                  :expand ((vcs2-program e defs)))))

; A COMPILED PROGRAM ON THE MACHINE WITH ARITIES, PRIMITIVES AND THROWS
; answers what its meaning does: its value, or the value a throw nothing
; caught carried
(defthm vcs2-correct
  (implies (and (x2defs-ok defs) (x2wf e 0 nil)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k))
           (equal (vcs2-run-program e defs (+ (s2clk e nil nil defs fuel) k))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable s2good vcs2-good s2halted-stays vcs2-program vcs2-program-fns-ok vcs2-run-plus
                                      s2-val s2-thr s2-rec s2-hyps vcs2-start-hyps thrown-at)
                  :use ((:instance vcs2-start-hyps)
                        (:instance vcs2-run-plus (prog (s2c-prog)) (s (list 0 0 0 nil nil)) (a (s2clk e nil nil defs fuel)) (b k))
                        (:instance vcs2-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 nil nil)) (env nil)
                                   (prog (s2c-prog)) (lc nil))
                        (:instance (:definition s2good) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (s2c-prog)) (lc nil))
                        (:instance (:definition s2-val) (s (list 0 0 0 nil nil)) (r (mx2 e nil nil defs fuel)) (s2 (s2c-end)))
                        (:instance (:definition s2-thr) (s (list 0 0 0 nil nil)) (r (mx2 e nil nil defs fuel)) (s2 (s2c-end)))
                        (:instance (:definition thrown-at) (s (list 0 0 0 nil nil)) (v (cdr (mx2 e nil nil defs fuel)))
                                   (s2 (s2c-end)))
                        (:instance s2halted-stays (prog (s2c-prog)) (s (s2c-end)))
                        (:instance s2thrown-stays (prog (s2c-prog)) (s (s2c-end)))
                        (:instance cagree-nth (r 0) (h 1) (a (cadddr (s2c-end)))
                                   (b (update-nth 0 (cdr (mx2 e nil nil defs fuel)) nil)))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcs2-compile e 0 nil nil 0 nil))
                                   (b (cons '(:ret) (car (vcs2-defs defs (len (s2v-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcs2-program))))

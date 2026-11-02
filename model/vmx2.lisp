; clotran's VM, formally (PLAN step 30): the stack machine extended to the
; rest of what the Fortran stack VM must run, on top of model/vmx.lisp's
; loop and recur:
;
;   MULTI-ARITY AND VARIADIC FUNCTIONS. A function is a list of clauses,
;   (n body) or (n body :rest). A call with m arguments takes the clause
;   of arity m, or else the variadic clause of n <= m, whose body gets
;   the first n arguments and a list of the rest as local n.
;
;   CALLS INTO THE RUNTIME. (:prim op e1 .. en): the runtime's prim on the
;   values. prim is constrained by nothing -- the theorems hold whatever
;   the builtins compute -- and may throw: an answer (:throw . v) throws v.
;   For the checks below an executable one is attached (defattach).
;
;   A CALL OF WHAT IS NOT ONE OF THE MACHINE'S CLOSURES is the runtime's:
;   (prim :invoke (f . args)), its answer the call's or its throw thrown --
;   so a call of a builtin, a Var or a fn the machine did not compile is a
;   call like any other, and the runtime decides what it is.
;
;   APPLY. The value :apply is clojure.core/apply. (:applyv f e1 .. en) is
;   :callv's call, but when f's value is apply, its first argument a
;   closure and its last a seq -- the model's list, no closure -- it is the
;   call of that closure on the arguments between and the seq's elements
;   (apply's spread, IFn.applyTo): a call whose head may be apply, which
;   only the head's value tells. Any other call of apply -- of a builtin,
;   of no fn, of what is no seq, with fewer than two arguments -- is the
;   runtime's, as any non-closure's call is.
;
;   THROW AND TRY. (:throw e); (:try body handler), the handler's new
;   local the thrown value. A call of a closure with no clause of its
;   arity THROWS :arity, so a try catches it, as clj's ArityException is
;   caught. finally is
;   not a form: (try B (finally F)) is
;       (let [r (try B (catch t (do F (throw t))))] (do F r))
;   exactly, F's value being discarded.
;
; THE MACHINE adds to vmx.lisp's:
;   (:callv m)        as before, by the clause the arity picks; a variadic
;                     clause's extra values packed into one list in place
;   (:applyv m)       as :callv, but when the closure is apply (and its
;                     arguments spread, as above) the last value's elements
;                     put in its place, the fn above them, and :callv's
;                     dispatch at the count that makes
;   (:prim op n)      n values popped, the runtime's answer pushed
;   (:throw)          the top value thrown
;   (:try h d)        a handler record (:h h fb d) on the control stack
;   (:endtry)         the body finished: its record popped
; A throw unwinds the control stack -- call records and all -- to the
; nearest handler record, puts the stack top at its frame's base + d,
; pushes the thrown value as the handler's local, and jumps to h; with
; none, the machine stops at pc :thrown with the value at slot 0.

(in-package "ACL2")

(include-book "vmx")

; ---- THE RUNTIME ------------------------------------------------------------

(encapsulate (((prim * *) => *))
  (local (defun prim (op vals) (declare (ignore op vals)) nil)))

(defun throwp (x) (and (consp x) (eq (car x) :throw)))

; ---- CLAUSES: the arity a call picks ------------------------------------------

(defun restp (cl) (eq (caddr cl) :rest))

(defun pick-fixed (cls m)
  (cond ((atom cls) nil)
        ((and (not (restp (car cls))) (equal (nfix (caar cls)) m)) (car cls))
        (t (pick-fixed (cdr cls) m))))

(defun pick-rest (cls m)
  (cond ((atom cls) nil)
        ((and (restp (car cls)) (<= (nfix (caar cls)) m)) (car cls))
        (t (pick-rest (cdr cls) m))))

(defun pick-arity (cls m) (or (pick-fixed cls m) (pick-rest cls m)))

; a variadic clause's locals: its first n arguments, then the rest as one list
(defun split-rest (n vs) (append (take n vs) (list (nthcdr n vs))))

; ---- APPLY: a call's callee and arguments once apply has spread them ------------

(defun x2-seqp (l) (and (true-listp l) (not (clop l))))
(defun x2-spreads (op c vs)
  (and (eq op :applyv) (eq c :apply) (consp vs) (consp (cdr vs)) (clop (car vs)) (x2-seqp (car (last vs)))))
(defun x2-fn (op c vs) (if (x2-spreads op c vs) (car vs) c))
(defun x2-vals (op c vs) (if (x2-spreads op c vs) (append (butlast (cdr vs) 1) (car (last (cdr vs)))) vs))

; ---- THE MEANING --------------------------------------------------------------
;
; An answer is (:val . v), (:recur . vs), (:thrown . v) or (:out).

(defun thrownp (r) (eq (car r) :thrown))

(mutual-recursion
 (defun mx2 (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     (:const (cons :val (cadr e)))
     (:local (cons :val (nth (nfix (cadr e)) env)))
     (:capt (cons :val (nth (nfix (cadr e)) caps)))
     (:if (let ((rc (mx2 (cadr e) env caps defs fuel)))
            (cond ((not (valp rc)) rc)
                  ((truthy (val rc)) (mx2 (caddr e) env caps defs fuel))
                  (t (mx2 (cadddr e) env caps defs fuel)))))
     (:let (let ((ri (mx2 (cadr e) env caps defs fuel)))
             (if (valp ri) (mx2 (caddr e) (append env (list (val ri))) caps defs fuel) ri)))
     ((:add :lt)
      (let ((ra (mx2 (cadr e) env caps defs fuel)))
        (if (not (valp ra))
            ra
          (let ((rb (mx2 (caddr e) env caps defs fuel)))
            (cond ((not (valp rb)) rb)
                  ((eq (car e) :add) (cons :val (+ (fix (val ra)) (fix (val rb)))))
                  (t (cons :val (bool (< (rfix (val ra)) (rfix (val rb)))))))))))
     (:mkclo (let ((rs (mx2-args (cddr e) env caps defs fuel)))
               (if (valp rs) (cons :val (clo (cadr e) (val rs))) rs)))
     ((:callv :applyv)
      (let ((rs (mx2-args (cddr e) env caps defs fuel)))
        (if (not (valp rs))
            rs
          (let ((rf (mx2 (cadr e) env caps defs fuel)))
            (if (not (valp rf))
                rf
              (let ((c (x2-fn (car e) (val rf) (val rs))) (vs (x2-vals (car e) (val rf) (val rs))))
                (if (not (clop c))
                    (let ((a (prim :invoke (cons c vs))))
                      (if (throwp a) (cons :thrown (cdr a)) (cons :val a)))
                  (let* ((cls (cdr (assoc-equal (clo-f c) defs)))
                         (cl (pick-arity cls (len vs))))
                    (cond ((not (consp cl)) (cons :thrown :arity))
                          ((zp fuel) (list :out))
                          (t (mx2 (cadr cl)
                                  (if (restp cl) (split-rest (nfix (car cl)) vs) vs)
                                  (clo-caps c) defs (1- fuel))))))))))))
     (:loop (let ((ri (mx2-args (cadr e) env caps defs fuel)))
              (if (valp ri) (mx2-loop e env (val ri) caps defs fuel) ri)))
     (:recur (let ((rs (mx2-args (cdr e) env caps defs fuel)))
               (if (valp rs) (cons :recur (val rs)) rs)))
     (:prim (let ((rs (mx2-args (cddr e) env caps defs fuel)))
              (if (not (valp rs))
                  rs
                (let ((a (prim (cadr e) (val rs))))
                  (if (throwp a) (cons :thrown (cdr a)) (cons :val a))))))
     (:throw (let ((r (mx2 (cadr e) env caps defs fuel)))
               (if (valp r) (cons :thrown (val r)) r)))
     (:try (let ((r (mx2 (cadr e) env caps defs fuel)))
             (if (thrownp r) (mx2 (caddr e) (append env (list (cdr r))) caps defs fuel) r)))
     (otherwise (cons :val nil))))
 (defun mx2-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1))))
   (if (atom es)
       (cons :val nil)
     (let ((r (mx2 (car es) env caps defs fuel)))
       (if (not (valp r))
           r
         (let ((rs (mx2-args (cdr es) env caps defs fuel)))
           (if (valp rs) (cons :val (cons (val r) (val rs))) rs))))))
 (defun mx2-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0))))
   (if (not (consp e))
       (cons :val nil)
     (let ((r (mx2 (caddr e) (append base vs) caps defs fuel)))
       (cond ((not (eq (car r) :recur)) r)
             ((zp fuel) (list :out))
             (t (mx2-loop e base (cdr r) caps defs (1- fuel))))))))

; ---- WELL FORMED ----------------------------------------------------------------
;
; as vmx.lisp's xwf, and: a prim's and a throw's operands are in no tail;
; a try's body and handler are in none either -- no recur across a try,
; as clj's compiler refuses one. A function's clauses each well formed
; for their locals: n, or n + 1 with the rest.

(mutual-recursion
 (defun x2wf (e n k)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:local (and (natp (cadr e)) (< (cadr e) (nfix n))))
     (:if (and (x2wf (cadr e) n nil) (x2wf (caddr e) n k) (x2wf (cadddr e) n k)))
     (:let (and (x2wf (cadr e) n nil) (x2wf (caddr e) (1+ (nfix n)) k)))
     ((:add :lt) (and (x2wf (cadr e) n nil) (x2wf (caddr e) n nil)))
     (:mkclo (x2wf-args (cddr e) n))
     ((:callv :applyv) (and (x2wf (cadr e) n nil) (x2wf-args (cddr e) n)))
     (:loop (and (true-listp (cadr e)) (consp (cadr e)) (x2wf-args (cadr e) n)
                 (x2wf (caddr e) (+ (nfix n) (len (cadr e))) (len (cadr e)))))
     (:recur (and (natp k) (true-listp (cdr e)) (equal (len (cdr e)) k) (x2wf-args (cdr e) n)))
     (:prim (x2wf-args (cddr e) n))
     (:throw (x2wf (cadr e) n nil))
     (:try (and (x2wf (cadr e) n nil) (x2wf (caddr e) (1+ (nfix n)) nil)))
     (otherwise t)))
 (defun x2wf-args (es n)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) t (and (x2wf (car es) n nil) (x2wf-args (cdr es) n)))))

(defun clauses-ok (cls)
  (if (atom cls)
      t
    (and (consp (car cls)) (natp (caar cls)) (consp (cdar cls))
         (x2wf (cadar cls) (if (restp (car cls)) (1+ (caar cls)) (caar cls)) nil)
         (clauses-ok (cdr cls)))))

(defun x2defs-ok (ds)
  (if (atom ds) t (and (consp (car ds)) (clauses-ok (cdar ds)) (x2defs-ok (cdr ds)))))

; ---- THE MACHINE ------------------------------------------------------------------

; unwinding to the nearest handler: call records dropped, the handler's
; frame back, the thrown value its local; none, and the machine stops
(defun unwind (v ctl stk)
  (cond ((atom ctl) (list :thrown 0 1 (update-nth 0 v stk) nil))
        ((eq (car (car ctl)) :h)
         (let ((h (nfix (cadr (car ctl)))) (hfb (nfix (caddr (car ctl)))) (hd (nfix (cadddr (car ctl)))))
           (list h hfb (+ hfb hd 1) (update-nth (+ hfb hd) v stk) (cdr ctl))))
        (t (unwind v (cdr ctl) stk))))

; a call's dispatch: the closure c on top of its arguments vs, which begin
; at fb2 in stk
(defun vcs2-callv (prog pc fb fb2 c vs stk ctl)
  (let* ((m (len vs)) (fntab (cdr prog))
         (cl (and (clop c) (pick-arity (cdr (assoc-equal (clo-f c) fntab)) m))))
    (cond ((not (clop c))
           (let ((a (prim :invoke (cons c vs))))
             (if (throwp a)
                 (unwind (cdr a) ctl stk)
               (list (1+ pc) fb (1+ fb2) (ssetreg fb2 a stk) ctl))))
          ((not (consp cl)) (unwind :arity ctl stk))
          ((not (restp cl)) (list (nfix (cadr cl)) fb2 (+ fb2 m 1) stk (cons (list (1+ pc) fb) ctl)))
          (t (let ((n (nfix (car cl))))
               ;; the rest packed into one list in slot n, the closure above it
               (list (nfix (cadr cl)) fb2 (+ fb2 n 2)
                     (update-nth (+ fb2 n 1) c
                                 (update-nth (+ fb2 n) (stk-from (+ fb2 n) (- m n) stk) stk))
                     (cons (list (1+ pc) fb) ctl)))))))

; vs written into stk from k on
(defun x2-put (k vs stk)
  (if (atom vs) stk (x2-put (1+ (nfix k)) (cdr vs) (update-nth (nfix k) (car vs) stk))))

; the stack apply's spread makes: the spread arguments, the fn above them
(defun x2-stk (op fb2 c vs stk)
  (if (x2-spreads op c vs) (x2-put fb2 (append (x2-vals op c vs) (list (car vs))) stk) stk))

(defun vcs2-step (prog s)
  (let* ((pc (car s)) (fb (nfix (cadr s))) (sp (nfix (caddr s))) (stk (cadddr s))
         (ctl (car (cddddr s))))
    (if (not (natp pc))
        s
      (case (car (nth pc (car prog)))
        ((:callv :applyv)
         (let* ((ins (nth pc (car prog))) (op (car ins)) (m (nfix (cadr ins))))
           (if (< sp (1+ m))
               s
             (let* ((c (sreg (1- sp) stk)) (fb2 (- sp (1+ m))) (vs (stk-from fb2 m stk)))
               (vcs2-callv prog pc fb fb2 (x2-fn op c vs) (x2-vals op c vs) (x2-stk op fb2 c vs stk) ctl)))))
        (:prim (let* ((ins (nth pc (car prog))) (n (nfix (caddr ins))))
                 (if (< sp n)
                     s
                   (let ((a (prim (cadr ins) (stk-from (- sp n) n stk))))
                     (if (throwp a)
                         (unwind (cdr a) ctl stk)
                       (list (1+ pc) fb (1+ (- sp n)) (ssetreg (- sp n) a stk) ctl))))))
        (:throw (if (zp sp) s (unwind (sreg (1- sp) stk) ctl stk)))
        (:try (let ((ins (nth pc (car prog))))
                (list (1+ pc) fb sp stk (cons (list :h (nfix (cadr ins)) fb (nfix (caddr ins))) ctl))))
        (:endtry (list (1+ pc) fb sp stk (cdr ctl)))
        (otherwise (vcsx-step prog s))))))

(defun vcs2-run (prog s n)
  (if (zp n) s (vcs2-run prog (vcs2-step prog s) (1- n))))

; ---- THE COMPILER -------------------------------------------------------------------

(mutual-recursion
 (defun vcs2-compile (e depth cenv self pc lc)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :push (cadr e))))
     (:local (list (list :load (nth (nfix (cadr e)) cenv))))
     (:capt (if (natp self) (list (list :capt self (cadr e))) (list (list :push nil))))
     (:if (let* ((cc (vcs2-compile (cadr e) depth cenv self pc nil))
                 (pc1 (+ pc (len cc) 1))
                 (tc (vcs2-compile (caddr e) depth cenv self pc1 lc))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (vcs2-compile (cadddr e) depth cenv self pc2 lc)))
            (append cc (list (list :jmpf pc2)) tc (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (vcs2-compile (cadr e) depth cenv self pc nil))
                  (bc (vcs2-compile (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (len ic)) lc)))
             (append ic bc (list (list :slide)))))
     ((:add :lt)
      (let* ((ac (vcs2-compile (cadr e) depth cenv self pc nil))
             (bc (vcs2-compile (caddr e) (1+ depth) cenv self (+ pc (len ac)) nil)))
        (append ac bc (list (list (car e))))))
     (:mkclo (let ((ac (vcs2-compile-args (cddr e) depth cenv self pc)))
               (append ac (list (list :mkclo (cadr e) (len (cddr e)))))))
     ((:callv :applyv)
      (let* ((n (len (cddr e)))
             (ac (vcs2-compile-args (cddr e) depth cenv self pc))
             (fc (vcs2-compile (cadr e) (+ depth n) cenv self (+ pc (len ac)) nil)))
        (append ac fc (list (list (car e) n)))))
     (:loop (let* ((k (len (cadr e)))
                   (ic (vcs2-compile-args (cadr e) depth cenv self pc))
                   (head (+ pc (len ic)))
                   (bc (vcs2-compile (caddr e) (+ depth k) (append cenv (count-from depth (+ depth k))) self head
                                     (list head depth k))))
              (append ic bc (slides k))))
     (:recur (let ((ac (vcs2-compile-args (cdr e) depth cenv self pc)))
               (append ac (list (list :recur (nfix (caddr lc)) (nfix (cadr lc)) (nfix (car lc)))))))
     (:prim (let ((ac (vcs2-compile-args (cddr e) depth cenv self pc)))
              (append ac (list (list :prim (cadr e) (len (cddr e)))))))
     (:throw (append (vcs2-compile (cadr e) depth cenv self pc nil) (list (list :throw))))
     ;; (:try h depth) body (:endtry) (:jmp end) h: handler (:slide) end:
     (:try (let* ((bc (vcs2-compile (cadr e) depth cenv self (1+ pc) nil))
                  (h (+ pc 1 (len bc) 2))
                  (hc (vcs2-compile (caddr e) (1+ depth) (append cenv (list depth)) self h nil)))
             (append (list (list :try h depth)) bc (list (list :endtry) (list :jmp (+ h (len hc) 1))) hc
                     (list (list :slide)))))
     (otherwise (list (list :push nil)))))
 (defun vcs2-compile-args (es depth cenv self pc)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (vcs2-compile (car es) depth cenv self pc nil)))
       (append c (vcs2-compile-args (cdr es) (1+ depth) cenv self (+ pc (len c))))))))

; a clause's body: its locals the arguments (and the rest), its closure above them
(defun vcs2-body (cl pc)
  (let* ((n (nfix (car cl))) (nl (if (restp cl) (1+ n) n)))
    (append (vcs2-compile (cadr cl) (1+ nl) (count-from 0 nl) nl pc nil) (list (list :ret)))))

; every clause of every function, one after another: (code . entries)
(defun vcs2-clauses (cls pc)
  (if (atom cls)
      (cons nil nil)
    (let* ((c (vcs2-body (car cls) pc))
           (rest (vcs2-clauses (cdr cls) (+ pc (len c)))))
      (cons (append c (car rest))
            (cons (if (restp (car cls)) (list (nfix (caar cls)) pc :rest) (list (nfix (caar cls)) pc))
                  (cdr rest))))))

(defun vcs2-defs (defs pc)
  (if (atom defs)
      (cons nil nil)
    (let* ((c (vcs2-clauses (cdar defs) pc))
           (rest (vcs2-defs (cdr defs) (+ pc (len (car c))))))
      (cons (append (car c) (car rest))
            (cons (cons (caar defs) (cdr c)) (cdr rest))))))

(defun vcs2-program (e defs)
  (let* ((main (append (vcs2-compile e 0 nil nil 0 nil) (list (list :ret))))
         (rest (vcs2-defs defs (len main))))
    (cons (append main (car rest)) (cdr rest))))

(defun vcs2-answer (s)
  (if (eq (car s) :thrown) (cons :thrown (nth 0 (cadddr s))) (cons :val (nth 0 (cadddr s)))))

(defun vcs2-run-program (e defs steps)
  (vcs2-answer (vcs2-run (vcs2-program e defs) (list 0 0 0 nil nil) steps)))

; ---- AS A CHECK ----------------------------------------------------------------------
;
; an executable runtime for the checks: a few list and arithmetic ops, and
; a division that throws on zero. The theorems are about prim unconstrained.

(defun prim-impl (op vals)
  (declare (xargs :guard t))
  (case op
    (:first (if (consp vals) (if (consp (car vals)) (car (car vals)) nil) nil))
    (:rest (if (consp vals) (if (consp (car vals)) (cdr (car vals)) nil) nil))
    (:empty (if (consp vals) (if (consp (car vals)) nil t) t))
    (:count (if (consp vals) (len (car vals)) 0))
    (:div (if (and (consp vals) (consp (cdr vals)) (rationalp (car vals)) (rationalp (cadr vals))
                   (not (equal (cadr vals) 0)))
              (floor (car vals) (cadr vals))
            (cons :throw :arith)))
    ;; a call of what is not a closure: here nothing else is callable
    (:invoke (cons :throw :not-fn))
    (otherwise nil)))

(defattach prim prim-impl)

(defconst *x2-defs*
  '(; variadic: the sum of all its arguments, by a loop over the rest
    (vsum (0 (:loop ((:local 0) (:const 0))
                    (:if (:prim :empty (:local 1)) (:local 2)
                         (:recur (:prim :rest (:local 1)) (:add (:local 2) (:prim :first (:local 1))))))
             :rest))
    ; multi-arity: one, two, or one and any more
    (f2 (1 (:add (:local 0) (:const 100)))
        (2 (:add (:local 0) (:local 1)))
        (1 (:add (:local 0) (:prim :count (:local 1))) :rest))
    ; throws its argument
    (thr (1 (:throw (:local 0))))
    ; a loop that throws when it reaches 3
    (to3 (0 (:loop ((:const 0))
                   (:if (:lt (:local 0) (:const 3)) (:recur (:add (:local 0) (:const 1))) (:throw (:const :three))))))))

(defmacro check-x2 (e)
  `(assert-event (equal (vcs2-run-program ',e *x2-defs* 100000)
                        (mx2 ',e nil nil *x2-defs* 1000))))

(defmacro check-x2-is (e want)
  `(assert-event (and (equal (mx2 ',e nil nil *x2-defs* 1000) ',want)
                      (equal (vcs2-run-program ',e *x2-defs* 100000) ',want))))

(check-x2-is (:callv (:mkclo vsum) (:const 1) (:const 2) (:const 3) (:const 4)) (:val . 10))
(check-x2-is (:callv (:mkclo vsum)) (:val . 0))
(check-x2-is (:callv (:mkclo f2) (:const 5)) (:val . 105))
(check-x2-is (:callv (:mkclo f2) (:const 5) (:const 6)) (:val . 11))
(check-x2-is (:callv (:mkclo f2) (:const 5) (:const 6) (:const 7)) (:val . 7))
(check-x2-is (:callv (:mkclo f2)) (:thrown . :arity))
(check-x2-is (:try (:callv (:mkclo f2)) (:local 0)) (:val . :arity))
(check-x2-is (:callv (:const 3) (:const 1)) (:thrown . :not-fn))
(check-x2-is (:try (:throw (:const 7)) (:add (:local 0) (:const 1))) (:val . 8))
(check-x2-is (:throw (:const 3)) (:thrown . 3))
(check-x2-is (:try (:callv (:mkclo thr) (:const 9)) (:add (:local 0) (:const 1))) (:val . 10))
(check-x2-is (:try (:callv (:mkclo to3)) (:local 0)) (:val . :three))
(check-x2-is (:try (:prim :div (:const 7) (:const 0)) (:local 0)) (:val . :arith))
(check-x2-is (:prim :div (:const 7) (:const 2)) (:val . 3))
; apply: the spread call, fixed and variadic, the arity error from it;
; apply of what is no closure, and :callv's call of apply, the runtime's
(check-x2-is (:applyv (:const :apply) (:mkclo f2) (:const 5) (:const (6))) (:val . 11))
(check-x2-is (:applyv (:const :apply) (:mkclo f2) (:const (5 6 7 8))) (:val . 8))
(check-x2-is (:applyv (:const :apply) (:mkclo vsum) (:const 1) (:const 2) (:const (3 4))) (:val . 10))
(check-x2-is (:applyv (:const :apply) (:mkclo vsum) (:const nil)) (:val . 0))
(check-x2-is (:applyv (:const :apply) (:mkclo f2) (:const nil)) (:thrown . :arity))
(check-x2-is (:applyv (:const :apply) (:const 3) (:const (1))) (:thrown . :not-fn))
(check-x2-is (:callv (:const :apply) (:mkclo f2) (:const (5 6))) (:thrown . :not-fn))
(check-x2-is (:applyv (:mkclo f2) (:const 5) (:const 6)) (:val . 11))
(check-x2-is (:let (:const 1) (:applyv (:const :apply) (:mkclo vsum) (:local 0) (:add (:local 0) (:const 1)) (:const (10))))
             (:val . 13))
; a try inside a let, its value below the let's local; a throw past two calls
(check-x2-is (:let (:const 1) (:add (:local 0) (:try (:add (:const 1) (:callv (:mkclo thr) (:const 5))) (:local 1))))
             (:val . 6))
; finally, desugared: F runs on both ways out, the try's own value kept
(check-x2-is (:let (:try (:const 4) (:throw (:local 0))) (:add (:local 0) (:const 0))) (:val . 4))
(check-x2 (:try (:let (:const 2) (:loop ((:const 0)) (:if (:lt (:local 1) (:const 5))
                                                      (:recur (:add (:local 1) (:const 1)))
                                                      (:throw (:local 0)))))
                (:add (:local 0) (:const 40))))
; well formed, and a recur across a try not
(assert-event (x2defs-ok *x2-defs*))
(assert-event (not (x2wf '(:loop ((:const 0)) (:try (:recur (:const 1)) (:const 2))) 0 nil)))

; clotran's VM, formally (PLAN step 30): THE CALL, as both machines
; will make it. model/vm-call.lisp's calls name their callee statically;
; Clojure's do not. Here a function is a VALUE -- a closure: which code,
; and the values it captured -- the callee is read from a register at
; run time, a call with the wrong number of arguments is an error, and
; a body reads what it captured THROUGH its closure, which the call
; leaves in the callee's frame. Nothing is copied into a frame per call
; but the record that says where to return (clotran's call copied a
; closure's captures into registers every time, ct_stack_frame).
;
; THE FRAME is the same for the register machine and the stack machine
; (model/vm-stack.lisp): a base on the one value stack and a return
; record (pc, the caller's base, where the answer goes). The arguments
; are evaluated into the registers the callee's frame begins at, the
; closure into the next, so the call moves NO value: callee register i
; is the caller's register base+i already. A stack machine evaluates its
; arguments onto its stack top, which is the same place; this book's
; protocol is what both build on.

(in-package "ACL2")

(include-book "vm-call")

; ---- VALUES ---------------------------------------------------------------
; a closure: (:clo f caps), f the function's name in the table, caps the
; captured values
(defun clo (f caps) (list :clo f caps))
(defun clop (v) (and (consp v) (eq (car v) :clo) (consp (cdr v)) (consp (cddr v))))
(defun clo-f (v) (cadr v))
(defun clo-caps (v) (caddr v))

; ---- THE MEANING ----------------------------------------------------------
;
; stage 1's (:const v) (:local i) (:if c then else) (:let init body)
; (:add a b) (:lt a b), and
;   (:capt i)           the current function's captured value i
;   (:mkclo f e1 .. ek) a closure of function f capturing e1 .. ek
;   (:callv fe a1 .. an) call the closure fe evaluates to
; defs: f -> (n body), body's locals 0..n-1 its arguments. An answer is
; (:val . v), (:out) when fuel ran out, (:err) when a call's callee is not
; a closure of that arity -- clj's ClassCastException and ArityException.

(defun errp (r) (eq (car r) :err))

(mutual-recursion
 (defun mc (e env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     (:const (cons :val (cadr e)))
     (:local (cons :val (nth (nfix (cadr e)) env)))
     (:capt (cons :val (nth (nfix (cadr e)) caps)))
     (:if (let ((rc (mc (cadr e) env caps defs fuel)))
            (cond ((not (valp rc)) rc)
                  ((truthy (val rc)) (mc (caddr e) env caps defs fuel))
                  (t (mc (cadddr e) env caps defs fuel)))))
     (:let (let ((ri (mc (cadr e) env caps defs fuel)))
             (if (valp ri) (mc (caddr e) (append env (list (val ri))) caps defs fuel) ri)))
     ((:add :lt)
      (let ((ra (mc (cadr e) env caps defs fuel)))
        (if (not (valp ra))
            ra
          (let ((rb (mc (caddr e) env caps defs fuel)))
            (cond ((not (valp rb)) rb)
                  ((eq (car e) :add) (cons :val (+ (fix (val ra)) (fix (val rb)))))
                  (t (cons :val (bool (< (rfix (val ra)) (rfix (val rb)))))))))))
     (:mkclo (let ((rs (mc-args (cddr e) env caps defs fuel)))
               (if (valp rs) (cons :val (clo (cadr e) (val rs))) rs)))
     (:callv (let ((rs (mc-args (cddr e) env caps defs fuel)))
               (if (not (valp rs))
                   rs
                 (let ((rf (mc (cadr e) env caps defs fuel)))
                   (cond ((not (valp rf)) rf)
                         ((not (clop (val rf))) (list :err))
                         (t (let ((def (cdr (assoc-eq (clo-f (val rf)) defs))))
                              (cond ((not (consp def)) (list :err))
                                    ((not (equal (len (val rs)) (nfix (car def)))) (list :err))
                                    ((zp fuel) (list :out))
                                    (t (mc (cadr def) (val rs) (clo-caps (val rf)) defs (1- fuel)))))))))))
     (otherwise (cons :val nil))))
 (defun mc-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       (cons :val nil)
     (let ((r (mc (car es) env caps defs fuel)))
       (if (not (valp r))
           r
         (let ((rs (mc-args (cdr es) env caps defs fuel)))
           (if (valp rs) (cons :val (cons (val r) (val rs))) rs)))))))

; ---- THE MACHINE ----------------------------------------------------------
;
; model/vm-call.lisp's state (pc fb regs ctl) and its instructions but
; :call, and
;   (:mkclo d f a k)       register d := a closure of f capturing a..a+k-1
;   (:capt d self i)       register d := capture i of the closure in self
;   (:callv d nb n self)   call the closure in register nb+self, its
;                          arguments in nb..nb+n-1: the callee's frame
;                          BEGINS at nb, so they are its registers
;                          0..n-1 and the closure its register self = n,
;                          where they already are. Its answer goes to d.
; A program is (code . fntab), fntab: f -> (entry n). A call of what is
; not a closure, or of the wrong arity, stops the machine at pc :err.

(defun regs-from (fb a k regs)
  (declare (xargs :measure (nfix k)))
  (if (zp k) nil (cons (reg fb a regs) (regs-from fb (1+ (nfix a)) (1- k) regs))))

(defun vc-step (prog s)
  (let* ((code (car prog)) (fntab (cdr prog))
         (pc (car s)) (fb (nfix (cadr s))) (regs (caddr s)) (ctl (cadddr s)))
    (if (not (natp pc))
        s
      (let ((ins (nth pc code)))
        (case (car ins)
          (:loadk (list (1+ pc) fb (setreg fb (cadr ins) (caddr ins) regs) ctl))
          (:move (list (1+ pc) fb (setreg fb (cadr ins) (reg fb (caddr ins) regs) regs) ctl))
          (:add (list (1+ pc) fb
                      (setreg fb (cadr ins) (+ (fix (reg fb (caddr ins) regs))
                                               (fix (reg fb (cadddr ins) regs))) regs)
                      ctl))
          (:lt (list (1+ pc) fb
                     (setreg fb (cadr ins) (bool (< (rfix (reg fb (caddr ins) regs))
                                                    (rfix (reg fb (cadddr ins) regs)))) regs)
                     ctl))
          (:jmpf (if (truthy (reg fb (cadr ins) regs))
                     (list (1+ pc) fb regs ctl)
                   (list (nfix (caddr ins)) fb regs ctl)))
          (:jmp (list (nfix (cadr ins)) fb regs ctl))
          (:mkclo (list (1+ pc) fb
                        (setreg fb (cadr ins) (clo (caddr ins) (regs-from fb (cadddr ins) (car (cddddr ins)) regs)) regs)
                        ctl))
          (:capt (list (1+ pc) fb
                       (setreg fb (cadr ins) (nth (nfix (cadddr ins)) (clo-caps (reg fb (caddr ins) regs))) regs)
                       ctl))
          (:callv (let* ((d (cadr ins)) (nb (nfix (caddr ins))) (n (nfix (cadddr ins)))
                         (self (nfix (car (cddddr ins))))
                         (c (reg fb (+ nb self) regs))
                         (ent (and (clop c) (cdr (assoc-equal (clo-f c) fntab)))))
                    (if (or (not (clop c)) (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                        (list :err fb regs ctl)
                      ;; THE CALL: a record, a base, a jump -- no value moves
                      (list (nfix (car ent)) (+ fb nb) regs (cons (list (1+ pc) fb d) ctl)))))
          (:ret (let ((v (reg fb (cadr ins) regs)))
                  (if (atom ctl)
                      (list pc fb (setreg 0 0 v regs) ctl)
                    (let* ((rec (car ctl)) (rfb (nfix (cadr rec))))
                      (list (nfix (car rec)) rfb (setreg rfb (caddr rec) v regs) (cdr ctl))))))
          (otherwise s))))))

(defun vc-run (prog s n)
  (if (zp n) s (vc-run prog (vc-step prog s) (1- n))))

; ---- THE COMPILER ---------------------------------------------------------
;
; vc-compile e d f cenv pc: code leaving e's value in register d, its
; temporaries from f up, locals where cenv says; a body's own closure is
; in register self (nil in main, which has no captures). A call
; evaluates its arguments into f .. f+n-1 and the callee into f+n, then
; calls with the callee's frame at f: nothing moves.

(mutual-recursion
 (defun vc-compile (e d f cenv self pc)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :loadk d (cadr e))))
     (:local (list (list :move d (nth (nfix (cadr e)) cenv))))
     (:capt (if (natp self) (list (list :capt d self (cadr e))) (list (list :loadk d nil))))
     (:if (let* ((cc (vc-compile (cadr e) f (1+ f) cenv self pc))
                 (pc1 (+ pc (len cc) 1))
                 (tc (vc-compile (caddr e) d f cenv self pc1))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (vc-compile (cadddr e) d f cenv self pc2)))
            (append cc (list (list :jmpf f pc2)) tc
                    (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (vc-compile (cadr e) f (1+ f) cenv self pc))
                  (bc (vc-compile (caddr e) d (1+ f) (append cenv (list f)) self (+ pc (len ic)))))
             (append ic bc)))
     ((:add :lt)
      (let* ((ac (vc-compile (cadr e) f (1+ f) cenv self pc))
             (bc (vc-compile (caddr e) (1+ f) (+ 2 f) cenv self (+ pc (len ac)))))
        (append ac bc (list (list (car e) d f (1+ f))))))
     (:mkclo (let* ((k (len (cddr e)))
                    (ac (vc-compile-args (cddr e) f cenv self pc)))
               (append ac (list (list :mkclo d (cadr e) f k)))))
     (:callv (let* ((n (len (cddr e)))
                    (ac (vc-compile-args (cddr e) f cenv self pc))
                    (fc (vc-compile (cadr e) (+ f n) (+ f n 1) cenv self (+ pc (len ac)))))
               (append ac fc (list (list :callv d f n n)))))
     (otherwise (list (list :loadk d nil)))))
 (defun vc-compile-args (es f cenv self pc)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (vc-compile (car es) f (1+ f) cenv self pc)))
       (append c (vc-compile-args (cdr es) (1+ f) cenv self (+ pc (len c))))))))

; a body: its arguments in registers 0..n-1, its closure in n, its
; answer in n+1, then a return
(defun vc-body (def pc)
  (let ((n (nfix (car def))))
    (append (vc-compile (cadr def) (1+ n) (+ 2 n) (count-from 0 n) n pc)
            (list (list :ret (1+ n))))))

(defun vc-defs (defs pc)
  (if (atom defs)
      (cons nil nil)
    (let* ((c (vc-body (cdar defs) pc))
           (rest (vc-defs (cdr defs) (+ pc (len c)))))
      (cons (append c (car rest))
            (cons (list (caar defs) pc (nfix (cadar defs))) (cdr rest))))))

(defun vc-program (e defs)
  ; entries no longer go into the code (a call reads its callee's from
  ; the table), so one pass lays everything out
  (let* ((main (append (vc-compile e 0 1 nil nil 0) (list (list :ret 0))))
         (rest (vc-defs defs (len main))))
    (cons (append main (car rest)) (cdr rest))))

(defun vc-answer (s)
  (if (eq (car s) :err) (list :err) (cons :val (nth 0 (caddr s)))))

(defun vc-run-program (e defs steps)
  (vc-answer (vc-run (vc-program e defs) (list 0 0 nil nil) steps)))

; ---- EXAMPLES: the machine against the meaning ----------------------------

(defconst *clo-defs*
  '((inc1 1 (:add (:local 0) (:const 1)))
    ;; adds what it captured to its argument
    (adder 1 (:add (:local 0) (:capt 0)))
    ;; calls the closure it is given on its other argument
    (apply1 2 (:callv (:local 0) (:local 1)))
    ;; makes an adder over its argument, and calls it
    (mk 2 (:callv (:mkclo adder (:local 0)) (:local 1)))
    ;; counts down through a closure of itself it carries as a capture
    (down 1 (:if (:lt (:local 0) (:const 1))
                 (:const 0)
                 (:add (:const 1) (:callv (:mkclo down) (:add (:local 0) (:const -1))))))))

(defmacro check-vc (e)
  `(assert-event (equal (vc-run-program ',e *clo-defs* 100000)
                        (mc ',e nil nil *clo-defs* 1000))))

(check-vc (:callv (:mkclo inc1) (:const 41)))
(check-vc (:callv (:mkclo adder (:const 10)) (:const 5)))
(check-vc (:callv (:mkclo apply1) (:mkclo adder (:const 2)) (:const 3)))
(check-vc (:callv (:mkclo mk) (:const 7) (:const 8)))
(check-vc (:callv (:mkclo down) (:const 6)))
(check-vc (:let (:mkclo adder (:const 100)) (:add (:callv (:local 0) (:const 1)) (:callv (:local 0) (:const 2)))))
;; the wrong arity, and a call of what is not a closure, are errors in both
(check-vc (:callv (:mkclo inc1) (:const 1) (:const 2)))
(check-vc (:callv (:const 5) (:const 1)))
(assert-event (equal (mc '(:callv (:const 5) (:const 1)) nil nil *clo-defs* 10) '(:err)))

; ---- THE CALL MOVES NOTHING -----------------------------------------------
;
; vm-call's :call copies n arguments into the callee's frame. Here the
; registers a :callv leaves are the registers it found, every one: the
; call's cost is the record and the jump, whatever n is.

(defthm callv-moves-no-value
  (implies (and (natp (car s)) (equal (car (nth (car s) (car prog))) :callv)
                (not (eq (car (vc-step prog s)) :err)))
           (equal (caddr (vc-step prog s)) (caddr s))))

; ---- THE SAME CALL ON A STACK MACHINE ---------------------------------------
;
; The stack machine clotran would run is not model/vm-stack.lisp's, whose
; frames are lists apart: it is ONE value stack, as the register
; machine's, its operands pushed above the frame's locals. Its call is
; this book's call: the arguments are pushed, then the closure, and the
; callee's frame begins at the first argument -- its locals 0..n-1 the
; arguments, its local n the closure, where they already are. A return
; leaves the answer where the callee's frame began, on the caller's
; operand stack. The frame is a base and a return record, as above.
;
; A state is (pc fb sp stk ctl): stk the one stack, fb the frame's base,
; sp the next free slot. Local i is stk[fb+i].
;   (:push v) (:load i) (:add) (:lt) (:jmpf target) (:jmp target)
;   (:slide)            the top value replaces the one below it: a let's
;                       local goes when its body has answered
;   (:mkclo f k)        pop k captures, push the closure
;   (:capt self i)      push capture i of the closure in local self
;   (:callv n)          the closure on top, its n arguments below it
;   (:ret)              the answer on top, to where this frame began

(defun sreg (i stk) (nth (nfix i) stk))
(defun ssetreg (i v stk) (update-nth (nfix i) v stk))

(defun stk-from (a k stk)
  (declare (xargs :measure (nfix k)))
  (if (zp k) nil (cons (sreg a stk) (stk-from (1+ (nfix a)) (1- k) stk))))

(defun vcs-step (prog s)
  (let* ((code (car prog)) (fntab (cdr prog))
         (pc (car s)) (fb (nfix (cadr s))) (sp (nfix (caddr s))) (stk (cadddr s)) (ctl (car (cddddr s))))
    (if (not (natp pc))
        s
      (let ((ins (nth pc code)))
        (case (car ins)
          (:push (list (1+ pc) fb (1+ sp) (ssetreg sp (cadr ins) stk) ctl))
          (:load (list (1+ pc) fb (1+ sp) (ssetreg sp (sreg (+ fb (nfix (cadr ins))) stk) stk) ctl))
          (:add (if (< sp 2) s
                  (list (1+ pc) fb (1- sp)
                        (ssetreg (- sp 2) (+ (fix (sreg (- sp 2) stk)) (fix (sreg (1- sp) stk))) stk) ctl)))
          (:lt (if (< sp 2) s
                 (list (1+ pc) fb (1- sp)
                       (ssetreg (- sp 2) (bool (< (rfix (sreg (- sp 2) stk)) (rfix (sreg (1- sp) stk)))) stk) ctl)))
          (:slide (if (< sp 2) s
                    (list (1+ pc) fb (1- sp) (ssetreg (- sp 2) (sreg (1- sp) stk) stk) ctl)))
          (:jmpf (if (zp sp) s
                   (if (truthy (sreg (1- sp) stk))
                       (list (1+ pc) fb (1- sp) stk ctl)
                     (list (nfix (cadr ins)) fb (1- sp) stk ctl))))
          (:jmp (list (nfix (cadr ins)) fb sp stk ctl))
          (:mkclo (let ((k (nfix (caddr ins))))
                    (if (< sp k) s
                      (list (1+ pc) fb (1+ (- sp k))
                            (ssetreg (- sp k) (clo (cadr ins) (stk-from (- sp k) k stk)) stk) ctl))))
          (:capt (list (1+ pc) fb (1+ sp)
                       (ssetreg sp (nth (nfix (caddr ins)) (clo-caps (sreg (+ fb (nfix (cadr ins))) stk))) stk)
                       ctl))
          (:callv (let* ((n (nfix (cadr ins))))
                    (if (< sp (1+ n))
                        s
                      (let* ((c (sreg (1- sp) stk))
                             (ent (and (clop c) (cdr (assoc-equal (clo-f c) fntab)))))
                        (if (or (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                            (list :err fb sp stk ctl)
                          ;; THE CALL: the frame begins at the first argument
                          (list (nfix (car ent)) (- sp (1+ n)) sp stk (cons (list (1+ pc) fb) ctl)))))))
          (:ret (if (zp sp) s
                  (let ((v (sreg (1- sp) stk)))
                    (if (atom ctl)
                        (list pc fb 1 (ssetreg 0 v stk) ctl)
                      (let ((rec (car ctl)))
                        (list (nfix (car rec)) (nfix (cadr rec)) (1+ fb) (ssetreg fb v stk) (cdr ctl)))))))
          (otherwise s))))))

(defun vcs-run (prog s n)
  (if (zp n) s (vcs-run prog (vcs-step prog s) (1- n))))

; vcs-compile e depth cenv self pc: code pushing e's value. depth is how
; many slots this frame holds above its base when it starts, cenv each
; local's slot, self the closure's (nil in main).
(mutual-recursion
 (defun vcs-compile (e depth cenv self pc)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :push (cadr e))))
     (:local (list (list :load (nth (nfix (cadr e)) cenv))))
     (:capt (if (natp self) (list (list :capt self (cadr e))) (list (list :push nil))))
     (:if (let* ((cc (vcs-compile (cadr e) depth cenv self pc))
                 (pc1 (+ pc (len cc) 1))
                 (tc (vcs-compile (caddr e) depth cenv self pc1))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (vcs-compile (cadddr e) depth cenv self pc2)))
            (append cc (list (list :jmpf pc2)) tc (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (vcs-compile (cadr e) depth cenv self pc))
                  (bc (vcs-compile (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (len ic)))))
             (append ic bc (list (list :slide)))))
     ((:add :lt)
      (let* ((ac (vcs-compile (cadr e) depth cenv self pc))
             (bc (vcs-compile (caddr e) (1+ depth) cenv self (+ pc (len ac)))))
        (append ac bc (list (list (car e))))))
     (:mkclo (let ((ac (vcs-compile-args (cddr e) depth cenv self pc)))
               (append ac (list (list :mkclo (cadr e) (len (cddr e)))))))
     (:callv (let* ((n (len (cddr e)))
                    (ac (vcs-compile-args (cddr e) depth cenv self pc))
                    (fc (vcs-compile (cadr e) (+ depth n) cenv self (+ pc (len ac)))))
               (append ac fc (list (list :callv n)))))
     (otherwise (list (list :push nil)))))
 (defun vcs-compile-args (es depth cenv self pc)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (vcs-compile (car es) depth cenv self pc)))
       (append c (vcs-compile-args (cdr es) (1+ depth) cenv self (+ pc (len c))))))))

; a body: arguments in slots 0..n-1, its closure in n, operands above
(defun vcs-body (def pc)
  (let ((n (nfix (car def))))
    (append (vcs-compile (cadr def) (1+ n) (count-from 0 n) n pc) (list (list :ret)))))

(defun vcs-defs (defs pc)
  (if (atom defs)
      (cons nil nil)
    (let* ((c (vcs-body (cdar defs) pc))
           (rest (vcs-defs (cdr defs) (+ pc (len c)))))
      (cons (append c (car rest))
            (cons (list (caar defs) pc (nfix (cadar defs))) (cdr rest))))))

(defun vcs-program (e defs)
  (let* ((main (append (vcs-compile e 0 nil nil 0) (list (list :ret))))
         (rest (vcs-defs defs (len main))))
    (cons (append main (car rest)) (cdr rest))))

(defun vcs-answer (s)
  (if (eq (car s) :err) (list :err) (cons :val (nth 0 (cadddr s)))))

(defun vcs-run-program (e defs steps)
  (vcs-answer (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) steps)))

(defmacro check-vcs (e)
  `(assert-event (equal (vcs-run-program ',e *clo-defs* 100000)
                        (mc ',e nil nil *clo-defs* 1000))))

(check-vcs (:callv (:mkclo inc1) (:const 41)))
(check-vcs (:callv (:mkclo adder (:const 10)) (:const 5)))
(check-vcs (:callv (:mkclo apply1) (:mkclo adder (:const 2)) (:const 3)))
(check-vcs (:callv (:mkclo mk) (:const 7) (:const 8)))
(check-vcs (:callv (:mkclo down) (:const 6)))
(check-vcs (:let (:mkclo adder (:const 100)) (:add (:callv (:local 0) (:const 1)) (:callv (:local 0) (:const 2)))))
(check-vcs (:callv (:mkclo inc1) (:const 1) (:const 2)))
(check-vcs (:callv (:const 5) (:const 1)))

; the stack machine's call, too, moves no value: the stack is as it was
(defthm vcs-callv-moves-no-value
  (implies (and (natp (car s)) (equal (car (nth (car s) (car prog))) :callv)
                (not (eq (car (vcs-step prog s)) :err)))
           (equal (cadddr (vcs-step prog s)) (cadddr s))))

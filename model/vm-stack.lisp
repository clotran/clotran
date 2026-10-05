; clotran's VM, formally (PLAN step 28). Stage 3 again, as a STACK
; machine: the same language and the same meaning as model/vm-call.lisp,
; included from it, so the two machines answer to one definition of what
; a program means and can be compared on everything else (James,
; 2026-10-04: model both, then choose).
;
; THE MACHINE is an operand-stack machine: a frame is a locals vector and an
; operand stack; instructions take their operands from the stack and
; push their result. A state is
;   (pc locals ops ctl)
; and a call pops its arguments, saves the caller's (pc locals ops) on
; ctl, and starts the callee with the arguments as its locals and an
; empty operand stack; a return pops the answer, restores the caller,
; and pushes it. A let stores into the next local slot.
;
; ROOTING here: a computation's live values are the frames' locals in
; scope and their operand stacks -- the check wipes every local slot
; from the caller's scope up at each return, as vm-call's wipes
; registers above the frame's top.

(in-package "ACL2")

(include-book "vm-call")

; ---- THE MACHINE ------------------------------------------------------------
;
;   (:push v)          push v
;   (:load i)          push local i
;   (:store i)         pop into local i
;   (:add) (:lt)       pop b, pop a, push a+b or a<b
;   (:jmpf target)     pop; jump when it is false or nil
;   (:jmp target)
;   (:call target n)   pop n arguments, the last on top; call
;   (:ret)             pop the answer; return it, or with no caller
;                      halt with it alone on the stack

(defun s-step (prog s)
  (let* ((pc (nfix (car s))) (locals (cadr s)) (ops (caddr s)) (ctl (cadddr s))
         (ins (nth pc prog)))
    (case (car ins)
      (:push (list (1+ pc) locals (cons (cadr ins) ops) ctl))
      (:load (list (1+ pc) locals (cons (nth (nfix (cadr ins)) locals) ops) ctl))
      (:store (list (1+ pc) (update-nth (nfix (cadr ins)) (car ops) locals) (cdr ops) ctl))
      (:add (list (1+ pc) locals (cons (+ (fix (cadr ops)) (fix (car ops))) (cddr ops)) ctl))
      (:lt (list (1+ pc) locals (cons (bool (< (rfix (cadr ops)) (rfix (car ops)))) (cddr ops)) ctl))
      (:jmpf (if (truthy (car ops))
                 (list (1+ pc) locals (cdr ops) ctl)
               (list (nfix (cadr ins)) locals (cdr ops) ctl)))
      (:jmp (list (nfix (cadr ins)) locals ops ctl))
      (:call (let ((n (nfix (caddr ins))))
               (list (nfix (cadr ins)) (reverse (take n ops)) nil
                     (cons (list (1+ pc) locals (nthcdr n ops)) ctl))))
      (:ret (if (atom ctl)
                (list pc locals (list (car ops)) ctl)        ; halted
              (let ((rec (car ctl)))
                (list (nfix (car rec)) (cadr rec) (cons (car ops) (caddr rec)) (cdr ctl)))))
      (otherwise s))))

(defun s-run (prog s n)
  (if (zp n) s (s-run prog (s-step prog s) (1- n))))

; ---- THE COMPILER -------------------------------------------------------------
;
; s-compile e n pc fnpcs: code pushing e's value; n locals are in scope,
; so a let stores into slot n

(mutual-recursion
 (defun s-compile (e n pc fnpcs)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :push (cadr e))))
     (:local (list (list :load (cadr e))))
     (:if (let* ((cc (s-compile (cadr e) n pc fnpcs))
                 (pc1 (+ pc (len cc) 1))
                 (tc (s-compile (caddr e) n pc1 fnpcs))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (s-compile (cadddr e) n pc2 fnpcs)))
            (append cc (list (list :jmpf pc2)) tc (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (s-compile (cadr e) n pc fnpcs))
                  (bc (s-compile (caddr e) (1+ (nfix n)) (+ pc (len ic) 1) fnpcs)))
             (append ic (list (list :store n)) bc)))
     ((:add :lt)
      (let* ((ac (s-compile (cadr e) n pc fnpcs))
             (bc (s-compile (caddr e) n (+ pc (len ac)) fnpcs)))
        (append ac bc (list (list (car e))))))
     (:call (let ((ac (s-compile-args (cddr e) n pc fnpcs)))
              (append ac (list (list :call (cdr (assoc-eq (cadr e) fnpcs)) (len (cddr e)))))))
     (otherwise (list (list :push nil)))))
 (defun s-compile-args (es n pc fnpcs)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (s-compile (car es) n pc fnpcs)))
       (append c (s-compile-args (cdr es) n (+ pc (len c)) fnpcs))))))

(defun s-body-code (def entry fnpcs)
  (append (s-compile (cadr def) (nfix (car def)) entry fnpcs) (list (list :ret))))

(defun s-lay-out (defs pc fnpcs)
  (if (atom defs)
      nil
    (cons (cons (caar defs) pc)
          (s-lay-out (cdr defs) (+ pc (len (s-body-code (cdar defs) pc fnpcs))) fnpcs))))

(defun s-compile-defs (defs fnpcs pc)
  (if (atom defs)
      nil
    (let ((c (s-body-code (cdar defs) pc fnpcs)))
      (append c (s-compile-defs (cdr defs) fnpcs (+ pc (len c)))))))

(defun s-compile-program (e defs)
  (let* ((main0 (append (s-compile e 0 0 nil) (list (list :ret))))
         (dummy (s-lay-out defs (len main0) nil))
         (fnpcs (s-lay-out defs (len main0) dummy))
         (main (append (s-compile e 0 0 fnpcs) (list (list :ret)))))
    (append main (s-compile-defs defs fnpcs (len main)))))

(defun s-run-program (e defs steps)
  (s-run (s-compile-program e defs) (list 0 nil nil nil) steps))

(defun s-answer (s) (car (caddr s)))

; ---- ROOTING, as a check ----------------------------------------------------
;
; after each return to a caller, every local slot from top up is wiped:
; the slots a let has finished with, and the rest of the vector

; one step, then, if it returned to a caller, the caller's local slots
; from top up wiped; top nil wipes nothing, so this IS s-step there
(defun s-w-step (prog s top)
  (let ((s2 (s-step prog s)))
    (if (and top (eq (car (nth (nfix (car s)) prog)) :ret) (consp (cadddr s)))
        (list (car s2) (wipe-above (nfix top) (cadr s2)) (caddr s2) (cadddr s2))
      s2)))

(defun s-run-wiping (prog s n top)
  (if (zp n) s (s-run-wiping prog (s-w-step prog s top) (1- n) top)))

; ---- EXAMPLES: the machine against the meaning, vm-call's own ---------------
;
; and one more, run on both machines: a local read AFTER a call returns,
; which a stack machine cannot keep on its operand stack instead

(defconst *more-exprs*
  '((:let (:const 5) (:add (:call double (:local 0)) (:local 0)))))

(assert-event (check-all *more-exprs*))

(defconst *all-exprs* (append *exprs* *more-exprs*))

(defun s-check-all (es)
  (if (atom es) t
    (and (equal (s-answer (s-run-program (car es) *defs* 10000))
                (val (m (car es) nil *defs* 1000)))
         (s-check-all (cdr es)))))

(assert-event (s-check-all *all-exprs*))

(defun s-check-all-wiping (es top)
  (if (atom es) t
    (and (equal (s-answer (s-run-wiping (s-compile-program (car es) *defs*) (list 0 nil nil nil) 10000 top))
                (val (m (car es) nil *defs* 1000)))
         (s-check-all-wiping (cdr es) top))))

(assert-event (s-check-all-wiping *all-exprs* 2))

; THE CHECK HAS TEETH: *more-exprs* reads local 0 after a call returns,
; so wiping every local slot (top 0) must change an answer
(defun s-some-differs-wiping (es top)
  (if (atom es) nil
    (or (not (equal (s-answer (s-run-wiping (s-compile-program (car es) *defs*) (list 0 nil nil nil) 10000 top))
                    (val (m (car es) nil *defs* 1000))))
        (s-some-differs-wiping (cdr es) top))))

(assert-event (s-some-differs-wiping *all-exprs* 0))

; ---- THE SAME PROGRAMS, BOTH MACHINES: code size and steps ------------------
;
; instructions in the program, and steps to the answer, register machine
; then stack machine -- the first numbers of the comparison PLAN step 28
; asks for

(defun steps-to-halt (run-fn prog s n)
  (declare (xargs :mode :program))
  (if (zp n) nil
    (let ((s2 (if (eq run-fn :reg) (vm-step prog s) (s-step prog s))))
      (if (equal s2 s) 0
        (let ((k (steps-to-halt run-fn prog s2 (1- n)))) (and k (1+ k)))))))

(defun compare-machines (es)
  (declare (xargs :mode :program))
  (if (atom es) nil
    (let ((rp (compile-program (car es) *defs*)) (sp (s-compile-program (car es) *defs*)))
      (cons (list (len rp) (len sp)
                  (steps-to-halt :reg rp (list 0 0 nil nil) 10000)
                  (steps-to-halt :stack sp (list 0 nil nil nil) 10000))
            (compare-machines (cdr es))))))

; clotran's VM, formally (PLAN step 28). Stage 3: calls and frames, on
; top of stage 1's core (model/vm.lisp). This book is the DESIGN as
; running definitions and checked examples; the theorems follow in their
; own books, each keeping the ones before.
;
; THE LANGUAGE adds (:call f a1 .. an) over a table of first-order
; functions, defs: f -> (n body), body's locals 0..n-1 the arguments.
; Calls may recurse without end, so the meaning takes fuel, as stage 2's.
;
; THE MACHINE has ONE value stack, regs, flat, as the thread's frame
; stack is (PLAN step 28, item 2): no per-frame heap object. A state is
;   (pc fb regs ctl)
; fb the current frame's base: register r is regs[fb + r]. A call puts
; the callee's frame right above the caller's live registers -- the
; call instruction says where, the caller's first free register --
; copies the arguments into it, and pushes a return record (pc, base,
; destination register) on ctl; a return writes the answer into the
; caller's register and pops. Nothing a computation still needs is held
; anywhere but regs and ctl: the ROOTING property, stated here as a
; check and proved later -- wiping every register above the live top,
; at any call or return, changes no answer. That is what clotran's
; collector relies on when it scans the value stack and nothing else;
; a value held only in a host local (as F_RETHROW held a message,
; 2026-10-04) has no place in this machine at all.

(in-package "ACL2")

(defun truthy (x) (not (or (null x) (eq x :false))))
(defun bool (b) (if b t :false))
(defun val (r) (cdr r))
(defun valp (r) (eq (car r) :val))

; ---- THE MEANING ----------------------------------------------------------
;
; stage 1's (:const v) (:local i) (:if c then else) (:let init body)
; (:add a b) (:lt a b), and (:call f args...)

(mutual-recursion
 (defun m (e env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count e))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     (:const (cons :val (cadr e)))
     (:local (cons :val (nth (nfix (cadr e)) env)))
     (:if (let ((rc (m (cadr e) env defs fuel)))
            (cond ((not (valp rc)) (list :out))
                  ((truthy (val rc)) (m (caddr e) env defs fuel))
                  (t (m (cadddr e) env defs fuel)))))
     (:let (let ((ri (m (cadr e) env defs fuel)))
             (if (valp ri) (m (caddr e) (append env (list (val ri))) defs fuel) (list :out))))
     ((:add :lt)
      (let ((ra (m (cadr e) env defs fuel)) (rb (m (caddr e) env defs fuel)))
        (cond ((not (and (valp ra) (valp rb))) (list :out))
              ((eq (car e) :add) (cons :val (+ (fix (val ra)) (fix (val rb)))))
              (t (cons :val (bool (< (rfix (val ra)) (rfix (val rb)))))))))
     (:call (let ((rs (m-args (cddr e) env defs fuel))
                  (def (cdr (assoc-eq (cadr e) defs))))
              (cond ((not (valp rs)) (list :out))
                    ((zp fuel) (list :out))
                    ((not (equal (len (val rs)) (nfix (car def)))) (list :out))
                    (t (m (cadr def) (val rs) defs (1- fuel))))))
     (otherwise (cons :val nil))))
 ; the arguments, left to right: (:val . values) or (:out)
 (defun m-args (es env defs fuel)
   (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count es))))
   (if (atom es)
       (cons :val nil)
     (let ((r (m (car es) env defs fuel)))
       (if (not (valp r))
           (list :out)
         (let ((rs (m-args (cdr es) env defs fuel)))
           (if (valp rs) (cons :val (cons (val r) (val rs))) (list :out))))))))

; ---- THE MACHINE ----------------------------------------------------------
;
; stage 1's (:loadk d v) (:move d s) (:add d a b) (:lt d a b)
; (:jmpf s target) (:jmp target), every register frame-relative, and
;   (:call d target a n nb)  the callee's base is fb+nb, its registers
;                            0..n-1 the caller's a..a+n-1, copied
;   (:ret s)                 the answer, register s, into the caller's
;                            destination; with no caller, the machine
;                            halts with it in register 0 of frame 0
; regs grows as a frame needs it: writing past its end extends it with
; nils (update-nth's own meaning).

(defun reg (fb r regs) (nth (+ (nfix fb) (nfix r)) regs))
(defun setreg (fb r v regs) (update-nth (+ (nfix fb) (nfix r)) v regs))

; the callee's n arguments, copied from the caller's registers a..
(defun copy-args (fb a nb i n regs)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n))
      regs
    (copy-args fb a nb (1+ i) n
               (setreg (+ (nfix fb) (nfix nb)) i (reg fb (+ (nfix a) i) regs) regs))))

(defun vm-step (prog s)
  (let* ((pc (nfix (car s))) (fb (nfix (cadr s))) (regs (caddr s)) (ctl (cadddr s))
         (ins (nth pc prog)))
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
      (:call (let ((d (cadr ins)) (target (caddr ins)) (a (cadddr ins))
                   (n (car (cddddr ins))) (nb (cadr (cddddr ins))))
               (list (nfix target) (+ fb (nfix nb))
                     (copy-args fb a nb 0 n regs)
                     (cons (list (1+ pc) fb d) ctl))))
      (:ret (let ((v (reg fb (cadr ins) regs)))
              (if (atom ctl)
                  (list pc fb (setreg 0 0 v regs) ctl)      ; halted: the answer in r0
                (let* ((rec (car ctl)) (rpc (car rec)) (rfb (nfix (cadr rec))) (d (caddr rec)))
                  (list (nfix rpc) rfb (setreg rfb d v regs) (cdr ctl))))))
      (otherwise s))))

(defun vm-run (prog s n)
  (if (zp n) s (vm-run prog (vm-step prog s) (1- n))))

; ---- THE COMPILER ---------------------------------------------------------
;
; vm-compile e d f cenv pc fnpcs: code leaving e's value in register d,
; its temporaries from f up, locals where cenv says; pc is where the code
; will sit (jump targets are absolute); fnpcs maps a function to its
; entry pc. A call evaluates its arguments into f, f+1, .. and calls with
; the callee's frame at f+n: above everything this frame holds live.

(mutual-recursion
 (defun vm-compile (e d f cenv pc fnpcs)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :loadk d (cadr e))))
     (:local (list (list :move d (nth (nfix (cadr e)) cenv))))
     (:if (let* ((cc (vm-compile (cadr e) f (1+ f) cenv pc fnpcs))
                 (pc1 (+ pc (len cc) 1))
                 (tc (vm-compile (caddr e) d f cenv pc1 fnpcs))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (vm-compile (cadddr e) d f cenv pc2 fnpcs)))
            (append cc (list (list :jmpf f pc2)) tc
                    (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (vm-compile (cadr e) f (1+ f) cenv pc fnpcs))
                  (bc (vm-compile (caddr e) d (1+ f) (append cenv (list f)) (+ pc (len ic)) fnpcs)))
             (append ic bc)))
     ((:add :lt)
      (let* ((ac (vm-compile (cadr e) f (1+ f) cenv pc fnpcs))
             (bc (vm-compile (caddr e) (1+ f) (+ 2 f) cenv (+ pc (len ac)) fnpcs)))
        (append ac bc (list (list (car e) d f (1+ f))))))
     (:call (let* ((n (len (cddr e)))
                   (ac (vm-compile-args (cddr e) f cenv pc fnpcs)))
              (append ac (list (list :call d (cdr (assoc-eq (cadr e) fnpcs)) f n (+ f n))))))
     (otherwise (list (list :loadk d nil)))))
 ; each argument into the next register from f, the later ones' temporaries
 ; above it
 (defun vm-compile-args (es f cenv pc fnpcs)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (vm-compile (car es) f (1+ f) cenv pc fnpcs)))
       (append c (vm-compile-args (cdr es) (1+ f) cenv (+ pc (len c)) fnpcs))))))

; A whole program: the main expression (with no locals), its answer in
; register 0 and a halting return, then each function's body -- its
; locals the arguments in registers 0..n-1, its answer in register n,
; then a return. Two passes: the first fixes where each function
; starts, the second compiles with those entries.

; the registers i, i+1, .. n-1: a function's locals are its arguments,
; in registers 0..n-1
(defun count-from (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) nil (cons i (count-from (1+ i) n))))

(defun body-code* (def entry fnpcs)
  (let ((n (nfix (car def))))
    (append (vm-compile (cadr def) n (1+ n) (count-from 0 n) entry fnpcs)
            (list (list :ret n)))))

(defun lay-out (defs pc fnpcs)
  ; the entries: each function's at pc, the next after its code
  (if (atom defs)
      nil
    (cons (cons (caar defs) pc)
          (lay-out (cdr defs) (+ pc (len (body-code* (cdar defs) pc fnpcs))) fnpcs))))

(defun compile-defs (defs fnpcs pc)
  (if (atom defs)
      nil
    (let ((c (body-code* (cdar defs) pc fnpcs)))
      (append c (compile-defs (cdr defs) fnpcs (+ pc (len c)))))))

(defun compile-program (e defs)
  ; main's code is fixed-length whatever the entries' values, so lay out
  ; with dummies, then compile for real at the same positions
  (let* ((main0 (append (vm-compile e 0 1 nil 0 nil) (list (list :ret 0))))
         (dummy (lay-out defs (len main0) nil))
         (fnpcs (lay-out defs (len main0) dummy))
         (main (append (vm-compile e 0 1 nil 0 fnpcs) (list (list :ret 0)))))
    (append main (compile-defs defs fnpcs (len main)))))

(defun run-program (e defs steps)
  (vm-run (compile-program e defs) (list 0 0 nil nil) steps))

; the answer, once the machine has halted (a :ret with no caller)
(defun answer (s) (nth 0 (caddr s)))

; ---- ROOTING, as a check --------------------------------------------------
;
; vm-run-wiping: as vm-run, but after every return to a caller, every
; register from the caller's base plus top up is wiped to nil. top is a
; bound on the registers a frame holds live across a call, which the
; compiler knows (model/vm-call-proof.lisp says which bound suffices).
; If the machine kept a value only in a dead register, the answer would
; change.

(defun wipe-above (k regs)
  (if (atom regs) regs
    (if (zp k) (cons nil (wipe-above 0 (cdr regs)))
      (cons (car regs) (wipe-above (1- k) (cdr regs))))))

; one step, then, if it returned to a caller, registers from (fb + top)
; up wiped; top nil wipes nothing, so this IS vm-step there and one
; proof covers the machine and the rooting claim both
(defun w-step (prog s top)
  (let ((s2 (vm-step prog s)))
    (if (and top (eq (car (nth (nfix (car s)) prog)) :ret) (consp (cadddr s)))
        (list (car s2) (cadr s2) (wipe-above (+ (nfix (cadr s2)) (nfix top)) (caddr s2)) (cadddr s2))
      s2)))

(defun vm-run-wiping (prog s n top)
  (if (zp n) s (vm-run-wiping prog (w-step prog s top) (1- n) top)))

; ---- EXAMPLES: the machine against the meaning ----------------------------

(defconst *defs*
  '((double 1 (:add (:local 0) (:local 0)))
    (sum3 3 (:add (:local 0) (:add (:local 1) (:local 2))))
    ; fact-ish without multiply: tri(n) = n + tri(n-1), tri(0) = 0
    (tri 1 (:if (:lt (:local 0) (:const 1))
                (:const 0)
                (:add (:local 0) (:call tri (:add (:local 0) (:const -1))))))
    ; calls nested in arguments, and a let around a call
    (twice 1 (:let (:call double (:local 0)) (:call double (:local 1))))))

(defconst *exprs*
  '((:call double (:const 21))
    (:call sum3 (:const 1) (:const 2) (:const 3))
    (:call tri (:const 10))
    (:call twice (:const 5))
    (:add (:call double (:const 1)) (:call tri (:const 4)))
    (:let (:const 7) (:call sum3 (:local 0) (:call double (:local 0)) (:const 1)))
    (:if (:lt (:call tri (:const 3)) (:const 7)) (:const :small) (:const :big))))

(defun check-all (es)
  (if (atom es) t
    (and (equal (answer (run-program (car es) *defs* 10000))
                (val (m (car es) nil *defs* 1000)))
         (check-all (cdr es)))))

(assert-event (check-all *exprs*))

; the same answers with every dead register wiped after each return,
; the frame's top taken generously (a frame of these uses fewer than 12)
(defun check-all-wiping (es)
  (if (atom es) t
    (and (equal (answer (vm-run-wiping (compile-program (car es) *defs*) (list 0 0 nil nil) 10000 12))
                (val (m (car es) nil *defs* 1000)))
         (check-all-wiping (cdr es)))))

(assert-event (check-all-wiping *exprs*))

; THE CHECK HAS TEETH: declare the frame's top too low -- one register,
; where (:add (:call ..) (:call ..)) holds the first call's answer in
; register 1 across the second -- and wiping must change some answer.
; A value kept where the collector does not look is exactly this, which
; is how F_RETHROW's message was lost (2026-10-04).
(defun some-differs-wiping (es top)
  (if (atom es) nil
    (or (not (equal (answer (vm-run-wiping (compile-program (car es) *defs*) (list 0 0 nil nil) 10000 top))
                    (val (m (car es) nil *defs* 1000))))
        (some-differs-wiping (cdr es) top))))

(assert-event (some-differs-wiping *exprs* 1))

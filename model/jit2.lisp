; clotran's JIT, formally (PLAN step 31, stage 2a: static stack depth).
;
; In stack bytecode the depth of the stack at each instruction is fixed
; by the code: every path to an instruction arrives with the same number
; of slots above the frame's base. The JIT infers that depth for every pc
; (dinfer, a worklist over the code, linear), and then CHECKS it
; (dcheck), as a bytecode verifier does: each instruction's successors
; get the depth it leaves, its operands and the slots it reads are below
; it, and each function's entry is at its arity plus one (the arguments
; and the closure). Code that passes is translated with every slot
; addressed as FB + depth: the stack-top register and its adjustments
; are gone. Code that does not pass is translated by stage 1
; (model/jit.lisp), so the JIT is right whatever bytecode it is given.

(in-package "ACL2")

(include-book "jit")

; ---- THE DEPTH OF EVERY INSTRUCTION ----------------------------------------------

; the successors of pc and the depth each is reached with
(defun dsuccs (pc ins d)
  (case (car ins)
    ((:push :load :capt) (list (cons (1+ pc) (1+ d))))
    ((:add :lt :slide) (list (cons (1+ pc) (- d 1))))
    (:jmpf (list (cons (1+ pc) (- d 1)) (cons (nfix (cadr ins)) (- d 1))))
    (:jmp (list (cons (nfix (cadr ins)) d)))
    (:mkclo (list (cons (1+ pc) (+ 1 (- d (nfix (caddr ins)))))))
    (:callv (list (cons (1+ pc) (- d (nfix (cadr ins))))))
    (otherwise nil)))

; set the depths not yet known, and put their pcs to do
(defun dset (pairs dmap work)
  (if (atom pairs)
      (mv dmap work)
    (let ((p (car (car pairs))) (d (cdr (car pairs))))
      (if (and (natp p) (natp d) (not (natp (nth p dmap))))
          (dset (cdr pairs) (update-nth p d dmap) (cons p work))
        (dset (cdr pairs) dmap work)))))

; THE INFERENCE: each pc is set once and done once, so the fuel -- twice
; the code and the entries -- is never what stops it on code it accepts
(defun dloop (code dmap work fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (atom work))
      dmap
    (let* ((pc (car work)) (d (nth pc dmap)))
      (mv-let (dmap2 work2)
        (dset (dsuccs pc (nth pc code) (nfix d)) dmap (cdr work))
        (dloop code dmap2 work2 (1- fuel))))))

(defun dentries (fntab dmap work)
  (if (atom fntab)
      (mv dmap work)
    (let ((pc (cadar fntab)) (n (caddar fntab)))
      (if (and (natp pc) (not (natp (nth pc dmap))))
          (dentries (cdr fntab) (update-nth pc (1+ (nfix n)) dmap) (cons pc work))
        (dentries (cdr fntab) dmap work)))))

(defun dinfer (prog)
  (mv-let (dmap work) (dentries (cdr prog) (list 0) (list 0))
    (dloop (car prog) dmap work (* 2 (+ 1 (len (car prog)) (len (cdr prog)))))))

; ---- THE CHECK -------------------------------------------------------------------

(defun succs-ok (pairs dmap ncode)
  (if (atom pairs)
      t
    (and (natp (car (car pairs))) (< (car (car pairs)) ncode)
         (equal (nth (car (car pairs)) dmap) (cdr (car pairs)))
         (succs-ok (cdr pairs) dmap ncode))))

; one instruction at depth d: what it reads is below the top, and its
; successors have the depth it leaves
(defun dok (pc ins d dmap ncode)
  (and (case (car ins)
         ((:load :capt) (< (nfix (cadr ins)) d))
         ((:add :lt :slide) (<= 2 d))
         ((:jmpf :ret) (<= 1 d))
         (:mkclo (<= (nfix (caddr ins)) d))
         (:callv (<= (1+ (nfix (cadr ins))) d))
         (otherwise t))
       (succs-ok (dsuccs pc ins d) dmap ncode)))

(defun dcheck-code (rest pc dmap ncode)
  (if (atom rest)
      t
    (and (or (not (natp (nth pc dmap))) (dok pc (car rest) (nth pc dmap) dmap ncode))
         (dcheck-code (cdr rest) (1+ pc) dmap ncode))))

(defun dcheck-entries (fntab dmap)
  (if (atom fntab)
      t
    (and (consp (car fntab)) (consp (cdar fntab)) (consp (cddar fntab))
         (natp (cadar fntab))
         (equal (nth (cadar fntab) dmap) (1+ (nfix (caddar fntab))))
         (dcheck-entries (cdr fntab) dmap))))

; no depth past the code
(defun dbounded (dmap pc ncode)
  (if (atom dmap)
      t
    (and (or (not (natp (car dmap))) (< pc ncode)) (dbounded (cdr dmap) (1+ pc) ncode))))

(defun dcheck (prog dmap)
  (and (consp (car prog))
       (equal (nth 0 dmap) 0)
       (dbounded dmap 0 (len (car prog)))
       (dcheck-code (car prog) 0 dmap (len (car prog)))
       (dcheck-entries (cdr prog) dmap)))

; ---- THE TRANSLATION ---------------------------------------------------------------

; each bytecode's block at depth d: every slot FB + its depth, no SP
(defun jblock2 (ins d tgt)
  (case (car ins)
    (:push (list (list :movi 0 (cadr ins)) (list :str 0 :fb d)))
    (:load (list (list :ldr 0 :fb (nfix (cadr ins))) (list :str 0 :fb d)))
    (:add (list (list :ldr 0 :fb (- d 2)) (list :ldr 1 :fb (- d 1)) (list :add 0 0 1) (list :str 0 :fb (- d 2))))
    (:lt (list (list :ldr 0 :fb (- d 2)) (list :ldr 1 :fb (- d 1)) (list :lt 0 0 1) (list :str 0 :fb (- d 2))))
    (:slide (list (list :ldr 0 :fb (- d 1)) (list :str 0 :fb (- d 2))))
    (:jmpf (list (list :ldr 0 :fb (- d 1)) (list :cbf 0 tgt)))
    (:jmp (list (list :b tgt)))
    (:mkclo (list (list :mkclod (cadr ins) (nfix (caddr ins)) d)))
    (:capt (list (list :ldr 0 :fb (nfix (cadr ins))) (list :capt 0 (nfix (caddr ins))) (list :str 0 :fb d)))
    (:callv (list (list :calld (nfix (cadr ins)) d)))
    (:ret (list (list :retd d)))
    (otherwise (list (list :stuck)))))

(defun blen2 (ins) (len (jblock2 ins 0 0)))

(defun npc2 (p code)
  (if (zp p) 0 (+ (blen2 (car code)) (npc2 (1- p) (cdr code)))))

(defun jtarget2 (ins code) (npc2 (nfix (cadr ins)) code))

(defun jit2-code (rest pc code dmap)
  (if (atom rest)
      nil
    (append (jblock2 (car rest) (nfix (nth pc dmap)) (jtarget2 (car rest) code))
            (jit2-code (cdr rest) (1+ pc) code dmap))))

(defun jit2-fntab (fntab code)
  (if (atom fntab)
      nil
    (cons (list* (caar fntab) (npc2 (nfix (cadar fntab)) code) (cddar fntab))
          (jit2-fntab (cdr fntab) code))))

(defun jit2-checked (prog dmap)
  (cons (jit2-code (car prog) 0 (car prog) dmap) (jit2-fntab (cdr prog) (car prog))))

; THE JIT: the depth-addressed code when the check passes, stage 1's
; otherwise
(defun jit2 (prog)
  (let ((dmap (dinfer prog)))
    (if (dcheck prog dmap) (jit2-checked prog dmap) (jit prog))))

; ---- THE SIMULATION, as a check ----------------------------------------------------
;
; A bytecode state embeds in a machine state as in stage 1, but the
; machine keeps no stack top: the bytecode's is FB + the depth at its pc.

(defun emb2-ctl (ctl code)
  (if (atom ctl)
      ctl
    (cons (list (npc2 (nfix (caar ctl)) code) (cadar ctl)) (emb2-ctl (cdr ctl) code))))

(defun emb2 (s code)
  (list (if (natp (car s)) (npc2 (car s) code) (car s))
        (cadr s) (cadddr s) (emb2-ctl (car (cddddr s)) code)))

(defun nview2 (ns) (list (car ns) (cadr ns) (cadddr ns) (car (cddddr ns))))

(defun j2clk (prog s n)
  (if (zp n)
      0
    (+ (if (natp (car s)) (blen2 (nth (car s) (car prog))) 1)
       (j2clk prog (vcs-step prog s) (1- n)))))

(defun jit2-run-program (e defs steps)
  (let ((ns (nrun (jit2 (vcs-program e defs)) (list 0 0 0 nil nil nil) steps)))
    (vcs-answer (nview ns))))

(defmacro check-jit2 (e steps)
  `(assert-event
    (let* ((prog (vcs-program ',e *jit-defs*)) (s0 (list 0 0 0 nil nil)))
      (and (dcheck prog (dinfer prog))
           (equal (nview2 (nrun (jit2 prog) (append s0 (list nil)) (j2clk prog s0 ,steps)))
                  (emb2 (vcs-run prog s0 ,steps) (car prog)))
           (equal (jit2-run-program ',e *jit-defs* 400000)
                  (mc ',e nil nil *jit-defs* 1000))))))

(check-jit2 (:callv (:mkclo inc1) (:const 41)) 50)
(check-jit2 (:callv (:mkclo adder (:const 10)) (:const 5)) 50)
(check-jit2 (:callv (:mkclo apply1) (:mkclo adder (:const 2)) (:const 3)) 50)
(check-jit2 (:callv (:mkclo mk) (:const 7) (:const 8)) 50)
(check-jit2 (:callv (:mkclo down) (:const 6)) 400)
(check-jit2 (:let (:mkclo adder (:const 100)) (:add (:callv (:local 0) (:const 1)) (:callv (:local 0) (:const 2)))) 100)
(check-jit2 (:callv (:mkclo inc1) (:const 1) (:const 2)) 50)
(check-jit2 (:callv (:const 5) (:const 1)) 50)
(check-jit2 (:callv (:mkclo fib) (:const 10)) 5000)
(check-jit2 (:callv (:mkclo tri) (:const 20)) 2000)

; ---- STAGE 2a AGAINST STAGE 1 AND THE REGISTER SHAPE --------------------------------

(defun stk2-mem (ins)
  (case (car ins) ((:push :jmpf) 1) ((:load :slide :capt) 2) ((:add :lt) 3) (otherwise 0)))

(defun vcs-tally2 (prog s n acc)
  (declare (xargs :mode :program))
  (if (or (zp n) (not (natp (car s))) (eq (car s) :err))
      acc
    (let ((ins (nth (car s) (car prog))))
      (if (and (eq (car ins) :ret) (atom (car (cddddr s))))
          acc
        (vcs-tally2 prog (vcs-step prog s) (1- n)
                    (list (1+ (car acc)) (+ (cadr acc) (blen2 ins)) (+ (caddr acc) (stk2-mem ins))))))))

(defun compare-jit2 (e)
  (declare (xargs :mode :program))
  (list :stack-stage1 (vcs-tally (vcs-program e *jit-defs*) (list 0 0 0 nil nil) 1000000 '(0 0 0))
        :stack-stage2a (vcs-tally2 (vcs-program e *jit-defs*) (list 0 0 0 nil nil) 1000000 '(0 0 0))
        :register (vc-tally (vc-program e *jit-defs*) (list 0 0 nil nil) 1000000 '(0 0 0))))

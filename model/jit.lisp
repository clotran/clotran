; clotran's JIT, formally (PLAN step 31, stage 1: the baseline JIT).
;
; The stack VM's bytecode (vm-closure.lisp's vcs-step) translated, one
; instruction at a time, into machine code for a model CPU: a block of
; loads, stores and register arithmetic per bytecode, with the frame
; base and the stack top held in two machine registers (FB and SP).
; Calls, returns and closure-making stay single instructions, as in
; the real JIT they are calls into the runtime.
;
; What the translation removes is DISPATCH: an interpreter fetches each
; bytecode, decodes it and jumps to its handler, every time it runs it.
; Here that is done once, when translating; the machine runs straight
; through a block and on into the next. What stays is the work: every
; stack slot is still in memory, and the stack top is still adjusted at
; run time. Stage 2 (static stack depth, the top slots in machine
; registers) removes those.
;
; THE CPU is the instructions the emitter will produce, on arm64 and
; x86-64, and no more:
;
;   (:movi r v)        x[r] := the constant v
;   (:ldr r b off)     x[r] := mem[b + off], b one of :fb :sp
;   (:str r b off)     mem[b + off] := x[r]
;   (:addsp k)         SP := SP + k
;   (:add d a b)       x[d] := x[a] + x[b]
;   (:lt d a b)        x[d] := x[a] < x[b]
;   (:cbf r t)         to t if x[r] is false or nil
;   (:b t)             to t
;   (:mkclo f k)       the runtime: the top k slots made a closure of f
;   (:capt d i)        x[d] := capture i of the closure in x[d]
;   (:call n)          the runtime: call the closure on top, n arguments
;   (:ret)             the runtime: return the top to the frame's base
;
; and for stage 2 (model/jit2.lisp), where the stack depth at every
; instruction is known when translating and SP is not kept:
;
;   (:mov d s)         x[d] := x[s]
;   (:mkclod f k d)    :mkclo with the top at FB + d
;   (:calld n d)       :call with the top at FB + d
;   (:retd d)          :ret with the top at FB + d
;
; A machine state is (pc fb sp mem ctl x): x the scratch registers.

(in-package "ACL2")

(include-book "vm-closure")

; ---- THE MACHINE -------------------------------------------------------------------

(defun xr (r x) (nth (nfix r) x))
(defun xset (r v x) (update-nth (nfix r) v x))
(defun nbase (b fb sp) (if (eq b :fb) fb sp))

(defun nstep (nprog ns)
  (let* ((code (car nprog)) (fntab (cdr nprog))
         (pc (car ns)) (fb (nfix (cadr ns))) (sp (nfix (caddr ns))) (stk (cadddr ns))
         (ctl (car (cddddr ns))) (x (cadr (cddddr ns))))
    (if (not (natp pc))
        ns
      (let ((ins (nth pc code)))
        (case (car ins)
          (:movi (list (1+ pc) fb sp stk ctl (xset (cadr ins) (caddr ins) x)))
          (:ldr (list (1+ pc) fb sp stk ctl
                      (xset (cadr ins) (nth (nfix (+ (nbase (caddr ins) fb sp) (ifix (cadddr ins)))) stk) x)))
          (:str (list (1+ pc) fb sp
                      (update-nth (nfix (+ (nbase (caddr ins) fb sp) (ifix (cadddr ins)))) (xr (cadr ins) x) stk)
                      ctl x))
          (:addsp (list (1+ pc) fb (nfix (+ sp (ifix (cadr ins)))) stk ctl x))
          (:add (list (1+ pc) fb sp stk ctl
                      (xset (cadr ins) (+ (fix (xr (caddr ins) x)) (fix (xr (cadddr ins) x))) x)))
          (:lt (list (1+ pc) fb sp stk ctl
                     (xset (cadr ins) (bool (< (rfix (xr (caddr ins) x)) (rfix (xr (cadddr ins) x)))) x)))
          (:cbf (if (truthy (xr (cadr ins) x))
                    (list (1+ pc) fb sp stk ctl x)
                  (list (nfix (caddr ins)) fb sp stk ctl x)))
          (:b (list (nfix (cadr ins)) fb sp stk ctl x))
          (:mkclo (let ((k (nfix (caddr ins))))
                    (if (< sp k) ns
                      (list (1+ pc) fb (1+ (- sp k))
                            (ssetreg (- sp k) (clo (cadr ins) (stk-from (- sp k) k stk)) stk) ctl x))))
          (:capt (list (1+ pc) fb sp stk ctl
                       (xset (cadr ins) (nth (nfix (caddr ins)) (clo-caps (xr (cadr ins) x))) x)))
          (:call (let ((n (nfix (cadr ins))))
                   (if (< sp (1+ n))
                       ns
                     (let* ((c (sreg (1- sp) stk))
                            (ent (and (clop c) (cdr (assoc-equal (clo-f c) fntab)))))
                       (if (or (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                           (list :err fb sp stk ctl x)
                         (list (nfix (car ent)) (- sp (1+ n)) sp stk (cons (list (1+ pc) fb) ctl) x))))))
          (:mov (list (1+ pc) fb sp stk ctl (xset (cadr ins) (xr (caddr ins) x) x)))
          (:mkclod (let ((k (nfix (caddr ins))) (d (nfix (cadddr ins))))
                     (if (< d k) ns
                       (list (1+ pc) fb sp
                             (ssetreg (+ fb (- d k)) (clo (cadr ins) (stk-from (+ fb (- d k)) k stk)) stk) ctl x))))
          (:calld (let ((n (nfix (cadr ins))) (d (nfix (caddr ins))))
                    (if (< d (1+ n))
                        ns
                      (let* ((c (sreg (+ fb (1- d)) stk))
                             (ent (and (clop c) (cdr (assoc-equal (clo-f c) fntab)))))
                        (if (or (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                            (list :err fb sp stk ctl x)
                          (list (nfix (car ent)) (+ fb (- d (1+ n))) sp stk (cons (list (1+ pc) fb) ctl) x))))))
          (:retd (let ((d (nfix (cadr ins))))
                   (if (zp d) ns
                     (let ((v (sreg (+ fb (1- d)) stk)))
                       (if (atom ctl)
                           (list pc fb sp (ssetreg 0 v stk) ctl x)
                         (let ((rec (car ctl)))
                           (list (nfix (car rec)) (nfix (cadr rec)) sp (ssetreg fb v stk) (cdr ctl) x)))))))
          (:ret (if (zp sp) ns
                  (let ((v (sreg (1- sp) stk)))
                    (if (atom ctl)
                        (list pc fb 1 (ssetreg 0 v stk) ctl x)
                      (let ((rec (car ctl)))
                        (list (nfix (car rec)) (nfix (cadr rec)) (1+ fb) (ssetreg fb v stk) (cdr ctl) x))))))
          (otherwise ns))))))

(defun nrun (nprog ns n)
  (if (zp n) ns (nrun nprog (nstep nprog ns) (1- n))))

; ---- THE TRANSLATION ---------------------------------------------------------------

; each bytecode's block; t is a bytecode pc, translated by the caller
(defun jblock (ins tgt)
  (case (car ins)
    (:push (list (list :movi 0 (cadr ins)) (list :str 0 :sp 0) (list :addsp 1)))
    (:load (list (list :ldr 0 :fb (nfix (cadr ins))) (list :str 0 :sp 0) (list :addsp 1)))
    (:add (list (list :ldr 0 :sp -2) (list :ldr 1 :sp -1) (list :add 0 0 1) (list :str 0 :sp -2) (list :addsp -1)))
    (:lt (list (list :ldr 0 :sp -2) (list :ldr 1 :sp -1) (list :lt 0 0 1) (list :str 0 :sp -2) (list :addsp -1)))
    (:slide (list (list :ldr 0 :sp -1) (list :str 0 :sp -2) (list :addsp -1)))
    (:jmpf (list (list :ldr 0 :sp -1) (list :addsp -1) (list :cbf 0 tgt)))
    (:jmp (list (list :b tgt)))
    (:mkclo (list (list :mkclo (cadr ins) (nfix (caddr ins)))))
    (:capt (list (list :ldr 0 :fb (nfix (cadr ins))) (list :capt 0 (nfix (caddr ins)))
                 (list :str 0 :sp 0) (list :addsp 1)))
    (:callv (list (list :call (nfix (cadr ins)))))
    (:ret (list (list :ret)))
    (otherwise (list (list :stuck)))))

; a block's length depends only on its opcode
(defun blen (ins) (len (jblock ins 0)))

; where bytecode pc p begins in the machine code: the blocks before it
(defun npc (p code)
  (if (zp p) 0 (+ (blen (car code)) (npc (1- p) (cdr code)))))

(defun jtarget (ins code) (npc (nfix (cadr ins)) code))

(defun jit-code (rest code)
  (if (atom rest)
      nil
    (append (jblock (car rest) (jtarget (car rest) code)) (jit-code (cdr rest) code))))

; a function's entry: its bytecode entry's block
(defun jit-fntab (fntab code)
  (if (atom fntab)
      nil
    (cons (list* (caar fntab) (npc (nfix (cadar fntab)) code) (cddar fntab))
          (jit-fntab (cdr fntab) code))))

(defun jit (prog) (cons (jit-code (car prog) (car prog)) (jit-fntab (cdr prog) (car prog))))

; ---- THE SIMULATION, as a check ----------------------------------------------------
;
; A bytecode state embeds in a machine state: the same frame base, top,
; stack and return records, its pcs (and the records' pcs) moved to
; their blocks. The scratch registers carry nothing between blocks.

(defun emb-ctl (ctl code)
  (if (atom ctl)
      ctl
    (cons (list (npc (nfix (caar ctl)) code) (cadar ctl)) (emb-ctl (cdr ctl) code))))

(defun emb (s code)
  (list (if (natp (car s)) (npc (car s) code) (car s))
        (cadr s) (caddr s) (cadddr s) (emb-ctl (car (cddddr s)) code)))

; the machine state, its scratch registers dropped
(defun nview (ns) (list (car ns) (cadr ns) (caddr ns) (cadddr ns) (car (cddddr ns))))

; the machine steps the bytecode run takes: its blocks' lengths
(defun jclk (prog s n)
  (if (zp n)
      0
    (+ (if (natp (car s)) (blen (nth (car s) (car prog))) 1)
       (jclk prog (vcs-step prog s) (1- n)))))

(defun jit-run-program (e defs steps)
  (let ((ns (nrun (jit (vcs-program e defs)) (list 0 0 0 nil nil nil) steps)))
    (vcs-answer (nview ns))))

(defconst *jit-defs*
  (append *clo-defs*
          '((fib 1 (:if (:lt (:local 0) (:const 2))
                        (:local 0)
                        (:add (:callv (:mkclo fib) (:add (:local 0) (:const -1)))
                              (:callv (:mkclo fib) (:add (:local 0) (:const -2))))))
            (tri 1 (:if (:lt (:local 0) (:const 1))
                        (:const 0)
                        (:add (:local 0) (:callv (:mkclo tri) (:add (:local 0) (:const -1)))))))))

; each check: the bytecode run, block for block, is the machine's run
(defmacro check-jit (e steps)
  `(assert-event
    (let* ((prog (vcs-program ',e *jit-defs*)) (s0 (list 0 0 0 nil nil)))
      (and (equal (nview (nrun (jit prog) (append s0 (list nil)) (jclk prog s0 ,steps)))
                  (emb (vcs-run prog s0 ,steps) (car prog)))
           (equal (jit-run-program ',e *jit-defs* 400000)
                  (mc ',e nil nil *jit-defs* 1000))))))

(check-jit (:callv (:mkclo inc1) (:const 41)) 50)
(check-jit (:callv (:mkclo adder (:const 10)) (:const 5)) 50)
(check-jit (:callv (:mkclo apply1) (:mkclo adder (:const 2)) (:const 3)) 50)
(check-jit (:callv (:mkclo mk) (:const 7) (:const 8)) 50)
(check-jit (:callv (:mkclo down) (:const 6)) 400)
(check-jit (:let (:mkclo adder (:const 100)) (:add (:callv (:local 0) (:const 1)) (:callv (:local 0) (:const 2)))) 100)
(check-jit (:callv (:mkclo inc1) (:const 1) (:const 2)) 50)
(check-jit (:callv (:const 5) (:const 1)) 50)
(check-jit (:callv (:mkclo fib) (:const 10)) 5000)
(check-jit (:callv (:mkclo tri) (:const 20)) 2000)

; ---- REGISTER OR STACK BYTECODE, UNDER THIS JIT ------------------------------------
;
; A baseline JIT runs one block per bytecode executed, so what each
; bytecode shape costs once translated is the count of each opcode
; executed times its block. The register machine's blocks, by the same
; rules (a register is a slot in memory at FB + r):
;   :loadk 2  :move 2  :add/:lt 4  :jmpf 2  :jmp 1  :mkclo 1  :capt 3
;   :callv 1  :ret 1
; and the memory operations among them: a register read or write each.

(defun reg-blen (op)
  (case op ((:loadk :move :jmpf) 2) ((:add :lt) 4) (:capt 3) (otherwise 1)))
(defun reg-mem (op)
  (case op ((:loadk :jmpf) 1) (:move 2) ((:add :lt) 3) (:capt 2) (otherwise 0)))
(defun stk-mem (ins)
  (case (car ins) ((:push :jmpf) 1) ((:load :slide) 2) ((:add :lt) 3) (:capt 2) (otherwise 0)))

; (bytecodes machine-instructions memory-operations) over a run
(defun vcs-tally (prog s n acc)
  (declare (xargs :mode :program))
  (if (or (zp n) (not (natp (car s))) (eq (car s) :err))
      acc
    (let ((ins (nth (car s) (car prog))))
      (if (and (eq (car ins) :ret) (atom (car (cddddr s))))
          acc
        (vcs-tally prog (vcs-step prog s) (1- n)
                   (list (1+ (car acc)) (+ (cadr acc) (blen ins)) (+ (caddr acc) (stk-mem ins))))))))

(defun vc-tally (prog s n acc)
  (declare (xargs :mode :program))
  (if (or (zp n) (not (natp (car s))) (eq (car s) :err))
      acc
    (let ((ins (nth (car s) (car prog))))
      (if (and (eq (car ins) :ret) (atom (cadddr s)))
          acc
        (vc-tally prog (vc-step prog s) (1- n)
                  (list (1+ (car acc)) (+ (cadr acc) (reg-blen (car ins))) (+ (caddr acc) (reg-mem (car ins)))))))))

(defun compare-jit (e)
  (declare (xargs :mode :program))
  (list :stack (vcs-tally (vcs-program e *jit-defs*) (list 0 0 0 nil nil) 1000000 '(0 0 0))
        :register (vc-tally (vc-program e *jit-defs*) (list 0 0 nil nil) 1000000 '(0 0 0))))

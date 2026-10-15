; clotran's JIT for the machine it runs (PLAN step 31, stage 1 over
; model/vmi.lisp, the machine vm_gen.f90 is generated from).
;
; jit.lisp .. jit3.lisp designed the JIT on vm-closure.lisp's small
; machine. This is the same idea on the real one: each bytecode becomes a
; block of native code, translated once, so the running program pays no
; fetch, decode or dispatch for it. A block either does its instruction
; itself or hands the machine to THE STEP the Fortran is generated from
; (vmg_step), then goes on at the block of whatever pc that step left.
;
; Done in native code: push, load, slide, jmpf, jmp -- the moves of
; values between slots and the branches, which are most of the
; instructions a compiled Clojure body executes. Everything else (calls,
; returns, prims, closures, throws, handlers) is the runtime's work
; already, and its block is one call of the step.
;
; Every slot an inline block reads or writes is checked against the
; stack's length first; a check that fails sends the block to the step,
; which does exactly what the interpreter does there (a read past the
; stack is nil, a write past it is an overflow). So a native store or
; load is never out of the stack's memory.
;
; THE NATIVE OPS, each a few arm64 instructions (src/f/vmjit.inc's
; encoder, fuzzed by scripts/fuzz -m vm,jit; the machine's registers hold pc, the frame base and sp):
;
;   (:chk-ix b k)       on to the next op if slot base(b)+k is in the
;                       stack, else the step; b one of :fb :sp
;   (:chk-sp n)         on if sp >= n, else the step
;   (:mov db dk sb sk)  slot base(db)+dk := slot base(sb)+sk
;   (:movc db dk j)     slot base(db)+dk := the pool's constant j
;   (:addsp k)          sp := sp + k
;   (:cbf b k tg)       to block tg if slot base(b)+k is false or nil
;   (:goto tg)          to block tg
;   (:slow)             the step
;
; vmj-block-is: a block run from its pc is one vmi-step. vmj-run-is: the
; native machine, its blocks translated ONCE from the program before the
; run, is vmi-run step for step -- a step changes no code and no pool,
; so the blocks stay the program's.

(in-package "ACL2")

(include-book "vmi")

; ---- THE NATIVE MACHINE ----------------------------------------------------------------

(defun vmj-ix (b k vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (nfix (+ (if (eq b :fb) (nfix (v-fb vmi)) (nfix (v-sp vmi))) (ifix k))))

; a block's ops run from the block of bytecode pc p, to where control
; leaves it: the machine after, its pc the next block's
(defun vmj-exec (ops vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (atom ops)
      vmi
    (let ((op (car ops)))
      (case (car op)
        (:chk-ix (if (< (vmj-ix (cadr op) (caddr op) vmi) (v-stk-length vmi))
                     (vmj-exec (cdr ops) vmi)
                   (vmi-step vmi)))
        (:chk-sp (if (<= (nfix (cadr op)) (nfix (v-sp vmi)))
                     (vmj-exec (cdr ops) vmi)
                   (vmi-step vmi)))
        (:mov (let ((vmi (vmi-sset (vmj-ix (cadr op) (caddr op) vmi)
                                   (vmi-sreg (vmj-ix (cadddr op) (car (cddddr op)) vmi) vmi) vmi)))
                (vmj-exec (cdr ops) vmi)))
        (:movc (let ((vmi (vmi-sset (vmj-ix (cadr op) (caddr op) vmi) (vmi-poolv (cadddr op) vmi) vmi)))
                 (vmj-exec (cdr ops) vmi)))
        (:addsp (let ((vmi (update-v-sp (nfix (+ (nfix (v-sp vmi)) (ifix (cadr op)))) vmi)))
                  (vmj-exec (cdr ops) vmi)))
        (:cbf (if (truthy (vmi-sreg (vmj-ix (cadr op) (caddr op) vmi) vmi))
                  (vmj-exec (cdr ops) vmi)
                (update-v-pc (nfix (cadddr op)) vmi)))
        (:goto (update-v-pc (nfix (cadr op)) vmi))
        (:slow (vmi-step vmi))
        (otherwise vmi)))))

; ---- THE TRANSLATION ---------------------------------------------------------------------

; the block of the instruction at p
(defun vmj-block (p vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((op (vmi-w p 0 vmi)) (a (nfix (vmi-w p 1 vmi))) (nx (1+ (nfix p))))
    (case op
      (1 (if (< a (v-pool-length vmi))
             (list '(:chk-ix :sp 0) (list :movc :sp 0 a) '(:addsp 1) (list :goto nx))
           '((:slow))))
      (2 (list (list :chk-ix :fb a) '(:chk-ix :sp 0) (list :mov :sp 0 :fb a) '(:addsp 1) (list :goto nx)))
      (5 (list '(:chk-sp 2) '(:chk-ix :sp -1) (list :mov :sp -2 :sp -1) '(:addsp -1) (list :goto nx)))
      (6 (list '(:chk-sp 1) '(:chk-ix :sp -1) '(:addsp -1) (list :cbf :sp 0 a) (list :goto nx)))
      (7 (list (list :goto a)))
      (otherwise '((:slow))))))

; the blocks of pcs p .. p+n-1
(defun vmj-translate (p n vmi)
  (declare (xargs :stobjs vmi :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (cons (vmj-block p vmi) (vmj-translate (1+ (nfix p)) (1- n) vmi))))

; enough blocks for every pc the code can hold an instruction at: one per
; word is more than enough (four words an instruction), and past them the
; step does nothing
(defun vmj-ncode (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (v-code-length vmi))

; the native machine: n blocks, each the one its table holds for the pc
(defun vmj-run (tab n vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (zp n)
      vmi
    (let ((vmi (if (equal (v-status vmi) 0) (vmj-exec (nth (nfix (v-pc vmi)) tab) vmi) vmi)))
      (vmj-run tab (1- n) vmi))))

; ---- A BLOCK IS ONE STEP -----------------------------------------------------------------

(defthm vmi-w-nfix
  (equal (vmi-w (nfix p) k vmi) (vmi-w p k vmi))
  :hints (("Goal" :in-theory (enable vmi-w))))

(defthm vmi-w-update-other
  (implies (not (equal i *v-codei*)) (equal (vmi-w p k (update-nth i v vmi)) (vmi-w p k vmi)))
  :hints (("Goal" :in-theory (enable vmi-w))))

(defthm vmi-w-not-natp
  (implies (not (natp p)) (equal (vmi-w p k vmi) (vmi-w 0 k vmi)))
  :hints (("Goal" :in-theory (enable vmi-w))))

; the step at an opcode is that opcode's instruction
(defmacro vmj-step-op (name op fn)
  `(defthm ,name
     (implies (and (equal (v-status vmi) 0) (equal (vmi-w (v-pc vmi) 0 vmi) ,op))
              (equal (vmi-step vmi) (,fn vmi)))
     :hints (("Goal" :in-theory (enable vmi-step)))))

(vmj-step-op vmj-step-push 1 vmi-push)
(vmj-step-op vmj-step-load 2 vmi-load)
(vmj-step-op vmj-step-slide 5 vmi-slide)
(vmj-step-op vmj-step-jmpf 6 vmi-jmpf)
(vmj-step-op vmj-step-jmp 7 vmi-jmp)

(in-theory (disable vmi-step vmi-w))

; an opcode's block, run from its pc, is the step; where a check fails the
; block is the step already, so only the inline path is the instruction's
(defmacro vmj-op-is (name op fn step)
  `(defthm ,name
     (implies (and (equal (v-status vmi) 0) (equal (vmi-w (v-pc vmi) 0 vmi) ,op))
              (equal (vmj-exec (vmj-block (nfix (v-pc vmi)) vmi) vmi) (vmi-step vmi)))
     :hints (("Goal" :in-theory (enable ,fn vmi-sset vmi-sreg vmi-poolv) :use ,step))))

(vmj-op-is vmj-push-is 1 vmi-push vmj-step-push)
(vmj-op-is vmj-load-is 2 vmi-load vmj-step-load)
(vmj-op-is vmj-slide-is 5 vmi-slide vmj-step-slide)
(vmj-op-is vmj-jmpf-is 6 vmi-jmpf vmj-step-jmpf)
(vmj-op-is vmj-jmp-is 7 vmi-jmp vmj-step-jmp)

(defthm vmj-other-is
  (implies (and (equal (v-status vmi) 0) (not (member (vmi-w (v-pc vmi) 0 vmi) '(1 2 5 6 7))))
           (equal (vmj-exec (vmj-block (nfix (v-pc vmi)) vmi) vmi) (vmi-step vmi))))

; from any pc: a negative one reads as 0, as the step reads it
(defthm vmj-block-is
  (implies (equal (v-status vmi) 0)
           (equal (vmj-exec (vmj-block (nfix (v-pc vmi)) vmi) vmi) (vmi-step vmi)))
  :hints (("Goal" :in-theory (disable vmj-exec vmj-block)
           :use (vmj-push-is vmj-load-is vmj-slide-is vmj-jmpf-is vmj-jmp-is vmj-other-is))))

; past the code the step does nothing, and no block is there to run
(defthm vmj-step-past-code
  (implies (<= (vmj-ncode vmi) (nfix (v-pc vmi)))
           (equal (vmi-step vmi) vmi))
  :hints (("Goal" :in-theory (enable vmi-step vmi-w vmj-ncode))))

(defun vmj-ind (i p n)
  (if (or (zp i) (zp n)) (list p n) (vmj-ind (1- i) (1+ (nfix p)) (1- n))))

(defthm nth-vmj-translate
  (implies (and (natp p) (natp i) (< i (nfix n)))
           (equal (nth i (vmj-translate p n vmi)) (vmj-block (+ p i) vmi)))
  :hints (("Goal" :induct (vmj-ind i p n) :in-theory (disable vmj-block) :expand ((vmj-translate p n vmi)))))

(defthm nth-vmj-translate-past
  (implies (and (natp i) (<= (nfix n) i))
           (equal (nth i (vmj-translate p n vmi)) nil))
  :hints (("Goal" :induct (vmj-ind i p n) :in-theory (disable vmj-block) :expand ((vmj-translate p n vmi)))))

; ---- WHAT A BLOCK DEPENDS ON: THE CODE AND THE POOL'S LENGTH ----------------------------

(defthm vmj-block-same
  (implies (and (equal (nth *v-codei* a) (nth *v-codei* b)) (equal (nth *v-pooli* a) (nth *v-pooli* b)))
           (equal (equal (vmj-block p a) (vmj-block p b)) t))
  :hints (("Goal" :in-theory (enable vmi-w))))

(defthm vmj-ncode-same
  (implies (equal (nth *v-codei* a) (nth *v-codei* b))
           (equal (equal (vmj-ncode a) (vmj-ncode b)) t)))

; ---- A STEP CHANGES NO CODE AND NO POOL -----------------------------------------------------

(defmacro vmj-keeps (name call &rest hints)
  `(defthm ,name
     (and (equal (nth *v-codei* ,call) (nth *v-codei* vmi))
          (equal (nth *v-pooli* ,call) (nth *v-pooli* vmi)))
     ,@hints))

(vmj-keeps vmj-sset-keeps (vmi-sset i v vmi) :hints (("Goal" :in-theory (enable vmi-sset))))
(vmj-keeps vmj-copy-down-keeps (vmi-copy-down src dst k vmi)
           :hints (("Goal" :induct (vmi-copy-down src dst k vmi) :in-theory (disable vmi-sset))))
(vmj-keeps vmj-push-rec-keeps (vmi-push-rec kind a b c vmi) :hints (("Goal" :in-theory (disable nth update-nth))))
(vmj-keeps vmj-pop-rec-keeps (vmi-pop-rec vmi) :hints (("Goal" :in-theory (disable nth update-nth))))
(vmj-keeps vmj-unwind-keeps (vmi-unwind v vmi) :hints (("Goal" :in-theory (disable vmi-sset nth update-nth))))

(in-theory (disable vmi-sset vmi-copy-down vmi-push-rec vmi-pop-rec vmi-unwind vmi-sreg vmi-stk-from vmi-pick vmi-poolv))

(vmj-keeps vmj-step-keeps (vmi-step vmi) :hints (("Goal" :in-theory (e/d (vmi-step) (nth update-nth)))))

; ---- THE NATIVE MACHINE IS THE INTERPRETER --------------------------------------------------

; the table's block for the pc is the step, whatever the pc: in the code
; it is the block the pc's instruction makes, past it nothing runs and the
; step does nothing either
(defthm vmj-tab-step
  (implies (and (equal (v-status vmi) 0)
                (equal (nth *v-codei* vmi) (nth *v-codei* vmi0))
                (equal (nth *v-pooli* vmi) (nth *v-pooli* vmi0)))
           (equal (vmj-exec (nth (nfix (v-pc vmi)) (vmj-translate 0 (vmj-ncode vmi0) vmi0)) vmi)
                  (vmi-step vmi)))
  :hints (("Goal" :in-theory (disable vmj-exec vmj-block vmj-ncode vmj-block-same vmj-ncode-same)
           :cases ((< (nfix (v-pc vmi)) (vmj-ncode vmi0)))
           :use (vmj-block-is vmj-step-past-code
                 (:instance vmj-block-same (p (nfix (v-pc vmi))) (a vmi) (b vmi0))
                 (:instance vmj-ncode-same (a vmi) (b vmi0))))
          ("Subgoal 2" :in-theory (e/d (vmj-exec) (vmj-block vmj-ncode vmj-block-same vmj-ncode-same)))))

; blocks translated once, from the machine as it starts (or any with its
; code and pool), then n of them run: the interpreter's n steps
(defthm vmj-run-is
  (implies (and (equal (nth *v-codei* vmi) (nth *v-codei* vmi0))
                (equal (nth *v-pooli* vmi) (nth *v-pooli* vmi0)))
           (equal (vmj-run (vmj-translate 0 (vmj-ncode vmi0) vmi0) n vmi) (vmi-run n vmi)))
  :hints (("Goal" :induct (vmi-run n vmi)
           :in-theory (e/d (vmi-run) (vmj-exec vmj-block vmj-ncode vmj-translate nth update-nth nfix))
           :expand ((vmj-run (vmj-translate 0 (vmj-ncode vmi0) vmi0) n vmi)))
          ("Subgoal *1/2" :cases ((equal (v-status vmi) 0)) :use vmj-tab-step)
          ("Subgoal *1/2.2" :in-theory (e/d (vmi-run vmi-step) (vmj-exec vmj-block vmj-ncode vmj-translate nth update-nth)))))

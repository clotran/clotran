; clotran's JIT, formally (PLAN step 31, stage 2b: slots in registers).
;
; Stage 2a addresses every stack slot as FB + its depth, so every
; operand is a load and every result a store. Here the frame's first K
; slots live in machine registers R0 .. R(K-1) instead; the rest stay in
; memory. Which slots are in registers is known when translating, since
; the depth at every pc is (stage 2a's dcheck).
;
; At the runtime's instructions -- making a closure, calling, returning
; -- the cached slots are spilled to memory first: the runtime reads and
; writes memory, and these are where a collector can run, so what it
; sees below the stack top in memory is every live value (the rooting
; contract, as vcs-rooted states it for the bytecode). After a call the
; caller's cached slots are filled again, inside the call's own block;
; a function's prologue fills its arguments and closure.
;
; Registers: x[0 .. K-1] the cached slots, x[K] and x[K+1] scratch.

(in-package "ACL2")

(include-book "jit2")

(defconst *k* 8)
(defmacro sk () '*k*)
(defmacro s0 () '(+ *k* 0))
(defmacro s1 () '(+ *k* 1))

; slot j into a register: (mv code reg)
(defun rd3 (j s)
  (if (< (nfix j) (sk)) (mv nil (nfix j)) (mv (list (list :ldr s :fb (nfix j))) s)))

; register r into slot j
(defun wr3 (j r)
  (cond ((< (nfix j) (sk)) (if (equal (nfix j) r) nil (list (list :mov (nfix j) r))))
        (t (list (list :str r :fb (nfix j))))))

; the cached slots from a below b to memory, and back
(defun spill3 (a b)
  (declare (xargs :measure (nfix (- (min (nfix b) (sk)) (nfix a)))))
  (if (and (natp a) (< a (min (nfix b) (sk)))) (cons (list :str a :fb a) (spill3 (1+ a) b)) nil))
(defun fill3 (a b)
  (declare (xargs :measure (nfix (- (min (nfix b) (sk)) (nfix a)))))
  (if (and (natp a) (< a (min (nfix b) (sk)))) (cons (list :ldr a :fb a) (fill3 (1+ a) b)) nil))

(defun binop3 (op d)
  (mv-let (ca ra) (rd3 (- d 2) (s0))
    (mv-let (cb rb) (rd3 (- d 1) (s1))
      (let ((dst (if (< (- d 2) (sk)) (- d 2) (s0))))
        (append ca cb (list (list op dst ra rb)) (wr3 (- d 2) dst))))))

; each bytecode's block at depth d
(defun jblock3 (ins d tgt)
  (case (car ins)
    (:push (if (< d (sk)) (list (list :movi d (cadr ins)))
             (list (list :movi (s0) (cadr ins)) (list :str (s0) :fb d))))
    (:load (mv-let (c r) (rd3 (cadr ins) (s0)) (append c (wr3 d r))))
    (:add (binop3 :add d))
    (:lt (binop3 :lt d))
    (:slide (mv-let (c r) (rd3 (- d 1) (s0)) (append c (wr3 (- d 2) r))))
    (:jmpf (mv-let (c r) (rd3 (- d 1) (s0)) (append c (list (list :cbf r tgt)))))
    (:jmp (list (list :b tgt)))
    (:mkclo (let ((k (nfix (caddr ins))))
              (append (spill3 0 d) (list (list :mkclod (cadr ins) k d)) (fill3 (- d k) (1+ (- d k))))))
    (:capt (mv-let (c r) (rd3 (cadr ins) (s0))
             (append c (list (list :capt r (nfix (caddr ins)))) (wr3 d r))))
    (:callv (let ((n (nfix (cadr ins))))
              (append (spill3 0 d) (list (list :calld n d)) (fill3 0 (- d n)))))
    (:ret (append (spill3 (- d 1) d) (list (list :retd d))))
    (otherwise (list (list :stuck)))))

; a function entry's prologue: its arguments and closure into registers
(defun prologue3 (pc fntab)
  (if (atom fntab)
      nil
    (if (equal (nfix (cadar fntab)) pc)
        (fill3 0 (1+ (nfix (caddar fntab))))
      (prologue3 pc (cdr fntab)))))

; ---- measured, not yet translated: the instructions each executed
; bytecode costs, with its function entry's prologue when it is one
(defun mem3 (blk)
  (if (atom blk) 0 (+ (if (member-equal (car (car blk)) '(:ldr :str)) 1 0) (mem3 (cdr blk)))))

(defun vcs-tally3 (prog dmap s n acc)
  (declare (xargs :mode :program))
  (if (or (zp n) (not (natp (car s))) (eq (car s) :err))
      acc
    (let* ((pc (car s)) (ins (nth pc (car prog))) (d (nfix (nth pc dmap)))
           (blk (append (prologue3 pc (cdr prog)) (jblock3 ins d 0))))
      (if (and (eq (car ins) :ret) (atom (car (cddddr s))))
          acc
        (vcs-tally3 prog dmap (vcs-step prog s) (1- n)
                    (list (1+ (car acc)) (+ (cadr acc) (len blk)) (+ (caddr acc) (mem3 blk))))))))

(defun compare-jit3 (e)
  (declare (xargs :mode :program))
  (let ((prog (vcs-program e *jit-defs*)))
    (list :stage2a (vcs-tally2 prog (list 0 0 0 nil nil) 1000000 '(0 0 0))
          :stage2b (vcs-tally3 prog (dinfer prog) (list 0 0 0 nil nil) 1000000 '(0 0 0))
          :register (vc-tally (vc-program e *jit-defs*) (list 0 0 nil nil) 1000000 '(0 0 0)))))

; ---- THE LAZY ALLOCATOR -------------------------------------------------------------
;
; Each cached slot's state is tracked while translating: :m (in memory
; only), :r (in its register only, dirty), :b (both). A slot is loaded
; only when first read, stored only when dirty and something needs it in
; memory -- the runtime, or a boundary where code from elsewhere joins.
; At every boundary (a branch target, a function entry, after a jump,
; call, closure or return) every slot is :m: that is the state code
; joining from anywhere can agree on.

(defun st-get (j st) (if (< (nfix j) (sk)) (nth (nfix j) st) :m))
(defun st-set (j v st) (if (< (nfix j) (sk)) (update-nth (nfix j) v st) st))
(defun st-mem () (make-list (sk) :initial-element :m))

; read slot j: (mv code reg st)
(defun rdl (j s st)
  (let ((j (nfix j)))
    (cond ((>= j (sk)) (mv (list (list :ldr s :fb j)) s st))
          ((not (member-equal (st-get j st) (quote (:r :b)))) (mv (list (list :ldr j :fb j)) j (st-set j :b st)))
          (t (mv nil j st)))))

; write register r to slot j: (mv code st)
(defun wrl (j r st)
  (let ((j (nfix j)))
    (if (>= j (sk))
        (mv (list (list :str r :fb j)) st)
      (mv (if (equal j r) nil (list (list :mov j r))) (st-set j :r st)))))

; dirty slots below b to memory: (mv code st)
(defun spilll (j b st)
  (declare (xargs :measure (nfix (- (sk) (nfix j)))))
  (if (or (not (natp j)) (>= j (sk)))
      (mv nil st)
    (mv-let (c st2) (spilll (1+ j) b st)
      (if (and (< j (nfix b)) (eq (st-get j st) :r))
          (mv (cons (list :str j :fb j) c) (st-set j :b st2))
        (mv c st2)))))

; slots at or above the depth are dead: forget them
(defun dropl (j d st)
  (declare (xargs :measure (nfix (- (sk) (nfix j)))))
  (if (or (not (natp j)) (>= j (sk))) st (dropl (1+ j) d (if (>= j (nfix d)) (st-set j :m st) st))))

(defun binopl (op d st)
  (mv-let (ca ra st) (rdl (- d 2) (s0) st)
    (mv-let (cb rb st) (rdl (- d 1) (s1) st)
      (let ((dst (if (< (- d 2) (sk)) (- d 2) (s0))))
        (mv-let (cw st) (wrl (- d 2) dst st)
          (mv (append ca cb (list (list op dst ra rb)) cw) st))))))

; each bytecode at depth d, the slot states st on entry: (mv code st)
(defun jblockl (ins d tgt st)
  (case (car ins)
    (:push (if (< d (sk))
               (mv (list (list :movi d (cadr ins))) (st-set d :r st))
             (mv (list (list :movi (s0) (cadr ins)) (list :str (s0) :fb d)) st)))
    (:load (mv-let (c r st) (rdl (cadr ins) (s0) st)
             (mv-let (cw st) (wrl d r st) (mv (append c cw) st))))
    (:add (binopl :add d st))
    (:lt (binopl :lt d st))
    (:slide (mv-let (c r st) (rdl (- d 1) (s0) st)
              (mv-let (cw st) (wrl (- d 2) r st) (mv (append c cw) (dropl 0 (- d 1) st)))))
    (:jmpf (mv-let (c r st) (rdl (- d 1) (s0) st)
             (mv-let (cs st) (spilll 0 (- d 1) st)
               (declare (ignore st))
               (mv (append c cs (list (list :cbf r tgt))) (st-mem)))))
    (:jmp (mv-let (cs st) (spilll 0 d st) (declare (ignore st)) (mv (append cs (list (list :b tgt))) (st-mem))))
    (:mkclo (let ((k (nfix (caddr ins))))
              (mv-let (cs st) (spilll 0 d st)
                (mv (append cs (list (list :mkclod (cadr ins) k d)))
                    (dropl 0 (1+ (- d k)) (st-set (- d k) :m st))))))
    ;; the closure copied to the result's register and the capture taken
    ;; there: :capt overwrites its register, and the closure's own may be
    ;; a cached slot still live (found by the proof, model/jit3-proof.lisp)
    (:capt (mv-let (c r st) (rdl (cadr ins) (s0) st)
             (let ((dst (if (< d (sk)) d (s0))))
               (mv-let (cw st) (wrl d dst st)
                 (mv (append c (if (equal dst r) nil (list (list :mov dst r)))
                             (list (list :capt dst (nfix (caddr ins)))) cw)
                     st)))))
    (:callv (mv-let (cs st) (spilll 0 d st) (declare (ignore st))
              (mv (append cs (list (list :calld (nfix (cadr ins)) d))) (st-mem))))
    (:ret (mv-let (cs st) (spilll (- d 1) d st) (declare (ignore st))
            (mv (append cs (list (list :retd d))) (st-mem))))
    (otherwise (mv (list (list :stuck)) st))))

; the pcs code from elsewhere joins at -- branch targets, entries, main
; -- and every :ret, so a return finds its frame in memory and its block
; is the return alone (a halted :ret then repeats where it stands; the
; measured cost of this on fib, tri and down: none)
(defun targets (rest acc)
  (if (atom rest)
      acc
    (targets (cdr rest)
             (if (member-equal (car (car rest)) '(:jmp :jmpf)) (cons (nfix (cadr (car rest))) acc) acc))))
(defun rets (rest pc acc)
  (if (atom rest) acc (rets (cdr rest) (1+ pc) (if (eq (car (car rest)) :ret) (cons pc acc) acc))))
(defun boundaries (prog)
  (append (list 0) (targets (car prog) nil) (strip-cadrs (cdr prog)) (rets (car prog) 0 nil)))

; measured: the lazy allocator over a run, the state at each pc taken
; along the code as the translator walks it
(defun lazy-states (rest pc dmap bnd st acc)
  (declare (xargs :mode :program))
  (if (atom rest)
      (reverse acc)
    (let ((st (if (member-equal pc bnd) (st-mem) st)))
      (mv-let (code st2) (jblockl (car rest) (nfix (nth pc dmap)) 0 st)
        ;; falling into a boundary: dirty slots out first
        (let ((into (member-equal (1+ pc) bnd)))
          (mv-let (cs st3) (if into (spilll 0 (nfix (nth (1+ pc) dmap)) st2) (mv nil st2))
            (lazy-states (cdr rest) (1+ pc) dmap bnd (if into (st-mem) st3)
                         (cons (append code cs) acc))))))))

(defun vcs-tallyl (prog blocks s n acc)
  (declare (xargs :mode :program))
  (if (or (zp n) (not (natp (car s))) (eq (car s) :err))
      acc
    (let* ((pc (car s)) (ins (nth pc (car prog))) (blk (nth pc blocks)))
      (if (and (eq (car ins) :ret) (atom (car (cddddr s))))
          acc
        (vcs-tallyl prog blocks (vcs-step prog s) (1- n)
                    (list (1+ (car acc)) (+ (cadr acc) (len blk)) (+ (caddr acc) (mem3 blk))))))))

(defun compare-lazy (e)
  (declare (xargs :mode :program))
  (let* ((prog (vcs-program e *jit-defs*)) (dmap (dinfer prog))
         (blocks (lazy-states (car prog) 0 dmap (boundaries prog) (st-mem) nil)))
    (list :stage2a (vcs-tally2 prog (list 0 0 0 nil nil) 1000000 '(0 0 0))
          :lazy (vcs-tallyl prog blocks (list 0 0 0 nil nil) 1000000 '(0 0 0))
          :register (vc-tally (vc-program e *jit-defs*) (list 0 0 nil nil) 1000000 '(0 0 0)))))

; ---- THE TRANSLATION ----------------------------------------------------------------
;
; The blocks in order, each pc's entry state the previous block's exit
; state -- or all :m at a boundary -- and a block that falls into a
; boundary storing its dirty slots first.

(defun lblocks (rest pc dmap bnd st)
  (if (atom rest)
      nil
    (let ((st (if (member-equal pc bnd) (st-mem) st)))
      (mv-let (blk st2) (jblockl (car rest) (nfix (nth pc dmap)) (nfix (cadr (car rest))) st)
        (let ((into (member-equal (1+ pc) bnd)))
          (mv-let (cs st3) (if into (spilll 0 (nfix (nth (1+ pc) dmap)) st2) (mv nil st2))
            (cons (append blk cs)
                  (lblocks (cdr rest) (1+ pc) dmap bnd (if into (st-mem) st3)))))))))

; where each bytecode pc's block begins
(defun lnpc (p blocks)
  (if (zp p) 0 (+ (if (consp blocks) (len (car blocks)) 1) (lnpc (1- p) (cdr blocks)))))

; branch targets are bytecode pcs until the blocks are laid out
(defun lfix (blk blocks)
  (if (atom blk)
      nil
    (cons (let ((ins (car blk)))
            (case (car ins)
              (:cbf (list :cbf (cadr ins) (lnpc (nfix (caddr ins)) blocks)))
              (:b (list :b (lnpc (nfix (cadr ins)) blocks)))
              (otherwise ins)))
          (lfix (cdr blk) blocks))))

(defun lcode (bs blocks)
  (if (atom bs) nil (append (lfix (car bs) blocks) (lcode (cdr bs) blocks))))

(defun lfntab (fntab blocks)
  (if (atom fntab)
      nil
    (cons (list* (caar fntab) (lnpc (nfix (cadar fntab)) blocks) (cddar fntab))
          (lfntab (cdr fntab) blocks))))

(defun jit3-checked (prog dmap)
  (let ((blocks (lblocks (car prog) 0 dmap (boundaries prog) (st-mem))))
    (cons (lcode blocks blocks) (lfntab (cdr prog) blocks))))

; THE JIT: slots in registers when the depth check passes, stage 1's
; code otherwise
(defun jit3 (prog)
  (let ((dmap (dinfer prog)))
    (if (dcheck prog dmap) (jit3-checked prog dmap) (jit prog))))

(defun jit3-run-program (e defs steps)
  (let ((ns (nrun (jit3 (vcs-program e defs)) (list 0 0 0 nil nil (make-list (+ 2 (sk)))) steps)))
    (vcs-answer (nview ns))))

(defmacro check-jit3 (e)
  `(assert-event (equal (jit3-run-program ',e *jit-defs* 400000)
                        (mc ',e nil nil *jit-defs* 1000))))

(check-jit3 (:callv (:mkclo inc1) (:const 41)))
(check-jit3 (:callv (:mkclo adder (:const 10)) (:const 5)))
(check-jit3 (:callv (:mkclo apply1) (:mkclo adder (:const 2)) (:const 3)))
(check-jit3 (:callv (:mkclo mk) (:const 7) (:const 8)))
(check-jit3 (:callv (:mkclo down) (:const 6)))
(check-jit3 (:let (:mkclo adder (:const 100)) (:add (:callv (:local 0) (:const 1)) (:callv (:local 0) (:const 2)))))
(check-jit3 (:callv (:mkclo inc1) (:const 1) (:const 2)))
(check-jit3 (:callv (:const 5) (:const 1)))
(check-jit3 (:callv (:mkclo fib) (:const 10)))
(check-jit3 (:callv (:mkclo tri) (:const 20)))
(check-jit3 (:let (:const 1) (:let (:const 2) (:let (:add (:local 0) (:local 1)) (:add (:local 2) (:add (:local 0) (:local 2)))))))

; a closure that reads its capture twice: :capt took the capture in the
; closure's own register, a live cached slot, and the second read got
; the capture instead of the closure (11, not 21)
(defconst *jit3-defs* (append *jit-defs* '((two 1 (:add (:capt 0) (:add (:capt 0) (:local 0)))))))
(assert-event (equal (jit3-run-program '(:callv (:mkclo two (:const 10)) (:const 1)) *jit3-defs* 100000)
                     (mc '(:callv (:mkclo two (:const 10)) (:const 1)) nil nil *jit3-defs* 1000)))

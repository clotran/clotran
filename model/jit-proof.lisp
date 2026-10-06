; clotran's JIT, formally (PLAN step 31, stage 1): the baseline JIT's
; theorem.
;
;   jit-sim   for ANY bytecode program, a run whose every step has its
;             operands on the stack (jok) is simulated by the machine
;             code block for block: after the blocks of n bytecode
;             steps, the machine's frame base, top, stack and return
;             records are the bytecode's, its pc at the block of the
;             bytecode's pc
;
; Nothing about the compiler is assumed: this is the JIT alone, on any
; bytecode. A compiled program's runs meet jok (vm-closure-stack-proof's
; run-reads-ok), so with vcs-correct the machine code answers what the
; meaning does.

(in-package "ACL2")

(include-book "jit")
(include-book "arithmetic-5/top" :dir :system)

; ---- what the simulation needs of a step --------------------------------------------

; the machine checks no operand count; the bytecode does, and does
; nothing when one is short. A step that has its operands is simulated.
(defun jok (prog s)
  (let ((ins (nth (car s) (car prog))) (sp (nfix (caddr s))))
    (case (car ins)
      ((:add :lt :slide) (<= 2 sp))
      (:jmpf (<= 1 sp))
      (otherwise t))))

(defun run-jok (prog s n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) t (and (jok prog s) (run-jok prog (vcs-step prog s) (1- n)))))

; a bytecode state's shape: five fields, a natural frame base and top
(defun bshape (s)
  (and (true-listp s) (equal (len s) 5) (natp (cadr s)) (natp (caddr s))))

; a machine state's: six
(defun nshape (ns)
  (and (true-listp ns) (equal (len ns) 6)))

; the machine state a bytecode state embeds in, scratch registers x
(defun nst (s code x) (append (emb s code) (list x)))

; the function table's entries are (name pc n ...)
(defun jfntab-ok (ft)
  (if (atom ft) t (and (consp (car ft)) (consp (cdar ft)) (jfntab-ok (cdr ft)))))

; ---- THE CODE'S LAYOUT ---------------------------------------------------------------

; blk sits in code from a on
(defun ncode-at (code a blk)
  (declare (xargs :measure (acl2-count blk)))
  (if (atom blk) t (and (equal (nth a code) (car blk)) (ncode-at code (1+ a) (cdr blk)))))

(defthm ncode-at-cons-shift
  (implies (natp i) (equal (ncode-at (cons y c) (1+ i) blk) (ncode-at c i blk)))
  :hints (("Goal" :induct (ncode-at c i blk))))

(defthm ncode-at-append-shift
  (implies (natp i) (equal (ncode-at (append a c) (+ (len a) i) blk) (ncode-at c i blk)))
  :hints (("Goal" :induct (len a))
          ("Subgoal *1/1" :use ((:instance ncode-at-cons-shift (y (car a)) (c (append (cdr a) c))
                                           (i (+ (len (cdr a)) i)))))))

(defthm ncode-at-prefix (ncode-at (append a c) 0 a)
  :hints (("Goal" :induct (len a))
          ("Subgoal *1/1" :use ((:instance ncode-at-cons-shift (y (car a)) (c (append (cdr a) c)) (i 0)
                                           (blk (cdr a)))))))

(defthm len-jblock (equal (len (jblock ins tgt)) (blen ins)) :hints (("Goal" :in-theory (enable blen))))
(defthm blen-pos (<= 1 (blen ins)) :rule-classes :linear :hints (("Goal" :in-theory (e/d (blen) (len-jblock)))))
(in-theory (disable blen))

(defthm natp-npc (natp (npc p code)) :rule-classes :type-prescription)

(defthm npc-succ
  (implies (natp p) (equal (npc (1+ p) code) (+ (npc p code) (blen (nth p code))))))

; the blocks sit where npc says
(defthm jit-code-layout
  (implies (and (natp p) (< p (len rest)))
           (ncode-at (jit-code rest code) (npc p rest) (jblock (nth p rest) (jtarget (nth p rest) code))))
  :hints (("Goal" :induct (npc p rest) :in-theory (disable jblock jtarget ncode-at ncode-at-append-shift)
                  :expand ((jit-code rest code) (npc p rest)))
          ("Subgoal *1/2" :use ((:instance ncode-at-append-shift
                                           (a (jblock (car rest) (jtarget (car rest) code)))
                                           (c (jit-code (cdr rest) code))
                                           (i (npc (1- p) (cdr rest)))
                                           (blk (jblock (nth (1- p) (cdr rest)) (jtarget (nth (1- p) (cdr rest)) code))))))))

(defthm len-append-sum (equal (len (append a b)) (+ (len a) (len b))))

; past the code, nothing: the bytecode and the machine both stop
(defthm len-jit-code (equal (len (jit-code rest code)) (npc (len rest) rest))
  :hints (("Goal" :induct (jit-code rest code) :in-theory (disable jblock jtarget npc-succ)
                  :expand ((npc (len rest) rest)))))

(defthm npc-past
  (implies (and (natp p) (<= (len rest) p)) (<= (npc (len rest) rest) (npc p rest)))
  :rule-classes nil
  :hints (("Goal" :induct (npc p rest) :in-theory (disable npc-succ) :expand ((npc (len rest) rest)))))

(defthm nth-past-len (implies (and (natp n) (<= (len l) n)) (equal (nth n l) nil)))

(defthm jit-code-past
  (implies (and (natp p) (<= (len rest) p)) (equal (nth (npc p rest) (jit-code rest code)) nil))
  :hints (("Goal" :in-theory (disable jblock jtarget nth-past-len) :use ((:instance npc-past)
                         (:instance nth-past-len (n (npc p rest)) (l (jit-code rest code)))))))

; the machine's function table: each entry at its block
(defthm jit-fntab-lookup
  (implies (jfntab-ok ft)
           (equal (cdr (assoc-equal name (jit-fntab ft code)))
                  (if (consp (assoc-equal name ft))
                      (cons (npc (nfix (cadr (assoc-equal name ft))) code) (cddr (assoc-equal name ft)))
                    nil))))

(defthm jfntab-ok-entry
  (implies (and (jfntab-ok ft) (consp (assoc-equal name ft))) (consp (cdr (assoc-equal name ft)))))

; ---- the machine, a step at a time

(defthm nrun-0 (equal (nrun p ns 0) ns))
(defthm nrun-step
  (implies (and (integerp n) (< 0 n)) (equal (nrun p ns n) (nrun p (nstep p ns) (1- n)))))
(in-theory (disable nrun))

; the scratch registers, a short list
(defthm nth-cons-pos
  (implies (and (integerp n) (< 0 n)) (equal (nth n (cons a b)) (nth (1- n) b))))

; ---- ONE BYTECODE, ONE BLOCK ---------------------------------------------------------

(defthm blen-op
  (equal (blen ins)
         (case (car ins) ((:add :lt) 5) ((:push :load :slide :jmpf) 3) (:capt 4) (otherwise 1)))
  :hints (("Goal" :in-theory (e/d (blen) (len-jblock)))))

(defthm bshape-step
  (implies (bshape s) (bshape (vcs-step prog s)))
  :hints (("Goal" :in-theory (enable vcs-step))))

; the facts every block's run needs: its code, its state, its table
(defmacro bhyps (op)
  `(and (bshape s) (natp (car s)) (< (car s) (len (car prog)))
        (equal (car (nth (car s) (car prog))) ,op) (jok prog s) (jfntab-ok (cdr prog))))

(defmacro bconcl ()
  '(let ((r (nrun (jit prog) (nst s (car prog) x) (blen (nth (car s) (car prog))))))
     (and (nshape r) (equal (nview r) (emb (vcs-step prog s) (car prog))))))

(defmacro defblock (name op)
  `(defthm ,name (implies (bhyps ,op) (bconcl))
     :hints (("Goal" :in-theory (e/d (vcs-step) (jit-code-layout npc-succ jit-code npc jit-fntab nth nth-add1))
            :use ((:instance jit-code-layout (rest (car prog)) (code (car prog)) (p (car s)))
                  (:instance npc-succ (p (car s)) (code (car prog))))))))

(defblock block-push :push)
(defblock block-load :load)
(defblock block-add :add)
(defblock block-lt :lt)
(defblock block-slide :slide)
(defblock block-jmpf :jmpf)
(defblock block-jmp :jmp)
(defblock block-mkclo :mkclo)
(defblock block-capt :capt)
(defblock block-callv :callv)
(defblock block-ret :ret)

(defthm block-other
  (implies (and (bshape s) (natp (car s)) (< (car s) (len (car prog)))
                (not (member-equal (car (nth (car s) (car prog)))
                                   '(:push :load :add :lt :slide :jmpf :jmp :mkclo :capt :callv :ret))))
           (bconcl))
  :hints (("Goal" :in-theory (e/d (vcs-step) (jit-code-layout npc-succ jit-code npc jit-fntab nth nth-add1))
            :use ((:instance jit-code-layout (rest (car prog)) (code (car prog)) (p (car s)))
                  (:instance npc-succ (p (car s)) (code (car prog)))))))

; past the code, and at no pc at all, both machines stand still
(defthm block-past
  (implies (and (bshape s) (natp (car s)) (<= (len (car prog)) (car s)))
           (bconcl))
  :hints (("Goal" :in-theory (enable vcs-step)
                  :use ((:instance jit-code-past (rest (car prog)) (code (car prog)) (p (car s)))))))

(defthm block-nopc
  (implies (and (bshape s) (not (natp (car s))))
           (let ((r (nrun (jit prog) (nst s (car prog) x) 1)))
             (and (nshape r) (equal (nview r) (emb (vcs-step prog s) (car prog))))))
  :hints (("Goal" :in-theory (enable vcs-step))))

; ---- ANY STEP -------------------------------------------------------------------------

(defun bsteps (prog s) (if (natp (car s)) (blen (nth (car s) (car prog))) 1))

(defthm block-any
  (implies (and (bshape s) (jok prog s) (jfntab-ok (cdr prog)))
           (let ((r (nrun (jit prog) (nst s (car prog) x) (bsteps prog s))))
             (and (nshape r) (equal (nview r) (emb (vcs-step prog s) (car prog))))))
  :hints (("Goal" :in-theory (e/d (bsteps) (block-push block-load block-add block-lt block-slide block-jmpf block-jmp
                                             block-mkclo block-capt block-callv block-ret block-other block-past block-nopc
                                             nrun-step nst emb nview nshape jit blen-op jok))
                  :cases ((not (natp (car s))) (<= (len (car prog)) (car s)))
                  :use (block-push block-load block-add block-lt block-slide block-jmpf block-jmp
                        block-mkclo block-capt block-callv block-ret block-other block-past block-nopc))))

; ---- THE SIMULATION -------------------------------------------------------------------

(defthm nrun-plus
  (implies (and (natp a) (natp b)) (equal (nrun p ns (+ a b)) (nrun p (nrun p ns a) b)))
  :hints (("Goal" :induct (nrun p ns a) :in-theory (e/d (nrun) (nstep nrun-step)))))

(defthm nview-nst (equal (nview (nst s code x)) (emb s code)))
(defthm nshape-nst (nshape (nst s code x)))

; a machine state of six fields is its view and its scratch registers
(defthm six-list
  (implies (and (true-listp r) (equal (len r) 6))
           (equal (list (car r) (cadr r) (caddr r) (cadddr r) (car (cddddr r)) (cadr (cddddr r))) r))
  :rule-classes nil
  :hints (("Goal" :expand ((len r) (len (cdr r)) (len (cddr r)) (len (cdddr r)) (len (cddddr r))
                           (len (cdr (cddddr r))) (len (cddr (cddddr r)))))))

(defthm nshape-is-nst
  (implies (and (nshape r) (equal (nview r) (emb s code)))
           (equal (nst s code (cadr (cddddr r))) r))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable emb) :use ((:instance six-list)))))

(defun jsim-ind (prog s n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list s x)
    (jsim-ind prog (vcs-step prog s) (1- n)
              (cadr (cddddr (nrun (jit prog) (nst s (car prog) x) (bsteps prog s)))))))

(defthm jclk-is
  (equal (jclk prog s n) (if (zp n) 0 (+ (bsteps prog s) (jclk prog (vcs-step prog s) (1- n)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (bsteps) (blen-op)) :expand ((jclk prog s n)))))

(defthm natp-bsteps (natp (bsteps prog s)) :rule-classes :type-prescription)
(defthm natp-jclk (natp (jclk prog s n)) :rule-classes :type-prescription)

; THE BASELINE JIT IS THE BYTECODE: for any program, after the blocks of
; n bytecode steps that each have their operands, the machine is where
; the bytecode is -- the same frame base, top, stack and return records,
; at the block of the bytecode's pc
(defthm jit-sim
  (implies (and (bshape s) (jfntab-ok (cdr prog)) (run-jok prog s n))
           (let ((r (nrun (jit prog) (nst s (car prog) x) (jclk prog s n))))
             (and (nshape r) (equal (nview r) (emb (vcs-run prog s n) (car prog))))))
  :hints (("Goal" :induct (jsim-ind prog s n x)
                  :in-theory (disable jclk nst emb nview nshape jit bsteps block-any vcs-step nstep vcs-run run-jok
                                      emb-ctl nrun-step nrun-plus jok bshape)
                  :expand ((vcs-run prog s n) (run-jok prog s n)))
          ("Subgoal *1/2" :use ((:instance jclk-is)
                                (:instance block-any)
                                (:instance nshape-is-nst (s (vcs-step prog s)) (code (car prog))
                                           (r (nrun (jit prog) (nst s (car prog) x) (bsteps prog s))))
                                (:instance nrun-plus (p (jit prog)) (ns (nst s (car prog) x)) (a (bsteps prog s))
                                           (b (jclk prog (vcs-step prog s) (1- n))))))
          ("Subgoal *1/1" :use ((:instance jclk-is)))))

; ---- ITS COST --------------------------------------------------------------------------

(defthm bsteps-bound (<= (bsteps prog s) 5) :rule-classes :linear
  :hints (("Goal" :in-theory (enable bsteps))))

; at most five machine instructions per bytecode, none of them a dispatch
(defthm jit-clock-bound
  (<= (jclk prog s n) (* 5 (nfix n)))
  :hints (("Goal" :induct (jclk prog s n) :in-theory (enable bsteps))))

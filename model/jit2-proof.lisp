; clotran's JIT, formally (PLAN step 31, stage 2a): the theorems.
;
;   dinv-step   THE CHECK IS SOUND: when dcheck passes, every step keeps
;               the bytecode's stack top at FB + the depth of its pc,
;               each caller's frame where its return expects it -- for
;               ANY bytecode that passes, as a verifier's theorem is
;   jit2-sim    so the depth-addressed machine code is the bytecode, block
;               for block, from any state the invariant holds in; no
;               assumption about the run is needed, unlike stage 1's
;               jit-sim, which needed every step to have its operands
;   jit2-correct  and a compiled program answers its meaning through the
;               JIT -- by stage 2 when the check passes, by stage 1 when
;               it does not

(in-package "ACL2")

(include-book "jit2")
(include-book "jit-proof")

; ---- THE CODE'S LAYOUT, as stage 1's -------------------------------------------------

(defthm len-jblock2 (equal (len (jblock2 ins d tgt)) (blen2 ins)) :hints (("Goal" :in-theory (enable blen2))))
(defthm blen2-pos (<= 1 (blen2 ins)) :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (blen2) (len-jblock2)))))
(in-theory (disable blen2))
(defthm blen2-op
  (equal (blen2 ins)
         (case (car ins) ((:add :lt) 4) ((:push :load :slide :jmpf) 2) (:capt 3) (otherwise 1)))
  :hints (("Goal" :in-theory (e/d (blen2) (len-jblock2)))))
(in-theory (disable blen2-op))

(defthm natp-npc2 (natp (npc2 p code)) :rule-classes :type-prescription)

(defthm npc2-succ
  (implies (natp p) (equal (npc2 (1+ p) code) (+ (npc2 p code) (blen2 (nth p code))))))

(defun l2-ind (p rest pc0)
  (if (or (zp p) (atom rest)) (list p rest pc0) (l2-ind (1- p) (cdr rest) (1+ pc0))))

(defthm jit2-code-layout
  (implies (and (natp p) (< p (len rest)) (natp pc0))
           (ncode-at (jit2-code rest pc0 code dmap) (npc2 p rest)
                     (jblock2 (nth p rest) (nfix (nth (+ pc0 p) dmap)) (jtarget2 (nth p rest) code))))
  :hints (("Goal" :induct (l2-ind p rest pc0)
                  :in-theory (disable jblock2 jtarget2 ncode-at ncode-at-append-shift npc2-succ)
                  :expand ((jit2-code rest pc0 code dmap) (npc2 p rest)))
          ("Subgoal *1/2" :use ((:instance ncode-at-append-shift
                                           (a (jblock2 (car rest) (nfix (nth pc0 dmap)) (jtarget2 (car rest) code)))
                                           (c (jit2-code (cdr rest) (1+ pc0) code dmap))
                                           (i (npc2 (1- p) (cdr rest)))
                                           (blk (jblock2 (nth (1- p) (cdr rest)) (nfix (nth (+ pc0 p) dmap))
                                                         (jtarget2 (nth (1- p) (cdr rest)) code))))))))

(defthm jit2-fntab-lookup
  (implies (jfntab-ok ft)
           (equal (cdr (assoc-equal name (jit2-fntab ft code)))
                  (if (consp (assoc-equal name ft))
                      (cons (npc2 (nfix (cadr (assoc-equal name ft))) code) (cddr (assoc-equal name ft)))
                    nil))))

; ---- WHAT THE CHECK SAYS -------------------------------------------------------------

(defthm dcheck-code-at
  (implies (and (dcheck-code rest pc0 dmap n) (natp p) (< p (len rest)) (natp pc0)
                (natp (nth (+ pc0 p) dmap)))
           (dok (+ pc0 p) (nth p rest) (nth (+ pc0 p) dmap) dmap n))
  :hints (("Goal" :induct (list (dcheck-code rest pc0 dmap n) (nth p rest)) :in-theory (disable dok))))

(defthm dbounded-at
  (implies (and (dbounded dmap pc0 n) (natp p) (natp pc0) (natp (nth p dmap)))
           (< (+ pc0 p) n))
  :hints (("Goal" :induct (list (dbounded dmap pc0 n) (nth p dmap)))))

; an instruction the check gave a depth: in the code, and as dok says
(defthm dcheck-at
  (implies (and (dcheck prog dmap) (natp pc) (natp (nth pc dmap)))
           (and (< pc (len (car prog)))
                (dok pc (nth pc (car prog)) (nth pc dmap) dmap (len (car prog)))))
  :hints (("Goal" :in-theory (disable dok dcheck-code-at dbounded-at)
                  :use ((:instance dcheck-code-at (rest (car prog)) (pc0 0) (p pc) (n (len (car prog))))
                        (:instance dbounded-at (pc0 0) (p pc) (n (len (car prog))))))))

; a function's entry is at its arity and its closure
(defthm dcheck-entries-at
  (implies (and (dcheck-entries ft dmap) (consp (assoc-equal name ft)))
           (and (natp (cadr (assoc-equal name ft)))
                (equal (nth (cadr (assoc-equal name ft)) dmap) (1+ (nfix (caddr (assoc-equal name ft)))))
                (consp (cddr (assoc-equal name ft))))))

(defthm dcheck-entries-jfntab-ok
  (implies (dcheck-entries ft dmap) (jfntab-ok ft)))

(defthm dok-succs
  (implies (dok pc ins d dmap n) (succs-ok (dsuccs pc ins d) dmap n)))

(defthm succs-ok-cons
  (equal (succs-ok (cons pr rest) dmap n)
         (and (natp (car pr)) (< (car pr) n) (equal (nth (car pr) dmap) (cdr pr)) (succs-ok rest dmap n))))

; ---- THE INVARIANT ---------------------------------------------------------------------

; each return record: its pc has a depth, and the frame above it began
; where that depth says the caller's top was; the outermost frame at 0
(defun dctl (ctl fb dmap)
  (if (atom ctl)
      (equal fb 0)
    (let ((rpc (car (car ctl))) (rfb (cadr (car ctl))))
      (and (natp rpc) (natp rfb) (natp (nth rpc dmap))
           (equal (+ 1 fb) (+ rfb (nth rpc dmap)))
           (dctl (cdr ctl) rfb dmap)))))

; the top is FB + the depth of the pc -- or the program has halted: its
; :ret ran with no caller, leaving one value, the top's own copy
(defun dinv (prog dmap s)
  (let ((pc (car s)) (fb (cadr s)) (sp (caddr s)) (stk (cadddr s)) (ctl (car (cddddr s))))
    (or (not (natp pc))
        (and (natp (nth pc dmap)) (dctl ctl fb dmap)
             (or (equal sp (+ fb (nth pc dmap)))
                 (and (atom ctl) (equal (car (nth pc (car prog))) :ret) (equal sp 1) (<= 1 (nth pc dmap))
                      (equal (nth (1- (nth pc dmap)) stk) (nth 0 stk))))))))

(defmacro dhyps ()
  '(and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (natp (car s))))

; THE CHECK IS SOUND: a step keeps the invariant
(defthm dinv-step
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s))
           (dinv prog dmap (vcs-step prog s)))
  :hints (("Goal" :in-theory (e/d (vcs-step) (dcheck dcheck-at dok))
                  :cases ((natp (car s)))
                  :use ((:instance dcheck-at (pc (car s)))
                        (:instance dcheck-entries-at (ft (cdr prog))
                                   (name (clo-f (nth (+ -1 (caddr s)) (cadddr s)))))))
          ("Subgoal 1" :in-theory (e/d (vcs-step dok dcheck) (dcheck-at)))))

; the runtime instructions, a step each: what nstep does with the
; instruction it fetches, its fields named
(defmacro nins () 'ins)

(defthm nstep-mkclod
  (implies (and (natp (car ns)) (equal (nth (car ns) (car np)) ins) (equal (car ins) :mkclod))
           (equal (nstep np ns)
                  (let ((fb (nfix (cadr ns))) (stk (cadddr ns))
                        (k (nfix (caddr (nins)))) (d (nfix (cadddr (nins)))))
                    (if (< d k) ns
                      (list (1+ (car ns)) fb (nfix (caddr ns))
                            (ssetreg (+ fb (- d k)) (clo (cadr (nins)) (stk-from (+ fb (- d k)) k stk)) stk)
                            (car (cddddr ns)) (cadr (cddddr ns)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nstep))))

(defthm nstep-calld
  (implies (and (natp (car ns)) (equal (nth (car ns) (car np)) ins) (equal (car ins) :calld))
           (equal (nstep np ns)
                  (let* ((fb (nfix (cadr ns))) (sp (nfix (caddr ns))) (stk (cadddr ns))
                         (ctl (car (cddddr ns))) (x (cadr (cddddr ns)))
                         (n (nfix (cadr (nins)))) (d (nfix (caddr (nins)))))
                    (if (< d (1+ n))
                        ns
                      (let* ((c (sreg (+ fb (1- d)) stk))
                             (ent (and (clop c) (cdr (assoc-equal (clo-f c) (cdr np))))))
                        (if (or (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                            (list :err fb sp stk ctl x)
                          (list (nfix (car ent)) (+ fb (- d (1+ n))) sp stk (cons (list (1+ (car ns)) fb) ctl) x)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nstep))))

(defthm nstep-retd
  (implies (and (natp (car ns)) (equal (nth (car ns) (car np)) ins) (equal (car ins) :retd))
           (equal (nstep np ns)
                  (let* ((fb (nfix (cadr ns))) (sp (nfix (caddr ns))) (stk (cadddr ns))
                         (ctl (car (cddddr ns))) (x (cadr (cddddr ns))) (d (nfix (cadr (nins)))))
                    (if (zp d) ns
                      (let ((v (sreg (+ fb (1- d)) stk)))
                        (if (atom ctl)
                            (list (car ns) fb sp (ssetreg 0 v stk) ctl x)
                          (let ((rec (car ctl)))
                            (list (nfix (car rec)) (nfix (cadr rec)) sp (ssetreg fb v stk) (cdr ctl) x))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nstep))))

; ---- ONE BYTECODE, ONE BLOCK ------------------------------------------------------------

(defthm dcheck-facts
  (implies (dcheck prog dmap)
           (and (dcheck-entries (cdr prog) dmap) (jfntab-ok (cdr prog)) (equal (nth 0 dmap) 0)))
  :hints (("Goal" :in-theory (enable dcheck))))

; the machine state a bytecode state embeds in: y its unused SP
(defun nst2 (s code y x)
  (list (if (natp (car s)) (npc2 (car s) code) (car s)) (cadr s) y (cadddr s)
        (emb2-ctl (car (cddddr s)) code) x))

(defmacro b2hyps (op)
  `(and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (natp (car s))
        (equal (car (nth (car s) (car prog))) ,op)))

(defmacro b2concl ()
  '(let ((r (nrun (jit2-checked prog dmap) (nst2 s (car prog) y x) (blen2 (nth (car s) (car prog))))))
     (and (nshape r) (equal (nview2 r) (emb2 (vcs-step prog s) (car prog))))))

(defmacro defblock2 (name op)
  `(defthm ,name (implies (b2hyps ,op) (b2concl))
     :hints (("Goal" :in-theory (e/d (vcs-step dok blen2-op)
                                     (jit2-code-layout npc2-succ jit2-code npc2 jit2-fntab nth nth-add1
                                      dcheck dcheck-at))
                     :use ((:instance jit2-code-layout (rest (car prog)) (pc0 0) (code (car prog)) (p (car s)))
                           (:instance dcheck-at (pc (car s)))
                           (:instance npc2-succ (p (car s)) (code (car prog))))))))

(defblock2 block2-push :push)
(defblock2 block2-load :load)
(defblock2 block2-add :add)
(defblock2 block2-lt :lt)
(defblock2 block2-slide :slide)
(defblock2 block2-jmpf :jmpf)
(defblock2 block2-jmp :jmp)
(defblock2 block2-capt :capt)

(defmacro defblock2rt (name op step)
  `(defthm ,name (implies (b2hyps ,op) (b2concl))
     :hints (("Goal" :in-theory (e/d (vcs-step dok blen2-op)
                                     (jit2-code-layout npc2-succ jit2-code npc2 jit2-fntab nth nth-add1
                                      dcheck dcheck-at nstep))
                     :use ((:instance jit2-code-layout (rest (car prog)) (pc0 0) (code (car prog)) (p (car s)))
                           (:instance dcheck-at (pc (car s)))
                           (:instance npc2-succ (p (car s)) (code (car prog)))
                           (:instance ,step (np (jit2-checked prog dmap)) (ns (nst2 s (car prog) y x))
                                      (ins (car (jblock2 (nth (car s) (car prog)) (nfix (nth (car s) dmap))
                                                         (jtarget2 (nth (car s) (car prog)) (car prog)))))))))))

(defblock2rt block2-mkclo :mkclo nstep-mkclod)
(defblock2rt block2-callv :callv nstep-calld)
(defblock2rt block2-ret :ret nstep-retd)

(defthm block2-other
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (natp (car s))
                (not (member-equal (car (nth (car s) (car prog)))
                                   '(:push :load :add :lt :slide :jmpf :jmp :mkclo :capt :callv :ret))))
           (b2concl))
  :hints (("Goal" :in-theory (e/d (vcs-step dok blen2-op)
                                  (jit2-code-layout npc2-succ jit2-code npc2 jit2-fntab nth nth-add1 dcheck dcheck-at))
                  :use ((:instance jit2-code-layout (rest (car prog)) (pc0 0) (code (car prog)) (p (car s)))
                        (:instance dcheck-at (pc (car s)))
                        (:instance npc2-succ (p (car s)) (code (car prog)))))))

(defthm block2-nopc
  (implies (and (bshape s) (not (natp (car s))))
           (let ((r (nrun (jit2-checked prog dmap) (nst2 s (car prog) y x) 1)))
             (and (nshape r) (equal (nview2 r) (emb2 (vcs-step prog s) (car prog))))))
  :hints (("Goal" :in-theory (enable vcs-step))))

; ---- ANY STEP, THEN THE SIMULATION ---------------------------------------------------------

(defun b2steps (prog s) (if (natp (car s)) (blen2 (nth (car s) (car prog))) 1))

(defthm block2-any
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s))
           (let ((r (nrun (jit2-checked prog dmap) (nst2 s (car prog) y x) (b2steps prog s))))
             (and (nshape r) (equal (nview2 r) (emb2 (vcs-step prog s) (car prog))))))
  :hints (("Goal" :in-theory (e/d (b2steps)
                                  (block2-push block2-load block2-add block2-lt block2-slide block2-jmpf block2-jmp
                                   block2-mkclo block2-capt block2-callv block2-ret block2-other block2-nopc
                                   nrun-step nst2 emb2 nview2 nshape jit2-checked blen2-op dinv dcheck
                                   vcs-step nstep emb2-ctl jit2-code npc2))
                  :cases ((not (natp (car s))))
                  :use (block2-push block2-load block2-add block2-lt block2-slide block2-jmpf block2-jmp
                        block2-mkclo block2-capt block2-callv block2-ret block2-other block2-nopc))))

(defthm nview2-nst2 (equal (nview2 (nst2 s code y x)) (emb2 s code)))
(defthm nshape-nst2 (nshape (nst2 s code y x)))

(defthm nshape-is-nst2
  (implies (and (nshape r) (equal (nview2 r) (emb2 s code)))
           (equal (nst2 s code (caddr r) (cadr (cddddr r))) r))
  :rule-classes nil
  :hints (("Goal" :use ((:instance six-list)))))

(defun jsim2-ind (prog dmap s n y x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list s y x)
    (let ((r (nrun (jit2-checked prog dmap) (nst2 s (car prog) y x) (b2steps prog s))))
      (jsim2-ind prog dmap (vcs-step prog s) (1- n) (caddr r) (cadr (cddddr r))))))

(defthm j2clk-is
  (equal (j2clk prog s n) (if (zp n) 0 (+ (b2steps prog s) (j2clk prog (vcs-step prog s) (1- n)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (b2steps) (blen2-op)) :expand ((j2clk prog s n)))))

(defthm natp-b2steps (natp (b2steps prog s)) :rule-classes :type-prescription)
(defthm natp-j2clk (natp (j2clk prog s n)) :rule-classes :type-prescription)

; THE DEPTH-ADDRESSED CODE IS THE BYTECODE: from any state the invariant
; holds in, after the blocks of n steps the machine is where the
; bytecode is. The check alone makes it so; nothing about the run is
; assumed.
(defthm jit2-sim
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s))
           (let ((r (nrun (jit2-checked prog dmap) (nst2 s (car prog) y x) (j2clk prog s n))))
             (and (nshape r) (equal (nview2 r) (emb2 (vcs-run prog s n) (car prog))))))
  :hints (("Goal" :induct (jsim2-ind prog dmap s n y x)
                  :in-theory (disable j2clk nst2 emb2 nview2 nshape jit2-checked b2steps block2-any vcs-step nstep
                                      vcs-run emb2-ctl nrun-step nrun-plus bshape dinv dcheck)
                  :expand ((vcs-run prog s n)))
          ("Subgoal *1/2" :use ((:instance j2clk-is)
                                (:instance block2-any)
                                (:instance dinv-step)
                                (:instance bshape-step)
                                (:instance nshape-is-nst2 (s (vcs-step prog s)) (code (car prog))
                                           (r (nrun (jit2-checked prog dmap) (nst2 s (car prog) y x) (b2steps prog s))))
                                (:instance nrun-plus (p (jit2-checked prog dmap)) (ns (nst2 s (car prog) y x))
                                           (a (b2steps prog s)) (b (j2clk prog (vcs-step prog s) (1- n))))))
          ("Subgoal *1/1" :use ((:instance j2clk-is)))))

(defthm b2steps-bound (<= (b2steps prog s) 4) :rule-classes :linear
  :hints (("Goal" :in-theory (enable b2steps blen2-op))))

; at most four machine instructions per bytecode
(defthm jit2-clock-bound
  (<= (j2clk prog s n) (* 4 (nfix n)))
  :hints (("Goal" :induct (j2clk prog s n) :in-theory (enable b2steps blen2-op))))

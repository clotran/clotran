; clotran's JIT, formally (PLAN step 31, stage 2b): compiled programs.
;
;   jit3-correct  a compiled closure program answers its meaning through
;                 the stage-2b JIT: through the register-allocated code
;                 when the depth check passes (jit3-sim), through stage
;                 1's when it does not (jit-sim)
;   jit3-linear   in at most 18 machine instructions per bytecode, 36 per
;                 expression the meaning evaluates

(in-package "ACL2")

(include-book "jit3-proof")
(include-book "jit2-correct")

; ---- WHERE THE BYTECODE ENDS ---------------------------------------------------------------

; the bytecode run of a program whose meaning answers ends halted at
; main's :ret, its frame at the bottom
(defthm vcs-final
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0) (valp (mc e nil nil defs fuel)) (natp k))
           (let ((s2 (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k))))
             (and (natp (car s2)) (equal (cadr s2) 0)
                  (equal (nth (car s2) (car (vcs-program e defs))) '(:ret)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable sgood vcs-good shalted-stays vcs-program vcs-program-fns-ok vcs-run-plus)
                  :use ((:instance vcs-program-fns-ok)
                        (:instance vcs-run-plus (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (a (sclk e nil nil defs fuel)) (b k))
                        (:instance vcs-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 nil nil)) (env nil)
                                   (prog (vcs-program e defs)))
                        (:instance (:definition sgood) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (vcs-program e defs)))
                        (:instance shalted-stays (prog (vcs-program e defs))
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (sclk e nil nil defs fuel))))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcs-compile e 0 nil nil 0))
                                   (b (cons '(:ret) (car (vcs-defs defs (len (sv-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcs-program))))

(defthm dinv-run
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s))
           (and (dinv prog dmap (vcs-run prog s n)) (bshape (vcs-run prog s n))))
  :hints (("Goal" :induct (vcs-run prog s n) :in-theory (e/d (vcs-run) (dinv bshape vcs-step dcheck)))))

; ---- THE START AND THE ANSWER -------------------------------------------------------------

(defthm slots-ok-zero (implies (zp d) (slots-ok d st fb stk mem x)) :hints (("Goal" :in-theory (enable slots-ok))))
(defthm below-ok-zero (below-ok 0 stk mem) :hints (("Goal" :in-theory (enable below-ok))))

(defthm l3-start
  (implies (dcheck prog dmap)
           (l3 prog dmap (list 0 0 0 nil nil) (list 0 0 0 nil nil x)))
  :hints (("Goal" :in-theory (disable dcheck lblocks lstates) :use dcheck-facts)))

; halted at a :ret, the answer slot is in memory: the machine answers the bytecode's answer
(defthm l3-answer
  (implies (and (dcheck prog dmap) (l3 prog dmap s ns) (natp (car s)) (natp (nth (car s) dmap))
                (equal (car (nth (car s) (car prog))) :ret) (equal (cadr s) 0))
           (equal (vcs-answer (nview ns)) (vcs-answer s)))
  :hints (("Goal" :in-theory (e/d (vcs-answer nview)
                                  (l3 dcheck lblocks lstates jit3-checked mem-ok-nth mem-ok-of-st-mem (:e st-mem)))
                  :use ((:instance l3-facts)
                        (:instance l3-shape)
                        (:instance ret-code (pc (car s)))
                        (:instance mem-ok-of-st-mem (d (nth (car s) dmap)) (fb 0) (stk (cadddr s)) (mem (cadddr ns))
                                   (x (cadr (cddddr ns))))
                        (:instance mem-ok-nth (d (nth (car s) dmap)) (fb 0) (stk (cadddr s)) (mem (cadddr ns)) (j 0))))))

; ---- THE PROGRAM ---------------------------------------------------------------------------

; the machine steps the stage-2b JIT's code takes for n bytecode steps
(defun jit3-clk (prog n)
  (let ((dmap (dinfer prog)))
    (if (dcheck prog dmap)
        (j3clk prog dmap (list 0 0 0 nil nil) n)
      (jclk prog (list 0 0 0 nil nil) n))))

(defmacro P3 () '(vcs-program e defs))
(defmacro N3 () '(+ (sclk e nil nil defs fuel) k))
(defmacro X3 () '(make-list (+ 2 (sk))))

(defthm jit3-correct-checked
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k)
                (dcheck (P3) (dinfer (P3))))
           (equal (jit3-run-program e defs (jit3-clk (P3) (N3)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (e/d (jit3-run-program jit3 vcs-run-program jit3-clk)
                                  (jit3-sim vcs-correct l3-answer l3-start dinv-run jit3-checked vcs-program j3clk
                                   dinfer dcheck dinv-start l3 nview vcs-run))
                  :use ((:instance vcs-correct)
                        (:instance vcs-final)
                        (:instance dinv-start (prog (P3)) (dmap (dinfer (P3))))
                        (:instance dinv-run (prog (P3)) (dmap (dinfer (P3))) (s (list 0 0 0 nil nil)) (n (N3)))
                        (:instance l3-start (prog (P3)) (dmap (dinfer (P3))) (x (X3)))
                        (:instance jit3-sim (prog (P3)) (dmap (dinfer (P3))) (s (list 0 0 0 nil nil))
                                   (ns (list 0 0 0 nil nil (X3))) (n (N3)))
                        (:instance l3-answer (prog (P3)) (dmap (dinfer (P3)))
                                   (s (vcs-run (P3) (list 0 0 0 nil nil) (N3)))
                                   (ns (nrun (jit3-checked (P3) (dinfer (P3))) (list 0 0 0 nil nil (X3))
                                             (j3clk (P3) (dinfer (P3)) (list 0 0 0 nil nil) (N3)))))))))

; stage 1 from the stage-2b JIT's start: its registers are not read before written
(defthm jit-start-x
  (equal (nst (list 0 0 0 nil nil) code x) (list 0 0 0 nil nil x))
  :hints (("Goal" :in-theory (enable nst emb npc))))

(defthm jit3-correct-fallback
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k)
                (not (dcheck (P3) (dinfer (P3)))))
           (equal (jit3-run-program e defs (jit3-clk (P3) (N3)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (e/d (jit3-run-program jit3 vcs-run-program jit3-clk)
                                  (jit-sim vcs-correct vcs-program-reads run-reads-ok-jok jit nview emb nst
                                   vcs-program jclk vcs-answer-emb dinfer dcheck))
                  :use ((:instance vcs-correct)
                        (:instance vcs-program-reads)
                        (:instance run-reads-ok-jok (prog (P3)) (s (list 0 0 0 nil nil)) (n (N3)))
                        (:instance jit-sim (prog (P3)) (s (list 0 0 0 nil nil)) (x (X3)) (n (N3)))
                        (:instance vcs-answer-emb (code (car (P3)))
                                   (s (vcs-run (P3) (list 0 0 0 nil nil) (N3))))))))

; A COMPILED PROGRAM THROUGH THE STAGE-2b JIT answers what its meaning does
(defthm jit3-correct
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (jit3-run-program e defs (jit3-clk (P3) (N3)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable jit3-correct-checked jit3-correct-fallback jit3-run-program jit3-clk)
                  :use (jit3-correct-checked jit3-correct-fallback))))

; ---- IN LINEAR TIME -------------------------------------------------------------------------

(defthm len-spilll-gen
  (<= (len (car (spilll j b st))) (nfix (- (sk) (nfix j))))
  :rule-classes nil
  :hints (("Goal" :induct (spilll j b st))))

(defthm len-spilll (<= (len (car (spilll j b st))) (sk)) :rule-classes :linear
  :hints (("Goal" :use len-spilll-gen)))

(defthm len-rdl (<= (len (car (rdl j s st))) 1) :rule-classes :linear)
(defthm len-wrl (<= (len (car (wrl j r st))) 1) :rule-classes :linear)

(defthm len-jblockl (<= (len (car (jblockl ins d tgt st))) 10) :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (jblockl binopl) (spilll rdl wrl dropl st-set)))))

(defthm len-lstep (<= (len (car (lstep ins pc dmap bnd st))) 18) :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (lstep) (jblockl spilll)))))

(defthm b3steps-bound (<= (b3steps prog dmap s) 18) :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (b3steps) (lstep lblocks lstates))
                  :cases ((and (natp (car s)) (< (car s) (len (car prog)))))
                  :use ((:instance lblocks-nth (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))))))

; at most eighteen machine instructions per bytecode: the spills before
; a runtime op, its block, and the spills into a boundary
(defthm jit3-clock-bound
  (<= (j3clk prog dmap s n) (* 18 (nfix n)))
  :hints (("Goal" :induct (j3clk prog dmap s n) :in-theory (disable b3steps))))

; AND IN LINEAR TIME
(defthm jit3-linear
  (implies (natp k)
           (<= (jit3-clk (vcs-program e defs) (+ (sclk e nil nil defs fuel) k))
               (+ (* 36 (cevals e nil nil defs fuel)) (* 18 k))))
  :hints (("Goal" :in-theory (e/d (jit3-clk) (jit3-clock-bound jit-clock-bound sclk-linear j3clk jclk dinfer dcheck vcs-program))
                  :use ((:instance jit3-clock-bound (prog (vcs-program e defs)) (dmap (dinfer (vcs-program e defs)))
                                   (s (list 0 0 0 nil nil)) (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance jit-clock-bound (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance sclk-linear (env nil) (caps nil))))))

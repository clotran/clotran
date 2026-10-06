; clotran's JIT, formally (PLAN step 31, stage 2a): compiled programs.
;
;   jit2-correct  a compiled closure program answers its meaning through
;                 the stage-2 JIT: through the depth-addressed code when
;                 the check passes (jit2-sim), through stage 1's when it
;                 does not (jit-correct)
;   jit2-linear   in at most 10 machine instructions per expression the
;                 meaning evaluates, 8 when the check passes

(in-package "ACL2")

(include-book "jit2-proof")
(include-book "jit-correct")

; the machine steps the stage-2 JIT's code takes for n bytecode steps
(defun jit2-clk (prog n)
  (if (dcheck prog (dinfer prog))
      (j2clk prog (list 0 0 0 nil nil) n)
    (jclk prog (list 0 0 0 nil nil) n)))

(defthm jit2-start
  (equal (nst2 (list 0 0 0 nil nil) code 0 nil) (list 0 0 0 nil nil nil))
  :hints (("Goal" :in-theory (enable nst2 npc2))))

(defthm dinv-start
  (implies (dcheck prog dmap) (dinv prog dmap (list 0 0 0 nil nil)))
  :hints (("Goal" :in-theory (enable dinv dctl))))

; the machine's answer is the bytecode's, when the views agree
(defthm vcs-answer-nview
  (implies (equal (nview2 r) (emb2 s code))
           (equal (vcs-answer (nview r)) (vcs-answer s)))
  :hints (("Goal" :in-theory (enable vcs-answer nview nview2 emb2))))

(defthm jit2-correct-checked
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k)
                (dcheck (vcs-program e defs) (dinfer (vcs-program e defs))))
           (equal (jit2-run-program e defs (jit2-clk (vcs-program e defs) (+ (sclk e nil nil defs fuel) k)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (e/d (jit2-run-program jit2 vcs-run-program jit2-clk)
                                  (jit2-sim vcs-correct vcs-answer-nview jit2-checked nview nview2 emb2 nst2
                                   vcs-program j2clk dinfer dcheck dinv-start jit2-start))
                  :use ((:instance vcs-correct)
                        (:instance dinv-start (prog (vcs-program e defs)) (dmap (dinfer (vcs-program e defs))))
                        (:instance jit2-start (code (car (vcs-program e defs))))
                        (:instance jit2-sim (prog (vcs-program e defs)) (dmap (dinfer (vcs-program e defs)))
                                   (s (list 0 0 0 nil nil)) (y 0) (x nil)
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance vcs-answer-nview (code (car (vcs-program e defs)))
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k)))
                                   (r (nrun (jit2-checked (vcs-program e defs) (dinfer (vcs-program e defs)))
                                            (list 0 0 0 nil nil nil)
                                            (j2clk (vcs-program e defs) (list 0 0 0 nil nil)
                                                   (+ (sclk e nil nil defs fuel) k)))))))))

(defthm jit2-correct-fallback
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k)
                (not (dcheck (vcs-program e defs) (dinfer (vcs-program e defs)))))
           (equal (jit2-run-program e defs (jit2-clk (vcs-program e defs) (+ (sclk e nil nil defs fuel) k)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (e/d (jit2-run-program jit2 jit2-clk jit-run-program)
                                  (jit-correct vcs-program dinfer dcheck jit jclk))
                  :use ((:instance jit-correct)))))

; A COMPILED PROGRAM THROUGH THE STAGE-2 JIT answers what its meaning does
(defthm jit2-correct
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (jit2-run-program e defs (jit2-clk (vcs-program e defs) (+ (sclk e nil nil defs fuel) k)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable jit2-correct-checked jit2-correct-fallback jit2-run-program jit2-clk)
                  :use (jit2-correct-checked jit2-correct-fallback))))

; AND IN LINEAR TIME
(defthm jit2-linear
  (implies (natp k)
           (<= (jit2-clk (vcs-program e defs) (+ (sclk e nil nil defs fuel) k))
               (+ (* 10 (cevals e nil nil defs fuel)) (* 5 k))))
  :hints (("Goal" :in-theory (e/d (jit2-clk) (jit2-clock-bound jit-clock-bound sclk-linear))
                  :use ((:instance jit2-clock-bound (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance jit-clock-bound (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance sclk-linear (env nil) (caps nil))))))

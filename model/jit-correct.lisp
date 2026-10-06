; clotran's JIT, formally (PLAN step 31, stage 1): compiled programs.
;
;   jit-correct   a closure program compiled to stack bytecode and then
;                 translated by the baseline JIT answers, on the machine
;                 code, what its meaning does
;   jit-linear    in at most 10 machine instructions per expression the
;                 meaning evaluates
;
; jit-sim (jit-proof.lisp) is the JIT alone, for any bytecode whose run
; has its operands; a compiled program's run reads only slots that exist
; (vcs-program-reads), so it is one, and vcs-correct says what the
; bytecode answers.

(in-package "ACL2")

(include-book "jit-proof")
(include-book "vm-closure-rooted")
(include-book "vm-closure-cost")

(defthm reads-ok-jok
  (implies (reads-ok prog s) (jok prog s))
  :hints (("Goal" :in-theory (enable reads-ok jok))))

(defthm run-reads-ok-jok
  (implies (run-reads-ok prog s n) (run-jok prog s n))
  :hints (("Goal" :induct (run-jok prog s n) :in-theory (disable reads-ok jok)
                  :expand ((run-reads-ok prog s n) (run-jok prog s n)))))

(defthm jfntab-ok-vcs-defs
  (jfntab-ok (cdr (vcs-defs ds pc)))
  :hints (("Goal" :induct (vcs-defs ds pc))))

(defthm jfntab-ok-vcs-program
  (jfntab-ok (cdr (vcs-program e defs)))
  :hints (("Goal" :in-theory (enable vcs-program))))

; the machine's answer is the bytecode's
(defthm vcs-answer-emb
  (equal (vcs-answer (emb s code)) (vcs-answer s))
  :hints (("Goal" :in-theory (enable vcs-answer emb))))

(defthm jit-start
  (equal (nst (list 0 0 0 nil nil) code nil) (list 0 0 0 nil nil nil))
  :hints (("Goal" :in-theory (enable nst emb npc))))

; A COMPILED PROGRAM THROUGH THE JIT answers what its meaning does
(defthm jit-correct
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (jit-run-program e defs (jclk (vcs-program e defs) (list 0 0 0 nil nil)
                                                (+ (sclk e nil nil defs fuel) k)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (e/d (jit-run-program vcs-run-program)
                                  (jit-sim vcs-correct vcs-program-reads run-reads-ok-jok jit nview emb nst
                                   vcs-program jclk vcs-answer-emb))
                  :use ((:instance vcs-correct)
                        (:instance vcs-program-reads)
                        (:instance run-reads-ok-jok (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance jit-sim (prog (vcs-program e defs)) (s (list 0 0 0 nil nil)) (x nil)
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance vcs-answer-emb (code (car (vcs-program e defs)))
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k))))))))

; AND IN LINEAR TIME: the meaning's own count of expressions bounds the
; machine instructions, five per bytecode and two bytecodes per expression
(defthm jit-linear
  (implies (natp k)
           (<= (jclk (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k))
               (+ (* 10 (cevals e nil nil defs fuel)) (* 5 k))))
  :hints (("Goal" :in-theory (disable jit-clock-bound sclk-linear)
                  :use ((:instance jit-clock-bound (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance sclk-linear (env nil) (caps nil))))))

; clotran's VM, formally (PLAN step 30): A FUSED PROGRAM ANSWERS WHAT THE
; PROGRAM DOES. Each superinstruction of vmf.lisp is the run of
; instructions it replaces (vmi-f17-steps ..), so a vmi-xstep is one to
; four vmi-steps and a fused run is a run at least as long (vmi-xrun-is).
; The pass writes only a load's fourth word, which nothing reads back:
; the fused machine is the compiled one in every fact vmi-correct uses,
; so vmf-correct is vmic-correct for the fused run.

(in-package "ACL2")

(include-book "vmf")
(include-book "vmic-correct")

(defthm update-nth-update-nth-diff
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i a (update-nth j b x)) (update-nth j b (update-nth i a x))))
  :rule-classes ((:rewrite :loop-stopper ((i j))))
  :hints (("Goal" :in-theory (enable update-nth))))

; one step, its instruction known
(defmacro step-is (k f)
  `(defthm ,(intern-in-package-of-symbol (concatenate 'string "VMI-STEP-" (symbol-name f)) 'vmi-step)
     (implies (and (equal (nth 3 vmi) 0) (equal (vmi-w (nth 0 vmi) 0 vmi) ,k)) (equal (vmi-step vmi) (,f vmi)))
     :hints (("Goal" :in-theory (enable vmi-step)))))
(step-is 1 vmi-push)
(step-is 2 vmi-load)
(step-is 3 vmi-add)
(step-is 4 vmi-lt)
(step-is 6 vmi-jmpf)
(step-is 13 vmi-prim)

(in-theory (disable vmi-step))

(defmacro vmf-at (p o) `(equal (vmi-w ,p 0 vmi) ,o))

(defthm vmi-f17-steps
  (implies (and (vmi-shape vmi) (natp (v-pc vmi)) (natp (v-sp vmi)) (natp (v-fb vmi)) (equal (v-status vmi) 0) (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 1)
                (vmf-at (+ 2 (v-pc vmi)) 4) (vmf-at (+ 3 (v-pc vmi)) 6) (vmf-room vmi))
           (equal (vmi-f17 vmi) (vmi-step (vmi-step (vmi-step (vmi-step vmi))))))
  :hints (("Goal" :in-theory (disable vmi-callv vmi-ret vmi-recur vmi-prim vmi-mkclo vmi-capt vmi-throw vmi-try vmi-endtry))))

(defthm vmi-f18-steps
  (implies (and (vmi-shape vmi) (natp (v-pc vmi)) (natp (v-sp vmi)) (natp (v-fb vmi)) (equal (v-status vmi) 0)
                (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 1) (vmf-at (+ 2 (v-pc vmi)) 3) (vmf-room vmi))
           (equal (vmi-f18 vmi) (vmi-step (vmi-step (vmi-step vmi)))))
  :hints (("Goal" :in-theory (disable vmi-callv vmi-ret vmi-recur vmi-prim vmi-mkclo vmi-capt vmi-throw vmi-try vmi-endtry))))

(defthm vmi-f19-steps
  (implies (and (vmi-shape vmi) (natp (v-pc vmi)) (natp (v-sp vmi)) (natp (v-fb vmi)) (equal (v-status vmi) 0)
                (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 2) (vmf-at (+ 2 (v-pc vmi)) 3) (vmf-room vmi))
           (equal (vmi-f19 vmi) (vmi-step (vmi-step (vmi-step vmi)))))
  :hints (("Goal" :in-theory (disable vmi-callv vmi-ret vmi-recur vmi-prim vmi-mkclo vmi-capt vmi-throw vmi-try vmi-endtry))))

(defmacro f-hyps (&rest ats)
  `(and (vmi-shape vmi) (natp (v-pc vmi)) (natp (v-sp vmi)) (natp (v-fb vmi)) (equal (v-status vmi) 0)
        (vmf-room vmi) ,@ats))

(defmacro f-theory ()
  '(disable vmi-callv vmi-ret vmi-recur vmi-mkclo vmi-capt vmi-throw vmi-try vmi-endtry vmi-unwind))

; the prim's answer, as the fused step computes it
(defmacro f20-r ()
  '(prim (vmi-poolv (vmi-w (+ 2 (v-pc vmi)) 1 vmi) vmi)
         (list (vmi-sreg (+ (v-fb vmi) (nfix (vmi-w (v-pc vmi) 1 vmi))) vmi) (vmi-poolv (vmi-w (+ 1 (v-pc vmi)) 1 vmi) vmi))))

(defthm stk-from-1 (equal (stk-from a 1 l) (list (sreg a l))) :hints (("Goal" :expand ((stk-from a 1 l)))))
(defthm stk-from-2 (implies (natp a) (equal (stk-from a 2 l) (list (sreg a l) (sreg (+ 1 a) l)))) :hints (("Goal" :expand ((stk-from a 2 l) (stk-from (+ 1 a) 1 l)))))

(defthm vmi-f20-steps
  (implies (f-hyps (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 1) (vmf-at (+ 2 (v-pc vmi)) 13)
                   (equal (vmi-w (+ 2 (v-pc vmi)) 2 vmi) 2) (vmf-at (+ 3 (v-pc vmi)) 6))
           (equal (vmi-f20 vmi)
                  (if (throwp (f20-r))
                      (vmi-step (vmi-step (vmi-step vmi)))
                    (vmi-step (vmi-step (vmi-step (vmi-step vmi)))))))
  :hints (("Goal" :in-theory (f-theory))))

(defthm vmi-f21-steps
  (implies (f-hyps (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 13) (equal (vmi-w (+ 1 (v-pc vmi)) 2 vmi) 1))
           (equal (vmi-f21 vmi) (vmi-step (vmi-step vmi))))
  :hints (("Goal" :in-theory (f-theory))))

(defthm vmi-f22-steps
  (implies (f-hyps (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 2) (vmf-at (+ 2 (v-pc vmi)) 13)
                   (equal (vmi-w (+ 2 (v-pc vmi)) 2 vmi) 2))
           (equal (vmi-f22 vmi) (vmi-step (vmi-step (vmi-step vmi)))))
  :hints (("Goal" :in-theory (f-theory))))

(defthm vmi-f23-steps
  (implies (f-hyps (vmf-at (v-pc vmi) 2) (vmf-at (+ 1 (v-pc vmi)) 1) (vmf-at (+ 2 (v-pc vmi)) 13)
                   (equal (vmi-w (+ 2 (v-pc vmi)) 2 vmi) 2))
           (equal (vmi-f23 vmi) (vmi-step (vmi-step (vmi-step vmi)))))
  :hints (("Goal" :in-theory (f-theory))))

(in-theory (disable vmi-f17 vmi-f18 vmi-f19 vmi-f20 vmi-f21 vmi-f22 vmi-f23))

; ---- A FUSED STEP IS ONE TO FOUR STEPS ---------------------------------------------------------

(defun vmi-xcount (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((p (nfix (v-pc vmi))))
    (if (and (equal (v-status vmi) 0) (< (+ 15 (* 4 p)) (v-code-length vmi)) (equal (vmi-w p 0 vmi) 2) (vmf-room vmi))
        (let ((tag (vmi-w p 3 vmi)))
          (cond ((and (equal tag 17) (equal (vmi-w (+ p 1) 0 vmi) 1) (equal (vmi-w (+ p 2) 0 vmi) 4)
                      (equal (vmi-w (+ p 3) 0 vmi) 6))
                 4)
                ((and (equal tag 18) (equal (vmi-w (+ p 1) 0 vmi) 1) (equal (vmi-w (+ p 2) 0 vmi) 3)) 3)
                ((and (equal tag 19) (equal (vmi-w (+ p 1) 0 vmi) 2) (equal (vmi-w (+ p 2) 0 vmi) 3)) 3)
                ((and (equal tag 20) (equal (vmi-w (+ p 1) 0 vmi) 1) (equal (vmi-w (+ p 2) 0 vmi) 13) (equal (vmi-w (+ p 2) 2 vmi) 2)
                      (equal (vmi-w (+ p 3) 0 vmi) 6))
                 (if (throwp (prim (vmi-poolv (vmi-w (+ p 2) 1 vmi) vmi)
                                   (list (vmi-sreg (+ (nfix (v-fb vmi)) (nfix (vmi-w p 1 vmi))) vmi) (vmi-poolv (vmi-w (+ p 1) 1 vmi) vmi))))
                     3 4))
                ((and (equal tag 21) (equal (vmi-w (+ p 1) 0 vmi) 13) (equal (vmi-w (+ p 1) 2 vmi) 1)) 2)
                ((and (equal tag 22) (equal (vmi-w (+ p 1) 0 vmi) 2) (equal (vmi-w (+ p 2) 0 vmi) 13) (equal (vmi-w (+ p 2) 2 vmi) 2)) 3)
                ((and (equal tag 23) (equal (vmi-w (+ p 1) 0 vmi) 1) (equal (vmi-w (+ p 2) 0 vmi) 13) (equal (vmi-w (+ p 2) 2 vmi) 2)) 3)
                (t 1)))
      1)))

(defthm vmi-xstep-is
  (implies (and (vmi-shape vmi) (natp (v-pc vmi)) (natp (v-sp vmi)) (natp (v-fb vmi)))
           (equal (vmi-xstep vmi) (vmi-run (vmi-xcount vmi) vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-run) (vmi-load vmi-push vmi-lt vmi-add vmi-jmpf vmi-prim)))))

(defthm vmi-xstep-stopped (implies (not (equal (v-status vmi) 0)) (equal (vmi-xstep vmi) vmi))
  :hints (("Goal" :in-theory (enable vmi-step))))

(in-theory (disable vmi-xstep vmi-xcount))

(defthm vmi-xcount-pos (and (integerp (vmi-xcount vmi)) (< 0 (vmi-xcount vmi))) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable vmi-xcount))))

(defthm vmi-run-plus
  (implies (and (natp a) (natp b)) (equal (vmi-run (+ a b) vmi) (vmi-run b (vmi-run a vmi))))
  :hints (("Goal" :induct (vmi-run a vmi) :in-theory (disable vmi-step))))

(defun-nx vmi-xsteps (n vmi)
  (declare (xargs :verify-guards nil))
  (if (zp n) 0 (+ (vmi-xcount vmi) (vmi-xsteps (1- n) (vmi-xstep vmi)))))

(defthm vmi-xsteps-bound (implies (natp n) (<= n (vmi-xsteps n vmi))) :rule-classes :linear)
(defthm vmi-xsteps-natp (natp (vmi-xsteps n vmi)) :rule-classes :type-prescription)

(defthm vmi-xrun-stopped (implies (not (equal (v-status vmi) 0)) (equal (vmi-xrun n vmi) vmi)))
(defthm vmi-run-stopped (implies (not (equal (v-status vmi) 0)) (equal (vmi-run n vmi) vmi))
  :hints (("Goal" :in-theory (enable vmi-run))))

(defthm vmi-run-zero (implies (zp n) (equal (vmi-run n vmi) vmi)) :hints (("Goal" :in-theory (enable vmi-run))))

(defthm vmi-ok-regs (implies (vmi-ok vmi) (and (natp (v-pc vmi)) (natp (v-sp vmi)) (natp (v-fb vmi))))
  :rule-classes :forward-chaining)

; A FUSED RUN is a run at least as long
(defthm vmi-xrun-is
  (implies (and (vmi-shape vmi) (vmi-ok vmi))
           (equal (vmi-xrun n vmi) (vmi-run (vmi-xsteps n vmi) vmi)))
  :hints (("Goal" :induct (vmi-xrun n vmi) :in-theory (disable vmi-ok vmi-shape vmi-prog vmi-run))
          ("Subgoal *1/2" :cases ((equal (v-status (vmi-xstep vmi)) 0))
                          :use ((:instance vmi-run-refines (n (vmi-xcount vmi)))))))

; ---- THE PASS CHANGES NOTHING ANYTHING READS -------------------------------------------------
;
; It writes only a load's fourth word: the machine is the same but for
; the code, and the code reads back as the same instructions.

(defmacro code-is (c) `(update-nth 6 ,c vmi))

(defthm vmi-sreg-code (equal (vmi-sreg i (code-is c)) (vmi-sreg i vmi)) :hints (("Goal" :in-theory (enable vmi-sreg))))
(defthm vmi-poolv-code (equal (vmi-poolv i (code-is c)) (vmi-poolv i vmi)) :hints (("Goal" :in-theory (enable vmi-poolv))))
(defthm hidx-of-code (equal (hidx-of i (code-is c)) (hidx-of i vmi)))
(defthm prevs-ok-code (equal (prevs-ok i (code-is c)) (prevs-ok i vmi)))
(defthm vmi-ctl-code (equal (vmi-ctl i (code-is c)) (vmi-ctl i vmi)))
(defthm vmi-stk-list-code (equal (vmi-stk-list i k (code-is c)) (vmi-stk-list i k vmi)))
(defthm vmi-clauses-code (equal (vmi-clauses ci k (code-is c)) (vmi-clauses ci k vmi)))
(defthm vmi-fntab-code (equal (vmi-fntab f k (code-is c)) (vmi-fntab f k vmi)))

(defthm vmi-fuse-is-code
  (implies (< 6 (len vmi)) (equal (vmi-fuse i n vmi) (code-is (nth 6 (vmi-fuse i n vmi)))))
  :rule-classes nil
  :hints (("Goal" :induct (vmi-fuse i n vmi))))

(defthm len-code-fuse (equal (len (nth 6 (vmi-fuse i n vmi))) (len (nth 6 vmi))))

(defthm word-index-3
  (implies (and (integerp a) (integerp b) (natp k) (< k 4))
           (equal (equal (+ k (* 4 a)) (+ 3 (* 4 b))) (and (equal a b) (equal k 3))))
  :hints (("Goal" :cases ((< a b) (equal a b)))))

(defthm vmi-w-load-word3
  (implies (and (natp i) (< (+ 3 (* 4 i)) (len (nth 6 vmi))) (< (nfix k) 4))
           (equal (vmi-w pc k (code-is (update-nth (+ 3 (* 4 i)) v (nth 6 vmi))))
                  (if (and (equal (nfix pc) i) (equal (nfix k) 3)) v (vmi-w pc k vmi))))
  :hints (("Goal" :in-theory (enable vmi-w) :use ((:instance word-index-3 (a (nfix pc)) (b i) (k (nfix k)))))))

(defthm vmi-w-not-natp (implies (not (natp pc)) (equal (vmi-w pc k vmi) (vmi-w 0 k vmi))) :hints (("Goal" :in-theory (enable vmi-w))))

(defthm vmi-ins-load-word3
  (implies (and (natp i) (< (+ 3 (* 4 i)) (len (nth 6 vmi))) (equal (vmi-w i 0 vmi) 2))
           (equal (vmi-ins pc (code-is (update-nth (+ 3 (* 4 i)) v (nth 6 vmi)))) (vmi-ins pc vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-ins) (vmi-w)))))

(defthm vmi-ins-load-word3-0
  (implies (and (< 3 (len (nth 6 vmi))) (equal (vmi-w 0 0 vmi) 2))
           (equal (vmi-ins pc (code-is (update-nth 3 v (nth 6 vmi)))) (vmi-ins pc vmi)))
  :hints (("Goal" :use ((:instance vmi-ins-load-word3 (i 0))) :in-theory (disable vmi-ins-load-word3 vmi-ins))))

(defthm vmi-ins-fuse (equal (vmi-ins pc (vmi-fuse i n vmi)) (vmi-ins pc vmi))
  :hints (("Goal" :induct (vmi-fuse i n vmi) :in-theory (disable vmi-ins))))

(defthm vmi-code-list-fuse (equal (vmi-code-list pc k (vmi-fuse i n vmi)) (vmi-code-list pc k vmi))
  :hints (("Goal" :induct (vmi-code-list pc k vmi) :in-theory (e/d (vmi-code-list) (vmi-ins vmi-fuse)))))

(defmacro fused () '(vmi-fuse-prog vmi))

(defthm vmi-fuse-prog-facts
  (implies (and (vmi-shape vmi) (vmi-ok vmi))
           (and (vmi-shape (fused)) (vmi-ok (fused))
                (equal (vmi-prog (fused)) (vmi-prog vmi))
                (equal (vmi-abs (fused)) (vmi-abs vmi))
                (equal (nth 8 (fused)) (nth 8 vmi))))
  :hints (("Goal" :in-theory (e/d (vmi-fuse-prog vmi-shape vmi-ok vmi-prog vmi-abs) (vmi-fuse vmi-code-list))
                  :use ((:instance vmi-fuse-is-code (i 0) (n (len (nth 6 vmi))))))))

; ---- THE THEOREM -------------------------------------------------------------------------------

(in-theory (disable vmi-fuse-prog vmi-xrun))

; a machine that reads back as a compiled program at its start, run fused
(defthm vmf-machine-correct
  (implies (and (vmi-shape s) (vmi-ok s) (equal (vmi-prog s) (vcs2-program e defs))
                (equal (vmi-abs s) (list 0 0 0 (nth 8 s) nil))
                (x2defs-ok defs) (x2wf e 0 nil)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmi-xrun (+ (s2clk e nil nil defs fuel) k) s)) 2)))
           (equal (vcs2-answer (vmi-abs (vmi-xrun (+ (s2clk e nil nil defs fuel) k) s)))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable vmi-run vcs2-run mx2 s2clk vmi-xsteps vmi-abs vmi-prog vmi-ok vmi-shape
                                      vcs2-answer vcs2-program vmi-run-refines vcs2-correct-stk vmi-xsteps-bound)
                  :use ((:instance vmi-xsteps-bound (n (+ (s2clk e nil nil defs fuel) k)) (vmi s))
                        (:instance vmi-run-refines (n (vmi-xsteps (+ (s2clk e nil nil defs fuel) k) s)) (vmi s))
                        (:instance vcs2-correct-stk (stk (nth 8 s))
                                   (k (- (vmi-xsteps (+ (s2clk e nil nil defs fuel) k) s) (s2clk e nil nil defs fuel))))))))

(defmacro fprog () '(vmi-fuse-prog (car (vmic-program e defs nstk nctl vmi vce))))

; A PROGRAM THE COMPILER COMPILES without an error or an overflow, FUSED
; and run by vmi-xrun, answers what its meaning does -- its value, or
; the value of a throw nothing caught -- unless an array overflowed.
(defthm vmf-correct
  (implies (and (vmip vmi) (x2defs-ok defs) (x2wf e 0 nil) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl)
                (vp-ok)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmi-xrun (+ (s2clk e nil nil defs fuel) k) (fprog))) 2)))
           (equal (vcs2-answer (vmi-abs (vmi-xrun (+ (s2clk e nil nil defs fuel) k) (fprog))))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))
                  :use (vp-shape-ok vp-prog vp-abs
                        (:instance vmi-fuse-prog-facts (vmi (car (vmic-program e defs nstk nctl vmi vce))))
                        (:instance vmf-machine-correct (s (fprog)))))))

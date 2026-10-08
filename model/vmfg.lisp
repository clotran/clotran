; clotran's VM, formally (PLAN step 30): THE SUPERINSTRUCTIONS' DEFINITIONS
; THE FORTRAN IS GENERATED FROM. vmf.lisp's fused step and pass, word for
; word, with guards and every integer result declared 64-bit, as vmg.lisp
; is vmi.lisp's machine.
;
;   vmg-xstep-is ..     each is its vmf twin
;   vmg-xstep-good      a fused step keeps the bounds, so vmg-xrun's
;                       guard holds for a whole run
;   vmfg-correct        the generated pipeline: vmicg-program, then
;                       vmg-fuse-prog, then vmg-xrun, answers what the
;                       program means unless an array overflowed

(in-package "ACL2")

(include-book "vmg")
(include-book "vmf-proof")
(include-book "vmicg")

(defmacro vmg-room (vmi) `(< (i64 (1+ (nfix (v-sp ,vmi)))) (v-stk-length ,vmi)))

; the run inside the code, the stack with room
(defmacro vmg-fast (vmi)
  `(and (vmg-bnd ,vmi) (< (+ 15 (* 4 (nfix (v-pc ,vmi)))) (v-code-length ,vmi)) (vmg-room ,vmi)))

(defun vmg-f17 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w p 1 vmi)))) vmi))
         (y (vmg-poolv (vmg-w (i64 (+ p 1)) 1 vmi) vmi))
         (b (rt-lt x y))
         (vmi (update-v-stki sp b vmi))
         (vmi (update-v-stki (i64 (+ sp 1)) y vmi))
         (vmi (update-v-sp sp vmi)))
    (if (rt-truthy b)
        (update-v-pc (i64 (+ p 4)) vmi)
      (update-v-pc (nfix (vmg-w (i64 (+ p 3)) 1 vmi)) vmi))))

(defun vmg-f18 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w p 1 vmi)))) vmi))
         (y (vmg-poolv (vmg-w (i64 (+ p 1)) 1 vmi) vmi))
         (vmi (update-v-stki sp (rt-add x y) vmi))
         (vmi (update-v-stki (i64 (+ sp 1)) y vmi))
         (vmi (update-v-sp (i64 (+ sp 1)) vmi)))
    (update-v-pc (i64 (+ p 3)) vmi)))

(defun vmg-f19 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi))) (fb (nfix (v-fb vmi)))
         (x (vmg-sreg (i64 (+ fb (nfix (vmg-w p 1 vmi)))) vmi))
         (vmi (update-v-stki sp x vmi))
         (y (vmg-sreg (i64 (+ fb (nfix (vmg-w (i64 (+ p 1)) 1 vmi)))) vmi))
         (vmi (update-v-stki sp (rt-add x y) vmi))
         (vmi (update-v-stki (i64 (+ sp 1)) y vmi))
         (vmi (update-v-sp (i64 (+ sp 1)) vmi)))
    (update-v-pc (i64 (+ p 3)) vmi)))

(defun vmg-xstep (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-good vmi) :verify-guards nil))
  (let ((p (nfix (v-pc vmi))))
    (if (and (equal (v-status vmi) 0) (< (i64 (+ 15 (i64 (* 4 p)))) (v-code-length vmi))
             (equal (vmg-w p 0 vmi) 2) (vmg-room vmi))
        (let ((tag (vmg-w p 3 vmi)))
          (cond ((and (equal tag 17) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 1) (equal (vmg-w (i64 (+ p 2)) 0 vmi) 4)
                      (equal (vmg-w (i64 (+ p 3)) 0 vmi) 6))
                 (vmg-f17 vmi))
                ((and (equal tag 18) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 1) (equal (vmg-w (i64 (+ p 2)) 0 vmi) 3))
                 (vmg-f18 vmi))
                ((and (equal tag 19) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 2) (equal (vmg-w (i64 (+ p 2)) 0 vmi) 3))
                 (vmg-f19 vmi))
                (t (vmg-step vmi))))
      (vmg-step vmi))))

; ---- THE PASS --------------------------------------------------------------------------------

(defun vmg-tag (i vmi)
  (declare (xargs :stobjs vmi :guard (and (natp i) (<= (+ 3 i) *b40*))))
  (let ((o1 (vmg-w (i64 (+ i 1)) 0 vmi)) (o2 (vmg-w (i64 (+ i 2)) 0 vmi)) (o3 (vmg-w (i64 (+ i 3)) 0 vmi)))
    (cond ((and (equal o1 1) (equal o2 4) (equal o3 6)) 17)
          ((and (equal o1 1) (equal o2 3)) 18)
          ((and (equal o1 2) (equal o2 3)) 19)
          (t 0))))

(defun vmg-fuse (i n vmi)
  (declare (xargs :stobjs vmi :measure (nfix (- (nfix n) (nfix i))) :verify-guards nil
                  :guard (and (natp i) (<= i *b40*) (natp n) (<= (v-code-length vmi) *b40*))))
  (if (or (<= (nfix n) (nfix i)) (<= (v-code-length vmi) (i64 (+ 3 (i64 (* 4 (nfix i)))))))
      vmi
    (let ((vmi (if (equal (vmg-w (nfix i) 0 vmi) 2)
                   (update-v-codei (i64 (+ 3 (i64 (* 4 (nfix i))))) (vmg-tag (nfix i) vmi) vmi)
                 vmi)))
      (vmg-fuse (i64 (1+ (nfix i))) n vmi))))

(defun vmg-fuse-prog (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (<= (v-code-length vmi) *b40*) (vmg-fuse 0 (v-code-length vmi) vmi) vmi))

; ==== EACH IS ITS vmf TWIN ======================================================================

(defthm vmg-f17-is (equal (vmg-f17 vmi) (vmi-f17 vmi))
  :hints (("Goal" :in-theory (enable vmi-f17 vmg-w-is vmg-sreg-is vmg-poolv-is))))
(defthm vmg-f18-is (equal (vmg-f18 vmi) (vmi-f18 vmi))
  :hints (("Goal" :in-theory (enable vmi-f18 vmg-w-is vmg-sreg-is vmg-poolv-is))))
(defthm vmg-f19-is (equal (vmg-f19 vmi) (vmi-f19 vmi))
  :hints (("Goal" :in-theory (enable vmi-f19 vmg-w-is vmg-sreg-is vmg-poolv-is))))
(defthm vmg-xstep-is (equal (vmg-xstep vmi) (vmi-xstep vmi))
  :hints (("Goal" :in-theory (e/d (vmi-xstep vmg-w-is vmg-step-is) (vmg-f17 vmg-f18 vmg-f19 vmi-f17 vmi-f18 vmi-f19 vmg-step vmi-step)))))
(defthm vmg-tag-is (equal (vmg-tag i vmi) (vmf-tag i vmi)) :hints (("Goal" :in-theory (enable vmg-w-is))))
(defthm vmg-fuse-is (equal (vmg-fuse i n vmi) (vmi-fuse i n vmi))
  :hints (("Goal" :induct (vmg-fuse i n vmi) :in-theory (e/d (vmg-w-is) (vmg-tag vmf-tag)))))
(defthm vmg-fuse-prog-is (equal (vmg-fuse-prog vmi) (vmi-fuse-prog vmi)) :hints (("Goal" :in-theory (enable vmi-fuse-prog))))

; ==== THE GUARDS, AND THE BOUNDS KEPT ===========================================================

(defmacro def-fbnd (name f)
  `(defthm ,name
     (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-fast vmi)) (vmg-bnd (,f vmi)))
     :hints (("Goal" :do-not-induct t
                     :in-theory (e/d (,f vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth
                                                    vmg-f17-is vmg-f18-is vmg-f19-is))))))
(def-fbnd vmg-f17-bnd vmg-f17)
(def-fbnd vmg-f18-bnd vmg-f18)
(def-fbnd vmg-f19-bnd vmg-f19)

(in-theory (disable vmg-f17-is vmg-f18-is vmg-f19-is))

(defthm vmg-f-status
  (and (equal (v-status (vmg-f17 vmi)) (v-status vmi))
       (equal (v-status (vmg-f18 vmi)) (v-status vmi))
       (equal (v-status (vmg-f19 vmi)) (v-status vmi)))
  :hints (("Goal" :in-theory (e/d (vmg-f17 vmg-f18 vmg-f19) (vmg-w)))))

(verify-guards vmg-f17 :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok))))
(verify-guards vmg-f18 :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok))))
(verify-guards vmg-f19 :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok))))
(verify-guards vmg-xstep
  :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok vmg-f17 vmg-f18 vmg-f19 vmg-step))))

(defthm vmg-xstep-good
  (implies (and (vmip vmi) (vmg-good vmi)) (vmg-good (vmg-xstep vmi)))
  :hints (("Goal" :in-theory (e/d (vmg-xstep vmg-good) (vmg-f17 vmg-f18 vmg-f19 vmg-step vmg-bnd vmg-xstep-is))
                  :use (vmg-step-good))))

(in-theory (disable vmg-xstep))

; A FUSED RUN, step after step, every step in 64 bits
(defun vmg-xrun (n vmi)
  (declare (xargs :stobjs vmi :guard (and (natp n) (vmg-good vmi))
                  :guard-hints (("Goal" :in-theory (disable vmg-good vmg-xstep-is)))))
  (if (zp n) vmi (let ((vmi (vmg-xstep vmi))) (vmg-xrun (1- n) vmi))))

(defthm vmg-xrun-is (equal (vmg-xrun n vmi) (vmi-xrun n vmi))
  :hints (("Goal" :induct (vmg-xrun n vmi) :in-theory (enable vmi-xrun))))

(verify-guards vmg-tag)
(verify-guards vmg-fuse)
(verify-guards vmg-fuse-prog)

; ==== THE GENERATED PIPELINE ====================================================================

(defmacro gfprog () '(vmg-fuse-prog (car (vmicg-program e defs nstk nctl vmi vce))))

; A PROGRAM THE GENERATED COMPILER COMPILES without an error or an
; overflow, FUSED by the generated pass and RUN by the generated fused
; machine, answers what its meaning does -- its value, or the value of a
; throw nothing caught -- unless an array overflowed while it ran.
(defthm vmfg-correct
  (implies (and (vmip vmi) (x2defs-ok defs) (x2wf e 0 nil) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl)
                (equal (nth 3 (car (vmicg-program e defs nstk nctl vmi vce))) 0)
                (not (failed (mv-nth 1 (vmicg-program e defs nstk nctl vmi vce))))
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmg-xrun (+ (s2clk e nil nil defs fuel) k) (gfprog))) 2)))
           (equal (vcs2-answer (vmi-abs (vmg-xrun (+ (s2clk e nil nil defs fuel) k) (gfprog))))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :cases ((vmicg-small))
                  :in-theory (union-theories '(vmicg-program-is vmicg-program-big vmg-xrun-is vmg-fuse-prog-is)
                                             (theory 'minimal-theory)))
          ("Subgoal 1" :use vmf-correct)))

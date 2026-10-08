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

; the runtime's operations, fused: a throw unwinds where the prim's own
; step would, at the prim with its arguments pushed -- the stack slots;
; the pc and the stack top it would have are the unwind's to overwrite,
; and it reads neither (vmi-unwind-pc-sp)
; a prim's answer that is not a throw: in the run's first slot, the run done
(defun vmg-f20-ok (r vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (vmi (update-v-stki sp r vmi)) (vmi (update-v-sp sp vmi)))
    (if (rt-truthy r)
        (update-v-pc (i64 (+ p 4)) vmi)
      (update-v-pc (nfix (vmg-w (i64 (+ p 3)) 1 vmi)) vmi))))

(defun vmg-fk-ok (r k vmi)
  (declare (xargs :stobjs vmi :guard (and (vmg-fast vmi) (member k '(2 3))) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (vmi (update-v-stki sp r vmi)) (vmi (update-v-sp (i64 (+ sp 1)) vmi)))
    (update-v-pc (i64 (+ p (nfix k))) vmi)))

(defun vmg-f20 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w p 1 vmi)))) vmi))
         (y (vmg-poolv (vmg-w (i64 (+ p 1)) 1 vmi) vmi))
         (r (rt-prim (vmg-poolv (vmg-w (i64 (+ p 2)) 1 vmi) vmi) (list x y)))
         (vmi (update-v-stki sp x vmi))
         (vmi (update-v-stki (i64 (+ sp 1)) y vmi)))
    (if (rt-throwp r)
        (vmg-unwind (rt-thrown r) vmi)
      (vmg-f20-ok r vmi))))

(defun vmg-f21 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w p 1 vmi)))) vmi))
         (r (rt-prim (vmg-poolv (vmg-w (i64 (+ p 1)) 1 vmi) vmi) (list x)))
         (vmi (update-v-stki sp x vmi)))
    (if (rt-throwp r)
        (vmg-unwind (rt-thrown r) vmi)
      (vmg-fk-ok r 2 vmi))))

(defun vmg-f22 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi))) (fb (nfix (v-fb vmi)))
         (x (vmg-sreg (i64 (+ fb (nfix (vmg-w p 1 vmi)))) vmi))
         (vmi (update-v-stki sp x vmi))
         (y (vmg-sreg (i64 (+ fb (nfix (vmg-w (i64 (+ p 1)) 1 vmi)))) vmi))
         (vmi (update-v-stki (i64 (+ sp 1)) y vmi))
         (r (rt-prim (vmg-poolv (vmg-w (i64 (+ p 2)) 1 vmi) vmi) (list x y))))
    (if (rt-throwp r)
        (vmg-unwind (rt-thrown r) vmi)
      (vmg-fk-ok r 3 vmi))))

(defun vmg-f23 (vmi)
  (declare (xargs :stobjs vmi :guard (vmg-fast vmi) :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmg-sreg (i64 (+ (nfix (v-fb vmi)) (nfix (vmg-w p 1 vmi)))) vmi))
         (y (vmg-poolv (vmg-w (i64 (+ p 1)) 1 vmi) vmi))
         (r (rt-prim (vmg-poolv (vmg-w (i64 (+ p 2)) 1 vmi) vmi) (list x y)))
         (vmi (update-v-stki sp x vmi))
         (vmi (update-v-stki (i64 (+ sp 1)) y vmi)))
    (if (rt-throwp r)
        (vmg-unwind (rt-thrown r) vmi)
      (vmg-fk-ok r 3 vmi))))

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
                ((and (equal tag 20) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 1) (equal (vmg-w (i64 (+ p 2)) 0 vmi) 13) (equal (vmg-w (i64 (+ p 2)) 2 vmi) 2) (equal (vmg-w (i64 (+ p 3)) 0 vmi) 6))
                 (vmg-f20 vmi))
                ((and (equal tag 21) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 13) (equal (vmg-w (i64 (+ p 1)) 2 vmi) 1))
                 (vmg-f21 vmi))
                ((and (equal tag 22) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 2) (equal (vmg-w (i64 (+ p 2)) 0 vmi) 13) (equal (vmg-w (i64 (+ p 2)) 2 vmi) 2))
                 (vmg-f22 vmi))
                ((and (equal tag 23) (equal (vmg-w (i64 (+ p 1)) 0 vmi) 1) (equal (vmg-w (i64 (+ p 2)) 0 vmi) 13) (equal (vmg-w (i64 (+ p 2)) 2 vmi) 2))
                 (vmg-f23 vmi))
                (t (vmg-step vmi))))
      (vmg-step vmi))))

; ---- THE PASS --------------------------------------------------------------------------------

(defun vmg-tag (i vmi)
  (declare (xargs :stobjs vmi :guard (and (natp i) (<= (+ 3 i) *b40*))))
  (let ((o1 (vmg-w (i64 (+ i 1)) 0 vmi)) (o2 (vmg-w (i64 (+ i 2)) 0 vmi)) (o3 (vmg-w (i64 (+ i 3)) 0 vmi))
        (n1 (vmg-w (i64 (+ i 1)) 2 vmi)) (n2 (vmg-w (i64 (+ i 2)) 2 vmi)))
    (cond ((and (equal o1 1) (equal o2 4) (equal o3 6)) 17)
          ((and (equal o1 1) (equal o2 13) (equal n2 2) (equal o3 6)) 20)
          ((and (equal o1 13) (equal n1 1)) 21)
          ((and (equal o1 2) (equal o2 13) (equal n2 2)) 22)
          ((and (equal o1 1) (equal o2 13) (equal n2 2)) 23)
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

(defthm vmi-unwind-pc-sp
  (equal (vmi-unwind v (update-nth *v-pc* a (update-nth *v-sp* b vmi))) (vmi-unwind v vmi))
  :hints (("Goal" :in-theory (e/d (vmi-unwind vmi-sset) (nth update-nth)))))

(defthm vmg-f17-is (equal (vmg-f17 vmi) (vmi-f17 vmi))
  :hints (("Goal" :in-theory (enable vmi-f17 vmg-w-is vmg-sreg-is vmg-poolv-is))))
(defthm vmg-f18-is (equal (vmg-f18 vmi) (vmi-f18 vmi))
  :hints (("Goal" :in-theory (enable vmi-f18 vmg-w-is vmg-sreg-is vmg-poolv-is))))
(defthm vmg-f19-is (equal (vmg-f19 vmi) (vmi-f19 vmi))
  :hints (("Goal" :in-theory (enable vmi-f19 vmg-w-is vmg-sreg-is vmg-poolv-is))))
(defthm vmg-f20-is (equal (vmg-f20 vmi) (vmi-f20 vmi))
  :hints (("Goal" :in-theory (enable vmi-f20 vmg-f20-ok vmg-w-is vmg-sreg-is vmg-poolv-is vmg-unwind-is))))
(defthm vmg-f21-is (equal (vmg-f21 vmi) (vmi-f21 vmi))
  :hints (("Goal" :in-theory (enable vmi-f21 vmg-fk-ok vmg-w-is vmg-sreg-is vmg-poolv-is vmg-unwind-is))))
(defthm vmg-f22-is (equal (vmg-f22 vmi) (vmi-f22 vmi))
  :hints (("Goal" :in-theory (enable vmi-f22 vmg-fk-ok vmg-w-is vmg-sreg-is vmg-poolv-is vmg-unwind-is))))
(defthm vmg-f23-is (equal (vmg-f23 vmi) (vmi-f23 vmi))
  :hints (("Goal" :in-theory (enable vmi-f23 vmg-fk-ok vmg-w-is vmg-sreg-is vmg-poolv-is vmg-unwind-is))))
(defthm vmg-xstep-is (equal (vmg-xstep vmi) (vmi-xstep vmi))
  :hints (("Goal" :in-theory (e/d (vmi-xstep vmg-w-is vmg-step-is) (vmg-f17 vmg-f18 vmg-f19 vmg-f20 vmg-f21 vmg-f22 vmg-f23 vmi-f17 vmi-f18 vmi-f19 vmi-f20 vmi-f21 vmi-f22 vmi-f23 vmg-step vmi-step)))))
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

; the prims': a throw unwinds from the machine with the arguments pushed,
; itself in bounds and a stobj
(defthm vmip-stk-true-listp (implies (vmip vmi) (true-listp (nth *v-stki* vmi))) :hints (("Goal" :in-theory (enable vmip))))

(defthm v-stkp-of-true-listp (implies (true-listp l) (v-stkp l)))

(defthm vmg-stk-write-ok
  (implies (and (vmip vmi) (vmg-bnd vmi) (true-listp l) (equal (len l) (len (nth *v-stki* vmi))))
           (and (vmip (update-nth *v-stki* l vmi)) (vmg-bnd (update-nth *v-stki* l vmi))))
  :hints (("Goal" :in-theory (e/d (vmip vmg-bnd) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens)))))

(defthm vmg-unwind-stk-bnd
  (implies (and (vmip vmi) (vmg-bnd vmi) (true-listp l) (equal (len l) (len (nth *v-stki* vmi)))
                (equal (v-status (vmg-unwind v (update-nth *v-stki* l vmi))) 0))
           (vmg-bnd (vmg-unwind v (update-nth *v-stki* l vmi))))
  :hints (("Goal" :in-theory (disable vmg-unwind-bnd vmg-stk-write-ok vmip vmg-bnd vmg-unwind-is)
                  :use (vmg-stk-write-ok (:instance vmg-unwind-bnd (vmi (update-nth *v-stki* l vmi)))))))

(defmacro def-pbnd (name f)
  `(defthm ,name
     (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-fast vmi) (equal (v-status (,f vmi)) 0))
              (vmg-bnd (,f vmi)))
     :hints (("Goal" :do-not-induct t
                     :in-theory (e/d (,f) (vmg-bnd nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth
                                                         vmip vmg-unwind-bnd vmg-unwind-is vmg-unwind
                                                         vmg-f20-is vmg-f21-is vmg-f22-is vmg-f23-is))))))
(defthm vmg-f20-ok-bnd
  (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-fast vmi)) (vmg-bnd (vmg-f20-ok r vmi)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (vmg-f20-ok vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth)))))
(defthm vmg-fk-ok-bnd
  (implies (and (vmip vmi) (equal (v-status vmi) 0) (vmg-fast vmi) (member k '(2 3))) (vmg-bnd (vmg-fk-ok r k vmi)))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (vmg-fk-ok vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth)))))
(defthm vmg-fok-status (and (equal (nth *v-status* (vmg-f20-ok r vmi)) (nth *v-status* vmi))
                            (equal (nth *v-status* (vmg-fk-ok r k vmi)) (nth *v-status* vmi)))
  :hints (("Goal" :in-theory (enable vmg-f20-ok vmg-fk-ok))))
(defthm vmg-stk-write-fast
  (implies (and (vmip vmi) (vmg-fast vmi) (true-listp l) (equal (len l) (len (nth *v-stki* vmi))))
           (vmg-fast (update-nth *v-stki* l vmi)))
  :hints (("Goal" :in-theory (disable vmg-bnd vmip) :use vmg-stk-write-ok)))
(in-theory (disable vmg-f20-ok vmg-fk-ok))

(def-pbnd vmg-f20-bnd vmg-f20)
(def-pbnd vmg-f21-bnd vmg-f21)
(def-pbnd vmg-f22-bnd vmg-f22)
(def-pbnd vmg-f23-bnd vmg-f23)

(in-theory (disable vmg-f17-is vmg-f18-is vmg-f19-is vmg-f20-is vmg-f21-is vmg-f22-is vmg-f23-is))

(defthm vmg-f-status
  (and (equal (v-status (vmg-f17 vmi)) (v-status vmi))
       (equal (v-status (vmg-f18 vmi)) (v-status vmi))
       (equal (v-status (vmg-f19 vmi)) (v-status vmi)))
  :hints (("Goal" :in-theory (e/d (vmg-f17 vmg-f18 vmg-f19) (vmg-w)))))

(verify-guards vmg-f17 :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok))))
(verify-guards vmg-f18 :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok))))
(verify-guards vmg-f19 :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok))))
(verify-guards vmg-f20-ok :hints (("Goal" :in-theory (e/d (vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth)))))
(verify-guards vmg-fk-ok :hints (("Goal" :in-theory (e/d (vmg-bnd bnd40p) (nth update-nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth)))))
(verify-guards vmg-f20 :hints (("Goal" :in-theory (disable vmg-bnd nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth vmip vmg-unwind vmg-unwind-is vmg-f20-ok vmg-fk-ok))))
(verify-guards vmg-f21 :hints (("Goal" :in-theory (disable vmg-bnd nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth vmip vmg-unwind vmg-unwind-is vmg-f20-ok vmg-fk-ok))))
(verify-guards vmg-f22 :hints (("Goal" :in-theory (disable vmg-bnd nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth vmip vmg-unwind vmg-unwind-is vmg-f20-ok vmg-fk-ok))))
(verify-guards vmg-f23 :hints (("Goal" :in-theory (disable vmg-bnd nth words-ok cls-ok fns-ok recs-ok vmg-lens vmg-w rok-nth vmip vmg-unwind vmg-unwind-is vmg-f20-ok vmg-fk-ok))))
(verify-guards vmg-xstep
  :hints (("Goal" :in-theory (disable nth update-nth words-ok cls-ok fns-ok recs-ok vmg-f17 vmg-f18 vmg-f19 vmg-f20 vmg-f21 vmg-f22 vmg-f23 vmg-step))))

(defthm vmg-xstep-good
  (implies (and (vmip vmi) (vmg-good vmi)) (vmg-good (vmg-xstep vmi)))
  :hints (("Goal" :in-theory (e/d (vmg-xstep vmg-good) (vmg-f17 vmg-f18 vmg-f19 vmg-f20 vmg-f21 vmg-f22 vmg-f23 vmg-step vmg-bnd vmg-xstep-is))
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

; clotran's VM, formally (PLAN step 30): SUPERINSTRUCTIONS. A loop in
; vmx2's bytecode runs about 11 instructions an iteration, and what costs
; is not the dispatch but each instruction's own reads and writes of the
; code and the stack (measured: composing the instructions under one
; dispatch was no faster). So a superinstruction here is a direct
; definition of a run of instructions -- the local and the constant read
; once, compared, the branch taken -- proved equal to running them.
;
; THE ENCODING. A load uses only its first operand; the fusion pass
; writes a tag into the load's fourth word (word 3) where the next
; instructions are a run worth fusing:
;
;   17  load a; push k; lt; jmpf t     a loop's test against a constant
;   18  load a; push k; add            a local plus a constant
;   19  load a; load b; add            a local plus a local
;
; The opcode stays 2 and nothing else changes, so a fused program reads
; back as the same program (vmi-ins ignores a load's words 2 and 3) and
; runs the same under vmi-step. The tag is only a hint: vmi-xstep checks
; that the next opcodes are the run's and the stack has room, and
; otherwise takes one ordinary step. So each vmi-xstep is a number of
; vmi-steps (vmf-proof.lisp), and a fused program answers what the
; program does.

(in-package "ACL2")

(include-book "vmi")

; the run's instructions follow, and the stack has room for two pushes
(defmacro vmf-room (vmi)
  `(< (1+ (nfix (v-sp ,vmi))) (v-stk-length ,vmi)))

; 17: load a; push k; lt; jmpf t
(defun vmi-f17 (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmi-sreg (+ (nfix (v-fb vmi)) (nfix (vmi-w p 1 vmi))) vmi))
         (y (vmi-poolv (vmi-w (+ p 1) 1 vmi) vmi))
         (b (bool (< (rfix x) (rfix y))))
         (vmi (update-v-stki sp b vmi))
         (vmi (update-v-stki (+ sp 1) y vmi))
         (vmi (update-v-sp sp vmi)))
    (if (truthy b)
        (update-v-pc (+ p 4) vmi)
      (update-v-pc (nfix (vmi-w (+ p 3) 1 vmi)) vmi))))

; 18: load a; push k; add
(defun vmi-f18 (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi)))
         (x (vmi-sreg (+ (nfix (v-fb vmi)) (nfix (vmi-w p 1 vmi))) vmi))
         (y (vmi-poolv (vmi-w (+ p 1) 1 vmi) vmi))
         (vmi (update-v-stki sp (+ (fix x) (fix y)) vmi))
         (vmi (update-v-stki (+ sp 1) y vmi))
         (vmi (update-v-sp (+ sp 1) vmi)))
    (update-v-pc (+ p 3) vmi)))

; 19: load a; load b; add -- the second load reads the stack after the
; first has written it, as the instructions do
(defun vmi-f19 (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((p (nfix (v-pc vmi))) (sp (nfix (v-sp vmi))) (fb (nfix (v-fb vmi)))
         (x (vmi-sreg (+ fb (nfix (vmi-w p 1 vmi))) vmi))
         (vmi (update-v-stki sp x vmi))
         (y (vmi-sreg (+ fb (nfix (vmi-w (+ p 1) 1 vmi))) vmi))
         (vmi (update-v-stki sp (+ (fix x) (fix y)) vmi))
         (vmi (update-v-stki (+ sp 1) y vmi))
         (vmi (update-v-sp (+ sp 1) vmi)))
    (update-v-pc (+ p 3) vmi)))

; ONE STEP, fused where the tag and the code say so: the run inside the
; code, its instructions there, the stack with room
(defun vmi-xstep (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((p (nfix (v-pc vmi))))
    (if (and (equal (v-status vmi) 0) (< (+ 15 (* 4 p)) (v-code-length vmi)) (equal (vmi-w p 0 vmi) 2) (vmf-room vmi))
        (let ((tag (vmi-w p 3 vmi)))
          (cond ((and (equal tag 17) (equal (vmi-w (+ p 1) 0 vmi) 1) (equal (vmi-w (+ p 2) 0 vmi) 4)
                      (equal (vmi-w (+ p 3) 0 vmi) 6))
                 (vmi-f17 vmi))
                ((and (equal tag 18) (equal (vmi-w (+ p 1) 0 vmi) 1) (equal (vmi-w (+ p 2) 0 vmi) 3))
                 (vmi-f18 vmi))
                ((and (equal tag 19) (equal (vmi-w (+ p 1) 0 vmi) 2) (equal (vmi-w (+ p 2) 0 vmi) 3))
                 (vmi-f19 vmi))
                (t (vmi-step vmi))))
      (vmi-step vmi))))

(defun vmi-xrun (n vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (zp n) vmi (let ((vmi (vmi-xstep vmi))) (vmi-xrun (1- n) vmi))))

; ---- THE PASS: each load that begins a run gets the run's tag ----------------------------

(defun vmf-tag (i vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((o1 (vmi-w (+ i 1) 0 vmi)) (o2 (vmi-w (+ i 2) 0 vmi)) (o3 (vmi-w (+ i 3) 0 vmi)))
    (cond ((and (equal o1 1) (equal o2 4) (equal o3 6)) 17)
          ((and (equal o1 1) (equal o2 3)) 18)
          ((and (equal o1 2) (equal o2 3)) 19)
          (t 0))))

; instructions i .. n-1
(defun vmi-fuse (i n vmi)
  (declare (xargs :stobjs vmi :measure (nfix (- (nfix n) (nfix i))) :verify-guards nil))
  (if (or (<= (nfix n) (nfix i)) (<= (v-code-length vmi) (+ 3 (* 4 (nfix i)))))
      vmi
    (let ((vmi (if (equal (vmi-w (nfix i) 0 vmi) 2)
                   (update-v-codei (+ 3 (* 4 (nfix i))) (vmf-tag (nfix i) vmi) vmi)
                 vmi)))
      (vmi-fuse (1+ (nfix i)) n vmi))))

; the whole code; code longer than 2^40 words is left as it is
(defun vmi-fuse-prog (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (<= (v-code-length vmi) 1099511627776) (vmi-fuse 0 (v-code-length vmi) vmi) vmi))

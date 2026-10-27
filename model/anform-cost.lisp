; THE COST OF THE ANALYZER'S SPECIAL FORMS (model/anform.lisp,
; model/anform-proof.lisp), counted as the generated Fortran runs them: a
; host read (frf-*, frm-*) one step, a generated function's own work one
; step, and in the analyzer's walks a step an element.
;
;   anf-*-reads-bound   each check a constant number of reads: anf-if,
;                       anf-quote, anf-throw, anf-set 1 step, anf-try-op 5,
;                       anf-try-step 6, anf-catch 6 (the name's check
;                       anlocal's, 3), anf-set-target 5, anf-dot 2,
;                       anf-dot-member 6, anf-new 5, anf-def 9
;   anf-try-code-steps-bound  a try's clauses walked: at most 6n + 1 steps,
;                       n clauses
;   (the analyzer's own walks are anbuild-cost.lisp's)

(in-package "ACL2")

(include-book "anform-proof")

; ---- THE CHECKS: READS ALONG THE PATH TAKEN --------------------------------------------------

(defun anf-try-op-reads (f)
  (if (equal (frf-kind f) 3) (if (< 0 (frf-len f)) 5 3) 2))
(defthm anf-try-op-reads-bound (<= (anf-try-op-reads f) 5) :rule-classes :linear)

; the step: the clause's operator, then the code from it
(defun anf-try-step-reads (st f lastp w) (declare (ignore st lastp w)) (+ 1 (anf-try-op-reads f)))
(defthm anf-try-step-reads-bound (<= (anf-try-step-reads st f lastp w) 6) :rule-classes :linear)

(defun anf-catch-reads (f)
  (if (equal (frf-class (frf-nth f 1)) 0) 3 (+ 3 (if (equal (frm-kind (frf-nth f 2)) 2) 3 2))))
(defthm anf-catch-reads-bound (<= (anf-catch-reads f) 6) :rule-classes :linear)

(defun anf-set-target-reads (x)
  (if (and (equal (frf-kind x) 3) (< 0 (frf-len x))) 5 3))
(defthm anf-set-target-reads-bound (<= (anf-set-target-reads x) 5) :rule-classes :linear)

(defun anf-dot-member-reads (n m)
  (cond ((and (equal n 3) (equal (frm-kind m) 2)) 2)
        ((equal (frf-kind m) 3) 5)
        (t 4)))
(defthm anf-dot-member-reads-bound (<= (anf-dot-member-reads n m) 6) :rule-classes :linear)

(defun anf-new-reads (f) (if (< (frf-len f) 2) 2 5))
(defthm anf-new-reads-bound (<= (anf-new-reads f) 5) :rule-classes :linear)

; the count, the docstring's kind, the name and its kind, the var twice
(defun anf-def-reads (f)
  (+ 3 (if (equal (frf-len f) 4) 2 0) (if (equal (frm-kind (frf-nth f 1)) 2) 3 1)))
(defthm anf-def-reads-bound (<= (anf-def-reads f) 9) :rule-classes :linear)

; the counts' checks read nothing: one step each
(defun anf-count-reads (n) (declare (ignore n)) 1)
(defthm anf-count-reads-bound (equal (anf-count-reads n) 1))

(defun anf-dot-reads (f) (declare (ignore f)) 2)
(defthm anf-dot-reads-bound (equal (anf-dot-reads f) 2))

; ---- THE TRY'S WALK ------------------------------------------------------------------------------

(defun anf-try-code-steps (cls st)
  (if (atom cls) 1
    (let* ((lastp (if (atom (cdr cls)) 1 0)) (code (anf-try-step st (car cls) lastp 0)))
      (+ (anf-try-step-reads st (car cls) lastp 0)
         (if (equal code 0) (anf-try-code-steps (cdr cls) (anf-try-step st (car cls) lastp 2)) 1)))))

(defthm anf-try-code-steps-bound
  (<= (anf-try-code-steps cls st) (+ 1 (* 6 (len cls))))
  :hints (("Goal" :in-theory (disable anf-try-step-reads anf-try-step)))
  :rule-classes :linear)

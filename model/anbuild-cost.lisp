; THE COST OF THE ANALYZER'S NODE ASSEMBLY (model/anbuild.lisp), counted as
; the generated Fortran runs it: a host read (frf-*, frm-*) or a builder
; operation one step, a generated function's own work one step, and in its
; walks a step an element. What analysing a subform costs is that subform's
; (each subform is analysed by its own anb-an), a lookup's is anlocal-cost's
; anl-lookup-steps-bound, a check's anform-cost's.
;
;   anb-an-own-bound      one form's dispatch: at most 14 steps before its
;                         driver or the host takes it (the reads, the check's
;                         9 at most, the refusal)
;   anb-listn-steps-bound a list's first n forms: at most n + 1 steps
;   anb-binds-steps-bound, anb-lfinits-steps-bound, anb-lfnames-steps-bound
;                         a binding vector's pairs from i: at most p - i + 1
;   anb-params-steps-bound  a parameter vector from i: at most c - i + 1
;   anb-try-walk-steps-bound  a try's n clauses: at most n + 1, each clause's
;                         step 6 reads more (anform-cost's anf-try-step-reads)
;   anb-try-n-steps-bound, anb-drop-steps-bound, anb-try-fin-steps-bound
;                         the try's scans of its forms: at most n + 1

(in-package "ACL2")

(include-book "anbuild-proof")
(include-book "anform-cost")

(defthm anb-len-bound (<= (frf-len (frf-rest x)) (frf-len x))
  :hints (("Goal" :in-theory (enable frf-rest frf-len frf-kind frm-kind))) :rule-classes :linear)

; ---- ONE FORM'S DISPATCH -------------------------------------------------------------------------

; the reads anb-an makes before a driver or the host has the form: its kind
; (twice), its head's special form and its count, then the check's reads and
; one refusal, or a symbol's id and its lookup
(defun anb-an-own (x)
  (cond ((equal (frf-kind x) 2) 3)
        ((not (equal (frf-kind x) 3)) 2)
        (t (+ 4 (case (frf-sp x)
                  (3 (+ 1 (anf-def-reads x)))
                  (7 (+ 1 (anf-set-target-reads (frf-nth x 1))))
                  (8 (+ 1 (anf-dot-reads x)))
                  (9 (+ 1 (anf-new-reads x)))
                  ((1 4 5) 2)
                  (otherwise 0))))))

(defthm anb-an-own-bound (<= (anb-an-own x) 14) :rule-classes :linear
  :hints (("Goal" :in-theory (disable anf-def-reads anf-set-target-reads anf-new-reads))))

; ---- THE WALKS -----------------------------------------------------------------------------------

; logic only (defun-nx): the steps, the locals and the builder threaded as
; the analyzer threads them
(defun-nx anb-listn-steps (xs n b anls anb)
  (declare (xargs :measure (acl2-count xs)))
  (if (or (not (natp n)) (equal n 0) (equal (frf-len xs) 0)) 1
    (let ((r (anb-sub (frf-nth xs 0) b anls anb)))
      (if (or (not (equal (car r) 0)) (< (frf-len xs) 2)) 1
        (+ 1 (anb-listn-steps (frf-rest xs) (- n 1) b (mv-nth 1 r) (mv-nth 2 r)))))))

(defthm anb-listn-steps-bound (<= (anb-listn-steps xs n b anls anb) (+ 1 (nfix n))) :rule-classes :linear)

(defun-nx anb-binds-steps (bv i c start loopp anls anb)
  (declare (xargs :measure (nfix (- (frm-pairs bv) (nfix i)))))
  (if (and (natp i) (< i (frm-pairs bv)))
      (let ((k (frm-nth bv (* 2 i))))
        (if (not (equal (anl-name-code k) 0)) 1
          (let ((r (anb-sub (frm-nth bv (+ 1 (* 2 i))) c anls anb)))
            (if (not (equal (car r) 0)) 1
              (let* ((slot (+ start i)) (anls (anl-bind c (frm-bid k) slot (mv-nth 1 r))))
                (if (not (equal (anb-let-kind k c slot loopp) 0)) 1
                  (+ 1 (anb-binds-steps bv (+ 1 i) c start loopp anls (mv-nth 2 r)))))))))
    1))

(defthm anb-binds-steps-bound
  (<= (anb-binds-steps bv i c start loopp anls anb) (+ 1 (nfix (- (frm-pairs bv) (nfix i))))) :rule-classes :linear)

(defun-nx anb-lfinits-steps (bv i c anls anb)
  (declare (xargs :measure (nfix (- (frm-pairs bv) (nfix i)))))
  (if (and (natp i) (< i (frm-pairs bv)))
      (let ((r (anb-sub (frm-nth bv (+ 1 (* 2 i))) c anls anb)))
        (if (not (equal (car r) 0)) 1 (+ 1 (anb-lfinits-steps bv (+ 1 i) c (mv-nth 1 r) (mv-nth 2 r)))))
    1))

(defthm anb-lfinits-steps-bound
  (<= (anb-lfinits-steps bv i c anls anb) (+ 1 (nfix (- (frm-pairs bv) (nfix i))))) :rule-classes :linear)

; letfn*'s names and a method's parameters: one step a pair, a parameter
(defun anb-lfnames-steps (bv i)
  (declare (xargs :measure (nfix (- (frm-pairs bv) (nfix i)))))
  (if (and (natp i) (< i (frm-pairs bv))) (+ 1 (anb-lfnames-steps bv (+ 1 i))) 1))
(defthm anb-lfnames-steps-bound
  (<= (anb-lfnames-steps bv i) (+ 1 (nfix (- (frm-pairs bv) (nfix i))))) :rule-classes :linear)

(defun anb-params-steps (pv i)
  (declare (xargs :measure (nfix (- (frm-count pv) (nfix i)))))
  (if (and (natp i) (< i (frm-count pv))) (+ 1 (anb-params-steps pv (+ 1 i))) 1))
(defthm anb-params-steps-bound
  (<= (anb-params-steps pv i) (+ 1 (nfix (- (frm-count pv) (nfix i))))) :rule-classes :linear)

; a try's clauses: one step a clause (and its step's reads), each catch's
; body and the finally's that body's
(defun-nx anb-try-walk-steps (cls st b anls anb)
  (declare (xargs :measure (acl2-count cls)))
  (if (equal (frf-len cls) 0) 1
    (let* ((f (frf-nth cls 0)) (lastp (if (< (frf-len cls) 2) 1 0))
           (code (anf-try-step st f lastp 0)) (op (anf-try-step st f lastp 1)) (st2 (anf-try-step st f lastp 2)))
      (cond ((not (equal code 0)) 1)
            ((equal op 1)
             (if (not (equal (anf-catch f) 0)) 1
               (let* ((r1 (anb-child b anls)) (r2 (anl-reserve (car r1) 1 (mv-nth 1 r1)))
                      (anls (anl-bind (car r1) (frm-bid (frf-nth f 2)) (car r2) (mv-nth 1 r2)))
                      (r (anb-body (frf-rest (frf-rest (frf-rest f))) (car r1) anls anb)))
                 (if (or (not (equal (car r) 0)) (< (frf-len cls) 2)) 1
                   (+ 1 (anb-try-walk-steps (frf-rest cls) st2 b (mv-nth 1 r) (anb-catch f (car r2) (mv-nth 2 r))))))))
            ((equal op 2) 1)
            ((< (frf-len cls) 2) 1)
            (t (+ 1 (anb-try-walk-steps (frf-rest cls) st2 b anls anb)))))))

(defthm anb-try-walk-steps-bound
  (<= (anb-try-walk-steps cls st b anls anb) (+ 1 (anb-len cls))) :rule-classes :linear
  :hints (("Goal" :in-theory (disable anf-try-step anf-catch anb-body anb-child anl-reserve anl-bind))))

; the try's scans of its forms: the body forms before the first clause, the
; clauses after them, whether a finally came
(defun anb-try-n-steps (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (or (equal (frf-len xs) 0) (not (equal (anf-try-op (frf-nth xs 0)) 0)) (< (frf-len xs) 2)) 1
    (+ 1 (anb-try-n-steps (frf-rest xs)))))
(defthm anb-try-n-steps-bound (<= (anb-try-n-steps xs) (+ 1 (anb-len xs))) :rule-classes :linear)

(defun anb-drop-steps (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n)) (equal n 0)) 1 (+ 1 (anb-drop-steps (- n 1)))))
(defthm anb-drop-steps-bound (<= (anb-drop-steps n) (+ 1 (nfix n))) :rule-classes :linear)

(defun anb-try-fin-steps (cls)
  (declare (xargs :measure (acl2-count cls)))
  (cond ((equal (frf-len cls) 0) 1)
        ((equal (anf-try-op (frf-nth cls 0)) 2) 1)
        ((< (frf-len cls) 2) 1)
        (t (+ 1 (anb-try-fin-steps (frf-rest cls))))))
(defthm anb-try-fin-steps-bound (<= (anb-try-fin-steps cls) (+ 1 (anb-len cls))) :rule-classes :linear)

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
;   anb-host-own-bound    the host's forms' own work: at most 8 steps (a
;                         list's dispatch, a call, a case*, a var, a
;                         collection literal)
;   anb-case-thens-steps-bound, anb-elems-steps-bound  a case*'s n thens,
;                         a collection literal's n forms: at most n + 1
;   anb-type-steps-bound  a deftype*, reify* or proxy of n method names:
;                         at most n + 5

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

; THE DRIVERS. A fn's methods: one step each over the first n, the
; methods' own analyses counted where they run
(defun-nx anb-methods-steps (ms n r anls anb)
  (declare (xargs :measure (acl2-count ms)))
  (if (or (not (natp n)) (equal n 0) (equal (frf-len ms) 0)) 1
    (let ((rr (anb-method (frf-nth ms 0) r anls anb)))
      (if (or (not (equal (car rr) 0)) (< (frf-len ms) 2)) 1
        (+ 1 (anb-methods-steps (frf-rest ms) (- n 1) r (mv-nth 1 rr) (mv-nth 2 rr)))))))

(defthm anb-methods-steps-bound (<= (anb-methods-steps ms n r anls anb) (+ 1 (nfix n))) :rule-classes :linear)

; and each driver's own work, its subforms' analyses, its walks (anb-listn,
; anb-methods, anb-params, anb-self) and the host's counted where they run:
; the reads, checks, hook calls and node shims on its longest path -- a
; set! 7, a . 10, a new 4, a recur 5, a fn* 11, a method 12
(defun anb-drv-own (sp)
  (case sp (7 7) (8 10) (9 4) (13 5) (14 11) (otherwise 12)))
(defthm anb-drv-own-bound (<= (anb-drv-own sp) 12) :rule-classes :linear)

; a fn's own name: a reserve and a bind, or nothing
(defun anb-self-steps (nm) (if (equal (frm-kind nm) 2) 2 1))
(defthm anb-self-steps-bound (<= (anb-self-steps nm) 2) :rule-classes :linear)

; THE HOST'S FORMS, each one's own work on its longest path, its subforms'
; analyses counted where they run: a list's dispatch 3 (its kind, the
; macroexpansion hook, the call), a call 6 (its head read twice, its
; count, the walk's entry, its kind, its node), a case* 8 (its count, its
; table's, the expr's and the default's reads, the walk's entry, its
; node), a var 4 (its symbol read twice, its resolution, its node), a
; collection literal 7 (its kind, its count twice, the walk's entry, its
; node, its metadata's read and node)
(defun anb-host-own (w) (case w (0 3) (1 6) (2 8) (3 7) (otherwise 4)))
(defthm anb-host-own-bound (<= (anb-host-own w) 8) :rule-classes :linear)

; a case*'s then forms from entry i: one step an entry
(defun-nx anb-case-thens-steps (x i n b anls anb)
  (declare (xargs :measure (nfix (- *anl40* (nfix i)))))
  (if (and (equal (frf-kind x) 3) (natp i) (< i n) (< i *anl40*))
      (let ((r (anb-sub (anb-case-then x i) b anls anb)))
        (if (not (equal (car r) 0)) 1
          (+ 1 (anb-case-thens-steps x (+ 1 i) n b (mv-nth 1 r) (mv-nth 2 r)))))
    1))

; a collection literal's forms from i: one step a form
(defun-nx anb-elems-steps (x i b anls anb)
  (declare (xargs :measure (nfix (- *anl40* (nfix i)))))
  (if (and (natp i) (< i (anb-coll-n x)) (< i *anl40*))
      (let ((r (anb-sub (anb-coll-elem x i) b anls anb)))
        (if (not (equal (car r) 0)) 1
          (+ 1 (anb-elems-steps x (+ 1 i) b (mv-nth 1 r) (mv-nth 2 r)))))
    1))

(defthm anb-elems-steps-bound
  (implies (natp i) (<= (anb-elems-steps x i b anls anb) (+ 1 (nfix (- (min (anb-coll-n x) *anl40*) i)))))
  :rule-classes :linear :hints (("Goal" :induct (anb-elems-steps x i b anls anb))))

(defthm anb-case-thens-steps-bound
  (implies (and (natp i) (integerp n))
           (<= (anb-case-thens-steps x i n b anls anb) (+ 1 (nfix (- (min n *anl40*) i)))))
  :rule-classes :linear :hints (("Goal" :induct (anb-case-thens-steps x i n b anls anb))))

; A TYPE (deftype*, reify*, proxy): its own work 4 steps (the open, the
; class's number, the count of its method names, its node) and one step
; a method name, each method's fn the host's to analyse (anb-type-method,
; as anb-host2's forms are); n names at most n + 5 steps
(defun-nx anb-type-methods-steps (w x i n b anls anb)
  (declare (xargs :measure (nfix (- *anl40* (nfix i)))))
  (if (and (natp i) (< i n) (< i *anl40*))
      (let ((r (anb-type-method w x i b anls anb)))
        (if (not (equal (car r) 0)) 1
          (+ 1 (anb-type-methods-steps w x (+ 1 i) n b (mv-nth 1 r) (mv-nth 2 r)))))
    1))
(defthm anb-type-methods-steps-bound
  (implies (and (natp i) (natp n))
           (<= (anb-type-methods-steps w x i n b anls anb) (+ 1 (nfix (- (min n *anl40*) i)))))
  :rule-classes :linear :hints (("Goal" :induct (anb-type-methods-steps w x i n b anls anb))))
(defun-nx anb-type-steps (w x b anls anb)
  (if (not (equal (anb-type-open w x b) 0)) 1
    (+ 4 (anb-type-methods-steps w x 0 (anb-type-n w x) b anls anb))))
(defthm anb-type-steps-bound
  (<= (anb-type-steps w x b anls anb) (+ 5 (anb-type-n w x)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance anb-type-methods-steps-bound (i 0) (n (anb-type-n w x))) (:instance anb-type-reads-sb64))
           :in-theory (disable anb-type-methods-steps-bound anb-type-reads-sb64))))

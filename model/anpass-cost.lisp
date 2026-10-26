; THE COST OF THE ANALYZER'S PASSES (model/anpass.lisp), counted as the
; generated Fortran runs them: every call of a pass, a node or a step of a
; walk over children, is a step; every word of a live set copied, or-ed or
; zeroed is a step; every capture set is a step.
;
;   anp-tc-steps-bound    the tail check: at most 3 steps for each node it can
;                         visit and 1 more (anp-tc-size), refusals stopping it
;                         early -- linear
;   anp-hfr-steps-bound   has_fn_recur the same (anp-hfr-size)
;   anp-rd-steps-bound    reads_in: 3 steps a node and a capture, and 1
;   anp-live-steps-copies liveness: at most 2n + 1 steps for each step of its
;                         walk, n the frame's slots -- an alternative's live
;                         set copied and or-ed back
;   anp-live-steps-walk   its walk: at most 3 steps for each node it visits,
;                         each counted once more for every loop it sits in (a
;                         loop's reads_in, anp-live-size), and 1
;   anp-clears-steps-bound  apply_clears: has_fn_recur, n words zeroed, and
;                         liveness: O(n * nodes * loop depth)
;
; A host read (ast_*) is one step; analyze.inc's ast_alt of a case reads the
; case's map entries anew (gca_entries), linear in its branches.

(in-package "ACL2")

(include-book "anpass")

; (anp-cond+1 ((test body) ...)): a cond whose every body is one step more,
; so that each call stands under the tests that rule it
(defun anp-add1-clauses (cs)
  (declare (xargs :mode :program))
  (if (endp cs) nil (cons (list (car (car cs)) (list (quote +) 1 (cadr (car cs)))) (anp-add1-clauses (cdr cs)))))
(defmacro anp-cond+1 (cs) (cons (quote cond) (anp-add1-clauses cs)))

; ---- THE TAIL CHECK --------------------------------------------------------------------------------

(defun anp-tc-steps (fl x j m tt)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (anp-cond+1
           ( ((equal k *n-recur*)
                  (if (or (equal tt 0) (equal tt 3) (and (equal tt 1) (equal (ast-rfn x) 0))
                          (and (equal tt 2) (not (equal (ast-rfn x) 0))))
                      0
                    (anp-tc-steps 1 x 0 (ast-nkids x) 0)))
                 ((equal k *n-if*)
                  (+ (anp-tc-steps 0 (ast-kid x 0) 0 0 0)
                     (if (equal (anp-tc 0 (ast-kid x 0) 0 0 0) 0)
                         (+ (anp-tc-steps 0 (ast-kid x 1) 0 0 tt)
                            (if (equal (anp-tc 0 (ast-kid x 1) 0 0 tt) 0) (anp-tc-steps 0 (ast-kid x 2) 0 0 tt) 0))
                       0)))
                 ((or (equal k *n-do*) (equal k *n-let*))
                  (let ((m2 (ast-nkids x)))
                    (if (equal m2 0) 0
                      (+ (anp-tc-steps 1 x 0 (- m2 1) 0)
                         (if (equal (anp-tc 1 x 0 (- m2 1) 0) 0) (anp-tc-steps 0 (ast-kid x (- m2 1)) 0 0 tt) 0)))))
                 ((or (equal k *n-letfn*) (equal k *n-loop*))
                  (let ((nn (anp-nn x)))
                    (+ (anp-tc-steps 1 x 0 nn 0)
                       (if (equal (anp-tc 1 x 0 nn 0) 0)
                           (anp-tc-steps 0 (ast-kid x nn) 0 0 (if (equal k *n-loop*) 2 tt))
                         0))))
                 ((equal k *n-case*)
                  (+ (anp-tc-steps 0 (ast-kid x 0) 0 0 0)
                     (if (equal (anp-tc 0 (ast-kid x 0) 0 0 0) 0)
                         (+ (anp-tc-steps 0 (ast-kid x 1) 0 0 tt)
                            (if (equal (anp-tc 0 (ast-kid x 1) 0 0 tt) 0) (anp-tc-steps 3 x 0 (ast-nalts x) tt) 0))
                       0)))
                 ((equal k *n-try*)
                  (let ((t0 (if (equal tt 0) 0 3)))
                    (+ (anp-tc-steps 0 (ast-kid x 0) 0 0 t0)
                       (if (equal (anp-tc 0 (ast-kid x 0) 0 0 t0) 0)
                           (+ (anp-tc-steps 3 x 0 (ast-nalts x) 0)
                              (if (equal (anp-tc 3 x 0 (ast-nalts x) 0) 0) (anp-tc-steps 0 (ast-kid x 1) 0 0 0) 0))
                         0))))
                 ((equal k *n-def*)
                  (+ (anp-tc-steps 1 x 0 (ast-nkids x) 0)
                     (if (equal (anp-tc 1 x 0 (ast-nkids x) 0) 0) (anp-tc-steps 0 (ast-s3 x) 0 0 0) 0)))
                 ((equal k *n-deftype*) (anp-tc-steps 3 x 0 (ast-nalts x) 0))
                 ((or (equal k 0) (equal k *n-local*) (equal k *n-const*) (equal k *n-var*)
                      (equal k *n-fn*) (equal k *n-lazy*))
                  0)
                 (t (anp-tc-steps 1 x 0 (ast-nkids x) 0)))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-tc-steps 0 (anp-ch fl x j) 0 0 tt)
           (if (equal (anp-tc 0 (anp-ch fl x j) 0 0 tt) 0) (anp-tc-steps fl x (+ 1 j) m tt) 0))
      1)))

; the nodes it can visit, refusing none
(defun anp-tc-size (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((or (equal k 0) (equal k *n-local*) (equal k *n-const*) (equal k *n-var*)
                   (equal k *n-fn*) (equal k *n-lazy*))
               1)
              ((or (equal k *n-if*) (equal k *n-case*) (equal k *n-try*))
               (+ 1 (anp-tc-size 0 (ast-kid x 0) 0 0) (anp-tc-size 0 (ast-kid x 1) 0 0)
                  (if (equal k *n-if*) (anp-tc-size 0 (ast-kid x 2) 0 0) (anp-tc-size 3 x 0 (ast-nalts x)))))
              ((or (equal k *n-do*) (equal k *n-let*))
               (let ((m2 (ast-nkids x)))
                 (if (equal m2 0) 1 (+ 1 (anp-tc-size 1 x 0 (- m2 1)) (anp-tc-size 0 (ast-kid x (- m2 1)) 0 0)))))
              ((or (equal k *n-letfn*) (equal k *n-loop*))
               (+ 1 (anp-tc-size 1 x 0 (anp-nn x)) (anp-tc-size 0 (ast-kid x (anp-nn x)) 0 0)))
              ((equal k *n-def*) (+ 1 (anp-tc-size 1 x 0 (ast-nkids x)) (anp-tc-size 0 (ast-s3 x) 0 0)))
              ((equal k *n-deftype*) (+ 1 (anp-tc-size 3 x 0 (ast-nalts x))))
              (t (+ 1 (anp-tc-size 1 x 0 (ast-nkids x))))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-tc-size 0 (anp-ch fl x j) 0 0) (anp-tc-size fl x (+ 1 j) m))
      0)))

(defthm anp-tc-size-pos (and (integerp (anp-tc-size fl x j m)) (<= 0 (anp-tc-size fl x j m)))
  :rule-classes ((:type-prescription :corollary (natp (anp-tc-size fl x j m)))))
(defthm anp-tc-steps-pos (and (integerp (anp-tc-steps fl x j m tt)) (<= 1 (anp-tc-steps fl x j m tt)))
  :rule-classes ((:type-prescription :corollary (natp (anp-tc-steps fl x j m tt)))
                 (:linear :corollary (<= 1 (anp-tc-steps fl x j m tt)))))

(defthm anp-tc-steps-bound
  (<= (anp-tc-steps fl x j m tt) (+ 1 (* 3 (anp-tc-size fl x j m))))
  :rule-classes :linear)

; ---- HAS_FN_RECUR -------------------------------------------------------------------------------------

(defun anp-hfr-steps (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (anp-cond+1
           ( ((equal k *n-recur*) (if (equal (ast-rfn x) 0) (anp-hfr-steps 1 x 0 (ast-nkids x)) 0))
                 ((equal k *n-try*)
                  (+ (anp-hfr-steps 0 (ast-kid x 0) 0 0)
                     (if (anp-hfr 0 (ast-kid x 0) 0 0) 0
                       (+ (anp-hfr-steps 3 x 0 (ast-nalts x))
                          (if (anp-hfr 3 x 0 (ast-nalts x)) 0 (anp-hfr-steps 0 (ast-kid x 1) 0 0))))))
                 ((equal k *n-case*)
                  (+ (anp-hfr-steps 3 x 0 (ast-nalts x))
                     (if (anp-hfr 3 x 0 (ast-nalts x)) 0 (anp-hfr-steps 1 x 0 (ast-nkids x)))))
                 ((equal k *n-def*)
                  (+ (anp-hfr-steps 0 (ast-s3 x) 0 0)
                     (if (anp-hfr 0 (ast-s3 x) 0 0) 0 (anp-hfr-steps 1 x 0 (ast-nkids x)))))
                 ((equal k *n-deftype*) (anp-hfr-steps 3 x 0 (ast-nalts x)))
                 ((or (equal k 0) (equal k *n-local*) (equal k *n-const*) (equal k *n-var*)
                      (equal k *n-fn*) (equal k *n-lazy*))
                  0)
                 (t (anp-hfr-steps 1 x 0 (ast-nkids x))))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-hfr-steps 0 (anp-ch fl x j) 0 0)
           (if (anp-hfr 0 (anp-ch fl x j) 0 0) 0 (anp-hfr-steps fl x (+ 1 j) m)))
      1)))

(defun anp-hfr-size (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((or (equal k 0) (equal k *n-local*) (equal k *n-const*) (equal k *n-var*)
                   (equal k *n-fn*) (equal k *n-lazy*))
               1)
              ((equal k *n-try*)
               (+ 1 (anp-hfr-size 0 (ast-kid x 0) 0 0) (anp-hfr-size 3 x 0 (ast-nalts x)) (anp-hfr-size 0 (ast-kid x 1) 0 0)))
              ((equal k *n-case*) (+ 1 (anp-hfr-size 3 x 0 (ast-nalts x)) (anp-hfr-size 1 x 0 (ast-nkids x))))
              ((equal k *n-def*) (+ 1 (anp-hfr-size 0 (ast-s3 x) 0 0) (anp-hfr-size 1 x 0 (ast-nkids x))))
              ((equal k *n-deftype*) (+ 1 (anp-hfr-size 3 x 0 (ast-nalts x))))
              (t (+ 1 (anp-hfr-size 1 x 0 (ast-nkids x))))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-hfr-size 0 (anp-ch fl x j) 0 0) (anp-hfr-size fl x (+ 1 j) m))
      0)))

(defthm anp-hfr-size-pos (natp (anp-hfr-size fl x j m)) :rule-classes :type-prescription)
(defthm anp-hfr-steps-pos (and (integerp (anp-hfr-steps fl x j m)) (<= 1 (anp-hfr-steps fl x j m)))
  :rule-classes ((:type-prescription :corollary (natp (anp-hfr-steps fl x j m)))
                 (:linear :corollary (<= 1 (anp-hfr-steps fl x j m)))))

(defthm anp-hfr-steps-bound
  (<= (anp-hfr-steps fl x j m) (+ 1 (* 3 (anp-hfr-size fl x j m))))
  :rule-classes :linear)

; ---- READS_IN AND LIVENESS -----------------------------------------------------------------------------

(defun anp-caps-steps (i k) (declare (xargs :measure (nfix (- (nfix k) (nfix i)))))
  (if (and (natp i) (natp k) (< i k)) (+ 1 (anp-caps-steps (+ 1 i) k)) 1))

(defun anp-fncaps-steps (x i k)
  (declare (xargs :measure (nfix (- (ifix k) (nfix i)))))
  (if (and (natp i) (integerp k) (< i k))
      (+ 1 (anp-caps-steps 0 (ast-ncaps (ast-kid x i))) (anp-fncaps-steps x (+ 1 i) k))
    1))

(defun anp-rd-steps (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (anp-cond+1
           ( ((equal k 0) 0)
                 ((equal k *n-local*) 1)
                 ((or (equal k *n-fn*) (equal k *n-lazy*)) (anp-caps-steps 0 (ast-ncaps x)))
                 ((equal k *n-deftype*) (anp-rd-steps 3 x 0 (ast-nalts x)))
                 ((or (equal k *n-try*) (equal k *n-case*))
                  (+ (anp-rd-steps 0 (ast-kid x 0) 0 0) (anp-rd-steps 3 x 0 (ast-nalts x)) (anp-rd-steps 0 (ast-kid x 1) 0 0)))
                 ((equal k *n-def*) (+ (anp-rd-steps 0 (ast-s3 x) 0 0) (anp-rd-steps 1 x 0 (ast-nkids x))))
                 (t (anp-rd-steps 1 x 0 (ast-nkids x))))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-rd-steps 0 (anp-ch fl x j) 0 0) (anp-rd-steps fl x (+ 1 j) m))
      1)))

; the nodes and captures reads_in visits
(defun anp-rd-size (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k 0) 0)
              ((equal k *n-local*) 1)
              ((or (equal k *n-fn*) (equal k *n-lazy*)) (+ 1 (ast-ncaps x)))
              ((equal k *n-deftype*) (+ 1 (anp-rd-size 3 x 0 (ast-nalts x))))
              ((or (equal k *n-try*) (equal k *n-case*))
               (+ 1 (anp-rd-size 0 (ast-kid x 0) 0 0) (anp-rd-size 3 x 0 (ast-nalts x)) (anp-rd-size 0 (ast-kid x 1) 0 0)))
              ((equal k *n-def*) (+ 1 (anp-rd-size 0 (ast-s3 x) 0 0) (anp-rd-size 1 x 0 (ast-nkids x))))
              (t (+ 1 (anp-rd-size 1 x 0 (ast-nkids x))))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-rd-size 0 (anp-ch fl x j) 0 0) (anp-rd-size fl x (+ 1 j) m))
      0)))

(defthm anp-caps-steps-is (implies (and (natp i) (natp k)) (equal (anp-caps-steps i k) (+ 1 (nfix (- k i))))))
(defthm anp-rd-size-pos (natp (anp-rd-size fl x j m)) :rule-classes :type-prescription)
(defthm anp-rd-steps-pos (and (integerp (anp-rd-steps fl x j m)) (<= 1 (anp-rd-steps fl x j m)))
  :rule-classes ((:type-prescription :corollary (natp (anp-rd-steps fl x j m)))
                 (:linear :corollary (<= 1 (anp-rd-steps fl x j m)))))

(defthm anp-rd-steps-bound
  (<= (anp-rd-steps fl x j m) (+ 1 (* 3 (anp-rd-size fl x j m))))
  :rule-classes :linear)

(defun anp-live-steps (fl x j m n)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (cond
   ((equal fl 0)
    (let ((k (ast-kind x)))
      (anp-cond+1
         (
          ((equal k 0) 0)
          ((equal k *n-local*) 1)
          ((or (equal k *n-fn*) (equal k *n-lazy*)) (anp-caps-steps 0 (ast-ncaps x)))
          ((equal k *n-deftype*) (anp-live-steps 3 x 0 (ast-nalts x) n))
          ((equal k *n-if*)
           (+ (* 2 (nfix n)) (anp-live-steps 0 (ast-kid x 1) 0 0 n) (anp-live-steps 0 (ast-kid x 2) 0 0 n)
              (anp-live-steps 0 (ast-kid x 0) 0 0 n)))
          ((or (equal k *n-case*) (equal k *n-try*))
           (+ (* 2 (nfix n)) (anp-live-steps 2 x 0 (ast-nalts x) n) (anp-live-steps 0 (ast-kid x 1) 0 0 n)
              (anp-live-steps 0 (ast-kid x 0) 0 0 n)))
          ((equal k *n-loop*)
           (+ (anp-rd-steps 0 (ast-kid x (anp-nn x)) 0 0) (anp-live-steps 0 (ast-kid x (anp-nn x)) 0 0 n)
              (anp-live-steps 1 x 0 (anp-nn x) n)))
          ((equal k *n-letfn*)
           (+ (anp-live-steps 0 (ast-kid x (anp-nn x)) 0 0 n) (anp-fncaps-steps x 0 (anp-nn x))
              (anp-live-steps 1 x 0 (anp-nn x) n)))
          ((equal k *n-def*) (+ (anp-live-steps 0 (ast-s3 x) 0 0 n) (anp-live-steps 1 x 0 (ast-nkids x) n)))
          (t (anp-live-steps 1 x 0 (ast-nkids x) n))))))
   ((equal fl 2)
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (* 2 (nfix n)) (anp-live-steps 0 (ast-alt x j) 0 0 n) (anp-live-steps 2 x (+ 1 j) m n))
      1))
   (t
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-live-steps 0 (anp-ch fl x (- m 1)) 0 0 n) (anp-live-steps fl x j (- m 1) n))
      1))))

; the nodes liveness visits, and for each loop its body's again (its reads_in)
(defun anp-live-size (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (cond
   ((equal fl 0)
    (let ((k (ast-kind x)))
      (cond
       ((equal k 0) 0)
       ((equal k *n-local*) 1)
       ((or (equal k *n-fn*) (equal k *n-lazy*)) (+ 1 (ast-ncaps x)))
       ((equal k *n-deftype*) (+ 1 (anp-live-size 3 x 0 (ast-nalts x))))
       ((equal k *n-if*)
        (+ 1 (anp-live-size 0 (ast-kid x 1) 0 0) (anp-live-size 0 (ast-kid x 2) 0 0) (anp-live-size 0 (ast-kid x 0) 0 0)))
       ((or (equal k *n-case*) (equal k *n-try*))
        (+ 1 (anp-live-size 2 x 0 (ast-nalts x)) (anp-live-size 0 (ast-kid x 1) 0 0) (anp-live-size 0 (ast-kid x 0) 0 0)))
       ((equal k *n-loop*)
        (+ 1 (anp-rd-size 0 (ast-kid x (anp-nn x)) 0 0) (anp-live-size 0 (ast-kid x (anp-nn x)) 0 0)
           (anp-live-size 1 x 0 (anp-nn x))))
       ((equal k *n-letfn*)
        (+ 1 (anp-live-size 0 (ast-kid x (anp-nn x)) 0 0) (anp-fncaps-steps x 0 (anp-nn x))
           (anp-live-size 1 x 0 (anp-nn x))))
       ((equal k *n-def*) (+ 1 (anp-live-size 0 (ast-s3 x) 0 0) (anp-live-size 1 x 0 (ast-nkids x))))
       (t (+ 1 (anp-live-size 1 x 0 (ast-nkids x)))))))
   (t
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (anp-live-size 0 (if (equal fl 2) (ast-alt x j) (anp-ch fl x (- m 1))) 0 0)
           (if (equal fl 2) (anp-live-size 2 x (+ 1 j) m) (anp-live-size fl x j (- m 1))))
      0))))

(defthm anp-fncaps-steps-pos (and (integerp (anp-fncaps-steps x i k)) (<= 1 (anp-fncaps-steps x i k)))
  :rule-classes ((:type-prescription :corollary (natp (anp-fncaps-steps x i k)))
                 (:linear :corollary (<= 1 (anp-fncaps-steps x i k)))))
(defthm anp-live-size-pos (natp (anp-live-size fl x j m)) :rule-classes :type-prescription)
(defthm anp-live-steps-pos (and (integerp (anp-live-steps fl x j m n)) (<= 1 (anp-live-steps fl x j m n)))
  :rule-classes ((:type-prescription :corollary (natp (anp-live-steps fl x j m n)))
                 (:linear :corollary (<= 1 (anp-live-steps fl x j m n)))))

; the copies: at most 2n + 1 steps for each step of the walk
(defthm anp-live-steps-copies
  (implies (natp n) (<= (anp-live-steps fl x j m n) (* (+ 1 (* 2 n)) (anp-live-steps fl x j m 0)))))

; the walk: at most 3 steps for each node it visits, and 1
(defthm anp-live-steps-walk
  (<= (anp-live-steps fl x j m 0) (+ 1 (* 3 (anp-live-size fl x j m))))
  :rule-classes :linear)

(defthm anp-mult-mono
  (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c)) (<= (* c a) (* c b)))
  :hints (("Goal" :nonlinearp t)) :rule-classes nil)

; apply_clears: has_fn_recur, then n words zeroed and liveness
(defun anp-clears-steps (x n)
  (+ 1 (anp-hfr-steps 0 x 0 0) (if (anp-hfr 0 x 0 0) 0 (+ 1 (nfix n) (anp-live-steps 0 x 0 0 n)))))

(defthm anp-clears-steps-bound
  (implies (natp n)
           (<= (anp-clears-steps x n)
               (+ 3 n (* 3 (anp-hfr-size 0 x 0 0)) (* (+ 1 (* 2 n)) (+ 1 (* 3 (anp-live-size 0 x 0 0)))))))
  :hints (("Goal" :in-theory (disable anp-live-steps-copies anp-live-steps-walk)
           :use ((:instance anp-live-steps-copies (fl 0) (j 0) (m 0))
                 (:instance anp-live-steps-walk (fl 0) (j 0) (m 0))
                 (:instance anp-mult-mono (c (+ 1 (* 2 n))) (a (anp-live-steps 0 x 0 0 0))
                            (b (+ 1 (* 3 (anp-live-size 0 x 0 0)))))))))

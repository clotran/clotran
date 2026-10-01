; The boundary between clotran's runtime and Fortran, formally.
;
; A Clojure value crosses into a Fortran routine in one of four shapes
; -- a number, an array, text, a record -- and nothing else does.
; This book states what crossing means for the parts that are NOT a
; choice of ours:
;
;   1. ARRAYS are Fortran's own: one contiguous column-major block of
;      any rank, with per-dimension lower bounds (DEVIATIONS 24,
;      src/f/NativeArray.f90). The index arithmetic is a bijection
;      between in-bounds subscripts and buffer offsets.
;   2. ALIASING is the Fortran standard's rule (F2018 15.5.2.13): an
;      actual argument a routine may modify must not be associated with
;      any other argument of the same call. The door checks it; a call
;      that passes the check has no modified buffer bound twice.
;   3. COST: crossing never copies an array. Marshalling costs one unit
;      per argument plus one per dimension, whatever the extents.
;
; Scalar conversion (int4 from a long, real4 from a double, logical
; from a value) IS a choice, and is the subject of PLAN step 27's
; open questions; it is modelled once decided.
;
; Certify: ~/jborden/acl2/saved_acl2 then (certify-book "boundary").

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

; ---- 1. arrays ---------------------------------------------------------
;
; A shape is a list of extents (positive integers) and a list of lower
; bounds (integers), one each per dimension, first dimension first. A
; subscript is a list of integers, one per dimension.

(defun extents-p (exts)
  (if (endp exts)
      (null exts)
    (and (posp (car exts)) (extents-p (cdr exts)))))

(defun lows-p (lows)
  (if (endp lows)
      (null lows)
    (and (integerp (car lows)) (lows-p (cdr lows)))))

; the number of elements: the product of the extents
(defun total (exts)
  (if (endp exts)
      1
    (* (car exts) (total (cdr exts)))))

; every subscript within its dimension's bounds
(defun in-bounds (subs lows exts)
  (if (endp subs)
      (and (null subs) (endp lows) (endp exts))
    (and (consp lows) (consp exts)
         (integerp (car subs))
         (<= (car lows) (car subs))
         (< (car subs) (+ (car lows) (car exts)))
         (in-bounds (cdr subs) (cdr lows) (cdr exts)))))

; COLUMN-MAJOR: the first dimension varies fastest. With 0-based
; positions p_d = s_d - low_d, the offset is
;   p_1 + e_1 * (p_2 + e_2 * (p_3 + ...))
; which is NativeArray.f90's gcna_index and Fortran's own storage order.
(defun cm-offset (subs lows exts)
  (if (endp subs)
      0
    (+ (- (car subs) (car lows))
       (* (car exts) (cm-offset (cdr subs) (cdr lows) (cdr exts))))))

(defthm total-positive
  (implies (extents-p exts)
           (and (integerp (total exts)) (< 0 (total exts))))
  :rule-classes (:rewrite :type-prescription))

(defthm cm-offset-integer
  (implies (and (in-bounds subs lows exts) (lows-p lows) (extents-p exts))
           (integerp (cm-offset subs lows exts))))

; one digit of a mixed-radix number: p < e and r < T give p + e*r < e*T
(defthm digit-below-place
  (implies (and (posp e) (integerp p) (integerp r) (integerp tt)
                (< p e) (< r tt))
           (< (+ p (* e r)) (* e tt)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm cm-offset-nonnegative
  (implies (and (in-bounds subs lows exts) (lows-p lows) (extents-p exts))
           (<= 0 (cm-offset subs lows exts)))
  :hints (("Goal" :nonlinearp t)))

; Every in-bounds subscript lands inside the buffer.
(defthm cm-offset-in-buffer
  (implies (and (in-bounds subs lows exts) (lows-p lows) (extents-p exts))
           (< (cm-offset subs lows exts) (total exts)))
  :hints (("Goal" :induct (cm-offset subs lows exts))
          (and stable-under-simplificationp
               '(:use ((:instance digit-below-place
                        (e (car exts))
                        (p (- (car subs) (car lows)))
                        (r (cm-offset (cdr subs) (cdr lows) (cdr exts)))
                        (tt (total (cdr exts)))))))))

; p + e*r = q + e*s with 0 <= p, q < e forces p = q and r = s
(defthm mixed-radix-digits-unique
  (implies (and (posp e) (integerp p) (integerp q) (integerp r) (integerp s)
                (<= 0 p) (< p e) (<= 0 q) (< q e)
                (equal (+ p (* e r)) (+ q (* e s))))
           (and (equal p q) (equal r s)))
  :rule-classes nil
  :hints (("Goal" :cases ((< r s) (< s r))
                  :nonlinearp t)))

; Distinct in-bounds subscripts land at distinct offsets: no two
; elements share storage. With cm-offset-in-buffer, and since there are
; exactly (total exts) in-bounds subscripts, the layout is a bijection.
(defthm cm-offset-injective
  (implies (and (in-bounds s1 lows exts) (in-bounds s2 lows exts)
                (lows-p lows) (extents-p exts)
                (equal (cm-offset s1 lows exts) (cm-offset s2 lows exts)))
           (equal s1 s2))
  :rule-classes nil
  :hints (("Goal" :induct (and (cm-offset s1 lows exts) (cm-offset s2 lows exts)))
          ("Subgoal *1/2" :use ((:instance mixed-radix-digits-unique
                                 (e (car exts))
                                 (p (- (car s1) (car lows)))
                                 (q (- (car s2) (car lows)))
                                 (r (cm-offset (cdr s1) (cdr lows) (cdr exts)))
                                 (s (cm-offset (cdr s2) (cdr lows) (cdr exts))))))))

; ---- 2. aliasing -------------------------------------------------------
;
; An argument is (kind handle intent): kind :array or :scalar; a
; scalar's handle is ignored (it crosses as a fresh temporary, so it
; aliases nothing); an array's handle is its registry buffer. A slice
; shares its parent's handle, so it counts as the same buffer: the rule
; is conservative, never permissive. Intent is :in, :out or :inout.

(defun arg-array-p (a) (eq (car a) :array))
(defun arg-handle (a) (cadr a))
(defun arg-writes-p (a) (not (eq (caddr a) :in)))

; the array arguments of args bound to buffer h
(defun binds-of (h args)
  (cond ((endp args) 0)
        ((and (arg-array-p (car args)) (equal (arg-handle (car args)) h))
         (+ 1 (binds-of h (cdr args))))
        (t (binds-of h (cdr args)))))

; THE CHECK the door makes before calling: every array the routine may
; modify is bound exactly once.
(defun alias-ok-1 (rest args)
  (cond ((endp rest) t)
        ((and (arg-array-p (car rest)) (arg-writes-p (car rest)))
         (and (equal (binds-of (arg-handle (car rest)) args) 1)
              (alias-ok-1 (cdr rest) args)))
        (t (alias-ok-1 (cdr rest) args))))

(defun alias-ok (args) (alias-ok-1 args args))

(defthm alias-ok-1-member
  (implies (and (alias-ok-1 rest args)
                (member-equal a rest)
                (arg-array-p a) (arg-writes-p a))
           (equal (binds-of (arg-handle a) args) 1)))

; What the standard requires, as a consequence of the check: a buffer
; the routine may write is bound to that one argument and no other.
(defthm alias-ok-means-written-buffers-unshared
  (implies (and (alias-ok args)
                (member-equal a args)
                (arg-array-p a) (arg-writes-p a))
           (equal (binds-of (arg-handle a) args) 1))
  :hints (("Goal" :use ((:instance alias-ok-1-member (rest args)))
                  :in-theory (disable alias-ok-1))))

; ---- 3. cost -----------------------------------------------------------
;
; Marshalling an argument: one unit for its pointer, and for an array
; one more per dimension (its extents cross as separate integers, as
; pkg_call passes them). A shape is (kind rank extents).

(defun marshal-cost (shapes)
  (if (endp shapes)
      0
    (+ 1 (if (eq (car (car shapes)) :array) (cadr (car shapes)) 0)
       (marshal-cost (cdr shapes)))))

; two argument lists alike but for their arrays' extents
(defun same-but-extents (xs ys)
  (if (endp xs)
      (endp ys)
    (and (consp ys)
         (equal (car (car xs)) (car (car ys)))
         (equal (cadr (car xs)) (cadr (car ys)))
         (same-but-extents (cdr xs) (cdr ys)))))

; O(arguments + ranks), independent of the data: crossing copies nothing.
(defthm marshal-cost-ignores-extents
  (implies (same-but-extents xs ys)
           (equal (marshal-cost xs) (marshal-cost ys))))

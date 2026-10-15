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
; and the parts that ARE choices, as PLAN step 27 records them (James,
; 2026-10-01):
;
;   4. NUMBERS NEVER MIX: an integer crosses only into an integer kind
;      and only inside its window; a real only into a real kind.
;   5. TEXT is UTF-8 in clotran and UCS-4 where a routine declares it;
;      the conversion is lossless.
;   6. OWNERSHIP follows the declarations; no handle is freed twice,
;      none is used after it is freed, and clotran never frees what it
;      only borrowed.
;   7. EQUALITY is by value, and the hash is by type and shape: equal
;      values hash alike, and writing in place never moves the hash.
;
; Certify: ../acl2/saved_acl2 then (certify-book "boundary").

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

; The door checks the MANIFEST's intents, which bind-fortran infers
; conservatively: an array is :in only when the body provably never
; writes it (scripts/bind-fortran never-written?), so every argument
; the routine really writes is a writer in the manifest too. Checking
; the conservative intents is enough: the true ones pass as well, and
; with them every buffer the routine really writes is unshared.
(defun weaker-intents (xs ys)
  ; ys is xs with some writers turned into readers, handles unchanged
  (if (endp xs)
      (endp ys)
    (and (consp ys)
         (equal (car (car xs)) (car (car ys)))
         (equal (arg-handle (car xs)) (arg-handle (car ys)))
         (or (equal (caddr (car xs)) (caddr (car ys)))
             (eq (caddr (car ys)) :in))
         (weaker-intents (cdr xs) (cdr ys)))))

(defthm binds-of-weaker
  (implies (weaker-intents xs ys)
           (equal (binds-of h ys) (binds-of h xs))))

(defthm alias-ok-1-weaker
  (implies (and (weaker-intents rest1 rest2) (alias-ok-1 rest1 args1)
                (weaker-intents args1 args2))
           (alias-ok-1 rest2 args2)))

(defthm alias-ok-conservative-suffices
  (implies (and (alias-ok args) (weaker-intents args true-args))
           (alias-ok true-args)))

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

; ---- 4. numbers never mix --------------------------------------------
;
; A Clojure scalar as it reaches the door: (:int n), (:real r) with r a
; rational or one of :nan :pinf :ninf (IEEE's specials), (:bool b), or
; anything else. ACL2 has no floating point, so a real is modelled by
; the value it denotes; rounding to real32 is IEEE's and is not claimed
; here -- only WHEN a real may cross.

(defun int-kind-bits (k)
  (case k (:int8 8) (:int16 16) (:int32 32) (:int64 64) (otherwise nil)))

(defun int-kind-p (k) (and (int-kind-bits k) t))

; the window of a signed two's-complement kind, as both compilers
; report it: -2^(b-1) .. 2^(b-1)-1
(defun kind-min (k) (- (expt 2 (1- (int-kind-bits k)))))
(defun kind-max (k) (1- (expt 2 (1- (int-kind-bits k)))))

; the largest finite real32, (2 - 2^-23) * 2^127 = 3.40282347e38
(defconst *real32-max* (* (- 2 (expt 2 -23)) (expt 2 127)))

(defun real-special-p (r) (member-eq r '(:nan :pinf :ninf)))

; Crossing: (:ok value) or (:refused why). Never a third thing.
(defun cross (k v)
  (cond ((int-kind-p k)
         (cond ((not (and (consp v) (eq (car v) :int) (integerp (cadr v))))
                (list :refused :not-an-integer))
               ((or (< (cadr v) (kind-min k)) (< (kind-max k) (cadr v)))
                (list :refused :out-of-range))
               (t (list :ok (cadr v)))))
        ((eq k :real64)
         (if (and (consp v) (eq (car v) :real)
                  (or (rationalp (cadr v)) (real-special-p (cadr v))))
             (list :ok (cadr v))
           (list :refused :not-a-real)))
        ((eq k :real32)
         (cond ((not (and (consp v) (eq (car v) :real)
                          (or (rationalp (cadr v)) (real-special-p (cadr v)))))
                (list :refused :not-a-real))
               ((and (rationalp (cadr v)) (< *real32-max* (abs (cadr v))))
                (list :refused :out-of-range))
               (t (list :ok (cadr v)))))
        ((eq k :logical)
         (if (and (consp v) (eq (car v) :bool) (booleanp (cadr v)))
             (list :ok (cadr v))
           (list :refused :not-a-logical)))
        (t (list :refused :unknown-kind))))

(defun crossed-p (r) (eq (car r) :ok))

; Every crossing answers, and only :ok or :refused.
(defthm cross-answers
  (member-eq (car (cross k v)) '(:ok :refused)))

; An integer that crosses is UNCHANGED and inside the window: no wrap,
; no truncation.
(defthm int-crossing-exact
  (implies (and (int-kind-p k) (crossed-p (cross k v)))
           (and (equal (car v) :int)
                (equal (cadr (cross k v)) (cadr v))
                (<= (kind-min k) (cadr v))
                (<= (cadr v) (kind-max k)))))

; ...and every integer inside the window crosses.
(defthm int-in-window-crosses
  (implies (and (int-kind-p k) (integerp n)
                (<= (kind-min k) n) (<= n (kind-max k)))
           (crossed-p (cross k (list :int n)))))

; NO MIXING: nothing but an integer enters an integer kind, and nothing
; but a real enters a real kind -- (:int 1) is refused as a real64.
(defthm no-real-into-integer
  (implies (and (int-kind-p k) (not (equal (car v) :int)))
           (not (crossed-p (cross k v)))))

(defthm no-integer-into-real
  (implies (and (member-eq k '(:real64 :real32)) (not (equal (car v) :real)))
           (not (crossed-p (cross k v)))))

(defthm real32-never-overflows
  (implies (and (crossed-p (cross :real32 v)) (rationalp (cadr v)))
           (<= (abs (cadr v)) *real32-max*)))

(defthm logical-only-booleans
  (implies (crossed-p (cross :logical v))
           (and (equal (car v) :bool) (booleanp (cadr v)))))

; ---- 5. text ---------------------------------------------------------
;
; A clotran string is a list of code points; UTF-8 is its bytes. A
; routine declaring character(kind=ucs4) gets the code points, one per
; position; plain character gets the bytes. Lossless: decoding the
; bytes gives back exactly the code points.

(defun code-point-p (c)
  (and (natp c) (<= c #x10FFFF)
       (not (and (<= #xD800 c) (<= c #xDFFF)))))   ; no surrogates

(defun code-points-p (cs)
  (if (endp cs) (null cs) (and (code-point-p (car cs)) (code-points-p (cdr cs)))))

(defun utf8-1 (c)
  (cond ((< c #x80) (list c))
        ((< c #x800) (list (+ #xC0 (floor c 64)) (+ #x80 (mod c 64))))
        ((< c #x10000) (list (+ #xE0 (floor c 4096))
                             (+ #x80 (mod (floor c 64) 64))
                             (+ #x80 (mod c 64))))
        (t (list (+ #xF0 (floor c 262144))
                 (+ #x80 (mod (floor c 4096) 64))
                 (+ #x80 (mod (floor c 64) 64))
                 (+ #x80 (mod c 64))))))

(defun utf8 (cs)
  (if (endp cs) nil (append (utf8-1 (car cs)) (utf8 (cdr cs)))))

; one code point from the front of bytes: (code-point . rest)
(defun utf8-decode-1 (bs)
  (let ((b (car bs)))
    (cond ((< b #x80) (cons b (cdr bs)))
          ((< b #xE0) (cons (+ (* 64 (- b #xC0)) (- (cadr bs) #x80)) (cddr bs)))
          ((< b #xF0) (cons (+ (* 4096 (- b #xE0)) (* 64 (- (cadr bs) #x80))
                               (- (caddr bs) #x80))
                            (cdddr bs)))
          (t (cons (+ (* 262144 (- b #xF0)) (* 4096 (- (cadr bs) #x80))
                      (* 64 (- (caddr bs) #x80)) (- (cadddr bs) #x80))
                   (cddddr bs))))))

(defthm utf8-decode-1-of-utf8-1
  (implies (code-point-p c)
           (equal (utf8-decode-1 (append (utf8-1 c) rest))
                  (cons c rest)))
  :hints (("Goal" :nonlinearp t)))

(defun utf8-decode (bs n)
  ; n code points from bs
  (if (zp n)
      nil
    (let ((d (utf8-decode-1 bs)))
      (cons (car d) (utf8-decode (cdr d) (1- n))))))

(defthm append-associative
  (equal (append (append x y) z) (append x (append y z))))

(defthm utf8-decode-of-utf8
  (implies (code-points-p cs)
           (equal (utf8-decode (append (utf8 cs) rest) (len cs)) cs))
  :hints (("Goal" :in-theory (disable utf8-1 utf8-decode-1))))

; ---- 6. ownership ----------------------------------------------------
;
; A handle's owner comes from the routine's declaration (PLAN step 27,
; decision 8): :borrowed (a plain dummy: the routine may not keep it),
; :owned (transferred to clotran: allocatable intent(out) or result),
; :retained (a TARGET or POINTER dummy: kept alive by a keep-alive
; link while its holder lives), :library (a pointer result: freed by
; the library's destroy routine, when the manifest names one). A
; handle is (owner live? frees), frees counting how often it was freed.
;
; Events: :collect (the collector finds no reference left), :release
; (the holder of a retained handle is collected), :destroy (the
; library's destroy routine is called on it), :may-free (it was passed
; to a routine the source analysis marks as possibly freeing it).

(defun h-owner (h) (car h))
(defun h-live (h) (cadr h))
(defun h-frees (h) (caddr h))
(defun mk-h (owner live frees) (list owner live frees))

(defun h-free (h)
  ; freeing a live handle: once, and it is dead after
  (if (h-live h) (mk-h (h-owner h) nil (1+ (h-frees h))) h))

(defun h-step (h ev)
  (case ev
    (:collect (if (member-eq (h-owner h) '(:owned :library)) (h-free h) h))
    (:release (if (eq (h-owner h) :retained) (mk-h :owned (h-live h) (h-frees h)) h))
    (:destroy (if (eq (h-owner h) :borrowed) h (h-free h)))
    (:may-free (if (h-live h) (mk-h (h-owner h) nil (h-frees h)) h))
    (otherwise h)))

(defun h-run (h evs)
  (if (endp evs) h (h-run (h-step h (car evs)) (cdr evs))))

; using a handle: only while it is live
(defun h-use-ok (h) (and (h-live h) t))

(defun h-ok (h)
  (and (member-eq (h-owner h) '(:borrowed :owned :retained :library))
       (booleanp (h-live h))
       (natp (h-frees h))
       (if (h-live h) (equal (h-frees h) 0) (<= (h-frees h) 1))))

(defthm h-step-ok
  (implies (h-ok h) (h-ok (h-step h ev))))

(defthm h-run-ok
  (implies (h-ok h) (h-ok (h-run h evs))))

; NEVER FREED TWICE, whatever happens to it.
(defthm freed-at-most-once
  (implies (and (h-ok h) (equal (h-frees h) 0))
           (<= (h-frees (h-run h evs)) 1)))

; NEVER USED AFTER IT IS FREED: a handle that is not live stays so.
(defthm dead-stays-dead
  (implies (not (h-live h))
           (not (h-use-ok (h-run h evs)))))

; CLOTRAN NEVER FREES WHAT IT BORROWED: the collector and the destroy
; routine leave a borrowed handle's free count alone.
(defun no-may-free (evs)
  (if (endp evs) t (and (not (eq (car evs) :may-free)) (no-may-free (cdr evs)))))

(defthm borrowed-never-freed
  (implies (equal (h-owner h) :borrowed)
           (and (equal (h-owner (h-run h evs)) :borrowed)
                (equal (h-frees (h-run h evs)) (h-frees h)))))

; A RETAINED handle survives every collection until its holder goes.
(defun no-release (evs)
  (if (endp evs) t (and (not (member-eq (car evs) '(:release :destroy :may-free)))
                        (no-release (cdr evs)))))

(defthm retained-survives-collection
  (implies (and (equal (h-owner h) :retained) (no-release evs))
           (equal (h-run h evs) h)))

; ---- 7. equality and hashing -----------------------------------------
;
; A Fortran array or object as clotran compares it: (type shape
; contents), contents its elements in storage order, each a rational or
; :nan. = is Fortran's all(a == b) with equal shapes; NaN equals
; nothing, itself included. The hash reads the type and the shape only.

(defun elem-eq (x y)
  (and (rationalp x) (rationalp y) (equal x y)))   ; :nan is never equal

(defun elems-eq (xs ys)
  (if (endp xs)
      (endp ys)
    (and (consp ys) (elem-eq (car xs) (car ys)) (elems-eq (cdr xs) (cdr ys)))))

(defun f-type (a) (car a))
(defun f-shape (a) (cadr a))
(defun f-contents (a) (caddr a))

(defun f-equal (a b)
  (and (equal (f-type a) (f-type b))
       (equal (f-shape a) (f-shape b))
       (elems-eq (f-contents a) (f-contents b))))

; the hash: any function of type and shape alone; this one is the pair
(defun f-hash (a) (list (f-type a) (f-shape a)))

; Clojure's contract: equal values hash alike.
(defthm f-equal-same-hash
  (implies (f-equal a b) (equal (f-hash a) (f-hash b))))

; writing element i in place changes contents only
(defun put-nth (i x xs)
  (if (zp i) (if (consp xs) (cons x (cdr xs)) xs) (if (consp xs) (cons (car xs) (put-nth (1- i) x (cdr xs))) xs)))

(defun f-write (a i x)
  (list (f-type a) (f-shape a) (put-nth i x (f-contents a))))

; THE HASH NEVER MOVES under a write: as a map key it is never lost.
(defthm f-write-keeps-hash
  (equal (f-hash (f-write a i x)) (f-hash a)))

; NaN, as IEEE and Fortran say: an array holding one is not equal even
; to itself.
(defun has-nan (xs) (if (endp xs) nil (or (eq (car xs) :nan) (has-nan (cdr xs)))))

(defthm elems-with-nan-never-equal
  (implies (has-nan xs) (not (elems-eq xs xs))))

(defthm nan-never-equal
  (implies (has-nan (f-contents a)) (not (f-equal a a))))

; COST, counted: = reads at most one element pair per element; the hash
; reads the rank, never the elements.
(defun elems-eq-cost (xs ys)
  (if (or (endp xs) (endp ys))
      1
    (if (elem-eq (car xs) (car ys)) (1+ (elems-eq-cost (cdr xs) (cdr ys))) 1)))

(defthm f-equal-linear
  (<= (elems-eq-cost xs ys) (1+ (len xs))))

(defun f-hash-cost (a) (1+ (len (f-shape a))))

(defthm f-hash-cost-ignores-contents
  (equal (f-hash-cost (list ty sh c1)) (f-hash-cost (list ty sh c2))))

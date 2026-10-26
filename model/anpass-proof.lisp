; THE GENERATED LIVENESS PASS COMPUTES ITS MEANING (model/anpass.lisp's
; anp-live, the Fortran of src/f/gen/anpass_gen.inc): the live sets as
; lists and the marked reads, sp-out and sp-mk, the same backwards walk with
; no regions, no copies, no array to run out of.
;
;   anp-live-frame    a pass writes only its own region and the free ones
;                     above top, nothing else below top
;   anp-live-spec     when it ends with no error, its region holds sp-out of
;                     the region it started from, and the marks it added are
;                     sp-mk's, in order
;   anp-clears-spec   so apply_clears' marks are sp-mk of the body from the
;                     empty live set, or none when it recurs to its fn

(in-package "ACL2")

(include-book "anpass")

; ---- THE MEANING: live sets as lists ---------------------------------------------------------

(defun sp-set (s L n) (if (and (integerp s) (<= 0 s) (< s n)) (update-nth s 1 L) L))

(defun sp-or (A B) (if (consp A) (cons (if (equal (car A) 0) (car B) 1) (sp-or (cdr A) (cdr B))) nil))

(defun sp-caps (x i k L n)
  (declare (xargs :measure (nfix (- (nfix k) (nfix i)))))
  (if (and (natp i) (natp k) (< i k)) (sp-caps x (+ 1 i) k (sp-set (ast-cap x i) L n) n) L))

(defun sp-fncaps (x i k L n)
  (declare (xargs :measure (nfix (- (ifix k) (nfix i)))))
  (if (and (natp i) (integerp k) (< i k))
      (sp-fncaps x (+ 1 i) k (sp-caps (ast-kid x i) 0 (ast-ncaps (ast-kid x i)) L n) n)
    L))

(defun sp-rd (fl x j m L n)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k 0) L)
              ((equal k *n-local*) (sp-set (ast-i2 x) L n))
              ((or (equal k *n-fn*) (equal k *n-lazy*)) (sp-caps x 0 (ast-ncaps x) L n))
              ((equal k *n-deftype*) (sp-rd 3 x 0 (ast-nalts x) L n))
              ((equal k *n-try*)
               (sp-rd 0 (ast-kid x 1) 0 0 (sp-rd 3 x 0 (ast-nalts x) (sp-rd 0 (ast-kid x 0) 0 0 L n) n) n))
              ((equal k *n-case*)
               (sp-rd 3 x 0 (ast-nalts x) (sp-rd 0 (ast-kid x 1) 0 0 (sp-rd 0 (ast-kid x 0) 0 0 L n) n) n))
              ((equal k *n-def*) (sp-rd 1 x 0 (ast-nkids x) (sp-rd 0 (ast-s3 x) 0 0 L n) n))
              (t (sp-rd 1 x 0 (ast-nkids x) L n))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (sp-rd fl x (+ 1 j) m (sp-rd 0 (anp-ch fl x j) 0 0 L n) n)
      L)))

; the live set before the node, L the one after it (fl 0); fl 1 and 3 the
; children or alternatives j .. m-1, the last first; fl 2 the alternatives
; j .. m-1 each from L, or-ed into A
(defun sp-out (fl x j m A L n)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (cond
   ((equal fl 0)
    (let ((k (ast-kind x)))
      (cond
       ((equal k 0) L)
       ((equal k *n-local*) (sp-set (ast-i2 x) L n))
       ((or (equal k *n-fn*) (equal k *n-lazy*)) (sp-caps x 0 (ast-ncaps x) L n))
       ((equal k *n-deftype*) (sp-out 3 x 0 (ast-nalts x) nil L n))
       ((equal k *n-if*)
        (sp-out 0 (ast-kid x 0) 0 0 nil
                (sp-or (sp-out 0 (ast-kid x 1) 0 0 nil L n) (sp-out 0 (ast-kid x 2) 0 0 nil L n)) n))
       ((equal k *n-case*)
        (sp-out 0 (ast-kid x 0) 0 0 nil
                (sp-or (sp-out 2 x 0 (ast-nalts x) L L n) (sp-out 0 (ast-kid x 1) 0 0 nil L n)) n))
       ((equal k *n-try*)
        (let ((L1 (sp-out 0 (ast-kid x 1) 0 0 nil L n)))
          (sp-out 0 (ast-kid x 0) 0 0 nil (sp-out 2 x 0 (ast-nalts x) L1 L1 n) n)))
       ((equal k *n-loop*)
        (let* ((nn (anp-nn x)) (bd (ast-kid x nn)) (L1 (sp-rd 0 bd 0 0 L n)))
          (sp-out 1 x 0 nn nil (sp-out 0 bd 0 0 nil L1 n) n)))
       ((equal k *n-letfn*)
        (let ((nn (anp-nn x)))
          (sp-out 1 x 0 nn nil (sp-fncaps x 0 nn (sp-out 0 (ast-kid x nn) 0 0 nil L n) n) n)))
       ((equal k *n-def*) (sp-out 1 x 0 (ast-nkids x) nil (sp-out 0 (ast-s3 x) 0 0 nil L n) n))
       (t (sp-out 1 x 0 (ast-nkids x) nil L n)))))
   ((equal fl 2)
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (sp-out 2 x (+ 1 j) m (sp-or (sp-out 0 (ast-alt x j) 0 0 nil L n) A) L n)
      A))
   (t
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (sp-out fl x j (- m 1) nil (sp-out 0 (anp-ch fl x (- m 1)) 0 0 nil L n) n)
      L))))

; the reads marked for clearing, in the order the pass marks them
(defun sp-mk (fl x j m L n)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (cond
   ((equal fl 0)
    (let ((k (ast-kind x)))
      (cond
       ((equal k 0) nil)
       ((equal k *n-local*)
        (let ((s (ast-i2 x))) (if (and (integerp s) (<= 0 s) (< s n) (equal (nth s L) 0)) (list x) nil)))
       ((or (equal k *n-fn*) (equal k *n-lazy*)) nil)
       ((equal k *n-deftype*) (sp-mk 3 x 0 (ast-nalts x) L n))
       ((equal k *n-if*)
        (append (sp-mk 0 (ast-kid x 1) 0 0 L n) (sp-mk 0 (ast-kid x 2) 0 0 L n)
                (sp-mk 0 (ast-kid x 0) 0 0
                       (sp-or (sp-out 0 (ast-kid x 1) 0 0 nil L n) (sp-out 0 (ast-kid x 2) 0 0 nil L n)) n)))
       ((equal k *n-case*)
        (append (sp-mk 2 x 0 (ast-nalts x) L n) (sp-mk 0 (ast-kid x 1) 0 0 L n)
                (sp-mk 0 (ast-kid x 0) 0 0
                       (sp-or (sp-out 2 x 0 (ast-nalts x) L L n) (sp-out 0 (ast-kid x 1) 0 0 nil L n)) n)))
       ((equal k *n-try*)
        (let ((L1 (sp-out 0 (ast-kid x 1) 0 0 nil L n)))
          (append (sp-mk 0 (ast-kid x 1) 0 0 L n) (sp-mk 2 x 0 (ast-nalts x) L1 n)
                  (sp-mk 0 (ast-kid x 0) 0 0 (sp-out 2 x 0 (ast-nalts x) L1 L1 n) n))))
       ((equal k *n-loop*)
        (let* ((nn (anp-nn x)) (bd (ast-kid x nn)) (L1 (sp-rd 0 bd 0 0 L n)))
          (append (sp-mk 0 bd 0 0 L1 n) (sp-mk 1 x 0 nn (sp-out 0 bd 0 0 nil L1 n) n))))
       ((equal k *n-letfn*)
        (let ((nn (anp-nn x)))
          (append (sp-mk 0 (ast-kid x nn) 0 0 L n)
                  (sp-mk 1 x 0 nn (sp-fncaps x 0 nn (sp-out 0 (ast-kid x nn) 0 0 nil L n) n) n))))
       ((equal k *n-def*)
        (append (sp-mk 0 (ast-s3 x) 0 0 L n) (sp-mk 1 x 0 (ast-nkids x) (sp-out 0 (ast-s3 x) 0 0 nil L n) n)))
       (t (sp-mk 1 x 0 (ast-nkids x) L n)))))
   ((equal fl 2)
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (append (sp-mk 0 (ast-alt x j) 0 0 L n) (sp-mk 2 x (+ 1 j) m L n))
      nil))
   (t
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (append (sp-mk 0 (anp-ch fl x (- m 1)) 0 0 L n)
                (sp-mk fl x j (- m 1) (sp-out 0 (anp-ch fl x (- m 1)) 0 0 nil L n) n))
      nil))))

; ---- THE ARRAY AS READ ------------------------------------------------------------------------

; the region of n words at b, as anp-get reads them
(defun reg (anps b n)
  (declare (xargs :stobjs anps :verify-guards nil))
  (if (zp n) nil (cons (anp-get b anps) (reg anps (+ 1 b) (- n 1)))))

; the marks so far
(defun-nx mks (anps)
  (take (nfix (anp-nmk anps)) (nth *anp-mki* anps)))

(defun lvl (anps) (declare (xargs :stobjs anps :verify-guards nil)) (anp-lv-length anps))

; ---- THE PRIMITIVES ---------------------------------------------------------------------------

(defthm anp-put-fields
  (and (equal (anp-lv-length (anp-put i v anps)) (anp-lv-length anps))
       (equal (mks (anp-put i v anps)) (mks anps))
       (equal (anp-err (anp-put i v anps))
              (if (and (integerp i) (<= 0 i) (< i (anp-lv-length anps))) (anp-err anps) 1))
       (equal (anp-get k (anp-put i v anps))
              (if (and (equal k i) (integerp i) (<= 0 i) (< i (anp-lv-length anps))) v (anp-get k anps)))))

(defthm take-update-nth-last
  (implies (and (natp k) (< k (len l)))
           (equal (take (+ 1 k) (update-nth k x l)) (append (take k l) (list x))))
  :hints (("Goal" :in-theory (enable take update-nth))))

(defthm anp-mark-fields
  (and (equal (anp-lv-length (anp-mark x anps)) (anp-lv-length anps))
       (equal (anp-get k (anp-mark x anps)) (anp-get k anps))
       (implies (equal (anp-err (anp-mark x anps)) 0)
                (and (equal (anp-err anps) 0)
                     (equal (mks (anp-mark x anps)) (append (mks anps) (list x)))))
       (implies (not (equal (anp-err anps) 0)) (not (equal (anp-err (anp-mark x anps)) 0))))
  :hints (("Goal" :in-theory (enable take))))

(in-theory (disable anp-put anp-get anp-mark anp-lv-length anp-err anp-nmk mks))

; err only grows; the length and the marks stay
(defmacro anp-keeps (call)
  `(and (equal (anp-lv-length ,call) (anp-lv-length anps))
        (equal (mks ,call) (mks anps))
        (implies (not (equal (anp-err anps) 0)) (not (equal (anp-err ,call) 0)))))

(defthm anp-copy-keeps (anp-keeps (anp-copy k n from to anps)))
(defthm anp-or-keeps (anp-keeps (anp-or k n from to anps)))
(defthm anp-zero-keeps (anp-keeps (anp-zero k n anps)))
(defthm anp-set-keeps (anp-keeps (anp-set s b n anps)))
(defthm anp-caps-keeps (anp-keeps (anp-caps x i k b n anps)))
(defthm anp-fncaps-keeps (anp-keeps (anp-fncaps x i k b n anps)))
(defthm anp-rd-keeps (anp-keeps (anp-rd fl x j m b n anps)))

; what each writes: nothing outside its words
(defthm anp-copy-frame
  (implies (or (not (integerp i)) (< i (+ to (nfix k))) (<= (+ to (nfix n)) i))
           (equal (anp-get i (anp-copy k n from to anps)) (anp-get i anps))))
(defthm anp-or-frame
  (implies (or (not (integerp i)) (< i (+ to (nfix k))) (<= (+ to (nfix n)) i))
           (equal (anp-get i (anp-or k n from to anps)) (anp-get i anps))))
(defthm anp-zero-frame
  (implies (or (not (integerp i)) (< i (nfix k)) (<= (nfix n) i))
           (equal (anp-get i (anp-zero k n anps)) (anp-get i anps))))
(defthm anp-set-frame
  (implies (or (not (integerp i)) (< i b) (<= (+ b n) i))
           (equal (anp-get i (anp-set s b n anps)) (anp-get i anps))))
(defthm anp-caps-frame
  (implies (or (not (integerp i)) (< i b) (<= (+ b n) i))
           (equal (anp-get i (anp-caps x i0 k b n anps)) (anp-get i anps))))
(defthm anp-fncaps-frame
  (implies (or (not (integerp i)) (< i b) (<= (+ b n) i))
           (equal (anp-get i (anp-fncaps x i0 k b n anps)) (anp-get i anps))))
(defthm anp-rd-frame
  (implies (or (not (integerp i)) (< i b) (<= (+ b n) i))
           (equal (anp-get i (anp-rd fl x j m b n anps)) (anp-get i anps))))

; an error at the end was no error before
(defmacro anp-err-back (name call)
  `(defthm ,name (implies (equal (anp-err ,call) 0) (equal (anp-err anps) 0))
     :rule-classes :forward-chaining))

(anp-err-back anp-put-err-back (anp-put i v anps))
(anp-err-back anp-mark-err-back (anp-mark x anps))
(anp-err-back anp-copy-err-back (anp-copy k n from to anps))
(anp-err-back anp-or-err-back (anp-or k n from to anps))
(anp-err-back anp-zero-err-back (anp-zero k n anps))
(anp-err-back anp-set-err-back (anp-set s b n anps))
(anp-err-back anp-caps-err-back (anp-caps x i k b n anps))
(anp-err-back anp-fncaps-err-back (anp-fncaps x i k b n anps))
(anp-err-back anp-rd-err-back (anp-rd fl x j m b n anps))

; ---- REGIONS ------------------------------------------------------------------------------------

(defthm len-reg (equal (len (reg anps b n)) (nfix n)))

(defun nth-reg-ind (s b n) (if (or (zp s) (zp n)) (list b n) (nth-reg-ind (- s 1) (+ 1 b) (- n 1))))

(defthm nth-reg
  (implies (and (natp s) (< s (nfix n)) (natp b))
           (equal (nth s (reg anps b n)) (anp-get (+ b s) anps)))
  :hints (("Goal" :induct (nth-reg-ind s b n) :expand ((reg anps b n)))))

(defthm reg-put
  (implies (natp b)
           (equal (reg (anp-put i v anps) b n)
                  (if (and (integerp i) (<= 0 i) (< i (anp-lv-length anps)) (<= b i) (< i (+ b (nfix n))))
                      (update-nth (- i b) v (reg anps b n))
                    (reg anps b n))))
  :hints (("Goal" :induct (reg anps b n) :in-theory (enable update-nth))))

; a region no write reaches is as it was
(defmacro reg-frame (name call cond)
  `(defthm ,name
     (implies (and (natp c) (natp b) (natp n) (natp to) ,cond) (equal (reg ,call c n2) (reg anps c n2)))
     :hints (("Goal" :induct (reg anps c n2)))))

(reg-frame reg-copy-frame (anp-copy k n from to anps) (or (<= (+ c (nfix n2)) (+ to (nfix k))) (<= (+ to (nfix n)) c)))
(reg-frame reg-or-frame (anp-or k n from to anps) (or (<= (+ c (nfix n2)) (+ to (nfix k))) (<= (+ to (nfix n)) c)))
(reg-frame reg-set-frame (anp-set s b n anps) (or (<= (+ c (nfix n2)) b) (<= (+ b n) c)))
(reg-frame reg-caps-frame (anp-caps x i k b n anps) (or (<= (+ c (nfix n2)) b) (<= (+ b n) c)))
(reg-frame reg-fncaps-frame (anp-fncaps x i k b n anps) (or (<= (+ c (nfix n2)) b) (<= (+ b n) c)))
(reg-frame reg-rd-frame (anp-rd fl x j m b n anps) (or (<= (+ c (nfix n2)) b) (<= (+ b n) c)))
(reg-frame reg-mark-frame (anp-mark x anps) t)

; what a copy and an or leave in their target
(defthm reg-copy-k
  (implies (and (natp k) (natp n) (<= k n) (natp from) (natp to) (or (<= (+ from n) to) (<= (+ to n) from))
                (equal (anp-err (anp-copy k n from to anps)) 0))
           (equal (reg (anp-copy k n from to anps) (+ to k) (- n k)) (reg anps (+ from k) (- n k))))
  :hints (("Goal" :induct (anp-copy k n from to anps))))

(defthm reg-copy
  (implies (and (natp n) (natp from) (natp to) (or (<= (+ from n) to) (<= (+ to n) from))
                (equal (anp-err (anp-copy 0 n from to anps)) 0))
           (equal (reg (anp-copy 0 n from to anps) to n) (reg anps from n)))
  :hints (("Goal" :use (:instance reg-copy-k (k 0)))))

(defthm reg-or-k
  (implies (and (natp k) (natp n) (<= k n) (natp from) (natp to) (or (<= (+ from n) to) (<= (+ to n) from))
                (equal (anp-err (anp-or k n from to anps)) 0))
           (equal (reg (anp-or k n from to anps) (+ to k) (- n k))
                  (sp-or (reg anps (+ from k) (- n k)) (reg anps (+ to k) (- n k)))))
  :hints (("Goal" :induct (anp-or k n from to anps))))

(defthm reg-or
  (implies (and (natp n) (natp from) (natp to) (or (<= (+ from n) to) (<= (+ to n) from))
                (equal (anp-err (anp-or 0 n from to anps)) 0))
           (equal (reg (anp-or 0 n from to anps) to n) (sp-or (reg anps from n) (reg anps to n))))
  :hints (("Goal" :use (:instance reg-or-k (k 0)))))

(defthm reg-set
  (implies (and (natp b) (natp n) (equal (anp-err (anp-set s b n anps)) 0))
           (equal (reg (anp-set s b n anps) b n) (sp-set s (reg anps b n) n))))

(defthm reg-caps
  (implies (and (natp b) (natp n) (equal (anp-err (anp-caps x i k b n anps)) 0))
           (equal (reg (anp-caps x i k b n anps) b n) (sp-caps x i k (reg anps b n) n))))

(defthm reg-fncaps
  (implies (and (natp b) (natp n) (equal (anp-err (anp-fncaps x i k b n anps)) 0))
           (equal (reg (anp-fncaps x i k b n anps) b n) (sp-fncaps x i k (reg anps b n) n))))

(defthm reg-rd
  (implies (and (natp b) (natp n) (equal (anp-err (anp-rd fl x j m b n anps)) 0))
           (equal (reg (anp-rd fl x j m b n anps) b n) (sp-rd fl x j m (reg anps b n) n))))

(defthm update-err-fields
  (and (equal (anp-lv-length (update-anp-err v anps)) (anp-lv-length anps))
       (equal (anp-get i (update-anp-err v anps)) (anp-get i anps))
       (equal (mks (update-anp-err v anps)) (mks anps))
       (equal (anp-err (update-anp-err v anps)) v))
  :hints (("Goal" :in-theory (enable anp-lv-length anp-get mks anp-err anp-nmk))))

(defthm update-nmk-fields
  (and (equal (anp-lv-length (update-anp-nmk v anps)) (anp-lv-length anps))
       (equal (anp-get i (update-anp-nmk v anps)) (anp-get i anps))
       (equal (mks (update-anp-nmk 0 anps)) nil)
       (equal (anp-err (update-anp-nmk v anps)) (anp-err anps)))
  :hints (("Goal" :in-theory (enable anp-lv-length anp-get mks anp-err anp-nmk))))

(in-theory (disable update-anp-err update-anp-nmk))

(defthm reg-update-err (equal (reg (update-anp-err v anps) b n) (reg anps b n)))
(defthm reg-update-nmk (equal (reg (update-anp-nmk v anps) b n) (reg anps b n)))

; ---- THE LIVENESS PASS ----------------------------------------------------------------------------

(defthm anp-live-err-stops
  (implies (not (equal (anp-err anps) 0)) (equal (anp-live fl x j m b top n anps) anps)))

(defthm anp-live-length (equal (anp-lv-length (anp-live fl x j m b top n anps)) (anp-lv-length anps)))

(defthm anp-live-err-back
  (implies (equal (anp-err (anp-live fl x j m b top n anps)) 0) (equal (anp-err anps) 0))
  :rule-classes :forward-chaining)

; what it writes: its own region and the free ones above top
(defthm anp-live-frame
  (implies (and (natp b) (natp top) (natp n) (<= (+ b n) top)
                (or (not (integerp i)) (and (< i top) (or (equal fl 2) (< i b) (<= (+ b n) i)))))
           (equal (anp-get i (anp-live fl x j m b top n anps)) (anp-get i anps))))

(defthm reg-live-frame
  (implies (and (natp c) (natp b) (natp top) (natp n) (<= (+ b n) top) (<= (+ c (nfix n2)) top)
                (or (equal fl 2) (<= (+ c (nfix n2)) b) (<= (+ b n) c)))
           (equal (reg (anp-live fl x j m b top n anps) c n2) (reg anps c n2)))
  :hints (("Goal" :induct (reg anps c n2))))

(defthm anp-append-assoc (equal (append (append a b) c) (append a (append b c))))

; ---- THE PASS COMPUTES ITS MEANING ----------------------------------------------------------------

(defthm anp-live-spec
  (implies (and (natp b) (natp top) (natp n) (<= (+ b n) top)
                (equal (anp-err (anp-live fl x j m b top n anps)) 0))
           (and (equal (reg (anp-live fl x j m b top n anps) (if (equal fl 2) top b) n)
                       (sp-out fl x j m (if (equal fl 2) (reg anps top n) nil) (reg anps b n) n))
                (equal (mks (anp-live fl x j m b top n anps))
                       (append (mks anps) (sp-mk fl x j m (reg anps b n) n)))))
  :hints (("Goal" :induct (anp-live fl x j m b top n anps))))

(defun zeros (n) (if (zp n) nil (cons 0 (zeros (- n 1)))))

(defthm reg-zero-k
  (implies (and (natp k) (natp n) (<= k n) (equal (anp-err (anp-zero k n anps)) 0))
           (equal (reg (anp-zero k n anps) k (- n k)) (zeros (- n k))))
  :hints (("Goal" :induct (anp-zero k n anps))))

(defthm reg-zero
  (implies (and (natp n) (equal (anp-err (anp-zero 0 n anps)) 0))
           (equal (reg (anp-zero 0 n anps) 0 n) (zeros n)))
  :hints (("Goal" :use (:instance reg-zero-k (k 0)))))

; apply_clears' marks: the body's from the empty live set, none when it recurs to its fn
(defthm anp-clears-spec
  (implies (and (natp n) (equal (anp-err (anp-clears x n anps)) 0))
           (equal (mks (anp-clears x n anps))
                  (if (anp-hfr 0 x 0 0) nil (sp-mk 0 x 0 0 (zeros n) n))))
  :hints (("Goal" :in-theory (disable anp-live-spec)
           :use ((:instance anp-live-spec (fl 0) (j 0) (m 0) (b 0) (top n)
                            (anps (anp-zero 0 n (update-anp-nmk 0 (update-anp-err 0 anps)))))))))

; SLICE 4c-ii of the ahead-of-time compiler (model/aot-PLAN.md): THE PRIMS, the instruction's own
; facts, before aot-ir-proof composes them with the compile (aot-cc-correct, 4c-iii). A guarded op
; (:prim d t p w xs hd hs blk res) puts in d the op's value when its guard passes, else what the
; generic call of the head's fn on the operands answers (the escape hatch), and the run stops when
; that throws (aot-prim-run). Passing its guard, the op is in range (aot-pg-inr: no long + - * inc dec
; or int cast that passes its guard overflows), so its Fortran value is the generic call's, by A-PRIM
; (aot-pg-host). The guard's own arithmetic never overflows (aot-pg-safe), so the guard is defined
; Fortran.
;
; ASSUMED, named: A-PRIM (aot-prim-ok f p w ts ws): the host's call of f -- the op's fn, the head the
; compiler read (head-op) -- on operand values whose annotated types are ts answers Clojure's value,
; which is the op on the operands as the Fortran reads them (at ws: a long read as a double is
; widened, aot-cv): the exact one on longs where Clojure answers at all (in range; out of range clj
; throws, which the hatch does too), the IEEE one on doubles. A-FMUL (aot-fmul-ok): a product of
; longs whose double-precision magnitude is at most 9e18 is a long (two roundings lose at most a few
; ulps; 9e18 is 2.4% below 2^63). Neither is reducible to the model.

(in-package "ACL2")
(include-book "aot-ir")

; ---- SLOTS -----------------------------------------------------------------------------------

; x and y agree below n
(defun aot-same (n x y) (equal (take n x) (take n y)))
(defthm aot-take-update-hi
  (implies (and (natp d) (natp n) (<= n d)) (equal (take n (update-nth d v x)) (take n x))))
(defthm aot-nth-take (implies (and (natp j) (natp n) (< j n)) (equal (nth j (take n x)) (nth j x))))
(defun aot-tt-ind (n m x) (if (or (zp n) (zp m)) (list n m x) (aot-tt-ind (- n 1) (- m 1) (cdr x))))
(defthm aot-take-take
  (implies (and (natp n) (natp m) (<= n m)) (equal (take n (take m x)) (take n x)))
  :hints (("Goal" :induct (aot-tt-ind n m x))))
(defthm aot-same-refl (aot-same n x x))
(defthm aot-same-update (implies (and (natp d) (natp n) (<= n d)) (equal (aot-same n (update-nth d v x) y) (aot-same n x y))))
(defthm aot-same-update2 (implies (and (natp d) (natp n) (<= n d)) (equal (aot-same n x (update-nth d v y)) (aot-same n x y))))
(defthm aot-same-trans-lower
  (implies (and (aot-same m x y) (aot-same n y z) (natp n) (natp m) (<= n m)) (aot-same n x z))
  :hints (("Goal" :use ((:instance aot-take-take (x x)) (:instance aot-take-take (x y))) :in-theory (disable aot-take-take))))
(defthm aot-same-trans (implies (and (aot-same n x y) (aot-same n y z)) (aot-same n x z)))
(defthm aot-same-lower
  (implies (and (aot-same m x y) (natp n) (natp m) (<= n m)) (aot-same n x y))
  :hints (("Goal" :use ((:instance aot-take-take (x x)) (:instance aot-take-take (x y))) :in-theory (disable aot-take-take))))
(defthm aot-nth-same
  (implies (and (aot-same n x y) (natp j) (natp n) (< j n)) (equal (nth j x) (nth j y)))
  :hints (("Goal" :use ((:instance aot-nth-take (x x)) (:instance aot-nth-take (x y))) :in-theory (disable aot-nth-take)))
  :rule-classes nil)
(in-theory (disable aot-same))

; ---- THE SPEC: A-PRIM, A-FMUL ----------------------------------------------------------------

(defun aot-nargs (p) (cond ((member p '(5 6 13 14 15 18 19 20 21)) 1) ((and (integerp p) (< 21 p) (< p 35)) 1) ((equal p 17) 3) (t 2)))
(defun aot-i64l (l) (if (atom l) t (and (aot-i64p (car l)) (aot-i64l (cdr l)))))

; where Clojure answers the op's exact value
(defun aot-inr (p w vals)
  (let ((a (car vals)))
    (if (equal w 2)
        (case p ((1 2 3 5 6) (aot-i64p (aot-opx p w vals)))
          (19 (and (<= (- (expt 2 31)) a) (< a (expt 2 31))))
          (otherwise t))
      (if (member p '(19 20)) (aot-dcast p a) t))))

; an operand value as the Fortran reads it: a long read as a double widened (aot-coerce's (:real))
(defun aot-cvl (vals ts ws)
  (if (atom vals) nil (cons (aot-cv (car vals) (car ts) (car ws)) (aot-cvl (cdr vals) (cdr ts) (cdr ws)))))
; values fitting their annotated types, as far as A-PRIM needs: a long one is a 64-bit integer
(defun aot-fitl (vals ts)
  (if (atom vals) t (and (implies (equal (car ts) 2) (aot-i64p (car vals))) (aot-fitl (cdr vals) (cdr ts)))))

; A-PRIM
(defun-sk aot-prim-ok (f p w ts ws)
  (forall vals (implies (and (aot-fitl vals ts) (equal (len vals) (aot-nargs p)) (aot-inr p w (aot-cvl vals ts ws)))
                        (equal (aot-hcall f vals) (cons :val (aot-opx p w (aot-cvl vals ts ws)))))))
; A-FMUL
(defun-sk aot-fmul-ok ()
  (forall (a b) (implies (and (aot-i64p a) (aot-i64p b) (not (aot-fbig a b))) (aot-i64p (* a b)))))

; THE GUARD: passing it, the op is in range
(defthm aot-pg-inr
  (implies (and (aot-pg p w vals) (implies (equal w 2) (aot-i64l vals)) (equal (len vals) (aot-nargs p)) (aot-fmul-ok))
           (aot-inr p w vals))
  :hints (("Goal" :in-theory (disable aot-fmul-ok-necc)
                  :use ((:instance aot-fmul-ok-necc (a (car vals)) (b (cadr vals)))))))

(defthm aot-len-cvl (equal (len (aot-cvl vals ts ws)) (len vals)))
(defthm aot-pg-host
  (implies (and (aot-pg p w (aot-cvl vals ts ws)) (implies (equal w 2) (aot-i64l (aot-cvl vals ts ws)))
                (aot-fitl vals ts) (equal (len vals) (aot-nargs p)) (aot-fmul-ok) (aot-prim-ok f p w ts ws))
           (equal (aot-hcall f vals) (cons :val (aot-opx p w (aot-cvl vals ts ws)))))
  :hints (("Goal" :in-theory (disable aot-prim-ok-necc aot-pg aot-inr aot-opx aot-cvl)
                  :use ((:instance aot-prim-ok-necc) (:instance aot-pg-inr (vals (aot-cvl vals ts ws)))))))
; an unguarded op is in range wherever it is defined
(defthm aot-unguarded-inr
  (implies (and (not (member p '(19 20))) (or (not (equal w 2)) (not (member p '(1 2 3 5 6)))))
           (aot-inr p w vals)))

; the guard's own terms are longs: Fortran evaluates both halves of an .and., whatever b's sign
(defthm aot-pg-safe
  (implies (and (aot-i64p b))
           (and (aot-i64p (- *aot-h* (max b 0))) (aot-i64p (- (- (- *aot-h*) 1) (min b 0)))
                (aot-i64p (+ *aot-h* (min b 0))) (aot-i64p (+ (- (- *aot-h*) 1) (max b 0))))))

; ---- THE INSTRUCTION ---------------------------------------------------------------------------

(defthm aot-wblk-nth-lo
  (implies (and (natp j) (natp blk) (< j blk)) (equal (nth j (aot-wblk blk vals bt)) (nth j bt))))
(defthm aot-wblk-same
  (implies (and (natp n) (natp blk) (<= n blk)) (aot-same n (aot-wblk blk vals bt) bt))
  :hints (("Goal" :induct (aot-wblk blk vals bt) :in-theory (enable aot-same-update2))))

; the head's fn: a Var dereffed from its pool slot hd, or the pool slot hs itself
(defun aot-hd (hd hs bt) (if hd (aot-deref (nth (nfix hd) bt)) (nth (nfix hs) bt)))

; the slots the compile gives it: the temporaries at or above n, the head in the pool below them
(defun aot-prim-slots (x n)
  (let ((d (nth 1 x)) (hd (nth 6 x)) (hs (nth 7 x)) (blk (nth 8 x)) (res (nth 9 x)))
    (and (equal (car x) :prim) (natp n) (natp d) (natp blk) (natp res) (natp hs)
         (<= n d) (<= n blk) (<= n res)
         (if hd (and (natp hd) (< hd n) (<= n hs)) (< hs n)))))

; AOT-PRIM-RUN: the instruction answers the op when its guard passes, else exactly when the
; generic call answers, d then holding its value; the frame is the operands' (a marked read clears
; its slot) and no slot below n moved
(defthm aot-prim-run
  (implies (aot-prim-slots x n)
           (let* ((xr (aot-xsrun (nth 5 x) fr bt)) (vals (car xr)) (s (aot-ir-step x fr bt))
                  (g (aot-pg (nth 3 x) (nth 4 x) vals)) (h (aot-hcall (aot-hd (nth 6 x) (nth 7 x) bt) vals)))
             (and (iff s (or g (and (consp h) (equal (car h) :val))))
                  (implies s (and (equal (nth (nth 1 x) (cadr s)) (if g (aot-opx (nth 3 x) (nth 4 x) vals) (cdr h)))
                                  (equal (car s) (cdr xr))
                                  (aot-same n (cadr s) bt))))))
  :hints (("Goal" :in-theory (e/d (aot-prim-step) (aot-pg aot-opx aot-same aot-wblk))
                  :use ((:instance aot-wblk-same (blk (nth 8 x)) (vals (car (aot-xsrun (nth 5 x) fr bt))))
                        (:instance aot-wblk-nth-lo (j (nth 6 x)) (blk (nth 8 x)) (vals (car (aot-xsrun (nth 5 x) fr bt))))
                        (:instance aot-wblk-nth-lo (j (nth 7 x)) (blk (nth 8 x)) (vals (car (aot-xsrun (nth 5 x) fr bt))))))))

; ---- 4c-iv: THE COMPARE WITH A BOXED OPERAND ---------------------------------------------------
; A-CMPB (aot-cmpb-ok f p nt bi): the host's call of f -- the compare's fn -- on the typed operand (a
; long when nt is 2: a 64-bit integer) and a boxed number (tagged 2: a 64-bit integer; 3: a double),
; in the order bi keeps, answers the compare as the Fortran computes it on the tag-numeric path
; (aot-cmpval): the two longs exactly, else both as doubles. The spec of the core compares at mixed
; types, A-PRIM's counterpart for the boxed path; named, not reducible to the model.
(defun-sk aot-cmpb-ok (f p nt bi)
  (forall (xv v)
    (implies (and (or (equal nt 2) (equal nt 3)) (implies (equal nt 2) (aot-i64p xv))
                  (aot-numtag (aot-vtag v)) (implies (equal (aot-vtag v) 2) (aot-i64p v)))
             (equal (aot-hcall f (aot-ord bi xv v)) (cons :val (aot-cmpval p nt bi xv v))))))
(defun aot-cmpb-slots (x n)
  (let ((d (nth 1 x)) (s (nth 6 x)) (hd (nth 7 x)) (hs (nth 8 x)) (blk (nth 9 x)) (res (nth 10 x)))
    (and (equal (car x) :cmpb) (natp n) (natp d) (natp s) (natp blk) (natp res) (natp hs)
         (<= n d) (<= n blk) (<= n res)
         (if hd (and (natp hd) (< hd n) (<= n hs)) (< hs n)))))
(defun aot-cmpb-fit (x fr bt)
  (let ((xv (car (aot-xrun (nth 5 x) fr bt))) (v (nth (nth 6 x) bt)) (nt (nth 3 x)))
    (and (or (equal nt 2) (equal nt 3)) (implies (equal nt 2) (aot-i64p xv))
         (implies (and (aot-numtag (aot-vtag v)) (equal (aot-vtag v) 2)) (aot-i64p v)))))
; AOT-CMPB-RUN: the instruction answers exactly when the generic call of the head's fn on the operands
; (in the order kept) does, d then holding its value; the frame is the typed operand's and no slot
; below n moved
(defthm aot-cmpb-run
  (implies (and (aot-cmpb-slots x n) (aot-cmpb-fit x fr bt)
                (aot-cmpb-ok (aot-hd (nth 7 x) (nth 8 x) bt) (nth 2 x) (nth 3 x) (nth 4 x)))
           (let* ((xr (aot-xrun (nth 5 x) fr bt)) (vals (aot-ord (nth 4 x) (car xr) (nth (nth 6 x) bt)))
                  (s (aot-ir-step x fr bt)) (h (aot-hcall (aot-hd (nth 7 x) (nth 8 x) bt) vals)))
             (and (iff s (and (consp h) (equal (car h) :val)))
                  (implies s (and (equal (nth (nth 1 x) (cadr s)) (cdr h))
                                  (equal (car s) (cdr xr))
                                  (aot-same n (cadr s) bt))))))
  :hints (("Goal" :in-theory (e/d (aot-cmpb-step aot-cmpb-fit) (aot-same aot-wblk aot-cmpb-ok-necc aot-xrun aot-cmpval))
                  :use ((:instance aot-cmpb-ok-necc (f (aot-hd (nth 7 x) (nth 8 x) bt)) (p (nth 2 x)) (nt (nth 3 x)) (bi (nth 4 x))
                                   (xv (car (aot-xrun (nth 5 x) fr bt))) (v (nth (nth 6 x) bt)))
                        (:instance aot-wblk-same (blk (nth 9 x)) (vals (aot-ord (nth 4 x) (car (aot-xrun (nth 5 x) fr bt)) (nth (nth 6 x) bt))))
                        (:instance aot-wblk-nth-lo (j (nth 7 x)) (blk (nth 9 x)) (vals (aot-ord (nth 4 x) (car (aot-xrun (nth 5 x) fr bt)) (nth (nth 6 x) bt))))
                        (:instance aot-wblk-nth-lo (j (nth 8 x)) (blk (nth 9 x)) (vals (aot-ord (nth 4 x) (car (aot-xrun (nth 5 x) fr bt)) (nth (nth 6 x) bt))))))))

(defthm aot-xrun-op
  (equal (aot-xrun (list :op p w xs) fr bt) (let ((r (aot-xsrun xs fr bt))) (cons (aot-opx p w (car r)) (cdr r))))
  :hints (("Goal" :expand ((aot-xrun (list :op p w xs) fr bt)))))
(defthm aot-xrun-real
  (equal (aot-xrun (list :real x) fr bt) (let ((r (aot-xrun x fr bt))) (cons (aot-l2d (car r)) (cdr r))))
  :hints (("Goal" :expand ((aot-xrun (list :real x) fr bt)))))
(defthm aot-xrun-coerce
  (equal (aot-xrun (aot-coerce x a w) fr bt) (let ((r (aot-xrun x fr bt))) (cons (aot-cv (car r) a w) (cdr r)))))
(defthm aot-xsrun-2
  (and (equal (aot-xsrun (list x) fr bt) (let ((r (aot-xrun x fr bt))) (cons (list (car r)) (cdr r))))
       (equal (aot-xsrun (list x y) fr bt)
              (let* ((r (aot-xrun x fr bt)) (r2 (aot-xrun y (cdr r) bt))) (cons (list (car r) (car r2)) (cdr r2)))))
  :hints (("Goal" :expand ((aot-xsrun (list x) fr bt) (aot-xsrun (list x y) fr bt) (aot-xsrun (list y) (cdr (aot-xrun x fr bt)) bt)))))

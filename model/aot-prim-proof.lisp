; SLICE 4c-ii of the ahead-of-time compiler (model/aot-PLAN.md): THE PRIMS, proved against the host's
; generic call. A guarded op (:prim d t p w xs hd hs blk res) answers in d exactly what the generic
; call of the op's fn on its operands answers -- the escape hatch by definition when the guard fails,
; and when it passes the Fortran's own value, which is the call's by A-PRIM, because the guard keeps
; the op in range (aot-pg-inr: no long + - * inc dec or int cast that passes its guard overflows).
; An unguarded op's value (:op p w xs) is the call's the same way (aot-pg-host). The guard's own
; arithmetic never overflows (aot-pg-safe), so the guard is defined Fortran.
;
; ASSUMED, named: A-PRIM (aot-prim-ok f p w): the host's call of f -- the op's fn, the head the
; compiler read (head-op) -- on operands of the type it is read at answers Clojure's value, the exact
; one on longs where Clojure answers at all (in range; out of range clj throws, which the hatch
; does too), the IEEE one on doubles. A-FMUL (aot-fmul-ok): a product of longs whose double-
; precision magnitude is at most 9e18 is a long (two roundings lose at most a few ulps; 9e18 is 2.4%
; below 2^63). Neither is reducible to the model: exec does not model the host's apply of a builtin
; (ex-ev answers (:out) for it), which is also why aot-cc-correct's subset has no call -- a tree whose
; prim runs is outside it, and composing this with aot-cc-correct is OWED (it needs an exec that
; applies the core ops).

(in-package "ACL2")
(include-book "aot-ir-proof")

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

; A-PRIM
(defun-sk aot-prim-ok (f p w)
  (forall vals (implies (and (implies (equal w 2) (aot-i64l vals)) (equal (len vals) (aot-nargs p)) (aot-inr p w vals))
                        (equal (aot-hcall f vals) (cons :val (aot-opx p w vals))))))
; A-FMUL
(defun-sk aot-fmul-ok ()
  (forall (a b) (implies (and (aot-i64p a) (aot-i64p b) (not (aot-fbig a b))) (aot-i64p (* a b)))))

; THE GUARD: passing it, the op is in range
(defthm aot-pg-inr
  (implies (and (aot-pg p w vals) (implies (equal w 2) (aot-i64l vals)) (equal (len vals) (aot-nargs p)) (aot-fmul-ok))
           (aot-inr p w vals))
  :hints (("Goal" :in-theory (disable aot-fmul-ok-necc)
                  :use ((:instance aot-fmul-ok-necc (a (car vals)) (b (cadr vals)))))))

(defthm aot-pg-host
  (implies (and (aot-pg p w vals) (implies (equal w 2) (aot-i64l vals)) (equal (len vals) (aot-nargs p))
                (aot-fmul-ok) (aot-prim-ok f p w))
           (equal (aot-hcall f vals) (cons :val (aot-opx p w vals))))
  :hints (("Goal" :in-theory (disable aot-prim-ok-necc aot-pg aot-inr aot-opx)
                  :use ((:instance aot-prim-ok-necc) aot-pg-inr))))

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

(defun aot-prim-hyp (x n fr bt)
  (let ((d (nth 1 x)) (p (nth 3 x)) (w (nth 4 x)) (hd (nth 6 x)) (hs (nth 7 x)) (blk (nth 8 x)) (res (nth 9 x))
        (vals (car (aot-xsrun (nth 5 x) fr bt))))
    (and (equal (car x) :prim) (natp n) (natp d) (natp blk) (natp res) (natp hs)
         (<= n d) (<= n blk) (<= n res)
         (if hd (and (natp hd) (< hd n) (<= n hs)) (< hs n))      ; the head in the pool, below the temporaries
         (aot-prim-ok (aot-hd hd hs bt) p w) (aot-fmul-ok)     ; A-PRIM, A-FMUL
         (implies (equal w 2) (aot-i64l vals)) (equal (len vals) (aot-nargs p)))))

; AOT-PRIM-CORRECT: the instruction runs exactly when the generic call answers, d then holds its
; value, the frame is the operands' (a marked read clears its slot), and no slot below n moved
(defthm aot-prim-correct
  (implies (aot-prim-hyp x n fr bt)
           (let* ((xr (aot-xsrun (nth 5 x) fr bt)) (s (aot-ir-step x fr bt))
                  (h (aot-hcall (aot-hd (nth 6 x) (nth 7 x) bt) (car xr))))
             (and (iff s (and (consp h) (equal (car h) :val)))
                  (implies s (and (equal (nth (nth 1 x) (cadr s)) (cdr h))
                                  (equal (car s) (cdr xr))
                                  (aot-same n (cadr s) bt))))))
  :hints (("Goal" :in-theory (e/d (aot-prim-step) (aot-pg aot-opx aot-prim-ok aot-fmul-ok aot-same aot-wblk))
                  :use ((:instance aot-pg-host (p (nth 3 x)) (w (nth 4 x)) (vals (car (aot-xsrun (nth 5 x) fr bt)))
                                   (f (aot-hd (nth 6 x) (nth 7 x) bt)))
                        (:instance aot-wblk-same (blk (nth 8 x)) (vals (car (aot-xsrun (nth 5 x) fr bt))))
                        (:instance aot-wblk-nth-lo (j (nth 6 x)) (blk (nth 8 x)) (vals (car (aot-xsrun (nth 5 x) fr bt))))
                        (:instance aot-wblk-nth-lo (j (nth 7 x)) (blk (nth 8 x)) (vals (car (aot-xsrun (nth 5 x) fr bt))))))))

; an unguarded op set into a temporary, (:tset d t (:op p w xs)): the generic call's value
(defthm aot-xrun-op
  (equal (aot-xrun (list :op p w xs) fr bt) (let ((r (aot-xsrun xs fr bt))) (cons (aot-opx p w (car r)) (cdr r))))
  :hints (("Goal" :expand ((aot-xrun (list :op p w xs) fr bt)))))
(defthm aot-op-correct
  (implies (and (equal x (list :op p w xs)) (aot-pg p w (car (aot-xsrun xs fr bt)))
                (aot-prim-ok f p w) (aot-fmul-ok)
                (implies (equal w 2) (aot-i64l (car (aot-xsrun xs fr bt)))) (equal (len (car (aot-xsrun xs fr bt))) (aot-nargs p)))
           (equal (aot-hcall f (car (aot-xsrun xs fr bt))) (cons :val (car (aot-xrun x fr bt)))))
  :hints (("Goal" :in-theory (disable aot-pg aot-opx aot-prim-ok aot-fmul-ok aot-pg-host)
                  :use ((:instance aot-pg-host (vals (car (aot-xsrun xs fr bt))))))))

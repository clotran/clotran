; WHAT THE TYPE INFERENCE NEEDS, AND WHAT IT COSTS (model/aot.lisp aot-ty, slice 2 of
; model/aot-PLAN.md): the lemmas the soundness theorem against exec.lisp ex-ev stands on,
; and the cost. The theorem itself (aot-ty-sound) is drafted in aot-ty-sound.draft, NOT YET
; PROVED; aot-PLAN.md slice 2 states it and its hypotheses exactly.
;
;   aot-ty-restore   every walk leaves the slot types (tv), the current loop (cb cn) and rc length
;                    as it found them, and -- but a call argument walk (flag 4) -- the operand
;                    registers: each put paired with its restore (aot-ty-env, aot-ty-regs-env)
;   aot-ty-rc-grows  an ok walk only grows what the current loop recurs carried (rc), below the
;                    current loop top (aot-ty-rc-le; needs ok in every round, aot.lisp)
;   aot-star-*       a loop rounds: aot-star is the env the final round types the body in;
;                    the answer and ok are that walk (aot-star-ty), the walk leaves the loop rc
;                    settled below its types (aot-star-settled), and the env is above the one
;                    the rounds started in and the same off the loop slots (aot-star-env)
;   aot-ffr-*        a frame fitting an env (aot-ffr): kept by a let bind and unbind, by an ok
;                    walk (rc grows), settled into the plain fit, widened and narrowed by a
;                    loop rounds -- the steps the theorem cases take
;   aot-ty-cost      the nodes visited (ns) at most aot-wt: a node 1 + its parts, a loop body
;                    7 times (six rounds and the boxed one), an array cast operand twice --
;                    7^d walks of a node under d nested loops, as compiler.cljf loop-env
;
; aot-ty is disabled and opened by aot-ty-cases, one rule per flag and kind, each firing only on
; a call whose node and state are variables (so an inner walk stays closed, as its hypothesis).

(in-package "ACL2")

(include-book "aot")
(include-book "exec")

; ---- THE STOBJ'S FIELDS AS LISTS ------------------------------------------------------------
; fields: 0 tv, 1 rc, 2 lo, 3 cb, 4 cn, 5 a0, 6 a1, 7 a2, 8 ad, 9 ns

(defstub aot-tag (*) => *)
(defstub aot-opof (*) => *)

(defun tvg (s l) (if (and (natp s) (< s (len l))) (aot-code (nth s l)) 1))
(defun rcg (s l) (if (and (natp s) (< s (len l))) (aot-code (nth s l)) 0))

(defthm aot-get-tvg (equal (aot-get s aots) (tvg s (nth 0 aots)))
  :hints (("Goal" :in-theory (enable aot-get aot-tvi aot-tv-length))))
(defthm aot-rget-rcg (equal (aot-rget s aots) (rcg s (nth 1 aots)))
  :hints (("Goal" :in-theory (enable aot-rget aot-rci aot-rc-length))))
(defthm aot-raw-nth (equal (aot-raw s aots) (if (and (natp s) (< s (len (nth 0 aots)))) (nth s (nth 0 aots)) 1))
  :hints (("Goal" :in-theory (enable aot-raw aot-tvi aot-tv-length))))
(defthm aot-fields-nth
  (and (equal (aot-cb x) (nth 3 x)) (equal (aot-cn x) (nth 4 x)) (equal (aot-a0 x) (nth 5 x)) (equal (aot-a1 x) (nth 6 x))
       (equal (aot-a2 x) (nth 7 x)) (equal (aot-ad x) (nth 8 x)) (equal (aot-ns x) (nth 9 x)))
  :hints (("Goal" :in-theory (enable aot-cb aot-cn aot-a0 aot-a1 aot-a2 aot-ad aot-ns))))
(defthm aot-updates-nth
  (and (equal (update-aot-cb v x) (update-nth 3 v x)) (equal (update-aot-cn v x) (update-nth 4 v x))
       (equal (update-aot-a0 v x) (update-nth 5 v x)) (equal (update-aot-a1 v x) (update-nth 6 v x))
       (equal (update-aot-a2 v x) (update-nth 7 v x)) (equal (update-aot-ad v x) (update-nth 8 v x)))
  :hints (("Goal" :in-theory (enable update-aot-cb update-aot-cn update-aot-a0 update-aot-a1 update-aot-a2 update-aot-ad))))

(defthm aot-tick-nth (implies (and (natp f) (not (equal f 9))) (equal (nth f (aot-tick aots)) (nth f aots)))
  :hints (("Goal" :in-theory (enable aot-tick update-aot-ns))))
(defthm aot-tick-ns
  (equal (nth 9 (aot-tick aots)) (if (and (natp (nth 9 aots)) (< (nth 9 aots) *anp40*)) (+ 1 (nth 9 aots)) (nth 9 aots)))
  :hints (("Goal" :in-theory (enable aot-tick update-aot-ns aot-ns))))
(defthm aot-put-nth (implies (and (natp f) (not (equal f 0))) (equal (nth f (aot-put s v aots)) (nth f aots)))
  :hints (("Goal" :in-theory (enable aot-put update-aot-tvi aot-tv-length))))
(defthm aot-put-tv
  (equal (nth 0 (aot-put s v aots)) (if (and (natp s) (< s (len (nth 0 aots)))) (update-nth s v (nth 0 aots)) (nth 0 aots)))
  :hints (("Goal" :in-theory (enable aot-put update-aot-tvi aot-tv-length))))
(defthm aot-rjn-nth (implies (and (natp f) (not (equal f 1))) (equal (nth f (aot-rjn s v aots)) (nth f aots)))
  :hints (("Goal" :in-theory (enable aot-rjn update-aot-rci aot-rc-length))))
(defthm aot-rjn-rc
  (equal (nth 1 (aot-rjn s v aots))
         (if (and (natp s) (< s (len (nth 1 aots)))) (update-nth s (aot-jn (rcg s (nth 1 aots)) (aot-code v)) (nth 1 aots)) (nth 1 aots)))
  :hints (("Goal" :in-theory (enable aot-rjn update-aot-rci aot-rc-length))))
(defthm aot-rz-nth (implies (and (natp f) (not (equal f 1))) (equal (nth f (aot-rz s aots)) (nth f aots)))
  :hints (("Goal" :in-theory (enable aot-rz update-aot-rci aot-rc-length))))
(defthm aot-rz-rc
  (equal (nth 1 (aot-rz s aots)) (if (and (natp s) (< s (len (nth 1 aots)))) (update-nth s 0 (nth 1 aots)) (nth 1 aots)))
  :hints (("Goal" :in-theory (enable aot-rz update-aot-rci aot-rc-length))))
(defthm aot-lput-nth (implies (and (natp f) (not (equal f 2))) (equal (nth f (aot-lput s v aots)) (nth f aots)))
  :hints (("Goal" :in-theory (enable aot-lput update-aot-loi aot-lo-length))))
(in-theory (disable tvg rcg))

(defthm aot-rzero-nth (implies (and (natp f) (not (equal f 1))) (equal (nth f (aot-rzero b i m aots)) (nth f aots)))
  :hints (("Goal" :induct (aot-rzero b i m aots) :in-theory (enable aot-rzero))))
(defthm aot-rzero-len (equal (len (nth 1 (aot-rzero b i m aots))) (len (nth 1 aots)))
  :hints (("Goal" :induct (aot-rzero b i m aots) :in-theory (enable aot-rzero))))
(defthm aot-rzero-below
  (implies (and (natp s) (natp b) (< s b)) (equal (rcg s (nth 1 (aot-rzero b i m aots))) (rcg s (nth 1 aots))))
  :hints (("Goal" :induct (aot-rzero b i m aots) :in-theory (enable aot-rzero rcg))))
(defthm aot-lcopy-nth (implies (and (natp f) (not (equal f 2))) (equal (nth f (aot-lcopy b i m aots)) (nth f aots)))
  :hints (("Goal" :induct (aot-lcopy b i m aots) :in-theory (enable aot-lcopy))))

(defthm aot-update-nth-nth (implies (and (natp s) (< s (len l))) (equal (update-nth s (nth s l) l) l)))

; ---- aot-ty OPENED, ONE CASE AT A TIME ------------------------------------------------------

(defmacro aot-go (e j m k) `(and (not (equal (aot-k ,e) 0)) (natp ,j) (natp ,m) (natp ,k)))

(defthm aot-ty-stop
  (implies (not (aot-go e j m k)) (equal (aot-ty fl e j m k aots) (mv 1 1 (aot-tick aots))))
  :hints (("Goal" :expand ((aot-ty fl e j m k aots)))))

(defmacro aot-tycase (fl kd body)
  `(defthm ,(intern$ (concatenate 'string "AOT-TY-" (coerce (explode-atom fl 10) (quote string)) "-" (coerce (explode-atom kd 10) (quote string))) "ACL2")
     (implies (and (syntaxp (and (variablep e) (or (variablep j) (quotep j)) (variablep aots))) (aot-go e j m k) ,@(cond ((eq kd 'x) nil) ((eq kd 'other) '((not (member (aot-k e) '(1 2 4 5 6 11 12 16))))) (t `((equal (aot-k e) ,kd)))))
              (equal (aot-ty ,(if (eq fl 'z) 0 fl) e j m k aots)
                     (let ((aots (aot-tick aots))) ,body)))
     :hints (("Goal" :expand ((aot-ty ,(if (eq fl 'z) 0 fl) e j m k aots))))))

(aot-tycase z 1 (mv (aot-cty e) 1 aots))
(aot-tycase z 2 (mv (aot-get (aot-i2 e) aots) 1 aots))
(aot-tycase z 5 (if (equal (aot-nk e) 0) (mv 1 1 aots) (aot-ty 1 e 0 (aot-nk e) 0 aots)))
(aot-tycase z 4
  (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e 0) 0 0 0 aots)
    (declare (ignore t0))
    (mv-let (t1 o1 aots) (aot-ty 0 (aot-kid e 1) 0 0 0 aots)
      (mv-let (t2 o2 aots) (aot-ty 0 (aot-kid e 2) 0 0 0 aots)
        (mv (aot-jn t1 t2) (aot-and o0 (aot-and o1 o2)) aots)))))
(aot-tycase z 11 (aot-ty 2 e 0 (aot-i2 e) 0 aots))
(aot-tycase z 12 (aot-ty 6 e 0 (aot-i2 e) 0 aots))
(aot-tycase z 16
  (let* ((nk (aot-nk e)) (cb (aot-cb aots)) (cn (aot-cn aots)) (hit (equal (aot-rs e) cb))
         (mm (if (and hit (anp40p cn) (< nk cn)) cn nk)))
    (mv-let (t0 o0 aots) (aot-ty 3 e 0 mm 0 aots)
      (declare (ignore t0))
      (mv 0 (if (and (equal o0 1) hit (equal nk cn) (equal (aot-rn e) cn)) 1 0) aots))))
(aot-tycase z 6
  (let ((s0 (aot-a0 aots)) (s1 (aot-a1 aots)) (s2 (aot-a2 aots)) (sd (aot-ad aots)))
    (let* ((aots (update-aot-a0 1 aots)) (aots (update-aot-a1 1 aots))
           (aots (update-aot-a2 1 aots)) (aots (update-aot-ad 0 aots)))
      (mv-let (th oh aots) (aot-ty 0 (aot-kid e 0) 0 0 0 aots)
        (declare (ignore th))
        (mv-let (tw ow aots) (aot-ty 4 e 1 (aot-nk e) 0 aots)
          (declare (ignore tw))
          (let* ((tc (aot-optab (aot-hop e) (if (< 0 (aot-nk e)) (- (aot-nk e) 1) 0)
                                (aot-a0 aots) (aot-a1 aots) (aot-a2 aots)))
                 (aots (update-aot-a0 s0 aots)) (aots (update-aot-a1 s1 aots))
                 (aots (update-aot-a2 s2 aots)) (aots (update-aot-ad sd aots)))
            (mv tc (aot-and oh ow) aots)))))))
(aot-tycase z other (mv 1 1 aots))
(aot-tycase 1 x
  (if (< j m)
      (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e j) 0 0 0 aots)
        (if (< (+ 1 j) m)
            (mv-let (t1 o1 aots) (aot-ty 1 e (+ 1 j) m 0 aots) (mv t1 (aot-and o0 o1) aots))
          (mv t0 o0 aots)))
    (mv 1 1 aots)))
(defmacro aot-bindcase (fl rest)
  `(aot-tycase ,fl x
     (if (< j m)
         (let* ((s (+ (aot-s2 e) j)) (old (aot-raw s aots)) (fresh (equal (aot-get s aots) 1)))
           (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e j) 0 0 0 aots)
             (let ((aots (aot-put s t0 aots)))
               (mv-let (t1 o1 aots) (aot-ty ,fl e (+ 1 j) m 0 aots)
                 (let ((aots (aot-put s old aots)))
                   (mv t1 (if (and fresh (equal o0 1) (equal o1 1)) 1 0) aots))))))
       ,rest)))
(aot-bindcase 2 (aot-ty 0 (aot-kid e m) 0 0 0 aots))
(aot-bindcase 6
  (let* ((b (aot-s2 e)) (ocb (aot-cb aots)) (ocn (aot-cn aots))
         (dj (and (anp40p ocb) (anp40p ocn) (<= (+ ocb ocn) b)))
         (aots (aot-rzero b 0 m aots))
         (aots (update-aot-cb b aots)) (aots (update-aot-cn m aots)))
    (mv-let (t1 o1 aots) (aot-ty 5 e 0 m 0 aots)
      (let* ((aots (update-aot-cb ocb aots)) (aots (update-aot-cn ocn aots)))
        (mv t1 (if (and dj (equal o1 1)) 1 0) aots)))))
(aot-tycase 5 x
  (let ((b (aot-s2 e)))
    (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e m) 0 0 0 aots)
      (cond ((aot-settled b 0 m aots) (let ((aots (aot-lcopy b 0 m aots))) (mv t0 o0 aots)))
            ((< 4 k) (mv-let (t1 o1 aots) (aot-ty 8 e 0 m k aots) (mv t1 (aot-and o0 o1) aots)))
            (t (mv-let (t1 o1 aots) (aot-ty 7 e 0 m k aots) (mv t1 (aot-and o0 o1) aots)))))))
(aot-tycase 7 x
  (if (< j m)
      (let* ((s (+ (aot-s2 e) j)) (old (aot-raw s aots))
             (aots (aot-put s (aot-jn (aot-get s aots) (aot-rget s aots)) aots)))
        (mv-let (t1 o1 aots) (aot-ty 7 e (+ 1 j) m k aots)
          (let ((aots (aot-put s old aots))) (mv t1 o1 aots))))
    (if (< k 5) (aot-ty 5 e 0 m (+ 1 k) aots) (mv 1 1 aots))))
(aot-tycase 8 x
  (if (< j m)
      (let* ((s (+ (aot-s2 e) j)) (old (aot-raw s aots)) (aots (aot-put s 1 aots)))
        (mv-let (t1 o1 aots) (aot-ty 8 e (+ 1 j) m k aots)
          (let ((aots (aot-put s old aots))) (mv t1 o1 aots))))
    (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e m) 0 0 0 aots)
      (let ((aots (aot-lcopy (aot-s2 e) 0 m aots))) (mv t0 o0 aots)))))
(aot-tycase 3 x
  (if (< j m)
      (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e j) 0 0 0 aots)
        (let ((aots (if (and (equal (aot-rs e) (aot-cb aots)) (< j (aot-cn aots)))
                        (aot-rjn (+ (aot-rs e) j) t0 aots)
                      aots)))
          (mv-let (t1 o1 aots) (aot-ty 3 e (+ 1 j) m 0 aots)
            (declare (ignore t1))
            (mv 0 (aot-and o0 o1) aots))))
    (mv 0 1 aots)))
(aot-tycase 4 x
  (if (< j m)
      (let* ((a (aot-kid e j)) (h (aot-hop e))
             (cast (and (equal j 1) (or (equal h 7) (equal h 8) (equal h 9)) (equal (aot-k a) 6)
                        (equal (aot-hop a) 20) (not (equal (aot-kw (aot-kid a 2)) 0)))))
        (mv-let (t0 o0 aots) (aot-ty 0 a 0 0 0 aots)
          (mv-let (ti oi aots) (aot-ty 0 (aot-kid a (if cast 1 -1)) 0 0 0 aots)
            (let* ((d (and cast (equal ti (aot-kw (aot-kid a 2)))))
                   (aots (cond ((equal j 1) (let ((aots (update-aot-a0 (if d ti t0) aots)))
                                              (update-aot-ad (if d 1 0) aots)))
                               ((equal j 2) (update-aot-a1 t0 aots))
                               ((equal j 3) (update-aot-a2 t0 aots))
                               (t aots))))
              (mv-let (t1 o1 aots) (aot-ty 4 e (+ 1 j) m 0 aots)
                (declare (ignore t1))
                (mv 0 (aot-and o0 (aot-and oi o1)) aots))))))
    (mv 0 1 aots)))
(defthm aot-ty-flx
  (implies (and (aot-go e j m k) (not (member fl '(0 1 2 3 4 5 6 7 8)))) (equal (aot-ty fl e j m k aots) (mv 1 1 (aot-tick aots))))
  :hints (("Goal" :expand ((aot-ty fl e j m k aots)))))

(in-theory (disable (:definition aot-ty) nth update-nth aot-optab aot-jn aot-and aot-code aot-cty aot-settled))

; ---- EVERY PUT PAIRED WITH ITS RESTORE ------------------------------------------------------
; the walk's view of the stobj: tv, cb, cn and rc's length (aot-env); the operand registers (aot-regs)

(defun aot-env (x) (list (nth 0 x) (nth 3 x) (nth 4 x) (len (nth 1 x))))
(defun aot-regs (x) (list (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x)))
(defun env-put (s v en) (if (and (natp s) (< s (len (car en)))) (cons (update-nth s v (car en)) (cdr en)) en))
(defun env-raw (s en) (if (and (natp s) (< s (len (car en)))) (nth s (car en)) 1))

(defthm env-tick (and (equal (aot-env (aot-tick x)) (aot-env x)) (equal (aot-regs (aot-tick x)) (aot-regs x))))
(defthm env-rjn (and (equal (aot-env (aot-rjn s v x)) (aot-env x)) (equal (aot-regs (aot-rjn s v x)) (aot-regs x))))
(defthm env-rzero (and (equal (aot-env (aot-rzero b i m x)) (aot-env x)) (equal (aot-regs (aot-rzero b i m x)) (aot-regs x))))
(defthm env-lcopy (and (equal (aot-env (aot-lcopy b i m x)) (aot-env x)) (equal (aot-regs (aot-lcopy b i m x)) (aot-regs x))))
(defthm env-put-st (and (equal (aot-env (aot-put s v x)) (env-put s v (aot-env x))) (equal (aot-regs (aot-put s v x)) (aot-regs x))))
(defthm env-raw-st (equal (aot-raw s x) (env-raw s (aot-env x))))
(defthm aot-upd-upd (equal (update-nth s a (update-nth s b l)) (update-nth s a l)) :hints (("Goal" :in-theory (enable update-nth))))
(defthm env-put-raw (equal (env-put s (env-raw s (aot-env x)) (env-put s v (aot-env x))) (aot-env x)))
(defthm env-regs-upd
  (and (equal (aot-env (update-nth 5 v x)) (aot-env x)) (equal (aot-env (update-nth 6 v x)) (aot-env x))
       (equal (aot-env (update-nth 7 v x)) (aot-env x)) (equal (aot-env (update-nth 8 v x)) (aot-env x))
       (equal (aot-regs (update-nth 3 v x)) (aot-regs x)) (equal (aot-regs (update-nth 4 v x)) (aot-regs x))
       (equal (aot-env (update-nth 3 v x)) (list (car (aot-env x)) v (caddr (aot-env x)) (cadddr (aot-env x))))
       (equal (aot-env (update-nth 4 v x)) (list (car (aot-env x)) (cadr (aot-env x)) v (cadddr (aot-env x))))
       (equal (aot-regs (update-nth 8 d (update-nth 7 c (update-nth 6 b (update-nth 5 a y))))) (list a b c d)))
  :hints (("Goal" :in-theory (enable update-nth nth))))
(defthm env-fold
  (and (equal (list (car (aot-env x)) (nth 3 x) (nth 4 x) (cadddr (aot-env x))) (aot-env x))
       (equal (list (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x)) (aot-regs x))))
(in-theory (disable aot-env aot-regs env-put env-raw aot-raw-nth aot-put-tv aot-rjn-rc aot-rz-rc))

(defthm aot-ty-env (equal (aot-env (mv-nth 2 (aot-ty fl e j m k aots))) (aot-env aots))
  :hints (("Goal" :induct (aot-ty fl e j m k aots))))

(defthm aot-ty-regs-env (implies (not (equal fl 4)) (equal (aot-regs (mv-nth 2 (aot-ty fl e j m k aots))) (aot-regs aots)))
  :hints (("Goal" :induct (aot-ty fl e j m k aots))))

(defthm aot-ty-restore
  (let ((s2 (mv-nth 2 (aot-ty fl e j m k aots))))
    (and (equal (nth 0 s2) (nth 0 aots)) (equal (nth 3 s2) (nth 3 aots)) (equal (nth 4 s2) (nth 4 aots))
         (equal (len (nth 1 s2)) (len (nth 1 aots)))))
  :hints (("Goal" :use aot-ty-env :in-theory (e/d (aot-env) (aot-ty-env env-fold)))))

(defthm aot-ty-regs
  (implies (not (equal fl 4))
           (let ((s2 (mv-nth 2 (aot-ty fl e j m k aots))))
             (and (equal (nth 5 s2) (nth 5 aots)) (equal (nth 6 s2) (nth 6 aots)) (equal (nth 7 s2) (nth 7 aots))
                  (equal (nth 8 s2) (nth 8 aots)))))
  :hints (("Goal" :use aot-ty-regs-env :in-theory (e/d (aot-regs) (aot-ty-regs-env env-fold)))))

(deftheory aot-ty-cases
  (quote (aot-ty-z-1 aot-ty-z-2 aot-ty-z-5 aot-ty-z-4 aot-ty-z-11 aot-ty-z-12 aot-ty-z-16 aot-ty-z-6 aot-ty-z-other
          aot-ty-1-x aot-ty-2-x aot-ty-6-x aot-ty-5-x aot-ty-7-x aot-ty-8-x aot-ty-3-x aot-ty-4-x aot-ty-flx)))
(in-theory (disable aot-ty-cases))

; ---- THE ORDER: 0 none below every type, 1 any above, the rest flat ----------------------------

(defun aot-le (a b) (equal (aot-jn b a) b))

(defthm aot-le-refl (aot-le a a) :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-le-trans (implies (and (aot-le a b) (aot-le b c)) (aot-le a c)) :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-le-trans2 (implies (and (aot-le b c) (aot-le a b)) (aot-le a c)) :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-le-top (implies (aot-le 1 x) (equal x 1)) :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-le-jn (and (aot-le a (aot-jn a x)) (aot-le a (aot-jn x a))) :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-le-1 (implies (and (natp a) (<= a 6)) (aot-le a 1)) :hints (("Goal" :in-theory (enable aot-jn))))

(defthm aot-code-id (implies (and (natp v) (<= v 6)) (equal (aot-code v) v)) :hints (("Goal" :in-theory (enable aot-code))))
(defthm aot-code-p (and (natp (aot-code v)) (<= (aot-code v) 6)) :hints (("Goal" :in-theory (enable aot-code)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (aot-code v)) :hints (("Goal" :in-theory (enable aot-code))))
                 (:linear :corollary (<= (aot-code v) 6) :hints (("Goal" :in-theory (enable aot-code))))))
(defthm aot-jn-p (implies (and (natp a) (<= a 6) (natp b) (<= b 6)) (and (natp (aot-jn a b)) (<= (aot-jn a b) 6)))
  :hints (("Goal" :in-theory (enable aot-jn))))
(defthm tvg-p (and (natp (tvg s l)) (<= (tvg s l) 6)) :hints (("Goal" :in-theory (enable tvg)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (tvg s l)) :hints (("Goal" :in-theory (enable tvg))))
                 (:linear :corollary (<= (tvg s l) 6) :hints (("Goal" :in-theory (enable tvg))))))
(defthm rcg-p (and (natp (rcg s l)) (<= (rcg s l) 6)) :hints (("Goal" :in-theory (enable rcg)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (rcg s l)) :hints (("Goal" :in-theory (enable rcg))))
                 (:linear :corollary (<= (rcg s l) 6) :hints (("Goal" :in-theory (enable rcg))))))
(defthm tvg-update
  (implies (and (natp s2) (< s2 (len l))) (equal (tvg s (update-nth s2 v l)) (if (equal s s2) (aot-code v) (tvg s l))))
  :hints (("Goal" :in-theory (enable tvg nth update-nth))))
(defthm rcg-update
  (implies (and (natp s2) (< s2 (len l))) (equal (rcg s (update-nth s2 v l)) (if (equal s s2) (aot-code v) (rcg s l))))
  :hints (("Goal" :in-theory (enable rcg nth update-nth))))
(defthm len-update-nth-in (implies (and (natp s) (< s (len l))) (equal (len (update-nth s v l)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm aot-rjn-grows (aot-le (rcg s (nth 1 aots)) (rcg s (nth 1 (aot-rjn s2 v aots))))
  :hints (("Goal" :in-theory (enable aot-rjn-rc aot-jn))))

(in-theory (disable aot-le))

; ---- AN OK WALK ONLY GROWS THE CURRENT LOOP'S RECUR TYPES -------------------------------------

; rc-le r1 r2 n: below n, every slot's recur type in r1 is below r2's
(defun rc-le (r1 r2 n)
  (if (zp n) t (and (aot-le (rcg (- n 1) r1) (rcg (- n 1) r2)) (rc-le r1 r2 (- n 1)))))
(defthm rc-le-refl (rc-le r r n))
(defthm rc-le-trans (implies (and (rc-le a b n) (rc-le b c n)) (rc-le a c n)))
(defthm rc-le-shrink (implies (and (rc-le a b n2) (<= n n2) (natp n) (natp n2)) (rc-le a b n)))
(defthm rc-le-point (implies (and (rc-le a b n) (natp n) (natp s) (< s n)) (aot-le (rcg s a) (rcg s b))))
(defthm rc-le-rjn (rc-le (nth 1 x) (nth 1 (aot-rjn s v x)) n))
(defthm rc-le-rzero (implies (and (natp b) (natp n) (<= n b)) (rc-le (nth 1 x) (nth 1 (aot-rzero b i m x)) n)))
(defthm aot-and-1 (equal (equal (aot-and a b) 1) (and (equal a 1) (equal b 1))) :hints (("Goal" :in-theory (enable aot-and))))
(defthm rc-le-rjn2 (implies (rc-le r (nth 1 x) n) (rc-le r (nth 1 (aot-rjn s v x)) n))
  :hints (("Goal" :use ((:instance rc-le-trans (a r) (b (nth 1 x)) (c (nth 1 (aot-rjn s v x))))))))
(defthm rc-le-rzero2 (implies (and (rc-le r (nth 1 x) n) (natp b) (natp n) (<= n b)) (rc-le r (nth 1 (aot-rzero b i m x)) n))
  :hints (("Goal" :use ((:instance rc-le-trans (a r) (b (nth 1 x)) (c (nth 1 (aot-rzero b i m x))))))))
(in-theory (disable rc-le))

; every r below the walk's rc where it starts is below it where it ends (n at most the loop's top)
(defthm aot-ty-rc-le
  (implies (and (equal (mv-nth 1 (aot-ty fl e j m k aots)) 1) (natp (nth 3 aots)) (natp (nth 4 aots))
                (natp n) (<= n (+ (nth 3 aots) (nth 4 aots))) (rc-le r (nth 1 aots) n))
           (rc-le r (nth 1 (mv-nth 2 (aot-ty fl e j m k aots))) n))
  :hints (("Goal" :induct (aot-ty fl e j m k aots) :in-theory (enable aot-ty-cases))))

(defthm aot-ty-rc-grows
  (implies (and (equal (mv-nth 1 (aot-ty fl e j m k aots)) 1)
                (natp (nth 3 aots)) (natp (nth 4 aots)) (natp s) (< s (+ (nth 3 aots) (nth 4 aots))))
           (aot-le (rcg s (nth 1 aots)) (rcg s (nth 1 (mv-nth 2 (aot-ty fl e j m k aots))))))
  :hints (("Goal" :use ((:instance aot-ty-rc-le (r (nth 1 aots)) (n (+ (nth 3 aots) (nth 4 aots))))
                        (:instance rc-le-point (a (nth 1 aots)) (b (nth 1 (mv-nth 2 (aot-ty fl e j m k aots)))) (n (+ (nth 3 aots) (nth 4 aots)))))
           :in-theory (disable aot-ty-rc-le rc-le-point))))

; ---- A LOOP'S ROUNDS: THE ENV ITS FINAL ROUND TYPES THE BODY IN ------------------------------

(defun-nx aot-star (fl e j m k aots)
  (declare (xargs :measure (aot-meas fl e j m k)))
  (let ((aots (aot-tick aots)))
    (cond ((not (aot-go e j m k)) aots)
          ((equal fl 5)
           (let ((s1 (mv-nth 2 (aot-ty 0 (aot-kid e m) 0 0 0 aots))))
             (cond ((aot-settled (aot-s2 e) 0 m s1) aots)
                   ((< 4 k) (aot-star 8 e 0 m k s1))
                   (t (aot-star 7 e 0 m k s1)))))
          ((equal fl 7)
           (if (< j m)
               (let ((s (+ (aot-s2 e) j)))
                 (aot-star 7 e (+ 1 j) m k (aot-put s (aot-jn (aot-get s aots) (aot-rget s aots)) aots)))
             (if (< k 5) (aot-star 5 e 0 m (+ 1 k) aots) aots)))
          ((equal fl 8)
           (if (< j m) (aot-star 8 e (+ 1 j) m k (aot-put (+ (aot-s2 e) j) 1 aots)) aots))
          (t aots))))

(defthm aot-star-ty
  (implies (and (member fl '(5 7 8)) (implies (equal fl 7) (< k 5)) (aot-go e j m k))
           (let ((w (aot-ty 0 (aot-kid e m) 0 0 0 (aot-star fl e j m k aots))))
             (and (equal (mv-nth 0 (aot-ty fl e j m k aots)) (mv-nth 0 w))
                  (implies (equal (mv-nth 1 (aot-ty fl e j m k aots)) 1) (equal (mv-nth 1 w) 1)))))
  :hints (("Goal" :induct (aot-star fl e j m k aots) :in-theory (enable aot-ty-cases aot-and))))

(defun aot-allany (l b i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n)) (and (equal (tvg (+ b i) l) 1) (aot-allany l b (+ 1 i) n)) t))

(defthm aot-allany-settled
  (implies (and (aot-allany (nth 0 x) b i n) (natp b)) (aot-settled b i n x))
  :hints (("Goal" :induct (aot-allany (nth 0 x) b i n) :in-theory (enable aot-settled aot-jn))))
(defthm aot-allany-update-above
  (implies (and (natp i) (natp n) (natp b) (<= (+ b n) s) (natp s) (< s (len l)))
           (equal (aot-allany (update-nth s v l) b i n) (aot-allany l b i n))))
(defthm aot-allany-shrink (implies (and (aot-allany l b i n2) (natp n) (natp n2) (<= n n2)) (aot-allany l b i n)))
(defthm aot-allany-extend
  (implies (and (aot-allany l b i n) (natp i) (natp n) (<= i n) (equal (tvg (+ b n) l) 1))
           (aot-allany l b i (+ 1 n))))
(defthm tvg-out (implies (not (and (natp s) (< s (len l)))) (equal (tvg s l) 1)) :hints (("Goal" :in-theory (enable tvg))))

(defthm aot-star-settled
  (implies (and (member fl '(5 7 8)) (implies (equal fl 7) (< k 5)) (aot-go e j m k)
                (implies (equal fl 8) (aot-allany (nth 0 aots) (aot-s2 e) 0 j)))
           (aot-settled (aot-s2 e) 0 m (mv-nth 2 (aot-ty 0 (aot-kid e m) 0 0 0 (aot-star fl e j m k aots)))))
  :hints (("Goal" :induct (aot-star fl e j m k aots) :in-theory (enable aot-ty-cases aot-put-tv))))

(defthm aot-star-env
  (and (aot-le (tvg s (nth 0 aots)) (tvg s (nth 0 (aot-star fl e j m k aots))))
       (implies (not (and (natp s) (<= (aot-s2 e) s) (< s (+ (aot-s2 e) m))))
                (equal (tvg s (nth 0 (aot-star fl e j m k aots))) (tvg s (nth 0 aots))))
       (equal (nth 3 (aot-star fl e j m k aots)) (nth 3 aots))
       (equal (nth 4 (aot-star fl e j m k aots)) (nth 4 aots)))
  :hints (("Goal" :induct (aot-star fl e j m k aots) :in-theory (enable aot-put-tv))))

(in-theory (disable aot-star))

; ---- THE READS: aot-ty's and ex-ev's of the same fields, within 40 bits ------------------------

(defthm anp-nth-is-nth (implies (natp i) (equal (anp-nth i l) (nth i l))) :hints (("Goal" :in-theory (enable anp-nth nth))))
(defthm anp-len-is-len (equal (anp-len l) (len l)))
(defthm aot-nth-past (implies (and (natp j) (<= (len l) j)) (equal (nth j l) nil)) :hints (("Goal" :in-theory (enable nth))))
(defthm aot-reads-ex
  (and (implies (and (natp (ex-kind e)) (< (ex-kind e) *anp40*)) (equal (aot-k e) (ex-kind e)))
       (implies (< (ex-i2 e) *anp40*) (equal (aot-i2 e) (ex-i2 e)))
       (implies (< (ex-nk e) *anp40*) (equal (aot-nk e) (ex-nk e)))
       (implies (and (natp j) (< (ex-nk e) *anp40*)) (equal (aot-kid e j) (ex-kid-of e j)))
       (implies (< (ex-s2 e) *anp40*) (equal (aot-s2 e) (ex-s2 e)))
       (implies (< (ex-rstart e) *anp40*) (equal (aot-rs e) (ex-rstart e)))
       (implies (< (ex-rn e) *anp40*) (equal (aot-rn e) (ex-rn e))))
  :hints (("Goal" :in-theory (enable aot-k aot-i2 aot-nk aot-kid aot-s2 aot-rs aot-rn aot-n40 anp-sat nth))))
(defthm aot-kid-neg (implies (not (natp j)) (equal (aot-kid e j) nil)) :hints (("Goal" :in-theory (enable aot-kid))))
(defthm aot-k-nil (equal (aot-k nil) 0) :hints (("Goal" :in-theory (enable aot-k))))
(defthm ex-kid-of-count (implies (consp e) (< (acl2-count (ex-kid-of e j)) (acl2-count e))) :rule-classes :linear
  :hints (("Goal" :use ex-kid-count)))
(in-theory (disable ex-kind ex-i2 ex-kids ex-c ex-s2 ex-mark ex-rstart ex-rn ex-nk ex-kid-of))

; ---- A VALUE FITS A TYPE; A FRAME FITS AN ENV -------------------------------------------------

(defun aot-fits (v ty) (cond ((equal ty 0) nil) ((equal ty 1) t) (t (equal (aot-tag v) ty))))
(defthm aot-fits-le (implies (and (aot-fits v a) (aot-le a b)) (aot-fits v b)) :hints (("Goal" :in-theory (enable aot-le aot-jn))))
(defthm aot-fits-jn (implies (aot-fits v a) (and (aot-fits v (aot-jn a b)) (aot-fits v (aot-jn b a))))
  :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-fits-1 (aot-fits v 1))
(defthm aot-fits-0 (not (aot-fits v 0)))
(in-theory (disable aot-fits))

; a slot's type: the env's, or for a recur's frame the current loop's slot what its recurs carried
(defun aot-slt (s l r cb cn rec) (if (and rec (natp s) (<= cb s) (< s (+ cb cn)) (< s (len l))) (rcg s r) (tvg s l)))
; slots i..n-1 of fr fit, but lo..hi-1
(defun aot-ffr (fr l r cb cn rec lo hi i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (and (or (and (<= lo i) (< i hi)) (aot-fits (nth i fr) (aot-slt i l r cb cn rec)))
           (aot-ffr fr l r cb cn rec lo hi (+ 1 i) n))
    t))

(defthm aot-ffr-point
  (implies (and (aot-ffr fr l r cb cn rec lo hi i n) (natp n) (natp s) (natp i) (<= i s) (< s n) (not (and (<= lo s) (< s hi))))
           (aot-fits (nth s fr) (aot-slt s l r cb cn rec)))
  :hints (("Goal" :induct (aot-ffr fr l r cb cn rec lo hi i n))))
(defthm aot-ffr-bind
  (implies (and (aot-ffr fr l nil 0 0 nil lo hi i n) (aot-fits v (aot-code t0)) (natp s) (< s (len l)))
           (aot-ffr (update-nth s v fr) (update-nth s t0 l) nil 0 0 nil lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr l nil 0 0 nil lo hi i n) :expand ((aot-ffr (update-nth s v fr) (update-nth s t0 l) nil 0 0 nil lo hi i n)) :in-theory (enable nth-update-nth))))
(defthm aot-ffr-bind-out
  (implies (and (aot-ffr fr l r cb cn rec lo hi i n) (natp s) (<= n s))
           (aot-ffr (update-nth s v fr) l r cb cn rec lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr l r cb cn rec lo hi i n) :expand ((aot-ffr (update-nth s v fr) l r cb cn rec lo hi i n)))))
(defthm aot-ffr-unbind
  (implies (and (aot-ffr fr (update-nth s x l) r cb cn rec lo hi i n) (equal (tvg s l) 1) (natp s) (< s (len l)))
           (aot-ffr fr l r cb cn rec lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr (update-nth s x l) r cb cn rec lo hi i n) :expand ((aot-ffr fr l r cb cn rec lo hi i n)))))
(defthm aot-ffr-grows
  (implies (and (equal (mv-nth 1 (aot-ty fl e j m k st)) 1) (natp (nth 3 st)) (natp (nth 4 st))
                (aot-ffr fr l (nth 1 st) (nth 3 st) (nth 4 st) t lo hi i n))
           (aot-ffr fr l (nth 1 (mv-nth 2 (aot-ty fl e j m k st))) (nth 3 st) (nth 4 st) t lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr l (nth 1 st) (nth 3 st) (nth 4 st) t lo hi i n) :expand ((aot-ffr fr l (nth 1 (mv-nth 2 (aot-ty fl e j m k st))) (nth 3 st) (nth 4 st) t lo hi i n)))))
(defthm aot-ffr-rjn
  (implies (aot-ffr fr l (nth 1 st) cb cn t lo hi i n) (aot-ffr fr l (nth 1 (aot-rjn s2 v st)) cb cn t lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr l (nth 1 st) cb cn t lo hi i n) :expand ((aot-ffr fr l (nth 1 (aot-rjn s2 v st)) cb cn t lo hi i n)))))
(defthm aot-settled-point
  (implies (and (aot-settled b i0 m x) (natp b) (natp i0) (natp m) (natp s) (<= (+ b i0) s) (< s (+ b m)))
           (aot-le (rcg s (nth 1 x)) (tvg s (nth 0 x))))
  :hints (("Goal" :induct (aot-settled b i0 m x) :in-theory (enable aot-settled aot-le))))
(defthm aot-ffr-settle
  (implies (and (aot-ffr fr (nth 0 x) (nth 1 x) (nth 3 x) (nth 4 x) t lo hi i n) (aot-settled (nth 3 x) 0 (nth 4 x) x)
                (natp (nth 3 x)) (natp (nth 4 x)))
           (aot-ffr fr (nth 0 x) nil 0 0 nil lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr (nth 0 x) (nth 1 x) (nth 3 x) (nth 4 x) t lo hi i n) :expand ((aot-ffr fr (nth 0 x) nil 0 0 nil lo hi i n)))
          ("Subgoal *1/2" :use ((:instance aot-settled-point (b (nth 3 x)) (i0 0) (m (nth 4 x)) (s i))))))
(defthm aot-ffr-widen
  (implies (aot-ffr fr (nth 0 st) nil 0 0 nil lo hi i n) (aot-ffr fr (nth 0 (aot-star fl e j m k st)) nil 0 0 nil lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr (nth 0 st) nil 0 0 nil lo hi i n) :expand ((aot-ffr fr (nth 0 (aot-star fl e j m k st)) nil 0 0 nil lo hi i n)))))
(defthm aot-ffr-narrow
  (implies (and (aot-ffr fr (nth 0 (aot-star fl e j m k st)) nil 0 0 nil 0 0 i n) (< (ex-s2 e) *anp40*))
           (aot-ffr fr (nth 0 st) nil 0 0 nil (ex-s2 e) (+ (ex-s2 e) m) i n))
  :hints (("Goal" :induct (aot-ffr fr (nth 0 st) nil 0 0 nil (ex-s2 e) (+ (ex-s2 e) m) i n) :expand ((aot-ffr fr (nth 0 (aot-star fl e j m k st)) nil 0 0 nil 0 0 i n)))
          ("Subgoal *1/2" :use ((:instance aot-star-env (s i))))))

(defthm aot-ffr-point0
  (implies (and (aot-ffr fr l nil 0 0 nil 0 0 0 (len l)) (natp s))
           (aot-fits (nth s fr) (tvg s l)))
  :hints (("Goal" :cases ((< s (len l))) :use ((:instance aot-ffr-point (r nil) (cb 0) (cn 0) (rec nil) (lo 0) (hi 0) (i 0) (n (len l)))))))
(defthm aot-ffr-lohi
  (implies (aot-ffr fr l r cb cn rec 0 0 i n) (aot-ffr fr l r cb cn rec lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr l r cb cn rec 0 0 i n) :expand ((aot-ffr fr l r cb cn rec lo hi i n)))))


; ---- THE COST: THE NODES VISITED --------------------------------------------------------------
; aot-wt: aot-ty's walk with every state-dependent choice taken at its dearest -- a loop's rounds
; all six and the boxed one (7 walks of its body), an array cast's operand walked a second time
; (else the nil child, one visit) -- given the current loop (cb cn) a recur's count reads.
; So 7^d walks of a node under d nested loops, as compiler.cljf's loop-env.

(defun aot-wt (fl e j m k cb cn)
  (declare (xargs :measure (aot-meas fl e j m k) :ruler-extenders :all))
  (+ 1
     (cond ((not (aot-go e j m k)) 0)
           ((equal fl 0)
            (let ((kd (aot-k e)))
              (cond ((equal kd 5) (if (equal (aot-nk e) 0) 0 (aot-wt 1 e 0 (aot-nk e) 0 cb cn)))
                    ((equal kd 4) (+ (aot-wt 0 (aot-kid e 0) 0 0 0 cb cn) (aot-wt 0 (aot-kid e 1) 0 0 0 cb cn)
                                     (aot-wt 0 (aot-kid e 2) 0 0 0 cb cn)))
                    ((equal kd 11) (aot-wt 2 e 0 (aot-i2 e) 0 cb cn))
                    ((equal kd 12) (aot-wt 6 e 0 (aot-i2 e) 0 cb cn))
                    ((equal kd 16) (aot-wt 3 e 0 (if (and (equal (aot-rs e) cb) (anp40p cn) (< (aot-nk e) cn)) cn (aot-nk e)) 0 cb cn))
                    ((equal kd 6) (+ (aot-wt 0 (aot-kid e 0) 0 0 0 cb cn) (aot-wt 4 e 1 (aot-nk e) 0 cb cn)))
                    (t 0))))
           ((equal fl 1) (if (< j m) (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (if (< (+ 1 j) m) (aot-wt 1 e (+ 1 j) m 0 cb cn) 0)) 0))
           ((or (equal fl 2) (equal fl 6))
            (if (< j m)
                (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (aot-wt fl e (+ 1 j) m 0 cb cn))
              (if (equal fl 2) (aot-wt 0 (aot-kid e m) 0 0 0 cb cn) (aot-wt 5 e 0 m 0 (aot-s2 e) m))))
           ((equal fl 5) (+ (aot-wt 0 (aot-kid e m) 0 0 0 cb cn) (max (aot-wt 8 e 0 m k cb cn) (aot-wt 7 e 0 m k cb cn))))
           ((equal fl 7) (if (< j m) (aot-wt 7 e (+ 1 j) m k cb cn) (if (< k 5) (aot-wt 5 e 0 m (+ 1 k) cb cn) 0)))
           ((equal fl 8) (if (< j m) (aot-wt 8 e (+ 1 j) m k cb cn) (aot-wt 0 (aot-kid e m) 0 0 0 cb cn)))
           ((equal fl 3) (if (< j m) (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (aot-wt 3 e (+ 1 j) m 0 cb cn)) 0))
           ((equal fl 4) (if (< j m)
                             (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (aot-wt 0 (aot-kid (aot-kid e j) 1) 0 0 0 cb cn)
                                (aot-wt 4 e (+ 1 j) m 0 cb cn))
                           0))
           (t 0))))

(defthm aot-wt-posp (posp (aot-wt fl e j m k cb cn)) :rule-classes :type-prescription)
(defthm aot-wt-open
  (implies (syntaxp (and (variablep e) (or (variablep j) (and (quotep j) (member-equal (unquote j) '(1 2 3))))))
           (equal (aot-wt fl e j m k cb cn)
                  (+ 1
     (cond ((not (aot-go e j m k)) 0)
           ((equal fl 0)
            (let ((kd (aot-k e)))
              (cond ((equal kd 5) (if (equal (aot-nk e) 0) 0 (aot-wt 1 e 0 (aot-nk e) 0 cb cn)))
                    ((equal kd 4) (+ (aot-wt 0 (aot-kid e 0) 0 0 0 cb cn) (aot-wt 0 (aot-kid e 1) 0 0 0 cb cn)
                                     (aot-wt 0 (aot-kid e 2) 0 0 0 cb cn)))
                    ((equal kd 11) (aot-wt 2 e 0 (aot-i2 e) 0 cb cn))
                    ((equal kd 12) (aot-wt 6 e 0 (aot-i2 e) 0 cb cn))
                    ((equal kd 16) (aot-wt 3 e 0 (if (and (equal (aot-rs e) cb) (anp40p cn) (< (aot-nk e) cn)) cn (aot-nk e)) 0 cb cn))
                    ((equal kd 6) (+ (aot-wt 0 (aot-kid e 0) 0 0 0 cb cn) (aot-wt 4 e 1 (aot-nk e) 0 cb cn)))
                    (t 0))))
           ((equal fl 1) (if (< j m) (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (if (< (+ 1 j) m) (aot-wt 1 e (+ 1 j) m 0 cb cn) 0)) 0))
           ((or (equal fl 2) (equal fl 6))
            (if (< j m)
                (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (aot-wt fl e (+ 1 j) m 0 cb cn))
              (if (equal fl 2) (aot-wt 0 (aot-kid e m) 0 0 0 cb cn) (aot-wt 5 e 0 m 0 (aot-s2 e) m))))
           ((equal fl 5) (+ (aot-wt 0 (aot-kid e m) 0 0 0 cb cn) (max (aot-wt 8 e 0 m k cb cn) (aot-wt 7 e 0 m k cb cn))))
           ((equal fl 7) (if (< j m) (aot-wt 7 e (+ 1 j) m k cb cn) (if (< k 5) (aot-wt 5 e 0 m (+ 1 k) cb cn) 0)))
           ((equal fl 8) (if (< j m) (aot-wt 8 e (+ 1 j) m k cb cn) (aot-wt 0 (aot-kid e m) 0 0 0 cb cn)))
           ((equal fl 3) (if (< j m) (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (aot-wt 3 e (+ 1 j) m 0 cb cn)) 0))
           ((equal fl 4) (if (< j m)
                             (+ (aot-wt 0 (aot-kid e j) 0 0 0 cb cn) (aot-wt 0 (aot-kid (aot-kid e j) 1) 0 0 0 cb cn)
                                (aot-wt 4 e (+ 1 j) m 0 cb cn))
                           0))
           (t 0)))))
  :hints (("Goal" :expand ((aot-wt fl e j m k cb cn)))))
(in-theory (disable aot-wt))

(defthm aot-ty-cost
  (implies (natp (nth 9 aots))
           (and (natp (nth 9 (mv-nth 2 (aot-ty fl e j m k aots))))
                (<= (nth 9 (mv-nth 2 (aot-ty fl e j m k aots)))
                    (+ (nth 9 aots) (aot-wt fl e j m k (nth 3 aots) (nth 4 aots))))))
  :hints (("Goal" :induct (aot-ty fl e j m k aots) :in-theory (enable aot-ty-cases aot-tick-ns) :do-not (quote (generalize eliminate-destructors fertilize)) :do-not-induct t)))

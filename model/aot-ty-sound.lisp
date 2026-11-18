; THE TYPE INFERENCE IS SOUND (model/aot.lisp aot-ty, slice 2 of model/aot-PLAN.md), against
; exec.lisp's ex-ev: aot-ty-sound, (aot-cl flg e i tmp fr fuel s) at every ex-ev place, and its
; headline aot-ty-sound-m (a node's value fits the type aot-ty gives it).
;
; The induction is aot-ind, ex-ev's recursion with the state aot-ty walks each part in. Each
; ex-ev case is its own lemma (aot-cl-*), its induction hypotheses as aot-ind writes them, so the
; theorem itself only picks the case. The hypotheses (aot-hyp, aot-node-ok) are stated exactly
; in aot-PLAN.md slice 2: the typed subset and its 40-bit fields, no clearing marks, ex-wf's shape
; of an if and a let, A-CONST (aot-tag of a constant), A-HEAD (the op a call head reads as),
; A-OP (aot-opok: the ops answer aot-optab's type), ok = 1, the frame fitting the env.

(in-package "ACL2")
(set-prover-step-limit 30000000)   ; a runaway case fails in a minute, not at CERT_SECS
(include-book "aot-ty-proof")

; ---- A RECUR'S ARGUMENTS AND ITS WRITE ---------------------------------------------------------

; tmp's values fit what the recurs carried at slots b, b+1, ... (a slot past the env: any)
(defun aot-rfit (tmp l r b)
  (if (consp tmp)
      (and (aot-fits (car tmp) (if (and (natp b) (< b (len l))) (rcg b r) 1)) (aot-rfit (cdr tmp) l r (+ 1 (nfix b))))
    t))
(defthm aot-rfit-append
  (implies (and (natp b) (aot-rfit tmp l r b) (aot-fits v (if (< (+ b (len tmp)) (len l)) (rcg (+ b (len tmp)) r) 1)))
           (aot-rfit (append tmp (list v)) l r b))
  :hints (("Goal" :induct (aot-rfit tmp l r b) :do-not (quote (generalize eliminate-destructors fertilize)) :do-not-induct t :in-theory (disable aot-fits-le))))
(defun aot-rp-ind (tmp b x) (if (and (consp tmp) (not (zp x))) (aot-rp-ind (cdr tmp) (+ 1 b) (- x 1)) (list tmp b x)))
(defthm aot-rfit-point
  (implies (and (aot-rfit tmp l r b) (natp b) (natp x) (< x (len tmp)))
           (aot-fits (nth x tmp) (if (< (+ b x) (len l)) (rcg (+ b x) r) 1)))
  :hints (("Goal" :induct (aot-rp-ind tmp b x) :in-theory (enable nth) :do-not (quote (generalize eliminate-destructors fertilize)))))
(defthm aot-rfit-grows
  (implies (and (equal (mv-nth 1 (aot-ty fl e j m k st)) 1) (natp (nth 3 st)) (natp (nth 4 st)) (natp b)
                (<= (nth 3 st) b) (<= (+ b (len tmp)) (+ (nth 3 st) (nth 4 st))) (aot-rfit tmp l (nth 1 st) b))
           (aot-rfit tmp l (nth 1 (mv-nth 2 (aot-ty fl e j m k st))) b))
  :hints (("Goal" :induct (aot-rfit tmp l (nth 1 st) b))))
(defthm aot-rfit-rjn
  (implies (and (aot-rfit tmp l (nth 1 st) b) (natp b)) (aot-rfit tmp l (nth 1 (aot-rjn s2 v st)) b))
  :hints (("Goal" :induct (aot-rfit tmp l (nth 1 st) b))))
(defthm aot-rjn-here
  (implies (and (natp s) (< s (len (nth 1 st))) (aot-fits v t0) (natp t0) (<= t0 6))
           (aot-fits v (rcg s (nth 1 (aot-rjn s t0 st)))))
  :hints (("Goal" :in-theory (enable aot-rjn-rc))))

(defthm ex-write-nth
  (implies (and (natp b) (natp s))
           (equal (nth s (ex-write b vals fr))
                  (if (and (<= b s) (< s (+ b (len vals)))) (nth (- s b) vals) (nth s fr))))
  :hints (("Goal" :induct (ex-write b vals fr) :in-theory (enable nth-update-nth nth))))
(defthm aot-rfit-at
  (implies (and (aot-rfit tmp l r b) (natp b) (natp s) (<= b s) (< s (+ b (len tmp))) (< s (len l)))
           (aot-fits (nth (+ (- b) s) tmp) (rcg s r)))
  :hints (("Goal" :use ((:instance aot-rfit-point (x (- s b)))) :in-theory (disable aot-rfit-point))))
(defthm aot-ffr-write
  (implies (and (aot-ffr fr l nil 0 0 nil 0 0 i n) (aot-rfit tmp l r b) (natp b))
           (aot-ffr (ex-write b tmp fr) l r b (len tmp) t 0 0 i n))
  :hints (("Goal" :induct (aot-ffr fr l nil 0 0 nil 0 0 i n) :expand ((aot-ffr (ex-write b tmp fr) l r b (len tmp) t 0 0 i n)))))
(defthm aot-take-len (implies (true-listp x) (equal (take (len x) x) x)))

; ---- THE SMALL FACTS THE CASES ASK ------------------------------------------------------------

(defthm aot-jn-any (equal (aot-jn a 1) 1) :hints (("Goal" :in-theory (enable aot-jn))))
(defthm aot-optab-0 (implies (not (member k '(1 2 3 4 5 6 7 8 9 10 11 12 13))) (equal (aot-optab k n a b c) 1))
  :hints (("Goal" :in-theory (enable aot-optab))))
(defthm aot-nth-append1
  (implies (natp n)
           (equal (nth n (append tmp (list v))) (if (< n (len tmp)) (nth n tmp) (if (equal n (len tmp)) v nil))))
  :hints (("Goal" :in-theory (enable nth))))

(defun aot-iter-ind (e i tmp fr fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) (list e i tmp fr) (aot-iter-ind e 0 nil (cadr (ex-ev :m e 0 nil fr fuel)) (1- fuel))))
(defthm ex-ev-iter-norec
  (not (equal (car (car (ex-ev :iter e i tmp fr fuel))) :recur))
  :hints (("Goal" :induct (aot-iter-ind e i tmp fr fuel) :expand ((ex-ev :iter e i tmp fr fuel)))))
(defthm ex-ev-call-end
  (implies (and (natp i) (<= (ex-nk e) i))
           (and (equal (cadr (ex-ev :call e i tmp fr fuel)) fr)
                (not (equal (car (car (ex-ev :call e i tmp fr fuel))) :recur))))
  :hints (("Goal" :expand ((ex-ev :call e i tmp fr fuel)) :in-theory (disable ex-enters ex-callee ex-arerr ex-apway ex-fbody ex-bind))))

(in-theory (enable aot-put-tv aot-raw-nth))
(in-theory (disable ex-ev aot-slt))

; ---- THE TYPED SUBSET AND WHAT IT ASSUMES OF THE HOST --------------------------------------------

; an array cast as a call's first operand (aot-ty's cast at j = 1), and its type
(defun aot-castp (e)
  (let ((h (aot-hop e)) (a (ex-kid-of e 1)))
    (and (or (equal h 7) (equal h 8) (equal h 9)) (equal (aot-k a) 6) (equal (aot-hop a) 20)
         (not (equal (aot-kw (aot-kid a 2)) 0)))))
(defun aot-castkw (e) (aot-kw (aot-kid (ex-kid-of e 1) 2)))

; A-OP: the call answers a value of aot-optab's type for operands fitting the types (the first
; through an array cast: the cast's type)
(defun-sk aot-opok (e)
  (forall (tmp fr fuel ta tb tc)
    (implies (and (equal (len tmp) (ex-nk e)) (equal (aot-opof (car tmp)) (aot-hop e))
                  (or (and (aot-castp e) (equal ta (aot-castkw e))) (aot-fits (nth 1 tmp) ta))
                  (aot-fits (nth 2 tmp) tb) (aot-fits (nth 3 tmp) tc)
                  (valp (car (ex-ev :call e (ex-nk e) tmp fr fuel))))
             (aot-fits (val (car (ex-ev :call e (ex-nk e) tmp fr fuel))) (aot-optab (aot-hop e) (- (ex-nk e) 1) ta tb tc)))))

(defun aot-node-ok (e)
  (let ((k (ex-kind e)))
    (and (consp e) (natp k) (member k '(1 2 3 4 5 6 11 12 14 16))
         (< (ex-i2 e) *anp40*) (< (ex-nk e) *anp40*) (< (ex-s2 e) *anp40*) (< (ex-rstart e) *anp40*) (< (ex-rn e) *anp40*)
         (not (ex-mark e))
         (implies (equal k 4) (or (equal (ex-nk e) 2) (equal (ex-nk e) 3)))                ; ex-wf shape of an if
         (implies (or (equal k 11) (equal k 12)) (equal (ex-nk e) (+ 1 (ex-i2 e))))       ; and of a let or loop
         (implies (equal k 1) (aot-fits (ex-c e) (aot-cty e)))                       ; A-CONST
         (implies (equal k 6) (and (< 0 (ex-nk e)) (aot-opok e)                       ; A-OP
                                   (or (equal (aot-hop e) 0)                          ; A-HEAD
                                       (and (or (equal (ex-kind (ex-kid-of e 0)) 1) (equal (ex-kind (ex-kid-of e 0)) 3))
                                            (equal (aot-opof (ex-c (ex-kid-of e 0))) (aot-hop e)))))))))

(defthm aot-node-ok-consp (implies (aot-node-ok e) (consp e)) :rule-classes :forward-chaining)
(in-theory (disable aot-node-ok))
(defun aot-sub (fl e j)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (if (equal fl 0) 2 1) (nfix (- (ex-nk e) (nfix j)))))
                  :well-founded-relation o<))
  (if (equal fl 0)
      (and (aot-node-ok e) (aot-sub 1 e 0))
    (if (and (consp e) (natp j) (< j (ex-nk e))) (and (aot-sub 0 (ex-kid-of e j) 0) (aot-sub 1 e (+ 1 j))) t)))

(defun aot-subs-ind (e i)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (natp i) (< i (ex-nk e))) (aot-subs-ind e (+ 1 i)) (list e i)))
(defthm aot-sub-kid
  (implies (and (aot-sub 1 e i) (natp i) (natp j) (<= i j) (< j (ex-nk e)) (consp e)) (aot-sub 0 (ex-kid-of e j) 0))
  :hints (("Goal" :induct (aot-subs-ind e i) :in-theory (disable aot-sub) :expand ((aot-sub 1 e i)))))
(defthm aot-sub-0 (equal (aot-sub 0 e j) (and (aot-node-ok e) (aot-sub 1 e 0))) :hints (("Goal" :in-theory (disable aot-sub) :expand ((aot-sub 0 e j)))))
(defthm aot-sub-kids
  (implies (and (aot-sub 0 e 0) (natp j) (< j (ex-nk e))) (aot-sub 0 (ex-kid-of e j) 0))
  :hints (("Goal" :use ((:instance aot-sub-kid (i 0))) :in-theory (disable aot-sub-kid))))
(in-theory (disable aot-sub aot-sub-0))
(defthm aot-sub-node (implies (aot-sub 0 e j) (aot-node-ok e)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable aot-sub-0))))

(defun aot-cast (e i)
  (let ((a (ex-kid-of e i)) (h (aot-hop e)))
    (and (equal i 1) (or (equal h 7) (equal h 8) (equal h 9)) (equal (aot-k a) 6)
         (equal (aot-hop a) 20) (not (equal (aot-kw (aot-kid a 2)) 0)))))
(defun-nx aot-w2 (e i s)
  (aot-ty 0 (aot-kid (ex-kid-of e i) (if (aot-cast e i) 1 -1)) 0 0 0 (mv-nth 2 (aot-ty 0 (ex-kid-of e i) 0 0 0 (aot-tick s)))))
(defun-nx aot-s3 (e i s)
  (let* ((t0 (mv-nth 0 (aot-ty 0 (ex-kid-of e i) 0 0 0 (aot-tick s)))) (ti (mv-nth 0 (aot-w2 e i s))) (s2 (mv-nth 2 (aot-w2 e i s)))
         (d (and (aot-cast e i) (equal ti (aot-kw (aot-kid (ex-kid-of e i) 2))))))
    (cond ((equal i 1) (update-nth 8 (if d 1 0) (update-nth 5 (if d ti t0) s2)))
          ((equal i 2) (update-nth 6 t0 s2))
          ((equal i 3) (update-nth 7 t0 s2))
          (t s2))))
(in-theory (disable aot-cast aot-w2 aot-s3))

; ---- THE STATEMENT ----------------------------------------------------------------------------

(defun aot-isloop (flg e) (and (eq flg :let) (equal (ex-kind e) 12)))
(defun-nx aot-tyof (flg e i s)
  (case flg
    ((:m :iter) (aot-ty 0 e 0 0 0 s))
    (:do (aot-ty 1 e i (ex-nk e) 0 s))
    (:let (aot-ty (if (equal (ex-kind e) 12) 6 2) e i (ex-i2 e) 0 s))
    (:rec (aot-ty 3 e i (ex-nk e) 0 s))
    (otherwise (aot-ty 4 e i (ex-nk e) 0 s))))

; the operand registers: the operands so far fit them (the first may be an array cast: its keyword type)
(defun aot-regok (e tmp s)
  (and (or (and (equal (nth 8 s) 1) (aot-castp e) (equal (nth 5 s) (aot-castkw e))) (aot-fits (nth 1 tmp) (nth 5 s)))
       (aot-fits (nth 2 tmp) (nth 6 s)) (aot-fits (nth 3 tmp) (nth 7 s))))
(in-theory (disable aot-regok))

(defun-nx aot-hyp (flg e i tmp fr s)
  (and (aot-sub 0 e 0) (natp (nth 3 s)) (natp (nth 4 s)) (<= (len (nth 0 s)) (len (nth 1 s)))
       (equal (mv-nth 1 (aot-tyof flg e i s)) 1)
       (aot-ffr fr (nth 0 s) nil 0 0 nil 0 0 0 (len (nth 0 s)))
       (case flg
         (:do (and (natp i) (< i (ex-nk e))))
         (:let (and (natp i) (<= i (ex-i2 e)) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12))))
         (:rec (and (natp i) (<= i (ex-nk e)) (equal (ex-kind e) 16) (equal (ex-rstart e) (nth 3 s)) (equal (ex-nk e) (nth 4 s))
                    (equal (ex-rn e) (ex-nk e)) (equal (len tmp) i) (true-listp tmp)
                    (aot-rfit tmp (nth 0 s) (nth 1 s) (ex-rstart e))))
         (:call (and (natp i) (<= 1 i) (<= i (ex-nk e)) (equal (ex-kind e) 6) (equal (len tmp) i)
                     (implies (not (equal (aot-hop e) 0)) (equal (aot-opof (car tmp)) (aot-hop e)))
                     (aot-regok e tmp s)))
         (:iter (aot-settled (nth 3 s) 0 (nth 4 s) (mv-nth 2 (aot-ty 0 e 0 0 0 s))))
         (otherwise (eq flg :m)))))

(defun-nx aot-concl (flg e i tmp fr fuel s)
  (let* ((r (ex-ev flg e i tmp fr fuel)) (w (aot-tyof flg e i s)) (s2 (mv-nth 2 w))
         (ty (if (eq flg :call) (aot-optab (aot-hop e) (- (ex-nk e) 1) (nth 5 s2) (nth 6 s2) (nth 7 s2)) (mv-nth 0 w)))
         (lo (if (aot-isloop flg e) (ex-s2 e) 0)) (hi (if (aot-isloop flg e) (+ (ex-s2 e) (ex-i2 e)) 0)))
    (and (implies (valp (car r))
                  (and (aot-fits (val (car r)) ty) (aot-ffr (cadr r) (nth 0 s2) nil 0 0 nil lo hi 0 (len (nth 0 s2)))))
         (implies (equal (car (car r)) :recur)
                  (aot-ffr (cadr r) (nth 0 s2) (nth 1 s2) (nth 3 s2) (nth 4 s2) t lo hi 0 (len (nth 0 s2)))))))

(defun-nx aot-cl (flg e i tmp fr fuel s) (implies (aot-hyp flg e i tmp fr s) (aot-concl flg e i tmp fr fuel s)))

; the induction: ex-ev's recursion, each call with the state aot-ty walks it in
(defun-nx aot-ind (flg e i tmp fr fuel s)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)) (s0 (aot-tick s)))
    (case flg
      (:iter (if (not (consp e)) nil
               (let ((r (ex-ev :m e 0 nil fr fuel)))
                 (if (zp fuel) (aot-ind :m e 0 nil fr fuel s)
                   (list (aot-ind :m e 0 nil fr fuel s) (aot-ind :iter e 0 nil (cadr r) (1- fuel) s))))))
      (:do (cond ((not (consp e)) nil)
                 ((zp nk) nil)
                 ((< i (- nk 1))
                  (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (list (aot-ind :m (ex-kid-of e i) 0 nil fr fuel s0)
                          (aot-ind :do e (1+ i) tmp (cadr r) fuel (mv-nth 2 (aot-ty 0 (ex-kid-of e i) 0 0 0 s0))))))
                 (t (aot-ind :m (ex-kid-of e (- nk 1)) 0 nil fr fuel s0))))
      (:let (cond ((not (consp e)) nil)
                  ((< i n2)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)) (w (aot-ty 0 (ex-kid-of e i) 0 0 0 s0)))
                     (list (aot-ind :m (ex-kid-of e i) 0 nil fr fuel s0)
                           (aot-ind :let e (1+ i) tmp (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel
                                    (aot-put (+ (ex-s2 e) i) (mv-nth 0 w) (mv-nth 2 w))))))
                  ((equal k 12)
                   (aot-ind :iter (ex-kid-of e n2) 0 nil fr fuel
                            (aot-star 5 e 0 n2 0 (update-nth 4 n2 (update-nth 3 (ex-s2 e) (aot-rzero (ex-s2 e) 0 n2 s0))))))
                  (t (aot-ind :m (ex-kid-of e n2) 0 nil fr fuel s0))))
      (:rec (cond ((not (consp e)) nil)
                  ((< i nk)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)) (w (aot-ty 0 (ex-kid-of e i) 0 0 0 s0)))
                     (list (aot-ind :m (ex-kid-of e i) 0 nil fr fuel s0)
                           (aot-ind :rec e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel
                                    (aot-rjn (+ (ex-rstart e) i) (mv-nth 0 w) (mv-nth 2 w))))))
                  (t nil)))
      (:call (cond ((not (consp e)) nil)
                   ((< i nk)
                    (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (list (aot-ind :m (ex-kid-of e i) 0 nil fr fuel s0)
                            (aot-ind :call e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel (aot-s3 e i s)))))
                   (t nil)))
      ((:fin :coll) nil)
      (otherwise
       (cond ((not (consp e)) nil)
             ((equal k 4)
              (let* ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel))
                     (s1 (mv-nth 2 (aot-ty 0 (ex-kid-of e 0) 0 0 0 s0))) (s2 (mv-nth 2 (aot-ty 0 (ex-kid-of e 1) 0 0 0 s1))))
                (list (aot-ind :m (ex-kid-of e 0) 0 nil fr fuel s0) (aot-ind :m (ex-kid-of e 1) 0 nil (cadr r) fuel s1)
                      (aot-ind :m (ex-kid-of e 2) 0 nil (cadr r) fuel s2))))
             ((equal k 5) (aot-ind :do e 0 nil fr fuel s0))
             ((or (equal k 11) (equal k 12)) (aot-ind :let e 0 nil fr fuel s0))
             ((equal k 16) (aot-ind :rec e 0 nil fr fuel s0))
             ((equal k 6)
              (let* ((sa (update-nth 8 0 (update-nth 7 1 (update-nth 6 1 (update-nth 5 1 s0))))) (h (ex-kid-of e 0))
                     (sh (mv-nth 2 (aot-ty 0 h 0 0 0 sa))) (r (ex-ev :m h 0 nil fr fuel)))
                (if (ex-linked h)
                    (aot-ind :call e 1 (list (ex-c h)) fr fuel sh)
                  (list (aot-ind :m h 0 nil fr fuel sa) (aot-ind :call e 1 (list (val (car r))) (cadr r) fuel sh)))))
             (t nil))))))


; ---- THE CASES: one lemma per ex-ev case, its induction hypotheses as aot-ind writes them -------

(in-theory (disable aot-ffr))

(defthm aot-node-ok-fc
  (implies (aot-node-ok e)
           (and (consp e) (posp (ex-kind e)) (not (equal (ex-kind e) 0)) (not (equal (aot-k e) 0)) (< (ex-kind e) 17) (< (ex-i2 e) *anp40*) (< (ex-nk e) *anp40*)
                (< (ex-s2 e) *anp40*) (< (ex-rstart e) *anp40*) (< (ex-rn e) *anp40*) (not (ex-mark e))
                (member (ex-kind e) '(1 2 3 4 5 6 11 12 14 16))))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable aot-node-ok aot-k anp-nth aot-n40 nth ex-kind))))
(defthm aot-node-if-nk
  (implies (and (aot-node-ok e) (equal (ex-kind e) 4)) (and (<= 2 (ex-nk e)) (<= (ex-nk e) 3)))
  :rule-classes (:linear :forward-chaining) :hints (("Goal" :in-theory (enable aot-node-ok))))
(defthm aot-node-let-nk
  (implies (and (aot-node-ok e) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12))) (equal (ex-nk e) (+ 1 (ex-i2 e))))
  :hints (("Goal" :in-theory (enable aot-node-ok))))
(defthm aot-node-const (implies (and (aot-node-ok e) (equal (ex-kind e) 1)) (aot-fits (ex-c e) (aot-cty e)))
  :hints (("Goal" :in-theory (enable aot-node-ok))))
(defthm aot-node-call
  (implies (and (aot-node-ok e) (equal (ex-kind e) 6))
           (and (< 0 (ex-nk e)) (aot-opok e)
                (or (equal (aot-hop e) 0)
                    (and (or (equal (ex-kind (ex-kid-of e 0)) 1) (equal (ex-kind (ex-kid-of e 0)) 3))
                         (equal (aot-opof (ex-c (ex-kid-of e 0))) (aot-hop e))))))
  :rule-classes nil :hints (("Goal" :in-theory (enable aot-node-ok))))

(defthm aot-ffr-settle-ty
  (let ((x (mv-nth 2 (aot-ty fl e j m k s))))
    (implies (and (aot-ffr fr (nth 0 s) (nth 1 x) (nth 3 s) (nth 4 s) t lo hi i n) (aot-settled (nth 3 s) 0 (nth 4 s) x)
                  (natp (nth 3 s)) (natp (nth 4 s)))
             (aot-ffr fr (nth 0 s) nil 0 0 nil lo hi i n)))
  :hints (("Goal" :use ((:instance aot-ffr-settle (x (mv-nth 2 (aot-ty fl e j m k s))))) :in-theory (disable aot-ffr-settle))))

(defthm aot-cl-atom (implies (not (consp e)) (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (enable aot-cl aot-hyp))))

(defthm aot-cl-iter
  (implies (and (consp e)
                (aot-cl :m e 0 nil fr fuel s)
                (implies (not (zp fuel)) (aot-cl :iter e 0 nil (cadr (ex-ev :m e 0 nil fr fuel)) (1- fuel) s)))
           (aot-cl :iter e i tmp fr fuel s))
  :hints (("Goal" :in-theory (enable aot-cl aot-hyp aot-concl aot-tyof) :expand ((ex-ev :iter e i tmp fr fuel)))))

(defthm aot-cl-badkind
  (implies (not (member (ex-kind e) '(1 2 3 4 5 6 11 12 14 16))) (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (enable aot-cl aot-hyp aot-node-ok aot-sub-0))))
(defthm aot-cl-leaf
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (not (member (ex-kind e) '(4 5 6 11 12 16))))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :cases ((member (ex-kind e) '(1 2 3 14))) :in-theory (disable aot-cl))
          ("Subgoal 1" :in-theory (enable aot-cl aot-hyp aot-concl aot-tyof aot-ty-cases) :expand ((ex-ev :m e i tmp fr fuel)))))

(defthm ex-ev-atom (implies (not (consp e)) (equal (ex-ev flg e i tmp fr fuel) (list (list :out) fr 0)))
  :hints (("Goal" :expand ((ex-ev flg e i tmp fr fuel)))))
(defthm aot-kid-past (implies (and (natp j) (<= (ex-nk e) j)) (equal (ex-kid-of e j) nil))
  :hints (("Goal" :in-theory (enable ex-kid-of ex-nk))))
(defthm aot-ffr-grows2
  (implies (and (equal (mv-nth 1 (aot-ty fl e j m k st)) 1) (equal (nth 3 st) cb) (equal (nth 4 st) cn) (natp cb) (natp cn)
                (aot-ffr fr l (nth 1 st) cb cn t lo hi i n))
           (aot-ffr fr l (nth 1 (mv-nth 2 (aot-ty fl e j m k st))) cb cn t lo hi i n))
  :hints (("Goal" :use aot-ffr-grows :in-theory (disable aot-ffr-grows))))

(defmacro aot-case-theory (&rest more) `(e/d (aot-cl aot-hyp aot-concl aot-tyof ,@more) (env-raw-st)))

(defthm aot-cl-do-mid
  (implies (and (consp e) (< (nfix i) (- (ex-nk e) 1))
                (aot-cl :m (ex-kid-of e (nfix i)) 0 nil fr fuel (aot-tick s))
                (aot-cl :do e (1+ (nfix i)) tmp (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)) fuel
                        (mv-nth 2 (aot-ty 0 (ex-kid-of e (nfix i)) 0 0 0 (aot-tick s)))))
           (aot-cl :do e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-1-x) :expand ((ex-ev :do e i tmp fr fuel)))))

(defthm aot-cl-do-last
  (implies (and (consp e) (not (zp (ex-nk e))) (not (< (nfix i) (- (ex-nk e) 1)))
                (aot-cl :m (ex-kid-of e (- (ex-nk e) 1)) 0 nil fr fuel (aot-tick s)))
           (aot-cl :do e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-1-x) :cases ((equal i (- (ex-nk e) 1))) :expand ((:free (i) (ex-ev :do e i tmp fr fuel)) (:free (i) (aot-ty 1 e i (ex-nk e) 0 s))))))

(defthm ex-ev-do-empty (implies (and (consp e) (zp (ex-nk e))) (equal (ex-ev :do e i tmp fr fuel) (list (cons :val nil) fr 1)))
  :hints (("Goal" :expand ((ex-ev :do e i tmp fr fuel)))))
(defthm aot-cl-m-do
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (equal (ex-kind e) 5)
                (aot-cl :do e 0 nil fr fuel (aot-tick s)))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-z-5) :expand ((ex-ev :m e i tmp fr fuel)))))

(defthm aot-cl-if
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (equal (ex-kind e) 4)
                (aot-cl :m (ex-kid-of e 0) 0 nil fr fuel (aot-tick s))
                (aot-cl :m (ex-kid-of e 1) 0 nil (cadr (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)) fuel
                        (mv-nth 2 (aot-ty 0 (ex-kid-of e 0) 0 0 0 (aot-tick s))))
                (aot-cl :m (ex-kid-of e 2) 0 nil (cadr (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)) fuel
                        (mv-nth 2 (aot-ty 0 (ex-kid-of e 1) 0 0 0 (mv-nth 2 (aot-ty 0 (ex-kid-of e 0) 0 0 0 (aot-tick s)))))))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-z-4) :expand ((ex-ev :m e i tmp fr fuel)))))

; ---- a let's and a loop's bindings --------------------------------------------------------------

(defthm aot-ffr-unbind-in
  (implies (and (aot-ffr fr (update-nth s x l) r cb cn rec lo hi i n) (natp s) (< s (len l)) (<= lo s) (< s hi))
           (aot-ffr fr l r cb cn rec lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr (update-nth s x l) r cb cn rec lo hi i n) :in-theory (enable aot-ffr aot-slt)
           :expand ((aot-ffr fr l r cb cn rec lo hi i n)))))

(defthm aot-ffr-empty
  (implies (aot-ffr fr l r cb cn rec lo lo i n) (aot-ffr fr l r cb cn rec 0 0 i n))
  :hints (("Goal" :induct (aot-ffr fr l r cb cn rec lo lo i n) :in-theory (enable aot-ffr)
           :expand ((aot-ffr fr l r cb cn rec 0 0 i n)))))
(defthm aot-allany-point
  (implies (and (aot-allany l b j m) (natp b) (natp j) (natp m) (natp s) (<= (+ b j) s) (< s (+ b m)))
           (equal (tvg s l) 1))
  :hints (("Goal" :induct (aot-allany l b j m))))
(defthm aot-ffr-allany
  (implies (and (aot-ffr fr l nil 0 0 nil b hi i n) (aot-allany l b 0 m) (equal hi (+ b m)) (natp b) (natp m))
           (aot-ffr fr l nil 0 0 nil 0 0 i n))
  :hints (("Goal" :induct (aot-ffr fr l nil 0 0 nil b hi i n) :in-theory (e/d (aot-ffr aot-slt) (aot-allany))
           :expand ((aot-ffr fr l nil 0 0 nil 0 0 i n)))))
(defthm aot-allany-update-below
  (implies (and (natp s) (< s (len l)) (natp b) (natp i) (< s (+ b i)))
           (equal (aot-allany (update-nth s v l) b i n) (aot-allany l b i n)))
  :hints (("Goal" :induct (aot-allany l b i n) :expand ((aot-allany (update-nth s v l) b i n)))))

(defun-nx aot-6-ind (e j m st)
  (declare (xargs :measure (nfix (- (nfix m) (nfix j)))))
  (if (and (natp j) (natp m) (< j m))
      (aot-6-ind e (+ 1 j) m (aot-put (+ (aot-s2 e) j) (mv-nth 0 (aot-ty 0 (aot-kid e j) 0 0 0 (aot-tick st)))
                                      (mv-nth 2 (aot-ty 0 (aot-kid e j) 0 0 0 (aot-tick st)))))
    (list e st)))
(defthm aot-ty6-fresh
  (implies (and (equal (mv-nth 1 (aot-ty 6 e j m 0 st)) 1) (not (equal (aot-k e) 0)) (natp j) (natp m))
           (aot-allany (nth 0 st) (aot-s2 e) j m))
  :hints (("Goal" :induct (aot-6-ind e j m st) :in-theory (enable aot-ty-6-x aot-put-tv aot-raw-nth))))

(in-theory (disable aot-allany))
(defthm aot-star-len
  (and (equal (len (nth 0 (aot-star fl e j m k st))) (len (nth 0 st)))
       (equal (len (nth 1 (aot-star fl e j m k st))) (len (nth 1 st))))
  :hints (("Goal" :induct (aot-star fl e j m k st) :in-theory (enable aot-star aot-put-tv))))

(defthm aot-star-settled-ex
  (implies (and (aot-node-ok e) (equal m (ex-i2 e)))
           (aot-settled (ex-s2 e) 0 m (mv-nth 2 (aot-ty 0 (ex-kid-of e m) 0 0 0 (aot-star 5 e 0 m 0 x)))))
  :hints (("Goal" :use ((:instance aot-star-settled (fl 5) (j 0) (k 0) (aots x))) :in-theory (disable aot-star-settled))))

(defthm aot-star-ty-ex
  (implies (and (aot-node-ok e) (equal m (ex-i2 e)))
           (let ((w (aot-ty 0 (ex-kid-of e m) 0 0 0 (aot-star 5 e 0 m 0 x))))
             (and (equal (mv-nth 0 (aot-ty 5 e 0 m 0 x)) (mv-nth 0 w))
                  (implies (equal (mv-nth 1 (aot-ty 5 e 0 m 0 x)) 1) (equal (mv-nth 1 w) 1)))))
  :hints (("Goal" :use ((:instance aot-star-ty (fl 5) (j 0) (k 0) (aots x))) :in-theory (disable aot-star-ty))))
(defthm aot-ffr-narrow2
  (implies (and (aot-ffr fr (nth 0 (aot-star fl e j m k st)) nil 0 0 nil 0 0 i n) (equal (nth 0 st) l) (< (ex-s2 e) *anp40*)
                (equal lo (ex-s2 e)) (equal hi (+ (ex-s2 e) m)))
           (aot-ffr fr l nil 0 0 nil lo hi i n))
  :hints (("Goal" :use aot-ffr-narrow :in-theory (disable aot-ffr-narrow))))

(defthm aot-cl-let-bind
  (implies (and (consp e) (< (nfix i) (ex-i2 e))
                (aot-cl :m (ex-kid-of e (nfix i)) 0 nil fr fuel (aot-tick s))
                (aot-cl :let e (1+ (nfix i)) tmp
                        (update-nth (+ (ex-s2 e) (nfix i)) (val (car (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
                                    (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
                        fuel
                        (aot-put (+ (ex-s2 e) (nfix i)) (mv-nth 0 (aot-ty 0 (ex-kid-of e (nfix i)) 0 0 0 (aot-tick s)))
                                 (mv-nth 2 (aot-ty 0 (ex-kid-of e (nfix i)) 0 0 0 (aot-tick s))))))
           (aot-cl :let e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-2-x aot-ty-6-x) :expand ((ex-ev :let e i tmp fr fuel)))))

(defthm aot-cl-let-body
  (implies (and (consp e) (not (< (nfix i) (ex-i2 e))) (not (equal (ex-kind e) 12))
                (aot-cl :m (ex-kid-of e (ex-i2 e)) 0 nil fr fuel (aot-tick s)))
           (aot-cl :let e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-2-x) :cases ((equal i (ex-i2 e)))
           :expand ((:free (i) (ex-ev :let e i tmp fr fuel)) (:free (i) (aot-ty 2 e i (ex-i2 e) 0 s))))))

(defthm aot-cl-loop-body
  (implies (and (consp e) (not (< (nfix i) (ex-i2 e))) (equal (ex-kind e) 12)
                (aot-cl :iter (ex-kid-of e (ex-i2 e)) 0 nil fr fuel
                        (aot-star 5 e 0 (ex-i2 e) 0
                                  (update-nth 4 (ex-i2 e) (update-nth 3 (ex-s2 e) (aot-rzero (ex-s2 e) 0 (ex-i2 e) (aot-tick s)))))))
           (aot-cl :let e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-6-x nth-update-nth) :cases ((equal i (ex-i2 e)))
           :expand ((:free (i) (ex-ev :let e i tmp fr fuel)) (:free (i) (aot-ty 6 e i (ex-i2 e) 0 s))))))

(defun-nx aot-let-ind (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix i)))))
  (if (< (nfix i) (ex-i2 e))
      (aot-let-ind e (1+ (nfix i)) tmp
                   (update-nth (+ (ex-s2 e) (nfix i)) (val (car (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
                               (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
                   fuel)
    (list e tmp fr fuel)))
(defthm ex-ev-loop-norec
  (implies (equal (ex-kind e) 12) (not (equal (car (car (ex-ev :let e i tmp fr fuel))) :recur)))
  :hints (("Goal" :induct (aot-let-ind e i tmp fr fuel) :expand ((ex-ev :let e i tmp fr fuel)))))
(defthm aot-cl-m-let
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12))
                (aot-cl :let e 0 nil fr fuel (aot-tick s)))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-z-11 aot-ty-z-12) :expand ((ex-ev :m e i tmp fr fuel))
           :use ((:instance aot-ty6-fresh (j 0) (m (ex-i2 e)) (st (aot-tick s)))))))

; ---- a recur's arguments ------------------------------------------------------------------------

(defthm aot-ffr-write2
  (implies (and (aot-ffr fr l nil 0 0 nil 0 0 i n) (aot-rfit tmp l r b) (natp b) (equal cb b) (equal cn (len tmp)))
           (aot-ffr (ex-write b tmp fr) l r cb cn t 0 0 i n)))

(defthm aot-rjn-len (equal (len (nth 1 (aot-rjn s v x))) (len (nth 1 x))) :hints (("Goal" :in-theory (enable aot-rjn-rc))))
(defthm aot-rfit-step
  (let ((w (aot-ty 0 a 0 0 0 (aot-tick s))))
    (implies (and (aot-rfit tmp (nth 0 s) (nth 1 s) b) (equal (nth 3 s) b) (natp b) (natp (nth 4 s)) (< (len tmp) (nth 4 s))
                  (equal (mv-nth 1 w) 1) (aot-fits v (mv-nth 0 w)) (<= (len (nth 0 s)) (len (nth 1 s))))
             (aot-rfit (append tmp (list v)) (nth 0 s) (nth 1 (aot-rjn (+ b (len tmp)) (car w) (mv-nth 2 w))) b)))
  :hints (("Goal" :use ((:instance aot-rfit-append (l (nth 0 s)) (r (nth 1 (aot-rjn (+ b (len tmp)) (mv-nth 0 (aot-ty 0 a 0 0 0 (aot-tick s))) (mv-nth 2 (aot-ty 0 a 0 0 0 (aot-tick s)))))))
                         (:instance aot-rjn-here (s (+ b (len tmp))) (t0 (mv-nth 0 (aot-ty 0 a 0 0 0 (aot-tick s)))) (st (mv-nth 2 (aot-ty 0 a 0 0 0 (aot-tick s)))))
                         (:instance aot-rfit-grows (l (nth 0 s)) (fl 0) (e a) (j 0) (m 0) (k 0) (st (aot-tick s))))
           :in-theory (disable aot-rfit-append aot-rjn-here aot-rfit-grows))))
(defthm aot-ffr-cn0
  (implies (aot-ffr fr l nil 0 0 nil lo hi i n) (aot-ffr fr l r cb 0 t lo hi i n))
  :hints (("Goal" :induct (aot-ffr fr l nil 0 0 nil lo hi i n) :in-theory (enable aot-ffr aot-slt)
           :expand ((aot-ffr fr l r cb 0 t lo hi i n)))))
(defthm aot-take-len2 (implies (and (true-listp x) (equal n (len x))) (equal (take n x) x)))
(defthm aot-len-append (equal (len (append a b)) (+ (len a) (len b))))
(defthm aot-true-listp-append (implies (true-listp b) (true-listp (append a b))))
(defun-nx aot-rec-ind (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (< (nfix i) (ex-nk e))
      (aot-rec-ind e (1+ (nfix i)) (append tmp (list (val (car (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))))
                   (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)) fuel)
    (list e tmp fr fuel)))
(defthm ex-ev-rec-noval
  (not (equal (car (car (ex-ev :rec e i tmp fr fuel))) :val))
  :hints (("Goal" :induct (aot-rec-ind e i tmp fr fuel) :expand ((ex-ev :rec e i tmp fr fuel)))))
(defthm aot-cl-rec-arg
  (implies (and (consp e) (< (nfix i) (ex-nk e))
                (aot-cl :m (ex-kid-of e (nfix i)) 0 nil fr fuel (aot-tick s))
                (aot-cl :rec e (1+ (nfix i)) (append tmp (list (val (car (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))))
                        (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)) fuel
                        (aot-rjn (+ (ex-rstart e) (nfix i)) (mv-nth 0 (aot-ty 0 (ex-kid-of e (nfix i)) 0 0 0 (aot-tick s)))
                                 (mv-nth 2 (aot-ty 0 (ex-kid-of e (nfix i)) 0 0 0 (aot-tick s))))))
           (aot-cl :rec e i tmp fr fuel s))
  :hints (("Goal" :do-not-induct t :in-theory (aot-case-theory aot-ty-3-x) :expand ((:free (i) (ex-ev :rec e i tmp fr fuel)) (:free (i) (aot-ty 3 e i (ex-nk e) 0 s))))))

(defthm aot-cl-rec-end
  (implies (and (consp e) (not (< (nfix i) (ex-nk e))))
           (aot-cl :rec e i tmp fr fuel s))
  :hints (("Goal" :do-not-induct t :in-theory (aot-case-theory aot-ty-3-x) :expand ((:free (i) (ex-ev :rec e i tmp fr fuel)) (:free (i) (aot-ty 3 e i (ex-nk e) 0 s))))))

(defthm aot-cl-m-rec
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (equal (ex-kind e) 16)
                (aot-cl :rec e 0 nil fr fuel (aot-tick s)))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (aot-case-theory aot-ty-z-16) :expand ((ex-ev :m e i tmp fr fuel)))))

; ---- a call's operands and its answer -----------------------------------------------------------

(defthm ex-ev-const
  (implies (and (consp h) (or (equal (ex-kind h) 1) (equal (ex-kind h) 3)))
           (equal (ex-ev :m h i tmp fr fuel) (list (cons :val (ex-c h)) fr 1)))
  :hints (("Goal" :expand ((ex-ev :m h i tmp fr fuel)))))
(defthm ex-ev-const2
  (implies (and (aot-sub 0 h 0) (or (equal (ex-kind h) 1) (equal (ex-kind h) 3)))
           (equal (ex-ev :m h i tmp fr fuel) (list (cons :val (ex-c h)) fr 1))))
(in-theory (disable aot-opok))
(defthm aot-car-append (implies (consp a) (equal (car (append a b)) (car a))))

(defthm aot-ty-4-open
  (implies (and (syntaxp (variablep s)) (natp i) (< i (ex-nk e)) (< (ex-nk e) *anp40*) (not (equal (aot-k e) 0)))
           (equal (aot-ty 4 e i (ex-nk e) 0 s)
                  (mv 0 (aot-and (mv-nth 1 (aot-ty 0 (ex-kid-of e i) 0 0 0 (aot-tick s)))
                                 (aot-and (mv-nth 1 (aot-w2 e i s)) (mv-nth 1 (aot-ty 4 e (1+ i) (ex-nk e) 0 (aot-s3 e i s)))))
                      (mv-nth 2 (aot-ty 4 e (1+ i) (ex-nk e) 0 (aot-s3 e i s))))))
  :hints (("Goal" :in-theory (enable aot-ty-4-x aot-w2 aot-s3 aot-cast))))

(defthm aot-s3-env
  (and (equal (nth 0 (aot-s3 e i s)) (nth 0 s)) (equal (nth 3 (aot-s3 e i s)) (nth 3 s)) (equal (nth 4 (aot-s3 e i s)) (nth 4 s))
       (equal (len (nth 1 (aot-s3 e i s))) (len (nth 1 s))))
  :hints (("Goal" :in-theory (enable aot-s3 aot-w2 nth-update-nth))))

(defthm aot-s3-regok
  (implies (and (natp i) (<= 1 i) (equal (len tmp) i) (aot-regok e tmp s)
                (aot-fits v (mv-nth 0 (aot-ty 0 (ex-kid-of e i) 0 0 0 (aot-tick s)))))
           (aot-regok e (append tmp (list v)) (aot-s3 e i s)))
  :hints (("Goal" :in-theory (enable aot-regok aot-s3 aot-w2 aot-cast nth-update-nth))))

(defthm aot-cl-call-arg
  (implies (and (consp e) (< (nfix i) (ex-nk e))
                (aot-cl :m (ex-kid-of e (nfix i)) 0 nil fr fuel (aot-tick s))
                (aot-cl :call e (1+ (nfix i)) (append tmp (list (val (car (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))))
                        (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)) fuel (aot-s3 e (nfix i) s)))
           (aot-cl :call e i tmp fr fuel s))
  :hints (("Goal" :do-not-induct t :in-theory (aot-case-theory)
           :expand ((:free (i) (ex-ev :call e i tmp fr fuel))))))

(defthm aot-cl-call-end
  (implies (and (consp e) (not (< (nfix i) (ex-nk e))))
           (aot-cl :call e i tmp fr fuel s))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (aot-cl aot-hyp aot-concl aot-tyof aot-regok) (env-raw-st aot-opok)) :cases ((equal i (ex-nk e))) :expand ((:free (j) (aot-ty 4 e j (ex-nk e) 0 s)))
           :use (aot-node-call (:instance aot-opok-necc (ta (nth 5 s)) (tb (nth 6 s)) (tc (nth 7 s)))))))

(defmacro aot-sa (s) `(update-nth 8 0 (update-nth 7 1 (update-nth 6 1 (update-nth 5 1 (aot-tick ,s))))))

(defthm aot-cl-m-call-linked
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (equal (ex-kind e) 6)
                (ex-linked (ex-kid-of e 0))
                (aot-cl :call e 1 (list (ex-c (ex-kid-of e 0))) fr fuel (mv-nth 2 (aot-ty 0 (ex-kid-of e 0) 0 0 0 (aot-sa s)))))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :do-not-induct t :in-theory (aot-case-theory aot-ty-z-6 nth-update-nth aot-regok) :expand ((ex-ev :m e i tmp fr fuel))
           :use aot-node-call)))

(defthm aot-cl-m-call
  (implies (and (not (member-eq flg '(:iter :do :let :rec :call :fin :coll))) (equal (ex-kind e) 6)
                (not (ex-linked (ex-kid-of e 0)))
                (aot-cl :m (ex-kid-of e 0) 0 nil fr fuel (aot-sa s))
                (aot-cl :call e 1 (list (val (car (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel))))
                        (cadr (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)) fuel
                        (mv-nth 2 (aot-ty 0 (ex-kid-of e 0) 0 0 0 (aot-sa s)))))
           (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :do-not-induct t :in-theory (aot-case-theory aot-ty-z-6 nth-update-nth aot-regok) :expand ((ex-ev :m e i tmp fr fuel))
           :use aot-node-call)))

; ---- THE THEOREM -------------------------------------------------------------------------------

(defthm aot-cl-do-zero (implies (and (consp e) (zp (ex-nk e))) (aot-cl :do e i tmp fr fuel s))
  :hints (("Goal" :in-theory (enable aot-cl aot-hyp))))
(defthm aot-cl-flag-other (implies (not (member-eq flg '(:m :iter :do :let :rec :call))) (aot-cl flg e i tmp fr fuel s))
  :hints (("Goal" :in-theory (enable aot-cl aot-hyp))))

(in-theory (disable aot-cl aot-hyp aot-concl aot-tyof))

; THE TYPE INFERENCE IS SOUND: at every ex-ev place, on the typed subset (aot-hyp), what ex-ev answers
; fits the type aot-ty gives it and the frame after fits the env (aot-concl)
(defthm aot-ty-sound (aot-cl flg e i tmp fr fuel s)
  :hints (("Goal" :induct (aot-ind flg e i tmp fr fuel s) :do-not '(generalize fertilize eliminate-destructors))))

; the headline: a node on the typed subset, walked ok in an env its frame fits, answers in ex-ev a
; value of the type aot-ty gives it, and leaves the frame fitting the env
(defthm aot-ty-sound-m
  (let ((r (ex-ev :m e 0 nil fr fuel)) (w (aot-ty 0 e 0 0 0 s)))
    (implies (and (aot-sub 0 e 0) (natp (nth 3 s)) (natp (nth 4 s)) (<= (len (nth 0 s)) (len (nth 1 s)))
                  (equal (mv-nth 1 w) 1) (aot-ffr fr (nth 0 s) nil 0 0 nil 0 0 0 (len (nth 0 s)))
                  (valp (car r)))
             (and (aot-fits (val (car r)) (mv-nth 0 w))
                  (aot-ffr (cadr r) (nth 0 s) nil 0 0 nil 0 0 0 (len (nth 0 s))))))
  :hints (("Goal" :use ((:instance aot-ty-sound (flg :m) (i 0) (tmp nil)))
           :in-theory (e/d (aot-cl aot-hyp aot-concl aot-tyof) (aot-ty-sound)))))

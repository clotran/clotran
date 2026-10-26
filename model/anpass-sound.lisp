; LOCALS CLEARING IS SOUND, AND A RECUR IS LAST (model/anpass.lisp's passes,
; their runs in model/anpass-runs.lisp): tr-sound, anp-clears-sound, tr-tail.
;
; Assumed, not proved here: each node the analyzer makes stands at one place
; in its tree, so marking a node (slot 3) marks the one read tr annotates.

(in-package "ACL2")

(include-book "anpass-runs")

(defthm ast-kind-not-node (implies (not (ast-p x)) (equal (ast-kind x) 0)) :hints (("Goal" :in-theory (enable ast-kind))))

; ---- SOUND -------------------------------------------------------------------------------------------

(defun all-live (ss L n)
  (if (atom ss) t
    (and (implies (and (natp (car ss)) (< (car ss) n)) (not (equal (nth (car ss) L) 0)))
         (all-live (cdr ss) L n))))

(defthm all-live-member
  (implies (and (all-live ss L n) (member s ss) (natp s) (< s n)) (not (equal (nth s L) 0))))

(defthm all-live-rds
  (implies (and (subsetp ss (rds fl x j m)) (equal (len L) n))
           (all-live ss (sp-rd fl x j m L n) n))
  :hints (("Goal" :induct (len ss))))

(defthm subsetp-cons-more (implies (subsetp a b) (subsetp a (cons y b))))
(defthm subsetp-refl (subsetp x x))

; a run of a body whose reads are all live after it marks nothing
(defthm tr-0-no-ann-live
  (implies (and (ok-ann evs L n) (all-live (slots evs) L n)) (no-ann evs))
  :hints (("Goal" :induct (ok-ann evs L n))))

(defthm all-live-sub
  (implies (and (all-live ss L n) (subsetp s2 ss)) (all-live s2 L n))
  :hints (("Goal" :induct (all-live s2 L n))))

(defthm tr-0-rds
  (implies (member s (slots (tr 0 x j m L os n))) (member s (rds 0 x 0 0)))
  :hints (("Goal" :use ((:instance tr-rds (fl 0) (j 0) (m 0))) :in-theory (disable tr-rds tr-0-open)
           :expand ((tr 0 x j m L os n) (tr 0 x 0 0 L os n)))))

(defthm subsetp-tr0-rds
  (implies (subsetp a (slots (tr 0 x 0 0 L os n))) (subsetp a (rds 0 x 0 0)))
  :hints (("Goal" :induct (len a) :in-theory (disable tr-0-open tr-seq-open tr-4-open rds rds-0-open))))

(defthm slots-tr-sub
  (subsetp (slots (tr 0 x 0 0 L os n)) (rds 0 x 0 0))
  :hints (("Goal" :use ((:instance subsetp-tr0-rds (a (slots (tr 0 x 0 0 L os n)))))
           :in-theory (disable subsetp-tr0-rds tr-0-open rds rds-0-open))))


; ---- WHAT A LIVE SET COVERS ---------------------------------------------------------------------------

(defthm tr-alt-out
  (implies (not (and (natp i) (< i (ast-nalts x)))) (equal (tr 0 (ast-alt x i) j m L os n) nil)))
(defthm tr-kid-out
  (implies (not (and (natp i) (< i (ast-nkids x)))) (equal (tr 0 (ast-kid x i) j m L os n) nil)))

(in-theory (disable tr-0-open tr-seq-open tr-4-open sp-out-seq-open rds-0-open))

(defthm dom-cover
  (implies (and (equal (len L) n) (not (equal fl 2)) (not (equal fl 4)))
           (dom (sp-out fl x j m nil L n) (tr fl x j m L os n) L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t
           :use ((:instance tr-cover (s (dom-witness (sp-out fl x j m nil L n) (tr fl x j m L os n) L n)))))))

(defthm dom-or-1
  (implies (and (dom A b L n) (equal (len A) n)) (dom (sp-or A A2) b L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t :use ((:instance dom-necc (LA A) (s (dom-witness (sp-or A A2) b L n)))))))

(defthm dom-or-2
  (implies (and (dom A2 b L n) (equal (len A) n)) (dom (sp-or A A2) b L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t :use ((:instance dom-necc (LA A2) (s (dom-witness (sp-or A A2) b L n)))))))

; the or of alternatives covers what its first set does, and what each alternative's does
(defthm dom-alts-acc
  (implies (and (dom A b L2 n) (equal (len A) n) (equal (len L) n))
           (dom (sp-out 2 x j m A L n) b L2 n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t
           :use ((:instance dom-necc (LA A) (L L2) (s (dom-witness (sp-out 2 x j m A L n) b L2 n)))))))

(defthm dom-alts-one
  (implies (and (dom (sp-out 0 (ast-alt x i) 0 0 nil L n) b L2 n) (equal (len A) n) (equal (len L) n)
                (natp i) (< i (ast-nalts x)) (not (equal (ast-kind x) 0)))
           (dom (sp-out 2 x 0 (ast-nalts x) A L n) b L2 n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t
           :use ((:instance dom-necc (LA (sp-out 0 (ast-alt x i) 0 0 nil L n)) (L L2)
                            (s (dom-witness (sp-out 2 x 0 (ast-nalts x) A L n) b L2 n)))))))

(defthm dom-append
  (implies (and (dom LA a L2 n) (dom L2 b L n)) (dom LA (append a b) L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t
           :use ((:instance dom-necc (L L2) (b a) (s (dom-witness LA (append a b) L n)))
                 (:instance dom-necc (LA L2) (b b) (s (dom-witness LA (append a b) L n))))))
  :rule-classes nil)

(defthm dom-no-slots
  (implies (not (consp (slots b))) (dom L b L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t)))

; a loop's iterations read only what its body's reads_in found
(defthm dom-loop
  (implies (equal (len L) n)
           (dom (sp-out 0 bd 0 0 nil (sp-rd 0 bd 0 0 L n) n) (tr 4 bd 0 0 (sp-rd 0 bd 0 0 L n) os n) L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t)))

; letfn's captures copied again, then its body
(defthm dom-letfn
  (implies (equal (len L) n)
           (dom (sp-fncaps x 0 k (sp-out 0 bd 0 0 nil L n) n) (append (fncap-evs x 0 k) (tr 0 bd 0 0 L o n)) L n))
  :hints (("Goal" :in-theory (enable dom) :do-not-induct t
           :use ((:instance tr-cover (fl 0) (x bd) (j 0) (m 0) (os o)
                            (s (dom-witness (sp-fncaps x 0 k (sp-out 0 bd 0 0 nil L n) n)
                                            (append (fncap-evs x 0 k) (tr 0 bd 0 0 L o n)) L n)))))))

; a try: a catch's run then the finally's
(defthm dom-try-catch
  (implies (and (equal (len L) n) (natp i) (< i (ast-nalts x)) (not (equal (ast-kind x) 0)))
           (let ((L1 (sp-out 0 kd 0 0 nil L n)))
             (dom (sp-out 2 x 0 (ast-nalts x) L1 L1 n) (append (tr 0 (ast-alt x i) 0 0 L1 o n) (tr 0 kd 0 0 L o2 n)) L n)))
  :hints (("Goal" :use ((:instance dom-append (LA (sp-out 2 x 0 (ast-nalts x) (sp-out 0 kd 0 0 nil L n) (sp-out 0 kd 0 0 nil L n) n))
                                    (a (tr 0 (ast-alt x i) 0 0 (sp-out 0 kd 0 0 nil L n) o n))
                                    (L2 (sp-out 0 kd 0 0 nil L n)) (b (tr 0 kd 0 0 L o2 n)))
                        (:instance dom-alts-one (A (sp-out 0 kd 0 0 nil L n)) (L (sp-out 0 kd 0 0 nil L n))
                                   (b (tr 0 (ast-alt x i) 0 0 (sp-out 0 kd 0 0 nil L n) o n)) (L2 (sp-out 0 kd 0 0 nil L n)))
                        (:instance dom-cover (fl 0) (x (ast-alt x i)) (j 0) (m 0) (L (sp-out 0 kd 0 0 nil L n)) (os o))
                        (:instance dom-cover (fl 0) (x kd) (j 0) (m 0) (os o2)))
           :in-theory (disable dom dom-cover dom-alts-one))))

(defthm dom-try-catch-out
  (implies (and (equal (len L) n) (not (and (natp i) (< i (ast-nalts x)))))
           (let ((L1 (sp-out 0 kd 0 0 nil L n)))
             (dom (sp-out 2 x 0 (ast-nalts x) L1 L1 n) (append (tr 0 (ast-alt x i) 0 0 L1 o n) (tr 0 kd 0 0 L o2 n)) L n)))
  :hints (("Goal" :in-theory (disable dom dom-cover dom-alts-acc)
           :use ((:instance dom-alts-acc (A (sp-out 0 kd 0 0 nil L n)) (L (sp-out 0 kd 0 0 nil L n)) (j 0) (m (ast-nalts x))
                            (b (tr 0 kd 0 0 L o2 n)) (L2 L))
                 (:instance dom-cover (fl 0) (x kd) (j 0) (m 0) (os o2))))))

(defthm subsetp-tr4-rds
  (implies (subsetp a (slots (tr 4 x j m L os n))) (subsetp a (rds 0 x 0 0)))
  :hints (("Goal" :induct (len a) :in-theory (disable tr-0-open tr-seq-open tr-4-open rds rds-0-open))))

(defthm slots-tr4-sub
  (subsetp (slots (tr 4 x j m L os n)) (rds 0 x 0 0))
  :hints (("Goal" :use ((:instance subsetp-tr4-rds (a (slots (tr 4 x j m L os n)))))
           :in-theory (disable subsetp-tr4-rds tr-4-open rds rds-0-open))))

(defthm tr-4-no-ann
  (implies (and (ok-ann (tr 4 x j m L os n) L n) (all-live (rds 0 x 0 0) L n))
           (no-ann (tr 4 x j m L os n)))
  :hints (("Goal" :in-theory (disable tr-4-open rds rds-0-open all-live-sub)
           :use ((:instance all-live-sub (ss (rds 0 x 0 0)) (s2 (slots (tr 4 x j m L os n))))))))

(defthm dom-try-catch-any
  (implies (and (equal (len L) n) (not (equal (ast-kind x) 0)))
           (let ((L1 (sp-out 0 kd 0 0 nil L n)))
             (dom (sp-out 2 x 0 (ast-nalts x) L1 L1 n) (append (tr 0 (ast-alt x i) 0 0 L1 o n) (tr 0 kd 0 0 L o2 n)) L n)))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nalts x)))) :in-theory (disable dom))))

(defthm dom-case-default
  (implies (equal (len L) n)
           (dom (sp-or (sp-out 2 x 0 k L L n) (sp-out 0 kd 0 0 nil L n)) (tr 0 kd 0 0 L o n) L n))
  :hints (("Goal" :in-theory (disable dom dom-or-2 dom-cover)
           :use ((:instance dom-or-2 (A (sp-out 2 x 0 k L L n)) (A2 (sp-out 0 kd 0 0 nil L n)) (b (tr 0 kd 0 0 L o n)))
                 (:instance dom-cover (fl 0) (x kd) (j 0) (m 0) (os o))))))

(defthm dom-case-alt
  (implies (and (equal (len L) n) (not (equal (ast-kind x) 0)))
           (dom (sp-or (sp-out 2 x 0 (ast-nalts x) L L n) (sp-out 0 kd 0 0 nil L n)) (tr 0 (ast-alt x i) 0 0 L o n) L n))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nalts x))))
           :in-theory (disable dom dom-or-1 dom-cover dom-alts-one)
           :use ((:instance dom-or-1 (A (sp-out 2 x 0 (ast-nalts x) L L n)) (A2 (sp-out 0 kd 0 0 nil L n)) (b (tr 0 (ast-alt x i) 0 0 L o n)))
                 (:instance dom-alts-one (A L) (b (tr 0 (ast-alt x i) 0 0 L o n)) (L2 L))
                 (:instance dom-cover (fl 0) (x (ast-alt x i)) (j 0) (m 0) (os o))))))

(defthm ok-ann-append-prefix
  (implies (and (ok-ann a LA n) (ok-ann b L n) (dom LA b L n)) (ok-ann (append (anp-prefix k a) b) L n))
  :hints (("Goal" :in-theory (disable ok-ann-append dom) :use ((:instance ok-ann-append (a (anp-prefix k a)))))))

(defthm tr-0-nonnode
  (implies (equal (ast-kind x) 0) (equal (tr 0 x j m L os n) nil))
  :hints (("Goal" :expand ((tr 0 x j m L os n)))))

(in-theory (enable tr-0-open tr-seq-open tr-4-open sp-out-seq-open rds-0-open))

(defthm tr-sound
  (implies (and (natp n) (equal (len L) n) (not (equal fl 2))
                (implies (equal fl 4) (all-live (rds 0 x 0 0) L n)))
           (ok-ann (tr fl x j m L os n) L n))
  :hints (("Goal" :induct (tr fl x j m L os n) :in-theory (disable dom fncap-evs cap-evs cap-list rds rds-0-open)
           :do-not (quote (generalize eliminate-destructors)) :do-not-induct t)))

; ---- A RECUR IS THE LAST THING ITS BODY DOES ------------------------------------------------------

(defun recp (e) (and (consp e) (eq (car e) :recur)))
(defun no-rec (evs) (if (atom evs) t (and (not (recp (car evs))) (no-rec (cdr evs)))))
; a recur only as the very last event, to the target f says
(defun rec-last (evs f)
  (cond ((atom evs) t)
        ((recp (car evs)) (and (atom (cdr evs)) (equal (cdar evs) f)))
        (t (rec-last (cdr evs) f))))

(defthm no-rec-append (equal (no-rec (append a b)) (and (no-rec a) (no-rec b))))
(defthm rec-last-append (implies (and (no-rec a) (rec-last b f)) (rec-last (append a b) f)))
(defthm no-rec-rec-last (implies (no-rec a) (rec-last a f)))
(defthm no-rec-prefix (implies (no-rec a) (no-rec (anp-prefix k a))))
(defthm no-rec-init (implies (no-rec a) (no-rec (anp-init a))))
(defthm rec-last-init (implies (rec-last a f) (no-rec (anp-init a))))
(defthm rec-last-not-last (implies (and (rec-last a f) (not (equal (anp-last a) (cons :recur f)))) (no-rec a)))
(defthm no-rec-cap-evs (no-rec (cap-evs x i k)))
(defthm no-rec-fncap-evs (no-rec (fncap-evs x i k)) :hints (("Goal" :in-theory (enable fncap-evs))))

(defthm tc-nil (equal (anp-tc 0 nil j m tt) 0) :hints (("Goal" :in-theory (enable ast-kind ast-p))))

(defthm tc-seq-open
  (implies (and (not (equal fl 0)) (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (anp-tc fl x j m tt)
                  (if (equal (anp-tc 0 (anp-ch fl x j) 0 0 tt) 0) (anp-tc fl x (+ 1 j) m tt) (anp-tc 0 (anp-ch fl x j) 0 0 tt)))))
(defthm tc-seq-done
  (implies (and (not (equal fl 0)) (not (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))))
           (equal (anp-tc fl x j m tt) 0)))

(defthm tc-seq-elem
  (implies (and (equal (anp-tc fl x j m tt) 0) (not (equal fl 0)) (natp i) (natp j) (<= j i) (< i m) (integerp m)
                (not (equal (ast-kind x) 0)))
           (equal (anp-tc 0 (anp-ch fl x i) 0 0 tt) 0))
  :hints (("Goal" :induct (seq-ind j m))))

(defthm tc-alt
  (implies (and (equal (anp-tc 3 x 0 (ast-nalts x) tt) 0) (not (equal (ast-kind x) 0)))
           (equal (anp-tc 0 (ast-alt x i) 0 0 tt) 0))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nalts x))))
           :use ((:instance tc-seq-elem (fl 3) (j 0) (m (ast-nalts x)))))))

; the last of the children j .. m-1 in tt's position, the rest in none
(defun tc-seq-last (fl x j m tt)
  (declare (xargs :measure (nfix (- (ifix m) (nfix j)))))
  (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
      (if (equal j (- m 1))
          (equal (anp-tc 0 (anp-ch fl x j) 0 0 tt) 0)
        (and (equal (anp-tc 0 (anp-ch fl x j) 0 0 0) 0) (tc-seq-last fl x (+ 1 j) m tt)))
    t))

(defthm tc-seq-last-is
  (implies (and (not (equal fl 0)) (natp j) (integerp m) (< j m) (not (equal (ast-kind x) 0)))
           (equal (tc-seq-last fl x j m tt)
                  (and (equal (anp-tc fl x j (- m 1) 0) 0) (equal (anp-tc 0 (anp-ch fl x (- m 1)) 0 0 tt) 0))))
  :hints (("Goal" :induct (tc-seq-last fl x j m tt)))
  :rule-classes nil)

; as the tail check of a do or a let reads it
(defthm tc-seq-last-0
  (implies (and (not (equal fl 0)) (natp m) (not (equal (ast-kind x) 0)))
           (equal (tc-seq-last fl x 0 m tt)
                  (and (equal (anp-tc fl x 0 (- m 1) 0) 0) (equal (anp-tc 0 (anp-ch fl x (- m 1)) 0 0 tt) 0))))
  :hints (("Goal" :cases ((equal m 0)) :use ((:instance tc-seq-last-is (j 0))))))

(defthm tc-seq-last-open
  (implies (syntaxp (variablep j))
           (equal (tc-seq-last fl x j m tt)
                  (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
                      (if (equal j (- m 1))
                          (equal (anp-tc 0 (anp-ch fl x j) 0 0 tt) 0)
                        (and (equal (anp-tc 0 (anp-ch fl x j) 0 0 0) 0) (tc-seq-last fl x (+ 1 j) m tt)))
                    t))))

(defun tail-all (fl x j m evs)
  (cond ((equal fl 4) (implies (equal (anp-tc 0 x 0 0 2) 0) (no-rec evs)))
        ((equal fl 0)
         (and (implies (equal (anp-tc 0 x 0 0 0) 0) (no-rec evs))
              (implies (equal (anp-tc 0 x 0 0 3) 0) (no-rec evs))
              (implies (equal (anp-tc 0 x 0 0 1) 0) (rec-last evs t))
              (implies (equal (anp-tc 0 x 0 0 2) 0) (rec-last evs nil))))
        (t (and (implies (equal (anp-tc fl x j m 0) 0) (no-rec evs))
                (implies (tc-seq-last fl x j m 0) (no-rec evs))
                (implies (tc-seq-last fl x j m 3) (no-rec evs))
                (implies (tc-seq-last fl x j m 1) (rec-last evs t))
                (implies (tc-seq-last fl x j m 2) (rec-last evs nil))))))

(defthm tc-0-open
  (implies (syntaxp (variablep x)) (equal (anp-tc 0 x j m tt) (anp-tc-node)))
  :hints (("Goal" :expand ((anp-tc 0 x j m tt)))))

(defthm tr-tail (tail-all fl x j m (tr fl x j m L os n))
  :hints (("Goal" :induct (tr fl x j m L os n) :in-theory (disable fncap-evs cap-evs cap-list (:definition anp-tc) (:definition tc-seq-last))
           :do-not (quote (generalize eliminate-destructors)) :do-not-induct t)
          (and stable-under-simplificationp (quote (:cases ((equal (ast-nkids x) 1) (equal j (+ -1 m))))))))

; ---- A RECUR TO THE FN -------------------------------------------------------------------------------

(defun no-frec (evs) (if (atom evs) t (and (not (equal (car evs) (cons :recur t))) (no-frec (cdr evs)))))

(defthm no-frec-append (equal (no-frec (append a b)) (and (no-frec a) (no-frec b))))
(defthm no-frec-prefix (implies (no-frec a) (no-frec (anp-prefix k a))))
(defthm no-frec-init (implies (no-frec a) (no-frec (anp-init a))))
(defthm no-frec-cap-evs (no-frec (cap-evs x i k)))
(defthm no-frec-fncap-evs (no-frec (fncap-evs x i k)) :hints (("Goal" :in-theory (enable fncap-evs))))
(defthm no-frec-last (implies (no-frec a) (not (equal (anp-last a) (cons :recur t)))))

(defthm hfr-nil (equal (anp-hfr 0 nil j m) nil) :hints (("Goal" :in-theory (enable ast-kind ast-p))))

(defthm hfr-seq-open
  (implies (and (not (equal fl 0)) (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (anp-hfr fl x j m) (if (anp-hfr 0 (anp-ch fl x j) 0 0) t (anp-hfr fl x (+ 1 j) m)))))
(defthm hfr-seq-done
  (implies (and (not (equal fl 0)) (not (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))))
           (equal (anp-hfr fl x j m) nil)))

(defthm hfr-seq-elem
  (implies (and (not (anp-hfr fl x j m)) (not (equal fl 0)) (natp i) (natp j) (<= j i) (< i m) (integerp m)
                (not (equal (ast-kind x) 0)))
           (not (anp-hfr 0 (anp-ch fl x i) 0 0)))
  :hints (("Goal" :induct (seq-ind j m))))

(defthm hfr-alt
  (implies (and (not (anp-hfr 3 x 0 (ast-nalts x))) (not (equal (ast-kind x) 0)))
           (not (anp-hfr 0 (ast-alt x i) 0 0)))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nalts x))))
           :use ((:instance hfr-seq-elem (fl 3) (j 0) (m (ast-nalts x)))))))

(defthm hfr-kid
  (implies (and (not (anp-hfr 1 x 0 (ast-nkids x))) (not (equal (ast-kind x) 0)))
           (not (anp-hfr 0 (ast-kid x i) 0 0)))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nkids x))))
           :use ((:instance hfr-seq-elem (fl 1) (j 0) (m (ast-nkids x)))))))

(defthm hfr-seq-prefix
  (implies (and (not (anp-hfr fl x j m)) (not (equal fl 0)) (integerp m) (integerp m2) (<= m2 m) (natp j) (not (equal (ast-kind x) 0)))
           (not (anp-hfr fl x j m2)))
  :hints (("Goal" :induct (seq-ind j m2))))

(defthm hfr-0-open
  (implies (syntaxp (variablep x)) (equal (anp-hfr 0 x j m) (anp-hfr-node)))
  :hints (("Goal" :expand ((anp-hfr 0 x j m)))))

(defthm tr-no-frec
  (implies (not (anp-hfr (if (equal fl 4) 0 fl) x (if (equal fl 4) 0 j) (if (equal fl 4) 0 m)))
           (no-frec (tr fl x j m L os n)))
  :hints (("Goal" :induct (tr fl x j m L os n) :in-theory (disable fncap-evs cap-evs cap-list (:definition anp-hfr))
           :do-not (quote (generalize eliminate-destructors)) :do-not-induct t)))

; ---- APPLY_CLEARS IS SOUND ----------------------------------------------------------------------------

(defthm len-zeros (equal (len (zeros n)) (nfix n)))

(defthm fn-tr-once
  (implies (no-frec (tr 0 x 0 0 L (car os) n))
           (equal (fn-tr x L os n) (if (consp os) (tr 0 x 0 0 L (car os) n) nil))))

; a body with no recur to its fn runs once a call, and no read apply_clears
; marks is followed by a read of its slot in any run of it
(defthm anp-clears-sound
  (implies (and (natp n) (not (anp-hfr 0 x 0 0)))
           (ok-ann (fn-tr x (zeros n) os n) (zeros n) n))
  :hints (("Goal" :use ((:instance tr-no-frec (fl 0) (j 0) (m 0) (L (zeros n)) (os (car os)))
                        (:instance tr-sound (fl 0) (j 0) (m 0) (L (zeros n)) (os (car os)))))))

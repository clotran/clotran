; THE RUNS OF A NODE AND WHAT THEY READ, the first half of the argument
; model/anpass-sound.lisp finishes: LOCALS CLEARING IS SOUND, AND A RECUR IS LAST (model/anpass.lisp's
; passes, through their meaning in model/anpass-proof.lisp).
;
; THE RUNS: tr is the reads a node makes as exec.inc runs it, for every
; choice a run can make (the oracle o): an if's test then one branch; a
; case's test then its default or one branch; a try's body then its
; finally, or a prefix of the body (a throw) then one catch then the
; finally, or a prefix then the finally (the throw goes on); a loop's
; inits then its body again for as long as the body ends in its recur; a
; letfn's fns, their captures copied again, then its body; a def's init
; then its metadata; a fn, a lazy seq, a deftype's methods their
; captures; anything else its children in order; and fn-tr a fn's body
; again for every recur to the fn. A read is (slot . clear?), clear? the
; pass's decision at that read; a recur is (:recur . to-the-fn?).
;
;   tr-sound          no read annotated for clearing is followed by another
;                     read of its slot, in any run, nor is its slot live
;                     after the node
;   anp-clears-sound  the reads apply_clears marks (anp-clears-spec) are
;                     clearing reads of every run of the fn body, the recurs
;                     to the fn included, when its tail check passes
;   tr-tail           a node the tail check passes in position tt makes a
;                     recur only as the last thing it does, to its target
;                     (tt 1 the fn's, 2 a loop's), and none in 0 or 3

(in-package "ACL2")

(include-book "anpass-proof")

; ---- THE RUNS ---------------------------------------------------------------------------------

(defun anp-prefix (k l) (if (or (zp k) (atom l)) nil (cons (car l) (anp-prefix (- k 1) (cdr l)))))
(defun anp-init (l) (if (or (atom l) (atom (cdr l))) nil (cons (car l) (anp-init (cdr l)))))
(defun anp-last (l) (if (or (atom l) (atom (cdr l))) (if (consp l) (car l) nil) (anp-last (cdr l))))

; a fn's captures i .. k-1, read when the closure is made
(defun cap-evs (x i k)
  (declare (xargs :measure (nfix (- (nfix k) (nfix i)))))
  (if (and (natp i) (natp k) (< i k)) (cons (cons (ast-cap x i) nil) (cap-evs x (+ 1 i) k)) nil))

; letfn's fns i .. k-1, their captures copied again (exec.inc's refresh_captures,
; of each value that is a closure: a fn's)
(defun fncap-evs (x i k)
  (declare (xargs :measure (nfix (- (ifix k) (nfix i)))))
  (if (and (natp i) (integerp k) (< i k))
      (append (if (equal (ast-kind (ast-kid x i)) *n-fn*) (cap-evs (ast-kid x i) 0 (ast-ncaps (ast-kid x i))) nil)
              (fncap-evs x (+ 1 i) k))
    nil))

; fl 0 the node, L the live set after it; 1 and 3 its children or
; alternatives j .. m-1 in order, each with the live set the pass has after
; it; 4 a loop body x run while it ends in its recur
; the run of one node (fl 0), a macro so that its opener below says the same
(defmacro tr0-body ()
  (quote
    (let ((k (ast-kind x)) (o os))
      (cond
       ((or (equal k 0) (equal k *n-const*) (equal k *n-var*)) nil)
       ((equal k *n-local*)
        (let ((s (ast-i2 x)))
          (list (cons s (and (integerp s) (<= 0 s) (< s n) (equal (nth s L) 0))))))
       ((or (equal k *n-fn*) (equal k *n-lazy*)) (cap-evs x 0 (ast-ncaps x)))
       ((equal k *n-deftype*) (tr 3 x 0 (ast-nalts x) L (nth 1 o) n))
       ((equal k *n-if*)
        (append (tr 0 (ast-kid x 0) 0 0
                    (sp-or (sp-out 0 (ast-kid x 1) 0 0 nil L n) (sp-out 0 (ast-kid x 2) 0 0 nil L n)) (nth 1 o) n)
                (if (zp (nfix (car o))) (tr 0 (ast-kid x 1) 0 0 L (nth 2 o) n) (tr 0 (ast-kid x 2) 0 0 L (nth 3 o) n))))
       ((equal k *n-case*)
        (let ((c (nfix (car o))))
          (append (tr 0 (ast-kid x 0) 0 0
                      (sp-or (sp-out 2 x 0 (ast-nalts x) L L n) (sp-out 0 (ast-kid x 1) 0 0 nil L n)) (nth 1 o) n)
                  (if (zp c) (tr 0 (ast-kid x 1) 0 0 L (nth 2 o) n) (tr 0 (ast-alt x (- c 1)) 0 0 L (nth 2 o) n)))))
       ((equal k *n-try*)
        (let* ((L1 (sp-out 0 (ast-kid x 1) 0 0 nil L n))
               (bt (tr 0 (ast-kid x 0) 0 0 (sp-out 2 x 0 (ast-nalts x) L1 L1 n) (nth 1 o) n))
               (ft (tr 0 (ast-kid x 1) 0 0 L (nth 2 o) n))
               (cut (nfix (nth 4 o))))
          (cond ((zp (nfix (car o))) (append bt ft))
                ((equal (nfix (car o)) 1)
                 (append (anp-prefix cut bt) (tr 0 (ast-alt x (nfix (nth 5 o))) 0 0 L1 (nth 3 o) n) ft))
                (t (append (anp-prefix cut bt) ft)))))
       ((equal k *n-loop*)
        (let* ((nn (anp-nn x)) (bd (ast-kid x nn)) (L1 (sp-rd 0 bd 0 0 L n)))
          (append (tr 1 x 0 nn (sp-out 0 bd 0 0 nil L1 n) (nth 1 o) n) (tr 4 bd 0 0 L1 (nth 2 o) n))))
       ((equal k *n-letfn*)
        (let* ((nn (anp-nn x)) (L1 (sp-out 0 (ast-kid x nn) 0 0 nil L n)))
          (append (tr 1 x 0 nn (sp-fncaps x 0 nn L1 n) (nth 1 o) n) (fncap-evs x 0 nn)
                  (tr 0 (ast-kid x nn) 0 0 L (nth 2 o) n))))
       ((equal k *n-def*)
        (append (tr 1 x 0 (ast-nkids x) (sp-out 0 (ast-s3 x) 0 0 nil L n) (nth 1 o) n)
                (tr 0 (ast-s3 x) 0 0 L (nth 2 o) n)))
       ((equal k *n-recur*)
        (append (tr 1 x 0 (ast-nkids x) L (nth 1 o) n) (list (cons :recur (not (equal (ast-rfn x) 0))))))
       (t (tr 1 x 0 (ast-nkids x) L (nth 1 o) n))))))

(defun tr (fl x j m L os n)
  (declare (xargs :measure (anp-meas fl x j m os)))
  (cond
   ((equal fl 0)
    (tr0-body))
   ((equal fl 4)
    (if (consp os)
        (let ((tt (tr 0 x 0 0 L (car os) n)))
          (if (equal (anp-last tt) '(:recur)) (append (anp-init tt) (tr 4 x 0 0 L (cdr os) n)) tt))
      nil))
   (t
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (append (tr 0 (anp-ch fl x j) 0 0 (sp-out fl x (+ 1 j) m nil L n) (car os) n)
                (tr fl x (+ 1 j) m L (cdr os) n))
      nil))))

; a fn body, run again for every recur to the fn
(defun fn-tr (x L os n)
  (if (consp os)
      (let ((tt (tr 0 x 0 0 L (car os) n)))
        (if (equal (anp-last tt) '(:recur . t)) (append (anp-init tt) (fn-tr x L (cdr os) n)) tt))
    nil))

; ---- WHAT SOUND MEANS -------------------------------------------------------------------------

(defun rdp (e) (and (consp e) (integerp (car e))))

(defun slots (evs)
  (cond ((atom evs) nil)
        ((rdp (car evs)) (cons (caar evs) (slots (cdr evs))))
        (t (slots (cdr evs)))))

; every read marked for clearing reads a slot of the frame no later read
; reads, and that is not live after the run: L, the live set after it
(defun ok-ann (evs L n)
  (if (atom evs) t
    (and (implies (and (rdp (car evs)) (cdar evs))
                  (and (natp (caar evs)) (< (caar evs) n)
                       (not (member (caar evs) (slots (cdr evs))))
                       (equal (nth (caar evs) L) 0)))
         (ok-ann (cdr evs) L n))))

; ---- RUNS PUT TOGETHER ---------------------------------------------------------------------------

(defthm anp-member-append (iff (member x (append a b)) (or (member x a) (member x b))))
(defthm slots-append (equal (slots (append a b)) (append (slots a) (slots b))))

; the live set LA before b covers what b reads and what is live after it
(defun-sk dom (LA b L n)
  (forall s (implies (and (natp s) (< s n) (equal (nth s LA) 0))
                     (and (not (member s (slots b))) (equal (nth s L) 0)))))

(defthm ok-ann-append
  (implies (and (ok-ann a LA n) (ok-ann b L n) (dom LA b L n)) (ok-ann (append a b) L n))
  :hints (("Goal" :induct (ok-ann a LA n))
          ("Subgoal *1/2" :use ((:instance dom-necc (s (caar a)))))))

(defun no-ann (evs) (if (atom evs) t (and (not (and (rdp (car evs)) (cdar evs))) (no-ann (cdr evs)))))

(defthm ok-ann-no-ann (implies (no-ann a) (ok-ann a L n)))

(defthm ok-ann-append-no-ann (implies (and (no-ann a) (ok-ann b L n)) (ok-ann (append a b) L n)))

(defthm slots-prefix (implies (member s (slots (anp-prefix k a))) (member s (slots a))))
(defthm slots-prefix-not (implies (not (member s (slots a))) (not (member s (slots (anp-prefix k a))))))
(defthm ok-ann-prefix (implies (ok-ann a L n) (ok-ann (anp-prefix k a) L n)))
(defthm slots-init (implies (member s (slots (anp-init a))) (member s (slots a))))
(defthm slots-init-not (implies (not (member s (slots a))) (not (member s (slots (anp-init a))))))
(defthm ok-ann-init (implies (ok-ann a L n) (ok-ann (anp-init a) L n)))
(defthm no-ann-init (implies (no-ann a) (no-ann (anp-init a))))
(defthm no-ann-append (equal (no-ann (append a b)) (and (no-ann a) (no-ann b))))

; ---- THE LIVE SETS' SHAPE ------------------------------------------------------------------------

(defthm len-sp-set (implies (equal (len L) n) (equal (len (sp-set s L n)) n)))
(defthm len-sp-or (equal (len (sp-or A B)) (len A)))
(defthm len-sp-caps (implies (equal (len L) n) (equal (len (sp-caps x i k L n)) n)))
(defthm len-sp-fncaps (implies (equal (len L) n) (equal (len (sp-fncaps x i k L n)) n)))
(defthm len-sp-rd (implies (equal (len L) n) (equal (len (sp-rd fl x j m L n)) n)))
(defthm len-sp-out
  (implies (and (equal (len L) n) (or (not (equal fl 2)) (equal (len A) n)))
           (equal (len (sp-out fl x j m A L n)) n)))

(defun nth-or-ind (s A B) (if (or (zp s) (atom A)) (list A B) (nth-or-ind (- s 1) (cdr A) (cdr B))))

(defthm nth-sp-or
  (implies (and (natp s) (< s (len A)))
           (equal (nth s (sp-or A B)) (if (equal (nth s A) 0) (nth s B) 1)))
  :hints (("Goal" :induct (nth-or-ind s A B))))

; ---- WHAT STAYS LIVE ------------------------------------------------------------------------------

(defthm sp-set-mono
  (implies (and (natp s) (not (equal (nth s L) 0))) (not (equal (nth s (sp-set s2 L n)) 0))))
(defthm sp-caps-mono
  (implies (and (natp s) (not (equal (nth s L) 0))) (not (equal (nth s (sp-caps x i k L n)) 0))))
(defthm sp-fncaps-mono
  (implies (and (natp s) (not (equal (nth s L) 0))) (not (equal (nth s (sp-fncaps x i k L n)) 0))))
(defthm sp-rd-mono
  (implies (and (natp s) (not (equal (nth s L) 0))) (not (equal (nth s (sp-rd fl x j m L n)) 0))))

(defthm sp-out-mono
  (implies (and (natp s) (< s n) (equal (len L) n)
                (if (equal fl 2) (and (equal (len A) n) (not (equal (nth s A) 0))) (not (equal (nth s L) 0))))
           (not (equal (nth s (sp-out fl x j m A L n)) 0))))

; an alternative's live set is in their or
(defun alts-ind (x j m A L n)
  (declare (xargs :measure (nfix (- (ifix m) (nfix j)))))
  (if (and (natp j) (integerp m) (< j m))
      (alts-ind x (+ 1 j) m (sp-or (sp-out 0 (ast-alt x j) 0 0 nil L n) A) L n)
    (list x A L)))

(defthm sp-out-2-open
  (implies (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (sp-out 2 x j m A L n) (sp-out 2 x (+ 1 j) m (sp-or (sp-out 0 (ast-alt x j) 0 0 nil L n) A) L n))))

(defthm sp-out-2-done
  (implies (not (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m)))
           (equal (sp-out 2 x j m A L n) A)))

(defthm sp-out-alts
  (implies (and (not (equal (nth s (sp-out 0 (ast-alt x i) 0 0 nil L n)) 0))
                (natp s) (< s n) (equal (len L) n) (equal (len A) n) (natp i) (natp j) (integerp m) (<= j i) (< i m)
                (not (equal (ast-kind x) 0)))
           (not (equal (nth s (sp-out 2 x j m A L n)) 0)))
  :hints (("Goal" :induct (alts-ind x j m A L n))))

(in-theory (disable sp-out-2-open))

; ---- WHAT A NODE CAN READ -------------------------------------------------------------------------

(defun cap-list (x i k)
  (declare (xargs :measure (nfix (- (nfix k) (nfix i)))))
  (if (and (natp i) (natp k) (< i k)) (cons (ast-cap x i) (cap-list x (+ 1 i) k)) nil))

; the slots reads_in finds under a node, as a list
(defun rds (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k 0) nil)
              ((equal k *n-local*) (list (ast-i2 x)))
              ((or (equal k *n-fn*) (equal k *n-lazy*)) (cap-list x 0 (ast-ncaps x)))
              ((equal k *n-deftype*) (rds 3 x 0 (ast-nalts x)))
              ((equal k *n-try*) (append (rds 0 (ast-kid x 0) 0 0) (rds 3 x 0 (ast-nalts x)) (rds 0 (ast-kid x 1) 0 0)))
              ((equal k *n-case*) (append (rds 0 (ast-kid x 0) 0 0) (rds 0 (ast-kid x 1) 0 0) (rds 3 x 0 (ast-nalts x))))
              ((equal k *n-def*) (append (rds 0 (ast-s3 x) 0 0) (rds 1 x 0 (ast-nkids x))))
              (t (rds 1 x 0 (ast-nkids x)))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (append (rds 0 (anp-ch fl x j) 0 0) (rds fl x (+ 1 j) m))
      nil)))

(defthm rds-0-open
  (implies (syntaxp (variablep x))
           (equal (rds 0 x j m)
                  (let ((k (ast-kind x)))
                    (cond ((equal k 0) nil)
                          ((equal k *n-local*) (list (ast-i2 x)))
                          ((or (equal k *n-fn*) (equal k *n-lazy*)) (cap-list x 0 (ast-ncaps x)))
                          ((equal k *n-deftype*) (rds 3 x 0 (ast-nalts x)))
                          ((equal k *n-try*) (append (rds 0 (ast-kid x 0) 0 0) (rds 3 x 0 (ast-nalts x)) (rds 0 (ast-kid x 1) 0 0)))
                          ((equal k *n-case*) (append (rds 0 (ast-kid x 0) 0 0) (rds 0 (ast-kid x 1) 0 0) (rds 3 x 0 (ast-nalts x))))
                          ((equal k *n-def*) (append (rds 0 (ast-s3 x) 0 0) (rds 1 x 0 (ast-nkids x))))
                          (t (rds 1 x 0 (ast-nkids x))))))))

(defthm rds-seq-open
  (implies (and (not (equal fl 0)) (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (rds fl x j m) (append (rds 0 (anp-ch fl x j) 0 0) (rds fl x (+ 1 j) m)))))
(defthm rds-seq-done
  (implies (and (not (equal fl 0)) (not (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))))
           (equal (rds fl x j m) nil)))

(defthm sp-caps-sets
  (implies (and (natp s) (< s n) (equal (len L) n) (member s (cap-list x i k)))
           (not (equal (nth s (sp-caps x i k L n)) 0))))

(defthm rds-sp-rd
  (implies (and (natp s) (< s n) (equal (len L) n) (member s (rds fl x j m)))
           (not (equal (nth s (sp-rd fl x j m L n)) 0))))

(defthm slots-cap-evs (equal (slots (cap-evs x i k)) (cap-list x i k)))

(defthm cap-evs-no-ann (no-ann (cap-evs x i k)))

(defthm rds-nil (equal (rds 0 nil j m) nil) :hints (("Goal" :in-theory (enable ast-kind ast-p))))

(defthm rds-seq-in
  (implies (and (member s (rds 0 (anp-ch fl x i) 0 0)) (natp i) (natp j) (integerp m) (<= j i) (< i m)
                (not (equal (ast-kind x) 0)) (not (equal fl 0)) (not (equal fl 2)))
           (member s (rds fl x j m)))
  :hints (("Goal" :induct (rds fl x j m))))

(defthm ast-kid-out (implies (not (and (natp i) (< i (ast-nkids x)))) (equal (ast-kid x i) nil))
  :hints (("Goal" :in-theory (enable ast-kid))))
(defthm ast-alt-out (implies (not (and (natp i) (< i (ast-nalts x)))) (equal (ast-alt x i) nil))
  :hints (("Goal" :in-theory (enable ast-alt))))

(defthm rds-kid
  (implies (and (member s (rds 0 (ast-kid x i) 0 0)) (not (equal (ast-kind x) 0)))
           (member s (rds 1 x 0 (ast-nkids x))))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nkids x))))
           :use ((:instance rds-seq-in (fl 1) (j 0) (m (ast-nkids x)))))))

(defthm rds-alt
  (implies (and (member s (rds 0 (ast-alt x i) 0 0)) (not (equal (ast-kind x) 0)))
           (member s (rds 3 x 0 (ast-nalts x))))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nalts x))))
           :use ((:instance rds-seq-in (fl 3) (j 0) (m (ast-nalts x)))))))

(defun seq-ind (j m)
  (declare (xargs :measure (nfix (- (ifix m) (nfix j)))))
  (if (and (natp j) (integerp m) (< j m)) (seq-ind (+ 1 j) m) (list j m)))

(defthm rds-kids-range
  (implies (and (member s (rds 1 x j m)) (natp j) (not (equal (ast-kind x) 0)))
           (member s (rds 1 x 0 (ast-nkids x))))
  :hints (("Goal" :induct (seq-ind j m))))

(defthm rds-fn (implies (equal (ast-kind y) *n-fn*) (equal (rds 0 y 0 0) (cap-list y 0 (ast-ncaps y)))))

(defthm slots-fncap-evs-seq
  (implies (and (member s (slots (fncap-evs x i k))) (natp i) (not (equal (ast-kind x) 0)))
           (member s (rds 1 x i k)))
  :hints (("Goal" :induct (fncap-evs x i k))))

(defthm slots-fncap-evs
  (implies (and (member s (slots (fncap-evs x 0 k))) (not (equal (ast-kind x) 0)))
           (member s (rds 1 x 0 (ast-nkids x))))
  :hints (("Goal" :use ((:instance slots-fncap-evs-seq (i 0)) (:instance rds-kids-range (j 0) (m k))))))

(defthm fncap-evs-no-ann (no-ann (fncap-evs x i k)))

(defthm tr-0-open
  (implies (and (syntaxp (and (variablep x) (variablep os))) (equal fl 0)) (equal (tr fl x j m L os n) (tr0-body)))
  :hints (("Goal" :expand ((tr fl x j m L os n)))))

(defthm tr-seq-open
  (implies (and (syntaxp (variablep j)) (not (equal fl 0)) (not (equal fl 4)) (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (tr fl x j m L os n)
                  (append (tr 0 (anp-ch fl x j) 0 0 (sp-out fl x (+ 1 j) m nil L n) (car os) n)
                          (tr fl x (+ 1 j) m L (cdr os) n)))))
(defthm tr-seq-done
  (implies (and (not (equal fl 0)) (not (equal fl 4)) (not (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))))
           (equal (tr fl x j m L os n) nil)))
(defthm tr-4-open
  (implies (and (syntaxp (variablep os)) (equal fl 4))
           (equal (tr fl x j m L os n)
                  (if (consp os)
                      (let ((tt (tr 0 x 0 0 L (car os) n)))
                        (if (equal (anp-last tt) (quote (:recur))) (append (anp-init tt) (tr 4 x 0 0 L (cdr os) n)) tt))
                    nil))))

(in-theory (disable (:definition tr)))

; an induction on a run: each case opens the run of the node it is about, once
(defmacro defthm-tr (name body)
  `(defthm ,name ,body
     :hints (("Goal" :induct (tr fl x j m L os n) :in-theory (disable fncap-evs cap-evs cap-list)
              :do-not (quote (generalize eliminate-destructors)) :do-not-induct t))))

; every read a run makes, reads_in finds
(defthm-tr tr-rds
  (implies (member s (slots (tr fl x j m L os n)))
           (member s (rds (if (equal fl 4) 0 fl) x (if (equal fl 4) 0 j) (if (equal fl 4) 0 m)))))

; ---- THE LIVE SET BEFORE A NODE COVERS ITS RUNS ----------------------------------------------------

(defthm fncap-evs-sets
  (implies (and (natp s) (< s n) (equal (len L) n) (member s (slots (fncap-evs x i k))))
           (not (equal (nth s (sp-fncaps x i k L n)) 0)))
  :hints (("Goal" :induct (sp-fncaps x i k L n))))

(defthm sp-out-seq-open
  (implies (and (not (equal fl 0)) (not (equal fl 2)) (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (sp-out fl x j m A L n)
                  (sp-out fl x j (- m 1) nil (sp-out 0 (anp-ch fl x (- m 1)) 0 0 nil L n) n))))
(defthm sp-out-seq-done
  (implies (and (not (equal fl 0)) (not (equal fl 2)) (not (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))))
           (equal (sp-out fl x j m A L n) L)))

(defun front-ind (fl x j m L n)
  (declare (xargs :measure (nfix (- (ifix m) (nfix j)))))
  (if (and (natp j) (integerp m) (< (+ 1 j) m))
      (front-ind fl x j (- m 1) (sp-out 0 (anp-ch fl x (- m 1)) 0 0 nil L n) n)
    (list fl x j m L n)))

; the children j .. m-1, last first, are child j after the rest
(defthm sp-out-seq-front
  (implies (and (not (equal fl 0)) (not (equal fl 2)) (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
           (equal (sp-out fl x j m A L n)
                  (sp-out 0 (anp-ch fl x j) 0 0 nil (sp-out fl x (+ 1 j) m nil L n) n)))
  :hints (("Goal" :induct (front-ind fl x j m L n))))

(defthm tr-0-nil (equal (tr 0 nil j m L os n) nil)
  :hints (("Goal" :expand ((tr 0 nil j m L os n)) :in-theory (enable ast-kind ast-p))))

(defthm tr-alt-in-range
  (implies (member s (slots (tr 0 (ast-alt x i) j m L os n))) (and (natp i) (< i (ast-nalts x))))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nalts x))))))
  :rule-classes :forward-chaining)

(defthm tr-kid-in-range
  (implies (member s (slots (tr 0 (ast-kid x i) j m L os n))) (and (natp i) (< i (ast-nkids x))))
  :hints (("Goal" :cases ((and (natp i) (< i (ast-nkids x))))))
  :rule-classes :forward-chaining)

(defthm tr-4-rds
  (implies (member s (slots (tr 4 x j m L os n))) (member s (rds 0 x 0 0)))
  :hints (("Goal" :use ((:instance tr-rds (fl 4))))))

(defthm-tr tr-cover
  (implies (and (natp s) (< s n) (equal (len L) n) (not (equal fl 2)) (not (equal fl 4))
                (or (not (equal (nth s L) 0)) (member s (slots (tr fl x j m L os n)))))
           (not (equal (nth s (sp-out fl x j m nil L n)) 0))))

; SLICE 4a-4b of the ahead-of-time compiler (model/aot-PLAN.md): the emission of const local var if
; do let loop recur, boxed, PROVED against exec's ex-ev -- aot-cc-correct, vmic-correct's shape: on
; the subset (aot-s4), the pool holding what the host put there (aot-poolok: a constant, a Var, or
; a direct-linked Var's value, each below the first temporary n), when ex-ev answers (fuel left),
; running the code aot-cc emits with the same fuel answers ex-ev's value in the slot it names, or
; ex-ev's recur by the flag raised, with ex-ev's frame either way, and leaves every slot below n as
; it was. The induction is aot-cc-ind (aot-cc's recursion, the frame and slots the code before
; leaves, and a loop's next round on less fuel); one lemma per case (aot-cc-cl-*), its induction
; hypotheses as aot-cc-ind writes them.
;
; COST: the compile makes at most 2 + 6 acl2-count(e) calls -- linear in the tree (aot-cc-cost);
; a run takes at most aot-ir-size instructions with fuel + 1 rounds a loop (aot-ir-cost).

(in-package "ACL2")
(set-prover-step-limit 30000000)
(include-book "aot-ir")

(in-theory (disable ex-ev ex-kid-of c+))
(defthm aot-ex-ev-m-i
  (implies (syntaxp (not (and (equal i (quote (quote 0))) (equal tmp (quote (quote nil))))))
           (equal (ex-ev :m e i tmp fr fuel) (ex-ev :m e 0 nil fr fuel)))
  :hints (("Goal" :expand ((ex-ev :m e i tmp fr fuel) (ex-ev :m e 0 nil fr fuel)))))

; ---- RUNS ------------------------------------------------------------------------------------

(defthm aot-ir-run-append
  (equal (aot-ir-run (append a b) fr bt rp fuel)
         (let ((r (aot-ir-run a fr bt rp fuel))) (if (caddr r) (aot-ir-run b (car r) (cadr r) (cadddr r) fuel) r)))
  :hints (("Goal" :induct (aot-ir-run a fr bt rp fuel))))
(defthm aot-ir-run-nil (implies (not (consp code)) (equal (aot-ir-run code fr bt rp fuel) (list fr bt t rp))))
(defthm aot-ir-run-cons
  (equal (aot-ir-run (cons x code) fr bt rp fuel)
         (cond ((aot-isop x :if)
                (let ((r (aot-ir-run (if (truthy (nth (nfix (cadr x)) bt)) (caddr x) (cadddr x)) fr bt rp fuel)))
                  (if (caddr r) (aot-ir-run code (car r) (cadr r) (cadddr r) fuel) r)))
               ((aot-isop x :loop)
                (let ((r (aot-ir-run (cadr x) fr bt nil fuel)))
                  (cond ((not (caddr r)) r)
                        ((not (cadddr r)) (aot-ir-run code (car r) (cadr r) rp fuel))
                        ((zp fuel) (list (car r) (cadr r) nil nil))
                        (t (let ((r2 (aot-ir-run (list x) (car r) (cadr r) nil (1- fuel))))
                             (if (caddr r2) (aot-ir-run code (car r2) (cadr r2) rp fuel) r2))))))
               ((aot-isop x :recur) (aot-ir-run code fr bt t fuel))
               (t (let ((s (aot-ir-step x fr bt)))
                    (if s (aot-ir-run code (car s) (cadr s) rp fuel) (list fr bt nil rp)))))))
(in-theory (disable aot-ir-run))
; a loop that ends leaves the flag as it found it (each Fortran loop has its own)
(defthm aot-ir-loop-rp
  (implies (caddr (aot-ir-run (list (list :loop b)) fr bt rp fuel))
           (equal (cadddr (aot-ir-run (list (list :loop b)) fr bt rp fuel)) rp))
  :hints (("Goal" :expand ((aot-ir-run (list (list :loop b)) fr bt rp fuel)) :in-theory (disable aot-ir-run-cons))))

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

; every pool slot is below n; and holds what the host put there
(defun aot-pslt (pool n)
  (if (atom pool) t (and (consp (car pool)) (natp (cadr (car pool))) (< (cadr (car pool)) n) (aot-pslt (cdr pool) n))))
(defun aot-pval (ent) (if (and (equal (car (car ent)) 3) (not (caddr ent))) (list :var (cadr (car ent))) (cadr (car ent))))
(defun aot-poolok (pool bt)
  (if (atom pool) t (and (equal (nth (cadr (car pool)) bt) (aot-pval (car pool))) (aot-poolok (cdr pool) bt))))

(defthm aot-pslt-grows (implies (and (aot-pslt pool n) (<= n m)) (aot-pslt pool m)))
(defthm aot-inpool-lt (implies (and (aot-pslt pool n) (aot-inpool s pool)) (and (natp s) (< s n)))
  :rule-classes :forward-chaining)
(defthm aot-inpool-ge (implies (and (aot-pslt pool n) (natp s) (<= n s)) (not (aot-inpool s pool))))
(defthm aot-poolok-same
  (implies (and (aot-pslt pool n) (aot-poolok pool bt) (aot-same n bt2 bt) (natp n)) (aot-poolok pool bt2))
  :hints (("Goal" :induct (aot-poolok pool bt))
          (and stable-under-simplificationp (quote (:use ((:instance aot-nth-same (j (cadr (car pool))) (x bt2) (y bt))))))))
(defthm aot-pent-in
  (implies (and (consp (assoc-equal key pool)) (aot-pslt pool n)) (aot-inpool (cadr (assoc-equal key pool)) pool)))
(defthm aot-pent-val
  (implies (and (consp (assoc-equal key pool)) (aot-poolok pool bt))
           (equal (nth (cadr (assoc-equal key pool)) bt)
                  (if (and (equal (car key) 3) (not (caddr (assoc-equal key pool)))) (list :var (cadr key)) (cadr key)))))

(defthm aot-assoc-inpool
  (implies (consp (assoc-equal key pool)) (aot-inpool (cadr (assoc-equal key pool)) pool)))
(defthm aot-pent-inpool
  (implies (aot-pent e pool) (aot-inpool (cadr (aot-pent e pool)) pool)))
(defthm aot-pent-val2
  (implies (and (aot-pent e pool) (aot-poolok pool bt))
           (equal (nth (cadr (aot-pent e pool)) bt)
                  (if (and (equal (ex-kind e) 3) (not (caddr (aot-pent e pool)))) (list :var (ex-c e)) (ex-c e)))))
(defthm aot-pent-slot
  (implies (and (aot-pent e pool) (aot-pslt pool n)) (and (natp (cadr (aot-pent e pool))) (< (cadr (aot-pent e pool)) n)))
  :rule-classes ((:forward-chaining :trigger-terms ((aot-pent e pool))))
  :hints (("Goal" :use ((:instance aot-inpool-lt (s (cadr (aot-pent e pool))))) :in-theory (disable aot-inpool-lt))))
(defthm aot-pent-int
  (implies (and (aot-pent e pool) (aot-pslt pool n)) (and (integerp (cadr (aot-pent e pool))) (<= 0 (cadr (aot-pent e pool)))))
  :hints (("Goal" :use aot-pent-slot :in-theory (disable aot-pent-slot))))
(defthm aot-pent-kind (implies (and (not (equal (ex-kind e) 1)) (not (equal (ex-kind e) 3))) (not (aot-pent e pool))))
(in-theory (disable aot-pent ex-kind ex-i2 ex-c ex-mark ex-s2 ex-nk ex-rstart ex-rn))
(in-theory (disable (:definition aot-cc)))
; where the value lands: a fresh temporary, or a pool slot (and then, from gen, with no code)
(defthm aot-cc-atom-natp
  (implies (not (consp e)) (natp (caddr (aot-cc fl e i n pool)))) :rule-classes :type-prescription
  :hints (("Goal" :expand ((:free (fl i n) (aot-cc fl e i n pool))))))
(defthm aot-cc-atom
  (implies (not (consp e)) (<= (nfix n) (caddr (aot-cc fl e i n pool)))) :rule-classes :linear
  :hints (("Goal" :expand ((:free (fl i n) (aot-cc fl e i n pool))))))
(defthm aot-cc-next
  (and (natp (caddr (aot-cc fl e i n pool))) (<= (nfix n) (caddr (aot-cc fl e i n pool))))
  :rule-classes nil
  :hints (("Goal" :induct (aot-cc fl e i n pool) :expand ((:free (fl) (aot-cc fl e i n pool))))))
(defthm aot-cc-next-ge (<= (nfix n) (caddr (aot-cc fl e i n pool))) :rule-classes :linear
  :hints (("Goal" :use aot-cc-next)))
(defthm aot-cc-next-natp (natp (caddr (aot-cc fl e i n pool))) :rule-classes :type-prescription
  :hints (("Goal" :use aot-cc-next)))
(defun aot-slok (s n m pool) (or (and (natp s) (<= n s) (< s m)) (aot-inpool s pool)))
(defthm aot-slok-grow
  (implies (and (aot-slok s n m pool) (<= n2 n) (<= m m2) (rationalp m2)) (aot-slok s n2 m2 pool)))
(defthm aot-slok-fresh (implies (and (natp s) (<= n s) (< s m)) (aot-slok s n m pool)))
(defthm aot-slok-pool (implies (aot-inpool s pool) (aot-slok s n m pool)))
(in-theory (disable aot-slok))
(defmacro aot-sl (fl e i n) `(aot-slok (cadr (aot-cc ,fl ,e ,i ,n pool)) ,n (caddr (aot-cc ,fl ,e ,i ,n pool)) pool))
(defthm aot-sl-0 (implies (and (natp n) (aot-sl 1 e 0 n)) (aot-sl 0 e i n))
  :hints (("Goal" :expand ((aot-cc 0 e i n pool)) :in-theory (disable aot-slok-grow))))
(defthm aot-sl-1
  (implies (and (natp n)
                (implies (and (consp e) (equal (ex-kind e) 5) (not (zp (ex-nk e))) (not (aot-pent e pool))) (aot-sl 2 e 0 n))
                (implies (and (consp e) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (not (aot-pent e pool))) (aot-sl 3 e 0 n))
                (implies (and (consp e) (equal (ex-kind e) 16) (not (aot-pent e pool))) (aot-sl 4 e 0 n)))
           (aot-sl 1 e i n))
  :hints (("Goal" :expand ((aot-cc 1 e i n pool)))))
(defthm aot-sl-2
  (implies (and (natp n)
                (if (and (consp e) (< (+ 1 (nfix i)) (ex-nk e)))
                    (aot-sl 2 e (+ 1 (nfix i)) (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))
                  (implies (consp e) (aot-sl 0 (ex-kid-of e (nfix (- (ex-nk e) 1))) 0 n))))
           (aot-sl 2 e i n))
  :hints (("Goal" :expand ((aot-cc 2 e i n pool)))))
(defthm aot-sl-4
  (implies (and (natp n)
                (implies (and (consp e) (< (nfix i) (ex-nk e)))
                         (aot-sl 4 e (+ 1 (nfix i)) (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))))
           (aot-sl 4 e i n))
  :hints (("Goal" :expand ((aot-cc 4 e i n pool)))))
(defthm aot-sl-3
  (implies (and (natp n) (not (equal fl 0)) (not (equal fl 1)) (not (equal fl 2)) (not (equal fl 4))
                (if (and (consp e) (< (nfix i) (ex-i2 e)))
                    (aot-sl 3 e (+ 1 (nfix i)) (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))
                  (implies (consp e) (aot-sl 0 (ex-kid-of e (ex-i2 e)) 0 n))))
           (aot-sl fl e i n))
  :hints (("Goal" :expand ((aot-cc fl e i n pool)))))
(defthm aot-cc-slot1
  (implies (natp n) (aot-sl fl e i n))
  :hints (("Goal" :induct (aot-cc fl e i n pool) :do-not '(generalize fertilize eliminate-destructors))))
(defthm aot-cc-slot-0
  (let* ((cc (aot-cc 0 e i n pool)) (s (cadr cc)) (m (caddr cc)))
    (implies (and (natp n) (consp (car cc))) (and (natp s) (<= n s) (< s m))))
  :rule-classes ((:rewrite :corollary (implies (and (natp n) (consp (car (aot-cc 0 e i n pool)))) (integerp (cadr (aot-cc 0 e i n pool)))))
                 (:linear :corollary (implies (and (natp n) (consp (car (aot-cc 0 e i n pool)))) (<= n (cadr (aot-cc 0 e i n pool)))))
                 (:linear :corollary (implies (and (natp n) (consp (car (aot-cc 0 e i n pool))))
                                              (< (cadr (aot-cc 0 e i n pool)) (caddr (aot-cc 0 e i n pool))))))
  :hints (("Goal" :expand ((aot-cc 0 e i n pool)) :in-theory (enable aot-slok)
           :use ((:instance aot-cc-slot1 (fl 1) (i 0))))))
(defthm aot-cc-slot
  (let* ((cc (aot-cc fl e i n pool)) (s (cadr cc)) (m (caddr cc)))
    (implies (natp n)
             (and (natp m) (<= n m)
                  (or (and (natp s) (<= n s) (< s m)) (aot-inpool s pool))
                  (implies (and (equal fl 0) (consp (car cc))) (and (natp s) (<= n s) (< s m))))))
  :hints (("Goal" :in-theory (e/d (aot-slok) (aot-cc-slot-0)) :use (aot-cc-slot1 aot-cc-slot-0))))

(defthm aot-cc-slot-int
  (implies (and (natp n) (aot-pslt pool n)) (and (integerp (cadr (aot-cc fl e i n pool))) (<= 0 (cadr (aot-cc fl e i n pool)))))
  :rule-classes ((:rewrite :corollary (implies (and (natp n) (aot-pslt pool n)) (integerp (cadr (aot-cc fl e i n pool)))))
                 (:linear :corollary (implies (and (natp n) (aot-pslt pool n)) (<= 0 (cadr (aot-cc fl e i n pool))))))
  :hints (("Goal" :use (aot-cc-slot (:instance aot-inpool-lt (s (cadr (aot-cc fl e i n pool))))) :in-theory (disable aot-cc-slot aot-inpool-lt))))
(in-theory (disable aot-cc-slot))

; ---- A RECUR'S WRITES ------------------------------------------------------------------------
;
; aot-cc 4's fourth part: each argument's slot put into its local, its temporary let go. The
; values it writes are its arguments' slots as the code left them (aot-wvals); every temporary it
; lets go is at or above n and none a later put reads, so the run is ex-write's.

(defun aot-wvals (e i n pool bt)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (consp e) (< (nfix i) (ex-nk e)))
      (let ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))
        (cons (nth (cadr r) bt) (aot-wvals e (+ 1 (nfix i)) (caddr r) pool bt)))
    nil))

(defthm aot-cc-4-step
  (implies (and (consp e) (< (nfix i) (ex-nk e)))
           (equal (aot-cc 4 e i n pool)
                  (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 (nfix n) pool)) (r2 (aot-cc 4 e (+ 1 (nfix i)) (caddr r) pool)))
                    (list (append (car r) (car r2)) (cadr r2) (caddr r2)
                          (append (list (list :put (+ (ex-rstart e) (nfix i)) (cadr r)))
                                  (if (consp (car r)) (list (list :const (cadr r) nil)) nil)
                                  (cadddr r2))))))
  :hints (("Goal" :expand ((aot-cc 4 e i n pool)))))
(defthm aot-cc-4-end
  (implies (not (and (consp e) (< (nfix i) (ex-nk e))))
           (equal (aot-cc 4 e i n pool)
                  (if (consp e) (list nil (nfix n) (+ 1 (nfix n)) nil) (list (list (list :owed e)) (nfix n) (+ 1 (nfix n)) nil))))
  :hints (("Goal" :expand ((aot-cc 4 e i n pool)))))

(defthm aot-wvals-update
  (implies (and (natp n) (aot-pslt pool n) (natp d) (< d n) (not (aot-inpool d pool)))
           (equal (aot-wvals e i n pool (update-nth d v bt)) (aot-wvals e i n pool bt)))
  :hints (("Goal" :induct (aot-wvals e i n pool bt))
          ("Subgoal *1/1" :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))))))

(defun aot-w-ind (e i n pool bt fr)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (consp e) (< (nfix i) (ex-nk e)))
      (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) (s (cadr r)))
        (aot-w-ind e (+ 1 (nfix i)) (caddr r) pool
                   (if (consp (car r)) (update-nth s nil bt) bt)
                   (update-nth (+ (ex-rstart e) (nfix i)) (nth s bt) fr)))
    (list n pool bt fr)))

(defthm aot-writes-run
  (implies (and (natp n) (aot-pslt pool n))
           (let ((r (aot-ir-run (cadddr (aot-cc 4 e i n pool)) fr bt rp fuel)))
             (and (caddr r) (equal (cadddr r) rp)
                  (equal (car r) (ex-write (+ (ex-rstart e) (nfix i)) (aot-wvals e i n pool bt) fr))
                  (aot-same n (cadr r) bt))))
  :hints (("Goal" :induct (aot-w-ind e i n pool bt fr))
          ("Subgoal *1/1" :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))
                                (:instance aot-cc-slot-0 (e (ex-kid-of e (nfix i))) (i 0))))))

(defthm aot-wvals-true-listp (true-listp (aot-wvals e i n pool bt)))
(defthm aot-wvals-len (implies (consp e) (equal (len (aot-wvals e i n pool bt)) (nfix (- (ex-nk e) (nfix i))))))
(defthm aot-take-len (implies (and (true-listp x) (equal k (len x))) (equal (take k x) x)))
(defthm aot-append-assoc (equal (append (append a b) c) (append a (append b c))))
(defun aot-tk-ind (k x) (if (zp k) (list k x) (aot-tk-ind (- k 1) (cdr x))))
(defthm aot-take-append-nil (equal (take k (append x nil)) (take k x)) :hints (("Goal" :induct (aot-tk-ind k x))))

; ---- THE SUBSET ------------------------------------------------------------------------------

(defun aot-s4ok (e pool)
  (let ((k (ex-kind e)) (nk (ex-nk e)))
    (and (consp e) (member k '(1 2 3 4 5 11 12 16))
         (implies (equal k 4) (or (equal nk 2) (equal nk 3)))
         (implies (or (equal k 11) (equal k 12)) (equal nk (+ 1 (ex-i2 e))))
         (implies (equal k 16) (equal (ex-rn e) nk))
         (implies (equal k 3) (consp (aot-pent e pool))))))
(defun aot-s4 (fl e j pool)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (if (equal fl 0) 2 1) (nfix (- (ex-nk e) (nfix j)))))
                  :well-founded-relation o<))
  (if (equal fl 0)
      (and (aot-s4ok e pool) (aot-s4 1 e 0 pool))
    (if (and (consp e) (natp j) (< j (ex-nk e))) (and (aot-s4 0 (ex-kid-of e j) 0 pool) (aot-s4 1 e (+ 1 j) pool)) t)))

(defun aot-s4-ind (e i) (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (natp i) (< i (ex-nk e))) (aot-s4-ind e (+ 1 i)) (list e i)))
(defthm aot-s4-kid1
  (implies (and (aot-s4 1 e i pool) (natp i) (natp j) (<= i j) (< j (ex-nk e)) (consp e)) (aot-s4 0 (ex-kid-of e j) 0 pool))
  :hints (("Goal" :induct (aot-s4-ind e i) :in-theory (disable aot-s4) :expand ((aot-s4 1 e i pool)))))
(defthm aot-s4-0 (equal (aot-s4 0 e j pool) (and (aot-s4ok e pool) (aot-s4 1 e 0 pool)))
  :hints (("Goal" :in-theory (disable aot-s4) :expand ((aot-s4 0 e j pool)))))
(defthm aot-s4-kid
  (implies (and (aot-s4 0 e 0 pool) (natp j) (< j (ex-nk e))) (aot-s4 0 (ex-kid-of e j) 0 pool))
  :hints (("Goal" :use ((:instance aot-s4-kid1 (i 0))) :in-theory (disable aot-s4-kid1 aot-s4))))
(defthm aot-s4-ok (implies (aot-s4 0 e j pool) (aot-s4ok e pool)) :rule-classes :forward-chaining)
(in-theory (disable aot-s4 aot-s4-0))
(defthm aot-s4-kind
  (implies (aot-s4 0 e 0 pool) (and (consp e) (member (ex-kind e) '(1 2 3 4 5 11 12 16))))
  :rule-classes :forward-chaining :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok))))

(defthm aot-s4-var (implies (and (aot-s4 0 e 0 pool) (equal (ex-kind e) 3)) (aot-pent e pool))
  :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok))))

(defthm aot-s4-shape
  (implies (aot-s4 0 e 0 pool)
           (and (implies (equal (ex-kind e) 4)
                         (and (<= 2 (ex-nk e)) (<= (ex-nk e) 3)
                              (aot-s4 0 (ex-kid-of e 0) 0 pool) (aot-s4 0 (ex-kid-of e 1) 0 pool)
                              (implies (< 2 (ex-nk e)) (aot-s4 0 (ex-kid-of e 2) 0 pool))))
                (implies (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (equal (ex-nk e) (+ 1 (ex-i2 e))))
                (implies (equal (ex-kind e) 16) (equal (ex-rn e) (ex-nk e)))))
  :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok))))

; ---- THE STATEMENT ---------------------------------------------------------------------------

(defun aot-ccflg (fl) (case fl (2 :do) (3 :let) (4 :rec) (otherwise :m)))
(defun aot-cchyp (fl e i n pool bt)
  (and (natp n) (aot-s4 0 e 0 pool) (aot-pslt pool n) (aot-poolok pool bt)
       (case fl
         (2 (and (equal (ex-kind e) 5) (natp i) (< i (ex-nk e))))
         (3 (and (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (natp i) (<= i (ex-i2 e))))
         (4 (and (equal (ex-kind e) 16) (natp i) (<= i (ex-nk e))))
         (otherwise t))))
; when ex-ev answers: the code runs to the end, slots below n kept; a recur's arguments (fl 4)
; leave the frame ex-ev writes them into and their values for the writes; anything else its value
; in its slot, or its recur by the flag, and ex-ev's frame
(defun aot-ccconcl (fl e i n pool fr bt fuel tmp)
  (let* ((cc (aot-cc fl e i n pool)) (r (aot-ir-run (car cc) fr bt nil fuel)) (x (ex-ev (aot-ccflg fl) e i tmp fr fuel)))
    (implies (not (equal (car x) (list :out)))
             (and (caddr r)
                  (aot-same n (cadr r) bt)
                  (if (equal fl 4)
                      (and (not (cadddr r))
                           (equal (car x) (list :recur))
                           (equal (cadr x) (ex-write (ex-rstart e) (take (min (ex-rn e) (ex-nk e)) (append tmp (aot-wvals e i n pool (cadr r))))
                                                     (car r))))
                    (and (equal (car x) (if (cadddr r) (list :recur) (cons :val (nth (cadr cc) (cadr r)))))
                         (equal (cadr x) (car r))))))))
(defun aot-cc-cl (fl e i n pool fr bt fuel tmp)
  (implies (aot-cchyp fl e i n pool bt) (aot-ccconcl fl e i n pool fr bt fuel tmp)))
(in-theory (disable aot-cchyp aot-ccconcl aot-cc-cl))

(defun aot-cc-ind (fl e i n pool fr bt fuel tmp)
  (declare (irrelevant n pool fr bt tmp))
  (declare (xargs :ruler-extenders :all :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (aot-ccrank fl)) (aot-ccleft fl e i))))
                  :well-founded-relation o<))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n (nfix n)) (i (nfix i)))
    (case fl
      (0 (aot-cc-ind 1 e 0 n pool fr bt fuel nil))
      (1 (cond ((not (consp e)) nil)
               ((equal k 5) (if (zp nk) nil (aot-cc-ind 2 e 0 n pool fr bt fuel nil)))
               ((or (equal k 11) (equal k 12)) (aot-cc-ind 3 e 0 n pool fr bt fuel nil))
               ((equal k 16) (aot-cc-ind 4 e 0 n pool fr bt fuel nil))
               ((equal k 4)
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (list (aot-cc-ind 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                        (aot-cc-ind 0 (ex-kid-of e 1) 0 (+ 1 r) pool (car r0) bt1 fuel nil)
                        (aot-cc-ind 0 (ex-kid-of e 2) 0 m pool (car r0) bt1 fuel nil))))
               (t nil)))
      (2 (if (and (consp e) (< (+ 1 i) nk))
             (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
               (list (aot-cc-ind 0 (ex-kid-of e i) 0 n pool fr bt fuel nil)
                     (aot-cc-ind 2 e (+ 1 i) (caddr r) pool (car r0) (cadr r0) fuel tmp)))
           (if (consp e) (aot-cc-ind 0 (ex-kid-of e (nfix (- nk 1))) 0 n pool fr bt fuel nil) nil)))
      (4 (if (and (consp e) (< i nk))
             (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
               (list (aot-cc-ind 0 (ex-kid-of e i) 0 n pool fr bt fuel nil)
                     (aot-cc-ind 4 e (+ 1 i) (caddr r) pool (car r0) (cadr r0) fuel
                                 (append tmp (list (nth (cadr r) (cadr r0)))))))
           nil))
      (otherwise
       (if (and (consp e) (< i (ex-i2 e)))
           (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
             (list (aot-cc-ind 0 (ex-kid-of e i) 0 n pool fr bt fuel nil)
                   (aot-cc-ind 3 e (+ 1 i) (caddr r) pool
                               (update-nth (+ (ex-s2 e) i) (nth (cadr r) (cadr r0)) (car r0))
                               (if (consp (car r)) (update-nth (cadr r) nil (cadr r0)) (cadr r0)) fuel tmp)))
         (if (consp e)
             (let* ((b (ex-kid-of e (ex-i2 e))) (r0 (aot-ir-run (car (aot-cc 0 b 0 n pool)) fr bt nil fuel)))
               (list (aot-cc-ind 0 b 0 n pool fr bt fuel nil)
                     (if (and (equal k 12) (not (zp fuel)))
                         (aot-cc-ind 3 e i n pool (car r0) (cadr r0) (1- fuel) tmp)
                       nil)))
           nil))))))

; ---- THE CASES -------------------------------------------------------------------------------

(defmacro aot-cc-theory (&rest more) `(enable aot-cc-cl aot-cchyp aot-ccconcl ,@more))

(defthm aot-cc-cl-0
  (implies (aot-cc-cl 1 e 0 n pool fr bt fuel nil) (aot-cc-cl 0 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 0 e i n pool))
           :use ((:instance aot-cc-slot (fl 1) (i 0))))))

(defthm aot-cc-cl-leaf
  (implies (and (member (ex-kind e) '(1 2 3)) (member fl '(1)))
           (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel))
           :use ((:instance aot-pent-slot) (:instance aot-pent-inpool)))))

(defthm aot-cc-cl-do
  (implies (and (equal (ex-kind e) 5) (aot-cc-cl 2 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel) (ex-ev :do e 0 nil fr fuel)))))

(defthm aot-cc-cl-let
  (implies (and (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (aot-cc-cl 3 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel)))))

(defthm aot-cc-cl-recur
  (implies (and (equal (ex-kind e) 16) (aot-cc-cl 4 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel))
           :use ((:instance aot-writes-run (i 0) (n n) (fr (car (aot-ir-run (car (aot-cc 4 e 0 n pool)) fr bt nil fuel)))
                            (bt (cadr (aot-ir-run (car (aot-cc 4 e 0 n pool)) fr bt nil fuel))) (rp nil))
                 (:instance aot-s4-shape)
                 (:instance aot-same-trans
                            (x (cadr (aot-ir-run (cadddr (aot-cc 4 e 0 n pool)) (car (aot-ir-run (car (aot-cc 4 e 0 n pool)) fr bt nil fuel))
                                                 (cadr (aot-ir-run (car (aot-cc 4 e 0 n pool)) fr bt nil fuel)) nil fuel)))
                            (y (cadr (aot-ir-run (car (aot-cc 4 e 0 n pool)) fr bt nil fuel))) (z bt))))))

; a recur never answers a value (so an if's branch that is one needs no copy)
(defun aot-rec-ind (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (consp e) (< (nfix i) (ex-nk e)))
      (let ((r (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (aot-rec-ind e (+ 1 (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel))
    (list tmp fr)))
(defthm aot-rec-notval (not (equal (car (car (ex-ev :rec e i tmp fr fuel))) :val))
  :hints (("Goal" :induct (aot-rec-ind e i tmp fr fuel) :expand ((ex-ev :rec e i tmp fr fuel)))))
(defthm aot-recur-notval
  (implies (equal (ex-kind e) 16) (not (equal (car (ex-ev :m e 0 nil fr fuel)) (cons :val v))))
  :hints (("Goal" :expand ((ex-ev :m e 0 nil fr fuel)) :use ((:instance aot-rec-notval (i 0) (tmp nil))) :in-theory (disable aot-rec-notval))))

; a value answer, read through its equality
(defthm aot-val-car (implies (equal a (cons :val v)) (equal (car a) :val)))
(defthm aot-val-cdr (implies (equal a (cons :val v)) (equal (cdr a) v)))

; an if: the test, then the branch it takes
(defthm aot-cc-cl-if-then
  (implies (and (equal (ex-kind e) 4) (truthy (val (car (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel))))
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0))))
                  (and (aot-cc-cl 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 1) 0 (+ 1 r) pool (car r0) bt1 fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel))
           :do-not '(generalize fertilize))))

(defthm aot-cc-cl-if-else
  (implies (and (equal (ex-kind e) 4) (not (truthy (val (car (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))))
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (and (aot-cc-cl 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 2) 0 m pool (car r0) bt1 fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel))
           :do-not '(generalize fertilize))))

(defthm aot-cc-cl-if
  (implies (and (equal (ex-kind e) 4)
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (and (aot-cc-cl 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 1) 0 (+ 1 r) pool (car r0) bt1 fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 2) 0 m pool (car r0) bt1 fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((truthy (val (car (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel))))) :in-theory (disable aot-cc-cl))))

(defthm aot-cc-cl-do-mid
  (implies (and (< (+ 1 (nfix i)) (ex-nk e))
                (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
                  (and (aot-cc-cl 0 (ex-kid-of e (nfix i)) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 2 e (+ 1 (nfix i)) (caddr r) pool (car r0) (cadr r0) fuel tmp))))
           (aot-cc-cl 2 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 2 e i n pool) (ex-ev :do e i tmp fr fuel))
           :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))))))

(defthm aot-cc-cl-do-last
  (implies (and (not (< (+ 1 (nfix i)) (ex-nk e)))
                (aot-cc-cl 0 (ex-kid-of e (nfix (- (ex-nk e) 1))) 0 n pool fr bt fuel nil))
           (aot-cc-cl 2 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 2 e i n pool) (ex-ev :do e i tmp fr fuel)))))

(defthm aot-cc-cl-rec-mid
  (implies (and (< (nfix i) (ex-nk e))
                (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
                  (and (aot-cc-cl 0 (ex-kid-of e (nfix i)) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 4 e (+ 1 (nfix i)) (caddr r) pool (car r0) (cadr r0) fuel
                                  (append tmp (list (nth (cadr r) (cadr r0))))))))
           (aot-cc-cl 4 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((ex-ev :rec e i tmp fr fuel)
                                                     (aot-wvals e i n pool (cadr (aot-ir-run (car (aot-cc 4 e i n pool)) fr bt nil fuel))))
           :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))))
          (and stable-under-simplificationp
               '(:use ((:instance aot-nth-same (j (cadr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))
                        (n (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))
                        (x (cadr (aot-ir-run (car (aot-cc 4 e (+ 1 (nfix i)) (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) pool))
                                             (car (aot-ir-run (car (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) fr bt nil fuel))
                                             (cadr (aot-ir-run (car (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) fr bt nil fuel))
                                             nil fuel)))
                        (y (cadr (aot-ir-run (car (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) fr bt nil fuel)))))))))

(defthm aot-cc-cl-rec-end
  (implies (not (< (nfix i) (ex-nk e))) (aot-cc-cl 4 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 4 e i n pool) (ex-ev :rec e i tmp fr fuel)
                                                     (:free (bt) (aot-wvals e i n pool bt))))))

(defthm aot-cc-cl-let-mid
  (implies (and (< (nfix i) (ex-i2 e))
                (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
                  (and (aot-cc-cl 0 (ex-kid-of e (nfix i)) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 3 e (+ 1 (nfix i)) (caddr r) pool
                                  (update-nth (+ (ex-s2 e) (nfix i)) (nth (cadr r) (cadr r0)) (car r0))
                                  (if (consp (car r)) (update-nth (cadr r) nil (cadr r0)) (cadr r0)) fuel tmp))))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 3 e i n pool) (ex-ev :let e i tmp fr fuel))
           :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))))))

(defthm aot-cc-cl-let-body
  (implies (and (not (< (nfix i) (ex-i2 e))) (not (equal (ex-kind e) 12))
                (aot-cc-cl 0 (ex-kid-of e (ex-i2 e)) 0 n pool fr bt fuel nil))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 3 e i n pool) (ex-ev :let e i tmp fr fuel)))))

; a loop's body: ex-ev's :iter, its rounds the :loop's
(defthm aot-ev-loop-end
  (implies (and (consp e) (equal (ex-kind e) 12) (not (< (nfix i) (ex-i2 e))))
           (and (equal (car (ex-ev :let e i tmp fr fuel)) (car (ex-ev :iter (ex-kid-of e (ex-i2 e)) 0 nil fr fuel)))
                (equal (cadr (ex-ev :let e i tmp fr fuel)) (cadr (ex-ev :iter (ex-kid-of e (ex-i2 e)) 0 nil fr fuel)))))
  :hints (("Goal" :expand ((ex-ev :let e i tmp fr fuel)))))
(defthm aot-ev-iter
  (implies (consp b)
           (equal (ex-ev :iter b 0 nil fr fuel)
                  (let* ((r (ex-ev :m b 0 nil fr fuel)) (res (car r)))
                    (cond ((not (eq (car res) :recur)) r)
                          ((zp fuel) (list (list :out) fr 0))
                          (t (let ((r2 (ex-ev :iter b 0 nil (cadr r) (1- fuel))))
                               (list (car r2) (cadr r2) (c+ (caddr r) (caddr r2)))))))))
  :hints (("Goal" :expand ((ex-ev :iter b 0 nil fr fuel)))))
(defthm aot-cc-3-loop
  (implies (and (consp e) (equal (ex-kind e) 12) (not (< (nfix i) (ex-i2 e))))
           (equal (aot-cc 3 e i n pool)
                  (let ((rb (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 (nfix n) pool)))
                    (list (list (list :loop (car rb))) (cadr rb) (caddr rb)))))
  :hints (("Goal" :expand ((aot-cc 3 e i n pool)))))

(defthm aot-cc-cl-loop
  (implies (and (not (< (nfix i) (ex-i2 e))) (equal (ex-kind e) 12)
                (aot-cc-cl 0 (ex-kid-of e (ex-i2 e)) 0 n pool fr bt fuel nil)
                (implies (not (zp fuel))
                         (let ((r0 (aot-ir-run (car (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 n pool)) fr bt nil fuel)))
                           (aot-cc-cl 3 e i n pool (car r0) (cadr r0) (1- fuel) tmp))))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  ; the :loop opened once: its next round is the hypothesis, on less fuel, not opened again
  :hints (("Goal" :in-theory (e/d (aot-cc-cl aot-cchyp aot-ccconcl) (aot-ir-run-cons aot-s4-kid aot-s4-shape aot-ev-iter))
           :expand ((aot-ir-run (list (list :loop (car (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 n pool)))) fr bt nil fuel))
           :use ((:instance aot-s4-kid (j (ex-i2 e))) (:instance aot-s4-shape) (:instance aot-ev-iter (b (ex-kid-of e (ex-i2 e))))))
          (and stable-under-simplificationp
               '(:use ((:instance aot-poolok-same (bt2 (cadr (aot-ir-run (car (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 n pool)) fr bt nil fuel)))))))))

(defthm aot-cc-cl-3-badi (implies (not (natp i)) (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory))))
; a let's or loop's body, as aot-cc-ind gives its hypotheses
(defthm aot-cc-cl-let-end
  (implies (and (not (< (nfix i) (ex-i2 e)))
                (aot-cc-cl 0 (ex-kid-of e (ex-i2 e)) 0 n pool fr bt fuel nil)
                (implies (and (equal (ex-kind e) 12) (not (zp fuel)))
                         (let ((r0 (aot-ir-run (car (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 n pool)) fr bt nil fuel)))
                           (aot-cc-cl 3 e (nfix i) n pool (car r0) (cadr r0) (1- fuel) tmp))))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((not (natp i)) (equal (ex-kind e) 12)) :in-theory (disable aot-cc-cl))))

(defthm aot-cc-cl-badkind
  (implies (not (member (ex-kind e) '(1 2 3 4 5 11 12 16))) (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :use (aot-s4-kind))))
(defthm aot-cc-cl-1-leaf
  (implies (not (member (ex-kind e) '(4 5 11 12 16))) (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((member (ex-kind e) '(1 2 3))) :in-theory (disable aot-cc-cl))))
(defthm aot-cc-cl-do0
  (implies (and (equal (ex-kind e) 5) (consp e) (equal (ex-nk e) 0)) (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (ex-ev :m e 0 nil fr fuel) (ex-ev :do e 0 nil fr fuel)))))
(defthm aot-cc-cl-badn (implies (not (natp n)) (aot-cc-cl fl e i n pool fr bt fuel tmp)) :hints (("Goal" :in-theory (aot-cc-theory))))
(defthm aot-cc-cl-other
  (implies (and (member fl '(0 1 2 3 4)) (not (consp e))) (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory))))

; ---- THE THEOREM -----------------------------------------------------------------------------

(defthm aot-cc-sound
  (implies (member fl '(0 1 2 3 4)) (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :induct (aot-cc-ind fl e i n pool fr bt fuel tmp) :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (disable aot-cc-slot))))

; THE HEADLINE: a node of the subset, the pool as the host fills it, below the first temporary n:
; when ex-ev answers, the emitted code run on the same fuel runs to the end, its value in the slot
; aot-cc names is ex-ev's (or ex-ev's recur is the flag raised), the frame is ex-ev's, and no slot
; below n moved
(defthm aot-cc-correct
  (let* ((cc (aot-cc 0 e 0 n pool)) (r (aot-ir-run (car cc) fr bt nil fuel)) (x (ex-ev :m e 0 nil fr fuel)))
    (implies (and (aot-s4 0 e 0 pool) (natp n) (aot-pslt pool n) (aot-poolok pool bt)
                  (not (equal (car x) (list :out))))
             (and (caddr r)
                  (equal (car x) (if (cadddr r) (list :recur) (cons :val (nth (cadr cc) (cadr r)))))
                  (equal (cadr x) (car r))
                  (aot-same n (cadr r) bt))))
  :hints (("Goal" :use ((:instance aot-cc-sound (fl 0) (i 0) (tmp nil))) :in-theory (e/d (aot-cc-cl aot-cchyp aot-ccconcl) (aot-cc-sound)))))

;; ---- COST of a run (before arithmetic-5: aot-lmul kept closed) ----
; A RUN: every instruction once, a loop's body once a round, at most fuel + 1 rounds a loop
(defthm aot-lmul-natp (natp (aot-lmul k b)) :rule-classes :type-prescription)
(defthm aot-lmul-1+ (implies (natp f) (equal (aot-lmul (+ 1 f) b) (+ 1 (nfix b) (aot-lmul f b)))))
(defthm aot-lmul-mono-b (implies (<= (nfix b) (nfix b2)) (<= (aot-lmul f b) (aot-lmul f b2))) :rule-classes :linear
  :hints (("Goal" :nonlinearp t)))
(defthm aot-lmul-mono-k (implies (<= (nfix j) (nfix k)) (<= (aot-lmul j b) (aot-lmul k b))) :rule-classes :linear
  :hints (("Goal" :nonlinearp t)))
(in-theory (disable aot-lmul))
(defthm aot-ir-size-natp (natp (aot-ir-size code k)) :rule-classes :type-prescription)
(defthm aot-ir-size-mono
  (implies (and (natp j) (natp k) (<= j k)) (<= (aot-ir-size code j) (aot-ir-size code k)))
  :rule-classes nil
  :hints (("Goal" :induct (aot-ir-size code j))
          (and stable-under-simplificationp
               '(:use ((:instance aot-lmul-mono-k (b (aot-ir-size (cadr (car code)) k)))
                       (:instance aot-lmul-mono-b (f j) (b (aot-ir-size (cadr (car code)) j)) (b2 (aot-ir-size (cadr (car code)) k))))))))
(defthm aot-ir-size-mono-fuel
  (implies (natp f) (<= (aot-ir-size code f) (aot-ir-size code (+ 1 f)))) :rule-classes :linear
  :hints (("Goal" :use ((:instance aot-ir-size-mono (j f) (k (+ 1 f)))))))
(defthm aot-ir-cost
  (<= (aot-ir-steps code fr bt rp fuel) (aot-ir-size code (+ 1 (nfix fuel)))) :rule-classes :linear
  :hints (("Goal" :induct (aot-ir-steps code fr bt rp fuel) :in-theory (disable aot-ir-run-cons)
           :expand ((aot-ir-steps code fr bt rp fuel) (aot-ir-size code (+ 1 (nfix fuel))) (:free (k) (aot-ir-size (list (car code)) k))))
          (and stable-under-simplificationp
               '(:use ((:instance aot-lmul-mono-b (f (nfix fuel)) (b (aot-ir-size (cadr (car code)) (nfix fuel)))
                                  (b2 (aot-ir-size (cadr (car code)) (+ 1 (nfix fuel)))))
                       (:instance aot-ir-size-mono-fuel (code (cadr (car code))) (f (nfix fuel))))))))

(local (include-book "arithmetic-5/top" :dir :system))

; ---- COST ------------------------------------------------------------------------------------

(defthm aot-ac-nth (<= (acl2-count (nth j l)) (acl2-count l)) :rule-classes :linear)
(defun aot-kc (e i) (acl2-count (nthcdr (nfix i) (ex-kids e))))
(defthm aot-ac-nthcdr
  (implies (and (natp i) (< i (len l)))
           (equal (acl2-count (nthcdr i l)) (+ 1 (acl2-count (nth i l)) (acl2-count (nthcdr (+ 1 i) l)))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nth nthcdr))))
(defthm aot-kc-step
  (implies (and (natp i) (< i (ex-nk e)))
           (equal (aot-kc e i) (+ 1 (acl2-count (ex-kid-of e i)) (aot-kc e (+ 1 i)))))
  :hints (("Goal" :in-theory (enable ex-kid-of ex-nk aot-kc))))
(defthm aot-kc-last
  (implies (and (natp i) (< i (ex-nk e))) (< (acl2-count (ex-kid-of e i)) (aot-kc e i))) :rule-classes :linear
  :hints (("Goal" :use aot-kc-step :in-theory (disable aot-kc-step aot-kc))))
(defthm aot-kc-0
  (implies (consp e) (<= (+ (ex-i2 e) (aot-kc e 0) 1) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :in-theory (enable ex-kind ex-i2 ex-kids nth))))
(defthm aot-kc-kid
  (implies (and (natp j) (consp e)) (<= (+ 1 (acl2-count (ex-kid-of e j))) (+ 1 (aot-kc e 0)))) :rule-classes :linear
  :hints (("Goal" :in-theory (enable ex-kid-of nth))))
(defthm aot-ac-3 (<= (+ (acl2-count (car l)) (acl2-count (cadr l)) (acl2-count (caddr l))) (acl2-count l)) :rule-classes :linear
  :hints (("Goal" :expand ((acl2-count l) (acl2-count (cdr l)) (acl2-count (cddr l))))))
(defthm aot-kc-if
  (implies (and (consp e) (<= (ex-nk e) 3))
           (<= (+ (acl2-count (ex-kid-of e 0)) (acl2-count (ex-kid-of e 1)) (acl2-count (ex-kid-of e 2))) (aot-kc e 0)))
  :rule-classes :linear :hints (("Goal" :use ((:instance aot-ac-3 (l (nth 2 e)))) :in-theory (e/d (ex-kid-of ex-kids ex-nk aot-kc) (aot-ac-3)) :expand ((nth 1 (nth 2 e)) (nth 2 (nth 2 e)) (nth 1 (cdr (nth 2 e)))))))
(defthm aot-ac-cdr-nthcdr (<= (acl2-count (nthcdr i (cdr l))) (acl2-count (nthcdr i l))) :rule-classes :linear
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr))))
(defthm aot-kc-mono (implies (natp i) (<= (aot-kc e (+ 1 i)) (aot-kc e i))) :rule-classes :linear
  :hints (("Goal" :in-theory (enable ex-kids))))
(defthm aot-ac-nth-nthcdr
  (<= (+ (acl2-count (nth i l)) (acl2-count (nthcdr (+ 1 (nfix i)) l))) (acl2-count (nthcdr i l))) :rule-classes :linear
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nth nthcdr))))
(defthm aot-kc-split
  (implies (natp i) (<= (+ (acl2-count (ex-kid-of e i)) (aot-kc e (+ 1 i))) (aot-kc e i))) :rule-classes :linear
  :hints (("Goal" :use ((:instance aot-ac-nth-nthcdr (l (ex-kids e)))) :in-theory (e/d (ex-kid-of) (aot-ac-nth-nthcdr)))))
(defthm aot-ac-i2 (equal (acl2-count (ex-i2 e)) (ex-i2 e)) :hints (("Goal" :in-theory (enable ex-i2))))
(in-theory (disable aot-kc))

(defthm aot-kc-nth
  (implies (natp i) (<= (acl2-count (ex-kid-of e i)) (aot-kc e i))) :rule-classes :linear
  :hints (("Goal" :use aot-kc-split :in-theory (disable aot-kc-split))))

(defthm aot-cc-cnt-bound
  (and (implies (equal fl 0) (<= (aot-cc-cnt fl e i) (+ 2 (* 6 (acl2-count e)))))
       (implies (equal fl 1) (<= (aot-cc-cnt fl e i) (+ 1 (* 6 (acl2-count e)))))
       (implies (and (equal fl 2) (natp i) (< i (ex-nk e))) (<= (aot-cc-cnt fl e i) (* 6 (aot-kc e i))))
       (implies (and (equal fl 4) (natp i)) (<= (aot-cc-cnt fl e i) (+ 1 (* 6 (aot-kc e i)))))
       (implies (and (equal fl 3) (natp i) (<= i (ex-i2 e)))
                (<= (aot-cc-cnt fl e i) (+ 3 (* 6 (aot-kc e i)) (* 3 (- (ex-i2 e) i))))))
  :rule-classes nil
  :hints (("Goal" :induct (aot-cc-cnt fl e i) :expand ((aot-cc-cnt fl e i)))
          (and stable-under-simplificationp
               '(:use ((:instance aot-kc-split (i (nfix i))) (:instance aot-kc-nth (i (ex-i2 e)))
                       (:instance aot-kc-nth (i (nfix (- (ex-nk e) 1)))) (:instance aot-kc-step (i (nfix i)))
                       (:instance aot-kc-last (i (nfix i))) aot-kc-0 aot-kc-if)))))

; THE COMPILE'S COST: linear in the tree
(defthm aot-cc-cost (<= (aot-cc-cnt 0 e 0) (+ 2 (* 6 (acl2-count e)))) :rule-classes :linear
  :hints (("Goal" :use ((:instance aot-cc-cnt-bound (fl 0) (i 0))))))

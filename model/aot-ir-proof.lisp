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
;
; 4c's first part, the TYPED paths without prims: a typed local read (boxed from its variable), a
; typed if test, typed let and loop bindings, typed recur arguments (each into a typed temporary,
; then written), and gp (fl 5: its operand, read after its code, is ex-ev's value and its read
; ex-ev's frame -- a marked local's read clears it in the model, as ex-ev does) and fl 6. The types
; are gen's annotation and the theorem holds for any of them but one hypothesis: A-NONE (aot-noval),
; a node annotated none answers no value. Every case is one lemma again (aot-cc-cl-tif-*,
; -let-tmid, -5-*, -6); a recur argument either way through aot-ca and aot-cacl.
;
; 4c-iii, THE PRIMS COMPOSED: the meaning is now aot-ev (aot-ir.lisp), ex-ev with the host's apply of
; a builtin -- ex-ev answers (:out) for any call of one, so no tree whose prim runs was in the old
; statement; on a tree with no call aot-ev is ex-ev case for case (by construction; that agreement is
; not a theorem here: a first attempt, aot-ev-is-ex-ev, looped the rewriter and was dropped). The subset gains the TYPED CALL gen compiles through gp-call (aot-tcok: an op gen reads, its
; head a pooled constant or Var -- A-HEAD -- A-PRIM at its operands' types, A-FMUL), and one more
; annotation hypothesis, A-LONG (aot-lval: a node typed long answers a 64-bit integer). gp-call
; (fl 7) is a case of the same induction (aot-cc-cl-7: a cast, a long's long, a Math member, an op set
; once, a guarded op with its hatch); its operands are read in aot-ev's order (aot-ops2: the first
; saved before the second's code), so a marked typed read clears its slot just where aot-ev's does.

(in-package "ACL2")
(set-prover-step-limit 30000000)
(include-book "aot-prim-proof")

(in-theory (disable aot-ev ex-kid-of c+ aot-prim-step aot-happ))
(defthm aot-ex-ev-m-i
  (implies (syntaxp (not (and (equal i (quote (quote 0))) (equal tmp (quote (quote nil))))))
           (equal (aot-ev :m e i tmp fr fuel) (aot-ev :m e 0 nil fr fuel)))
  :hints (("Goal" :expand ((aot-ev :m e i tmp fr fuel) (aot-ev :m e 0 nil fr fuel)))))

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
               ((aot-isop x :tif)
                (let* ((xr (aot-xrun (cadr x) fr bt))
                       (r (aot-ir-run (if (truthy (car xr)) (caddr x) (cadddr x)) (cdr xr) bt rp fuel)))
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
; a typed operand, by its form; an operand aot-cc has not built yet stays closed
(defthm aot-xrun-forms
  (and (equal (aot-xrun (list :lit v ty) fr bt) (cons v fr))
       (equal (aot-xrun (list :sv s ty m) fr bt) (cons (nth (nfix s) fr) (if m (update-nth (nfix s) nil fr) fr)))
       (equal (aot-xrun (list :tv d ty) fr bt) (cons (nth (nfix d) bt) fr))
       (equal (aot-xrun (list :unbox d ty) fr bt) (cons (nth (nfix d) bt) fr))))
(in-theory (disable aot-xrun))
; a loop that ends leaves the flag as it found it (each Fortran loop has its own)
(defthm aot-ir-loop-rp
  (implies (caddr (aot-ir-run (list (list :loop b)) fr bt rp fuel))
           (equal (cadddr (aot-ir-run (list (list :loop b)) fr bt rp fuel)) rp))
  :hints (("Goal" :expand ((aot-ir-run (list (list :loop b)) fr bt rp fuel)) :in-theory (disable aot-ir-run-cons))))

; ---- SLOTS -----------------------------------------------------------------------------------


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
(in-theory (disable aot-pent ex-kind ex-i2 ex-c ex-mark ex-s2 ex-nk ex-rstart ex-rn aot-at aot-bt aot-typ aot-bty))
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
  :hints (("Goal" :induct (aot-cc fl e i n pool) :in-theory (disable aot-unprim aot-pw aot-coerce) :expand ((:free (fl) (aot-cc fl e i n pool))))))
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
;; fl 5 and fl 7 answer an operand, not a slot
(defmacro aot-sl (fl e i n)
  (let ((s `(aot-slok (cadr (aot-cc ,fl ,e ,i ,n pool)) ,n (caddr (aot-cc ,fl ,e ,i ,n pool)) pool)))
    (if (symbolp fl) `(or (equal ,fl 5) (equal ,fl 7) ,s) s)))
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
(defthm aot-sl-6 (implies (natp n) (aot-sl 6 e i n)) :hints (("Goal" :expand ((aot-cc 6 e i n pool)))))
(defthm aot-sl-4
  (implies (and (natp n)
                (implies (and (consp e) (< (nfix i) (ex-nk e)) (aot-typ (nth (nfix i) (aot-bt e))))
                         (aot-sl 4 e (+ 1 (nfix i)) (caddr (aot-cc 6 (ex-kid-of e (nfix i)) (nth (nfix i) (aot-bt e)) n pool))))
                (implies (and (consp e) (< (nfix i) (ex-nk e)) (not (aot-typ (nth (nfix i) (aot-bt e)))))
                         (aot-sl 4 e (+ 1 (nfix i)) (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))))
           (aot-sl 4 e i n))
  :hints (("Goal" :expand ((aot-cc 4 e i n pool)))))
(defthm aot-sl-3
  (implies (and (natp n) (not (equal fl 0)) (not (equal fl 1)) (not (equal fl 2)) (not (equal fl 4)) (not (equal fl 5)) (not (equal fl 6)) (not (equal fl 7))
                (if (and (consp e) (< (nfix i) (ex-i2 e)))
                    (if (aot-typ (aot-bty e (nfix i)))
                        (aot-sl 3 e (+ 1 (nfix i)) (caddr (aot-cc 5 (ex-kid-of e (nfix i)) (aot-bty e (nfix i)) n pool)))
                      (aot-sl 3 e (+ 1 (nfix i)) (caddr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool))))
                  (implies (consp e) (aot-sl 0 (ex-kid-of e (ex-i2 e)) 0 n))))
           (aot-slok (cadr (aot-cc fl e i n pool)) n (caddr (aot-cc fl e i n pool)) pool))
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
                  (implies (and (not (equal fl 5)) (not (equal fl 7))) (or (and (natp s) (<= n s) (< s m)) (aot-inpool s pool)))
                  (implies (and (equal fl 0) (consp (car cc))) (and (natp s) (<= n s) (< s m))))))
  :hints (("Goal" :in-theory (e/d (aot-slok) (aot-cc-slot-0)) :use (aot-cc-slot1 aot-cc-slot-0))))

(defthm aot-cc-slot-int
  (implies (and (natp n) (aot-pslt pool n) (not (equal fl 5)) (not (equal fl 7))) (and (integerp (cadr (aot-cc fl e i n pool))) (<= 0 (cadr (aot-cc fl e i n pool)))))
  :rule-classes ((:rewrite :corollary (implies (and (natp n) (aot-pslt pool n) (not (equal fl 5)) (not (equal fl 7))) (integerp (cadr (aot-cc fl e i n pool)))))
                 (:linear :corollary (implies (and (natp n) (aot-pslt pool n) (not (equal fl 5)) (not (equal fl 7))) (<= 0 (cadr (aot-cc fl e i n pool))))))
  :hints (("Goal" :use (aot-cc-slot (:instance aot-inpool-lt (s (cadr (aot-cc fl e i n pool))))) :in-theory (disable aot-cc-slot aot-inpool-lt))))
(in-theory (disable aot-cc-slot))
; a typed temporary: always fresh
(defthm aot-cc-slot-6
  (let* ((cc (aot-cc 6 e i n pool)) (s (cadr cc)) (m (caddr cc)))
    (implies (natp n) (and (natp s) (<= n s) (< s m) (consp (car cc)))))
  :rule-classes ((:rewrite :corollary (implies (natp n) (and (integerp (cadr (aot-cc 6 e i n pool))) (consp (car (aot-cc 6 e i n pool))))))
                 (:linear :corollary (implies (natp n) (and (<= n (cadr (aot-cc 6 e i n pool))) (< (cadr (aot-cc 6 e i n pool)) (caddr (aot-cc 6 e i n pool)))))))
  :hints (("Goal" :expand ((aot-cc 6 e i n pool)))))

; a recur's argument i: a typed temporary or gen's value
(defun aot-ca (e i n pool)
  (if (aot-typ (nth (nfix i) (aot-bt e))) (aot-cc 6 (ex-kid-of e (nfix i)) (nth (nfix i) (aot-bt e)) n pool) (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))
(defthm aot-ca-slot
  (let* ((r (aot-ca e i n pool)) (s (cadr r)) (m (caddr r)))
    (implies (and (natp n) (aot-pslt pool n))
             (and (natp m) (<= n m) (natp s)
                  (or (and (<= n s) (< s m)) (aot-inpool s pool))
                  (implies (or (aot-typ (nth (nfix i) (aot-bt e))) (consp (car r))) (and (<= n s) (< s m))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))
                        (:instance aot-cc-slot (fl 6) (e (ex-kid-of e (nfix i))) (i (nth (nfix i) (aot-bt e))))
                        (:instance aot-inpool-lt (s (cadr (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)))))
           :in-theory (disable aot-inpool-lt))))
(defthm aot-ca-next (and (natp (caddr (aot-ca e i n pool))) (<= (nfix n) (caddr (aot-ca e i n pool))))
  :rule-classes ((:type-prescription :corollary (natp (caddr (aot-ca e i n pool))))
                 (:linear :corollary (<= (nfix n) (caddr (aot-ca e i n pool))))))
(defthm aot-ca-nfix (equal (aot-ca e (nfix i) n pool) (aot-ca e i n pool)) :hints (("Goal" :in-theory (enable aot-ca))))
(in-theory (disable aot-ca))

; ---- A RECUR'S WRITES ------------------------------------------------------------------------
;
; aot-cc 4's fourth part: each argument's slot put into its local, its temporary let go. The
; values it writes are its arguments' slots as the code left them (aot-wvals); every temporary it
; lets go is at or above n and none a later put reads, so the run is ex-write's.

(defun aot-wvals (e i n pool bt)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (consp e) (< (nfix i) (ex-nk e)))
      (let ((r (aot-ca e i n pool)))
        (cons (nth (cadr r) bt) (aot-wvals e (+ 1 (nfix i)) (caddr r) pool bt)))
    nil))

(defthm aot-cc-4-step
  (implies (and (consp e) (< (nfix i) (ex-nk e)))
           (equal (aot-cc 4 e i n pool)
                  (let* ((ty (nth (nfix i) (aot-bt e))) (r (aot-ca e i (nfix n) pool)) (r2 (aot-cc 4 e (+ 1 (nfix i)) (caddr r) pool)))
                    (list (append (car r) (car r2)) (cadr r2) (caddr r2)
                          (append (if (aot-typ ty)
                                      (list (list :tput (+ (ex-rstart e) (nfix i)) ty (list :tv (cadr r) ty)))
                                    (append (list (list :put (+ (ex-rstart e) (nfix i)) (cadr r)))
                                            (if (consp (car r)) (list (list :const (cadr r) nil)) nil)))
                                  (cadddr r2))))))
  :hints (("Goal" :expand ((aot-cc 4 e i n pool)) :in-theory (enable aot-ca))))
(defthm aot-cc-4-end
  (implies (not (and (consp e) (< (nfix i) (ex-nk e))))
           (equal (aot-cc 4 e i n pool)
                  (if (consp e) (list nil (nfix n) (+ 1 (nfix n)) nil) (list (list (list :owed e)) (nfix n) (+ 1 (nfix n)) nil))))
  :hints (("Goal" :expand ((aot-cc 4 e i n pool)))))

(defthm aot-wvals-update
  (implies (and (natp n) (aot-pslt pool n) (natp d) (< d n) (not (aot-inpool d pool)))
           (equal (aot-wvals e i n pool (update-nth d v bt)) (aot-wvals e i n pool bt)))
  :hints (("Goal" :induct (aot-wvals e i n pool bt))
          ("Subgoal *1/1" :use ((:instance aot-ca-slot)))))

(defun aot-w-ind (e i n pool bt fr)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (consp e) (< (nfix i) (ex-nk e)))
      (let* ((r (aot-ca e i n pool)) (s (cadr r)))
        (aot-w-ind e (+ 1 (nfix i)) (caddr r) pool
                   (if (and (not (aot-typ (nth (nfix i) (aot-bt e)))) (consp (car r))) (update-nth s nil bt) bt)
                   (update-nth (+ (ex-rstart e) (nfix i)) (nth s bt) fr)))
    (list n pool bt fr)))

(defthm aot-writes-run
  (implies (and (natp n) (aot-pslt pool n))
           (let ((r (aot-ir-run (cadddr (aot-cc 4 e i n pool)) fr bt rp fuel)))
             (and (caddr r) (equal (cadddr r) rp)
                  (equal (car r) (ex-write (+ (ex-rstart e) (nfix i)) (aot-wvals e i n pool bt) fr))
                  (aot-same n (cadr r) bt))))
  :hints (("Goal" :induct (aot-w-ind e i n pool bt fr))
          ("Subgoal *1/1" :use ((:instance aot-ca-slot)))))

(defthm aot-wvals-true-listp (true-listp (aot-wvals e i n pool bt)))
(defthm aot-wvals-len (implies (consp e) (equal (len (aot-wvals e i n pool bt)) (nfix (- (ex-nk e) (nfix i))))))
(defthm aot-take-len (implies (and (true-listp x) (equal k (len x))) (equal (take k x) x)))
(defthm aot-append-assoc (equal (append (append a b) c) (append a (append b c))))
(defun aot-tk-ind (k x) (if (zp k) (list k x) (aot-tk-ind (- k 1) (cdr x))))
(defthm aot-take-append-nil (equal (take k (append x nil)) (take k x)) :hints (("Goal" :induct (aot-tk-ind k x))))

; ---- THE SUBSET ------------------------------------------------------------------------------

; A-NONE: a node gen types none (it never answers) answers no value -- slice 2's aot-ty-sound at
; type 0, at gen's env; that the annotation is aot-ty's is the fuzzer's check, not proved
(defun-sk aot-noval (e) (forall (fr fuel) (not (equal (car (car (aot-ev :m e 0 nil fr fuel))) :val))))
; A-LONG: a node gen types long answers a 64-bit integer -- slice 2's aot-ty-sound at type 2, A-NONE's
; kind (the annotation aot-ty's: fuzzed, not proved)
(defun-sk aot-lval (e)
  (forall (fr fuel) (let ((r (car (aot-ev :m e 0 nil fr fuel)))) (implies (equal (car r) :val) (aot-i64p (cdr r))))))
; a guarded op (4c-ii): long + - * inc dec, the int and long casts but a long's long
(defun aot-guarded (p ty a0) (or (equal p 19) (and (equal p 20) (not (equal a0 2))) (and (equal ty 2) (member p '(1 2 3 5 6)))))
; A TYPED CALL the compile covers (4c-iii): an op gen reads (not an array, not a compare with a boxed
; operand) of its own count of operands, its head a constant or Var in the pool (A-HEAD), the op's
; spec A-PRIM at the types its operands are annotated and read at, A-FMUL, and a guarded op's long
; operands typed long (gp-call's parts named: the operands' types, the type they are read at)
(defun aot-7a0 (e) (aot-at (ex-kid-of e 1)))
(defun aot-7a1 (e) (aot-at (ex-kid-of e 2)))
(defun aot-7w (e) (aot-pw (aot-pop e) (aot-at e) (aot-7a0 e) (aot-7a1 e)))
(defun aot-7w2 (e) (if (equal (aot-pop e) 12) (aot-7a1 e) (aot-7w e)))
(defun aot-tcok (e pool)
  (let ((p (aot-pop e)) (ty (aot-at e)) (a0 (aot-7a0 e)) (a1 (aot-7a1 e)) (w (aot-7w e)) (h (ex-kid-of e 0)))
    (and (aot-typ ty) (not (equal p 0)) (not (aot-unprim p a0 a1))
         (equal (ex-nk e) (+ 1 (aot-nargs p)))
         (consp (aot-pent h pool))
         (aot-prim-ok (ex-c h) p w (list a0 a1) (if (equal p 21) (list 3) (list w (aot-7w2 e))))
         (aot-fmul-ok)
         (implies (and (aot-guarded p ty a0) (equal w 2)) (and (equal a0 2) (implies (< 2 (ex-nk e)) (equal a1 2)))))))
(defun aot-s4ok (e pool)
  (let ((k (ex-kind e)) (nk (ex-nk e)))
    (and (consp e) (member k '(1 2 3 4 5 6 11 12 16))
         (implies (equal (aot-at e) 0) (aot-noval e))
         (implies (equal (aot-at e) 2) (aot-lval e))
         (implies (equal k 6) (aot-tcok e pool))
         (implies (equal k 4) (or (equal nk 2) (equal nk 3)))
         (implies (or (equal k 11) (equal k 12)) (equal nk (+ 1 (ex-i2 e))))
         (implies (equal k 16) (equal (ex-rn e) nk))
         (implies (equal k 3) (consp (aot-pent e pool))))))
(in-theory (disable aot-tcok aot-lval aot-noval))
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
  (implies (aot-s4 0 e 0 pool) (and (consp e) (member (ex-kind e) '(1 2 3 4 5 6 11 12 16))))
  :rule-classes :forward-chaining :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok))))

(defthm aot-s4-none (implies (and (aot-s4 0 e 0 pool) (equal (aot-at e) 0)) (aot-noval e))
  :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok aot-noval))))
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
         (7 (and (equal (ex-kind e) 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0))))
         (otherwise t))))
; when ex-ev answers: the code runs to the end, slots below n kept; a recur's arguments (fl 4)
; leave the frame ex-ev writes them into and their values for the writes; anything else its value
; in its slot, or its recur by the flag, and ex-ev's frame
(defun aot-ccconcl (fl e i n pool fr bt fuel tmp)
  (let* ((cc (aot-cc fl e i n pool)) (r (aot-ir-run (car cc) fr bt nil fuel)) (x (aot-ev (aot-ccflg fl) e i tmp fr fuel)))
    (implies (not (equal (car x) (list :out)))
             (and (caddr r)
                  (aot-same n (cadr r) bt)
                  (cond
                   ; gp: the operand, read after the code, is ex-ev's value (and its read ex-ev's frame)
                   ((or (equal fl 5) (equal fl 7))
                    (let ((xr (aot-xrun (cadr cc) (car r) (cadr r))))
                      (if (cadddr r)
                          (and (equal (car x) (list :recur)) (equal (cadr x) (car r)))
                        (and (equal (car x) (cons :val (car xr))) (equal (cadr x) (cdr xr))))))
                   ((equal fl 4)
                      (and (not (cadddr r))
                           (equal (car x) (list :recur))
                           (equal (cadr x) (ex-write (ex-rstart e) (take (min (ex-rn e) (ex-nk e)) (append tmp (aot-wvals e i n pool (cadr r))))
                                                     (car r)))))
                   (t
                    (and (equal (car x) (if (cadddr r) (list :recur) (cons :val (nth (cadr cc) (cadr r)))))
                         (implies (or (not (equal fl 6)) (not (cadddr r))) (equal (cadr x) (car r))))))))))
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
               ((and (equal k 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0))) (aot-cc-ind 7 e 0 n pool fr bt fuel nil))
               ((and (equal k 4) (equal (aot-at (ex-kid-of e 0)) 4))
                (let* ((tr (aot-cc 5 (ex-kid-of e 0) 4 n pool)) (r (caddr tr))
                       (r0 (aot-ir-run (car tr) fr bt nil fuel))
                       (xr (aot-xrun (cadr tr) (car r0) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (list (aot-cc-ind 5 (ex-kid-of e 0) 4 n pool fr bt fuel nil)
                        (aot-cc-ind 0 (ex-kid-of e 1) 0 (+ 1 r) pool (cdr xr) (cadr r0) fuel nil)
                        (aot-cc-ind 0 (ex-kid-of e 2) 0 m pool (cdr xr) (cadr r0) fuel nil))))
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
             (let* ((ty (nth i (aot-bt e))) (r (aot-ca e i n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
               (list (if (aot-typ ty)
                         (aot-cc-ind 6 (ex-kid-of e i) ty n pool fr bt fuel nil)
                       (aot-cc-ind 0 (ex-kid-of e i) 0 n pool fr bt fuel nil))
                     (aot-cc-ind 4 e (+ 1 i) (caddr r) pool (car r0) (cadr r0) fuel
                                 (append tmp (list (nth (cadr r) (cadr r0)))))))
           nil))
      (5 (cond ((not (consp e)) nil)
               ((and (equal k 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0))) (aot-cc-ind 7 e 0 n pool fr bt fuel nil))
               ((not (and (member k '(1 2 6)) (aot-typ (aot-at e)))) (aot-cc-ind 0 e 0 n pool fr bt fuel nil))
               (t nil)))
      (6 (aot-cc-ind 5 e i n pool fr bt fuel nil))
      ; a typed call: its operands, the second from the state the first's read (and the snapshot) left
      (7 (if (consp e)
             (let* ((a0 (aot-7a0 e)) (w (aot-7w e)) (w2 (aot-7w2 e))
                    (r1 (aot-cc 5 (ex-kid-of e 1) w n pool)) (n1 (caddr r1))
                    (r2 (aot-cc 5 (ex-kid-of e 2) w2 (+ 1 n1) pool))
                    (q1 (aot-ir-run (car r1) fr bt nil fuel))
                    (xr (aot-xrun (aot-coerce (cadr r1) a0 w) (car q1) (cadr q1)))
                    (b1 (if (consp (car r2)) (update-nth n1 (car xr) (cadr q1)) (cadr q1))))
               (list (aot-cc-ind 5 (ex-kid-of e 1) w n pool fr bt fuel nil)
                     (aot-cc-ind 5 (ex-kid-of e 2) w2 (+ 1 n1) pool (cdr xr) b1 fuel nil)))
           nil))
      (otherwise
       (if (and (consp e) (< i (ex-i2 e)) (aot-typ (aot-bty e i)))
           (let* ((r (aot-cc 5 (ex-kid-of e i) (aot-bty e i) n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel))
                  (xr (aot-xrun (cadr r) (car r0) (cadr r0))))
             (list (aot-cc-ind 5 (ex-kid-of e i) (aot-bty e i) n pool fr bt fuel nil)
                   (aot-cc-ind 3 e (+ 1 i) (caddr r) pool (update-nth (+ (ex-s2 e) i) (car xr) (cdr xr)) (cadr r0) fuel tmp)))
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
           nil)))))))

; ---- THE CASES -------------------------------------------------------------------------------

(defmacro aot-cc-theory (&rest more) `(enable aot-cc-cl aot-cchyp aot-ccconcl ,@more))

(defthm aot-cc-cl-0
  (implies (aot-cc-cl 1 e 0 n pool fr bt fuel nil) (aot-cc-cl 0 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 0 e i n pool))
           :use ((:instance aot-cc-slot (fl 1) (i 0))))))

(defthm aot-cc-cl-leaf
  (implies (and (member (ex-kind e) '(1 2 3)) (member fl '(1)))
           (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel))
           :use ((:instance aot-pent-slot) (:instance aot-pent-inpool)))))

(defthm aot-cc-cl-do
  (implies (and (equal (ex-kind e) 5) (aot-cc-cl 2 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel) (aot-ev :do e 0 nil fr fuel)))))

(defthm aot-cc-cl-let
  (implies (and (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (aot-cc-cl 3 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel)))))

(defthm aot-cc-cl-recur
  (implies (and (equal (ex-kind e) 16) (aot-cc-cl 4 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel))
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
      (let ((r (aot-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (aot-rec-ind e (+ 1 (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel))
    (list tmp fr)))
(defthm aot-rec-notval (not (equal (car (car (aot-ev :rec e i tmp fr fuel))) :val))
  :hints (("Goal" :induct (aot-rec-ind e i tmp fr fuel) :expand ((aot-ev :rec e i tmp fr fuel)))))
(defthm aot-recur-notval
  (implies (equal (ex-kind e) 16) (not (equal (car (aot-ev :m e 0 nil fr fuel)) (cons :val v))))
  :hints (("Goal" :expand ((aot-ev :m e 0 nil fr fuel)) :use ((:instance aot-rec-notval (i 0) (tmp nil))) :in-theory (disable aot-rec-notval))))

; a value answer, read through its equality
(defthm aot-val-car (implies (equal a (cons :val v)) (equal (car a) :val)))
(defthm aot-val-cdr (implies (equal a (cons :val v)) (equal (cdr a) v)))

; an if: the test, then the branch it takes
(defthm aot-cc-cl-if-then
  (implies (and (equal (ex-kind e) 4) (not (equal (aot-at (ex-kid-of e 0)) 4)) (truthy (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel))))
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0))))
                  (and (aot-cc-cl 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 1) 0 (+ 1 r) pool (car r0) bt1 fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel))
           :do-not '(generalize fertilize))))

(defthm aot-cc-cl-if-else
  (implies (and (equal (ex-kind e) 4) (not (equal (aot-at (ex-kid-of e 0)) 4)) (not (truthy (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)))))
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (and (aot-cc-cl 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 2) 0 m pool (car r0) bt1 fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel))
           :do-not '(generalize fertilize))))

; a TYPED test (4c): its operand, read after its code, decides
(defthm aot-cc-cl-tif-then
  (implies (and (equal (ex-kind e) 4) (equal (aot-at (ex-kid-of e 0)) 4) (truthy (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel))))
                (let* ((tr (aot-cc 5 (ex-kid-of e 0) 4 n pool)) (r (caddr tr))
                       (r0 (aot-ir-run (car tr) fr bt nil fuel)) (xr (aot-xrun (cadr tr) (car r0) (cadr r0))))
                  (and (aot-cc-cl 5 (ex-kid-of e 0) 4 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 1) 0 (+ 1 r) pool (cdr xr) (cadr r0) fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel))
           :do-not '(generalize fertilize))))
(defthm aot-cc-cl-tif-else
  (implies (and (equal (ex-kind e) 4) (equal (aot-at (ex-kid-of e 0)) 4) (not (truthy (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)))))
                (let* ((tr (aot-cc 5 (ex-kid-of e 0) 4 n pool)) (r (caddr tr))
                       (r0 (aot-ir-run (car tr) fr bt nil fuel)) (xr (aot-xrun (cadr tr) (car r0) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (and (aot-cc-cl 5 (ex-kid-of e 0) 4 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 2) 0 m pool (cdr xr) (cadr r0) fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel))
           :do-not '(generalize fertilize))))
(defthm aot-cc-cl-tif
  (implies (and (equal (ex-kind e) 4) (equal (aot-at (ex-kid-of e 0)) 4)
                (let* ((tr (aot-cc 5 (ex-kid-of e 0) 4 n pool)) (r (caddr tr))
                       (r0 (aot-ir-run (car tr) fr bt nil fuel)) (xr (aot-xrun (cadr tr) (car r0) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (and (aot-cc-cl 5 (ex-kid-of e 0) 4 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 1) 0 (+ 1 r) pool (cdr xr) (cadr r0) fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 2) 0 m pool (cdr xr) (cadr r0) fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((truthy (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel))))) :in-theory (disable aot-cc-cl))))

(defthm aot-cc-cl-if
  (implies (and (equal (ex-kind e) 4) (not (equal (aot-at (ex-kid-of e 0)) 4))
                (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                       (r0 (aot-ir-run tc fr bt nil fuel))
                       (bt1 (if (consp tc) (update-nth ts nil (cadr r0)) (cadr r0)))
                       (m (caddr (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool))))
                  (and (aot-cc-cl 0 (ex-kid-of e 0) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 1) 0 (+ 1 r) pool (car r0) bt1 fuel nil)
                       (aot-cc-cl 0 (ex-kid-of e 2) 0 m pool (car r0) bt1 fuel nil))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((truthy (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel))))) :in-theory (disable aot-cc-cl))))

(defthm aot-cc-cl-do-mid
  (implies (and (< (+ 1 (nfix i)) (ex-nk e))
                (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
                  (and (aot-cc-cl 0 (ex-kid-of e (nfix i)) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 2 e (+ 1 (nfix i)) (caddr r) pool (car r0) (cadr r0) fuel tmp))))
           (aot-cc-cl 2 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 2 e i n pool) (aot-ev :do e i tmp fr fuel))
           :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))))))

(defthm aot-cc-cl-do-last
  (implies (and (not (< (+ 1 (nfix i)) (ex-nk e)))
                (aot-cc-cl 0 (ex-kid-of e (nfix (- (ex-nk e) 1))) 0 n pool fr bt fuel nil))
           (aot-cc-cl 2 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 2 e i n pool) (aot-ev :do e i tmp fr fuel)))))

; an argument, typed or boxed, by its value's conclusion (aot-ca: fl 6 or fl 0)
(defun aot-cacl (e i n pool fr bt fuel)
  (let* ((r (aot-ca e i n pool)) (rr (aot-ir-run (car r) fr bt nil fuel)) (x (aot-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
    (implies (and (natp n) (aot-s4 0 (ex-kid-of e (nfix i)) 0 pool) (aot-pslt pool n) (aot-poolok pool bt) (not (equal (car x) (list :out))))
             (and (caddr rr) (aot-same n (cadr rr) bt)
                  (equal (car x) (if (cadddr rr) (list :recur) (cons :val (nth (cadr r) (cadr rr)))))
                  (implies (not (cadddr rr)) (equal (cadr x) (car rr)))))))
(defthm aot-cacl-of
  (implies (if (aot-typ (nth (nfix i) (aot-bt e)))
               (aot-cc-cl 6 (ex-kid-of e (nfix i)) (nth (nfix i) (aot-bt e)) n pool fr bt fuel nil)
             (aot-cc-cl 0 (ex-kid-of e (nfix i)) 0 n pool fr bt fuel nil))
           (aot-cacl e i n pool fr bt fuel))
  :hints (("Goal" :in-theory (enable aot-cc-cl aot-cchyp aot-ccconcl aot-ca))))
(defthm aot-cc-cl-rec-mid
  (implies (and (< (nfix i) (ex-nk e))
                (let* ((r (aot-ca e i n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
                  (and (aot-cacl e i n pool fr bt fuel)
                       (aot-cc-cl 4 e (+ 1 (nfix i)) (caddr r) pool (car r0) (cadr r0) fuel
                                  (append tmp (list (nth (cadr r) (cadr r0))))))))
           (aot-cc-cl 4 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-ev :rec e i tmp fr fuel)
                                                     (aot-wvals e i n pool (cadr (aot-ir-run (car (aot-cc 4 e i n pool)) fr bt nil fuel))))
           :use ((:instance aot-ca-slot)))
          (and stable-under-simplificationp
               '(:use ((:instance aot-nth-same (j (cadr (aot-ca e i n pool)))
                        (n (caddr (aot-ca e i n pool)))
                        (x (cadr (aot-ir-run (car (aot-cc 4 e (+ 1 (nfix i)) (caddr (aot-ca e i n pool)) pool))
                                             (car (aot-ir-run (car (aot-ca e i n pool)) fr bt nil fuel))
                                             (cadr (aot-ir-run (car (aot-ca e i n pool)) fr bt nil fuel))
                                             nil fuel)))
                        (y (cadr (aot-ir-run (car (aot-ca e i n pool)) fr bt nil fuel)))))))))
(defthm aot-cacl-nfix (equal (aot-cacl e (nfix i) n pool fr bt fuel) (aot-cacl e i n pool fr bt fuel)) :hints (("Goal" :in-theory (e/d (aot-cacl aot-ca) (aot-ca-nfix)))))
(in-theory (disable aot-cacl))

(defthm aot-cc-cl-rec-end
  (implies (not (< (nfix i) (ex-nk e))) (aot-cc-cl 4 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 4 e i n pool) (aot-ev :rec e i tmp fr fuel)
                                                     (:free (bt) (aot-wvals e i n pool bt))))))

(defthm aot-cc-cl-let-tmid
  (implies (and (< (nfix i) (ex-i2 e)) (aot-typ (aot-bty e (nfix i)))
                (let* ((r (aot-cc 5 (ex-kid-of e (nfix i)) (aot-bty e (nfix i)) n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel))
                       (xr (aot-xrun (cadr r) (car r0) (cadr r0))))
                  (and (aot-cc-cl 5 (ex-kid-of e (nfix i)) (aot-bty e (nfix i)) n pool fr bt fuel nil)
                       (aot-cc-cl 3 e (+ 1 (nfix i)) (caddr r) pool (update-nth (+ (ex-s2 e) (nfix i)) (car xr) (cdr xr)) (cadr r0) fuel tmp))))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 3 e i n pool) (aot-ev :let e i tmp fr fuel)))))
(defthm aot-cc-cl-let-mid
  (implies (and (< (nfix i) (ex-i2 e)) (not (aot-typ (aot-bty e (nfix i))))
                (let* ((r (aot-cc 0 (ex-kid-of e (nfix i)) 0 n pool)) (r0 (aot-ir-run (car r) fr bt nil fuel)))
                  (and (aot-cc-cl 0 (ex-kid-of e (nfix i)) 0 n pool fr bt fuel nil)
                       (aot-cc-cl 3 e (+ 1 (nfix i)) (caddr r) pool
                                  (update-nth (+ (ex-s2 e) (nfix i)) (nth (cadr r) (cadr r0)) (car r0))
                                  (if (consp (car r)) (update-nth (cadr r) nil (cadr r0)) (cadr r0)) fuel tmp))))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 3 e i n pool) (aot-ev :let e i tmp fr fuel))
           :use ((:instance aot-cc-slot (fl 0) (e (ex-kid-of e (nfix i))) (i 0))))))

(defthm aot-cc-cl-let-body
  (implies (and (not (< (nfix i) (ex-i2 e))) (not (equal (ex-kind e) 12))
                (aot-cc-cl 0 (ex-kid-of e (ex-i2 e)) 0 n pool fr bt fuel nil))
           (aot-cc-cl 3 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 3 e i n pool) (aot-ev :let e i tmp fr fuel)))))

; a loop's body: ex-ev's :iter, its rounds the :loop's
(defthm aot-ev-loop-end
  (implies (and (consp e) (equal (ex-kind e) 12) (not (< (nfix i) (ex-i2 e))))
           (and (equal (car (aot-ev :let e i tmp fr fuel)) (car (aot-ev :iter (ex-kid-of e (ex-i2 e)) 0 nil fr fuel)))
                (equal (cadr (aot-ev :let e i tmp fr fuel)) (cadr (aot-ev :iter (ex-kid-of e (ex-i2 e)) 0 nil fr fuel)))))
  :hints (("Goal" :expand ((aot-ev :let e i tmp fr fuel)))))
(defthm aot-ev-iter
  (implies (consp b)
           (equal (aot-ev :iter b 0 nil fr fuel)
                  (let* ((r (aot-ev :m b 0 nil fr fuel)) (res (car r)))
                    (cond ((not (eq (car res) :recur)) r)
                          ((zp fuel) (list (list :out) fr 0))
                          (t (let ((r2 (aot-ev :iter b 0 nil (cadr r) (1- fuel))))
                               (list (car r2) (cadr r2) (c+ (caddr r) (caddr r2)))))))))
  :hints (("Goal" :expand ((aot-ev :iter b 0 nil fr fuel)))))
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

; GP: a typed constant or local is its operand; a node typed none, its code and a literal it never
; reaches (A-NONE); anything else gen's value, unboxed
(defthm aot-cc-cl-5-leaf
  (implies (and (member (ex-kind e) '(1 2)) (aot-typ (aot-at e))) (aot-cc-cl 5 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory aot-typ) :expand ((aot-cc 5 e i n pool) (aot-ev :m e 0 nil fr fuel)))))
(defthm aot-cc-cl-5-none
  (implies (and (equal (aot-at e) 0) (aot-cc-cl 0 e 0 n pool fr bt fuel nil)) (aot-cc-cl 5 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory aot-typ) :expand ((aot-cc 5 e i n pool))
           :use ((:instance aot-noval-necc) (:instance aot-s4-none)))))
(defthm aot-cc-cl-5-else
  (implies (and (not (and (member (ex-kind e) '(1 2 6)) (aot-typ (aot-at e)))) (not (equal (aot-at e) 0))
                (aot-cc-cl 0 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 5 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory aot-typ) :expand ((aot-cc 5 e i n pool)))))
(defthm aot-cc-cl-5-untyped
  (implies (and (not (aot-typ (aot-at e))) (aot-cc-cl 0 e 0 n pool fr bt fuel nil)) (aot-cc-cl 5 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((equal (aot-at e) 0)) :in-theory (disable aot-cc-cl))))
(defthm aot-cc-cl-5-node
  (implies (and (not (member (ex-kind e) '(1 2 6))) (aot-cc-cl 0 e 0 n pool fr bt fuel nil)) (aot-cc-cl 5 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((equal (aot-at e) 0)) :in-theory (disable aot-cc-cl))))
(defthm aot-cc-cl-6
  (implies (aot-cc-cl 5 e (nfix i) n pool fr bt fuel nil) (aot-cc-cl 6 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 6 e i n pool)))))

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
  (implies (and (not (member (ex-kind e) '(1 2 3 4 5 6 11 12 16))) (not (equal fl 6))) (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :use (aot-s4-kind))))
(defthm aot-cc-cl-1-leaf
  (implies (not (member (ex-kind e) '(4 5 6 11 12 16))) (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((member (ex-kind e) '(1 2 3))) :in-theory (disable aot-cc-cl))))
(defthm aot-cc-cl-do0
  (implies (and (equal (ex-kind e) 5) (consp e) (equal (ex-nk e) 0)) (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool) (aot-ev :m e 0 nil fr fuel) (aot-ev :do e 0 nil fr fuel)))))
(defthm aot-cc-cl-badn (implies (not (natp n)) (aot-cc-cl fl e i n pool fr bt fuel tmp)) :hints (("Goal" :in-theory (aot-cc-theory))))
(defthm aot-cc-cl-other
  (implies (and (member fl '(0 1 2 3 4 5 7)) (not (consp e))) (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory))))

; ---- 4c-iii: A TYPED CALL ----------------------------------------------------------------------
;
; gp-call (fl 7) composed with the prims: the operands' code, each read in the order aot-ev runs
; them (the first saved into its slot before the second's code, when there is any), then the op --
; the unguarded op's operand or temporary, the guarded op's instruction with its hatch -- answers
; what aot-ev's host call of the head's fn on the operand values answers: by A-PRIM when the op
; runs, the hatch's own call when the guard sends it there.

(defthm aot-tcok-parts
  (implies (aot-tcok e pool) (and (aot-typ (aot-at e)) (not (equal (aot-pop e) 0))))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable aot-tcok))))
(defthm aot-s4-tc (implies (and (aot-s4 0 e 0 pool) (equal (ex-kind e) 6)) (aot-tcok e pool))
  :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok aot-tcok))))
(defthm aot-s4-long (implies (and (aot-s4 0 e 0 pool) (equal (aot-at e) 2)) (aot-lval e))
  :hints (("Goal" :use ((:instance aot-s4-ok (j 0))) :in-theory (disable aot-s4-ok aot-lval))))
(defthm aot-lval-i64
  (implies (and (aot-lval e) (equal (car (car (aot-ev :m e 0 nil fr fuel))) :val)) (aot-i64p (cdr (car (aot-ev :m e 0 nil fr fuel)))))
  :rule-classes nil :hints (("Goal" :use ((:instance aot-lval-necc)) :in-theory (disable aot-lval-necc aot-i64p))))
(in-theory (disable aot-tcok aot-lval))

; the tree's run of a typed call: its head's value, its operands', then the host's call of the one
; on the others -- when that answers
(defthm aot-ev-tcall
  (implies (and (consp e) (equal (ex-kind e) 6) (or (equal (ex-nk e) 2) (equal (ex-nk e) 3))
                (or (equal (ex-kind (ex-kid-of e 0)) 1) (equal (ex-kind (ex-kid-of e 0)) 3))
                (not (equal (car (aot-ev :m e 0 nil fr fuel)) '(:out))))
           (let* ((r1 (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel))
                  (r2 (aot-ev :m (ex-kid-of e 2) 0 nil (cadr r1) fuel))
                  (two (equal (ex-nk e) 3))
                  (h (aot-hcall (ex-c (ex-kid-of e 0)) (if two (list (cdr (car r1)) (cdr (car r2))) (list (cdr (car r1)))))))
             (and (equal (car (car r1)) :val)
                  (implies two (equal (car (car r2)) :val))
                  (consp h) (equal (car h) :val)
                  (equal (car (aot-ev :m e 0 nil fr fuel)) h)
                  (equal (cadr (aot-ev :m e 0 nil fr fuel)) (if two (cadr r2) (cadr r1))))))
  :hints (("Goal" :in-theory (enable aot-happ val valp ex-kind ex-c)
           :expand ((aot-ev :m e 0 nil fr fuel) (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)
                    (:free (tmp fr) (aot-ev :call e 1 tmp fr fuel)) (:free (tmp fr) (aot-ev :call e 2 tmp fr fuel))
                    (:free (tmp fr) (aot-ev :call e 3 tmp fr fuel))))))

; gp's conclusion, unpacked: a value answered, the code ran, no recur, its operand reads it
(defun aot-gpok (k w n pool fr bt fuel)
  (let* ((r (aot-cc 5 k w n pool)) (q (aot-ir-run (car r) fr bt nil fuel)) (x (aot-ev :m k 0 nil fr fuel))
         (xr (aot-xrun (cadr r) (car q) (cadr q))))
    (implies (equal (car (car x)) :val)
             (and (caddr q) (not (cadddr q)) (aot-same n (cadr q) bt)
                  (equal (cdr (car x)) (car xr)) (equal (cadr x) (cdr xr))))))
(defthm aot-gpok-of
  (implies (and (aot-cc-cl 5 k w n pool fr bt fuel nil) (natp n) (aot-s4 0 k 0 pool) (aot-pslt pool n) (aot-poolok pool bt))
           (aot-gpok k w n pool fr bt fuel))
  :hints (("Goal" :in-theory (aot-cc-theory))))

; two operands: their code and reads, the first saved before the second code when there is any
(defthm aot-ops2
  (let* ((q1 (aot-ir-run c1 fr bt nil fuel)) (xr1 (aot-xrun y1 (car q1) (cadr q1)))
         (b1 (if (consp c2) (update-nth n1 (car xr1) (cadr q1)) (cadr q1)))
         (q2 (aot-ir-run c2 (cdr xr1) b1 nil fuel)) (xr2 (aot-xrun y2 (car q2) (cadr q2))))
    (implies (and (natp n) (natp n1) (<= n n1)
                  (caddr q1) (not (cadddr q1)) (aot-same n (cadr q1) bt)
                  (caddr q2) (not (cadddr q2)) (aot-same (+ 1 n1) (cadr q2) b1))
             (let ((r (aot-ir-run (append c1 (if (consp c2) (list (list :tset n1 w y1)) nil) c2) fr bt nil fuel)))
               (and (caddr r) (not (cadddr r)) (aot-same n (cadr r) bt)
                    (equal (aot-xsrun (list (if (consp c2) (list :tv n1 w) y1) y2) (car r) (cadr r))
                           (cons (list (car xr1) (car xr2)) (cdr xr2)))))))
  :hints (("Goal" :cases ((consp c2)) :in-theory (enable aot-ir-step))
          (and stable-under-simplificationp
               (quote (:use ((:instance aot-nth-same (j n1) (n (+ 1 n1))
                                         (x (cadr (aot-ir-run c2 (cdr (aot-xrun y1 (car (aot-ir-run c1 fr bt nil fuel)) (cadr (aot-ir-run c1 fr bt nil fuel)))) (update-nth n1 (car (aot-xrun y1 (car (aot-ir-run c1 fr bt nil fuel)) (cadr (aot-ir-run c1 fr bt nil fuel)))) (cadr (aot-ir-run c1 fr bt nil fuel))) nil fuel)))
                                         (y (update-nth n1 (car (aot-xrun y1 (car (aot-ir-run c1 fr bt nil fuel)) (cadr (aot-ir-run c1 fr bt nil fuel)))) (cadr (aot-ir-run c1 fr bt nil fuel)))))))))))

; gp-call's parts, named: the operands' types, the type they are read at, the code and operands
(defun aot-7ops (e n pool)   ; (c xs m)
  (let* ((two (< 2 (ex-nk e))) (w (aot-7w e)) (w2 (aot-7w2 e))
         (r1 (aot-cc 5 (ex-kid-of e 1) w n pool)) (n1 (caddr r1))
         (r2 (if two (aot-cc 5 (ex-kid-of e 2) w2 (+ 1 n1) pool) (list nil nil n1)))
         (snap (and two (consp (car r2))))
         (x1 (aot-coerce (cadr r1) (aot-7a0 e) w))
         (xs (if two (list (if snap (list :tv n1 w) x1) (aot-coerce (cadr r2) (aot-7a1 e) w2)) (list x1))))
    (list (append (car r1) (if snap (list (list :tset n1 w x1)) nil) (car r2)) xs (caddr r2))))
(defthm aot-cc-7-is
  (implies (and (consp e) (not (aot-unprim (aot-pop e) (aot-7a0 e) (aot-7a1 e))))
           (equal (aot-cc 7 e i n pool)
                  (let* ((p (aot-pop e)) (ty (aot-at e)) (a0 (aot-7a0 e)) (w (aot-7w e))
                         (r1 (aot-cc 5 (ex-kid-of e 1) w (nfix n) pool))
                         (o (aot-7ops e (nfix n) pool)) (c (car o)) (xs (cadr o)) (m (caddr o)))
                    (cond ((equal p 21) (list (car r1) (aot-coerce (cadr r1) a0 3) (caddr r1)))
                          ((and (equal p 20) (equal a0 2)) (list (car r1) (cadr r1) (caddr r1)))
                          ((< 21 p) (list c (list :op p 3 xs) m))
                          ((or (equal p 19) (equal p 20) (and (equal ty 2) (member p '(1 2 3 5 6))))
                           (let* ((h (aot-cc 1 (ex-kid-of e 0) 0 (+ 1 m) pool)) (blk (caddr h)))
                             (list (append c (list (list :prim m ty p w xs (if (consp (car h)) (caddr (car (car h))) nil) (cadr h) blk (+ blk (len xs)))))
                                   (list :tv m ty) (+ 1 blk (len xs)))))
                          (t (list (append c (list (list :tset m ty (list :op p w xs)))) (list :tv m ty) (+ 1 m)))))))
  :hints (("Goal" :expand ((aot-cc 7 e i n pool)))))

; the operand values, and the frame after them, as aot-ev runs them
(in-theory (disable aot-7a0 aot-7a1 aot-7w aot-7w2))
(defun aot-7raw (e fr fuel)
  (let* ((r1 (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel)) (r2 (aot-ev :m (ex-kid-of e 2) 0 nil (cadr r1) fuel)))
    (if (< 2 (ex-nk e)) (list (cdr (car r1)) (cdr (car r2))) (list (cdr (car r1))))))
(defun aot-7fr (e fr fuel)
  (let* ((r1 (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel)) (r2 (aot-ev :m (ex-kid-of e 2) 0 nil (cadr r1) fuel)))
    (if (< 2 (ex-nk e)) (cadr r2) (cadr r1))))

; the IH a typed call's compile gives, as aot-cc-ind writes it
(defun aot-7ih (e n pool fr bt fuel)
  (let* ((a0 (aot-7a0 e)) (w (aot-7w e)) (w2 (aot-7w2 e))
         (r1 (aot-cc 5 (ex-kid-of e 1) w n pool)) (n1 (caddr r1))
         (r2 (aot-cc 5 (ex-kid-of e 2) w2 (+ 1 n1) pool))
         (q1 (aot-ir-run (car r1) fr bt nil fuel))
         (xr (aot-xrun (aot-coerce (cadr r1) a0 w) (car q1) (cadr q1)))
         (b1 (if (consp (car r2)) (update-nth n1 (car xr) (cadr q1)) (cadr q1))))
    (and (aot-cc-cl 5 (ex-kid-of e 1) w n pool fr bt fuel nil)
         (aot-cc-cl 5 (ex-kid-of e 2) w2 (+ 1 n1) pool (cdr xr) b1 fuel nil))))

; gp (fl 5) of an operand that answers a value, its conclusion as rewrites: the code ran, no recur,
; nothing below n moved, and its operand reads aot-ev's value and leaves aot-ev's frame
(defthm aot-gp-read
  (implies (and (aot-cc-cl 5 k w n pool fr bt fuel nil) (natp n) (aot-s4 0 k 0 pool) (aot-pslt pool n) (aot-poolok pool bt)
                (equal (car (car (aot-ev :m k 0 nil fr fuel))) :val))
           (let* ((r (aot-cc 5 k w n pool)) (q (aot-ir-run (car r) fr bt nil fuel)) (xr (aot-xrun (cadr r) (car q) (cadr q))))
             (and (equal (car xr) (cdr (car (aot-ev :m k 0 nil fr fuel))))
                  (equal (cdr xr) (cadr (aot-ev :m k 0 nil fr fuel)))
                  (caddr q) (not (cadddr q)) (aot-same n (cadr q) bt))))
  :hints (("Goal" :in-theory (e/d (aot-gpok) (aot-gpok-of)) :use ((:instance aot-gpok-of)))))
; the same, an operand with no code: read where it stands
(defthm aot-gp-read0
  (implies (and (aot-cc-cl 5 k w n pool fr bt fuel nil) (natp n) (aot-s4 0 k 0 pool) (aot-pslt pool n) (aot-poolok pool bt)
                (equal (car (car (aot-ev :m k 0 nil fr fuel))) :val) (not (consp (car (aot-cc 5 k w n pool)))))
           (let ((xr (aot-xrun (cadr (aot-cc 5 k w n pool)) fr bt)))
             (and (equal (car xr) (cdr (car (aot-ev :m k 0 nil fr fuel))))
                  (equal (cdr xr) (cadr (aot-ev :m k 0 nil fr fuel))))))
  :hints (("Goal" :in-theory (disable aot-gp-read) :use ((:instance aot-gp-read)))))

; THE OPERANDS: their code runs, no recur, nothing below n moved, and the operands read the values
; aot-ev's call is made on, as the Fortran reads them, and leave its frame
(defun aot-7opsok (e n pool fr bt fuel)
  (let* ((o (aot-7ops e n pool)) (r (aot-ir-run (car o) fr bt nil fuel)))
    (and (caddr r) (not (cadddr r)) (aot-same n (cadr r) bt)
         (natp (caddr o)) (<= n (caddr o))
         (equal (aot-xsrun (cadr o) (car r) (cadr r))
                (cons (aot-cvl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)) (list (aot-7w e) (aot-7w2 e)))
                      (aot-7fr e fr fuel))))))
(defmacro aot-7r1 () '(aot-cc 5 (ex-kid-of e 1) (aot-7w e) n pool))
(defmacro aot-7q1 () '(aot-ir-run (car (aot-7r1)) fr bt nil fuel))
(defmacro aot-7xr1 () '(aot-xrun (aot-coerce (cadr (aot-7r1)) (aot-7a0 e) (aot-7w e)) (car (aot-7q1)) (cadr (aot-7q1))))
(defmacro aot-7r2 () '(aot-cc 5 (ex-kid-of e 2) (aot-7w2 e) (+ 1 (caddr (aot-7r1))) pool))
(defmacro aot-7b1 () '(if (consp (car (aot-7r2))) (update-nth (caddr (aot-7r1)) (car (aot-7xr1)) (cadr (aot-7q1))) (cadr (aot-7q1))))
(defmacro aot-7ev1 () '(aot-ev :m (ex-kid-of e 1) 0 nil fr fuel))

(defthm aot-7ops-one
  (implies (and (not (< 2 (ex-nk e))) (natp n) (aot-s4 0 (ex-kid-of e 1) 0 pool) (aot-pslt pool n) (aot-poolok pool bt)
                (aot-cc-cl 5 (ex-kid-of e 1) (aot-7w e) n pool fr bt fuel nil)
                (equal (car (car (aot-7ev1))) :val))
           (aot-7opsok e n pool fr bt fuel))
  :hints (("Goal" :in-theory (e/d (aot-7ops aot-7raw aot-7fr) (aot-cc-cl aot-xrun aot-ev aot-cc)) :do-not-induct t)))

(defthm aot-7ops-two
  (implies (and (< 2 (ex-nk e)) (natp n) (aot-s4 0 (ex-kid-of e 1) 0 pool) (aot-s4 0 (ex-kid-of e 2) 0 pool)
                (aot-pslt pool n) (aot-poolok pool bt)
                (aot-cc-cl 5 (ex-kid-of e 1) (aot-7w e) n pool fr bt fuel nil)
                (aot-cc-cl 5 (ex-kid-of e 2) (aot-7w2 e) (+ 1 (caddr (aot-7r1))) pool (cdr (aot-7xr1)) (aot-7b1) fuel nil)
                (equal (car (car (aot-7ev1))) :val)
                (equal (car (car (aot-ev :m (ex-kid-of e 2) 0 nil (cadr (aot-7ev1)) fuel))) :val))
           (aot-7opsok e n pool fr bt fuel))
  :hints (("Goal" :in-theory (e/d (aot-7ops aot-7raw aot-7fr)
                                  (aot-cc-cl aot-ir-run aot-xrun aot-ev aot-cc aot-ir-run-append aot-xsrun aot-xsrun-2)) :do-not-induct t
           :cases ((consp (car (aot-7r2))))
           :use ((:instance aot-ops2 (c1 (car (aot-7r1))) (n1 (caddr (aot-7r1))) (y1 (aot-coerce (cadr (aot-7r1)) (aot-7a0 e) (aot-7w e)))
                            (c2 (car (aot-7r2))) (y2 (aot-coerce (cadr (aot-7r2)) (aot-7a1 e) (aot-7w2 e))) (w (aot-7w e)))
                 (:instance aot-poolok-same (bt2 (update-nth (caddr (aot-7r1)) (aot-cv (cdr (car (aot-7ev1))) (aot-7a0 e) (aot-7w e)) (cadr (aot-7q1)))))
                 (:instance aot-poolok-same (bt2 (cadr (aot-7q1))))
                 (:instance aot-pslt-grows (m (+ 1 (caddr (aot-7r1)))))))))

; the head read for the hatch: a Var not linked dereffed into a fresh slot from its pool slot, else
; its pool slot; either way its fn, the pool as the host filled it
(defthm aot-pent-consp (implies (aot-pent h pool) (consp h)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable aot-pent ex-kind))))
(defthm aot-cc-head
  (implies (and (aot-pent h pool) (consp (car (aot-cc 1 h 0 m pool))))
           (and (equal (caddr (car (car (aot-cc 1 h 0 m pool)))) (cadr (aot-pent h pool)))
                (equal (cadr (aot-cc 1 h 0 m pool)) (nfix m))))
  :hints (("Goal" :expand ((aot-cc 1 h 0 m pool)))))
(defthm aot-cc-head-pool
  (implies (and (aot-pent h pool) (not (consp (car (aot-cc 1 h 0 m pool)))))
           (and (equal (cadr (aot-cc 1 h 0 m pool)) (cadr (aot-pent h pool)))
                (equal (caddr (aot-cc 1 h 0 m pool)) (nfix m))))
  :hints (("Goal" :expand ((aot-cc 1 h 0 m pool)))))
(defthm aot-cc-head-fn
  (implies (and (aot-pent h pool) (aot-pslt pool n) (natp n) (natp m) (<= n m) (aot-poolok pool bt0) (aot-same n bt bt0))
           (let ((r (aot-cc 1 h 0 m pool)))
             (equal (aot-hd (if (consp (car r)) (caddr (car (car r))) nil) (cadr r) bt) (ex-c h))))
  :hints (("Goal" :expand ((aot-cc 1 h 0 m pool)) :in-theory (enable aot-hd aot-deref)
           :use ((:instance aot-pent-val2 (e h) (bt bt0)) (:instance aot-pent-slot (e h))
                 (:instance aot-nth-same (j (cadr (aot-pent h pool))) (x bt) (y bt0))))))

; A-PRIM on the call's values: when the op is in range at its operands as read, the host's call
; answers it
(defthm aot-7aprim
  (let* ((raw (aot-7raw e fr fuel)) (p (aot-pop e)) (w (aot-7w e)) (ts (list (aot-7a0 e) (aot-7a1 e)))
         (ws (if (equal p 21) (list 3) (list w (aot-7w2 e)))))
    (implies (and (aot-tcok e pool) (aot-fitl raw ts) (equal (len raw) (aot-nargs p)) (aot-inr p w (aot-cvl raw ts ws)))
             (equal (aot-hcall (ex-c (ex-kid-of e 0)) raw) (cons :val (aot-opx p w (aot-cvl raw ts ws))))))
  :hints (("Goal" :in-theory (e/d (aot-tcok) (aot-prim-ok-necc aot-opx aot-inr aot-cvl aot-pw aot-nargs aot-fitl aot-7raw))
           :use ((:instance aot-prim-ok-necc (f (ex-c (ex-kid-of e 0))) (p (aot-pop e)) (w (aot-7w e))
                            (ts (list (aot-7a0 e) (aot-7a1 e)))
                            (ws (if (equal (aot-pop e) 21) (list 3) (list (aot-7w e) (aot-7w2 e))))
                            (vals (aot-7raw e fr fuel)))))))
(defthm aot-tcok-prim
  (implies (and (aot-tcok e pool) (not (equal (aot-pop e) 21)))
           (and (aot-prim-ok (ex-c (ex-kid-of e 0)) (aot-pop e) (aot-7w e) (list (aot-7a0 e) (aot-7a1 e)) (list (aot-7w e) (aot-7w2 e)))
                (aot-fmul-ok)))
  :rule-classes nil :hints (("Goal" :in-theory (enable aot-tcok))))

(defthm aot-tcok-more
  (implies (aot-tcok e pool)
           (and (not (aot-unprim (aot-pop e) (aot-7a0 e) (aot-7a1 e)))
                (equal (ex-nk e) (+ 1 (aot-nargs (aot-pop e))))
                (or (equal (ex-nk e) 2) (equal (ex-nk e) 3))
                (aot-pent (ex-kid-of e 0) pool)
                (or (equal (ex-kind (ex-kid-of e 0)) 1) (equal (ex-kind (ex-kid-of e 0)) 3))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable aot-tcok aot-7a0 aot-7a1 aot-unprim) :use ((:instance aot-pent-kind (e (ex-kid-of e 0)))))))

; the facts every shape below starts from
(defun aot-7pre (e n pool fr bt fuel)
  (and (consp e) (equal (ex-kind e) 6) (aot-s4 0 e 0 pool) (natp n) (aot-pslt pool n) (aot-poolok pool bt)
       (aot-7ih e n pool fr bt fuel)
       (not (equal (car (aot-ev :m e 0 nil fr fuel)) '(:out)))))
(defthm aot-7pre-facts
  (implies (aot-7pre e n pool fr bt fuel)
           (let ((r1 (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel)))
             (and (aot-tcok e pool)
                  (not (aot-unprim (aot-pop e) (aot-7a0 e) (aot-7a1 e)))
                  (equal (ex-nk e) (+ 1 (aot-nargs (aot-pop e))))
                  (aot-pent (ex-kid-of e 0) pool)
                  (equal (car (car r1)) :val)
                  (implies (< 2 (ex-nk e)) (equal (car (car (aot-ev :m (ex-kid-of e 2) 0 nil (cadr r1) fuel))) :val))
                  (equal (car (aot-ev :m e 0 nil fr fuel)) (aot-hcall (ex-c (ex-kid-of e 0)) (aot-7raw e fr fuel)))
                  (equal (car (car (aot-ev :m e 0 nil fr fuel))) :val)
                  (equal (cadr (aot-ev :m e 0 nil fr fuel)) (aot-7fr e fr fuel)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable aot-7ih aot-ev-tcall)
           :use ((:instance aot-s4-tc) (:instance aot-tcok-more) (:instance aot-ev-tcall)))))

; the operand values fit their types (A-LONG), and there are as many as the op takes
(defthm aot-7long
  (implies (aot-7pre e n pool fr bt fuel)
           (let ((r1 (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel)))
             (and (implies (equal (aot-7a0 e) 2) (aot-i64p (cdr (car r1))))
                  (implies (and (< 2 (ex-nk e)) (equal (aot-7a1 e) 2))
                           (aot-i64p (cdr (car (aot-ev :m (ex-kid-of e 2) 0 nil (cadr r1) fuel))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-7a0 aot-7a1 aot-7pre) (aot-7ih aot-i64p aot-s4-long aot-tcok))
           :use ((:instance aot-7pre-facts) (:instance aot-s4-kid (j 1)) (:instance aot-s4-kid (j 2))
                 (:instance aot-s4-long (e (ex-kid-of e 1))) (:instance aot-s4-long (e (ex-kid-of e 2)))
                 (:instance aot-lval-i64 (e (ex-kid-of e 1)))
                 (:instance aot-lval-i64 (e (ex-kid-of e 2)) (fr (cadr (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel))))))))
(defthm aot-7fitl
  (implies (aot-7pre e n pool fr bt fuel)
           (and (aot-fitl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)))
                (equal (len (aot-7raw e fr fuel)) (aot-nargs (aot-pop e)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-7raw aot-nargs aot-unprim) (aot-7ih aot-7pre aot-i64p aot-tcok))
           :use ((:instance aot-7pre-facts) (:instance aot-7long)))))

; the first operand alone (a cast): its code, its read
(defthm aot-7one
  (implies (aot-7pre e n pool fr bt fuel)
           (let* ((r1 (aot-cc 5 (ex-kid-of e 1) (aot-7w e) n pool)) (q (aot-ir-run (car r1) fr bt nil fuel))
                  (x (aot-ev :m (ex-kid-of e 1) 0 nil fr fuel)) (xr (aot-xrun (cadr r1) (car q) (cadr q))))
             (and (caddr q) (not (cadddr q)) (aot-same n (cadr q) bt) (<= n (caddr r1))
                  (equal (cdr (car x)) (car xr)) (equal (cadr x) (cdr xr)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-7ih aot-7pre) (aot-cc-cl aot-tcok aot-ev aot-xrun))
           :use ((:instance aot-7pre-facts) (:instance aot-s4-kid (j 1))
                 ))))

(defmacro aot-7th (en dis)
  `(e/d (aot-cc-cl aot-cchyp aot-ccconcl aot-7pre ,@en) (aot-7ih aot-cc-7-is aot-7ops aot-pg ,@dis)))

; (double x): x read as a double
(defthm aot-cc-cl-7-dbl
  (implies (and (equal (aot-pop e) 21) (aot-7ih e n pool fr bt fuel)) (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-7th (aot-7raw aot-7fr aot-nargs) nil)
           :use ((:instance aot-7pre-facts) (:instance aot-7one) (:instance aot-cc-7-is)
                 (:instance aot-7aprim (pool pool)) (:instance aot-7fitl) (:instance aot-unguarded-inr (p 21) (w (aot-7w e))
                                                                  (vals (aot-cvl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)) (list 3))))))))

; (long x) of a long: x itself
(defthm aot-cc-cl-7-l2l
  (implies (and (equal (aot-pop e) 20) (equal (aot-7a0 e) 2) (aot-7ih e n pool fr bt fuel)) (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-7th (aot-7raw aot-7fr aot-nargs aot-7w aot-pw aot-i64p) nil)
           :use ((:instance aot-7pre-facts) (:instance aot-7one) (:instance aot-cc-7-is)
                 (:instance aot-s4-kid (j 1)) (:instance aot-s4-long (e (ex-kid-of e 1)))
                 (:instance aot-lval-i64 (e (ex-kid-of e 1)))
                 (:instance aot-7aprim (pool pool)) (:instance aot-7fitl)
                 (:instance aot-unguarded-inr (p 20) (w 2) (vals (aot-cvl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)) (list (aot-7w e) (aot-7w2 e)))))))))

; the facts of the operands, for the shapes that read them all
(defthm aot-7all
  (implies (aot-7pre e n pool fr bt fuel) (aot-7opsok e n pool fr bt fuel))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-7ih) (aot-7opsok aot-7ops aot-7raw aot-7fr aot-cc-cl aot-7pre))
           :cases ((< 2 (ex-nk e)))
           :use ((:instance aot-7pre-facts) (:instance aot-s4-kid (j 1)) (:instance aot-s4-kid (j 2))
                 (:instance aot-7ops-one) (:instance aot-7ops-two)))
          (and stable-under-simplificationp '(:in-theory (e/d (aot-7ih aot-7pre) (aot-7opsok aot-7ops aot-7raw aot-7fr aot-cc-cl))))))

; a Math member: the op on the operands, in place
(defthm aot-cc-cl-7-math
  (implies (and (< 21 (aot-pop e)) (aot-7ih e n pool fr bt fuel)) (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-7th (aot-7w aot-pw aot-7opsok) (aot-7raw aot-7fr aot-cvl aot-opx))
           :use ((:instance aot-7pre-facts) (:instance aot-7all) (:instance aot-cc-7-is)
                 (:instance aot-7aprim (pool pool)) (:instance aot-7fitl)
                 (:instance aot-unguarded-inr (p (aot-pop e)) (w (aot-7w e))
                            (vals (aot-cvl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)) (list (aot-7w e) (aot-7w2 e)))))))))

; an unguarded op set once into a temporary
(defthm aot-cc-cl-7-tset
  (implies (and (not (< 21 (aot-pop e))) (not (equal (aot-pop e) 21)) (not (equal (aot-pop e) 19)) (not (equal (aot-pop e) 20))
                (not (and (equal (aot-at e) 2) (member (aot-pop e) '(1 2 3 5 6))))
                (aot-7ih e n pool fr bt fuel))
           (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-7th (aot-7w aot-pw aot-7opsok) (aot-7raw aot-7fr aot-cvl aot-opx))
           :use ((:instance aot-7pre-facts) (:instance aot-7all) (:instance aot-cc-7-is)
                 (:instance aot-7aprim (pool pool)) (:instance aot-7fitl)
                 (:instance aot-unguarded-inr (p (aot-pop e)) (w (aot-7w e))
                            (vals (aot-cvl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)) (list (aot-7w e) (aot-7w2 e)))))))))

(defthm aot-cv-id (implies (not (and (equal a 2) (equal w 3))) (equal (aot-cv v a w) v)))
; a guarded op reads its operands at their own type: no long widened
(defthm aot-7guard-cvl
  (implies (and (aot-tcok e pool) (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)))
           (equal (aot-cvl (aot-7raw e fr fuel) (list (aot-7a0 e) (aot-7a1 e)) (list (aot-7w e) (aot-7w2 e))) (aot-7raw e fr fuel)))
  :hints (("Goal" :in-theory (e/d (aot-7raw aot-7w aot-7w2 aot-pw aot-nargs) (aot-tcok aot-ev aot-unprim)) :use ((:instance aot-tcok-more)))))
; a guarded op's long operands are longs (A-LONG)
(defthm aot-tcok-guard
  (implies (and (aot-tcok e pool) (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)) (equal (aot-7w e) 2))
           (and (equal (aot-7a0 e) 2) (implies (< 2 (ex-nk e)) (equal (aot-7a1 e) 2))))
  :rule-classes nil :hints (("Goal" :in-theory (e/d (aot-tcok) (aot-guarded aot-prim-ok)))))
(defthm aot-7guard-i64
  (implies (and (aot-7pre e n pool fr bt fuel) (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)) (equal (aot-7w e) 2))
           (aot-i64l (aot-7raw e fr fuel)))
  :hints (("Goal" :in-theory (e/d (aot-7raw) (aot-7ih aot-7pre aot-guarded aot-tcok))
           :use ((:instance aot-7pre-facts) (:instance aot-7long) (:instance aot-tcok-guard)))))

; the guarded op's instruction: its slots as the compile allocates them
(defthm aot-7prim-slots
  (implies (and (aot-pent h pool) (aot-pslt pool n) (natp n) (natp m) (<= n m))
           (let ((r (aot-cc 1 h 0 (+ 1 m) pool)))
             (aot-prim-slots (list :prim m ty p w xs (if (consp (car r)) (caddr (car (car r))) nil) (cadr r) (caddr r) (+ (caddr r) (len xs))) m)))
  :hints (("Goal" :in-theory (enable aot-prim-slots) :use ((:instance aot-pent-slot (e h))))))

; the guarded op's instruction as the compile writes it
(defun aot-7px (e n pool)
  (let* ((o (aot-7ops e n pool)) (m (caddr o)) (xs (cadr o)) (h (aot-cc 1 (ex-kid-of e 0) 0 (+ 1 m) pool)) (blk (caddr h)))
    (list :prim m (aot-at e) (aot-pop e) (aot-7w e) xs (if (consp (car h)) (caddr (car (car h))) nil) (cadr h) blk (+ blk (len xs)))))
(defthm aot-7px-op (equal (car (aot-7px e n pool)) :prim))
(defthm aot-cc-7-guarded
  (implies (and (consp e) (not (aot-unprim (aot-pop e) (aot-7a0 e) (aot-7a1 e))) (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)))
           (and (equal (car (aot-cc 7 e i n pool)) (append (car (aot-7ops e (nfix n) pool)) (list (aot-7px e (nfix n) pool))))
                (equal (cadr (aot-cc 7 e i n pool)) (list :tv (caddr (aot-7ops e (nfix n) pool)) (aot-at e)))))
  :hints (("Goal" :in-theory (e/d (aot-guarded aot-7px) (aot-cc-7-is aot-7ops)) :use ((:instance aot-cc-7-is)))))
(in-theory (disable aot-7px))

; the instruction, abstractly: its operands read vals and leave F, its head is f, the host's call of
; f on vals answers, and the op's value is that answer when the guard passes
(defthm aot-prim-step-gen
  (implies (and (aot-prim-slots x m) (natp n) (natp m) (<= n m)
                (equal (aot-xsrun (nth 5 x) fr bt) (cons vals f2))
                (equal (aot-hd (nth 6 x) (nth 7 x) bt) f)
                (consp (aot-hcall f vals)) (equal (car (aot-hcall f vals)) :val)
                (implies (aot-pg (nth 3 x) (nth 4 x) vals) (equal (aot-hcall f vals) (cons :val (aot-opx (nth 3 x) (nth 4 x) vals))))
                (aot-same n bt bt0))
           (let ((s (aot-ir-step x fr bt)))
             (and s (equal (car s) f2) (equal (nth (nth 1 x) (cadr s)) (cdr (aot-hcall f vals))) (aot-same n (cadr s) bt0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable aot-prim-run aot-ir-step aot-pg aot-opx aot-prim-slots aot-hd)
           :use ((:instance aot-prim-run (n m))
                 (:instance aot-same-lower (m m) (x (cadr (aot-ir-step x fr bt))) (y bt))
                 (:instance aot-same-trans (x (cadr (aot-ir-step x fr bt))) (y bt) (z bt0))))))

; the guard passing, A-PRIM answers the op's value
(defthm aot-7pass
  (implies (and (aot-7pre e n pool fr bt fuel) (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e))
                (aot-pg (aot-pop e) (aot-7w e) (aot-7raw e fr fuel)))
           (equal (aot-hcall (ex-c (ex-kid-of e 0)) (aot-7raw e fr fuel))
                  (cons :val (aot-opx (aot-pop e) (aot-7w e) (aot-7raw e fr fuel)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-guarded) (aot-7pre aot-7ih aot-7raw aot-pg aot-opx aot-cvl aot-pg-host aot-tcok aot-7guard-i64
                                                 aot-7guard-cvl aot-prim-ok aot-fmul-ok aot-fitl aot-i64l))
           :use ((:instance aot-7pre-facts) (:instance aot-7fitl) (:instance aot-7guard-i64) (:instance aot-tcok-prim) (:instance aot-7guard-cvl)
                 (:instance aot-pg-host (f (ex-c (ex-kid-of e 0))) (p (aot-pop e)) (w (aot-7w e)) (vals (aot-7raw e fr fuel))
                            (ts (list (aot-7a0 e) (aot-7a1 e))) (ws (list (aot-7w e) (aot-7w2 e))))))))

(defthm aot-7px-parts
  (and (equal (nth 1 (aot-7px e n pool)) (caddr (aot-7ops e n pool)))
       (equal (nth 3 (aot-7px e n pool)) (aot-pop e))
       (equal (nth 4 (aot-7px e n pool)) (aot-7w e))
       (equal (nth 5 (aot-7px e n pool)) (cadr (aot-7ops e n pool)))
       (equal (nth 6 (aot-7px e n pool)) (let ((h (aot-cc 1 (ex-kid-of e 0) 0 (+ 1 (caddr (aot-7ops e n pool))) pool))) (if (consp (car h)) (caddr (car (car h))) nil)))
       (equal (nth 7 (aot-7px e n pool)) (cadr (aot-cc 1 (ex-kid-of e 0) 0 (+ 1 (caddr (aot-7ops e n pool))) pool))))
  :hints (("Goal" :in-theory (e/d (aot-7px) (aot-cc-head aot-cc-head-pool)))))

(defthm aot-7px-slots
  (implies (and (aot-pent (ex-kid-of e 0) pool) (aot-pslt pool n) (natp n) (natp (caddr (aot-7ops e n pool))) (<= n (caddr (aot-7ops e n pool))))
           (aot-prim-slots (aot-7px e n pool) (caddr (aot-7ops e n pool))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-7px) (aot-prim-slots aot-7ops))
           :use ((:instance aot-7prim-slots (h (ex-kid-of e 0)) (m (caddr (aot-7ops e n pool))) (ty (aot-at e)) (p (aot-pop e)) (w (aot-7w e))
                            (xs (cadr (aot-7ops e n pool))))))))

(defthm aot-7prim-step
  (implies (and (aot-7pre e n pool fr bt fuel) (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)))
           (let* ((o (aot-7ops e n pool)) (r (aot-ir-run (car o) fr bt nil fuel))
                  (s (aot-ir-step (aot-7px e n pool) (car r) (cadr r))))
             (and s (equal (car s) (aot-7fr e fr fuel))
                  (equal (nth (caddr o) (cadr s)) (cdr (aot-hcall (ex-c (ex-kid-of e 0)) (aot-7raw e fr fuel))))
                  (aot-same n (cadr s) bt))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (aot-7opsok aot-7pre)
                                  (aot-7ih aot-7ops aot-7raw aot-7fr aot-pg aot-opx aot-cvl aot-ir-step aot-prim-slots aot-hd aot-guarded
                                   aot-ir-run aot-xsrun aot-ev aot-cc aot-cc-head-fn aot-tcok aot-7guard-cvl aot-cc-head aot-cc-head-pool))
           :use ((:instance aot-7pre-facts) (:instance aot-7all) (:instance aot-7pass) (:instance aot-7guard-cvl)
                 (:instance aot-7px-slots)
                 (:instance aot-cc-head-fn (h (ex-kid-of e 0)) (m (+ 1 (caddr (aot-7ops e n pool)))) (bt0 bt)
                            (bt (cadr (aot-ir-run (car (aot-7ops e n pool)) fr bt nil fuel))))
                 (:instance aot-prim-step-gen (x (aot-7px e n pool)) (m (caddr (aot-7ops e n pool)))
                            (fr (car (aot-ir-run (car (aot-7ops e n pool)) fr bt nil fuel)))
                            (bt (cadr (aot-ir-run (car (aot-7ops e n pool)) fr bt nil fuel)))
                            (vals (aot-7raw e fr fuel)) (f2 (aot-7fr e fr fuel)) (f (ex-c (ex-kid-of e 0))) (bt0 bt))))))

(defthm aot-cons-val (implies (equal (car x) :val) (equal (cons :val (cdr x)) x)))
(defthm aot-cc-cl-7-prim
  (implies (and (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)) (aot-7ih e n pool fr bt fuel))
           (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-7th (aot-guarded) (aot-7raw aot-7fr aot-ir-step aot-7opsok aot-ev))
           :use ((:instance aot-7pre-facts) (:instance aot-7all) (:instance aot-7prim-step) (:instance aot-cc-7-guarded)))
          (and stable-under-simplificationp (quote (:in-theory (aot-7th (aot-7opsok aot-guarded) (aot-7raw aot-7fr aot-ir-step aot-ev)))))))

; the induction's case, all shapes
(defthm aot-cc-cl-7
  (implies (aot-7ih e n pool fr bt fuel) (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((equal (aot-pop e) 21) (and (equal (aot-pop e) 20) (equal (aot-7a0 e) 2)) (< 21 (aot-pop e))
                          (aot-guarded (aot-pop e) (aot-at e) (aot-7a0 e)))
           :in-theory (e/d (aot-guarded) (aot-cc-cl aot-7ih)))))
; a call never answers a recur
(defun aot-call-ind (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (and (consp e) (< (nfix i) (ex-nk e)))
      (let ((r (aot-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (aot-call-ind e (+ 1 (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel))
    (list tmp fr)))
(defthm aot-call-norecur (not (equal (car (car (aot-ev :call e i tmp fr fuel))) :recur))
  :hints (("Goal" :induct (aot-call-ind e i tmp fr fuel) :expand ((aot-ev :call e i tmp fr fuel)) :in-theory (e/d (aot-happ (:induction aot-ev)) (aot-ex-ev-m-i)))))
(defthm aot-tcall-norecur
  (implies (equal (ex-kind e) 6) (not (equal (car (aot-ev :m e 0 nil fr fuel)) (quote (:recur)))))
  :hints (("Goal" :expand ((aot-ev :m e 0 nil fr fuel)) :use ((:instance aot-call-norecur (i 1) (tmp (list (ex-c (ex-kid-of e 0)))))
                                                          (:instance aot-call-norecur (i 1) (tmp (list (val (car (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)))))
                                                                     (fr (cadr (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)))))
           :in-theory (disable aot-call-norecur))))
(defthm aot-cc-cl-1-call
  (implies (and (equal (ex-kind e) 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0)) (aot-cc-cl 7 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 1 e i n pool)))))
(defthm aot-cc-cl-5-call
  (implies (and (equal (ex-kind e) 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0)) (aot-cc-cl 7 e 0 n pool fr bt fuel nil))
           (aot-cc-cl 5 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :expand ((aot-cc 5 e i n pool)))))
(defthm aot-cc-cl-6-bad
  (implies (and (equal (ex-kind e) 6) (not (and (aot-typ (aot-at e)) (not (equal (aot-pop e) 0)))))
           (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (aot-cc-theory) :use ((:instance aot-s4-tc) (:instance aot-tcok-parts)))))

(defthm aot-cc-cl-1-other
  (implies (and (not (member (ex-kind e) (quote (4 5 11 12 16)))) (not (and (equal (ex-kind e) 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0)))))
           (aot-cc-cl 1 e i n pool fr bt fuel tmp))
  :hints (("Goal" :cases ((equal (ex-kind e) 6)) :in-theory (disable aot-cc-cl))))
; the typed call case as the induction writes its hypotheses, the snapshot made or not
(defmacro aot-7ihx (snap)
  `(let* ((r1 (aot-cc 5 (ex-kid-of e 1) (aot-7w e) n pool)) (n1 (caddr r1))
          (r2 (aot-cc 5 (ex-kid-of e 2) (aot-7w2 e) (+ 1 n1) pool))
          (q1 (aot-ir-run (car r1) fr bt nil fuel))
          (xr (aot-xrun (cadr r1) (car q1) (cadr q1))))
     (and (aot-cc-cl 5 (ex-kid-of e 1) (aot-7w e) n pool fr bt fuel nil)
          ,(if snap `(consp (car r2)) `(not (consp (car r2))))
          (aot-cc-cl 5 (ex-kid-of e 2) (aot-7w2 e) (+ 1 n1) pool (cdr xr)
                     ,(if snap `(update-nth n1 (aot-cv (car xr) (aot-7a0 e) (aot-7w e)) (cadr q1)) `(cadr q1)) fuel nil))))
(defthm aot-cc-cl-7-snap
  (implies (aot-7ihx t) (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (e/d (aot-7ih) (aot-cc-cl-7 aot-cc-cl)) :use ((:instance aot-cc-cl-7)))))
(defthm aot-cc-cl-7-nosnap
  (implies (aot-7ihx nil) (aot-cc-cl 7 e i n pool fr bt fuel tmp))
  :hints (("Goal" :in-theory (e/d (aot-7ih) (aot-cc-cl-7 aot-cc-cl)) :use ((:instance aot-cc-cl-7)))))

; ---- THE THEOREM -----------------------------------------------------------------------------

(defthm aot-cc-sound
  (implies (member fl '(0 1 2 3 4 5 6 7)) (aot-cc-cl fl e i n pool fr bt fuel tmp))
  :hints (("Goal" :induct (aot-cc-ind fl e i n pool fr bt fuel tmp) :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (disable aot-cc-slot))))

; THE HEADLINE: a node of the subset, the pool as the host fills it, below the first temporary n:
; when ex-ev answers, the emitted code run on the same fuel runs to the end, its value in the slot
; aot-cc names is ex-ev's (or ex-ev's recur is the flag raised), the frame is ex-ev's, and no slot
; below n moved
(defthm aot-cc-correct
  (let* ((cc (aot-cc 0 e 0 n pool)) (r (aot-ir-run (car cc) fr bt nil fuel)) (x (aot-ev :m e 0 nil fr fuel)))
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

(defthm aot-ac-consp (implies (consp x) (<= 1 (acl2-count x))) :rule-classes :linear)
(defthm aot-nth-past (implies (and (natp i) (<= (len l) i)) (equal (nth i l) nil))
  :hints (("Goal" :induct (nth i l) :in-theory (enable nth))))
(defthm aot-kid-past (implies (and (natp i) (<= (ex-nk e) i)) (equal (ex-kid-of e i) nil))
  :hints (("Goal" :in-theory (enable ex-kid-of ex-nk))))
; a call (4c-ii): its kind, 6, and its three first kids fit in it with room
(defthm aot-kc-call
  (implies (and (consp e) (equal (ex-kind e) 6))
           (<= (+ 2 (acl2-count (ex-kid-of e 0)) (acl2-count (ex-kid-of e 1)) (acl2-count (ex-kid-of e 2))) (acl2-count e)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance aot-ac-3 (l (nth 2 e)))) :in-theory (e/d (ex-kid-of ex-kids ex-kind) (aot-ac-3))
                  :expand ((acl2-count e) (acl2-count (cdr e)) (acl2-count (cddr e)) (nth 2 e) (nth 1 (cdr e)) (nth 0 (cddr e))))))
(defthm aot-cc-cnt-bound
  (and (implies (equal fl 0) (<= (aot-cc-cnt fl e i) (+ 2 (* 6 (acl2-count e)))))
       (implies (and (equal fl 7) (consp e) (equal (ex-kind e) 6)) (<= (aot-cc-cnt fl e i) (* 6 (acl2-count e))))
       (implies (equal fl 1) (<= (aot-cc-cnt fl e i) (+ 1 (* 6 (acl2-count e)))))
       (implies (and (equal fl 2) (natp i) (< i (ex-nk e))) (<= (aot-cc-cnt fl e i) (* 6 (aot-kc e i))))
       (implies (and (equal fl 4) (natp i)) (<= (aot-cc-cnt fl e i) (+ 1 (* 6 (aot-kc e i)))))
       (implies (equal fl 5) (<= (aot-cc-cnt fl e i) (+ 3 (* 6 (acl2-count e)))))
       (implies (equal fl 6) (<= (aot-cc-cnt fl e i) (+ 4 (* 6 (acl2-count e)))))
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


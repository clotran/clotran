; Lock-free cell reads and atoms, formally (docs/model-coverage.md).
;
; src/c/seqlock.c and GC.f90: a shared cell -- a Var's root, an atom's,
; an agent's state, a namespace's mappings -- is a 16-byte value read
; with NO lock (gc_cell_get, clotran_seq_read16): load the sequence
; counter, retry while it is odd, copy both words, load it again, and
; keep the copy only if it did not move. Every write of such a cell is
; made under the state lock (gc_cell_set, gc_cell_cas, gc_root_cas), whose
; outermost acquire makes the counter odd (clotran_seq_begin) and whose
; release makes it even again (clotran_seq_end). Atoms: swap! and
; swap-vals! are the read / call f / compare-and-swap loop of
; model/casloop.lisp (Eval.f90, B_SWAPVAL); reset! and compare-and-set!
; are one write each under the state lock.
;
; Here a cell is two words, written one at a time (a 16-byte store is
; two 8-byte stores to any reader), by writers that each take the lock;
; readers take five steps -- load s1 (odd: again), word a, word b, load
; s2 (moved: again from the start). The interleaving is sequentially
; consistent: the C11 orders in seqlock.c are what make the hardware's
; agree with it (Boehm, "Can seqlocks get along with programming language
; memory models?", 2012) -- the release fence after clotran_seq_begin is
; the one his writer needs and acq_rel alone does not give.
;
; What it proves, under every interleaving of any writers and readers:
;
;   NO TORN READ  a read that ends returns both words of ONE committed
;                 value: the one current when it loaded s1 -- so it is
;                 linearizable at that load
;   THE RULE      this needs every write of the cell inside the lock: the
;                 counter even means no write is under way, and readers
;                 trust that (agent states and restart-agent stored
;                 without it until 2026-10-19)
;   ATOMS         swap! and swap-vals! from any number of threads are
;                 linearizable, each exactly once, lock-free, at most 2N + 2
;                 rounds a thread (casloop's theorems, instantiated)
;   COST          a read that does not end has seen the counter move: its
;                 failed checks are at most the counter's moves since it
;                 began, two a write -- at most 2 W retries of 4 steps for W
;                 writes that overlap it, and a spin on an odd counter lasts
;                 while one writer takes its 3 steps inside
;
; Not modelled: the lock itself (a pthread mutex: one writer at a time).

(in-package "ACL2")

(include-book "casloop")
(local (include-book "arithmetic-5/top" :dir :system))

; ---- the machine ------------------------------------------------------------------
;
; st = (seq cell vals lock ws rs): cell (a . b); vals the committed
; values, newest first, (car vals) the cell's value when seq is even; ws
; writers (pc todo) with todo the values left to write; rs readers
; (pc s1 a b start fails done res)

(defun mk-w (pc todo) (list pc todo))
(defun w-pc (x) (nth 0 x))
(defun w-todo (x) (nth 1 x))

(defun mk-r (pc s1 a b start fails res) (list pc s1 a b start fails res))
(defun r-pc (x) (nth 0 x))
(defun r-s1 (x) (nth 1 x))
(defun r-a (x) (nth 2 x))
(defun r-b (x) (nth 3 x))
(defun r-start (x) (nth 4 x))
(defun r-fails (x) (nth 5 x))
(defun r-res (x) (nth 6 x))

; a writer: the lock, the counter odd, word a, word b, the counter even
; and the value committed, the release
(defun w-step (i st)
  (let* ((seq (nth 0 st)) (cell (nth 1 st)) (vals (nth 2 st)) (lock (nth 3 st))
         (ws (nth 4 st)) (rs (nth 5 st)))
    (if (not (and (natp i) (< i (len ws)))) st
      (let* ((x (nth i ws)) (v (car (w-todo x))))
        (case (w-pc x)
          (:idle (if (and (consp (w-todo x)) (null lock))
                     (list seq cell vals i (update-nth i (mk-w :begin (w-todo x)) ws) rs)
                   st))
          (:begin (list (1+ seq) cell vals lock (update-nth i (mk-w :wa (w-todo x)) ws) rs))
          (:wa (list seq (cons (car v) (cdr cell)) vals lock (update-nth i (mk-w :wb (w-todo x)) ws) rs))
          (:wb (list seq (cons (car cell) (cdr v)) vals lock (update-nth i (mk-w :end (w-todo x)) ws) rs))
          (:end (list (1+ seq) cell (cons (cons (1+ seq) v) vals) lock (update-nth i (mk-w :rel (w-todo x)) ws) rs))
          (:rel (list seq cell vals nil (update-nth i (mk-w :idle (cdr (w-todo x))) ws) rs))
          (otherwise st))))))

; a reader: clotran_seq_read16
(defun r-step (j st)
  (let* ((seq (nth 0 st)) (cell (nth 1 st)) (vals (nth 2 st)) (lock (nth 3 st))
         (ws (nth 4 st)) (rs (nth 5 st)))
    (if (not (and (natp j) (< j (len rs)))) st
      (let ((x (nth j rs)))
        (case (r-pc x)
          (:s1 (if (oddp seq) st
                 (list seq cell vals lock ws
                       (update-nth j (mk-r :ra seq nil nil (r-start x) (r-fails x) nil) rs))))
          (:ra (list seq cell vals lock ws
                     (update-nth j (mk-r :rb (r-s1 x) (car cell) nil (r-start x) (r-fails x) nil) rs)))
          (:rb (list seq cell vals lock ws
                     (update-nth j (mk-r :s2 (r-s1 x) (r-a x) (cdr cell) (r-start x) (r-fails x) nil) rs)))
          (:s2 (if (equal seq (r-s1 x))
                   (list seq cell vals lock ws
                         (update-nth j (mk-r :done (r-s1 x) (r-a x) (r-b x) (r-start x) (r-fails x)
                                             (cons (r-a x) (r-b x))) rs))
                 (list seq cell vals lock ws
                       (update-nth j (mk-r :s1 nil nil nil (r-start x) (1+ (r-fails x)) nil) rs))))
          (otherwise st))))))

; a schedule: (:w . i) or (:r . j)
(defun sl-step (e st) (if (eq (car e) :w) (w-step (cdr e) st) (r-step (cdr e) st)))
(defun sl-run (sched st) (if (atom sched) st (sl-run (cdr sched) (sl-step (car sched) st))))

; ---- the invariant -------------------------------------------------------------------
;
; vals: (s . v) pairs, newest first, s the even counter value v was
; committed under

(defun val-of (s vals) (cdr (assoc-equal s vals)))

(defun pairs-p (l) (if (atom l) t (and (consp (car l)) (pairs-p (cdr l)))))

(defun w-ok (x i seq cell vals lock)
  (let ((v (car (w-todo x))))
    (and (pairs-p (w-todo x))
         (case (w-pc x)
           (:idle (not (equal lock i)))
           (:begin (and (equal lock i) (evenp seq) (consp (w-todo x))))
           (:wa (and (equal lock i) (oddp seq) (consp (w-todo x)) (equal cell (cdar vals))))
           (:wb (and (equal lock i) (oddp seq) (consp (w-todo x))
                     (equal (car cell) (car v)) (equal (cdr cell) (cdr (cdar vals)))))
           (:end (and (equal lock i) (oddp seq) (consp (w-todo x))
                      (equal (car cell) (car v)) (equal (cdr cell) (cdr v))))
           (:rel (and (equal lock i) (evenp seq) (consp (w-todo x))))
           (otherwise nil)))))

(defun r-ok (x seq vals)
  (let ((s1 (r-s1 x)) (f (r-fails x)) (st (r-start x)))
    (and (natp f) (natp st) (<= st seq)
         (case (r-pc x)
           (:s1 (<= f (- seq st)))
           (:ra (and (natp s1) (evenp s1) (<= s1 seq) (<= st s1) (<= f (- s1 st))))
           (:rb (and (natp s1) (evenp s1) (<= s1 seq) (<= st s1) (<= f (- s1 st))
                     (implies (equal seq s1) (equal (r-a x) (car (val-of s1 vals))))))
           (:s2 (and (natp s1) (evenp s1) (<= s1 seq) (<= st s1) (<= f (- s1 st))
                     (implies (equal seq s1) (and (equal (r-a x) (car (val-of s1 vals)))
                                                  (equal (r-b x) (cdr (val-of s1 vals)))))))
           (:done (and (natp s1) (evenp s1) (<= s1 seq) (<= st s1) (<= f (- s1 st)) (equal (r-res x) (val-of s1 vals))))
           (otherwise nil)))))

(defun ws-ok (k ws seq cell vals lock)
  (if (zp k) t (and (w-ok (nth (1- k) ws) (1- k) seq cell vals lock) (ws-ok (1- k) ws seq cell vals lock))))

(defun rs-ok (k rs seq vals)
  (if (zp k) t (and (r-ok (nth (1- k) rs) seq vals) (rs-ok (1- k) rs seq vals))))

(defun sl-inv (st)
  (let ((seq (nth 0 st)) (cell (nth 1 st)) (vals (nth 2 st)) (lock (nth 3 st)) (ws (nth 4 st)) (rs (nth 5 st)))
    (and (true-listp st) (equal (len st) 6)
         (natp seq) (consp vals) (consp (car vals)) (consp cell)
         (equal (caar vals) (if (evenp seq) seq (1- seq)))
         (implies (evenp seq) (equal cell (cdar vals)))
         (implies (oddp seq) lock)
         (or (null lock) (and (natp lock) (< lock (len ws))))
         (ws-ok (len ws) ws seq cell vals lock)
         (rs-ok (len rs) rs seq vals))))

(defthm ws-ok-nth
  (implies (and (ws-ok k ws seq cell vals lock) (natp i) (natp k) (< i k))
           (w-ok (nth i ws) i seq cell vals lock)))

(defthm rs-ok-nth
  (implies (and (rs-ok k rs seq vals) (natp j) (natp k) (< j k))
           (r-ok (nth j rs) seq vals)))

(in-theory (disable w-ok r-ok))

; the readers, when the counter or the committed values move
(defthm r-ok-seq-up
  (implies (and (r-ok x seq vals) (natp seq)) (r-ok x (1+ seq) vals))
  :hints (("Goal" :in-theory (enable r-ok))))

(defthm r-ok-commit
  (implies (and (r-ok x seq vals) (natp seq))
           (r-ok x (1+ seq) (cons (cons (1+ seq) v) vals)))
  :hints (("Goal" :in-theory (enable r-ok))))

(defthm rs-ok-seq-up
  (implies (and (rs-ok k rs seq vals) (natp seq)) (rs-ok k rs (1+ seq) vals)))

(defthm rs-ok-commit
  (implies (and (rs-ok k rs seq vals) (natp seq)) (rs-ok k rs (1+ seq) (cons (cons (1+ seq) v) vals))))

(defthm rs-ok-own
  (implies (and (rs-ok k rs seq vals) (natp j) (r-ok y seq vals))
           (rs-ok k (update-nth j y rs) seq vals)))

(defthm len-update-nth-sl
  (implies (and (natp i) (< i (len l))) (equal (len (update-nth i y l)) (len l))))


; the writers: with the lock free or i's, every other writer is idle, and
; stays fine whatever i does
(defthm w-ok-other
  (implies (and (w-ok x j seq cell vals lock) (natp j) (natp i) (not (equal j i))
                (or (null lock) (equal lock i)) (or (null lock2) (equal lock2 i)))
           (w-ok x j seq2 cell2 vals2 lock2))
  :hints (("Goal" :in-theory (enable w-ok))))

(defthm ws-ok-holder
  (implies (and (ws-ok k ws seq cell vals lock) (natp i)
                (or (null lock) (equal lock i)) (or (null lock2) (equal lock2 i))
                (w-ok y i seq2 cell2 vals2 lock2))
           (ws-ok k (update-nth i y ws) seq2 cell2 vals2 lock2))
  :hints (("Goal" :induct (ws-ok k ws seq cell vals lock))))

(defthm pairs-p-cdr (implies (pairs-p l) (pairs-p (cdr l))))

(defthm cons-car-cdr-sl (implies (consp v) (equal (cons (car v) (cdr v)) v)))

(defthm pairs-p-car (implies (and (pairs-p l) (consp l)) (consp (car l))))

(defthm cons-by-parts
  (implies (and (consp a) (consp b) (equal (car a) (car b)) (equal (cdr a) (cdr b))) (equal (equal a b) t)))

(defthm assoc-cons-other
  (implies (not (equal s k)) (equal (assoc-equal s (cons (cons k v) vals)) (assoc-equal s vals))))

; ---- each step keeps it ------------------------------------------------------------------

(defthm update-nth-nth-same-sl
  (implies (and (natp i) (< i (len l))) (equal (update-nth i (nth i l) l) l)))

; a writer step replaces writer i only, and the lock is free or i's after it
(defthm w-step-ws
  (implies (and (natp i) (< i (len (nth 4 st))))
           (equal (update-nth i (nth i (nth 4 (w-step i st))) (nth 4 st)) (nth 4 (w-step i st)))))

(defthm w-step-lock
  (implies (and (natp i) (or (null (nth 3 st)) (equal (nth 3 st) i)))
           (or (null (nth 3 (w-step i st))) (equal (nth 3 (w-step i st)) i)))
  :rule-classes nil)

(defthm w-step-keeps-inv
  (implies (and (sl-inv st) (natp i) (< i (len (nth 4 st))))
           (sl-inv (w-step i st)))
  :hints (("Goal" :in-theory (e/d (w-ok) (ws-ok-nth))
                  :do-not-induct t
                  :use ((:instance ws-ok-nth (k (len (nth 4 st))) (ws (nth 4 st)) (seq (nth 0 st))
                                   (cell (nth 1 st)) (vals (nth 2 st)) (lock (nth 3 st)))
                        (:instance ws-ok-nth (k (len (nth 4 st))) (ws (nth 4 st)) (seq (nth 0 st))
                                   (cell (nth 1 st)) (vals (nth 2 st)) (lock (nth 3 st)) (i (nth 3 st)))
                        (:instance w-step-lock)
                        (:instance ws-ok-holder (k (len (nth 4 st))) (ws (nth 4 st)) (seq (nth 0 st)) (cell (nth 1 st))
                                   (vals (nth 2 st)) (lock (nth 3 st)) (y (nth i (nth 4 (w-step i st))))
                                   (seq2 (nth 0 (w-step i st))) (cell2 (nth 1 (w-step i st))) (vals2 (nth 2 (w-step i st))) (lock2 (nth 3 (w-step i st))))))))

(defthm val-of-newest
  (implies (and (consp vals) (equal (caar vals) s)) (equal (val-of s vals) (cdar vals))))

(defthm r-step-rs
  (implies (and (natp j) (< j (len (nth 5 st))))
           (equal (update-nth j (nth j (nth 5 (r-step j st))) (nth 5 st)) (nth 5 (r-step j st)))))

(defthm r-step-globals
  (and (equal (nth 0 (r-step j st)) (nth 0 st)) (equal (nth 1 (r-step j st)) (nth 1 st)) (equal (nth 2 (r-step j st)) (nth 2 st))
       (equal (nth 3 (r-step j st)) (nth 3 st)) (equal (nth 4 (r-step j st)) (nth 4 st))))

(defthm r-step-keeps-inv
  (implies (and (sl-inv st) (natp j) (< j (len (nth 5 st))))
           (sl-inv (r-step j st)))
  :hints (("Goal" :in-theory (e/d (r-ok) (rs-ok-nth))
                  :do-not-induct t
                  :use ((:instance rs-ok-nth (k (len (nth 5 st))) (rs (nth 5 st)) (seq (nth 0 st)) (vals (nth 2 st)))
                        (:instance rs-ok-own (k (len (nth 5 st))) (rs (nth 5 st)) (seq (nth 0 st)) (vals (nth 2 st))
                                   (y (nth j (nth 5 (r-step j st)))))))))

(defthm sl-step-keeps-inv
  (implies (sl-inv st) (sl-inv (sl-step e st)))
  :hints (("Goal" :in-theory (disable w-step r-step sl-inv)
                  :cases ((and (eq (car e) :w) (natp (cdr e)) (< (cdr e) (len (nth 4 st))))
                          (and (not (eq (car e) :w)) (natp (cdr e)) (< (cdr e) (len (nth 5 st))))))
          ("Subgoal 3" :in-theory (enable w-step r-step))))

(defthm sl-inv-run
  (implies (sl-inv st) (sl-inv (sl-run sched st)))
  :hints (("Goal" :in-theory (disable sl-step sl-inv))))

; the start: the counter 0, the cell its first value, writers with their
; values (pairs), readers at :s1
(defun init-ws (todos) (if (atom todos) nil (cons (mk-w :idle (car todos)) (init-ws (cdr todos)))))
(defun init-rs (n) (if (zp n) nil (cons (mk-r :s1 nil nil nil 0 0 nil) (init-rs (1- n)))))
(defun todos-ok (todos) (if (atom todos) t (and (pairs-p (car todos)) (todos-ok (cdr todos)))))
(defun sl-start (cell0 todos nr) (list 0 cell0 (list (cons 0 cell0)) nil (init-ws todos) (init-rs nr)))

(defthm len-init-ws (equal (len (init-ws todos)) (len todos)))
(defthm len-init-rs (equal (len (init-rs n)) (nfix n)))
(defthm nth-init-ws
  (implies (< (nfix i) (len todos)) (equal (nth i (init-ws todos)) (mk-w :idle (nth i todos)))))
(defun dec2-sl (i n) (if (or (zp i) (zp n)) nil (dec2-sl (1- i) (1- n))))
(defthm nth-init-rs
  (implies (< (nfix i) (nfix n)) (equal (nth i (init-rs n)) (mk-r :s1 nil nil nil 0 0 nil)))
  :hints (("Goal" :induct (dec2-sl i n))))
(defthm todos-ok-nth (implies (todos-ok todos) (pairs-p (nth i todos))))

(defthm ws-ok-init
  (implies (and (todos-ok todos) (<= (nfix k) (len todos)))
           (ws-ok k (init-ws todos) 0 cell vals nil))
  :hints (("Goal" :induct (ws-ok k (init-ws todos) 0 cell vals nil) :in-theory (e/d (w-ok) (init-ws)))))

(defthm rs-ok-init
  (implies (<= (nfix k) (nfix n)) (rs-ok k (init-rs n) 0 vals))
  :hints (("Goal" :induct (rs-ok k (init-rs n) 0 vals) :in-theory (e/d (r-ok) (init-rs)))))

(defthm sl-inv-start
  (implies (and (consp cell0) (todos-ok todos)) (sl-inv (sl-start cell0 todos nr))))

(defthm sl-reached
  (implies (and (consp cell0) (todos-ok todos)) (sl-inv (sl-run sched (sl-start cell0 todos nr))))
  :hints (("Goal" :in-theory (disable sl-inv sl-run sl-start))))

(in-theory (disable sl-run sl-start))

(defthm sl-inv-readers
  (implies (sl-inv st) (rs-ok (len (nth 5 st)) (nth 5 st) (nth 0 st) (nth 2 st)))
  :rule-classes nil)

(defthm r-ok-done
  (implies (and (r-ok x seq vals) (equal (r-pc x) :done))
           (and (evenp (r-s1 x)) (<= (r-s1 x) seq) (equal (r-res x) (val-of (r-s1 x) vals))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable r-ok))))

; NO TORN READ: a read that ended has both words of the one value committed
; under the even counter it began from -- the value the cell held then
(defthm sl-no-torn-read
  (implies (and (consp cell0) (todos-ok todos) (natp j)
                (< j (len (nth 5 (sl-run sched (sl-start cell0 todos nr)))))
                (equal (r-pc (nth j (nth 5 (sl-run sched (sl-start cell0 todos nr))))) :done))
           (let* ((st (sl-run sched (sl-start cell0 todos nr))) (x (nth j (nth 5 st))))
             (and (evenp (r-s1 x))
                  (equal (r-res x) (val-of (r-s1 x) (nth 2 st))))))
  :hints (("Goal" :use ((:instance sl-inv-readers (st (sl-run sched (sl-start cell0 todos nr))))
                        (:instance rs-ok-nth (k (len (nth 5 (sl-run sched (sl-start cell0 todos nr)))))
                                   (rs (nth 5 (sl-run sched (sl-start cell0 todos nr))))
                                   (seq (nth 0 (sl-run sched (sl-start cell0 todos nr))))
                                   (vals (nth 2 (sl-run sched (sl-start cell0 todos nr)))))
                        (:instance r-ok-done (x (nth j (nth 5 (sl-run sched (sl-start cell0 todos nr)))))
                                   (seq (nth 0 (sl-run sched (sl-start cell0 todos nr))))
                                   (vals (nth 2 (sl-run sched (sl-start cell0 todos nr))))))
                  :in-theory (disable sl-inv rs-ok-nth))))

(defthm r-ok-fails
  (implies (r-ok x seq vals)
           (and (natp (r-fails x)) (<= (r-fails x) (- seq (r-start x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable r-ok))))

; COST: a read's failed checks are at most the counter's moves since it
; began, two a write
(defthm sl-retry-bound
  (implies (and (consp cell0) (todos-ok todos) (natp j)
                (< j (len (nth 5 (sl-run sched (sl-start cell0 todos nr))))))
           (let* ((st (sl-run sched (sl-start cell0 todos nr))) (x (nth j (nth 5 st))))
             (<= (r-fails x) (- (nth 0 st) (r-start x)))))
  :hints (("Goal" :use ((:instance sl-inv-readers (st (sl-run sched (sl-start cell0 todos nr))))
                        (:instance rs-ok-nth (k (len (nth 5 (sl-run sched (sl-start cell0 todos nr)))))
                                   (rs (nth 5 (sl-run sched (sl-start cell0 todos nr))))
                                   (seq (nth 0 (sl-run sched (sl-start cell0 todos nr))))
                                   (vals (nth 2 (sl-run sched (sl-start cell0 todos nr)))))
                        (:instance r-ok-fails (x (nth j (nth 5 (sl-run sched (sl-start cell0 todos nr)))))
                                   (seq (nth 0 (sl-run sched (sl-start cell0 todos nr))))
                                   (vals (nth 2 (sl-run sched (sl-start cell0 todos nr))))))
                  :in-theory (disable sl-inv rs-ok-nth))))

; the counter moves twice a committed write: it is twice the writes, plus
; one while a write is under way
(defthm sl-counter-is-writes
  (implies (sl-inv st)
           (equal (caar (nth 2 st)) (if (evenp (nth 0 st)) (nth 0 st) (1- (nth 0 st)))))
  :rule-classes nil)

; ---- ATOMS: swap! and swap-vals!, casloop for any function -----------------------------

(defstub swap-fn (* *) => *)

(defun at-replay-ok (hist s ops)
  (if (atom hist) t
    (and (consp (car hist)) (equal (cdar hist) s)
         (at-replay-ok (cdr hist) (swap-fn (nth (caar hist) ops) s) ops))))

(defun at-replay-final (hist s ops)
  (if (atom hist) s
    (at-replay-final (cdr hist) (swap-fn (nth (caar hist) ops) (cdar hist)) ops)))

; B_SWAPVAL's loop: never done at the read (it always swaps), and it
; answers [old new] (swap-vals!; swap! the second)
(defun at-cas-step (i b st ops)
  (let* ((cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let* ((x (nth i ths)) (op (nth i ops)))
        (case (th-pc x)
          (:read (if nil
                     (list cell count (append hist (list (cons i cell)))
                           (update-nth i (mk-th :done cell 0 (th-fails x) (1+ (th-steps x)) (cons cell (swap-fn op cell))) ths))
                   (list cell count hist
                         (update-nth i (mk-th :cas cell count (th-fails x) (1+ (th-steps x)) nil) ths))))
          (:cas (if (and (equal cell (th-snap x)) (or (equal count (th-snapc x)) (not b)))
                    (list (swap-fn op cell) (1+ count) (append hist (list (cons i cell)))
                          (update-nth i (mk-th :done cell 0 (th-fails x) (1+ (th-steps x)) (cons cell (swap-fn op cell))) ths))
                  (list cell count hist
                        (update-nth i (mk-th :read nil 0 (1+ (th-fails x)) (1+ (th-steps x)) nil) ths))))
          (otherwise st))))))

(defun at-cas-run (sched st ops)
  (if (atom sched) st (at-cas-run (cdr sched) (at-cas-step (caar sched) (cdar sched) st ops) ops)))

(defthm atom-swap-linearizable
  (let ((st (at-cas-run sched (cas-start n cell0) ops)))
    (and (at-replay-ok (nth 2 st) cell0 ops)
         (equal (at-replay-final (nth 2 st) cell0 ops) (nth 0 st))))
  :hints (("Goal" :use ((:functional-instance cas-linearizable
                         (op-next swap-fn) (op-noop (lambda (op m) nil))
                         (op-result (lambda (op m) (cons m (swap-fn op m))))
                         (replay-ok at-replay-ok) (replay-final at-replay-final)
                         (cas-step at-cas-step) (cas-run at-cas-run))))))

(defthm atom-swap-results
  (let ((st (at-cas-run sched (cas-start n cell0) ops)))
    (implies (and (natp i) (< i (nfix n)) (equal (th-pc (nth i (nth 3 st))) :done))
             (equal (th-result (nth i (nth 3 st)))
                    (let ((old (cdr (assoc-equal i (nth 2 st))))) (cons old (swap-fn (nth i ops) old))))))
  :hints (("Goal" :use ((:functional-instance cas-results
                         (op-next swap-fn) (op-noop (lambda (op m) nil))
                         (op-result (lambda (op m) (cons m (swap-fn op m))))
                         (replay-ok at-replay-ok) (replay-final at-replay-final)
                         (cas-step at-cas-step) (cas-run at-cas-run))))))

(defthm atom-swap-exactly-once
  (let ((st (at-cas-run sched (cas-start n cell0) ops)))
    (and (no-duplicatesp-equal (strip-cars (nth 2 st)))
         (implies (and (natp i) (< i (nfix n)))
                  (iff (assoc-equal i (nth 2 st)) (equal (th-pc (nth i (nth 3 st))) :done)))))
  :hints (("Goal" :use ((:functional-instance cas-exactly-once
                         (op-next swap-fn) (op-noop (lambda (op m) nil))
                         (op-result (lambda (op m) (cons m (swap-fn op m))))
                         (replay-ok at-replay-ok) (replay-final at-replay-final)
                         (cas-step at-cas-step) (cas-run at-cas-run))))))

(defthm atom-swap-cost
  (let ((st (at-cas-run sched (cas-start n cell0) ops)))
    (implies (and (natp i) (< i (nfix n)))
             (and (<= (th-fails (nth i (nth 3 st))) (nfix n))
                  (<= (th-steps (nth i (nth 3 st))) (+ 2 (* 2 (nfix n)))))))
  :hints (("Goal" :use ((:functional-instance cas-cost
                         (op-next swap-fn) (op-noop (lambda (op m) nil))
                         (op-result (lambda (op m) (cons m (swap-fn op m))))
                         (replay-ok at-replay-ok) (replay-final at-replay-final)
                         (cas-step at-cas-step) (cas-run at-cas-run))))))

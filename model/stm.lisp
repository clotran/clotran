; clotran's transactions (STM), formally (docs/model-coverage.md).
;
; src/f/Eval.f90 runs every dosync under ONE lock, tx_lk (B_RUNTX,
; DEVIATIONS 10): the outermost dosync of a thread takes it, a dosync
; inside is the same transaction; deref of a ref in a transaction reads
; the transaction's log, else the committed value (tx_value); alter,
; ref-set and commute write the log (tx_log); at the end tx_commit
; validates every ref in the log -- one refusal and nothing is written
; -- then writes every one; the lock is released; then the watches run,
; then the sends made inside are dispatched (LockingTransaction.run's
; order). An error in the body discards the log. Outside a transaction
; nothing writes a ref: ref-set and alter refuse, and swap!, swap-vals!,
; reset-vals! and compare-and-set! refuse a ref as clj does (a Ref is
; not an IAtom).
;
; Here refs are an alist ref -> value, a transaction a list of ops:
; (:read r), (:alter r) -- the new value (alter-fn op old), whatever the
; function -- and (:fail), an error; a validator is valid-p, any
; predicate. Threads each run a list of transactions; the lock is one
; slot. A watch's own dosync is one more transaction of its thread,
; after the lock is released.
;
; What it proves, under every interleaving:
;
;   SERIALIZABLE  the committed state is the transactions run one after
;                 another, in the order they took the lock, from the first
;                 state; a read in a transaction sees exactly what that
;                 serial run reads: the state the lock was taken in, under
;                 its own writes
;   ALL OR NONE   a commit writes every ref of its log or none (a
;                 validator's refusal, an error); a watch that throws runs
;                 after the writes, so it cannot leave half a commit
;   ONCE, IN ORDER each thread's transactions finish once each, in its
;                 program order
;   NO DEADLOCK   the holder of the lock never waits: it can always step,
;                 and only a thread at :idle ever waits, for the holder --
;                 so a watch's dosync, after the release, cannot wait on
;                 its own thread
;   COST          a transaction releases the lock within |tx| + 2 of its
;                 own steps after taking it (no other thread's step moves
;                 it meanwhile); its commit validates and writes 2 |log|
;                 <= 2 |tx| refs
;
; Not modelled: the wait for the lock outside the running mutators (a
; collection's stop, the multi-threaded heap row), and what a watch does
; but run its own transactions.

(in-package "ACL2")

(defstub alter-fn (* *) => *)
(defstub valid-p (* *) => *)

(defun ref-val (r refs) (cdr (assoc-equal r refs)))

; a transaction's view: its log's value, else the committed one (tx_value)
(defun tx-val (r log refs) (if (assoc-equal r log) (cdr (assoc-equal r log)) (ref-val r refs)))

(defun op-kind (op) (car op))
(defun op-ref (op) (cadr op))

; ---- the serial meaning --------------------------------------------------------

; a body run from a log: the log after it, or :fail
(defun seq-log (ops log refs)
  (cond ((atom ops) log)
        ((eq (op-kind (car ops)) :fail) :fail)
        ((eq (op-kind (car ops)) :alter)
         (seq-log (cdr ops)
                  (put-assoc-equal (op-ref (car ops)) (alter-fn (car ops) (tx-val (op-ref (car ops)) log refs)) log)
                  refs))
        (t (seq-log (cdr ops) log refs))))

(defun all-valid (log)
  (if (atom log) t (and (valid-p (caar log) (cdar log)) (all-valid (cdr log)))))

(defun apply-log (log refs)
  (if (atom log) refs (apply-log (cdr log) (put-assoc-equal (caar log) (cdar log) refs))))

; one transaction on its own: the state after it
(defun seq-tx (tx refs)
  (let ((log (seq-log tx nil refs)))
    (if (and (not (eq log :fail)) (all-valid log)) (apply-log log refs) refs)))

; ---- the machine ------------------------------------------------------------------
;
; a thread (pc ops done log txs at): pc :idle (txs to run), :body (ops
; left, done run, log), :commit, :notify; `at` the state when it took the
; lock (a ghost, for the proof). st = (refs lock hist ths), lock nil or the
; holder, hist the finished transactions (i tx before) in order.

(defun mk-tt (pc ops done log txs at) (list pc ops done log txs at))
(defun tt-pc (x) (nth 0 x))
(defun tt-ops (x) (nth 1 x))
(defun tt-done (x) (nth 2 x))
(defun tt-log (x) (nth 3 x))
(defun tt-txs (x) (nth 4 x))
(defun tt-at (x) (nth 5 x))

(defun stm-step (i st)
  (let* ((refs (nth 0 st)) (lock (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let ((x (nth i ths)))
        (case (tt-pc x)
          ; the outermost dosync: the lock, or wait for it
          (:idle (if (and (consp (tt-txs x)) (null lock))
                     (list refs i hist (update-nth i (mk-tt :body (car (tt-txs x)) nil nil (tt-txs x) refs) ths))
                   st))
          (:body
           (let ((ops (tt-ops x)) (log (tt-log x)))
             (cond ((atom ops) (list refs lock hist (update-nth i (mk-tt :commit nil (tt-done x) log (tt-txs x) (tt-at x)) ths)))
                   ; an error: the log discarded, the lock released
                   ((eq (op-kind (car ops)) :fail)
                    (list refs nil (append hist (list (list i (car (tt-txs x)) refs)))
                          (update-nth i (mk-tt :idle nil nil nil (cdr (tt-txs x)) nil) ths)))
                   ((eq (op-kind (car ops)) :alter)
                    (list refs lock hist
                          (update-nth i (mk-tt :body (cdr ops) (append (tt-done x) (list (car ops)))
                                               (put-assoc-equal (op-ref (car ops))
                                                                (alter-fn (car ops) (tx-val (op-ref (car ops)) log refs)) log)
                                               (tt-txs x) (tt-at x)) ths)))
                   ; a read: tx-val of the log and refs, nothing written
                   (t (list refs lock hist
                            (update-nth i (mk-tt :body (cdr ops) (append (tt-done x) (list (car ops))) log (tt-txs x) (tt-at x)) ths))))))
          ; tx_commit: validate all, then write all; then the release
          (:commit (list (if (all-valid (tt-log x)) (apply-log (tt-log x) refs) refs)
                         nil (append hist (list (list i (car (tt-txs x)) refs)))
                         (update-nth i (mk-tt :notify nil nil nil (tt-txs x) nil) ths)))
          ; the watches and the sends, the lock released: nothing to wait for
          (:notify (list refs lock hist (update-nth i (mk-tt :idle nil nil nil (cdr (tt-txs x)) nil) ths)))
          (otherwise st))))))

(defun stm-run (sched st) (if (atom sched) st (stm-run (cdr sched) (stm-step (car sched) st))))

; ---- the invariant --------------------------------------------------------------

; the transactions of thread j in hist, in order
(defun hist-txs (j hist)
  (cond ((atom hist) nil)
        ((equal (car (car hist)) j) (cons (cadr (car hist)) (hist-txs j (cdr hist))))
        (t (hist-txs j (cdr hist)))))

; hist replayed serially from refs0: each entry ran on the state before it
(defun stm-replay-ok (hist s)
  (if (atom hist) t
    (and (equal (caddr (car hist)) s) (stm-replay-ok (cdr hist) (seq-tx (cadr (car hist)) s)))))

(defun stm-replay-final (hist s)
  (if (atom hist) s (stm-replay-final (cdr hist) (seq-tx (cadr (car hist)) (caddr (car hist))))))

(defun tt-ok (x j refs lock hist prog)
  (case (tt-pc x)
    (:idle (and (not (equal lock j)) (true-list-listp (tt-txs x)) (equal (append (hist-txs j hist) (tt-txs x)) prog)))
    (:notify (and (not (equal lock j)) (consp (tt-txs x)) (true-list-listp (tt-txs x))
                  (equal (append (hist-txs j hist) (cdr (tt-txs x))) prog)))
    ((:body :commit)
     (and (equal lock j) (consp (tt-txs x)) (true-list-listp (tt-txs x)) (true-listp (tt-ops x))
          (equal (append (hist-txs j hist) (tt-txs x)) prog)
          (equal (tt-at x) refs)
          (true-listp (tt-done x))
          (equal (append (tt-done x) (tt-ops x)) (car (tt-txs x)))
          (not (eq (tt-log x) :fail))
          (equal (tt-log x) (seq-log (tt-done x) nil refs))
          (implies (eq (tt-pc x) :commit) (atom (tt-ops x)))))
    (otherwise nil)))

(in-theory (disable tt-ok))

(defun tts-ok (k ths refs lock hist progs)
  (if (zp k) t
    (and (tt-ok (nth (1- k) ths) (1- k) refs lock hist (nth (1- k) progs))
         (tts-ok (1- k) ths refs lock hist progs))))

(defun stm-inv (st refs0 progs)
  (let ((refs (nth 0 st)) (lock (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
    (and (true-listp st) (equal (len st) 4)
         (or (null lock) (and (natp lock) (< lock (len ths))))
         (stm-replay-ok hist refs0) (equal (stm-replay-final hist refs0) refs)
         (tts-ok (len ths) ths refs lock hist progs))))

(defthm tts-ok-nth
  (implies (and (tts-ok k ths refs lock hist progs) (natp i) (natp k) (< i k))
           (tt-ok (nth i ths) i refs lock hist (nth i progs)))
  :hints (("Goal" :induct (tts-ok k ths refs lock hist progs))))

; ---- facts of the serial meaning ------------------------------------------------

(defthm seq-log-append
  (implies (not (equal log :fail))
           (equal (seq-log (append a b) log refs)
                  (let ((l (seq-log a log refs))) (if (eq l :fail) :fail (seq-log b l refs))))))

(defthm hist-txs-append-one
  (equal (hist-txs j (append hist (list (list i tx b))))
         (if (equal j i) (append (hist-txs j hist) (list tx)) (hist-txs j hist))))

(defthm stm-replay-ok-append
  (implies (stm-replay-ok h s)
           (equal (stm-replay-ok (append h (list (list i tx b))) s)
                  (equal b (stm-replay-final h s))))
  :hints (("Goal" :induct (stm-replay-ok h s))))

(defthm stm-replay-final-append
  (equal (stm-replay-final (append h (list (list i tx b))) s) (seq-tx tx b))
  :hints (("Goal" :induct (stm-replay-final h s))))

(defthm append-assoc-stm (equal (append (append a b) c) (append a (append b c))))

; ---- the other threads, when the lock is taken or released ------------------------

(defthm tt-ok-other-acquire
  (implies (and (tt-ok x j refs nil hist prog) (natp j) (natp i) (not (equal j i)))
           (tt-ok x j refs i hist prog))
  :hints (("Goal" :in-theory (enable tt-ok))))

(defthm tt-ok-other-release
  (implies (and (tt-ok x j refs i hist prog) (natp j) (natp i) (not (equal j i)))
           (tt-ok x j refs2 nil (append hist (list (list i tx b))) prog))
  :hints (("Goal" :in-theory (enable tt-ok))))

(defthm tts-ok-acquire
  (implies (and (tts-ok k ths refs nil hist progs) (natp i)
                (tt-ok y i refs i hist (nth i progs)))
           (tts-ok k (update-nth i y ths) refs i hist progs))
  :hints (("Goal" :induct (tts-ok k ths refs nil hist progs))))

(defthm tts-ok-release
  (implies (and (tts-ok k ths refs i hist progs) (natp i)
                (tt-ok y i refs2 nil (append hist (list (list i tx b))) (nth i progs)))
           (tts-ok k (update-nth i y ths) refs2 nil (append hist (list (list i tx b))) progs))
  :hints (("Goal" :induct (tts-ok k ths refs i hist progs))))

(defthm tts-ok-own
  (implies (and (tts-ok k ths refs lock hist progs) (natp i)
                (tt-ok y i refs lock hist (nth i progs)))
           (tts-ok k (update-nth i y ths) refs lock hist progs))
  :hints (("Goal" :induct (tts-ok k ths refs lock hist progs))))

(defthm len-update-nth-stm
  (implies (and (natp i) (< i (len l))) (equal (len (update-nth i y l)) (len l))))

(defthm true-list-listp-cdr (implies (true-list-listp l) (true-list-listp (cdr l))))

(defthm true-list-listp-car (implies (true-list-listp l) (true-listp (car l))))

; ---- each step keeps the invariant ------------------------------------------------

(defun stm-inv4 (refs lock hist ths refs0 progs)
  (and (or (null lock) (and (natp lock) (< lock (len ths))))
       (stm-replay-ok hist refs0) (equal (stm-replay-final hist refs0) refs)
       (tts-ok (len ths) ths refs lock hist progs)))

(defthm stm-step-keeps-inv
  (implies (and (stm-inv4 (nth 0 st) (nth 1 st) (nth 2 st) (nth 3 st) refs0 progs) (natp i) (< i (len (nth 3 st))))
           (let ((st2 (stm-step i st)))
             (stm-inv4 (nth 0 st2) (nth 1 st2) (nth 2 st2) (nth 3 st2) refs0 progs)))
  :hints (("Goal" :in-theory (e/d (tt-ok) (tts-ok-nth))
                  :do-not-induct t
                  :use ((:instance tts-ok-nth (k (len (nth 3 st))) (ths (nth 3 st)) (refs (nth 0 st)) (lock (nth 1 st)) (hist (nth 2 st)))))))

(defthm stm-st-as-list
  (implies (and (true-listp st) (equal (len st) 4))
           (equal (list (nth 0 st) (nth 1 st) (nth 2 st) (nth 3 st)) st))
  :hints (("Goal" :do-not-induct t
           :expand ((len st) (len (cdr st)) (len (cddr st)) (len (cdddr st)) (len (cddddr st))
                    (true-listp st) (true-listp (cdr st)) (true-listp (cddr st)) (true-listp (cdddr st)) (true-listp (cddddr st))))))

(defthm stm-step-shape
  (implies (and (true-listp st) (equal (len st) 4))
           (and (true-listp (stm-step i st)) (equal (len (stm-step i st)) 4)
                (equal (len (nth 3 (stm-step i st))) (len (nth 3 st))))))

(defthm stm-inv-step
  (implies (stm-inv st refs0 progs) (stm-inv (stm-step i st) refs0 progs))
  :hints (("Goal" :in-theory (disable stm-step stm-step-keeps-inv)
                  :use ((:instance stm-step-keeps-inv))
                  :cases ((and (natp i) (< i (len (nth 3 st))))))
          ("Subgoal 2" :in-theory (enable stm-step))))

(defthm stm-inv-run
  (implies (stm-inv st refs0 progs) (stm-inv (stm-run sched st) refs0 progs))
  :hints (("Goal" :in-theory (disable stm-inv stm-step))))

(defun init-tts (progs)
  (if (atom progs) nil (cons (mk-tt :idle nil nil nil (car progs) nil) (init-tts (cdr progs)))))

(defun stm-start (refs0 progs) (list refs0 nil nil (init-tts progs)))

(defthm len-init-tts (equal (len (init-tts progs)) (len progs)))

(defthm nth-init-tts
  (implies (< (nfix i) (len progs)) (equal (nth i (init-tts progs)) (mk-tt :idle nil nil nil (nth i progs) nil))))

; each thread's program a list of transactions, each a list of ops
(defun prog-ok (progs) (if (atom progs) t (and (true-list-listp (car progs)) (prog-ok (cdr progs)))))

(defthm prog-ok-nth (implies (prog-ok progs) (true-list-listp (nth i progs))))

(defthm tts-ok-init
  (implies (and (prog-ok progs) (<= (nfix k) (len progs)))
           (tts-ok k (init-tts progs) refs nil nil progs))
  :hints (("Goal" :induct (tts-ok k (init-tts progs) refs nil nil progs) :in-theory (e/d (tt-ok) (init-tts)))))

(defthm stm-inv-start
  (implies (prog-ok progs) (stm-inv (stm-start refs0 progs) refs0 progs)))

(defthm stm-inv-reached
  (implies (prog-ok progs) (stm-inv (stm-run sched (stm-start refs0 progs)) refs0 progs))
  :hints (("Goal" :in-theory (disable stm-inv stm-run stm-start))))

(defthm stm-run-shape
  (implies (and (true-listp st) (equal (len st) 4))
           (and (consp (stm-run sched st)) (true-listp (stm-run sched st)) (equal (len (stm-run sched st)) 4)
                (equal (len (nth 3 (stm-run sched st))) (len (nth 3 st)))))
  :hints (("Goal" :in-theory (disable stm-step))))

(defthm len-ths-start (equal (len (nth 3 (stm-start refs0 progs))) (len progs)))

(defthm stm-start-shape (and (true-listp (stm-start refs0 progs)) (equal (len (stm-start refs0 progs)) 4)))

(in-theory (disable stm-run stm-start))

(defthm stm-inv-parts
  (implies (stm-inv st refs0 progs)
           (and (stm-replay-ok (nth 2 st) refs0)
                (equal (stm-replay-final (nth 2 st) refs0) (nth 0 st))
                (tts-ok (len (nth 3 st)) (nth 3 st) (nth 0 st) (nth 1 st) (nth 2 st) progs)
                (or (null (nth 1 st)) (and (natp (nth 1 st)) (< (nth 1 st) (len (nth 3 st)))))))
  :rule-classes nil)

; SERIALIZABLE: the committed state is the transactions run one after
; another, in the order they took the lock, each on the state before it
(defthm stm-serializable
  (implies (prog-ok progs)
           (let ((st (stm-run sched (stm-start refs0 progs))))
             (and (stm-replay-ok (nth 2 st) refs0)
                  (equal (stm-replay-final (nth 2 st) refs0) (nth 0 st)))))
  :hints (("Goal" :use ((:instance stm-inv-parts (st (stm-run sched (stm-start refs0 progs))))))))

(defthm tt-ok-body-facts
  (implies (and (tt-ok x j refs lock hist prog) (equal (tt-pc x) :body))
           (and (equal (tt-at x) refs) (equal lock j)
                (equal (tt-log x) (seq-log (tt-done x) nil refs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable tt-ok))))

; ... and a read in a transaction sees what that serial run reads: the
; state it took the lock in, under its own writes so far
(defthm stm-reads-are-serial
  (implies (and (stm-inv st refs0 progs) (natp i) (< i (len (nth 3 st)))
                (equal (tt-pc (nth i (nth 3 st))) :body))
           (let ((x (nth i (nth 3 st))))
             (equal (tx-val r (tt-log x) (nth 0 st))
                    (tx-val r (seq-log (tt-done x) nil (tt-at x)) (tt-at x)))))
  :hints (("Goal" :use ((:instance stm-inv-parts)
                        (:instance tts-ok-nth (k (len (nth 3 st))) (ths (nth 3 st)) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st)))
                        (:instance tt-ok-body-facts (x (nth i (nth 3 st))) (j i) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st)) (prog (nth i progs))))
                  :in-theory (disable stm-inv tts-ok-nth))))

; ALL OR NONE: a commit writes its whole log or nothing
(defthm stm-commit-all-or-none
  (implies (and (natp i) (< i (len (nth 3 st))) (equal (tt-pc (nth i (nth 3 st))) :commit))
           (let ((refs2 (nth 0 (stm-step i st))))
             (or (equal refs2 (nth 0 st))
                 (equal refs2 (apply-log (tt-log (nth i (nth 3 st))) (nth 0 st)))))))

; what is left of a thread's program
(defun tt-rest (x) (if (eq (tt-pc x) :notify) (cdr (tt-txs x)) (tt-txs x)))

(defthm tt-ok-order
  (implies (tt-ok x j refs lock hist prog)
           (equal (append (hist-txs j hist) (tt-rest x)) prog))
  :hints (("Goal" :in-theory (enable tt-ok))))

; ONCE, IN ORDER: what a thread finished, then what it has left, is its program
(defthm stm-once-in-order
  (implies (and (prog-ok progs) (natp i) (< i (len progs)))
           (let ((st (stm-run sched (stm-start refs0 progs))))
             (equal (append (hist-txs i (nth 2 st)) (tt-rest (nth i (nth 3 st)))) (nth i progs))))
  :hints (("Goal" :use ((:instance stm-inv-parts (st (stm-run sched (stm-start refs0 progs))))
                        (:instance tts-ok-nth (k (len (nth 3 (stm-run sched (stm-start refs0 progs)))))
                                   (ths (nth 3 (stm-run sched (stm-start refs0 progs))))
                                   (refs (nth 0 (stm-run sched (stm-start refs0 progs))))
                                   (lock (nth 1 (stm-run sched (stm-start refs0 progs))))
                                   (hist (nth 2 (stm-run sched (stm-start refs0 progs))))))
                  :do-not-induct t :in-theory (disable stm-inv tts-ok-nth tt-rest))))

(defthm tt-ok-holder
  (implies (and (tt-ok x j refs lock hist prog) (equal lock j))
           (member-equal (tt-pc x) '(:body :commit)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable tt-ok))))

; NO DEADLOCK: the holder of the lock can always step ...
(defthm cdr-differs-stm (implies (consp x) (not (equal (cdr x) x))))

(defthm nth1-of-equal
  (implies (equal (cons a (cons c r)) x) (equal (nth 1 x) c))
  :rule-classes nil)

; a body step consumes an op: the thread is not what it was
(defthm ops-consumed-differs
  (implies (consp (nth 1 x)) (not (equal (cons a (cons (cdr (nth 1 x)) r)) x)))
  :hints (("Goal" :use ((:instance cdr-differs-stm (x (nth 1 x))) (:instance nth1-of-equal (c (cdr (nth 1 x)))))
                  :in-theory (disable cdr-differs-stm))))

(defthm stm-holder-steps
  (implies (and (stm-inv st refs0 progs) (nth 1 st))
           (let ((st2 (stm-step (nth 1 st) st)) (i (nth 1 st)))
             (or (not (equal (nth 1 st2) i))
                 (not (equal (nth i (nth 3 st2)) (nth i (nth 3 st)))))))
  :hints (("Goal" :use ((:instance stm-inv-parts)
                        (:instance tts-ok-nth (k (len (nth 3 st))) (ths (nth 3 st)) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st)) (i (nth 1 st)))
                        (:instance tt-ok-holder (x (nth (nth 1 st) (nth 3 st))) (j (nth 1 st)) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st)) (prog (nth (nth 1 st) progs))))
                  :in-theory (disable stm-inv tts-ok-nth))))

; ... and a thread that cannot step is done, or waits at :idle for
; another thread's lock: never for its own
(defthm stm-only-idle-waits
  (implies (and (stm-inv st refs0 progs) (natp i) (< i (len (nth 3 st)))
                (equal (nth 1 (stm-step i st)) (nth 1 st))
                (equal (nth i (nth 3 (stm-step i st))) (nth i (nth 3 st))))
           (and (equal (tt-pc (nth i (nth 3 st))) :idle)
                (or (atom (tt-txs (nth i (nth 3 st))))
                    (and (nth 1 st) (not (equal (nth 1 st) i))))))
  :hints (("Goal" :use ((:instance stm-inv-parts)
                        (:instance tts-ok-nth (k (len (nth 3 st))) (ths (nth 3 st)) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st))))
                  :do-not-induct t
                  :in-theory (e/d (tt-ok) (stm-inv tts-ok-nth)))))

; COST: the holder's steps to the release
(defun hold-m (x) (if (eq (tt-pc x) :body) (+ 1 (len (tt-ops x))) 0))

(defthm stm-hold-bound
  (implies (and (stm-inv st refs0 progs) (natp i) (equal (nth 1 st) i))
           (let ((st2 (stm-step i st)))
             (or (null (nth 1 st2))
                 (and (equal (nth 1 st2) i)
                      (equal (hold-m (nth i (nth 3 st2))) (1- (hold-m (nth i (nth 3 st)))))))))
  :hints (("Goal" :use ((:instance stm-inv-parts)
                        (:instance tts-ok-nth (k (len (nth 3 st))) (ths (nth 3 st)) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st))))
                  :in-theory (e/d (tt-ok) (stm-inv tts-ok-nth)))))

; ... while no other thread's step moves the holder or the lock
(defthm stm-others-leave-the-holder
  (implies (and (stm-inv st refs0 progs) (natp i) (equal (nth 1 st) i) (natp j) (not (equal j i)))
           (let ((st2 (stm-step j st)))
             (and (equal (nth 1 st2) i) (equal (nth i (nth 3 st2)) (nth i (nth 3 st))))))
  :hints (("Goal" :use ((:instance stm-inv-parts)
                        (:instance tts-ok-nth (k (len (nth 3 st))) (ths (nth 3 st)) (refs (nth 0 st))
                                   (lock (nth 1 st)) (hist (nth 2 st)) (i j)))
                  :in-theory (e/d (tt-ok) (stm-inv tts-ok-nth)))))

; the lock taken: |tx| + 1 to go, so the release within |tx| + 2 holder steps
(defthm stm-acquire-measure
  (implies (and (natp i) (< i (len (nth 3 st))) (equal (tt-pc (nth i (nth 3 st))) :idle)
                (consp (tt-txs (nth i (nth 3 st)))) (null (nth 1 st)))
           (equal (hold-m (nth i (nth 3 (stm-step i st))))
                  (+ 1 (len (car (tt-txs (nth i (nth 3 st)))))))))

; the commit validates and writes each ref of the log once: at most |tx|
(defthm len-put-assoc-stm
  (<= (len (put-assoc-equal k v l)) (+ 1 (len l))) :rule-classes :linear)

(defthm stm-log-bound
  (implies (not (eq (seq-log ops log refs) :fail))
           (<= (len (seq-log ops log refs)) (+ (len log) (len ops))))
  :rule-classes :linear)

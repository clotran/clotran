; A compare-and-swap retried from what is there now, formally
; (docs/model-coverage.md).
;
; clotran writes a shared cell -- a namespace's mappings, the namespace
; registry, an atom -- the way clj's Namespace and Atom do: read the
; cell, compute the new value from what was read, and compare-and-swap
; it in; when another thread wrote first, read again and start over.
; In the Fortran: gcn_intern, register, gcn_remove, gcn_slot_assoc,
; gcn_slot_dissoc (Namespace.f90) and gce_refer_core (Eval.f90), each a
; gc_cell_get or gc_root_get, the new map, and gc_cell_cas or
; gc_root_cas -- which compare and store under the state lock, so the
; CAS itself is one atomic step.
;
; Here N threads each run one operation `op` on one cell: op-next is
; the cell's new value computed from a snapshot, op-result what the
; operation answers, both any functions (defstub) -- nothing below
; depends on what they are, only that they are functions of what was
; read. A thread's steps:
;
;   :read  snapshot the cell; if the op has nothing to write (op-noop:
;          a namespace already registered, a name already interned in
;          its own namespace) it is done there, with no write
;   :cas   store op-next of the snapshot if the cell still holds it,
;          and the op is done; else back to :read, a failure counted
;
; The CAS compares IDENTITY (gc_identical), the model compares values.
; Equal values that are different objects make the Fortran fail where
; a value compare would succeed, so the model's CAS may fail on equal
; values too (the bit b), but only once a write has happened since the
; snapshot: with none, the cell holds the very object read -- rooted by
; the reader, so its address cannot be reused -- and the CAS succeeds.
;
; What it proves, under every interleaving and every outcome of b:
;
;   LINEARIZABLE  the history of done ops, in the order they took
;                 effect, replayed from the cell's first value, gives
;                 the cell's value; each op took effect on exactly the
;                 value it read, and answered op-result of that value
;   EXACTLY ONCE  a thread is in the history iff it is done, and no
;                 thread is in it twice -- no lost update, none doubled
;   LOCK-FREE     a CAS fails only when the write count has moved past
;                 the thread's snapshot: some other op completed
;   COST          a thread fails at most as many times as there were
;                 writes, so it takes at most 2N + 2 of its own steps,
;                 N the number of threads; O(N) per op, O(N^2) in all
;
; The plain read-assoc-store this replaced has no such theorem: the
; counterexample is in model/envns.lisp (rmw-loses-an-update).

(in-package "ACL2")

(defstub op-result (* *) => *)

; op-noop: the op finds at its read that it has nothing to write -- a
; name already interned in its own namespace, a namespace already
; registered, a key already absent -- and is done there; only then is
; the cell left as it is. Any other op goes on to its CAS, even one whose
; new map is equal to the old (gcn_slot_assoc always swaps).
(encapsulate (((op-next * *) => *) ((op-noop * *) => *))
  (local (defun op-next (op m) (declare (ignore op)) m))
  (local (defun op-noop (op m) (declare (ignore op m)) nil))
  (defthm op-noop-writes-nothing
    (implies (op-noop op m) (equal (op-next op m) m))))

; a thread: (pc snap snapc fails steps result)
(defun mk-th (pc snap snapc fails steps result) (list pc snap snapc fails steps result))
(defun th-pc (x) (nth 0 x))
(defun th-snap (x) (nth 1 x))
(defun th-snapc (x) (nth 2 x))
(defun th-fails (x) (nth 3 x))
(defun th-steps (x) (nth 4 x))
(defun th-result (x) (nth 5 x))

; ---- the history -------------------------------------------------------
;
; an alist (j . s): thread j took effect on the cell's value s, in order

(defun replay-ok (hist s ops)
  (if (atom hist) t
    (and (consp (car hist)) (equal (cdar hist) s)
         (replay-ok (cdr hist) (op-next (nth (caar hist) ops) s) ops))))

(defun replay-final (hist s ops)
  (if (atom hist) s
    (replay-final (cdr hist) (op-next (nth (caar hist) ops) (cdar hist)) ops)))

(defthm replay-ok-append
  (implies (replay-ok h s ops)
           (equal (replay-ok (append h (list (cons i x))) s ops)
                  (equal x (replay-final h s ops))))
  :hints (("Goal" :induct (replay-ok h s ops))))

(defthm replay-final-append
  (equal (replay-final (append h (list (cons i x))) s ops)
         (op-next (nth i ops) x))
  :hints (("Goal" :induct (replay-final h s ops))))

(defthm assoc-equal-append-found
  (implies (assoc-equal j h)
           (equal (assoc-equal j (append h l)) (assoc-equal j h))))

(defthm assoc-equal-append-one
  (implies (and (alistp h) (not (assoc-equal j h)))
           (equal (assoc-equal j (append h (list (cons i x))))
                  (if (equal j i) (cons i x) nil))))

(defthm strip-cars-append-one
  (equal (strip-cars (append h (list (cons i x)))) (append (strip-cars h) (list i))))

(defthm member-strip-cars-assoc
  (implies (alistp h) (iff (member-equal j (strip-cars h)) (assoc-equal j h))))

(defthm member-append-one
  (iff (member-equal j (append l (list i))) (or (member-equal j l) (equal j i))))

(defthm no-dups-append-one
  (implies (and (no-duplicatesp-equal l) (not (member-equal i l)))
           (no-duplicatesp-equal (append l (list i)))))

(defthm alistp-append-one
  (implies (alistp h) (alistp (append h (list (cons i x))))))

(defthm len-append-one (equal (len (append h (list x))) (+ 1 (len h))))

; ---- a thread's invariant ----------------------------------------------

(defun th-ok (x j cell count hist ops)
  (let ((f (th-fails x)) (s (th-steps x)))
    (and (natp f) (natp s)
         (case (th-pc x)
           (:read (and (equal s (* 2 f)) (<= f count) (not (assoc-equal j hist))))
           (:cas (and (natp (th-snapc x)) (<= (th-snapc x) count)
                      (implies (equal count (th-snapc x)) (equal cell (th-snap x)))
                      (<= f (th-snapc x)) (equal s (+ 1 (* 2 f)))
                      (not (assoc-equal j hist))))
           (:done (and (assoc-equal j hist)
                       (equal (th-result x) (op-result (nth j ops) (cdr (assoc-equal j hist))))
                       (<= f count) (<= s (+ 2 (* 2 f)))))
           (otherwise nil)))))

(in-theory (disable th-ok))

(defun ths-ok (k ths cell count hist ops)
  (if (zp k) t
    (and (th-ok (nth (1- k) ths) (1- k) cell count hist ops)
         (ths-ok (1- k) ths cell count hist ops))))

(defthm ths-ok-nth
  (implies (and (ths-ok k ths cell count hist ops) (natp i) (natp k) (< i k))
           (th-ok (nth i ths) i cell count hist ops)))

(defun ndone (ths)
  (if (atom ths) 0 (+ (if (equal (th-pc (car ths)) :done) 1 0) (ndone (cdr ths)))))

(defthm ndone-bound (<= (ndone ths) (len ths)) :rule-classes :linear)

(defthm ndone-update-nth
  (implies (and (natp i) (< i (len ths)))
           (equal (ndone (update-nth i y ths))
                  (+ (ndone ths)
                     (- (if (equal (th-pc (nth i ths)) :done) 1 0))
                     (if (equal (th-pc y) :done) 1 0)))))

; the other threads, when thread i's op takes effect: with a write ...
(defthm th-ok-after-write
  (implies (and (th-ok x j cell count hist ops) (not (equal j i)) (alistp hist) (natp count))
           (th-ok x j cell2 (+ 1 count) (append hist (list (cons i s))) ops))
  :hints (("Goal" :in-theory (enable th-ok))))

; ... and without one
(defthm th-ok-after-done
  (implies (and (th-ok x j cell count hist ops) (not (equal j i)) (alistp hist))
           (th-ok x j cell count (append hist (list (cons i s))) ops))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm ths-ok-after-write
  (implies (and (ths-ok k ths cell count hist ops) (natp count) (natp i) (alistp hist)
                (th-ok y i cell2 (+ 1 count) (append hist (list (cons i s))) ops))
           (ths-ok k (update-nth i y ths) cell2 (+ 1 count) (append hist (list (cons i s))) ops)))

(defthm ths-ok-after-done
  (implies (and (ths-ok k ths cell count hist ops) (natp i) (alistp hist)
                (th-ok y i cell count (append hist (list (cons i s))) ops))
           (ths-ok k (update-nth i y ths) cell count (append hist (list (cons i s))) ops)))

(defthm ths-ok-after-own
  (implies (and (ths-ok k ths cell count hist ops) (natp i) (alistp hist)
                (th-ok y i cell count hist ops))
           (ths-ok k (update-nth i y ths) cell count hist ops)))

(defun cas-inv4 (cell count hist ths ops cell0)
  (and (natp count) (<= count (len hist))
       (alistp hist)
       (replay-ok hist cell0 ops) (equal (replay-final hist cell0 ops) cell)
       (no-duplicatesp-equal (strip-cars hist))
       (equal (len hist) (ndone ths))
       (ths-ok (len ths) ths cell count hist ops)))

(defun cas-inv (st ops cell0)
  (and (true-listp st) (equal (len st) 4)
       (cas-inv4 (nth 0 st) (nth 1 st) (nth 2 st) (nth 3 st) ops cell0)))

(defun init-ths (n)
  (if (zp n) nil (cons (mk-th :read nil 0 0 0 nil) (init-ths (1- n)))))

(defthm len-init-ths (equal (len (init-ths n)) (nfix n)))
(defthm ndone-init-ths (equal (ndone (init-ths n)) 0))
(defun dec2 (i n) (if (or (zp i) (zp n)) nil (dec2 (1- i) (1- n))))
(defthm nth-init-ths
  (implies (and (natp i) (< i (nfix n))) (equal (nth i (init-ths n)) (mk-th :read nil 0 0 0 nil)))
  :hints (("Goal" :induct (dec2 i n))))
(defthm ths-ok-init
  (implies (<= k (nfix n)) (ths-ok k (init-ths n) cell 0 nil ops))
  :hints (("Goal" :induct (ths-ok k (init-ths n) cell 0 nil ops) :in-theory (e/d (th-ok) (init-ths)))))

(defthm cas-inv-init
  (cas-inv (list cell0 0 nil (init-ths n)) ops cell0))

(defthm len-update-nth-in
  (implies (and (natp i) (< i (len l))) (equal (len (update-nth i y l)) (len l))))

(defthm not-member-when-not-done
  (implies (and (ths-ok k ths cell count hist ops) (natp i) (natp k) (< i k)
                (not (equal (th-pc (nth i ths)) :done)) (alistp hist))
           (not (member-equal i (strip-cars hist))))
  :hints (("Goal" :use ((:instance ths-ok-nth)) :in-theory (e/d (th-ok) (ths-ok-nth)))))

; what the invariant says of the stepping thread x, by its pc
(defthm th-ok-read-facts
  (implies (and (th-ok x i cell count hist ops) (equal (th-pc x) :read))
           (and (natp (th-fails x)) (equal (th-steps x) (* 2 (th-fails x)))
                (<= (th-fails x) count) (not (assoc-equal i hist))))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-cas-facts
  (implies (and (th-ok x i cell count hist ops) (equal (th-pc x) :cas))
           (and (natp (th-fails x)) (natp (th-snapc x)) (<= (th-snapc x) count)
                (implies (equal count (th-snapc x)) (equal cell (th-snap x)))
                (<= (th-fails x) (th-snapc x)) (equal (th-steps x) (+ 1 (* 2 (th-fails x))))
                (not (assoc-equal i hist))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-new-done
  (implies (and (alistp hist) (not (assoc-equal i hist)) (natp f) (<= f count) (<= s (+ 2 (* 2 f))) (natp s))
           (th-ok (mk-th :done c 0 f s (op-result (nth i ops) c)) i cell2 count
                  (append hist (list (cons i c))) ops))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-new-done-count
  (implies (and (alistp hist) (not (assoc-equal i hist)) (natp f) (<= f count) (<= s (+ 2 (* 2 f))) (natp s))
           (th-ok (mk-th :done c 0 f s (op-result (nth i ops) c)) i cell2 (+ 1 count)
                  (append hist (list (cons i c))) ops))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-new-cas
  (implies (and (not (assoc-equal i hist)) (natp f) (<= f count) (natp count))
           (th-ok (mk-th :cas cell count f (+ 1 (* 2 f)) nil) i cell count hist ops))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-new-read
  (implies (and (not (assoc-equal i hist)) (natp f) (natp count) (< f count))
           (th-ok (mk-th :read nil 0 (+ 1 f) (+ 2 (* 2 f)) nil) i cell count hist ops))
  :hints (("Goal" :in-theory (enable th-ok))))

(in-theory (disable mk-th th-pc th-snap th-snapc th-fails th-steps th-result))
(defthm th-fields-mk-th
  (and (equal (th-pc (mk-th a b c d e f)) a) (equal (th-snap (mk-th a b c d e f)) b)
       (equal (th-snapc (mk-th a b c d e f)) c) (equal (th-fails (mk-th a b c d e f)) d)
       (equal (th-steps (mk-th a b c d e f)) e) (equal (th-result (mk-th a b c d e f)) f))
  :hints (("Goal" :in-theory (enable mk-th th-pc th-snap th-snapc th-fails th-steps th-result))))

(defun cas-step (i b st ops)
  (let* ((cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let* ((x (nth i ths)) (op (nth i ops)))
        (case (th-pc x)
          (:read (if (op-noop op cell)
                     (list cell count (append hist (list (cons i cell)))
                           (update-nth i (mk-th :done cell 0 (th-fails x) (1+ (th-steps x)) (op-result op cell)) ths))
                   (list cell count hist
                         (update-nth i (mk-th :cas cell count (th-fails x) (1+ (th-steps x)) nil) ths))))
          ; b: the identity compare fails on equal values -- only once
          ; a write has happened since the snapshot
          (:cas (if (and (equal cell (th-snap x)) (or (equal count (th-snapc x)) (not b)))
                    (list (op-next op cell) (1+ count) (append hist (list (cons i cell)))
                          (update-nth i (mk-th :done cell 0 (th-fails x) (1+ (th-steps x)) (op-result op cell)) ths))
                  (list cell count hist
                        (update-nth i (mk-th :read nil 0 (1+ (th-fails x)) (1+ (th-steps x)) nil) ths))))
          (otherwise st))))))



(defthm step-read-done
  (implies (and (cas-inv4 cell count hist ths ops cell0) (natp i) (< i (len ths))
                (equal (th-pc (nth i ths)) :read) (op-noop (nth i ops) cell))
           (cas-inv (cas-step i b (list cell count hist ths) ops) ops cell0))
  :hints (("Goal" :in-theory (e/d (th-ok) (ths-ok-nth not-member-when-not-done))
     :use ((:instance ths-ok-nth (k (len ths)) (cell cell) (count count) (hist hist))
           (:instance not-member-when-not-done (k (len ths)))))))

(defthm step-read-cas
  (implies (and (cas-inv4 cell count hist ths ops cell0) (natp i) (< i (len ths))
                (equal (th-pc (nth i ths)) :read) (not (op-noop (nth i ops) cell)))
           (cas-inv (cas-step i b (list cell count hist ths) ops) ops cell0))
  :hints (("Goal" :in-theory (e/d (th-ok) (ths-ok-nth not-member-when-not-done))
     :use ((:instance ths-ok-nth (k (len ths)) (cell cell) (count count) (hist hist))
           (:instance not-member-when-not-done (k (len ths)))))))

(defthm step-cas-wins
  (implies (and (cas-inv4 cell count hist ths ops cell0) (natp i) (< i (len ths))
                (equal (th-pc (nth i ths)) :cas)
                (equal cell (th-snap (nth i ths))) (or (equal count (th-snapc (nth i ths))) (not b)))
           (cas-inv (cas-step i b (list cell count hist ths) ops) ops cell0))
  :hints (("Goal" :in-theory (e/d (th-ok) (ths-ok-nth not-member-when-not-done))
     :use ((:instance ths-ok-nth (k (len ths)) (cell cell) (count count) (hist hist))
           (:instance not-member-when-not-done (k (len ths)))))))

(defthm step-cas-fails
  (implies (and (cas-inv4 cell count hist ths ops cell0) (natp i) (< i (len ths))
                (equal (th-pc (nth i ths)) :cas)
                (not (and (equal cell (th-snap (nth i ths))) (or (equal count (th-snapc (nth i ths))) (not b)))))
           (cas-inv (cas-step i b (list cell count hist ths) ops) ops cell0))
  :hints (("Goal" :in-theory (e/d (th-ok) (ths-ok-nth not-member-when-not-done))
     :use ((:instance ths-ok-nth (k (len ths)) (cell cell) (count count) (hist hist))
           (:instance not-member-when-not-done (k (len ths)))))))

(defthm step-other
  (implies (and (cas-inv4 cell count hist ths ops cell0)
                (not (and (natp i) (< i (len ths))
                          (member-equal (th-pc (nth i ths)) '(:read :cas)))))
           (cas-inv (cas-step i b (list cell count hist ths) ops) ops cell0)))

(defthm st-as-list
  (implies (and (true-listp st) (equal (len st) 4))
           (equal (list (nth 0 st) (nth 1 st) (nth 2 st) (nth 3 st)) st))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((len st) (len (cdr st)) (len (cddr st)) (len (cdddr st)) (len (cddddr st))
                    (true-listp st) (true-listp (cdr st)) (true-listp (cddr st)) (true-listp (cdddr st)) (true-listp (cddddr st))))))

(defthm cas-inv-step
  (implies (cas-inv st ops cell0)
           (cas-inv (cas-step i b st ops) ops cell0))
  :hints (("Goal" :in-theory (disable cas-step cas-inv4 step-read-done step-read-cas step-cas-wins step-cas-fails step-other)
                  :use (st-as-list
                        (:instance step-read-done (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
                        (:instance step-read-cas (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
                        (:instance step-cas-wins (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
                        (:instance step-cas-fails (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
                        (:instance step-other (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))))))

(defun cas-run (sched st ops)
  (if (atom sched) st
    (cas-run (cdr sched) (cas-step (caar sched) (cdar sched) st ops) ops)))

(defthm cas-inv-run
  (implies (cas-inv st ops cell0) (cas-inv (cas-run sched st ops) ops cell0))
  :hints (("Goal" :in-theory (disable cas-inv cas-step))))

; ---- what the invariant says ------------------------------------------------

(defun cas-start (n cell0) (list cell0 0 nil (init-ths n)))

(defthm len-ths-step
  (equal (len (nth 3 (cas-step i b st ops))) (len (nth 3 st))))

(defthm len-ths-run
  (equal (len (nth 3 (cas-run sched st ops))) (len (nth 3 st)))
  :hints (("Goal" :in-theory (disable cas-step))))

(defthm cas-inv-reached
  (cas-inv (cas-run sched (cas-start n cell0) ops) ops cell0)
  :hints (("Goal" :in-theory (disable cas-inv cas-run))))

(in-theory (disable cas-run cas-start))

(defthm cas-inv4-of-inv
  (implies (cas-inv st ops cell0)
           (cas-inv4 (nth 0 st) (nth 1 st) (nth 2 st) (nth 3 st) ops cell0)))

; LINEARIZABLE: the history, replayed from the first value -- each op
; applied to exactly the value it read -- is the cell
(defthm cas-linearizable
  (let ((st (cas-run sched (cas-start n cell0) ops)))
    (and (replay-ok (nth 2 st) cell0 ops)
         (equal (replay-final (nth 2 st) cell0 ops) (nth 0 st))))
  :hints (("Goal" :use ((:instance cas-inv4-of-inv (st (cas-run sched (cas-start n cell0) ops))))
                  :in-theory (disable cas-inv4-of-inv cas-inv))))

(defthm th-ok-done-facts
  (implies (and (th-ok x i cell count hist ops) (equal (th-pc x) :done))
           (and (assoc-equal i hist)
                (equal (th-result x) (op-result (nth i ops) (cdr (assoc-equal i hist))))))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-not-done
  (implies (and (th-ok x i cell count hist ops) (not (equal (th-pc x) :done)))
           (not (assoc-equal i hist)))
  :hints (("Goal" :in-theory (enable th-ok))))

(defthm th-ok-fails-bound
  (implies (th-ok x i cell count hist ops)
           (and (natp (th-fails x)) (<= (th-fails x) count)
                (natp (th-steps x)) (<= (th-steps x) (+ 2 (* 2 (th-fails x))))))
  :hints (("Goal" :in-theory (enable th-ok))))



; ... and a done op answered op-result of the value it took effect on
(defthm cas-results
  (let ((st (cas-run sched (cas-start n cell0) ops)))
    (implies (and (natp i) (< i (nfix n)) (equal (th-pc (nth i (nth 3 st))) :done))
             (equal (th-result (nth i (nth 3 st)))
                    (op-result (nth i ops) (cdr (assoc-equal i (nth 2 st)))))))
  :hints (("Goal" :use ((:instance cas-inv4-of-inv (st (cas-run sched (cas-start n cell0) ops)))
                  (:instance ths-ok-nth
                             (k (len (nth 3 (cas-run sched (cas-start n cell0) ops))))
                             (ths (nth 3 (cas-run sched (cas-start n cell0) ops)))
                             (cell (nth 0 (cas-run sched (cas-start n cell0) ops)))
                             (count (nth 1 (cas-run sched (cas-start n cell0) ops)))
                             (hist (nth 2 (cas-run sched (cas-start n cell0) ops)))))
     :in-theory (e/d (cas-start) (cas-inv4-of-inv cas-inv ths-ok-nth)))))

; EXACTLY ONCE: in the history iff done, and never twice
(defthm cas-exactly-once
  (let ((st (cas-run sched (cas-start n cell0) ops)))
    (and (no-duplicatesp-equal (strip-cars (nth 2 st)))
         (implies (and (natp i) (< i (nfix n)))
                  (iff (assoc-equal i (nth 2 st))
                       (equal (th-pc (nth i (nth 3 st))) :done)))))
  :hints (("Goal" :use ((:instance cas-inv4-of-inv (st (cas-run sched (cas-start n cell0) ops)))
                  (:instance ths-ok-nth
                             (k (len (nth 3 (cas-run sched (cas-start n cell0) ops))))
                             (ths (nth 3 (cas-run sched (cas-start n cell0) ops)))
                             (cell (nth 0 (cas-run sched (cas-start n cell0) ops)))
                             (count (nth 1 (cas-run sched (cas-start n cell0) ops)))
                             (hist (nth 2 (cas-run sched (cas-start n cell0) ops)))))
     :in-theory (e/d (cas-start) (cas-inv4-of-inv cas-inv ths-ok-nth)))))

; LOCK-FREE: a CAS that fails had a write after its snapshot
(defthm cas-fails-only-after-a-write
  (implies (and (cas-inv st ops cell0) (natp i) (< i (len (nth 3 st)))
                (equal (th-pc (nth i (nth 3 st))) :cas)
                (equal (th-pc (nth i (nth 3 (cas-step i b st ops)))) :read))
           (< (th-snapc (nth i (nth 3 st))) (nth 1 st)))
  :hints (("Goal" :use ((:instance ths-ok-nth (k (len (nth 3 st))) (ths (nth 3 st))
                                   (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)))
                        (:instance th-ok-cas-facts (x (nth i (nth 3 st)))
                                   (cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st))))
                  :do-not-induct t
                  :in-theory (disable ths-ok-nth))))

; COST: at most one write per op, so at most N failures, so a thread's
; own steps are at most 2N + 2
(defthm cas-cost
  (let ((st (cas-run sched (cas-start n cell0) ops)))
    (implies (and (natp i) (< i (nfix n)))
             (and (<= (th-fails (nth i (nth 3 st))) (nfix n))
                  (<= (th-steps (nth i (nth 3 st))) (+ 2 (* 2 (nfix n)))))))
  :hints (("Goal" :use ((:instance cas-inv4-of-inv (st (cas-run sched (cas-start n cell0) ops)))
                        (:instance ths-ok-nth (k (len (nth 3 (cas-run sched (cas-start n cell0) ops)))) (ths (nth 3 (cas-run sched (cas-start n cell0) ops)))
                                   (cell (nth 0 (cas-run sched (cas-start n cell0) ops))) (count (nth 1 (cas-run sched (cas-start n cell0) ops))) (hist (nth 2 (cas-run sched (cas-start n cell0) ops))))
                        (:instance th-ok-fails-bound (x (nth i (nth 3 (cas-run sched (cas-start n cell0) ops))))
                                   (cell (nth 0 (cas-run sched (cas-start n cell0) ops))) (count (nth 1 (cas-run sched (cas-start n cell0) ops))) (hist (nth 2 (cas-run sched (cas-start n cell0) ops))))
                        (:instance ndone-bound (ths (nth 3 (cas-run sched (cas-start n cell0) ops)))))
                  :in-theory (e/d (cas-start) (cas-inv4-of-inv cas-inv ths-ok-nth th-ok-fails-bound ndone-bound)))))

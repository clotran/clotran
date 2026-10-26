; Several threads on one heap, formally (docs/model-coverage.md).
;
; src/f/GC.f90's heap is shared by every thread running clotran. The heap
; books (heapg, heapsw, heapal, heaprn, heapgn) prove one thread's view:
; the free list, a batch, the sweep and the young marking. This book is
; the threads': who may touch which cell when, and how a collection gets
; the heap to itself.
;
;   heap_lock     heap_enter/heap_leave take it for the slow path (a
;                 refill, a growth, a collection); world_stop sets
;                 stop_world and waits on heap_cond, letting the lock go,
;                 until n_parked = n_running - 1; heap_enter, finding
;                 stop_world, parks there -- a SAFEPOINT -- until
;                 world_start clears it. gc_poll is heap_enter+heap_leave,
;                 called by the interpreter's loop and a compiled
;                 back-edge, so a thread that allocates nothing still parks.
;   n_running     gc_mutator_enter/_leave, under the lock: a thread in a
;                 blocking call (a read, a wait, a lock that may be held
;                 across a safepoint) is out, and a stop does not wait
;                 for it; gc_mutator_enter waits while stop_world.
;   batches       with more than one running, a thread allocates from its
;                 own batch without the lock (gc_obj's fast path), fills
;                 it under the lock from the free list (obj_take, the
;                 generated hpg_*_fill), and from its own pending dead
;                 without the lock (pend_refill_*): a young collection
;                 hands each thread its own dead young (hand_off_young),
;                 and the next collection frees what is left of them
;                 first (finish_pending). A batched slot is flagged free,
;                 so the sweep passes it over.
;   state lock    gc_state_lock: short sections, every write a lock-free
;                 reader may see (model/seqlock.lisp); gc_state_wait lets
;                 it go before it steps out.
;   tx_lk         the transaction lock (and a monitor): held across
;                 safepoints, so waited for only out of the running
;                 (B_RUNTX, monitor-enter).
;
; Here a cell's owner is one of :free (the free list or the unused end),
; :used, (:b . i) (thread i's batch) or (:p . i) (thread i's pending dead);
; that each list holds a slot once and the lists are what these say is
; heapal-proof's. A thread is (ph w xw roots): its phase, whether it is
; blocked on the state lock or on tx_lk, and its roots -- everything its
; value stack reaches (the marking from them is heapg/heapgn's).
;
; This book is the model and its invariant, kept by every step;
; heapmt-proof.lisp the theorems. What they prove, under every
; interleaving, given the DISCIPLINE the code keeps: no thread enters the
; heap (heap_enter, gc_poll, world_stop, gc_mutator_enter) holding the
; state lock; tx_lk is waited for only out of the running mutators, and
; not holding the state lock; and only threads clotran starts
; (task_thread_main, which enters as a mutator) run clotran code -- an
; embedder's own thread calling the C ABI is outside it (model/threads.lisp).
; An instrumented build saw no heap_enter under the state lock in a run of
; six threads swapping atoms, altering refs, sending to agents, interning
; and pmapping (2026-10-25).
;
;   ROOTS      every cell any thread roots is :used -- on no free list, in
;              no batch, no pending list -- so no collection frees what
;              a thread can reach (rooted-is-used, sweep-keeps-rooted)
;   BATCHES    a cell in thread i's batch is no other thread's to take or
;              move (batch-private, others-cannot-pop), and the cell an
;              allocation hands out is in no thread's roots (alloc-fresh)
;   STOP       a collection runs only with every other thread parked or
;              out (collect-others-stopped), and while it runs no other
;              thread changes the heap, a root or a phase
;              (stop-excludes) -- none runs clotran until it ends
;   NO DEADLOCK  in every reachable state some thread can step (progress-thm);
;              without the discipline -- a thread parked holding the state
;              lock while a running one waits for it -- nothing can
;              (parked-under-state-lock-is-stuck)
;   COST       the stop waits for at most n - 1 parks and none is undone
;              while it waits (stop-deficit-bounded, stop-deficit-shrinks);
;              the collector's per-thread passes are 4 a thread plus its
;              roots (collect-threads-cost); a refill from the pending
;              list takes at most its length in turns and fills at most
;              the batch's room, whatever the threads (prefill-cost)

(in-package "ACL2")

(set-irrelevant-formals-ok t)

; ---- STATE ---------------------------------------------------------------------------

(defun mk-th (ph w xw rts) (list ph w xw rts))
(defun th-ph (x) (nth 0 x))
(defun th-w (x) (nth 1 x))
(defun th-xw (x) (nth 2 x))
(defun th-rts (x) (nth 3 x))

(defthm th-fields
  (and (equal (th-ph (mk-th p w xw r)) p) (equal (th-w (mk-th p w xw r)) w)
       (equal (th-xw (mk-th p w xw r)) xw) (equal (th-rts (mk-th p w xw r)) r)))

(in-theory (disable mk-th th-ph th-w th-xw th-rts))

; st = (hl sw nrun npark sl xl own ths): heap_lock's holder, stop_world (its
; setter), n_running, n_parked, the state lock's holder, tx_lk's holder,
; the cells' owners, the threads
(defun mk-st (hl sw nrun npark sl xl own ths) (list hl sw nrun npark sl xl own ths))
(defun st-hl (st) (nth 0 st))
(defun st-sw (st) (nth 1 st))
(defun st-nrun (st) (nth 2 st))
(defun st-npark (st) (nth 3 st))
(defun st-sl (st) (nth 4 st))
(defun st-xl (st) (nth 5 st))
(defun st-own (st) (nth 6 st))
(defun st-ths (st) (nth 7 st))

(defthm st-fields
  (and (equal (st-hl (mk-st a b c d e f g h)) a) (equal (st-sw (mk-st a b c d e f g h)) b)
       (equal (st-nrun (mk-st a b c d e f g h)) c) (equal (st-npark (mk-st a b c d e f g h)) d)
       (equal (st-sl (mk-st a b c d e f g h)) e) (equal (st-xl (mk-st a b c d e f g h)) f)
       (equal (st-own (mk-st a b c d e f g h)) g) (equal (st-ths (mk-st a b c d e f g h)) h)))

(in-theory (disable mk-st st-hl st-sw st-nrun st-npark st-sl st-xl st-own st-ths))

(defmacro phases () ''(:out :run :parked :inheap :stopping :collect))
(defmacro act-phases () ''(:run :inheap :stopping :collect))   ; running, not parked
(defmacro lock-phases () ''(:out :run :inheap :collect))       ; may take the state lock

(defun rooted (ths c)
  (if (atom ths) nil (or (member-equal c (th-rts (car ths))) (rooted (cdr ths) c))))

(defun all-used (r own)
  (if (atom r) t (and (natp (car r)) (equal (nth (car r) own) :used) (all-used (cdr r) own))))

; the sweep, after finish_pending: what is left of every pending list is
; freed; a :used cell no thread roots goes to the free list, or to the
; pending list of the thread `who` names for it (hand_off_young: a
; thread's own dead young) -- any choice, so every collection the code
; makes is one of these
(defun sweep1 (v c ths who)
  (cond ((and (consp v) (eq (car v) :p)) :free)
        ((and (eq v :used) (not (rooted ths c)))
         (let ((j (nth c who))) (if (and (natp j) (< j (len ths))) (cons :p j) :free)))
        (t v)))

(defun sweep (own c ths who)
  (if (atom own) nil (cons (sweep1 (car own) c ths who) (sweep (cdr own) (1+ c) ths who))))

; ---- THE STEP ------------------------------------------------------------------------
;
; One thread's next action, atomic: what it does under a lock is one step,
; and what it does without one touches only what is its own (its batch,
; its pending dead, its roots). A step that cannot go leaves the state as
; it was -- the thread is blocked, and the scheduler runs it again later.
; Each action is its own function; c is the cell (or, for :collect, the
; sweep's choice of pending lists).

(defun lockp (p) (if (member-equal p (lock-phases)) t nil))
(defun hlp (p) (if (member-equal p '(:inheap :collect)) t nil))      ; holds heap_lock
(defun mutp (p) (if (member-equal p '(:run :inheap)) t nil))         ; runs the program
(defun phasep (p) (if (member-equal p (phases)) t nil))
(in-theory (disable lockp hlp mutp phasep))

(defun rt! (i ph w xw ths rr) (update-nth i (mk-th ph w xw rr) ths))

(defmacro defact (name body)
  `(defun ,name (i c st)
     (declare (ignorable c))
     (let* ((hl (st-hl st)) (sw (st-sw st)) (nrun (st-nrun st)) (npark (st-npark st))
            (sl (st-sl st)) (xl (st-xl st)) (own (st-own st)) (ths (st-ths st)))
       (declare (ignorable hl sw nrun npark sl xl own ths))
       (if (not (and (natp i) (< i (len ths)))) st
         (let* ((x (nth i ths)) (ph (th-ph x)) (w (th-w x)) (xw (th-xw x)) (r (th-rts x))
                (free (not (or w xw))) (cell (and (natp c) (< c (len own)))))
           (declare (ignorable x ph w xw r free cell))
           ,body)))))

; gc_mutator_enter: under the lock, waiting while stop_world
(defact s-enter (if (and (eq ph :out) free (null hl) (null sw) (not (equal sl i)))
                    (mk-st hl sw (1+ nrun) npark sl xl own (rt! i :run w xw ths r)) st))
; gc_mutator_leave
(defact s-leave (if (and (eq ph :run) free (null hl))
                    (mk-st hl sw (1- nrun) npark sl xl own (rt! i :out w xw ths r)) st))
; gc_state_lock: taken, or blocked on it
(defact s-slock (if (and (lockp ph) (not xw) (not (equal sl i)))
                    (if (null sl) (mk-st hl sw nrun npark i xl own (rt! i ph nil xw ths r))
                      (mk-st hl sw nrun npark sl xl own (rt! i ph t xw ths r)))
                  st))
(defact s-sunlock (if (and (equal sl i) free (lockp ph)) (mk-st hl sw nrun npark nil xl own ths) st))
; tx_lk (or a monitor): waited for out of the running
(defact s-xlock (if (and (eq ph :out) (not w) (not (equal xl i)) (not (equal sl i)))
                    (if (null xl) (mk-st hl sw nrun npark sl i own (rt! i ph w nil ths r))
                      (mk-st hl sw nrun npark sl xl own (rt! i ph w t ths r)))
                  st))
(defact s-xunlock (if (and (equal xl i) free (lockp ph)) (mk-st hl sw nrun npark sl nil own ths) st))
; heap_enter (gc_poll too): the lock, and a park if a stop is asked for
(defact s-henter (if (and (eq ph :run) free (null hl) (not (equal sl i)))
                     (if sw (mk-st hl sw nrun (1+ npark) sl xl own (rt! i :parked w xw ths r))
                       (mk-st i sw nrun npark sl xl own (rt! i :inheap w xw ths r)))
                   st))
; ... a parked thread going on once the world starts, holding the lock
(defact s-wake (if (and (eq ph :parked) (null sw) (null hl))
                   (mk-st i sw nrun (1- npark) sl xl own (rt! i :inheap w xw ths r)) st))
(defact s-hleave (if (and (eq ph :inheap) free) (mk-st nil sw nrun npark sl xl own (rt! i :run w xw ths r)) st))
; world_stop: alone, nothing to stop; else stop_world, and wait (the lock let go)
(defact s-stop (if (and (eq ph :inheap) free (null sw) (not (equal sl i)))
                   (if (<= nrun 1) (mk-st hl sw nrun npark sl xl own (rt! i :collect w xw ths r))
                     (mk-st nil i nrun npark sl xl own (rt! i :stopping w xw ths r)))
                 st))
; ... its wait ending: every other running thread parked
(defact s-stopwake (if (and (eq ph :stopping) (null hl) (<= (1- nrun) npark))
                       (mk-st i sw nrun npark sl xl own (rt! i :collect w xw ths r)) st))
; world_start: still in the heap
(defact s-start (if (and (eq ph :collect) free) (mk-st hl nil nrun npark sl xl own (rt! i :inheap w xw ths r)) st))
(defact s-collect (if (and (eq ph :collect) free) (mk-st hl sw nrun npark sl xl (sweep own 0 ths c) ths) st))
; gc_obj's fast path: a cell off this thread's own batch, no lock
(defact s-fast (if (and (mutp ph) free cell (equal (nth c own) (cons :b i)))
                   (mk-st hl sw nrun npark sl xl (update-nth c :used own) (rt! i ph w xw ths (cons c r))) st))
; the slow path's one cell off the free list (the collector's too)
(defact s-take (if (and (hlp ph) free cell (equal (nth c own) :free))
                   (mk-st hl sw nrun npark sl xl (update-nth c :used own) (rt! i ph w xw ths (cons c r))) st))
; obj_take's fill: a free cell into this thread's batch, under the lock
(defact s-refill (if (and (eq ph :inheap) free cell (equal (nth c own) :free))
                     (mk-st hl sw nrun npark sl xl (update-nth c (cons :b i) own) ths) st))
; pend_refill: one of its own dead into its batch, no lock
(defact s-prefill (if (and (mutp ph) free cell (equal (nth c own) (cons :p i)))
                      (mk-st hl sw nrun npark sl xl (update-nth c (cons :b i) own) ths) st))
; the program drops a reference, or reads one out of the heap
(defact s-drop (if (and (mutp ph) free) (mk-st hl sw nrun npark sl xl own (rt! i ph w xw ths (remove-equal c r))) st))
(defact s-load (if (and (mutp ph) free (rooted ths c))
                   (mk-st hl sw nrun npark sl xl own (rt! i ph w xw ths (cons c r))) st))

(defmacro actions ()
  ''((:enter . s-enter) (:leave . s-leave) (:slock . s-slock) (:sunlock . s-sunlock)
     (:xlock . s-xlock) (:xunlock . s-xunlock) (:henter . s-henter) (:wake . s-wake)
     (:hleave . s-hleave) (:stop . s-stop) (:stopwake . s-stopwake) (:start . s-start)
     (:collect . s-collect) (:fast . s-fast) (:take . s-take) (:refill . s-refill)
     (:prefill . s-prefill) (:drop . s-drop) (:load . s-load)))

(defun step-cases (as)
  (if (atom as) '((otherwise st))
    (cons (list (caar as) (list (cdar as) 'i '(cadr a) 'st)) (step-cases (cdr as)))))

(defmacro def-hm-step ()
  `(defun hm-step (i a st) (case (car a) ,@(step-cases (actions)))))

(def-hm-step)

(defun hm-run (sched st)
  (if (atom sched) st (hm-run (cdr sched) (hm-step (caar sched) (cdar sched) st))))

; ---- THE INVARIANT -------------------------------------------------------------------

(defun actp (p) (if (member-equal p (act-phases)) t nil))
(in-theory (disable actp))

(defun cnt-act (ths)
  (if (atom ths) 0 (+ (if (actp (th-ph (car ths))) 1 0) (cnt-act (cdr ths)))))
(defun cnt-park (ths)
  (if (atom ths) 0 (+ (if (eq (th-ph (car ths)) :parked) 1 0) (cnt-park (cdr ths)))))

; the first running (not parked) thread but c, from index k
(defun find-act (ths k c)
  (cond ((atom ths) nil)
        ((and (actp (th-ph (car ths))) (not (equal k c))) k)
        (t (find-act (cdr ths) (1+ k) c))))

; a thread's conditions, by its phase: who holds heap_lock (an :inheap
; or :collect thread), who stopped the world (a :stopping or :collect
; one), and that a parked or stopping thread waits for nothing else and
; holds the state lock not at all; a thread blocked on a lock does not
; hold it, and nothing waits for tx_lk holding the state lock
(defun th-ok (st k)
  (let* ((x (nth k (st-ths st))) (ph (th-ph x)) (w (th-w x)) (xw (th-xw x))
         (hl (st-hl st)) (sw (st-sw st)) (sl (st-sl st)) (xl (st-xl st)))
    (and (booleanp w) (booleanp xw) (true-listp (th-rts x)) (all-used (th-rts x) (st-own st))
         (not (and w (equal sl k))) (not (and xw (equal xl k))) (not (and xw (equal sl k)))
         (case ph
           (:out (and (not (equal hl k)) (not (equal sw k)) (not (and w xw))))
           (:run (and (not (equal hl k)) (not (equal sw k)) (not xw)))
           (:parked (and (not (equal hl k)) (not (equal sw k)) (not w) (not xw) (not (equal sl k))))
           (:inheap (and (equal hl k) (not (equal sw k)) (not xw)))
           (:stopping (and (equal sw k) (not (equal hl k)) (not w) (not xw) (not (equal sl k))))
           (:collect (and (equal hl k) (not xw)))
           (otherwise nil)))))

(defun-sk all-th-ok (st)
  (forall k (implies (and (natp k) (< k (len (st-ths st)))) (th-ok st k))))

(defun idx-ok (v n) (or (null v) (and (natp v) (< v n))))

(defthm idx-ok-nil (idx-ok nil n))
(defthm idx-ok-in (implies (and (natp v) (< v n)) (idx-ok v n)))
(defthm idx-ok-natp (implies (and (idx-ok v n) v) (natp v)))
(defthm idx-ok-lt (implies (and (idx-ok v n) v) (< v n)))
(in-theory (disable idx-ok))

(defun hm-inv-g (st)
  (let* ((hl (st-hl st)) (sw (st-sw st)) (ths (st-ths st)) (n (len ths)))
    (and (true-listp ths) (true-listp (st-own st))
         (idx-ok hl n) (idx-ok sw n) (idx-ok (st-sl st) n) (idx-ok (st-xl st) n)
         (implies (and sw (eq (th-ph (nth sw ths)) :stopping)) (null hl))
         (equal (st-nrun st) (+ (cnt-act ths) (cnt-park ths)))
         (equal (st-npark st) (cnt-park ths))
         (implies (and hl (eq (th-ph (nth hl ths)) :collect)) (null (find-act ths 0 hl))))))

(defun hm-inv (st) (and (hm-inv-g st) (all-th-ok st)))

; ---- LEMMAS --------------------------------------------------------------------------

(defthm len-update-nth-hm
  (implies (and (natp i) (< i (len l))) (equal (len (update-nth i y l)) (len l))))

(defthm cnt-act-update-nth
  (implies (and (natp i) (< i (len ths)))
           (equal (cnt-act (update-nth i y ths))
                  (+ (cnt-act ths) (- (if (actp (th-ph (nth i ths))) 1 0))
                     (if (actp (th-ph y)) 1 0)))))

(defthm cnt-park-update-nth
  (implies (and (natp i) (< i (len ths)))
           (equal (cnt-park (update-nth i y ths))
                  (+ (cnt-park ths) (- (if (eq (th-ph (nth i ths)) :parked) 1 0))
                     (if (eq (th-ph y) :parked) 1 0)))))

(defthm cnt-park-pos
  (implies (and (natp k) (< k (len ths)) (eq (th-ph (nth k ths)) :parked)) (<= 1 (cnt-park ths)))
  :rule-classes :linear)

(defthm cnt-act-pos
  (implies (and (natp k) (< k (len ths)) (actp (th-ph (nth k ths))))
           (<= 1 (cnt-act ths)))
  :rule-classes :linear)

(defun two-ind (i j ths)
  (if (or (zp i) (zp j) (atom ths)) (list i j ths) (two-ind (1- i) (1- j) (cdr ths))))

(defthm two-act
  (implies (and (natp i) (natp j) (not (equal i j)) (< i (len ths)) (< j (len ths))
                (actp (th-ph (nth i ths)))
                (actp (th-ph (nth j ths))))
           (<= 2 (cnt-act ths)))
  :hints (("Goal" :induct (two-ind i j ths))
          ("Subgoal *1/1" :cases ((zp i) (zp j))
           :use ((:instance cnt-act-pos (k (1- j)) (ths (cdr ths)))
                 (:instance cnt-act-pos (k (1- i)) (ths (cdr ths))))))
  :rule-classes :linear)

(defthm find-act-props
  (implies (and (find-act ths k c) (natp k))
           (and (natp (find-act ths k c)) (<= k (find-act ths k c))
                (< (find-act ths k c) (+ k (len ths)))
                (not (equal (find-act ths k c) c))
                (actp (th-ph (nth (- (find-act ths k c) k) ths)))))
  :rule-classes nil)

(defthm find-act-none
  (implies (and (null (find-act ths k c)) (natp k) (natp j) (<= k j) (< j (+ k (len ths)))
                (not (equal j c)))
           (not (actp (th-ph (nth (- j k) ths)))))
  :rule-classes nil)

(defthm find-act-update-same
  (implies (and (natp i) (< i (len ths))
                (iff (actp (th-ph y)) (actp (th-ph (nth i ths)))))
           (equal (find-act (update-nth i y ths) k c) (find-act ths k c)))
  :hints (("Goal" :induct (list (update-nth i y ths) (find-act ths k c)))))

(defthm rooted-update-same
  (implies (and (natp i) (< i (len ths)) (equal (th-rts y) (th-rts (nth i ths))))
           (equal (rooted (update-nth i y ths) c) (rooted ths c))))

(defun rooted-at (ths c)
  (cond ((atom ths) 0) ((member-equal c (th-rts (car ths))) 0) (t (1+ (rooted-at (cdr ths) c)))))

(defthm rooted-at-props
  (implies (rooted ths c)
           (and (natp (rooted-at ths c)) (< (rooted-at ths c) (len ths))
                (member-equal c (th-rts (nth (rooted-at ths c) ths))))))

(defthm member-rts-rooted
  (implies (and (natp k) (< k (len ths)) (member-equal c (th-rts (nth k ths)))) (rooted ths c)))

(defthm all-used-member
  (implies (and (all-used r own) (member-equal c r)) (and (natp c) (equal (nth c own) :used))))

(defthm all-used-update-used
  (implies (all-used r own) (all-used r (update-nth c :used own))))

(defthm all-used-update-unused
  (implies (and (all-used r own) (not (equal (nth c own) :used))) (all-used r (update-nth c v own)))
  :hints (("Goal" :induct (all-used r own))))

(defthm all-used-remove
  (implies (all-used r own) (all-used (remove-equal c r) own)))

(defthm true-listp-remove-hm
  (implies (true-listp r) (true-listp (remove-equal c r))))

(defthm len-sweep (equal (len (sweep own c ths who)) (len own)))

(defthm nth-sweep
  (implies (and (natp k) (natp c))
           (equal (nth k (sweep own c ths who))
                  (if (< k (len own)) (sweep1 (nth k own) (+ c k) ths who) nil)))
  :hints (("Goal" :induct (list (nth k own) (sweep own c ths who)))))

(defthm true-listp-sweep (true-listp (sweep own c ths who)))

(in-theory (disable sweep1))

(defthm sweep1-used-rooted
  (implies (rooted ths c) (equal (sweep1 :used c ths who) :used))
  :hints (("Goal" :in-theory (enable sweep1))))

(defthm all-used-sweep
  (implies (and (all-used r own) (natp k) (< k (len ths)) (subsetp-equal r (th-rts (nth k ths))))
           (all-used r (sweep own 0 ths who))))

(defthm subsetp-cons-hm (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
(defthm subsetp-self-hm (subsetp-equal x x))

; a cell any thread roots is :used
(defthm rooted-used-by-ok
  (implies (and (all-th-ok st) (rooted (st-ths st) c))
           (and (natp c) (equal (nth c (st-own st)) :used)))
  :hints (("Goal" :in-theory (disable all-th-ok-necc rooted-at-props th-ok)
                  :use ((:instance all-th-ok-necc (k (rooted-at (st-ths st) c)))
                        (:instance rooted-at-props (ths (st-ths st)))
                        (:instance all-used-member (r (th-rts (nth (rooted-at (st-ths st) c) (st-ths st))))
                                   (own (st-own st)))))
          ("Goal'" :in-theory (enable th-ok))))

(defthm cnt-act-park-le-len
  (<= (+ (cnt-act ths) (cnt-park ths)) (len ths))
  :hints (("Goal" :in-theory (enable actp)))
  :rule-classes :linear)

; with at most one thread running (not parked), none but i is
(defthm one-act-none-other
  (implies (and (<= (cnt-act ths) 1) (natp i) (< i (len ths)) (actp (th-ph (nth i ths))))
           (null (find-act ths 0 i)))
  :hints (("Goal" :use ((:instance find-act-props (k 0) (c i))
                        (:instance two-act (j (find-act ths 0 i)))))))

(defthm len-ths-step
  (equal (len (st-ths (hm-step i a st))) (len (st-ths st))))


; ---- THE INVARIANT HOLDS -------------------------------------------------------------
;
; action by action: each thread's conditions, then the global ones

(defun th-ok-thm (fn)
  `(defthm ,(packn (list 'th-ok- fn))
     (implies (and (hm-inv st) (natp k) (< k (len (st-ths st))))
              (th-ok (,fn i c st) k))
     :hints (("Goal" :in-theory (disable all-th-ok-necc rooted-used-by-ok all-th-ok)
                     :cases ((equal k i))
                     :use ((:instance all-th-ok-necc (k k))
                           (:instance all-th-ok-necc (k i))
                           (:instance rooted-used-by-ok (c c)))))))

(defun inv-g-thm (fn)
  `(defthm ,(packn (list 'inv-g- fn))
     (implies (hm-inv st) (hm-inv-g (,fn i c st)))
     :hints (("Goal" :in-theory (disable all-th-ok-necc all-th-ok)
                     :use ((:instance all-th-ok-necc (k i))
                           (:instance all-th-ok-necc (k (st-hl st)))
                           (:instance one-act-none-other (ths (st-ths st)))
                           (:instance find-act-none (ths (st-ths st)) (k 0) (c (st-hl st)) (j i)))))))

(defmacro action-thms (fn) (list 'progn (th-ok-thm fn) (inv-g-thm fn)))

(action-thms s-enter)
(action-thms s-leave)
(action-thms s-slock)
(action-thms s-sunlock)
(action-thms s-xlock)
(action-thms s-xunlock)
(action-thms s-henter)
(action-thms s-wake)
(action-thms s-hleave)
(action-thms s-stop)
(action-thms s-stopwake)
(action-thms s-start)
(action-thms s-collect)
(action-thms s-fast)
(action-thms s-take)
(action-thms s-refill)
(action-thms s-prefill)
(action-thms s-drop)
(action-thms s-load)


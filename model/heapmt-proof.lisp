; Several threads on one heap: the theorems (model/heapmt.lisp says what
; the model is, and what these prove).

(in-package "ACL2")

(include-book "heapmt")

; the actions one at a time, by their lemmas (heapmt's action-thms)
(deftheory step-fns '(s-enter s-leave s-slock s-sunlock s-xlock s-xunlock s-henter s-wake s-hleave s-stop s-stopwake s-start s-collect s-fast s-take s-refill s-prefill s-drop s-load))
(defthm idx-ok-integerp (implies (and (idx-ok v n) v) (integerp v)) :hints (("Goal" :in-theory (enable idx-ok))))
(defthm idx-ok-nonneg (implies (and (idx-ok v n) v) (<= 0 v)) :hints (("Goal" :in-theory (enable idx-ok))))
(defthm idx-ok-numberp (implies (and (idx-ok v n) v) (acl2-numberp v)) :hints (("Goal" :in-theory (enable idx-ok))))
(defthm len-pos-hm (implies (consp x) (< 0 (len x))) :rule-classes :linear)
; a step that moves a field has changed the state
(defthm mk-st-neq-hl (implies (not (equal a (st-hl st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-hl))))
(defthm mk-st-neq-sw (implies (not (equal b (st-sw st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-sw))))
(defthm mk-st-neq-nrun (implies (not (equal c (st-nrun st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-nrun))))
(defthm mk-st-neq-npark (implies (not (equal d (st-npark st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-npark))))
(defthm mk-st-neq-sl (implies (not (equal e (st-sl st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-sl))))
(defthm mk-st-neq-xl (implies (not (equal f (st-xl st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-xl))))
(defthm mk-st-neq-own (implies (not (equal g (st-own st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-own))))
(defthm mk-st-neq-ths (implies (not (equal h (st-ths st))) (not (equal (mk-st a b c d e f g h) st))) :hints (("Goal" :in-theory (enable mk-st st-ths))))
(in-theory (disable s-enter s-leave s-slock s-sunlock s-xlock s-xunlock s-henter s-wake s-hleave s-stop s-stopwake s-start s-collect s-fast s-take s-refill s-prefill s-drop s-load))

(defthm th-ok-step
  (implies (and (hm-inv st) (natp k) (< k (len (st-ths st))))
           (th-ok (hm-step i a st) k))
  :hints (("Goal" :in-theory (disable all-th-ok-necc all-th-ok hm-inv-g th-ok)
                  :use ((:instance all-th-ok-necc (k k))))))

(defthm all-th-ok-step
  (implies (hm-inv st) (all-th-ok (hm-step i a st)))
  :hints (("Goal" :in-theory (disable th-ok-step hm-step th-ok hm-inv)
                  :use ((:instance th-ok-step (k (all-th-ok-witness (hm-step i a st))))))))

(defthm inv-g-step
  (implies (hm-inv st) (hm-inv-g (hm-step i a st)))
  :hints (("Goal" :in-theory (disable hm-inv-g all-th-ok))))

; THE INVARIANT, under every step and so every schedule
(defthm hm-inv-step
  (implies (hm-inv st) (hm-inv (hm-step i a st)))
  :hints (("Goal" :in-theory (disable hm-step hm-inv-g all-th-ok))))

(in-theory (disable hm-step))

(defthm hm-inv-run
  (implies (hm-inv st) (hm-inv (hm-run sched st)))
  :hints (("Goal" :induct (hm-run sched st) :in-theory (disable hm-inv))))

; ---- ROOTS ---------------------------------------------------------------------------

; in every reachable state, a cell any thread roots is :used -- on no free
; list, in no batch, on no pending list
(defthm rooted-is-used
  (implies (and (hm-inv st) (rooted (st-ths (hm-run sched st)) c))
           (equal (nth c (st-own (hm-run sched st))) :used))
  :hints (("Goal" :in-theory (disable hm-run hm-inv-run hm-inv-g)
                  :use ((:instance hm-inv-run)
                        (:instance rooted-used-by-ok (st (hm-run sched st)))))))

; and a collection's sweep leaves every rooted cell as it was
(defthm sweep-keeps-rooted
  (implies (and (natp c) (< c (len own)) (rooted ths c) (equal (nth c own) :used))
           (equal (nth c (sweep own 0 ths who)) :used)))

; ---- BATCHES -------------------------------------------------------------------------

; a cell in thread i's batch: no other thread's step takes or moves it
(defthm batch-private
  (implies (and (natp c) (< c (len (st-own st))) (equal (nth c (st-own st)) (cons :b i)) (not (equal i j)))
           (equal (nth c (st-own (hm-step j a st))) (cons :b i)))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step sweep1) (theory 'step-fns))) '())
                  :cases ((natp c)))))

(defthm others-cannot-pop
  (implies (and (equal (nth c (st-own st)) (cons :b i)) (not (equal i j)))
           (equal (hm-step j (list :fast c) st) st))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step) (theory 'step-fns))) '()))))

; the cell an allocation (fast or slow) hands out is in no thread's roots
(defthm alloc-fresh
  (implies (and (hm-inv st) (member-equal (car a) '(:fast :take))
                (not (equal (hm-step i a st) st)))
           (not (rooted (st-ths st) (cadr a))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step) (theory 'step-fns))) '(all-th-ok hm-inv-g))
                  :use ((:instance rooted-used-by-ok (c (cadr a)))))))

; ---- STOP ----------------------------------------------------------------------------

(defun collector (st)
  (and (st-hl st) (eq (th-ph (nth (st-hl st) (st-ths st))) :collect)))

; while a collection runs, every other thread is parked or out
(defthm collect-others-stopped
  (implies (and (hm-inv st) (collector st) (natp j) (< j (len (st-ths st)))
                (not (equal j (st-hl st))))
           (member-equal (th-ph (nth j (st-ths st))) '(:parked :out)))
  :hints (("Goal" :in-theory (e/d (actp) (all-th-ok-necc all-th-ok))
                  :use ((:instance find-act-none (ths (st-ths st)) (k 0) (c (st-hl st)))
                        (:instance all-th-ok-necc (k j))))))

; what a thread other than the collector may not change: the heap's
; locks and counters, the cells, every phase and every root (it may only
; take or wait for the state lock or tx_lk, out of the heap)
(defun strip-w (ths)
  (if (atom ths) nil (cons (list (th-ph (car ths)) (th-rts (car ths))) (strip-w (cdr ths)))))

(defun frozen (st)
  (list (st-hl st) (st-sw st) (st-nrun st) (st-npark st) (st-own st) (strip-w (st-ths st))))

(defthm strip-w-update-same
  (implies (and (natp i) (< i (len ths)) (equal (th-ph y) (th-ph (nth i ths)))
                (equal (th-rts y) (th-rts (nth i ths))))
           (equal (strip-w (update-nth i y ths)) (strip-w ths))))

(defthm stop-excludes
  (implies (and (hm-inv st) (collector st) (not (equal i (st-hl st))))
           (equal (frozen (hm-step i a st)) (frozen st)))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step) (theory 'step-fns))) '(all-th-ok-necc all-th-ok collect-others-stopped))
                  :use ((:instance collect-others-stopped (j i))))))

; ---- NO DEADLOCK ---------------------------------------------------------------------

(defun find-w (ths k) (cond ((atom ths) nil) ((th-w (car ths)) k) (t (find-w (cdr ths) (1+ k)))))
(defun find-xw (ths k) (cond ((atom ths) nil) ((th-xw (car ths)) k) (t (find-xw (cdr ths) (1+ k)))))
(defun find-park (ths k)
  (cond ((atom ths) nil) ((eq (th-ph (car ths)) :parked) k) (t (find-park (cdr ths) (1+ k)))))

(defthm find-w-props
  (implies (and (find-w ths k) (natp k))
           (and (natp (find-w ths k)) (<= k (find-w ths k)) (< (find-w ths k) (+ k (len ths)))
                (th-w (nth (- (find-w ths k) k) ths))))
  :rule-classes nil)
(defthm find-w-none
  (implies (and (null (find-w ths k)) (natp k) (natp j) (<= k j) (< j (+ k (len ths))))
           (not (th-w (nth (- j k) ths))))
  :rule-classes nil)
(defthm find-xw-props
  (implies (and (find-xw ths k) (natp k))
           (and (natp (find-xw ths k)) (<= k (find-xw ths k)) (< (find-xw ths k) (+ k (len ths)))
                (th-xw (nth (- (find-xw ths k) k) ths))))
  :rule-classes nil)
(defthm find-xw-none
  (implies (and (null (find-xw ths k)) (natp k) (natp j) (<= k j) (< j (+ k (len ths))))
           (not (th-xw (nth (- j k) ths))))
  :rule-classes nil)
(defthm find-park-props
  (implies (and (find-park ths k) (natp k))
           (and (natp (find-park ths k)) (<= k (find-park ths k)) (< (find-park ths k) (+ k (len ths)))
                (eq (th-ph (nth (- (find-park ths k) k) ths)) :parked)))
  :rule-classes nil)
(defthm find-park-none
  (implies (and (null (find-park ths k)) (natp k) (natp j) (<= k j) (< j (+ k (len ths))))
           (not (eq (th-ph (nth (- j k) ths)) :parked)))
  :rule-classes nil)

; with none running but c, at most c runs
(defthm find-act-none-count
  (implies (and (null (find-act ths k c)) (natp k))
           (<= (cnt-act ths) (if (and (natp c) (<= k c) (< c (+ k (len ths)))) 1 0)))
  :rule-classes nil)

; the thread that can go, and what it does: the state lock's holder lets
; it go; else a thread blocked on it takes it; else heap_lock's holder
; leaves the heap or starts the world; else the stopper's wait ends, or a
; thread still running reaches its safepoint; else a parked thread goes
; on; else tx_lk's holder lets it go, or one blocked on it takes it; else
; every thread is out, and one comes in
(defun progress (st)
  (let ((ths (st-ths st)) (sl (st-sl st)) (hl (st-hl st)) (sw (st-sw st)) (xl (st-xl st)))
    (cond (sl (list sl :sunlock))
          ((find-w ths 0) (list (find-w ths 0) :slock))
          (hl (if (eq (th-ph (nth hl ths)) :collect) (list hl :start) (list hl :hleave)))
          ((and sw (<= (1- (st-nrun st)) (st-npark st))) (list sw :stopwake))
          ((find-act ths 0 sw) (list (find-act ths 0 sw) :henter))
          ((find-park ths 0) (list (find-park ths 0) :wake))
          (xl (list xl :xunlock))
          ((find-xw ths 0) (list (find-xw ths 0) :xlock))
          (t (list 0 :enter)))))

; case by case, the witness's step changes the state
(defun expand-nec (us)
  (if (atom us) nil
    (cons (if (and (consp (car us)) (eq (caar us) 'nec))
              (list :instance 'all-th-ok-necc (list 'k (cadar us)))
            (car us))
          (expand-nec (cdr us)))))
(defmacro pthm (name hyps concl &rest uses)
  `(defthm ,name
     (implies (and (hm-inv st) ,@hyps) ,concl)
     :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(actp) (theory 'step-fns))) '(all-th-ok-necc all-th-ok))
                     :use ,(expand-nec uses)))
     :rule-classes nil))

(pthm pr-sunlock ((st-sl st))
      (not (equal (s-sunlock (st-sl st) c st) st))
      (nec (st-sl st)))

(pthm pr-slock ((not (st-sl st)) (find-w (st-ths st) 0))
      (not (equal (s-slock (find-w (st-ths st) 0) c st) st))
      (nec (find-w (st-ths st) 0)) (:instance find-w-props (ths (st-ths st)) (k 0)))

(pthm pr-hl ((not (st-sl st)) (not (find-w (st-ths st) 0)) (st-hl st))
      (if (eq (th-ph (nth (st-hl st) (st-ths st))) :collect)
          (not (equal (s-start (st-hl st) c st) st))
        (not (equal (s-hleave (st-hl st) c st) st)))
      (nec (st-hl st)) (:instance find-w-none (ths (st-ths st)) (k 0) (j (st-hl st))))

(pthm pr-stopwake ((not (st-hl st)) (st-sw st) (<= (1- (st-nrun st)) (st-npark st)))
      (not (equal (s-stopwake (st-sw st) c st) st))
      (nec (st-sw st)))

(pthm pr-henter ((not (st-sl st)) (not (find-w (st-ths st) 0)) (not (st-hl st))
                 (find-act (st-ths st) 0 (st-sw st)))
      (not (equal (s-henter (find-act (st-ths st) 0 (st-sw st)) c st) st))
      (nec (find-act (st-ths st) 0 (st-sw st)))
      (:instance find-act-props (ths (st-ths st)) (k 0) (c (st-sw st)))
      (:instance find-w-none (ths (st-ths st)) (k 0) (j (find-act (st-ths st) 0 (st-sw st)))))

; with none running but the stopper, the stop's wait is over
(pthm pr-no-sw ((not (st-hl st)) (not (find-act (st-ths st) 0 (st-sw st))))
      (not (and (st-sw st) (< (st-npark st) (1- (st-nrun st)))))
      (nec (st-sw st))
      (:instance find-act-none-count (ths (st-ths st)) (k 0) (c (st-sw st))))

(pthm pr-wake ((not (st-sl st)) (not (find-w (st-ths st) 0)) (not (st-hl st)) (not (st-sw st))
               (find-park (st-ths st) 0))
      (not (equal (s-wake (find-park (st-ths st) 0) c st) st))
      (:instance find-park-props (ths (st-ths st)) (k 0)))

(pthm pr-xunlock ((not (st-sl st)) (not (find-w (st-ths st) 0)) (not (st-hl st)) (not (st-sw st))
                  (not (find-act (st-ths st) 0 nil)) (not (find-park (st-ths st) 0)) (st-xl st))
      (not (equal (s-xunlock (st-xl st) c st) st))
      (nec (st-xl st))
      (:instance find-w-none (ths (st-ths st)) (k 0) (j (st-xl st)))
      (:instance find-act-none (ths (st-ths st)) (k 0) (c nil) (j (st-xl st)))
      (:instance find-park-none (ths (st-ths st)) (k 0) (j (st-xl st))))

(pthm pr-xlock ((not (st-sl st)) (not (find-w (st-ths st) 0)) (not (st-xl st)) (find-xw (st-ths st) 0))
      (not (equal (s-xlock (find-xw (st-ths st) 0) c st) st))
      (nec (find-xw (st-ths st) 0)) (:instance find-xw-props (ths (st-ths st)) (k 0))
      (:instance find-w-none (ths (st-ths st)) (k 0) (j (find-xw (st-ths st) 0))))

(pthm pr-enter ((consp (st-ths st)) (not (st-sl st)) (not (find-w (st-ths st) 0)) (not (st-hl st))
                (not (st-sw st)) (not (find-act (st-ths st) 0 nil)) (not (find-park (st-ths st) 0))
                (not (st-xl st)) (not (find-xw (st-ths st) 0)))
      (not (equal (s-enter 0 c st) st))
      (nec 0)
      (:instance find-w-none (ths (st-ths st)) (k 0) (j 0))
      (:instance find-xw-none (ths (st-ths st)) (k 0) (j 0))
      (:instance find-act-none (ths (st-ths st)) (k 0) (c nil) (j 0))
      (:instance find-park-none (ths (st-ths st)) (k 0) (j 0)))

(defthm progress-thm
  (implies (and (hm-inv st) (consp (st-ths st)))
           (not (equal (hm-step (car (progress st)) (cdr (progress st)) st) st)))
  :hints (("Goal" :in-theory (e/d (hm-step) (hm-inv all-th-ok))
                  :use ((:instance pr-sunlock (c nil)) (:instance pr-slock (c nil)) (:instance pr-hl (c nil))
                        (:instance pr-stopwake (c nil)) (:instance pr-henter (c nil)) pr-no-sw
                        (:instance pr-wake (c nil)) (:instance pr-xunlock (c nil))
                        (:instance pr-xlock (c nil)) (:instance pr-enter (c nil))))))

; WITHOUT THE DISCIPLINE: thread 0 parked holding the state lock (it
; entered the heap holding it), thread 1 stopping the world, thread 2
; running and blocked on the state lock. The stop waits for 2 to park, 2
; for the lock, 0 for the stop: no step of any thread changes anything.
(defconst *stuck*
  (mk-st nil 1 3 1 0 nil '(:used)
         (list (mk-th :parked nil nil nil) (mk-th :stopping nil nil nil) (mk-th :run t nil nil))))

(defthm parked-under-state-lock-is-stuck
  (equal (hm-step i a *stuck*) *stuck*)
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step mk-st mk-th) (theory 'step-fns))) '())
                  :cases ((equal i 0) (equal i 1) (equal i 2)))))

; ---- COST ----------------------------------------------------------------------------
;
; THE STOP. world_stop waits until n_parked = n_running - 1; what it waits
; for is the deficit, n_running - 1 - n_parked. It is at most n - 1, no
; step while the stop waits makes it larger (gc_mutator_enter and a
; parked thread's going on both wait for the world to start), and a
; thread reaching its safepoint makes it smaller by one: the stop waits
; for at most n - 1 parks or leaves, whatever the threads do.

(defun deficit (st) (- (st-nrun st) (+ 1 (st-npark st))))

(defthm stop-deficit-bounded
  (implies (hm-inv st) (<= (deficit st) (1- (len (st-ths st)))))
  :hints (("Goal" :in-theory (disable all-th-ok))))

(defthm stop-deficit-shrinks
  (implies (and (hm-inv st) (st-sw st))
           (<= (deficit (hm-step j a st)) (deficit st)))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step) (theory 'step-fns))) '(all-th-ok)))))

(defthm safepoint-shrinks-deficit
  (implies (and (hm-inv st) (st-sw st) (not (equal (hm-step j (list :henter) st) st)))
           (equal (deficit (hm-step j (list :henter) st)) (1- (deficit st))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories (current-theory :here) (append '(hm-step) (theory 'step-fns))) '(all-th-ok)))))

; THE COLLECTOR'S PASSES over the threads -- merge_batches, finish_pending,
; push_roots, hand_off_young -- each a turn a thread, and push_roots a
; turn a root besides: 4 a thread plus their roots (the per-cell work in
; them is the heap books' cost)
(defun passes-c (ths)
  (if (atom ths) 0 (+ 4 (len (th-rts (car ths))) (passes-c (cdr ths)))))

(defun all-roots-len (ths)
  (if (atom ths) 0 (+ (len (th-rts (car ths))) (all-roots-len (cdr ths)))))

(defthm collect-threads-cost
  (equal (passes-c ths) (+ (* 4 (len ths)) (all-roots-len ths))))

; A REFILL FROM THE PENDING LIST (pend_refill_obj): from the cursor on,
; each entry a turn, a dead one into the batch, until the batch is full;
; the turns are at most the entries and the batch gains at most its room.
; Nothing in it reads another thread. (The fill from the free list,
; hpg_obj_fill, is at most ALLOC_BATCH turns: heap-cost's hpg-%-fill-cost.)
(defun prefill-c (p room own i)
  (declare (xargs :measure (len p)))
  (if (or (atom p) (zp room)) (mv 0 0)
    (mv-let (taken turns) (prefill-c (cdr p) (if (equal (nth (car p) own) (cons :p i)) (1- room) room) own i)
      (mv (+ taken (if (equal (nth (car p) own) (cons :p i)) 1 0)) (1+ turns)))))

(defthm prefill-cost
  (implies (natp room)
           (and (<= (mv-nth 1 (prefill-c p room own i)) (len p))
                (<= (mv-nth 0 (prefill-c p room own i)) room)))
  :rule-classes nil)

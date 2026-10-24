; Futures, promises, latches, mailboxes and a wait's deadlock verdict,
; formally (docs/model-coverage.md).
;
; src/f/tasks.inc: every wait is block_on (a task finished, a promise
; delivered -- an atom set once by compare-and-set!, a latch at zero, a
; mailbox with a message), or a pool worker parked in sched_take
; (Eval.f90) until there is work. Under the state lock a waiter checks its
; target; ready, it goes on; with a deadline it sleeps until then; with
; none it sleeps until a notify or a 200 ms re-check -- unless the wait
; is a deadlock: every live thread waiting with no deadline. That
; verdict is an error, not a hang. Everything that makes a target ready
; is a live thread's act under the state lock, announced (gc_state_notify).
;
; The verdict counted the waiters (blocked_nodl + 1 >= live_threads, no
; deadline among them) and took a 100 ms pause with nothing announced to
; mean none of them was about to wake. That is a timing assumption, and
; it is wrong: a waiter whose target a thread readied just before it
; exited is still counted until the scheduler runs it, and on a loaded
; machine that is more than 100 ms -- the verdict then throws "deadlock"
; at a program that was going on (old-verdict-is-wrong, below). Now each
; waiter registers its target (tasks.inc, wait_kind/wait_target) and the
; verdict also asks whether any registered target is ready
; (any_waiter_ready): exact, with no clock in it.
;
; Here threads run programs of acts: (:sat t) and (:unsat t) make target
; t ready or not (a deliver, a finish, a count down, a send; a take), (:wait
; t dl) waits on t with or without a deadline, (:exit) ends the thread.
; Targets are names; ready is the list S. A sleeping waiter may wake at
; any step (a notify, its re-check, its deadline).
;
; What it proves, under every interleaving:
;
;   SOUND      a verdict is a deadlock: at that step every other live
;              thread is asleep with no deadline on a target not ready,
;              the verdict's own target is not ready, and no live thread
;              is left to make one ready -- every step from there leaves
;              S as it is
;   COMPLETE   in such a state, a waiter that re-checks reaches the
;              verdict: a deadlock is reported, not hung on
;   COUNTED    blocked_nodl and blocked_dl are the sleepers without and
;              with a deadline, live_threads the threads not exited
;   COST       once the state is a deadlock, the first re-check (within
;              200 ms of any sleeper) gives the verdict: 1 step
;
; Not modelled: the deadline's clock (a deadline is a wake at any time),
; and the waits the verdict does not count -- a lazy seq's, a monitor's
; -- which can make a deadlock a hang but never a verdict wrong.

(in-package "ACL2")

; a thread: (pc prog tgt dl); pc :run (prog the acts left), :check,
; :asleep, :dead (the verdict), :exited
(defun mk-t (pc prog tgt dl) (list pc prog tgt dl))
(defun t-pc (x) (nth 0 x))
(defun t-prog (x) (nth 1 x))
(defun t-tgt (x) (nth 2 x))
(defun t-dl (x) (nth 3 x))

; st = (s nodl dlc nlive ths): s the ready targets, the three counters
(defun count-pc (ths pc dl)
  (if (atom ths) 0
    (+ (if (and (equal (t-pc (car ths)) pc) (iff (t-dl (car ths)) dl)) 1 0)
       (count-pc (cdr ths) pc dl))))

(defun count-live (ths)
  (if (atom ths) 0 (+ (if (equal (t-pc (car ths)) :exited) 0 1) (count-live (cdr ths)))))

; any_waiter_ready: a sleeper with no deadline whose target is ready
(defun any-ready (ths s)
  (if (atom ths) nil
    (or (and (equal (t-pc (car ths)) :asleep) (not (t-dl (car ths))) (member-equal (t-tgt (car ths)) s))
        (any-ready (cdr ths) s))))

(defun wt-step (i st)
  (let* ((s (nth 0 st)) (nodl (nth 1 st)) (dlc (nth 2 st)) (nlive (nth 3 st)) (ths (nth 4 st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let* ((x (nth i ths)) (a (car (t-prog x))))
        (case (t-pc x)
          (:run
           (cond ((atom (t-prog x)) st)
                 ((eq (car a) :sat)
                  (list (if (member-equal (cadr a) s) s (cons (cadr a) s)) nodl dlc nlive
                        (update-nth i (mk-t :run (cdr (t-prog x)) nil nil) ths)))
                 ((eq (car a) :unsat)
                  (list (remove-equal (cadr a) s) nodl dlc nlive
                        (update-nth i (mk-t :run (cdr (t-prog x)) nil nil) ths)))
                 ((eq (car a) :wait)
                  (list s nodl dlc nlive (update-nth i (mk-t :check (cdr (t-prog x)) (cadr a) (caddr a)) ths)))
                 ((eq (car a) :exit)
                  (list s nodl dlc (1- nlive) (update-nth i (mk-t :exited nil nil nil) ths)))
                 (t (list s nodl dlc nlive (update-nth i (mk-t :run (cdr (t-prog x)) nil nil) ths)))))
          ; block_on's check, under the state lock
          (:check
           (cond ((member-equal (t-tgt x) s)
                  (list s nodl dlc nlive (update-nth i (mk-t :run (t-prog x) nil nil) ths)))
                 ((t-dl x)
                  (list s nodl (1+ dlc) nlive (update-nth i (mk-t :asleep (t-prog x) (t-tgt x) t) ths)))
                 ((and (equal dlc 0) (<= nlive (1+ nodl)) (not (any-ready ths s)))
                  (list s nodl dlc nlive (update-nth i (mk-t :dead (t-prog x) (t-tgt x) nil) ths)))
                 (t (list s (1+ nodl) dlc nlive (update-nth i (mk-t :asleep (t-prog x) (t-tgt x) nil) ths)))))
          ; a wake: a notify, the re-check, the deadline -- back to the check
          (:asleep
           (if (t-dl x)
               (list s nodl (1- dlc) nlive (update-nth i (mk-t :check (t-prog x) (t-tgt x) t) ths))
             (list s (1- nodl) dlc nlive (update-nth i (mk-t :check (t-prog x) (t-tgt x) nil) ths))))
          (otherwise st))))))

(defun wt-run (sched st) (if (atom sched) st (wt-run (cdr sched) (wt-step (car sched) st))))

(defun wt-inv (st)
  (let ((nodl (nth 1 st)) (dlc (nth 2 st)) (nlive (nth 3 st)) (ths (nth 4 st)))
    (and (true-listp st) (equal (len st) 5)
         (equal nodl (count-pc ths :asleep nil))
         (equal dlc (count-pc ths :asleep t))
         (equal nlive (count-live ths)))))

(defthm count-pc-update-nth
  (implies (and (natp i) (< i (len ths)))
           (equal (count-pc (update-nth i y ths) pc dl)
                  (+ (count-pc ths pc dl)
                     (- (if (and (equal (t-pc (nth i ths)) pc) (iff (t-dl (nth i ths)) dl)) 1 0))
                     (if (and (equal (t-pc y) pc) (iff (t-dl y) dl)) 1 0)))))

(defthm count-live-update-nth
  (implies (and (natp i) (< i (len ths)))
           (equal (count-live (update-nth i y ths))
                  (+ (count-live ths)
                     (- (if (equal (t-pc (nth i ths)) :exited) 0 1))
                     (if (equal (t-pc y) :exited) 0 1)))))

(defthm len-update-nth-wt
  (implies (and (natp i) (< i (len l))) (equal (len (update-nth i y l)) (len l))))

; COUNTED: the counters are the counts, whatever runs
(defthm wt-inv-step
  (implies (wt-inv st) (wt-inv (wt-step i st)))
  :hints (("Goal" :do-not-induct t)))

(defthm wt-inv-run
  (implies (wt-inv st) (wt-inv (wt-run sched st)))
  :hints (("Goal" :in-theory (disable wt-step wt-inv))))

; ---- SOUND ---------------------------------------------------------------------
;
; awake: live, and not asleep without a deadline
(defun awake-p (x)
  (and (not (equal (t-pc x) :exited)) (not (and (equal (t-pc x) :asleep) (not (t-dl x))))))

(defun awake-count (l) (if (atom l) 0 (+ (if (awake-p (car l)) 1 0) (awake-count (cdr l)))))

(defthm live-is-asleep-plus-awake
  (equal (count-live l) (+ (count-pc l :asleep nil) (awake-count l))))

; every thread but the one at place i (counting from j): gone, or asleep
; with no deadline on a target not ready
(defun stuck-but (l i j s)
  (if (atom l) t
    (and (or (equal i j) (equal (t-pc (car l)) :exited)
             (and (equal (t-pc (car l)) :asleep) (not (t-dl (car l))) (not (member-equal (t-tgt (car l)) s))))
         (stuck-but (cdr l) i (1+ j) s))))

(defthm awake-count-pos
  (implies (and (natp k) (< k (len l)) (awake-p (nth k l))) (<= 1 (awake-count l)))
  :rule-classes :linear)

(defthm stuck-but-none-awake
  (implies (and (equal (awake-count l) 0) (not (any-ready l s)))
           (stuck-but l i j s)))

(defthm nth-pos-cdr
  (implies (and (integerp n) (< 0 n)) (equal (nth n l) (nth (1- n) (cdr l)))))

(defthm stuck-but-from-count
  (implies (and (natp i) (natp j) (<= j i) (< i (+ j (len l)))
                (awake-p (nth (- i j) l)) (<= (awake-count l) 1) (not (any-ready l s)))
           (stuck-but l i j s))
  :hints (("Goal" :induct (stuck-but l i j s))
          ("Subgoal *1/2" :cases ((equal i j)))
          (and stable-under-simplificationp
               (quote (:use ((:instance awake-count-pos (l (cdr l)) (k (+ i (- j) -1)))))))))

; the verdict's test, at thread i's check, says: every other live thread
; sleeps with no deadline on a target not ready, and i's own is not ready
(defthm verdict-sound
  (let* ((s (nth 0 st)) (nodl (nth 1 st)) (dlc (nth 2 st)) (nlive (nth 3 st)) (ths (nth 4 st)) (x (nth i ths)))
    (implies (and (wt-inv st) (natp i) (< i (len ths)) (equal (t-pc x) :check)
                  (not (member-equal (t-tgt x) s)) (not (t-dl x))
                  (equal dlc 0) (<= nlive (1+ nodl)) (not (any-ready ths s)))
             (stuck-but ths i 0 s)))
  :hints (("Goal" :use ((:instance stuck-but-from-count (l (nth 4 st)) (j 0) (s (nth 0 st)))
                        (:instance awake-count-pos (l (nth 4 st)) (k i)))
                  :in-theory (disable stuck-but-from-count awake-count-pos))))

; ... and from such a state nothing makes a target ready: every thread's
; step leaves S as it is -- the wakes only check again
(defun stuck-all (l s)
  (if (atom l) t
    (and (or (equal (t-pc (car l)) :exited) (equal (t-pc (car l)) :dead)
             (and (member-equal (t-pc (car l)) '(:asleep :check)) (not (t-dl (car l)))
                  (not (member-equal (t-tgt (car l)) s))))
         (stuck-all (cdr l) s))))

(defthm stuck-all-nth
  (implies (and (stuck-all l s) (natp i) (< i (len l)))
           (or (equal (t-pc (nth i l)) :exited) (equal (t-pc (nth i l)) :dead)
               (and (member-equal (t-pc (nth i l)) '(:asleep :check)) (not (t-dl (nth i l)))
                    (not (member-equal (t-tgt (nth i l)) s)))))
  :rule-classes nil)

(defthm stuck-all-update
  (implies (and (stuck-all l s) (natp i) (< i (len l))
                (or (equal (t-pc y) :exited) (equal (t-pc y) :dead)
                    (and (member-equal (t-pc y) '(:asleep :check)) (not (t-dl y))
                         (not (member-equal (t-tgt y) s)))))
           (stuck-all (update-nth i y l) s)))

(defthm deadlock-is-stable
  (implies (and (wt-inv st) (stuck-all (nth 4 st) (nth 0 st)))
           (and (equal (nth 0 (wt-step j st)) (nth 0 st))
                (stuck-all (nth 4 (wt-step j st)) (nth 0 st))))
  :hints (("Goal" :use ((:instance stuck-all-nth (l (nth 4 st)) (s (nth 0 st)) (i j)))
                  :do-not-induct t)))

; ---- COMPLETE -------------------------------------------------------------------
;
; in a deadlock -- every live thread waiting with no deadline on a target
; not ready -- a waiter's check gives the verdict
(defthm stuck-all-no-ready
  (implies (stuck-all l s) (not (any-ready l s))))

(defthm stuck-all-no-dl (implies (stuck-all l s) (equal (count-pc l :asleep t) 0)))

; the last waiter awake (the others asleep, gone, or already told) gets
; the verdict at its check: a deadlock is reported, not hung on
(defthm verdict-complete
  (let* ((ths (nth 4 st)) (x (nth i ths)))
    (implies (and (wt-inv st) (stuck-all ths (nth 0 st)) (natp i) (< i (len ths))
                  (equal (t-pc x) :check) (equal (awake-count ths) 1))
             (equal (t-pc (nth i (nth 4 (wt-step i st)))) :dead)))
  :hints (("Goal" :use ((:instance stuck-all-nth (l (nth 4 st)) (s (nth 0 st))))
                  :do-not-induct t)))

; COST: from a deadlock, the verdict is that one step of the check

; ---- the counted verdict it replaced --------------------------------------------
;
; T2 delivered p and exited; T1, asleep on p, has not run yet; T0 checks
; its wait on f (T1 finishes f once it runs). The counters say every live
; thread waits (nodl 1, live 2, no deadlines): the old verdict, after its
; 100 ms with nothing announced -- T1 still not scheduled -- said deadlock.
; T1 is ready (any-ready), so the check now does not, and T1 does go on:
; three of its steps later f is ready.
(defconst *late-wake*
  (list (list :p) 1 0 2
        (list (mk-t :check nil :f nil)
              (mk-t :asleep (list (list :sat :f)) :p nil)
              (mk-t :exited nil nil nil))))

(defthm old-verdict-is-wrong
  (let ((st *late-wake*))
    (and (wt-inv st)
         ; what the old verdict looked at says deadlock ...
         (equal (nth 2 st) 0) (<= (nth 3 st) (1+ (nth 1 st)))
         ; ... but a sleeper is ready, so the check now sleeps instead
         (any-ready (nth 4 st) (nth 0 st))
         (equal (t-pc (nth 0 (nth 4 (wt-step 0 st)))) :asleep)
         ; and the sleeper goes on and readies f
         (member-equal :f (nth 0 (wt-run (list 1 1 1) st)))))
  :rule-classes nil)

; clotran's agents and their scheduler, formally (PLAN step 24). The
; language semantics are Clojure's: an agent holds a QUEUE of actions
; and an ERROR; its actions run one at a time, in the order sent; a send
; made INSIDE an action is held until the action ends and released then,
; in order, after the agent's state is set -- or dropped if the action
; threw; an action that throws fails the agent under :fail (its queue is
; kept, nothing runs until restart-agent, which either resubmits it or
; clears it) and is forgotten under :continue; a send inside a
; transaction is held until the commit. The scheduler underneath is the
; one the strong runtimes (BEAM, Pony, Go, Tokio) share, not clj's host's:
;
; - a RUN QUEUE per worker of agents with work, and one :global queue for
;   agents made runnable from outside the workers (the REPL, a future, a
;   commit); a worker takes from its own queue, from :global every nth
;   pick so it cannot starve, and otherwise STEALS half of a victim's
;   queue into its own empty one;
; - a BATCH: a worker runs at most b actions of one agent, then puts it
;   at the back of its queue if it has more, so a flooded agent cannot
;   starve the rest;
; - the :solo executor (send-off) has a worker per agent, no cap: a
;   blocking action holds nothing else up.
;
; THE STATE is (agents runq running holds log sent ticks):
;   agents   a -> (q err mode): the actions queued in order, whether the
;            agent is failed, its error mode (:fail or :continue)
;   runq     key -> agent ids waiting, in order; a key is a pool worker,
;            :global, or :solo
;   running  worker -> (agent kind left): the agent whose head the
;            worker runs, and how many actions of it remain in this batch
;            (nil: no cap, the :solo executor)
;   holds    holder -> (agent . action)s held, in order: a running
;            worker's nested sends, an open transaction's
;   log      (agent . action) finished, in order
;   sent     a -> the actions dispatched to a, in order (a ghost: never
;            read by the machine; restart-agent :clear-actions drops the
;            queued ones from it, since the user asked for them dropped)
;   ticks    worker -> local picks since its last :global pick
; THE EVENTS, in any order; k the pool's size, b the batch, n the
; :global period:
;   (:new a mode)       an agent is made
;   (:send h a act)     a send: from holder h (a running worker, an open
;                       transaction) it is held; from a worker w it goes
;                       to w's queue when the agent was idle; from
;                       anywhere else to :global (or :solo by kind)
;   (:take w)           a free pool worker w takes the head of its own
;                       queue, or of :global, as the period says
;   (:steal w v)        w, idle with an empty queue, moves the first half
;                       of v's queue to its own
;   (:take-solo w)      a free solo worker takes the head of :solo
;   (:finish w ok)      w's action ends: ok, or it threw
;   (:restart a clear)  restart-agent, with or without :clear-actions
;   (:tx h) (:commit h) (:abort h)   a transaction opens, commits, aborts
;
; THE THEOREMS hold for every schedule, so for every interleaving of
; every number of threads:
;   agents-serial    no two workers run the same agent at once
;   agents-order     the actions dispatched to an agent are exactly the
;                    ones it has run, in order, followed by its queue:
;                    nothing lost, nothing reordered, nothing run twice
;   agents-head      an agent is on a run queue or a worker exactly
;                    when it is unfailed with a nonempty queue -- the
;                    queues never hold a duplicate, a failed agent, or
;                    an idle one
;   agents-live      unfailed work queued means a take, a steal or a
;                    finish is enabled: the scheduler cannot deadlock
;                    (an action that waits on another agent is Clojure's
;                    error, not a schedule)
;   steal-no-delay   a steal leaves every agent it moves and every agent
;                    it leaves behind no further from the front
;   drive-finishes   the scheduler that finishes what runs and takes
;                    what waits empties every unfailed queue
;   drive-cost       in at most 2n events for n queued actions

(in-package "ACL2")

; ---- the state --------------------------------------------------------------

(defun st-agents (st) (nth 0 st))
(defun st-runq (st) (nth 1 st))
(defun st-running (st) (nth 2 st))
(defun st-holds (st) (nth 3 st))
(defun st-log (st) (nth 4 st))
(defun st-sent (st) (nth 5 st))
(defun st-ticks (st) (nth 6 st))
(defun mk-st (agents runq running holds log sent ticks) (list agents runq running holds log sent ticks))

(defun rec-q (r) (car r))
(defun rec-err (r) (cadr r))
(defun rec-mode (r) (caddr r))
(defun mk-rec (q err mode) (list q err mode))

(defun run-agent (e) (car e))
(defun run-kind (e) (cadr e))
(defun run-left (e) (caddr e))

; an alist with the newest binding first; `put` shadows
(defun put (k v al) (cons (cons k v) al))
(defun get-al (k al) (cdr (assoc-equal k al)))
(defun del (k al)
  (cond ((atom al) nil)
        ((equal (caar al) k) (del k (cdr al)))
        (t (cons (car al) (del k (cdr al))))))

; an action's executor: :pool, or :solo for anything else
(defun act-kind (act) (if (equal (car act) :pool) :pool :solo))

(defun agent-rec (a st) (get-al a (st-agents st)))
(defun agent-q (a st) (rec-q (agent-rec a st)))
(defun agent-err (a st) (rec-err (agent-rec a st)))
(defun agent-known (a st) (consp (assoc-equal a (st-agents st))))
(defun runq-of (key st) (get-al key (st-runq st)))
(defun sent-of (a st) (get-al a (st-sent st)))

; the agents on every run queue, in one list, and the agents running
(defun queued-agents (runq)
  (if (atom runq) nil (append (cdar runq) (queued-agents (cdr runq)))))
(defun running-agents (running)
  (if (atom running) nil (cons (run-agent (cdar running)) (running-agents (cdr running)))))
(defun count-kind (kind running)
  (cond ((atom running) 0)
        ((equal (run-kind (cdar running)) kind) (1+ (count-kind kind (cdr running))))
        (t (count-kind kind (cdr running)))))

; everything with a queue or a worker, in one list
(defun inflight-list (st)
  (append (queued-agents (st-runq st)) (running-agents (st-running st))))
(defun inflight (a st) (member-equal a (inflight-list st)))

; the state is abstract from here: one lemma per accessor, and the
; constructors closed, so every proof speaks in the same terms
(defthm st-agents-mk (equal (st-agents (mk-st a q r h l s tk)) a))
(defthm st-runq-mk (equal (st-runq (mk-st a q r h l s tk)) q))
(defthm st-running-mk (equal (st-running (mk-st a q r h l s tk)) r))
(defthm st-holds-mk (equal (st-holds (mk-st a q r h l s tk)) h))
(defthm st-log-mk (equal (st-log (mk-st a q r h l s tk)) l))
(defthm st-sent-mk (equal (st-sent (mk-st a q r h l s tk)) s))
(defthm st-ticks-mk (equal (st-ticks (mk-st a q r h l s tk)) tk))
(defthm rec-q-mk (equal (rec-q (mk-rec q e m)) q))
(defthm rec-err-mk (equal (rec-err (mk-rec q e m)) e))
(defthm rec-mode-mk (equal (rec-mode (mk-rec q e m)) m))
(defthm run-agent-list (equal (run-agent (list a k l)) a))
(defthm run-kind-list (equal (run-kind (list a k l)) k))
(defthm run-left-list (equal (run-left (list a k l)) l))
(defthm get-al-put (equal (get-al k (put k2 v al)) (if (equal k k2) v (get-al k al))))
(defthm assoc-put (equal (assoc-equal k (put k2 v al)) (if (equal k k2) (cons k2 v) (assoc-equal k al))))
(defthm strip-cars-put (equal (strip-cars (put k v al)) (cons k (strip-cars al))))
(defthm alistp-put (equal (alistp (put k v al)) (alistp al)))
(defthm running-agents-put (equal (running-agents (put w e r)) (cons (run-agent e) (running-agents r))))
(defthm count-kind-put
  (equal (count-kind kind (put w e r)) (+ (if (equal (run-kind e) kind) 1 0) (count-kind kind r))))
(defthm del-put-self (equal (del w (put w e r)) (del w r)))
(in-theory (disable st-agents st-runq st-running st-holds st-log st-sent st-ticks mk-st
                    rec-q rec-err rec-mode mk-rec run-agent run-kind run-left put))

; ---- the machine ------------------------------------------------------------

; a run queue is REPLACED, never shadowed: the queues are enumerated
(defun set-al (k v al) (cons (cons k v) (del k al)))
(defun runq-push (key a runq) (set-al key (append (get-al key runq) (list a)) runq))

; where an idle agent goes when it gets work: :solo by its action's
; kind; the queue of the worker that made it runnable (a release), or
; :global from anywhere else
(defun home (from act st)
  (cond ((equal (act-kind act) :solo) :solo)
        ((and from (assoc-equal from (st-running st))) from)
        (t :global)))

; Agent.enqueue: the action behind the queue; if the queue was empty the
; agent goes to a run queue. A failed or unknown agent refuses
; (Agent.dispatch throws; nothing is sent).
(defun enqueue (from a act st)
  (let ((r (agent-rec a st)))
    (if (or (not (agent-known a st)) (rec-err r))
        st
      (mk-st (set-al a (mk-rec (append (rec-q r) (list act)) nil (rec-mode r)) (st-agents st))
             (if (atom (rec-q r)) (runq-push (home from act st) a (st-runq st)) (st-runq st))
             (st-running st) (st-holds st) (st-log st)
             (put a (append (sent-of a st) (list act)) (st-sent st))
             (st-ticks st)))))

; Agent.releasePendingSends: each held send queued, in order, from the
; releasing worker (or transaction)
(defun enqueue-all (from sends st)
  (if (atom sends) st (enqueue-all from (cdr sends) (enqueue from (caar sends) (cdar sends) st))))

(defun held (h st) (and h (assoc-equal h (st-holds st))))

(defun send-ev (h a act st)
  (if (held h st)
      (mk-st (st-agents st) (st-runq st) (st-running st)
             (put h (append (get-al h (st-holds st)) (list (cons a act))) (st-holds st))
             (st-log st) (st-sent st) (st-ticks st))
    (enqueue h a act st)))

(defun worker-id (w) (and w (not (equal w :global)) (not (equal w :solo))))

; a free pool worker takes a head: :global's when its period is up or
; its own queue is empty, else its own
(defun take-ev (w k b n st)
  (let* ((own (runq-of w st))
         (global (runq-of :global st))
         (tick (nfix (get-al w (st-ticks st))))
         (from-global (and (consp global) (or (atom own) (>= tick (nfix n)))))
         (key (if from-global :global w))
         (waiting (runq-of key st)))
    (if (and (worker-id w) (consp waiting)
             (not (assoc-equal w (st-running st)))
             (< (count-kind :pool (st-running st)) (nfix k)))
        (mk-st (st-agents st)
               (set-al key (cdr waiting) (st-runq st))
               (put w (list (car waiting) :pool (nfix b)) (st-running st))
               (put w nil (st-holds st))
               (st-log st) (st-sent st)
               (put w (if from-global 0 (1+ tick)) (st-ticks st)))
      st)))

; a free solo worker takes :solo's head, with no batch cap
(defun take-solo-ev (w st)
  (let ((waiting (runq-of :solo st)))
    (if (and (worker-id w) (consp waiting) (not (assoc-equal w (st-running st))))
        (mk-st (st-agents st)
               (set-al :solo (cdr waiting) (st-runq st))
               (put w (list (car waiting) :solo nil) (st-running st))
               (put w nil (st-holds st))
               (st-log st) (st-sent st) (st-ticks st))
      st)))

; the first half, rounded up, of a victim's queue moves to an idle
; worker's empty queue
(defun half-len (xs) (if (atom xs) 0 (if (atom (cdr xs)) 1 (1+ (half-len (cddr xs))))))
(defun half (xs) (take (half-len xs) xs))
(defun steal-ev (w v st)
  (let ((victim (runq-of v st)))
    (if (and (worker-id w) (worker-id v) (not (equal w v))
             (atom (runq-of w st)) (consp victim)
             (not (assoc-equal w (st-running st))))
        (mk-st (st-agents st)
               (set-al w (half victim) (set-al v (nthcdr (half-len victim) victim) (st-runq st)))
               (st-running st) (st-holds st) (st-log st) (st-sent st) (st-ticks st))
      st)))

; Agent.Action.doRun's end: the held sends released if the action
; succeeded (the agent is still the worker's, so a send to itself queues
; behind the head), then the head popped with the error decided; the
; agent stays with the worker if its batch allows and it has more,
; otherwise the worker is freed and the agent goes to the back of the
; worker's queue (or of :solo) if unfailed with more to do.
(defun finish-core (w ok st)
  (let* ((e (assoc-equal w (st-running st)))
         (a (run-agent (cdr e))))
    (if (and e (consp (agent-q a st)))
        (let* ((r (agent-rec a st))
               (head (car (rec-q r)))
               (rest (cdr (rec-q r)))
               (err (and (not ok) (equal (rec-mode r) :fail)))
               (kind (run-kind (cdr e)))
               (left (run-left (cdr e)))
               (more (and (not err) (consp rest)))
               ; the next action goes where ITS executor is: a worker keeps the
               ; agent only for its own kind, within its batch
               (nk (and more (act-kind (car rest))))
               (stay (and more (equal nk kind) (or (null left) (> left 1)))))
          (mk-st (set-al a (mk-rec rest err (rec-mode r)) (st-agents st))
                 (if (and more (not stay))
                     (runq-push (cond ((equal nk :solo) :solo) ((equal kind :solo) :global) (t w)) a (st-runq st))
                   (st-runq st))
                 (if stay
                     (put w (list a kind (and left (1- left))) (del w (st-running st)))
                   (del w (st-running st)))
                 (if stay (put w nil (del w (st-holds st))) (del w (st-holds st)))
                 (append (st-log st) (list (cons a head)))
                 (st-sent st) (st-ticks st)))
      st)))

(defun finish-ev (w ok st)
  (if (assoc-equal w (st-running st))
      (finish-core w ok (if ok (enqueue-all w (get-al w (st-holds st)) st) st))
    st))

; Agent.restart: a failed agent cleared of its error and, with
; clear-actions, of its queue; otherwise it goes back out, to :global
(defun restart-ev (a clear st)
  (let ((r (agent-rec a st)))
    (if (or (not (agent-known a st)) (not (rec-err r)))
        st
      (if clear
          (mk-st (set-al a (mk-rec nil nil (rec-mode r)) (st-agents st))
                 (st-runq st) (st-running st) (st-holds st) (st-log st)
                 (put a (take (- (len (sent-of a st)) (len (rec-q r))) (sent-of a st)) (st-sent st))
                 (st-ticks st))
        (mk-st (set-al a (mk-rec (rec-q r) nil (rec-mode r)) (st-agents st))
               (if (consp (rec-q r)) (runq-push (home nil (car (rec-q r)) st) a (st-runq st)) (st-runq st))
               (st-running st) (st-holds st) (st-log st) (st-sent st) (st-ticks st))))))

(defun new-ev (a mode st)
  (if (agent-known a st)
      st
    (mk-st (set-al a (mk-rec nil nil mode) (st-agents st))
           (st-runq st) (st-running st) (st-holds st) (st-log st)
           (put a nil (st-sent st)) (st-ticks st))))

(defun tx-ev (h st)
  (if (or (not h) (held h st) (assoc-equal h (st-running st)))
      st
    (mk-st (st-agents st) (st-runq st) (st-running st) (put h nil (st-holds st)) (st-log st) (st-sent st) (st-ticks st))))

(defun commit-ev (h st)
  (if (and (held h st) (not (assoc-equal h (st-running st))))
      (let ((st1 (enqueue-all nil (get-al h (st-holds st)) st)))
        (mk-st (st-agents st1) (st-runq st1) (st-running st1) (del h (st-holds st1)) (st-log st1) (st-sent st1) (st-ticks st1)))
    st))

(defun abort-ev (h st)
  (if (and (held h st) (not (assoc-equal h (st-running st))))
      (mk-st (st-agents st) (st-runq st) (st-running st) (del h (st-holds st)) (st-log st) (st-sent st) (st-ticks st))
    st))

(defun agents-step (ev k b n st)
  (case (car ev)
    (:new (new-ev (cadr ev) (caddr ev) st))
    (:send (send-ev (cadr ev) (caddr ev) (cadddr ev) st))
    (:take (take-ev (cadr ev) k b n st))
    (:take-solo (take-solo-ev (cadr ev) st))
    (:steal (steal-ev (cadr ev) (caddr ev) st))
    (:finish (finish-ev (cadr ev) (caddr ev) st))
    (:restart (restart-ev (cadr ev) (caddr ev) st))
    (:tx (tx-ev (cadr ev) st))
    (:commit (commit-ev (cadr ev) st))
    (:abort (abort-ev (cadr ev) st))
    (otherwise st)))

(defun agents-run (evs k b n st)
  (if (atom evs) st (agents-run (cdr evs) k b n (agents-step (car evs) k b n st))))

(defun agents-start () (mk-st nil nil nil nil nil nil nil))

; ---- the invariant ----------------------------------------------------------

; the actions the log has for a, in order
(defun done-of (a log)
  (cond ((atom log) nil)
        ((equal (caar log) a) (cons (cdar log) (done-of a (cdr log))))
        (t (done-of a (cdr log)))))

; how many PLACES an agent is in: its occurrences over every run queue
; and every worker. The invariant is one place at most, and exactly one
; when the agent is unfailed with work -- counted, so each event is a
; local sum, whichever queue it touches.
(defun occ (a xs)
  (cond ((atom xs) 0)
        ((equal (car xs) a) (1+ (occ a (cdr xs))))
        (t (occ a (cdr xs)))))
(defun places-q (a runq)
  (if (atom runq) 0 (+ (occ a (cdar runq)) (places-q a (cdr runq)))))
(defun places-r (a running)
  (if (atom running) 0 (+ (if (equal (run-agent (cdar running)) a) 1 0) (places-r a (cdr running)))))
(defun places (a st) (+ (places-q a (st-runq st)) (places-r a (st-running st))))

; what holds of one agent
(defun agent-ok (a st)
  (and (<= (places a st) 1)
       (iff (equal (places a st) 1) (and (not (agent-err a st)) (consp (agent-q a st))))
       (true-listp (agent-q a st))
       (equal (sent-of a st) (append (done-of a (st-log st)) (agent-q a st)))))

(defun agents-ok (as st)
  (if (atom as) t (and (agent-ok (car as) st) (agents-ok (cdr as) st))))

(defun all-known (as st)
  (if (atom as) t (and (agent-known (car as) st) (all-known (cdr as) st))))

; every run queue a true list, under one key each
(defun runq-ok (runq)
  (if (atom runq) (null runq) (and (consp (car runq)) (true-listp (cdar runq)) (runq-ok (cdr runq)))))

(defun st-ok (st)
  (and (alistp (st-agents st))
       (no-duplicatesp-equal (strip-cars (st-agents st)))
       (runq-ok (st-runq st))
       (no-duplicatesp-equal (strip-cars (st-runq st)))
       (not (member-equal nil (strip-cars (st-runq st))))
       (alistp (st-running st))
       (no-duplicatesp-equal (strip-cars (st-running st)))
       (not (member-equal nil (strip-cars (st-running st))))
       (all-known (queued-agents (st-runq st)) st)
       (all-known (running-agents (st-running st)) st)
       (all-known (strip-cars (st-log st)) st)
       (agents-ok (strip-cars (st-agents st)) st)))

; ---- list lemmas ------------------------------------------------------------

(defthm append-assoc (equal (append (append x y) z) (append x (append y z))))

(defthm member-append-iff
  (iff (member-equal a (append x y)) (or (member-equal a x) (member-equal a y))))

(defthm take-len-append
  (implies (true-listp x) (equal (take (len x) (append x y)) x)))

(defthm len-append (equal (len (append x y)) (+ (len x) (len y))))
; what restart-agent :clear-actions keeps of the sent ghost: the done part
(defthm take-sub-len
  (implies (and (true-listp x) (equal s (append x y))) (equal (take (- (len s) (len y)) s) x)))

(defthm done-of-append
  (equal (done-of a (append x y)) (append (done-of a x) (done-of a y))))

(defthm done-of-absent
  (implies (not (member-equal a (strip-cars log))) (equal (done-of a log) nil)))

(defthm true-listp-done-of (true-listp (done-of a log)))

(defthm strip-cars-append (equal (strip-cars (append x y)) (append (strip-cars x) (strip-cars y))))

(defthm occ-append (equal (occ a (append x y)) (+ (occ a x) (occ a y))))

(defthm occ-absent (implies (not (member-equal a xs)) (equal (occ a xs) 0)))

(defthm occ-take-nthcdr-sum
  (implies (and (true-listp xs) (<= n (len xs)) (natp n))
           (equal (+ (occ a (take n xs)) (occ a (nthcdr n xs))) (occ a xs)))
  :rule-classes nil)
; as a rewrite: the taken part is the whole less the rest
(defthm occ-take-nthcdr
  (implies (and (true-listp xs) (<= n (len xs)) (natp n))
           (equal (occ a (take n xs)) (- (occ a xs) (occ a (nthcdr n xs)))))
  :hints (("Goal" :use occ-take-nthcdr-sum)))

(defthm member-take
  (implies (and (<= n (len xs)) (natp n) (member-equal b (take n xs))) (member-equal b xs)))
(defthm nthcdr-nil (equal (nthcdr n nil) nil))
(defthm member-nthcdr (implies (member-equal b (nthcdr n xs)) (member-equal b xs)))

(defthm true-listp-take-le (implies (and (true-listp xs) (<= n (len xs)) (natp n)) (true-listp (take n xs))))
(defthm true-listp-nthcdr (implies (true-listp xs) (true-listp (nthcdr n xs))))

(defthm half-len-le (<= (half-len xs) (len xs)) :rule-classes :linear
  :hints (("Goal" :induct (half-len xs))))
(defthm half-len-natp (natp (half-len xs)) :rule-classes :type-prescription)

; ---- alists and del ---------------------------------------------------------

(defthm alistp-del (implies (alistp al) (alistp (del w al))))
(defthm strip-cars-del (equal (strip-cars (del w al)) (remove-equal w (strip-cars al))))
(defthm member-remove-equal-sub
  (implies (not (member-equal b x)) (not (member-equal b (remove-equal w x)))))
(defthm no-dup-remove-equal
  (implies (no-duplicatesp-equal x) (no-duplicatesp-equal (remove-equal w x))))
(defthm assoc-absent-strip-cars
  (implies (not (member-equal w (strip-cars al))) (not (assoc-equal w al))))
(defthm del-absent (implies (and (alistp al) (not (assoc-equal w al))) (equal (del w al) al)))
(defthm assoc-member-strip-cars (implies (assoc-equal a al) (member-equal a (strip-cars al))))
(defthm not-member-strip-cars-alistp
  (implies (and (alistp al) (not (assoc-equal a al))) (not (member-equal a (strip-cars al)))))
(defthm not-member-remove-self (not (member-equal w (remove-equal w x))))

(defthm runq-ok-alistp (implies (runq-ok runq) (alistp runq)))
(defthm no-dup-cons-remove
  (implies (no-duplicatesp-equal keys) (no-duplicatesp-equal (cons a (remove-equal a keys)))))
; every key a queue or a worker is filed under is a real one
(defthm home-non-nil (home from act st))
(defthm assoc-key-non-nil
  (implies (and (not (member-equal nil (strip-cars al))) (assoc-equal w al)) w)
  :rule-classes :forward-chaining)
(defthm runq-ok-del (implies (runq-ok runq) (runq-ok (del k runq))))
(defthm runq-ok-get (implies (runq-ok runq) (true-listp (get-al k runq))))
(defthm true-listp-cdr (implies (true-listp x) (true-listp (cdr x))))

; ---- places over the queues -------------------------------------------------

; the places on the queues split at any key, when keys are unique
(defthm places-q-del
  (implies (and (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)))
           (equal (places-q a runq) (+ (occ a (get-al k runq)) (places-q a (del k runq)))))
  :rule-classes nil)

(defthm places-q-set-al
  (equal (places-q a (set-al k v runq)) (+ (occ a v) (places-q a (del k runq)))))

(defthm places-q-absent
  (implies (not (member-equal a (queued-agents runq))) (equal (places-q a runq) 0)))

(defthm places-r-del
  (implies (and (alistp running) (no-duplicatesp-equal (strip-cars running)) (assoc-equal w running))
           (equal (places-r a running)
                  (+ (if (equal (run-agent (cdr (assoc-equal w running))) a) 1 0) (places-r a (del w running)))))
  :rule-classes nil)

(defthm places-r-absent
  (implies (not (member-equal a (running-agents running))) (equal (places-r a running) 0)))

(defthm places-r-natp (natp (places-r a running)) :rule-classes :type-prescription)
(defthm places-q-natp (natp (places-q a runq)) :rule-classes :type-prescription)

; the agents of the queues after a replacement: the new list and the rest
(defthm queued-agents-set-al
  (equal (queued-agents (set-al k v runq)) (append v (queued-agents (del k runq)))))

(defthm member-queued-agents-del
  (implies (member-equal b (queued-agents (del k runq))) (member-equal b (queued-agents runq))))

(defthm member-queued-agents-get
  (implies (member-equal b (get-al k runq)) (member-equal b (queued-agents runq))))

(defthm assoc-member-running-agents
  (implies (assoc-equal w r) (member-equal (run-agent (cdr (assoc-equal w r))) (running-agents r)))
  :rule-classes (:rewrite :forward-chaining))

(defthm running-agents-del-sub
  (implies (not (member-equal b (running-agents r))) (not (member-equal b (running-agents (del w r))))))

; ---- known and ok over lists ------------------------------------------------

; the keys after a replacement are the key and the rest: what held of
; the rest still holds
(defthm agents-ok-remove
  (implies (agents-ok keys st) (agents-ok (remove-equal a keys) st)))

(defthm agents-ok-member
  (implies (and (agents-ok as st) (member-equal a as)) (agent-ok a st)))

(defthm all-known-member
  (implies (and (all-known as st) (member-equal a as)) (agent-known a st)))

(defthm all-known-append
  (equal (all-known (append x y) st) (and (all-known x st) (all-known y st))))

(defthm all-known-cdr (implies (all-known x st) (all-known (cdr x) st)))

(defthm agent-known-mk-st
  (equal (agent-known a (mk-st agents runq running holds log sent ticks))
         (consp (assoc-equal a agents))))

; knownness stays opaque from here: the lemmas say when it holds
(in-theory (disable agent-known))

(defthm all-known-queued-del
  (implies (all-known (queued-agents runq) st) (all-known (queued-agents (del k runq)) st)))
(defthm all-known-get
  (implies (all-known (queued-agents runq) st) (all-known (get-al k runq) st)))
(defthm all-known-take
  (implies (and (all-known xs st) (<= n (len xs)) (natp n)) (all-known (take n xs) st)))
(defthm all-known-nthcdr
  (implies (all-known xs st) (all-known (nthcdr n xs) st)))
(defthm all-known-running-del
  (implies (all-known (running-agents r) st) (all-known (running-agents (del w r)) st)))

; knownness carries to a state with the same agents, or more
(defthm assoc-set-al
  (equal (assoc-equal k (set-al k2 v al)) (if (equal k k2) (cons k2 v) (assoc-equal k (del k2 al))))
  :hints (("Goal" :in-theory (enable set-al))))
(defthm assoc-del-other (implies (not (equal w v)) (equal (assoc-equal w (del v al)) (assoc-equal w al))))
(defthm alistp-set-al (implies (alistp al) (alistp (set-al k v al))) :hints (("Goal" :in-theory (enable set-al))))
(defthm all-known-put-any
  (implies (all-known as st)
           (all-known as (mk-st (set-al a rec (st-agents st)) rq r h l s tk)))
  :hints (("Goal" :in-theory (enable agent-known))))
(defthm all-known-same-agents
  (implies (all-known as st)
           (all-known as (mk-st (st-agents st) rq r h l s tk)))
  :hints (("Goal" :in-theory (enable agent-known))))
(defthm agent-known-put-any
  (implies (agent-known b st)
           (agent-known b (mk-st (set-al a rec (st-agents st)) rq r h l s tk)))
  :hints (("Goal" :in-theory (enable agent-known))))
(defthm agent-known-same-agents
  (implies (agent-known b st)
           (agent-known b (mk-st (st-agents st) rq r h l s tk)))
  :hints (("Goal" :in-theory (enable agent-known))))
(defthm agent-known-put-self
  (agent-known a (mk-st (set-al a rec agents) rq r h l s tk))
  :hints (("Goal" :in-theory (enable agent-known))))
(defthm not-member-unknown
  (implies (and (all-known l st) (not (agent-known a st))) (not (member-equal a l))))
(defthm unknown-not-key
  (implies (and (alistp (st-agents st)) (not (agent-known a st))) (not (member-equal a (strip-cars (st-agents st)))))
  :hints (("Goal" :in-theory (enable agent-known))))
(defthm known-is-key
  (implies (agent-known a st) (member-equal a (strip-cars (st-agents st))))
  :hints (("Goal" :in-theory (enable agent-known))))

; ---- the steps: enqueue -----------------------------------------------------

(defthm strip-cars-set-al (equal (strip-cars (set-al k v al)) (cons k (remove-equal k (strip-cars al)))))
(defthm runq-ok-set-al (implies (and (runq-ok runq) (true-listp v)) (runq-ok (set-al k v runq))))
(defthm get-al-set-al (equal (get-al k (set-al k2 v al)) (if (equal k k2) v (get-al k (del k2 al)))))
(defthm get-al-del-other (implies (not (equal k k2)) (equal (get-al k (del k2 al)) (get-al k al))))
(defthm get-al-del-self (equal (get-al k (del k al)) nil))
(defthm get-al-nil (equal (get-al k nil) nil))
(defthm get-al-absent (implies (not (assoc-equal k al)) (equal (get-al k al) nil)))
; lookups stay in get-al form from here, so the queue lemmas match
(in-theory (disable get-al))

(defthm places-q-push-other
  (implies (and (not (equal b a)) (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)))
           (equal (places-q b (runq-push key a runq)) (places-q b runq)))
  :hints (("Goal" :use ((:instance places-q-del (a b) (k key))))))

(defthm places-q-push-self
  (implies (and (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)))
           (equal (places-q a (runq-push key a runq)) (1+ (places-q a runq))))
  :hints (("Goal" :use ((:instance places-q-del (k key))))))

(in-theory (disable set-al runq-push places-q-set-al))

(defthm runq-ok-push (implies (runq-ok runq) (runq-ok (runq-push key a runq)))
  :hints (("Goal" :in-theory (enable runq-push))))
(defthm no-dup-keys-push
  (implies (no-duplicatesp-equal (strip-cars runq)) (no-duplicatesp-equal (strip-cars (runq-push key a runq))))
  :hints (("Goal" :in-theory (enable runq-push))))
(defthm strip-cars-push
  (equal (strip-cars (runq-push key a runq)) (cons key (remove-equal key (strip-cars runq))))
  :hints (("Goal" :in-theory (enable runq-push))))
(defthm all-known-queued-push
  (implies (and (all-known (queued-agents runq) st) (agent-known a st))
           (all-known (queued-agents (runq-push key a runq)) st))
  :hints (("Goal" :in-theory (enable runq-push set-al))))

(defthm agent-ok-enqueue-other
  (implies (and (not (equal b a)) (runq-ok (st-runq st)) (no-duplicatesp-equal (strip-cars (st-runq st))))
           (equal (agent-ok b (enqueue from a act st)) (agent-ok b st))))

(defthm agents-ok-enqueue
  (implies (and (agents-ok keys st) (agent-ok a (enqueue from a act st))
                (runq-ok (st-runq st)) (no-duplicatesp-equal (strip-cars (st-runq st))))
           (agents-ok keys (enqueue from a act st)))
  :hints (("Goal" :induct (agents-ok keys st) :in-theory (disable enqueue agent-ok))
          ("Subgoal *1/2''" :cases ((equal (car keys) a)))))

(defthm agent-ok-enqueue-self
  (implies (and (st-ok st) (agent-known a st) (not (agent-err a st)))
           (agent-ok a (enqueue from a act st)))
  :hints (("Goal" :use ((:instance agents-ok-member (as (strip-cars (st-agents st)))))
                  :in-theory (e/d (agent-known) (agents-ok-member)))))

; enqueue's components, so the invariant is checked one part at a time
(defthm enqueue-noop
  (implies (or (not (agent-known a st)) (agent-err a st)) (equal (enqueue from a act st) st)))
(defthm st-agents-enqueue
  (implies (and (agent-known a st) (not (agent-err a st)))
           (equal (st-agents (enqueue from a act st))
                  (set-al a (mk-rec (append (agent-q a st) (list act)) nil (rec-mode (agent-rec a st))) (st-agents st)))))
(defthm st-runq-enqueue
  (implies (and (agent-known a st) (not (agent-err a st)))
           (equal (st-runq (enqueue from a act st))
                  (if (atom (agent-q a st)) (runq-push (home from act st) a (st-runq st)) (st-runq st)))))
(defthm st-log-enqueue (equal (st-log (enqueue from a act st)) (st-log st)))
(defthm st-running-enqueue (equal (st-running (enqueue from a act st)) (st-running st)))
(defthm st-holds-enqueue (equal (st-holds (enqueue from a act st)) (st-holds st)))
(defthm st-ticks-enqueue (equal (st-ticks (enqueue from a act st)) (st-ticks st)))

(in-theory (disable enqueue))

(defthm all-known-enqueue
  (implies (all-known as st) (all-known as (enqueue from a act st)))
  :hints (("Goal" :in-theory (enable enqueue))))
(defthm agent-known-enqueue
  (implies (agent-known b st) (agent-known b (enqueue from a act st)))
  :hints (("Goal" :in-theory (enable enqueue agent-known))))

(defthm st-ok-enqueue
  (implies (st-ok st) (st-ok (enqueue from a act st)))
  :hints (("Goal" :cases ((and (agent-known a st) (not (agent-err a st))))
                  :use (agent-ok-enqueue-self)
                  :in-theory (disable agent-ok-enqueue-self agent-ok))))

(defthm st-ok-enqueue-all
  (implies (st-ok st) (st-ok (enqueue-all from sends st)))
  :hints (("Goal" :in-theory (disable st-ok))))

(defthm st-running-enqueue-all (equal (st-running (enqueue-all from sends st)) (st-running st)))
(defthm st-holds-enqueue-all (equal (st-holds (enqueue-all from sends st)) (st-holds st)))
(defthm st-ticks-enqueue-all (equal (st-ticks (enqueue-all from sends st)) (st-ticks st)))

; ---- the steps: take, take-solo, steal --------------------------------------

(defthm occ-consp
  (implies (consp xs) (equal (occ a xs) (+ (if (equal (car xs) a) 1 0) (occ a (cdr xs))))))

; a take moves one agent from a queue to a worker: every count stays
(defthm places-q-take
  (implies (and (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)) (consp (get-al key runq)))
           (equal (places-q c (set-al key (cdr (get-al key runq)) runq))
                  (- (places-q c runq) (if (equal (car (get-al key runq)) c) 1 0))))
  :hints (("Goal" :in-theory (enable places-q-set-al) :use ((:instance places-q-del (a c) (k key))))))

(defthm places-r-put
  (equal (places-r c (put w e running)) (+ (if (equal (run-agent e) c) 1 0) (places-r c running)))
  :hints (("Goal" :in-theory (enable put))))

(defthm places-r-assoc
  (implies (and (alistp running) (assoc-equal w running))
           (<= 1 (places-r (run-agent (cdr (assoc-equal w running))) running)))
  :rule-classes :linear)

(defthm places-take-ev
  (implies (st-ok st) (equal (places c (take-ev w k b n st)) (places c st))))

(defthm agent-ok-take-ev
  (implies (st-ok st) (equal (agent-ok c (take-ev w k b n st)) (agent-ok c st)))
  :hints (("Goal" :in-theory (disable places-take-ev) :use places-take-ev)))

(defthm agents-ok-take-ev
  (implies (and (st-ok st) (agents-ok keys st)) (agents-ok keys (take-ev w k b n st)))
  :hints (("Goal" :induct (agents-ok keys st) :in-theory (disable take-ev agent-ok st-ok))))

(defthm all-known-queued-take
  (implies (all-known (queued-agents runq) st)
           (all-known (queued-agents (set-al key (cdr (get-al key runq)) runq)) st))
  :hints (("Goal" :in-theory (enable set-al))))

(defthm car-get-known
  (implies (and (all-known (queued-agents runq) st) (consp (get-al key runq)))
           (agent-known (car (get-al key runq)) st))
  :hints (("Goal" :use ((:instance all-known-member (as (get-al key runq)) (a (car (get-al key runq)))))
                  :in-theory (disable all-known-member))))

(defthm st-ok-take-ev
  (implies (st-ok st) (st-ok (take-ev w k b n st)))
  :hints (("Goal" :in-theory (disable agent-ok agents-ok-take-ev) :use ((:instance agents-ok-take-ev (keys (strip-cars (st-agents st))))))))

(defthm places-take-solo-ev
  (implies (st-ok st) (equal (places c (take-solo-ev w st)) (places c st))))

(defthm agent-ok-take-solo-ev
  (implies (st-ok st) (equal (agent-ok c (take-solo-ev w st)) (agent-ok c st)))
  :hints (("Goal" :in-theory (disable places-take-solo-ev) :use places-take-solo-ev)))

(defthm agents-ok-take-solo-ev
  (implies (and (st-ok st) (agents-ok keys st)) (agents-ok keys (take-solo-ev w st)))
  :hints (("Goal" :induct (agents-ok keys st) :in-theory (disable take-solo-ev agent-ok st-ok))))

(defthm st-ok-take-solo-ev
  (implies (st-ok st) (st-ok (take-solo-ev w st)))
  :hints (("Goal" :in-theory (disable agent-ok agents-ok-take-solo-ev) :use ((:instance agents-ok-take-solo-ev (keys (strip-cars (st-agents st))))))))

; a steal moves half a queue to an empty one: every count stays
(defthm del-del (equal (del w (del v al)) (del v (del w al))))
(defthm del-set-al-other
  (implies (not (equal w v)) (equal (del w (set-al v x al)) (set-al v x (del w al))))
  :hints (("Goal" :in-theory (enable set-al))))
(defthm no-dup-keys-del
  (implies (no-duplicatesp-equal (strip-cars al)) (no-duplicatesp-equal (strip-cars (del w al)))))

(defthm places-q-steal
  (implies (and (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)) (not (equal w v))
                (atom (get-al w runq)) (<= h (len (get-al v runq))) (natp h))
           (equal (places-q c (set-al w (take h (get-al v runq)) (set-al v (nthcdr h (get-al v runq)) runq)))
                  (places-q c runq)))
  :hints (("Goal" :in-theory (enable places-q-set-al)
                  :use ((:instance places-q-del (a c) (k w))
                        (:instance places-q-del (a c) (k v) (runq (del w runq)))
                        (:instance occ-take-nthcdr-sum (a c) (n h) (xs (get-al v runq)))))))

(defthm places-steal-ev
  (implies (st-ok st) (equal (places c (steal-ev w v st)) (places c st)))
  :hints (("Goal" :use ((:instance places-q-steal (runq (st-runq st)) (h (half-len (get-al v (st-runq st)))))))))

(defthm agent-ok-steal-ev
  (implies (st-ok st) (equal (agent-ok c (steal-ev w v st)) (agent-ok c st)))
  :hints (("Goal" :in-theory (disable places-steal-ev) :use places-steal-ev)))

(defthm agents-ok-steal-ev
  (implies (and (st-ok st) (agents-ok keys st)) (agents-ok keys (steal-ev w v st)))
  :hints (("Goal" :induct (agents-ok keys st) :in-theory (disable steal-ev agent-ok st-ok))))

(defthm all-known-queued-steal
  (implies (and (all-known (queued-agents runq) st) (runq-ok runq) (<= h (len (get-al v runq))) (natp h))
           (all-known (queued-agents (set-al w (take h (get-al v runq)) (set-al v (nthcdr h (get-al v runq)) runq))) st))
  :hints (("Goal" :in-theory (enable set-al))))

(defthm st-ok-steal-ev
  (implies (st-ok st) (st-ok (steal-ev w v st)))
  :hints (("Goal" :in-theory (disable agent-ok agents-ok-steal-ev) :use ((:instance agents-ok-steal-ev (keys (strip-cars (st-agents st))))))))

; ---- the steps: finish ------------------------------------------------------

(defthm places-r-del-self
  (implies (and (alistp running) (no-duplicatesp-equal (strip-cars running)) (assoc-equal w running))
           (equal (places-r (run-agent (cdr (assoc-equal w running))) (del w running))
                  (1- (places-r (run-agent (cdr (assoc-equal w running))) running))))
  :hints (("Goal" :use ((:instance places-r-del (a (run-agent (cdr (assoc-equal w running)))))))))

(defthm places-r-del-other
  (implies (and (alistp running) (no-duplicatesp-equal (strip-cars running)) (assoc-equal w running)
                (not (equal c (run-agent (cdr (assoc-equal w running))))))
           (equal (places-r c (del w running)) (places-r c running)))
  :hints (("Goal" :use ((:instance places-r-del (a c))))))


; the running agent is known, and so one place exactly, unfailed, with work
(defthm running-agent-facts
  (implies (and (st-ok st) (assoc-equal w (st-running st)))
           (let ((a (run-agent (cdr (assoc-equal w (st-running st))))))
             (and (agent-known a st)
                  (equal (places a st) 1)
                  (not (agent-err a st))
                  (consp (agent-q a st))
                  (true-listp (agent-q a st))
                  (equal (sent-of a st) (append (done-of a (st-log st)) (agent-q a st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable agents-ok-member all-known-member)
                  :use ((:instance all-known-member (as (running-agents (st-running st)))
                                   (a (run-agent (cdr (assoc-equal w (st-running st))))))
                        (:instance agents-ok-member (as (strip-cars (st-agents st)))
                                   (a (run-agent (cdr (assoc-equal w (st-running st))))))))))

(defthm list-car-when-single
  (implies (and (true-listp q) (consp q) (not (cdr q))) (equal (cons (car q) nil) q)))

(defthm done-of-single
  (equal (done-of c (list (cons a head))) (if (equal c a) (list head) nil)))

(defthm agent-ok-finish-core-other
  (implies (and (st-ok st) (assoc-equal w (st-running st))
                (not (equal c (run-agent (cdr (assoc-equal w (st-running st)))))))
           (equal (agent-ok c (finish-core w ok st)) (agent-ok c st)))
  :hints (("Goal" :in-theory (disable agents-ok-member all-known-member))))

(defthm agent-ok-finish-core-self
  (implies (and (st-ok st) (assoc-equal w (st-running st)))
           (agent-ok (run-agent (cdr (assoc-equal w (st-running st)))) (finish-core w ok st)))
  :hints (("Goal" :use running-agent-facts
                  :in-theory (disable agents-ok-member all-known-member))))

(defthm agents-ok-finish-core
  (implies (and (st-ok st) (assoc-equal w (st-running st)) (agents-ok keys st))
           (agents-ok keys (finish-core w ok st)))
  :hints (("Goal" :induct (agents-ok keys st)
                  :in-theory (disable finish-core agent-ok st-ok agent-ok-finish-core-self agent-ok-finish-core-other))
          ("Subgoal *1/2" :use (agent-ok-finish-core-self (:instance agent-ok-finish-core-other (c (car keys)))))))

(defthm all-known-running-cons-del
  (implies (and (all-known (running-agents r) st) (agent-known a st))
           (all-known (running-agents (put w (list a kind left) (del w r))) st))
  :hints (("Goal" :in-theory (enable put))))

(defthm st-ok-finish-core
  (implies (st-ok st) (st-ok (finish-core w ok st)))
  :hints (("Goal" :in-theory (disable agent-ok agents-ok-finish-core agents-ok-member all-known-member)
                  :use (running-agent-facts agent-ok-finish-core-self
                        (:instance agents-ok-finish-core (keys (strip-cars (st-agents st))))))))

(in-theory (disable finish-core))

(defthm st-ok-finish-ev
  (implies (st-ok st) (st-ok (finish-ev w ok st)))
  :hints (("Goal" :in-theory (disable st-ok))))

; ---- the steps: restart, new, holds -----------------------------------------

(defthm failed-no-place
  (implies (and (st-ok st) (agent-known a st) (agent-err a st)) (equal (places a st) 0))
  :hints (("Goal" :use ((:instance agents-ok-member (as (strip-cars (st-agents st)))))
                  :in-theory (disable agents-ok-member))))

(defthm agent-ok-restart-other
  (implies (and (st-ok st) (not (equal c a)))
           (equal (agent-ok c (restart-ev a clear st)) (agent-ok c st))))

(defthm agent-ok-restart-self
  (implies (and (st-ok st) (agent-known a st))
           (agent-ok a (restart-ev a clear st)))
  :hints (("Goal" :use (failed-no-place (:instance agents-ok-member (as (strip-cars (st-agents st)))))
                  :in-theory (disable agents-ok-member))))

(defthm agents-ok-restart
  (implies (and (st-ok st) (agent-known a st) (agents-ok keys st))
           (agents-ok keys (restart-ev a clear st)))
  :hints (("Goal" :induct (agents-ok keys st)
                  :in-theory (disable restart-ev agent-ok st-ok agent-ok-restart-self agent-ok-restart-other))
          ("Subgoal *1/2" :use (agent-ok-restart-self (:instance agent-ok-restart-other (c (car keys)))))))

(defthm restart-unknown
  (implies (not (agent-known a st)) (equal (restart-ev a clear st) st))
  :hints (("Goal" :in-theory (enable agent-known))))

(defthm st-ok-restart-ev
  (implies (st-ok st) (st-ok (restart-ev a clear st)))
  :hints (("Goal" :in-theory (disable agent-ok agents-ok-restart agents-ok-member agent-ok-restart-self)
                  :cases ((agent-known a st))
                  :use (agent-ok-restart-self
                        (:instance agents-ok-restart (keys (strip-cars (st-agents st))))
                        (:instance agents-ok-member (as (strip-cars (st-agents st))))))))

(defthm agent-ok-new-other
  (implies (not (equal c a)) (equal (agent-ok c (new-ev a mode st)) (agent-ok c st))))

(defthm agents-ok-new
  (implies (and (agents-ok keys st) (not (member-equal a keys)))
           (agents-ok keys (new-ev a mode st)))
  :hints (("Goal" :induct (agents-ok keys st) :in-theory (disable new-ev agent-ok))))

; a new agent is nowhere and has run nothing
(defthm agent-ok-new-self
  (implies (and (st-ok st) (not (agent-known a st))) (agent-ok a (new-ev a mode st)))
  :hints (("Goal" :use ((:instance not-member-unknown (l (queued-agents (st-runq st))))
                        (:instance not-member-unknown (l (running-agents (st-running st))))
                        (:instance not-member-unknown (l (strip-cars (st-log st)))))
                  :in-theory (disable not-member-unknown))))

(defthm st-ok-new-ev
  (implies (st-ok st) (st-ok (new-ev a mode st)))
  :hints (("Goal" :in-theory (disable agent-ok agents-ok-new agent-ok-new-self)
                  :use (agent-ok-new-self (:instance agents-ok-new (keys (strip-cars (st-agents st))))))))

; holds and ticks are not the invariant's business
(defthm agent-ok-holds
  (equal (agent-ok c (mk-st (st-agents st) (st-runq st) (st-running st) h (st-log st) (st-sent st) tk))
         (agent-ok c st)))
(defthm agents-ok-holds
  (equal (agents-ok keys (mk-st (st-agents st) (st-runq st) (st-running st) h (st-log st) (st-sent st) tk))
         (agents-ok keys st))
  :hints (("Goal" :induct (agents-ok keys st) :in-theory (disable agent-ok))))
(defthm st-ok-holds
  (implies (st-ok st) (st-ok (mk-st (st-agents st) (st-runq st) (st-running st) h (st-log st) (st-sent st) tk)))
  :hints (("Goal" :in-theory (disable agent-ok))))

(defthm st-ok-send-ev
  (implies (st-ok st) (st-ok (send-ev h a act st)))
  :hints (("Goal" :in-theory (disable st-ok))))
(defthm st-ok-tx-ev (implies (st-ok st) (st-ok (tx-ev h st)))
  :hints (("Goal" :in-theory (disable st-ok))))
(defthm st-ok-commit-ev (implies (st-ok st) (st-ok (commit-ev h st)))
  :hints (("Goal" :in-theory (disable st-ok st-ok-holds)
                  :use ((:instance st-ok-holds (st (enqueue-all nil (get-al h (st-holds st)) st))
                                   (h (del h (st-holds st))) (tk (st-ticks st)))))))
(defthm st-ok-abort-ev (implies (st-ok st) (st-ok (abort-ev h st)))
  :hints (("Goal" :in-theory (disable st-ok))))

; ---- every schedule ---------------------------------------------------------

(defthm st-ok-step
  (implies (st-ok st) (st-ok (agents-step ev k b n st)))
  :hints (("Goal" :in-theory (disable st-ok new-ev send-ev take-ev take-solo-ev steal-ev finish-ev
                                      restart-ev tx-ev commit-ev abort-ev))))

(defthm st-ok-run
  (implies (st-ok st) (st-ok (agents-run evs k b n st)))
  :hints (("Goal" :in-theory (disable st-ok agents-step))))

(defthm st-ok-start (st-ok (agents-start)))

(in-theory (disable st-ok agents-step agents-run agents-start))

; ---- the theorems -----------------------------------------------------------

(defthm places-r-two
  (implies (and (alistp r) (no-duplicatesp-equal (strip-cars r)) (assoc-equal w1 r) (assoc-equal w2 r)
                (not (equal w1 w2))
                (equal (run-agent (cdr (assoc-equal w2 r))) (run-agent (cdr (assoc-equal w1 r)))))
           (<= 2 (places-r (run-agent (cdr (assoc-equal w1 r))) r)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance places-r-del (a (run-agent (cdr (assoc-equal w1 r)))) (w w1))
                        (:instance places-r-assoc (w w2) (running (del w1 r)))))))

; NO TWO WORKERS RUN THE SAME AGENT, whatever the schedule
(defthm agents-serial
  (implies (and (assoc-equal w1 (st-running (agents-run evs k b n (agents-start))))
                (assoc-equal w2 (st-running (agents-run evs k b n (agents-start))))
                (not (equal w1 w2)))
           (not (equal (run-agent (cdr (assoc-equal w1 (st-running (agents-run evs k b n (agents-start))))))
                       (run-agent (cdr (assoc-equal w2 (st-running (agents-run evs k b n (agents-start)))))))))
  :hints (("Goal" :use ((:instance running-agent-facts (w w1) (st (agents-run evs k b n (agents-start))))
                        (:instance places-r-two (r (st-running (agents-run evs k b n (agents-start)))))
                        (:instance st-ok-run (st (agents-start))))
                  :in-theory (e/d (st-ok) (st-ok-run)))))

; WHAT WAS SENT IS WHAT RAN, IN ORDER, THEN WHAT WAITS: nothing lost,
; nothing reordered, nothing run twice
(defthm agents-order
  (implies (agent-known a (agents-run evs k b n (agents-start)))
           (equal (sent-of a (agents-run evs k b n (agents-start)))
                  (append (done-of a (st-log (agents-run evs k b n (agents-start))))
                          (agent-q a (agents-run evs k b n (agents-start))))))
  :hints (("Goal" :use ((:instance agents-ok-member (as (strip-cars (st-agents (agents-run evs k b n (agents-start)))))
                                   (st (agents-run evs k b n (agents-start))))
                        (:instance st-ok-run (st (agents-start))))
                  :in-theory (e/d (st-ok) (st-ok-run agents-ok-member)))))

; one agent's invariant, closed, for the theorems below
(defthm agent-ok-facts
  (implies (agent-ok a st)
           (and (<= (places a st) 1)
                (iff (equal (places a st) 1) (and (not (agent-err a st)) (consp (agent-q a st))))
                (true-listp (agent-q a st))
                (equal (sent-of a st) (append (done-of a (st-log st)) (agent-q a st)))))
  :rule-classes nil)

(defthm known-agent-ok
  (implies (and (st-ok st) (agent-known a st)) (agent-ok a st))
  :hints (("Goal" :in-theory (e/d (st-ok) (agents-ok-member))
                  :use ((:instance agents-ok-member (as (strip-cars (st-agents st))))))))

; AN AGENT IS ON ONE QUEUE OR ONE WORKER, EXACTLY WHEN UNFAILED WITH WORK
(defthm agents-head
  (implies (agent-known a (agents-run evs k b n (agents-start)))
           (and (<= (places a (agents-run evs k b n (agents-start))) 1)
                (iff (equal (places a (agents-run evs k b n (agents-start))) 1)
                     (and (not (agent-err a (agents-run evs k b n (agents-start))))
                          (consp (agent-q a (agents-run evs k b n (agents-start))))))))
  :hints (("Goal" :use ((:instance agent-ok-facts (st (agents-run evs k b n (agents-start))))
                        (:instance known-agent-ok (st (agents-run evs k b n (agents-start))))
                        (:instance st-ok-run (st (agents-start))))
                  :in-theory (disable st-ok-run known-agent-ok agent-ok places agent-q agent-err))))

; ---- live: unfailed work means an enabled event -----------------------------

(defthm places-q-pos-queued
  (implies (< 0 (places-q a runq)) (consp (queued-agents runq)))
  :hints (("Goal" :use places-q-absent :in-theory (disable places-q-absent))))
(defthm places-r-pos-running
  (implies (< 0 (places-r a running)) (consp running)))

; UNFAILED WORK QUEUED MEANS A WORKER IS BUSY OR A QUEUE IS NONEMPTY
(defthm agents-live
  (implies (and (st-ok st) (agent-known a st) (not (agent-err a st)) (consp (agent-q a st)))
           (or (consp (st-running st)) (consp (queued-agents (st-runq st)))))
  :rule-classes nil
  :hints (("Goal" :use (agent-ok-facts known-agent-ok)
                  :in-theory (disable known-agent-ok agent-ok))))

; and each of those is an enabled event: a busy worker can finish, and a
; nonempty queue can be taken by the worker its key names, or by any
; free worker for :global and :solo
(defthm st-log-enqueue-all (equal (st-log (enqueue-all from sends st)) (st-log st)))
(defthm st-agents-enqueue-all-q
  (implies (consp (agent-q a st)) (consp (agent-q a (enqueue-all from sends st))))
  :hints (("Goal" :in-theory (enable enqueue))))

(defthm finish-progresses
  (implies (and (st-ok st) (assoc-equal w (st-running st)))
           (equal (len (st-log (finish-ev w ok st))) (1+ (len (st-log st)))))
  :hints (("Goal" :use (running-agent-facts
                        (:instance st-agents-enqueue-all-q (a (run-agent (cdr (assoc-equal w (st-running st)))))
                                   (from w) (sends (get-al w (st-holds st)))))
                  :in-theory (e/d (finish-core) (agent-ok)))))

(defthm take-progresses
  (implies (and (worker-id w) (not (assoc-equal w (st-running st)))
                (< (count-kind :pool (st-running st)) (nfix k))
                (or (consp (runq-of w st)) (consp (runq-of :global st))))
           (assoc-equal w (st-running (take-ev w k b n st)))))

(defthm take-solo-progresses
  (implies (and (worker-id w) (not (assoc-equal w (st-running st))) (consp (runq-of :solo st)))
           (assoc-equal w (st-running (take-solo-ev w st)))))

; the first nonempty queue's key, when any queue is nonempty
(defun busy-key (runq)
  (cond ((atom runq) nil)
        ((consp (cdar runq)) (caar runq))
        (t (busy-key (cdr runq)))))

(defthm busy-key-non-nil
  (implies (and (not (member-equal nil (strip-cars runq))) (consp (get-al (busy-key runq) runq)))
           (busy-key runq))
  :hints (("Goal" :in-theory (enable get-al))))

(defthm busy-key-nonempty
  (implies (and (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)) (consp (queued-agents runq)))
           (consp (get-al (busy-key runq) runq)))
  :hints (("Goal" :in-theory (enable get-al))))

; NOTHING RUNNING AND SOMETHING QUEUED: A TAKE IS ENABLED -- by the
; queue's own worker, or by any free worker w for :global and :solo
(defthm agents-live-take
  (implies (and (st-ok st) (atom (st-running st)) (consp (queued-agents (st-runq st)))
                (posp k) (worker-id w))
           (let ((key (busy-key (st-runq st))))
             (cond ((equal key :solo) (assoc-equal w (st-running (take-solo-ev w st))))
                   ((equal key :global) (assoc-equal w (st-running (take-ev w k b n st))))
                   (t (assoc-equal key (st-running (take-ev key k b n st)))))))
  :hints (("Goal" :in-theory (e/d (st-ok) (take-ev take-solo-ev busy-key busy-key-nonempty))
                  :use ((:instance busy-key-nonempty (runq (st-runq st)))
                        (:instance busy-key-non-nil (runq (st-runq st)))))))

; ---- a steal delays nobody --------------------------------------------------

(defun pos (a xs)
  (cond ((atom xs) 0) ((equal (car xs) a) 0) (t (1+ (pos a (cdr xs))))))

(defthm pos-take
  (implies (and (member-equal a (take n xs)) (<= n (len xs)) (natp n))
           (equal (pos a (take n xs)) (pos a xs))))

(defthm member-occ-pos (implies (member-equal a xs) (< 0 (occ a xs))) :rule-classes :linear)

(defthm pos-nthcdr
  (implies (and (member-equal a (nthcdr n xs)) (not (member-equal a (take n xs))) (<= n (len xs)) (natp n))
           (equal (pos a (nthcdr n xs)) (- (pos a xs) n))))

(defthm occ-le-places-q
  (implies (and (runq-ok runq) (no-duplicatesp-equal (strip-cars runq)))
           (<= (occ a (get-al k runq)) (places-q a runq)))
  :rule-classes :linear
  :hints (("Goal" :use places-q-del)))

; an agent on a queue is on it once
(defthm queue-no-dup
  (implies (and (st-ok st) (agent-known a st) (member-equal a (runq-of k st)))
           (equal (occ a (runq-of k st)) 1))
  :hints (("Goal" :use (agent-ok-facts known-agent-ok (:instance occ-le-places-q (runq (st-runq st))))
                  :in-theory (e/d (st-ok) (known-agent-ok agent-ok occ-le-places-q)))))

(defthm not-in-take-when-in-rest
  (implies (and (true-listp xs) (<= n (len xs)) (natp n) (equal (occ a xs) 1) (member-equal a (nthcdr n xs)))
           (not (member-equal a (take n xs))))
  :hints (("Goal" :use (occ-take-nthcdr-sum (:instance member-occ-pos (xs (nthcdr n xs))) (:instance member-occ-pos (xs (take n xs))))
                  :in-theory (disable occ-take-nthcdr member-occ-pos))))

; A STEAL LEAVES EVERY AGENT NO FURTHER FROM THE FRONT: the moved ones
; keep their position in the thief's empty queue, the ones left behind
; move up by the number taken
(defthm steal-no-delay
  (implies (and (st-ok st) (worker-id w) (worker-id v) (not (equal w v))
                (atom (runq-of w st)) (consp (runq-of v st)) (not (assoc-equal w (st-running st)))
                (agent-known a st))
           (and (implies (member-equal a (runq-of w (steal-ev w v st)))
                         (equal (pos a (runq-of w (steal-ev w v st))) (pos a (runq-of v st))))
                (implies (member-equal a (runq-of v (steal-ev w v st)))
                         (equal (pos a (runq-of v (steal-ev w v st)))
                                (- (pos a (runq-of v st)) (half-len (runq-of v st)))))))
  :hints (("Goal" :in-theory (e/d (st-ok) (agent-ok))
                  :use ((:instance queue-no-dup (k v))
                        (:instance not-in-take-when-in-rest (xs (runq-of v st)) (n (half-len (runq-of v st))))
                        (:instance occ-take-nthcdr-sum (xs (runq-of v st)) (n (half-len (runq-of v st))))))))

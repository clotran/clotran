; clotran's agent scheduler, its cost (PLAN step 24): a step-count bound,
; by counting, as the other books have (CLAUDE.md: every algorithm in
; the model has one). THE DRIVER finishes what runs and takes what
; waits: with a worker busy it finishes that worker's action; with
; nothing running and a queue nonempty it takes from the first nonempty
; queue -- the queue's own worker, or worker 0 for :global and :solo.
; No sends happen while it drives, and no running worker holds a send,
; so every finish pops exactly one action and adds none.
;
;   drive-finishes  from any invariant state whose potential is within
;                   the fuel, the driver reaches a state with nothing
;                   running and nothing queued
;   drive-cost      so from n queued actions (the unfailed agents'
;                   queues, summed) it spends at most 2n events: one
;                   take and one finish per action at the worst, fewer
;                   when a batch lets a worker keep its agent
;
; The potential is 2n less one when a worker is busy: a finish pays one
; action (two) and may free a worker (one back), a take pays nothing
; and makes a worker busy (one), so every driver event costs at least
; one, and the potential is positive while anything is left to do.

(in-package "ACL2")

(include-book "agents")

; the unfailed work: every agent's queued actions, summed over the table
(defun work-al (agents)
  (cond ((atom agents) 0)
        ((rec-err (cdar agents)) (work-al (cdr agents)))
        (t (+ (len (rec-q (cdar agents))) (work-al (cdr agents))))))
(defun total-work (st) (work-al (st-agents st)))

; no running worker holds a send
(defun no-held (running holds)
  (if (atom running) t (and (atom (get-al (caar running) holds)) (no-held (cdr running) holds))))

(defun pick (st)
  (cond ((consp (st-running st)) (list :finish (caar (st-running st)) t))
        ((consp (queued-agents (st-runq st)))
         (let ((key (busy-key (st-runq st))))
           (cond ((equal key :solo) (list :take-solo 0))
                 ((equal key :global) (list :take 0))
                 (t (list :take key)))))
        (t nil)))

(defun drive (st k b n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (null (pick st)))
      st
    (drive (agents-step (pick st) k b n st) k b n (1- fuel))))

(defun potential (st) (- (* 2 (total-work st)) (if (consp (st-running st)) 1 0)))

; ---- the work, split at any agent ---------------------------------------------

(defthm len-pos-consp (implies (consp x) (< 0 (len x))) :rule-classes :linear)
(defthm work-al-natp (natp (work-al agents)) :rule-classes :type-prescription)

(defthm work-al-del
  (implies (and (alistp agents) (no-duplicatesp-equal (strip-cars agents)))
           (equal (work-al agents)
                  (+ (if (rec-err (get-al a agents)) 0 (len (rec-q (get-al a agents))))
                     (work-al (del a agents)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable get-al))))

(defthm work-al-set-al
  (equal (work-al (set-al a rec agents))
         (+ (if (rec-err rec) 0 (len (rec-q rec))) (work-al (del a agents))))
  :hints (("Goal" :in-theory (enable set-al))))

(defthm rec-nil (and (equal (rec-err nil) nil) (equal (rec-q nil) nil) (equal (rec-dead nil) nil))
  :hints (("Goal" :in-theory (enable rec-err rec-q))))

; an unfailed agent with work makes the work positive
(defthm work-al-pos
  (implies (and (alistp (st-agents st)) (no-duplicatesp-equal (strip-cars (st-agents st)))
                (not (agent-err a st)) (consp (agent-q a st)))
           (<= 1 (total-work st)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance work-al-del (agents (st-agents st)))))))

; ---- the events the driver picks ----------------------------------------------

(defthm enqueue-all-nil (equal (enqueue-all from nil st) st))

(defthm no-held-get
  (implies (and (no-held running holds) (assoc-equal w running)) (atom (get-al w holds))))

; a finish with nothing held pops one action: the work is one less
(defthm total-work-finish
  (implies (and (st-ok st) (assoc-equal w (st-running st)) (atom (get-al w (st-holds st))))
           (equal (total-work (finish-ev w t st)) (1- (total-work st))))
  :hints (("Goal" :use (running-agent-facts
                        (:instance work-al-del (agents (st-agents st))
                                   (a (run-agent (cdr (assoc-equal w (st-running st)))))))
                  :in-theory (e/d (finish-core st-ok) (agent-ok)))))

(defthm st-agents-take-ev (equal (st-agents (take-ev w k b n st)) (st-agents st)))
(defthm st-agents-take-solo-ev (equal (st-agents (take-solo-ev w st)) (st-agents st)))
(defthm total-work-take-ev (equal (total-work (take-ev w k b n st)) (total-work st)))
(defthm total-work-take-solo-ev (equal (total-work (take-solo-ev w st)) (total-work st)))

; no running worker holds a send, after a take or a finish
(defthm no-held-other-holds
  (implies (and (no-held running holds) (alistp running) (not (assoc-equal w running)))
           (no-held running (put w nil holds))))
(defthm no-held-del-holds
  (implies (and (no-held running holds) (alistp running) (not (assoc-equal w running)))
           (no-held running (del w holds))))
(defthm no-held-del-running
  (implies (and (no-held running holds) (alistp running) (no-duplicatesp-equal (strip-cars running)))
           (no-held (del w running) (del w holds))))
(defthm no-held-holds-put-nil
  (implies (no-held running holds) (no-held running (put w nil holds))))
(defthm no-held-put-running
  (equal (no-held (put w e running) holds) (and (atom (get-al w holds)) (no-held running holds)))
  :hints (("Goal" :in-theory (enable put))))
(defthm no-held-put-nil
  (implies (no-held running holds) (no-held (put w e running) (put w nil holds))))

(defthm no-held-take-ev
  (implies (no-held (st-running st) (st-holds st))
           (no-held (st-running (take-ev w k b n st)) (st-holds (take-ev w k b n st)))))
(defthm no-held-take-solo-ev
  (implies (no-held (st-running st) (st-holds st))
           (no-held (st-running (take-solo-ev w st)) (st-holds (take-solo-ev w st)))))
(defthm no-held-finish-ev
  (implies (and (st-ok st) (no-held (st-running st) (st-holds st)) (assoc-equal w (st-running st)))
           (no-held (st-running (finish-ev w t st)) (st-holds (finish-ev w t st))))
  :hints (("Goal" :use (running-agent-facts)
                  :in-theory (e/d (finish-core st-ok) (agent-ok)))))

; ---- the potential falls by one or more at every driver event --------------------

(defthm st-ok-no-dup-keys
  (implies (st-ok st) (and (alistp (st-agents st)) (no-duplicatesp-equal (strip-cars (st-agents st)))
                           (alistp (st-running st)) (no-duplicatesp-equal (strip-cars (st-running st)))
                           (not (member-equal nil (strip-cars (st-running st))))))
  :hints (("Goal" :in-theory (enable st-ok))))
(defthm assoc-caar (implies (and (consp al) (alistp al)) (assoc-equal (caar al) al)))
(defthm caar-non-nil
  (implies (and (consp al) (alistp al) (not (member-equal nil (strip-cars al)))) (caar al))
  :rule-classes :forward-chaining)

(defthm potential-finish
  (implies (and (st-ok st) (no-held (st-running st) (st-holds st)) (consp (st-running st)))
           (<= (potential (finish-ev (caar (st-running st)) t st)) (1- (potential st))))
  :hints (("Goal" :in-theory (disable finish-ev)
                  :use ((:instance total-work-finish (w (caar (st-running st))))))))

; the queued agent at the front of the busy queue has work, so the
; potential is at least two with nothing running
(defthm queued-has-work
  (implies (and (st-ok st) (atom (st-running st)) (consp (queued-agents (st-runq st))))
           (<= 1 (total-work st)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance busy-key-nonempty (runq (st-runq st)))
                        (:instance known-agent-ok (a (car (get-al (busy-key (st-runq st)) (st-runq st)))))
                        (:instance agent-ok-facts (a (car (get-al (busy-key (st-runq st)) (st-runq st)))))
                        (:instance car-get-known (runq (st-runq st)) (key (busy-key (st-runq st))))
                        (:instance occ-le-places-q (runq (st-runq st)) (k (busy-key (st-runq st)))
                                   (a (car (get-al (busy-key (st-runq st)) (st-runq st)))))
                        (:instance work-al-pos (a (car (get-al (busy-key (st-runq st)) (st-runq st))))))
                  :in-theory (e/d (st-ok) (known-agent-ok agent-ok busy-key-nonempty car-get-known
                                           occ-le-places-q work-al-pos)))))

(defthm running-has-work
  (implies (and (st-ok st) (consp (st-running st)))
           (<= 1 (total-work st)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance running-agent-facts (w (caar (st-running st))))
                        (:instance work-al-pos (a (run-agent (cdr (assoc-equal (caar (st-running st)) (st-running st)))))))
                  :in-theory (e/d (st-ok) (agent-ok work-al-pos)))))

(defthm potential-take
  (implies (and (st-ok st) (atom (st-running st)) (consp (queued-agents (st-runq st))) (posp k))
           (let ((key (busy-key (st-runq st))))
             (<= (potential (cond ((equal key :solo) (take-solo-ev 0 st))
                                  ((equal key :global) (take-ev 0 k b n st))
                                  (t (take-ev key k b n st))))
                 (1- (potential st)))))
  :hints (("Goal" :use ((:instance agents-live-take (w 0)))
                  :in-theory (disable take-ev take-solo-ev agents-live-take busy-key))))

(defthm pick-step-potential
  (implies (and (st-ok st) (no-held (st-running st) (st-holds st)) (posp k) (pick st))
           (<= (potential (agents-step (pick st) k b n st)) (1- (potential st))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (agents-step) (potential take-ev take-solo-ev finish-ev busy-key))
                  :use (potential-finish potential-take))))

(defthm pick-step-no-held
  (implies (and (st-ok st) (no-held (st-running st) (st-holds st)) (posp k) (pick st))
           (let ((st2 (agents-step (pick st) k b n st)))
             (no-held (st-running st2) (st-holds st2))))
  :hints (("Goal" :in-theory (e/d (agents-step) (take-ev take-solo-ev finish-ev busy-key)))))

(defthm potential-positive
  (implies (and (st-ok st) (pick st)) (<= 1 (potential st)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable busy-key total-work running-has-work queued-has-work)
                  :use (running-has-work queued-has-work))))

; ---- the theorems ---------------------------------------------------------------

; THE DRIVER FINISHES: with fuel for the potential it reaches a state
; with nothing running and nothing queued
(defthm drive-finishes
  (implies (and (st-ok st) (no-held (st-running st) (st-holds st)) (posp k)
                (<= (potential st) (nfix fuel)))
           (null (pick (drive st k b n fuel))))
  :hints (("Goal" :induct (drive st k b n fuel)
                  :in-theory (disable potential pick st-ok-step agents-step))
          ("Subgoal *1/2" :use (pick-step-potential pick-step-no-held potential-positive
                                (:instance st-ok-step (ev (pick st)))))))

; AND SPENDS AT MOST 2n EVENTS for n queued actions: every driver event
; is a take or a finish, and the potential they pay for is at most 2n
(defthm drive-cost
  (implies (and (st-ok st) (no-held (st-running st) (st-holds st)) (posp k))
           (null (pick (drive st k b n (* 2 (total-work st))))))
  :hints (("Goal" :use ((:instance drive-finishes (fuel (* 2 (total-work st)))))
                  :in-theory (disable drive-finishes drive pick))))

; AND COSTS NOTHING TO DRIVE: a send after shutdown-agents adds no work, so
; drive-cost's bound of 2n events is the work queued before it
(defthm total-work-enqueue-after-shutdown
  (implies (and (st-ok st) (shut st)) (equal (total-work (enqueue from a act st)) (total-work st)))
  :hints (("Goal" :in-theory (enable enqueue st-ok)
                  :cases ((agent-known a st))
                  :use ((:instance work-al-del (agents (st-agents st)))))))

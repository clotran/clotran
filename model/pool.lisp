; clotran's execution pool, formally (PLAN step 32). Tasks are data and
; their work is a pure function; contexts -- local threads, SSH hosts,
; Slurm jobs, Kubernetes pods -- are named slots that each run one task
; at a time. Contexts fail: a task they hold can be lost (a node dies,
; Slurm kills the job, a heartbeat times out), and it goes back to the
; queue to run again elsewhere. A task thought lost may still finish,
; late, so its answer can arrive twice.
;
; THE STATE is (pending inflight results):
;   pending   task ids not yet running, in order
;   inflight  (ctx . id) for each busy context
;   results   (id . value), newest first
; THE EVENTS, in any order and any mix of contexts:
;   (:dispatch c)  a free context c takes the next pending task
;   (:done c)      c's task finishes; its value is recorded, c is free
;   (:lost c)      c's task is lost; it is queued again, c is free
;   (:late i)      task i's answer arrives from a run thought lost
;
; THE THEOREMS hold for every schedule, so for every mix of contexts and
; every pattern of failures:
;   pool-sound     every recorded value is the task's work
;   pool-keeps     no task is ever dropped: each is pending, running or done
;   pool-correct   a run that empties the queue and the contexts has
;                  every task's value, the same map a local run makes
;   drive-finishes the round-robin scheduler finishes n tasks over k
;                  contexts once its outcomes hold n successes
;   drive-cost     in at most 2(n + f) events, f the losses

(in-package "ACL2")

; the work, any pure function: nothing below assumes what it computes
(defstub work (*) => *)

(defun input-of (i inputs) (cdr (assoc-equal i inputs)))

(defun ctx-task (c inflight) (assoc-equal c inflight))

(defun free (c inflight)
  (cond ((atom inflight) nil)
        ((equal (caar inflight) c) (free c (cdr inflight)))
        (t (cons (car inflight) (free c (cdr inflight))))))

(defun pool-step (ev inputs st)
  (let ((pending (car st)) (inflight (cadr st)) (results (caddr st))
        (c (cadr ev)))
    (case (car ev)
      (:dispatch (if (and (consp pending) (not (ctx-task c inflight)))
                     (list (cdr pending) (cons (cons c (car pending)) inflight) results)
                   st))
      (:done (let ((e (ctx-task c inflight)))
               (if e
                   (list pending (free c inflight)
                         (cons (cons (cdr e) (work (input-of (cdr e) inputs))) results))
                 st)))
      (:lost (let ((e (ctx-task c inflight)))
               (if e
                   (list (append pending (list (cdr e))) (free c inflight) results)
                 st)))
      (:late (if (assoc-equal c inputs)
                 (list pending inflight (cons (cons c (work (input-of c inputs))) results))
               st))
      (otherwise st))))

(defun pool-run (evs inputs st)
  (if (atom evs) st (pool-run (cdr evs) inputs (pool-step (car evs) inputs st))))

(defun pool-start (inputs) (list (strip-cars inputs) nil nil))

; ---- SOUND: every recorded value is right --------------------------------------------

(defun results-ok (results inputs)
  (if (atom results)
      t
    (and (consp (car results))
         (assoc-equal (caar results) inputs)
         (equal (cdar results) (work (input-of (caar results) inputs)))
         (results-ok (cdr results) inputs))))

(defun ids-ok (ids inputs)
  (if (atom ids) t (and (assoc-equal (car ids) inputs) (ids-ok (cdr ids) inputs))))

(defun inflight-ok (inflight inputs)
  (if (atom inflight)
      (null inflight)
    (and (consp (car inflight)) (assoc-equal (cdar inflight) inputs) (inflight-ok (cdr inflight) inputs))))

; a context runs one task at a time
(defun st-ok (st inputs)
  (and (true-listp (car st)) (ids-ok (car st) inputs) (inflight-ok (cadr st) inputs)
       (no-duplicatesp-equal (strip-cars (cadr st)))
       (results-ok (caddr st) inputs)))

(defthm inflight-ok-alistp (implies (inflight-ok f inputs) (alistp f)))

(defthm member-strip-cars-free (not (member-equal c (strip-cars (free c f)))))

(defthm member-strip-cars-free-other
  (implies (not (member-equal d (strip-cars f))) (not (member-equal d (strip-cars (free c f))))))

(defthm no-dup-free
  (implies (no-duplicatesp-equal (strip-cars f)) (no-duplicatesp-equal (strip-cars (free c f)))))

(defthm assoc-iff-member-strip-cars
  (implies (alistp f) (iff (assoc-equal c f) (member-equal c (strip-cars f)))))

(defthm ids-ok-append
  (equal (ids-ok (append a b) inputs) (and (ids-ok a inputs) (ids-ok b inputs))))

(defthm inflight-ok-free (implies (inflight-ok f inputs) (inflight-ok (free c f) inputs)))

(defthm inflight-ok-task
  (implies (and (inflight-ok f inputs) (assoc-equal c f)) (assoc-equal (cdr (assoc-equal c f)) inputs)))

(defthm st-ok-step
  (implies (st-ok st inputs) (st-ok (pool-step ev inputs st) inputs)))

(defthm st-ok-run
  (implies (st-ok st inputs) (st-ok (pool-run evs inputs st) inputs)))

(defthm ids-ok-strip-cars
  (implies (alistp inputs) (ids-ok (strip-cars inputs) inputs)))

(defthm st-ok-start (implies (alistp inputs) (st-ok (pool-start inputs) inputs)))

(defthm results-ok-assoc
  (implies (and (results-ok results inputs) (assoc-equal i results))
           (equal (cdr (assoc-equal i results)) (work (input-of i inputs)))))

; EVERY RECORDED VALUE IS THE TASK'S WORK, whatever the schedule
(defthm pool-sound
  (implies (and (alistp inputs) (assoc-equal i (caddr (pool-run evs inputs (pool-start inputs)))))
           (equal (cdr (assoc-equal i (caddr (pool-run evs inputs (pool-start inputs)))))
                  (work (input-of i inputs))))
  :hints (("Goal" :in-theory (disable pool-run st-ok-run results-ok-assoc)
                  :use ((:instance st-ok-run (st (pool-start inputs)))
                        (:instance results-ok-assoc (results (caddr (pool-run evs inputs (pool-start inputs)))))))))

; ---- KEPT: no task is ever dropped ----------------------------------------------------

(defun has-task (i st)
  (or (member-equal i (car st)) (rassoc-equal i (cadr st)) (assoc-equal i (caddr st))))

(defthm free-absent
  (implies (and (alistp f) (not (member-equal c (strip-cars f)))) (equal (free c f) f)))

(defthm rassoc-free
  (implies (and (rassoc-equal i f) (not (equal (cdr (assoc-equal c f)) i))
                (alistp f) (no-duplicatesp-equal (strip-cars f)))
           (rassoc-equal i (free c f))))

(defthm rassoc-assoc
  (implies (and (assoc-equal c f) (alistp f)) (rassoc-equal (cdr (assoc-equal c f)) f)))

(defthm member-append
  (iff (member-equal i (append a b)) (or (member-equal i a) (member-equal i b))))

(defthm has-task-step
  (implies (and (has-task i st) (st-ok st inputs)) (has-task i (pool-step ev inputs st)))
  :hints (("Goal" :in-theory (disable st-ok-step))))

(defthm has-task-run
  (implies (and (has-task i st) (st-ok st inputs)) (has-task i (pool-run evs inputs st)))
  :hints (("Goal" :induct (pool-run evs inputs st) :in-theory (disable has-task st-ok pool-step))))

; NO TASK IS DROPPED: each is pending, running, or done, whatever is lost
(defthm pool-keeps
  (implies (and (alistp inputs) (assoc-equal i inputs)) (has-task i (pool-run evs inputs (pool-start inputs))))
  :hints (("Goal" :in-theory (disable has-task-run)
                  :use ((:instance has-task-run (st (pool-start inputs)))))))

; ---- CORRECT: a finished run is the local map -----------------------------------------

(defun local-map (ids inputs)
  (if (atom ids) nil (cons (cons (car ids) (work (input-of (car ids) inputs))) (local-map (cdr ids) inputs))))

(defun pool-answer (ids results)
  (if (atom ids) nil (cons (cons (car ids) (cdr (assoc-equal (car ids) results))) (pool-answer (cdr ids) results))))

(defun finished (st) (and (atom (car st)) (atom (cadr st))))

(defun all-have (ids st) (if (atom ids) t (and (has-task (car ids) st) (all-have (cdr ids) st))))

(defthm all-have-run
  (implies (and (all-have ids st) (st-ok st inputs)) (all-have ids (pool-run evs inputs st)))
  :hints (("Goal" :induct (all-have ids st) :in-theory (disable has-task pool-run))))

(defthm all-have-start
  (implies (subsetp-equal ids (strip-cars inputs)) (all-have ids (pool-start inputs))))

(defthm subsetp-cons (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
(defthm subsetp-refl (subsetp-equal x x))

; finished, each id is done, and its value is its work
(defthm pool-answer-local
  (implies (and (finished st) (results-ok (caddr st) inputs) (all-have ids st))
           (equal (pool-answer ids (caddr st)) (local-map ids inputs))))

; A RUN THAT FINISHES ANSWERS THE LOCAL MAP, whatever mix of contexts ran it and whatever was lost
(defthm pool-correct
  (implies (and (alistp inputs) (finished (pool-run evs inputs (pool-start inputs))))
           (equal (pool-answer (strip-cars inputs) (caddr (pool-run evs inputs (pool-start inputs))))
                  (local-map (strip-cars inputs) inputs)))
  :hints (("Goal" :in-theory (disable pool-run pool-answer-local all-have-run st-ok-run pool-start finished
                                      st-ok-start all-have-start)
                  :do-not-induct t
                  :use ((:instance st-ok-start)
                        (:instance pool-answer-local (st (pool-run evs inputs (pool-start inputs))) (ids (strip-cars inputs)))
                        (:instance all-have-run (st (pool-start inputs)) (ids (strip-cars inputs)))
                        (:instance st-ok-run (st (pool-start inputs)))
                        (:instance all-have-start (ids (strip-cars inputs)))))))

; ---- LIVE: a scheduler that finishes, and what it costs --------------------------------
;
; The round-robin scheduler: the next context takes the next task, and
; the run's outcome says whether it finished or was lost -- outs is the
; sequence of outcomes, t done and nil lost, chosen by the world, not
; by us. Each outcome is two events.

(defun drive-evs (ctxs outs)
  (if (atom outs)
      nil
    (let ((c (car ctxs)))
      (list* (list :dispatch c) (list (if (car outs) :done :lost) c)
             (drive-evs (append (cdr ctxs) (list c)) (cdr outs))))))

(defun count-ok (outs) (if (atom outs) 0 (+ (if (car outs) 1 0) (count-ok (cdr outs)))))

(defthm drive-idle
  (equal (pool-run (drive-evs ctxs outs) inputs (list nil nil r)) (list nil nil r))
  :hints (("Goal" :induct (drive-evs ctxs outs))))

(defthm len-append-one (equal (len (append a (list x))) (+ 1 (len a))))

(defun drive-ind (ctxs outs p r inputs)
  (if (atom outs)
      (list ctxs p r inputs)
    (let ((c (car ctxs)))
      (if (atom p)
          nil
        (drive-ind (append (cdr ctxs) (list c)) (cdr outs)
                   (if (car outs) (cdr p) (append (cdr p) (list (car p))))
                   (if (car outs) (cons (cons (car p) (work (input-of (car p) inputs))) r) r)
                   inputs)))))

; WITH AS MANY SUCCESSES AS TASKS, THE SCHEDULER FINISHES, however many
; losses come between them, over any contexts
(defthm drive-finishes
  (implies (and (true-listp p) (<= (len p) (count-ok outs)))
           (finished (pool-run (drive-evs ctxs outs) inputs (list p nil r))))
  :hints (("Goal" :induct (drive-ind ctxs outs p r inputs))))

; IN TWO EVENTS AN OUTCOME: n tasks and f losses cost 2(n + f)
(defthm drive-cost
  (equal (len (drive-evs ctxs outs)) (* 2 (len outs))))

(defthm len-strip-cars (equal (len (strip-cars a)) (len a)))
(defthm true-listp-strip-cars (true-listp (strip-cars a)))

; AND WHAT IT FINISHES IS THE LOCAL MAP
(defthm drive-correct
  (implies (and (alistp inputs) (<= (len inputs) (count-ok outs)))
           (equal (pool-answer (strip-cars inputs) (caddr (pool-run (drive-evs ctxs outs) inputs (pool-start inputs))))
                  (local-map (strip-cars inputs) inputs)))
  :hints (("Goal" :in-theory (disable pool-correct drive-finishes pool-run drive-evs) :do-not-induct t
                  :use ((:instance pool-correct (evs (drive-evs ctxs outs)))
                        (:instance drive-finishes (p (strip-cars inputs)) (r nil))))))

; ---- A RUN, as a check -----------------------------------------------------------------
;
; work is a stub, so a concrete run uses a concrete function: square,
; over four windows on a laptop thread and a Slurm job. The job loses
; window b, which runs again on the laptop; the lost run then finishes
; late, and its answer arrives a second time -- the same value.

(defun sq-step (ev inputs st)
  (let ((pending (car st)) (inflight (cadr st)) (results (caddr st)) (c (cadr ev)))
    (case (car ev)
      (:dispatch (if (and (consp pending) (not (assoc-equal c inflight)))
                     (list (cdr pending) (cons (cons c (car pending)) inflight) results) st))
      (:done (let ((e (assoc-equal c inflight)))
               (if e (list pending (free c inflight)
                           (cons (cons (cdr e) (* (fix (input-of (cdr e) inputs)) (fix (input-of (cdr e) inputs)))) results))
                 st)))
      (:lost (let ((e (assoc-equal c inflight)))
               (if e (list (append pending (list (cdr e))) (free c inflight) results) st)))
      (:late (if (assoc-equal c inputs)
                 (list pending inflight (cons (cons c (* (fix (input-of c inputs)) (fix (input-of c inputs)))) results))
               st))
      (otherwise st))))

(defun sq-run (evs inputs st) (if (atom evs) st (sq-run (cdr evs) inputs (sq-step (car evs) inputs st))))

(assert-event
 (let* ((inputs '((a . 1) (b . 2) (c . 3) (d . 4)))
        (st (sq-run '((:dispatch :laptop) (:dispatch :slurm) (:done :laptop) (:lost :slurm)
                      (:dispatch :laptop) (:dispatch :slurm) (:done :slurm) (:done :laptop)
                      (:dispatch :slurm) (:late b) (:done :slurm))
                    inputs (pool-start inputs))))
   (and (finished st)
        (equal (pool-answer '(a b c d) (caddr st)) '((a . 1) (b . 4) (c . 9) (d . 16))))))

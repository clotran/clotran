; The main thread's mailbox, formally (PLAN step 37; src/f/Threads.f90,
; th_main_*). The program runs on a thread of its own; the process's
; first thread SERVES: a C function handed to it (fortran/main-thread*)
; runs there -- a window system's event loop, which macOS allows nowhere
; else. One slot; the program posts, the main thread takes and runs.
;
; THE STATE is (slot running ended serving accepted ran):
;   slot      the function posted and not yet started, or nil
;   running   the function the main thread is running, or nil
;   ended     the program has ended (th_main_ended)
;   serving   the main thread still serves (th_main_serve has not returned)
;   accepted  every function a post accepted, in order (ghost)
;   ran       every function the main thread finished, in order (ghost)
;
; THE STEPS, each one atomic under the mailbox's lock:
;   (:post f)  the program: accepted when serving, not ended, the slot empty
;   (:end)     the program has ended
;   (:take)    main: the slot's function started
;   (:finish)  main: it returned
;   (:stop)    main: ended, nothing in the slot, nothing running -- serving ends
; A schedule is any list of steps, so the theorems hold under every
; interleaving of the two threads.
;
; And clotran-ui's half (native/clotran_ui.c, on_main): a program thread
; that needs the loop to do something queues a JOB (uiQueueMain) and
; waits; the loop runs queued jobs in order. A libui-ng callback -- draw,
; mouse, key -- never calls into the evaluator: it pushes an event, which
; never waits, so the main thread never waits on the program thread and
; no cycle of waits can form (the evaluator waiting on a job while the
; main thread waits on the evaluator).

(in-package "ACL2")

(defun mb (slot running ended serving accepted ran)
  (list slot running ended serving accepted ran))
(defun mb-slot (st) (nth 0 st))
(defun mb-running (st) (nth 1 st))
(defun mb-ended (st) (nth 2 st))
(defun mb-serving (st) (nth 3 st))
(defun mb-accepted (st) (nth 4 st))
(defun mb-ran (st) (nth 5 st))

(defun mb-step (s st)
  (let ((slot (mb-slot st)) (running (mb-running st)) (ended (mb-ended st))
        (serving (mb-serving st)) (acc (mb-accepted st)) (ran (mb-ran st)))
    (case (car s)
      (:post (if (and serving (not ended) (not slot) (cadr s))
                 (mb (cadr s) running ended serving (append acc (list (cadr s))) ran)
               st))
      (:end (mb slot running t serving acc ran))
      (:take (if (and serving slot (not running)) (mb nil slot ended serving acc ran) st))
      (:finish (if running (mb slot nil ended serving acc (append ran (list running))) st))
      (:stop (if (and serving ended (not slot) (not running)) (mb slot running ended nil acc ran) st))
      (otherwise st))))

(defun mb-run (sched st)
  (if (atom sched) st (mb-run (cdr sched) (mb-step (car sched) st))))

(defun mb-start () (mb nil nil nil t nil nil))

; THE INVARIANT: what was accepted is what ran, then what runs, then what
; waits in the slot -- each accepted function exactly once, in order; and
; a mailbox no longer serving holds nothing
(defun mb-inv (st)
  (and (equal (mb-accepted st)
              (append (mb-ran st)
                      (if (mb-running st) (list (mb-running st)) nil)
                      (if (mb-slot st) (list (mb-slot st)) nil)))
       (implies (not (mb-serving st)) (and (not (mb-slot st)) (not (mb-running st))))
       (true-listp (mb-ran st))))

(defthm mb-inv-start (mb-inv (mb-start)))

(defthm append-assoc-mb
  (equal (append (append a b) c) (append a (append b c))))

(defthm mb-inv-step
  (implies (mb-inv st) (mb-inv (mb-step s st))))

(in-theory (disable mb-step mb-inv))

(defthm mb-inv-run
  (implies (mb-inv st) (mb-inv (mb-run sched st))))

; ---- THE THEOREMS, under every schedule ----------------------------------------

; NO LOST AND NO DOUBLED WORK: once the main thread stops serving, it has
; run every accepted function, each exactly once, in the order accepted
(defthm stopped-ran-all
  (let ((st (mb-run sched (mb-start))))
    (implies (not (mb-serving st))
             (equal (mb-ran st) (mb-accepted st))))
  :hints (("Goal" :use ((:instance mb-inv-run (st (mb-start))))
                  :in-theory (e/d (mb-inv) (mb-inv-run)))))

; THE MAIN THREAD NEVER WAITS ON THE PROGRAM but for work: while it serves
; with a function in the slot, one running, or the program ended, its
; next step (finish, else take, else stop) changes the state. It waits
; only when the slot is empty, nothing runs and the program goes on --
; waiting for a post, which the program never waits on in turn.
(defun mb-main-step (st)
  (cond ((mb-running st) (mb-step '(:finish) st))
        ((mb-slot st) (mb-step '(:take) st))
        (t (mb-step '(:stop) st))))

(defthm main-moves
  (implies (and (mb-inv st) (mb-serving st)
                (or (mb-slot st) (mb-running st) (mb-ended st)))
           (not (equal (mb-main-step st) st)))
  :hints (("Goal" :in-theory (enable mb-step mb-inv))))

; COST: once the program has ended, the main thread stops within 4 of its
; own steps (finish what runs, take and finish what waits, stop) -- the
; slot holds at most one, and posts are refused after the end.
(defun mb-main-n (n st)
  (if (zp n) st (mb-main-n (1- n) (mb-main-step st))))

; the work left: 1 to stop, 1 more to finish what runs, 2 for what waits
(defun mb-pot (st)
  (if (mb-serving st) (+ 1 (if (mb-running st) 1 0) (if (mb-slot st) 2 0)) 0))

(defthm main-step-ended
  (implies (mb-ended st) (mb-ended (mb-main-step st)))
  :hints (("Goal" :in-theory (enable mb-step))))

(defthm main-step-inv
  (implies (mb-inv st) (mb-inv (mb-main-step st))))

(defthm main-step-pot
  (implies (and (mb-inv st) (mb-ended st) (mb-serving st))
           (< (mb-pot (mb-main-step st)) (mb-pot st)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable mb-step mb-inv))))

(defthm pot-0-stopped
  (implies (equal (mb-pot st) 0) (not (mb-serving st))))

(defthm pot-stopped
  (implies (not (mb-serving st)) (equal (mb-pot st) 0)))

(defthm pot-serving
  (implies (mb-serving st) (< 0 (mb-pot st)))
  :rule-classes :linear)

(defthm main-step-stopped
  (implies (and (mb-inv st) (not (mb-serving st))) (not (mb-serving (mb-main-step st))))
  :hints (("Goal" :in-theory (enable mb-step mb-inv))))

(defthm pot-step-stopped
  (implies (and (mb-inv st) (not (mb-serving st))) (equal (mb-pot (mb-main-step st)) 0))
  :hints (("Goal" :in-theory (disable mb-pot mb-main-step))))

(in-theory (disable mb-slot mb-running mb-ended mb-serving mb-pot mb-main-step))

(defthm ended-stops-within-pot
  (implies (and (mb-inv st) (mb-ended st) (natp n) (<= (mb-pot st) n))
           (not (mb-serving (mb-main-n n st))))
  :hints (("Goal" :induct (mb-main-n n st)) ("Subgoal *1/2" :cases ((mb-serving st)))))

(defthm pot-at-most-4 (<= (mb-pot st) 4) :rule-classes :linear
  :hints (("Goal" :in-theory (enable mb-pot))))

(defthm ended-stops-in-4
  (implies (and (mb-inv st) (mb-ended st))
           (not (mb-serving (mb-main-n 4 st))))
  :hints (("Goal" :in-theory (disable mb-main-n mb-pot))))

; ---- clotran-ui's jobs: on_main ----------------------------------------------

; The loop's queue of jobs, oldest first; one loop step runs the oldest.
(defun jobs-step (q done) (if (consp q) (mv (cdr q) (append done (list (car q)))) (mv q done)))

(defun jobs-n (n q done)
  (if (zp n) (mv q done)
    (mv-let (q2 d2) (jobs-step q done) (jobs-n (1- n) q2 d2))))

; COST: a job k places from the queue's head is done within k + 1 steps of
; the loop -- the waiting program thread is woken after that many, whatever
; the callbacks did meanwhile, since a callback only pushes an event.
(defthm member-append-list
  (implies (member-equal j done) (member-equal j (append done x))))

(defun job-ind (k q done)
  (if (zp k) (list q done) (job-ind (1- k) (cdr q) (append done (list (car q))))))

(defthm jobs-n-unfold
  (implies (and (consp q) (natp k))
           (equal (jobs-n (1+ k) q done) (jobs-n k (cdr q) (append done (list (car q)))))))

(defthm job-done-in-k+1
  (implies (and (natp k) (< k (len q)))
           (member-equal (nth k q) (mv-nth 1 (jobs-n (1+ k) q done))))
  :hints (("Goal" :induct (job-ind k q done))))

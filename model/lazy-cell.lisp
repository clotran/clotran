; clotran's lazy cells, formally (PLAN step 30, the runtime). A lazy
; seq's cell is realised once: the first thread to force it runs its
; thunk, the others wait for the answer. Today a global mutex guards the
; claim and the settle; the design here claims the cell by ONE atomic
; compare-and-swap on its state, so no lock is taken to force a cell
; nobody else is forcing -- once per element of every lazy seq.
;
; THE CELL is one of
;   (:pending)          its thunk not yet run
;   (:running t)        thread t is running it
;   (:realised v)       its value v, for ever
; and a thrown thunk puts it back to :pending, as clotran does (an
; exception in flight must not cache an empty cell).
;
; THE THREADS each have a program counter:
;   :idle      not forcing
;   :claimed   won the CAS, running the thunk
;   :waiting   saw another thread's :running, waits
;   (:done v)  forced, and read v
; One step is one thread's ATOMIC action, and a schedule is any list of
; thread ids, so the theorems hold under every interleaving.

(in-package "ACL2")

; ---- the machine -------------------------------------------------------------

; a thread's pc, :idle when it has none
(defun pc-of (tid pcs) (let ((e (assoc-equal tid pcs))) (if e (cdr e) :idle)))
(defun set-pc (tid pc pcs) (cons (cons tid pc) pcs))

; one atomic step of thread tid; v is the value its thunk would answer,
; and throws whether this run of it throws
(defun step-thread (tid v throws st)
  (let* ((cell (car st)) (pcs (cdr st)) (pc (pc-of tid pcs)))
    (cond
     ;; start forcing: realised is a plain read; pending is the CAS,
     ;; pending -> running tid in one step; running by another, wait;
     ;; running by tid itself is a recursive force, which is the owner's
     ;; own business (re-entrant, as clj's synchronized LazySeq)
     ((or (eq pc :idle) (eq pc :waiting))
      (cond ((eq (car cell) :realised) (cons cell (set-pc tid (list :done (cadr cell)) pcs)))
            ((eq (car cell) :pending) (cons (list :running tid) (set-pc tid :claimed pcs)))
            ((equal (cadr cell) tid) st)
            (t (cons cell (set-pc tid :waiting pcs)))))
     ;; the thunk finished: settle, or give the cell back on a throw --
     ;; a plain store, since only the owner can be here
     ((eq pc :claimed)
      (if throws
          (cons (list :pending) (set-pc tid :idle pcs))
        (cons (list :realised v) (set-pc tid (list :done v) pcs))))
     (t st))))

; a schedule: each entry (tid v throws)
(defun run-sched (sched st)
  (if (atom sched)
      st
    (run-sched (cdr sched)
               (step-thread (car (car sched)) (cadr (car sched)) (caddr (car sched)) st))))

; ---- what must stay true ------------------------------------------------------

(defthm pc-of-set-pc
  (equal (pc-of a (set-pc tid pc pcs)) (if (equal a tid) pc (pc-of a pcs))))
(in-theory (disable pc-of set-pc))

; every thread mid-thunk owns the running cell, and every thread that
; finished read the realised value
(defun-sk all-ok (cell pcs)
  (forall a (and (implies (eq (pc-of a pcs) :claimed)
                          (and (eq (car cell) :running) (equal (cadr cell) a)))
                 (implies (and (consp (pc-of a pcs)) (eq (car (pc-of a pcs)) :done))
                          (and (eq (car cell) :realised)
                               (equal (cadr (pc-of a pcs)) (cadr cell)))))))

; THE INVARIANT: that, and a running cell's owner is mid-thunk
(defun inv (st)
  (let ((cell (car st)) (pcs (cdr st)))
    (and (consp cell)
         (member-equal (car cell) '(:pending :running :realised))
         (implies (eq (car cell) :running) (eq (pc-of (cadr cell) pcs) :claimed))
         (all-ok cell pcs))))

(defun start-state () (cons (list :pending) nil))

; nobody has started: every thread idle
(defthm all-ok-start (all-ok (quote (:pending)) nil)
  :hints (("Goal" :in-theory (enable pc-of))))

(defthm inv-start (inv (start-state))
  :hints (("Goal" :in-theory (enable pc-of))))

(defthm inv-step
  (implies (inv st) (inv (step-thread tid v throws st)))
  :hints (("Goal" :use ((:instance all-ok-necc (cell (car st)) (pcs (cdr st))
                                   (a (all-ok-witness (car (step-thread tid v throws st))
                                                      (cdr (step-thread tid v throws st)))))
                        (:instance all-ok-necc (cell (car st)) (pcs (cdr st)) (a tid)))
                  :expand ((all-ok (car (step-thread tid v throws st)) (cdr (step-thread tid v throws st)))))))

(defthm inv-run
  (implies (inv st) (inv (run-sched sched st)))
  :hints (("Goal" :induct (run-sched sched st) :in-theory (disable step-thread inv))))

; ---- THE THEOREMS, under every schedule ------------------------------------------

; MUTUAL EXCLUSION: two threads mid-thunk at once are the same thread
(defthm one-runner
  (let ((st (run-sched sched (start-state))))
    (implies (and (eq (pc-of a (cdr st)) :claimed) (eq (pc-of b (cdr st)) :claimed))
             (equal a b)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance inv-run (st (start-state)))
                        (:instance all-ok-necc (cell (car (run-sched sched (start-state))))
                                   (pcs (cdr (run-sched sched (start-state)))))
                        (:instance all-ok-necc (cell (car (run-sched sched (start-state))))
                                   (pcs (cdr (run-sched sched (start-state)))) (a b)))
                  :in-theory (disable inv-run all-ok-necc all-ok start-state))))

; NO LOST RESULT: a thread that finished forcing read the cell's value,
; and the cell is realised to it
(defthm done-reads-realised
  (let ((st (run-sched sched (start-state))))
    (implies (and (consp (pc-of a (cdr st))) (eq (car (pc-of a (cdr st))) :done))
             (and (eq (car (car st)) :realised)
                  (equal (cadr (pc-of a (cdr st))) (cadr (car st))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance inv-run (st (start-state)))
                        (:instance all-ok-necc (cell (car (run-sched sched (start-state))))
                                   (pcs (cdr (run-sched sched (start-state))))))
                  :in-theory (disable inv-run all-ok-necc all-ok start-state))))

; STABILITY: once realised, a step changes nothing about the cell
(defthm realised-stays
  (implies (and (inv st) (eq (car (car st)) :realised))
           (equal (car (step-thread tid v throws st)) (car st)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance all-ok-necc (cell (car st)) (pcs (cdr st)) (a tid))) :in-theory (disable all-ok all-ok-necc))))

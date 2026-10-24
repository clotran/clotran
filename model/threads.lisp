; clotran's threads: each thread's own slots, and its context, formally
; (docs/model-coverage.md).
;
; src/f/Threads.f90 gives a thread its own state through pthread keys
; (th_key_set, th_key_get) -- and, while one thread runs clotran, from a
; plain cache instead: a lookup per runtime entry was 15% of a compiled
; loop. The OWNER is the first thread to set a key; its sets are copied
; into the cache; th_start and th_spawn turn the cache off (tls_multi)
; before the new thread exists, and so does a set from any thread but the
; owner. th_start_sized does not: the program's own thread is started
; with it by a first thread that has set no key, and which from then on
; only serves the main-thread mailbox (main.f90, th_main_serve). It runs
; a package's C function there, though, and one that calls back into
; clotran's C ABI read the evaluator thread's slots -- its value stack --
; while the cache was on: th_main_serve now turns the cache off before it
; runs one (old-serve-reads-the-owners, below).
;
; src/f/Eval.f90 gives each running thread an evaluator context: an id
; taken under the state lock, a free one or the next (gce_ctx_new), and
; given back by the thread that ran on it as it ends (ctx_release), never
; while it is the context this thread is running.
;
; Here threads are :unborn, :active (running clotran), :passive (the first
; thread serving its mailbox) or :gone; vals a thread's pthread slots.
;
; What it proves, under every interleaving:
;
;   OWN SLOTS  a th_key_get by any active thread answers that thread's own
;              value, cache or not -- given the discipline the code keeps:
;              a thread other than the owner starts running clotran only
;              through th_start/th_spawn (the cache off first), as the
;              program's thread from a first thread that set nothing, or
;              in th_main_serve (the cache off first, now)
;   CONTEXTS   no two live threads hold one context id; the id a new
;              context gets is held by no other thread
;   JOIN       a th_join that has returned returned on a thread that
;              had exited (pthread_join); one of a running thread does not
;   COST       counted: th_key_get 2 steps (the flag, then the cache or one
;              pthread lookup), gce_ctx_new 3 (a pop or a bump, then the
;              store) under the state lock, ctx_release 2 (a push) -- none
;              grows with the threads, keys or ids (the table's growth, with
;              the world stopped, is amortised: it doubles)
;
; Not modelled: the lock and condition wrappers (pthread's own), and the
; mailbox (model/mainbox.lisp). An embedder's own thread that calls the C
; ABI before it sets a key is outside the discipline (see lanes.md).

(in-package "ACL2")

; ---- OWN SLOTS ---------------------------------------------------------------------
;
; st = (multi owner cache ths), ths a list of (role vals)

(defun mk-th2 (role vals) (list role vals))
(defun th2-role (x) (nth 0 x))
(defun th2-vals (x) (nth 1 x))
(defun slot (k al) (cdr (assoc-equal k al)))

(defthm th2-fields
  (and (equal (th2-role (mk-th2 r v)) r) (equal (th2-vals (mk-th2 r v)) v)))

(in-theory (disable mk-th2 th2-role th2-vals))

; th_key_get
(defun tls-get (st i k)
  (if (nth 0 st) (slot k (th2-vals (nth i (nth 3 st)))) (slot k (nth 2 st))))

(defun tls-step (i a st)
  (let* ((multi (nth 0 st)) (owner (nth 1 st)) (cache (nth 2 st)) (ths (nth 3 st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let ((x (nth i ths)))
        (case (car a)
          ; th_key_set by an active thread
          (:set (if (not (eq (th2-role x) :active)) st
                  (let* ((k (cadr a)) (p (caddr a))
                         (ths2 (update-nth i (mk-th2 :active (put-assoc-equal k p (th2-vals x))) ths))
                         (owner2 (if (null owner) i owner)))
                    (if (equal owner2 i)
                        (list multi owner2 (put-assoc-equal k p cache) ths2)
                      (list t owner2 cache ths2)))))
          ; th_spawn, th_start: the cache off, then the thread
          (:spawn (let ((j (cadr a)))
                    (if (and (eq (th2-role x) :active) (natp j) (< j (len ths))
                             (eq (th2-role (nth j ths)) :unborn))
                        (list t owner cache (update-nth j (mk-th2 :active nil) ths))
                      st)))
          ; th_start_sized: the program's thread, by a first thread that has
          ; set nothing and only serves from then on
          (:start-sized (let ((j (cadr a)))
                          (if (and (eq (th2-role x) :active) (null owner) (natp j) (< j (len ths))
                                   (eq (th2-role (nth j ths)) :unborn) (null (th2-vals x)))
                              (list multi owner cache
                                    (update-nth j (mk-th2 :active nil) (update-nth i (mk-th2 :passive nil) ths)))
                            st)))
          ; th_main_serve runs a posted function: the cache off first
          (:serve-run (if (eq (th2-role x) :passive)
                          (list t owner cache (update-nth i (mk-th2 :active (th2-vals x)) ths))
                        st))
          (:exit (if (eq (th2-role x) :active) (list multi owner cache (update-nth i (mk-th2 :gone (th2-vals x)) ths)) st))
          (otherwise st))))))

(defun tls-run (sched st) (if (atom sched) st (tls-run (cdr sched) (tls-step (caar sched) (cdar sched) st))))

(defun count-active (ths) (if (atom ths) 0 (+ (if (eq (th2-role (car ths)) :active) 1 0) (count-active (cdr ths)))))

(defun all-vals-nil (ths) (if (atom ths) t (and (null (th2-vals (car ths))) (all-vals-nil (cdr ths)))))

; the cache is the owner's slots; with no owner nothing is set anywhere;
; with the cache on, at most one thread runs clotran and it is the owner
(defun tls-inv (st)
  (let ((multi (nth 0 st)) (owner (nth 1 st)) (cache (nth 2 st)) (ths (nth 3 st)))
    (and (true-listp st) (equal (len st) 4)
         (or (null owner) (and (natp owner) (< owner (len ths))))
         (implies owner (equal cache (th2-vals (nth owner ths))))
         (implies (not owner) (and (null cache) (all-vals-nil ths)))
         (implies (not multi)
                  (and (<= (count-active ths) 1)
                       (implies owner
                                (or (eq (th2-role (nth owner ths)) :active) (equal (count-active ths) 0))))))))

(defthm count-active-update-nth
  (implies (and (natp i) (< i (len ths)))
           (equal (count-active (update-nth i y ths))
                  (+ (count-active ths) (- (if (eq (th2-role (nth i ths)) :active) 1 0))
                     (if (eq (th2-role y) :active) 1 0)))))

(defthm all-vals-nil-update-nth
  (implies (and (all-vals-nil ths) (null (th2-vals y))) (all-vals-nil (update-nth i y ths))))

(defthm all-vals-nil-nth
  (implies (all-vals-nil ths) (equal (th2-vals (nth i ths)) nil)))

(defthm len-update-nth-th2
  (implies (and (natp i) (< i (len l))) (equal (len (update-nth i y l)) (len l))))

(defthm count-active-pos
  (implies (and (natp k) (< k (len ths)) (eq (th2-role (nth k ths)) :active)) (<= 1 (count-active ths)))
  :rule-classes :linear)

(defun two-active-ind (i j ths)
  (if (or (zp i) (zp j) (atom ths)) (list i j ths) (two-active-ind (1- i) (1- j) (cdr ths))))

; two different active threads make two
(defthm two-active
  (implies (and (natp i) (natp j) (< i (len ths)) (< j (len ths)) (not (equal i j))
                (eq (th2-role (nth i ths)) :active) (eq (th2-role (nth j ths)) :active))
           (<= 2 (count-active ths)))
  :rule-classes nil
  :hints (("Goal" :induct (two-active-ind i j ths))
          (and stable-under-simplificationp
               (quote (:use ((:instance count-active-pos (ths (cdr ths)) (k (+ -1 i)))
                             (:instance count-active-pos (ths (cdr ths)) (k (+ -1 j)))))))))

; the owner is never a thread not yet born
(defun owner-born (st)
  (let ((owner (nth 1 st)) (ths (nth 3 st)))
    (implies owner (not (eq (th2-role (nth owner ths)) :unborn)))))

(defthm tls-inv-step
  (implies (and (tls-inv st) (owner-born st))
           (and (tls-inv (tls-step i a st)) (owner-born (tls-step i a st))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance two-active (ths (nth 3 st)) (j (nth 1 st)))))))

; OWN SLOTS: what th_key_get answers an active thread is its own
(defthm tls-get-is-own
  (implies (and (tls-inv st) (natp i) (< i (len (nth 3 st))) (eq (th2-role (nth i (nth 3 st))) :active))
           (equal (tls-get st i k) (slot k (th2-vals (nth i (nth 3 st))))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance two-active (ths (nth 3 st)) (j (nth 1 st)))))))

(defthm tls-inv-run
  (implies (and (tls-inv st) (owner-born st))
           (and (tls-inv (tls-run sched st)) (owner-born (tls-run sched st))))
  :hints (("Goal" :in-theory (disable tls-step tls-inv owner-born))))

; th_main_serve as it was: the posted function ran with the cache still on
(defun old-serve (i st)
  (let ((ths (nth 3 st)))
    (list (nth 0 st) (nth 1 st) (nth 2 st) (update-nth i (mk-th2 :active (th2-vals (nth i ths))) ths))))

; the first thread started the program's thread, which set its stack key;
; the first thread then ran a posted function that asked for its own
; stack: the cache answered the program thread's
(defthm old-serve-reads-the-owners
  (let* ((st0 (list nil nil nil (list (mk-th2 :active nil) (mk-th2 :unborn nil))))
         (st1 (tls-run (list (cons 0 (list :start-sized 1)) (cons 1 (list :set :stack 42))) st0))
         (st2 (old-serve 0 st1)))
    (and (equal (tls-get st2 0 :stack) 42)
         (equal (slot :stack (th2-vals (nth 0 (nth 3 st2)))) nil)
         ; and now, the cache off: its own, nil
         (equal (tls-get (tls-step 0 (list :serve-run) st1) 0 :stack) nil)))
  :rule-classes nil)

; ---- CONTEXTS ----------------------------------------------------------------------
;
; cs = (free next held): free the ids given back, next the next new one,
; held the ids the live threads run on -- a thread holds one at a time

; gce_ctx_new: a free one, else the next; answers the id too
(defun cx-new (cs)
  (let ((free (nth 0 cs)) (next (nth 1 cs)) (held (nth 2 cs)))
    (if (consp free)
        (mv (car free) (list (cdr free) next (cons (car free) held)))
      (mv next (list free (1+ next) (cons next held))))))

; ctx_release: an id back, by the thread that held it
(defun cx-release (x cs)
  (let ((free (nth 0 cs)) (next (nth 1 cs)) (held (nth 2 cs)))
    (if (member-equal x held) (list (cons x free) next (remove1-equal x held)) cs)))

(defun all-below (l n) (if (atom l) t (and (natp (car l)) (< (car l) n) (all-below (cdr l) n))))

(defun cx-inv (cs)
  (let ((free (nth 0 cs)) (next (nth 1 cs)) (held (nth 2 cs)))
    (and (natp next) (no-duplicatesp-equal (append free held)) (all-below (append free held) next))))

(defthm member-append-cx (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm no-dups-append-split
  (equal (no-duplicatesp-equal (append a b))
         (and (no-duplicatesp-equal a) (no-duplicatesp-equal b) (not (intersectp-equal a b)))))

(defthm intersectp-cons-2
  (iff (intersectp-equal a (cons x b)) (or (member-equal x a) (intersectp-equal a b))))

(defthm member-remove1-cx
  (implies (not (member-equal y b)) (not (member-equal y (remove1-equal x b)))))

(defthm member-remove1-other
  (implies (not (equal y x)) (iff (member-equal y (remove1-equal x b)) (member-equal y b))))

(defthm no-dups-remove1-cx
  (implies (no-duplicatesp-equal b) (no-duplicatesp-equal (remove1-equal x b))))

(defthm not-member-remove1-self
  (implies (no-duplicatesp-equal b) (not (member-equal x (remove1-equal x b)))))

(defthm intersectp-remove1
  (implies (not (intersectp-equal a b)) (not (intersectp-equal a (remove1-equal x b)))))

(defthm all-below-append (equal (all-below (append a b) n) (and (all-below a n) (all-below b n))))

(defthm all-below-remove1 (implies (all-below b n) (all-below (remove1-equal x b) n)))

(defthm all-below-up (implies (and (all-below l n) (natp n)) (all-below l (1+ n))))

(defthm all-below-not-member (implies (all-below l n) (not (member-equal n l))))

(defthm all-below-member (implies (and (all-below l n) (member-equal x l)) (and (natp x) (< x n))))

(defthm not-intersect-member
  (implies (and (member-equal x b) (not (intersectp-equal a b))) (not (member-equal x a))))

(defthm cx-new-keeps
  (implies (cx-inv cs) (cx-inv (mv-nth 1 (cx-new cs)))))

(defthm cx-release-keeps
  (implies (cx-inv cs) (cx-inv (cx-release x cs))))

; CONTEXTS: the id a new context gets is held by no other thread
(defthm cx-new-fresh
  (implies (cx-inv cs) (not (member-equal (mv-nth 0 (cx-new cs)) (nth 2 cs)))))

(defthm cx-held-distinct
  (implies (cx-inv cs) (no-duplicatesp-equal (nth 2 cs))))

; COST, by counting: each operation is the instrumented one, with a step
; per load or store it does; its answer is the plain one's, and the count
; is bounded by a constant -- not by the threads, the keys or the ids
;
; th_key_get: the flag, then the cache slot or pthread_getspecific
(defun tls-get-c (st i k)
  (if (nth 0 st) (mv (slot k (th2-vals (nth i (nth 3 st)))) 2) (mv (slot k (nth 2 st)) 2)))

(defthm tls-get-cost
  (and (equal (mv-nth 0 (tls-get-c st i k)) (tls-get st i k))
       (<= (mv-nth 1 (tls-get-c st i k)) 2)))

; gce_ctx_new: the free list's head and its rest (a pop), else the next
; id and its bump; then the store into the thread's slot
(defun cx-new-c (cs)
  (let ((free (nth 0 cs)) (next (nth 1 cs)) (held (nth 2 cs)))
    (if (consp free)
        (mv (car free) (list (cdr free) next (cons (car free) held)) 3)
      (mv next (list free (1+ next) (cons next held)) 3))))

(defthm cx-new-cost
  (and (equal (mv-nth 0 (cx-new-c cs)) (mv-nth 0 (cx-new cs)))
       (equal (mv-nth 1 (cx-new-c cs)) (mv-nth 1 (cx-new cs)))
       (<= (mv-nth 2 (cx-new-c cs)) 3)))

; ctx_release: the id onto the free list (a push) and the slot cleared
(defun cx-release-c (x cs) (mv (cx-release x cs) 2))

(defthm cx-release-cost
  (and (equal (mv-nth 0 (cx-release-c x cs)) (cx-release x cs))
       (<= (mv-nth 1 (cx-release-c x cs)) 2)))

; ---- JOIN --------------------------------------------------------------------------
;
; th_join is pthread_join: it returns once the thread has exited, never
; before. js = (roles joins): roles :unborn, :running or :exited; joins the
; (i . j) for which thread i's th_join of j has returned. A join of a
; thread still running does not return: the step leaves the state as it
; was, and the scheduler runs i's join again later (it is blocked).

(defun jn-step (a js)
  (let ((roles (nth 0 js)) (joins (nth 1 js)))
    (case (car a)
      (:start (let ((j (cadr a)))
                (if (and (natp j) (< j (len roles)) (eq (nth j roles) :unborn))
                    (list (update-nth j :running roles) joins) js)))
      (:exit (let ((j (cadr a)))
               (if (and (natp j) (< j (len roles)) (eq (nth j roles) :running))
                   (list (update-nth j :exited roles) joins) js)))
      (:join (let ((i (cadr a)) (j (caddr a)))
               (if (and (natp i) (< i (len roles)) (eq (nth i roles) :running)
                        (natp j) (< j (len roles)) (eq (nth j roles) :exited))
                   (list roles (cons (cons i j) joins)) js)))
      (otherwise js))))

(defun jn-run (sched js) (if (atom sched) js (jn-run (cdr sched) (jn-step (car sched) js))))

(defun joins-exited (joins roles)
  (if (atom joins) t
    (and (consp (car joins)) (natp (cdar joins)) (< (cdar joins) (len roles))
         (eq (nth (cdar joins) roles) :exited)
         (joins-exited (cdr joins) roles))))

(defun jn-inv (js) (and (true-listp js) (equal (len js) 2) (joins-exited (nth 1 js) (nth 0 js))))

; an exited thread stays exited: no step but :exit writes a role, and
; :exit writes only over :running
(defthm joins-exited-update-nth
  (implies (and (joins-exited joins roles) (natp j) (< j (len roles)) (not (eq (nth j roles) :exited)))
           (joins-exited joins (update-nth j r roles))))

(defthm jn-inv-step (implies (jn-inv js) (jn-inv (jn-step a js))))

(defthm jn-inv-run (implies (jn-inv js) (jn-inv (jn-run sched js)))
  :hints (("Goal" :in-theory (disable jn-step jn-inv))))

(defthm joins-exited-member
  (implies (and (joins-exited joins roles) (member-equal (cons i j) joins))
           (eq (nth j roles) :exited)))

; JOIN: under every schedule, every th_join that has returned returned on
; a thread that had exited -- and still has
(defthm join-after-exit
  (implies (and (jn-inv js) (member-equal (cons i j) (nth 1 (jn-run sched js))))
           (eq (nth j (nth 0 (jn-run sched js))) :exited))
  :hints (("Goal" :use ((:instance jn-inv-run))
                  :in-theory (disable jn-inv-run jn-run jn-step))))

; and a join of a thread not yet exited does not return
(defthm join-blocks-while-running
  (implies (not (eq (nth j (nth 0 js)) :exited))
           (equal (jn-step (list :join i j) js) js)))

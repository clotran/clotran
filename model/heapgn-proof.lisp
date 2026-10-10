; clotran's heap under the model (PLAN step 33, stage 1c): THE YOUNG
; COLLECTION, SOUND. GC.f90's young collection marks from the roots and
; the REMEMBERED SET, and stops at the old: what the last collection left
; marked is old, and is neither cleared nor scanned. It is sound when every
; old object that references something unmarked is remembered -- then the
; remembered objects' slots, pushed, make every old object black, and the
; drain (heapg-proof.lisp's hpg-drain-closed) closes the mark set: no young
; object an old one reaches is swept.
;
; THE REMEMBERED-SET INVARIANT, at a young collection's start (stack empty):
; every marked object is black or remembered (os), every marked run black
; or remembered (vs) -- young-start. The write barrier keeps it:
;
;   hpg-write-slot   object o's slot k := (tag, ref)
;   hpg-barrier      o is remembered when it is marked (old) and the
;                    reference written is not (young) -- gc_set_slot's
;
; Theorems:
;   young-inv        roots pushed, then the remembered objects and runs
;                    scanned (hpg-scan-obj, hpg-scan-vec, as collect_young
;                    pushes their slots), from a young start: the drain's
;                    invariant holds
;   young-closed     so a drain that empties its stack with no overflow
;                    leaves every marked object and run black
;   barrier-keeps    a write with its barrier keeps young-start
;   aging-keeps      so does AGING a survivor (its mark cleared), when every
;                    marked object and run that references it is remembered
;                    -- collect_young's pass over the promoted and
;                    forget_young's keeping of what points at the aged
;   young-cost       the scan of the remembered set is 5 pushes an object
;                    and a run's length a run: O(remembered), not O(old)

(in-package "ACL2")

(include-book "heapg-proof")

(in-theory (disable hpg-push hpg-scan-obj hpg-scan-vec hpg-scan-run hpg-drain))

; ---- THE YOUNG COLLECTION'S MARKING ----------------------------------------------------

(defun roots-ok (rs)
  (if (atom rs) t
    (and (consp (car rs)) (sb64p (car (car rs))) (sb64p (cadr (car rs))) (roots-ok (cdr rs)))))

(defun push-list (rs hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (if (atom rs) hpg (let ((hpg (hpg-push (car (car rs)) (cadr (car rs)) hpg))) (push-list (cdr rs) hpg))))

(defun scan-objs (os hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (if (atom os) hpg (let ((hpg (hpg-scan-obj (nfix (car os)) 0 hpg))) (scan-objs (cdr os) hpg))))

(defun scan-vecs (vs hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (if (atom vs) hpg (let ((hpg (hpg-scan-vec (car vs) hpg))) (scan-vecs (cdr vs) hpg))))

(defmacro young-mark (rs os vs h) `(scan-vecs ,vs (scan-objs ,os (push-list ,rs ,h))))

; ---- THEY KEEP THE STOBJ WELL FORMED ---------------------------------------------------

(defthm push-list-ok
  (implies (and (hpgp h) (hpg-ok h) (roots-ok rs)) (and (hpgp (push-list rs h)) (hpg-ok (push-list rs h))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok))))

(defthm scan-objs-ok
  (implies (and (hpgp h) (hpg-ok h)) (and (hpgp (scan-objs os h)) (hpg-ok (scan-objs os h))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok))))

(defthm scan-vecs-ok
  (implies (and (hpgp h) (hpg-ok h)) (and (hpgp (scan-vecs vs h)) (hpg-ok (scan-vecs vs h))))
  :hints (("Goal" :in-theory (disable hpgp hpg-ok))))

(defthm hpg-ok-msp-natp
  (implies (hpg-ok h) (natp (msp-of h)))
  :hints (("Goal" :use ((:instance hpg-ok-stack (hpg h)))))
  :rule-classes :forward-chaining)

(defthm perr-push-list (implies (perr h) (perr (push-list rs h)))
  :hints (("Goal" :induct (push-list rs h) :in-theory (disable perr))))
(defthm perr-scan-objs (implies (perr h) (perr (scan-objs os h)))
  :hints (("Goal" :induct (scan-objs os h) :in-theory (disable perr))))
(defthm perr-scan-vecs (implies (perr h) (perr (scan-vecs vs h)))
  :hints (("Goal" :induct (scan-vecs vs h) :in-theory (disable perr))))
(defthm perr-up-lists
  (implies (perr h) (and (perr (push-list rs h)) (perr (scan-objs os h)) (perr (scan-vecs vs h))))
  :hints (("Goal" :in-theory (disable perr push-list scan-objs scan-vecs))))

; ---- ONE REFERENCE AT A TIME -----------------------------------------------------------

; nothing that is no positive index is marked, so nothing of it is owed
(defthm p-not-index
  (implies (not (and (natp r) (< 0 r))) (and (pobj r h) (pvec r h)))
  :hints (("Goal" :in-theory (enable pobj pvec omarked vmarked))))

(defun pobj-y (r h os) (or (pobj r h) (member-equal r os)))
(defun pvec-y (r h vs) (or (pvec r h) (member-equal r vs)))

(defthm push-list-p
  (implies (and (hpgp h) (hpg-ok h) (roots-ok rs))
           (and (implies (pobj r h) (or (perr (push-list rs h)) (pobj r (push-list rs h))))
                (implies (pvec r h) (or (perr (push-list rs h)) (pvec r (push-list rs h))))))
  :hints (("Goal" :induct (push-list rs h) :in-theory (disable hpgp hpg-ok perr pobj pvec hpg-push-p))
          ("Subgoal *1/2" :use ((:instance hpg-push-p (tg (car (car rs))) (rf (cadr (car rs))))
                                (:instance perr-up-lists (h (hpg-push (car (car rs)) (cadr (car rs)) h)) (rs (cdr rs)))))))

; a remembered object, scanned, is black
(defthm scan-one-obj
  (implies (and (hpgp h) (hpg-ok h) (natp a) (not (perr (hpg-scan-obj a 0 h))))
           (pobj a (hpg-scan-obj a 0 h)))
  :hints (("Goal" :in-theory (e/d (pobj black-obj perr) (hpg-scan-obj-blackens))
           :use ((:instance hpg-scan-obj-blackens (i a) (k 0))))))

(defthm scan-objs-p
  (implies (and (hpgp h) (hpg-ok h) (pobj-y r h os) (pvec-y r h vs))
           (or (perr (scan-objs os h)) (and (pobj r (scan-objs os h)) (pvec-y r (scan-objs os h) vs))))
  :hints (("Goal" :induct (scan-objs os h) :in-theory (disable hpgp hpg-ok perr pobj pvec hpg-scan-obj-p scan-one-obj))
          ("Subgoal *1/2" :cases ((equal r (nfix (car os))))
           :use ((:instance hpg-scan-obj-p (i (nfix (car os))) (k 0))
                 (:instance scan-one-obj (a (nfix (car os))))
                 (:instance perr-up-lists (h (hpg-scan-obj (nfix (car os)) 0 h)) (os (cdr os)))))))

(defthm scan-one-vec
  (implies (and (hpgp h) (hpg-ok h) (not (perr (hpg-scan-vec a h))))
           (pvec a (hpg-scan-vec a h)))
  :hints (("Goal" :in-theory (e/d (pvec perr) (hpg-scan-vec-blackens))
           :use ((:instance hpg-scan-vec-blackens (i a))))))

(defthm scan-vecs-p
  (implies (and (hpgp h) (hpg-ok h) (pobj r h) (pvec-y r h vs))
           (or (perr (scan-vecs vs h)) (and (pobj r (scan-vecs vs h)) (pvec r (scan-vecs vs h)))))
  :hints (("Goal" :induct (scan-vecs vs h) :in-theory (disable hpgp hpg-ok perr pobj pvec hpg-scan-vec-p scan-one-vec))
          ("Subgoal *1/2" :cases ((equal r (car vs)))
           :use ((:instance hpg-scan-vec-p (i (car vs)))
                 (:instance scan-one-vec (a (car vs)))
                 (:instance perr-up-lists (h (hpg-scan-vec (car vs) h)) (vs (cdr vs)))))))

; a remembered thing stays remembered through the roots' pushes
(defthm push-list-y
  (implies (and (hpgp h) (hpg-ok h) (roots-ok rs) (pobj-y r h os) (pvec-y r h vs))
           (or (perr (push-list rs h)) (and (pobj-y r (push-list rs h) os) (pvec-y r (push-list rs h) vs))))
  :hints (("Goal" :in-theory (disable push-list perr pobj pvec) :use push-list-p)))

(defthm young-one
  (implies (and (hpgp h) (hpg-ok h) (roots-ok rs) (pobj-y r h os) (pvec-y r h vs))
           (or (perr (young-mark rs os vs h))
               (and (pobj r (young-mark rs os vs h)) (pvec r (young-mark rs os vs h)))))
  :hints (("Goal" :in-theory (disable push-list scan-objs scan-vecs perr pobj pvec pobj-y pvec-y
                                      scan-objs-p scan-vecs-p push-list-y)
           :use (push-list-y
                 (:instance scan-objs-p (h (push-list rs h)))
                 (:instance scan-vecs-p (h (scan-objs os (push-list rs h))))
                 (:instance perr-up-lists (h (push-list rs h)))
                 (:instance perr-up-lists (h (scan-objs os (push-list rs h))))))))

; ---- THE THEOREM -------------------------------------------------------------------------

; at a young collection's start: every marked object and run black or
; remembered (the stack is empty, so none is on it)
(defun-sk young-start (h os vs) (forall r (and (pobj-y r h os) (pvec-y r h vs))))

(defthm young-inv
  (implies (and (hpgp h) (hpg-ok h) (roots-ok rs) (young-start h os vs))
           (hpg-inv (young-mark rs os vs h)))
  :hints (("Goal" :in-theory (disable push-list scan-objs scan-vecs perr pobj pvec pobj-y pvec-y young-one
                                      young-start-necc)
           :expand ((hpg-inv-all (young-mark rs os vs h)))
           :use ((:instance young-one (r (hpg-inv-all-witness (young-mark rs os vs h))))
                 (:instance young-start-necc (r (hpg-inv-all-witness (young-mark rs os vs h))))))))

; THE YOUNG COLLECTION IS SOUND: from a start the barrier kept, roots
; pushed and the remembered set scanned, a drain that empties its stack
; with no overflow leaves every marked object and run black -- what the
; roots reach, through the old or not, is marked
(defthm young-closed
  (implies (and (hpgp h) (hpg-ok h) (roots-ok rs) (young-start h os vs)
                (equal (msp-of (hpg-drain fuel (young-mark rs os vs h))) 0)
                (not (perr (hpg-drain fuel (young-mark rs os vs h)))))
           (and (implies (omarked r (hpg-drain fuel (young-mark rs os vs h)))
                         (black-obj r (hpg-drain fuel (young-mark rs os vs h))))
                (implies (and (vmarked r (hpg-drain fuel (young-mark rs os vs h)))
                              (< r (len (nth *h-vleni* (hpg-drain fuel (young-mark rs os vs h))))))
                         (black-vec r (hpg-drain fuel (young-mark rs os vs h))))))
  :hints (("Goal" :in-theory (disable push-list scan-objs scan-vecs perr hpg-inv young-inv hpg-drain-closed
                                      young-start)
           :use (young-inv
                 (:instance hpg-drain-closed (h (young-mark rs os vs h)))))))

; ---- THE BARRIER KEEPS IT ------------------------------------------------------------------

; object o's slot k := (tag, ref), as gc_set_slot writes it
(defun hpg-write-slot (o k tag ref hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (let ((j (+ (* 5 (nfix o)) (nfix k))))
    (if (and (< (nfix k) 5) (< j (h-otag-length hpg)) (< j (h-oref-length hpg)))
        (let ((hpg (update-h-otagi j tag hpg))) (update-h-orefi j ref hpg))
      hpg)))

; the barrier: o remembered when it is old (marked) and what is written is
; not marked
(defun hpg-barrier (o tag ref os h)
  (if (and (omarked o h) (not (marked-ref tag ref h))) (cons o os) os))

; the write changes the slots' words alone
(defthm write-slot-marks
  (and (equal (nth *h-omarki* (hpg-write-slot o k tag ref h)) (nth *h-omarki* h))
       (equal (nth *h-vmarki* (hpg-write-slot o k tag ref h)) (nth *h-vmarki* h))
       (equal (nth *h-smarki* (hpg-write-slot o k tag ref h)) (nth *h-smarki* h))
       (equal (nth *h-vleni* (hpg-write-slot o k tag ref h)) (nth *h-vleni* h))
       (equal (nth *h-voffi* (hpg-write-slot o k tag ref h)) (nth *h-voffi* h))
       (equal (nth *h-atagi* (hpg-write-slot o k tag ref h)) (nth *h-atagi* h))
       (equal (nth *h-arefi* (hpg-write-slot o k tag ref h)) (nth *h-arefi* h))
       (equal (nth *h-msp* (hpg-write-slot o k tag ref h)) (nth *h-msp* h))
       (equal (len (nth *h-otagi* (hpg-write-slot o k tag ref h))) (len (nth *h-otagi* h)))
       (equal (len (nth *h-orefi* (hpg-write-slot o k tag ref h))) (len (nth *h-orefi* h)))))

(defthm marked-ref-write
  (equal (marked-ref tg rf (hpg-write-slot o k tag ref h)) (marked-ref tg rf h))
  :hints (("Goal" :in-theory (e/d (marked-ref omarked vmarked smarked) (hpg-write-slot)))))

(defthm omarked-write
  (and (equal (omarked r (hpg-write-slot o k tag ref h)) (omarked r h))
       (equal (vmarked r (hpg-write-slot o k tag ref h)) (vmarked r h)))
  :hints (("Goal" :in-theory (e/d (omarked vmarked) (hpg-write-slot)))))

; two objects' slot words never meet
(defthm slot-words-apart
  (implies (and (natp i) (natp o) (not (equal i o)) (natp k) (< k 5) (natp k2) (< k2 5))
           (not (equal (+ k (* 5 i)) (+ k2 (* 5 o)))))
  :hints (("Goal" :cases ((< i o)))))

; a word the write did not write reads as before
(defthm write-slot-words
  (implies (and (natp j) (not (equal j (+ (* 5 (nfix o)) (nfix k)))))
           (and (equal (nth j (nth *h-otagi* (hpg-write-slot o k tag ref h))) (nth j (nth *h-otagi* h)))
                (equal (nth j (nth *h-orefi* (hpg-write-slot o k tag ref h))) (nth j (nth *h-orefi* h))))))

; another object's slots, and every run, are as they were
(defthm slots-marked-write-other
  (implies (and (natp i) (natp o) (not (equal i o)) (natp k2) (< k2 5))
           (equal (slots-marked i k (hpg-write-slot o k2 tag ref h)) (slots-marked i k h)))
  :hints (("Goal" :induct (slots-marked i k h) :in-theory (disable marked-ref hpg-write-slot))))

(defthm slots-marked-write-out
  (implies (not (and (natp k2) (< k2 5)))
           (equal (hpg-write-slot o k2 tag ref h) (if (natp k2) h (hpg-write-slot o 0 tag ref h)))))

(defthm run-marked-write
  (equal (run-marked j e (hpg-write-slot o k tag ref h)) (run-marked j e h))
  :hints (("Goal" :induct (run-marked j e h) :in-theory (disable marked-ref hpg-write-slot))))

(defthm black-vec-write
  (equal (black-vec i (hpg-write-slot o k tag ref h)) (black-vec i h))
  :hints (("Goal" :in-theory (e/d (black-vec) (hpg-write-slot run-marked)))))

; o's own slots: those it had marked stay marked, and the new one is
; marked when what it holds is
(defthm write-slot-word-self
  (implies (and (< (nfix k) 5) (< (+ (* 5 (nfix o)) (nfix k)) (len (nth *h-otagi* h)))
                (< (+ (* 5 (nfix o)) (nfix k)) (len (nth *h-orefi* h))))
           (and (equal (nth (+ (* 5 (nfix o)) (nfix k)) (nth *h-otagi* (hpg-write-slot o k tag ref h))) tag)
                (equal (nth (+ (* 5 (nfix o)) (nfix k)) (nth *h-orefi* (hpg-write-slot o k tag ref h))) ref))))

(defthm slots-marked-write-self
  (implies (and (natp o) (slots-marked o k h) (marked-ref tag ref h))
           (slots-marked o k (hpg-write-slot o k2 tag ref h)))
  :hints (("Goal" :induct (slots-marked o k h) :in-theory (disable marked-ref hpg-write-slot))
          ("Subgoal *1/2" :cases ((equal (nfix k2) k))
           :use ((:instance write-slot-words (j (+ k (* 5 o))) (k k2))
                 (:instance write-slot-word-self (k k2))))))

(defthm barrier-keeps-one
  (implies (and (natp o) (natp k) (< k 5) (equal (msp-of h) 0) (pobj-y r h os) (pvec-y r h vs))
           (and (pobj-y r (hpg-write-slot o k tag ref h) (hpg-barrier o tag ref os h))
                (pvec-y r (hpg-write-slot o k tag ref h) vs)))
  :hints (("Goal" :in-theory (e/d (pobj pvec black-obj) (hpg-write-slot marked-ref))
           :cases ((equal r o)))))

; THE BARRIER KEEPS THE INVARIANT: a write with its barrier, between
; collections, leaves every old object black or remembered
(defthm barrier-keeps
  (implies (and (natp o) (natp k) (< k 5) (equal (msp-of h) 0) (young-start h os vs))
           (young-start (hpg-write-slot o k tag ref h) (hpg-barrier o tag ref os h) vs))
  :hints (("Goal" :in-theory (disable hpg-write-slot hpg-barrier pobj-y pvec-y young-start-necc barrier-keeps-one)
           :expand ((young-start (hpg-write-slot o k tag ref h) (hpg-barrier o tag ref os h) vs))
           :use ((:instance young-start-necc
                            (r (young-start-witness (hpg-write-slot o k tag ref h) (hpg-barrier o tag ref os h) vs)))
                 (:instance barrier-keeps-one
                            (r (young-start-witness (hpg-write-slot o k tag ref h) (hpg-barrier o tag ref os h) vs)))))))

; ---- COST ------------------------------------------------------------------------------------

; the remembered set's scan: 5 pushes a remembered object, a run's length
; a remembered run -- proportional to what is remembered, not to the old
(defun-nx scan-objs-pushes (os) (if (atom os) 0 (+ 5 (scan-objs-pushes (cdr os)))))

(defthm young-cost
  (equal (scan-objs-pushes os) (* 5 (len os))))

; ---- THE GENERATED TEST IS THE BARRIER'S ---------------------------------------------------

(include-book "heapgn")

(defthm hpg-young-ref-is
  (implies (integerp ref)
           (equal (hpg-young-ref tag ref h) (not (marked-ref tag ref h))))
  :hints (("Goal" :in-theory (enable marked-ref omarked vmarked smarked))))

; ---- AGING KEEPS IT ------------------------------------------------------------------------

; a young survivor is AGED, not promoted: its mark cleared, so it is young
; again at the next collection (collect_young's age_obj). An old object or
; run that references it is then no longer black; collect_young's own pass
; remembers each (any_aged_slot, any_aged_run). With that, the invariant
; holds after the aging.

(defun hpg-unmark (a h)
  (if (and (natp a) (< a (len (nth *h-omarki* h))))
      (update-nth *h-omarki* (update-nth a 0 (nth *h-omarki* h)) h)
    h))

; object i's slots k .. 4 hold a reference to object a
(defun slots-ref (i k a h)
  (declare (xargs :measure (nfix (- 5 (nfix k)))))
  (if (or (not (natp k)) (<= 5 k))
      nil
    (let ((j (+ (* 5 i) k)))
      (if (and (< j (len (nth *h-otagi* h))) (< j (len (nth *h-orefi* h))))
          (or (and (equal (nth j (nth *h-otagi* h)) 8) (equal (nth j (nth *h-orefi* h)) a))
              (slots-ref i (+ 1 k) a h))
        nil))))

(defun run-ref (j e a h)
  (declare (xargs :measure (nfix (- (nfix e) (nfix j)))))
  (if (or (not (natp j)) (not (natp e)) (<= e j))
      nil
    (if (and (< j (len (nth *h-atagi* h))) (< j (len (nth *h-arefi* h))))
        (or (and (equal (nth j (nth *h-atagi* h)) 8) (equal (nth j (nth *h-arefi* h)) a))
            (run-ref (+ 1 j) e a h))
      nil)))

(defun vec-ref (i a h)
  (if (and (< i (len (nth *h-voffi* h))) (< i (len (nth *h-vleni* h))))
      (let ((off (nfix (nth i (nth *h-voffi* h)))) (n (nfix (nth i (nth *h-vleni* h)))))
        (if (and (<= off *hb40*) (<= n *hb40*) (<= (+ off n) *hb40*))
            (run-ref off (+ off n) a h)
          nil))
    nil))

; the unmarking changes object a's mark alone
(defthm marked-ref-unmark
  (implies (not (and (equal tag 8) (equal ref a)))
           (equal (marked-ref tag ref (hpg-unmark a h)) (marked-ref tag ref h)))
  :hints (("Goal" :in-theory (enable marked-ref omarked vmarked smarked))))

(defthm unmark-omarked
  (implies (not (equal r a)) (equal (omarked r (hpg-unmark a h)) (omarked r h)))
  :hints (("Goal" :in-theory (enable omarked))))

(defthm unmark-omarked-down
  (implies (omarked r (hpg-unmark a h)) (and (omarked r h) (not (equal r a))))
  :hints (("Goal" :in-theory (enable omarked)))
  :rule-classes :forward-chaining)

(defthm unmark-vmarked (equal (vmarked r (hpg-unmark a h)) (vmarked r h))
  :hints (("Goal" :in-theory (enable vmarked))))

(defthm unmark-fields
  (and (equal (nth *h-otagi* (hpg-unmark a h)) (nth *h-otagi* h))
       (equal (nth *h-orefi* (hpg-unmark a h)) (nth *h-orefi* h))
       (equal (nth *h-atagi* (hpg-unmark a h)) (nth *h-atagi* h))
       (equal (nth *h-arefi* (hpg-unmark a h)) (nth *h-arefi* h))
       (equal (nth *h-voffi* (hpg-unmark a h)) (nth *h-voffi* h))
       (equal (nth *h-vleni* (hpg-unmark a h)) (nth *h-vleni* h))
       (equal (nth *h-msp* (hpg-unmark a h)) (nth *h-msp* h))))

; slots that reference no a stay marked when a's mark is cleared
(defthm slots-marked-unmark
  (implies (and (slots-marked i k h) (not (slots-ref i k a h)))
           (slots-marked i k (hpg-unmark a h)))
  :hints (("Goal" :induct (slots-marked i k h) :in-theory (disable hpg-unmark marked-ref))))

(defthm run-marked-unmark
  (implies (and (run-marked j e h) (not (run-ref j e a h)))
           (run-marked j e (hpg-unmark a h)))
  :hints (("Goal" :induct (run-marked j e h) :in-theory (disable hpg-unmark marked-ref))))

(defthm black-vec-unmark
  (implies (and (black-vec i h) (not (vec-ref i a h)))
           (black-vec i (hpg-unmark a h)))
  :hints (("Goal" :in-theory (e/d (black-vec) (hpg-unmark run-marked)))))

; every marked object and run that references a, remembered
(defun-sk aged-covered (h a os vs)
  (forall r (and (implies (and (omarked r h) (slots-ref r 0 a h)) (member-equal r os))
                 (implies (and (vmarked r h) (vec-ref r a h)) (member-equal r vs)))))

(defthm aging-keeps-one
  (implies (and (equal (msp-of h) 0) (pobj-y r h os) (pvec-y r h vs)
                (implies (and (omarked r h) (slots-ref r 0 a h)) (member-equal r os))
                (implies (and (vmarked r h) (vec-ref r a h)) (member-equal r vs)))
           (and (pobj-y r (hpg-unmark a h) os) (pvec-y r (hpg-unmark a h) vs)))
  :hints (("Goal" :in-theory (e/d (pobj pvec black-obj) (hpg-unmark marked-ref omarked vmarked)))))

; AGING KEEPS THE INVARIANT: a's mark cleared, with every marked object and
; run that references it remembered, every old object stays black or
; remembered
(defthm aging-keeps
  (implies (and (equal (msp-of h) 0) (young-start h os vs) (aged-covered h a os vs))
           (young-start (hpg-unmark a h) os vs))
  :hints (("Goal" :in-theory (disable hpg-unmark pobj-y pvec-y young-start-necc aged-covered-necc aging-keeps-one
                                      slots-ref vec-ref omarked vmarked unmark-omarked-down)
           :expand ((young-start (hpg-unmark a h) os vs))
           :use ((:instance young-start-necc (r (young-start-witness (hpg-unmark a h) os vs)))
                 (:instance aged-covered-necc (r (young-start-witness (hpg-unmark a h) os vs)))
                 (:instance aging-keeps-one (r (young-start-witness (hpg-unmark a h) os vs)))))))

; ---- THE GENERATED TESTS FIND WHAT AGING NEEDS REMEMBERED -----------------------------------

; a reference to an aged object a, in object o's slots or run v's words, is
; what hpg-obj-refs-aged and hpg-vec-refs-aged answer true for: so the
; passes that remember those, remember every one aged-covered asks for
(defmacro aged-obj (a h) `(and (natp ,a) (< 0 ,a) (< ,a (len (nth *h-oagedi* ,h))) (not (equal (nth ,a (nth *h-oagedi* ,h)) 0))))

(defthm obj-refs-aged-finds
  (implies (and (natp o) (slots-ref o k a h) (aged-obj a h))
           (hpg-obj-refs-aged o k h))
  :hints (("Goal" :induct (slots-ref o k a h))))

(defthm run-refs-aged-finds
  (implies (and (run-ref j e a h) (aged-obj a h))
           (hpg-run-refs-aged j e h))
  :hints (("Goal" :induct (run-ref j e a h))))

(defthm vec-refs-aged-finds
  (implies (and (hpgp h) (vec-ref v a h) (aged-obj a h))
           (hpg-vec-refs-aged v h))
  :hints (("Goal" :in-theory (disable run-ref hpg-run-refs-aged))))

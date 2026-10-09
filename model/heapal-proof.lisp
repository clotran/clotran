; Allocation (model/heapal.lisp) proved: no slot is handed out twice.
;
; THE INVARIANT over a ghost list L, the free list's slots in order, and B,
; the batch's: L runs from the head through the next links to 0; every slot
; of L and of B is free (flagged), in the pool and at most `used`; and L and
; B together have no slot twice. Then:
;   hpg-obj-take-safe  a take hands out L's head (and the list is L's rest)
;                      or the slot just past `used` (and L is as it was)
;   hpg-obj-pop-safe   a batch pop hands out B's last, B's rest left
;   hpg-obj-fill-safe  a fill moves slots from L's front, or from past
;                      `used`, onto B: the invariant holds of what is left
;   hpg-obj-use-safe   using a slot in neither L nor B keeps the invariant
;   hpg-free-obj-safe  the sweep's free of a slot not free puts it on L
; and so a slot handed out is in neither L nor B: nobody else gets it.

(in-package "ACL2")

(include-book "heapal")

(in-theory (disable nth update-nth hpgp hpg-ok hpg-sw-ok hpg-al-ok))

(defmacro ofree (h) `(nth *h-ofreei* ,h))
(defmacro onext (h) `(nth *h-onexti* ,h))
(defmacro oused (h) `(nth *h-oused* ,h))
(defmacro ohead (h) `(nth *h-ohead* ,h))

; a slot that may be on the free list or in the batch: in the pool, at most
; used, flagged free
(defun fslot (i h)
  (and (natp i) (< 0 i) (< i (len (ofree h))) (< i (len (onext h)))
       (integerp (oused h)) (<= i (oused h)) (not (equal (nth i (ofree h)) 0))))

(defun fl-ok (l head h)
  (if (endp l)
      (equal head 0)
    (and (equal head (car l)) (fslot (car l) h)
         (fl-ok (cdr l) (nth (car l) (onext h)) h))))

(defun all-fslot (l h) (if (endp l) t (and (fslot (car l) h) (all-fslot (cdr l) h))))

; the batch's slots, last first: ob[k], ob[k-1], .. ob[1]
(defun b-list (k h) (if (zp k) nil (cons (nth k (nth *h-obi* h)) (b-list (1- k) h))))

(defun al-inv (l h)
  (and (true-listp l)
       (fl-ok l (ohead h) h)
       (all-fslot l h)
       (all-fslot (b-list (nth *h-nob* h) h) h)
       (no-duplicatesp (append l (b-list (nth *h-nob* h) h)))))

; ---- FRAME: WHAT THE INVARIANT READS -------------------------------------------------------

(defthm hpg-s64-id (implies (sb64ip x) (equal (hpg-s64 x) x)) :hints (("Goal" :in-theory (enable hpg-s64))))

(defthm onext-elem-sb64
  (implies (and (hpgp h) (< (nfix i) (len (onext h))))
           (sb64ip (nth i (onext h))))
  :hints (("Goal" :use ((:instance hpg-onext-elem (hpg h) (j i))))))

(defthm hpg-s64-onext
  (implies (and (hpgp h) (< (nfix i) (len (onext h))))
           (equal (hpg-s64 (nth i (onext h))) (nth i (onext h))))
  :hints (("Goal" :in-theory (disable hpg-s64-id onext-elem-sb64)
           :use ((:instance hpg-s64-id (x (nth i (onext h)))) (:instance onext-elem-sb64)))))

(defthm hpg-s64-ohead
  (implies (hpgp h) (equal (hpg-s64 (nth *h-ohead* h)) (nth *h-ohead* h)))
  :hints (("Goal" :in-theory (enable hpgp hpg-s64))))

; fields the invariant does not read, written
(defmacro not-read (fld)
  `(and (equal (fslot i (update-nth ,fld v h)) (fslot i h))
        (equal (fl-ok l head (update-nth ,fld v h)) (fl-ok l head h))
        (equal (all-fslot l (update-nth ,fld v h)) (all-fslot l h))))

(defthm fslot-frame-head (not-read *h-ohead*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm fslot-frame-nob (not-read *h-nob*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm fslot-frame-obi (not-read *h-obi*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm fslot-frame-omark (not-read *h-omarki*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm fslot-frame-okind (not-read *h-okindi*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm fslot-frame-ofin (not-read *h-ofini*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm fslot-frame-nswo (not-read *h-nswo*) :hints (("Goal" :induct (fl-ok l head h))))
(defthm all-fslot-frame-head (equal (all-fslot l (update-nth *h-ohead* v h)) (all-fslot l h)))

(defthm b-list-frame
  (implies (and (natp fld) (not (equal fld *h-obi*)))
           (equal (b-list k (update-nth fld v h)) (b-list k h))))

; `used` raised: what was at most used still is
(defthm fslot-used-up
  (implies (and (fslot i h) (integerp u) (<= (oused h) u)) (fslot i (update-nth *h-oused* u h))))
(defthm fl-ok-used-up
  (implies (and (fl-ok l head h) (integerp u) (<= (oused h) u)) (fl-ok l head (update-nth *h-oused* u h))))
(defthm all-fslot-used-up
  (implies (and (all-fslot l h) (integerp u) (<= (oused h) u)) (all-fslot l (update-nth *h-oused* u h))))

; a slot's flag or link written: the slots of a list without it are as they were
(defthm fslot-other-flag
  (implies (and (equal x (ofree h)) (natp j) (< j (len (ofree h))) (not (equal j i)))
           (equal (fslot i (update-nth *h-ofreei* (update-nth j v x) h)) (fslot i h)))
  :hints (("Goal" :in-theory (enable nth update-nth))))
(defthm fl-ok-other
  (implies (and (natp j) (not (member j l)) (< j (len (ofree h))) (< j (len (onext h))))
           (and (implies (equal x (ofree h))
                         (equal (fl-ok l head (update-nth *h-ofreei* (update-nth j v x) h)) (fl-ok l head h)))
                (implies (equal x (onext h))
                         (equal (fl-ok l head (update-nth *h-onexti* (update-nth j v x) h)) (fl-ok l head h)))))
  :hints (("Goal" :induct (fl-ok l head h) :in-theory (enable nth update-nth))))
(defthm all-fslot-other
  (implies (and (natp j) (not (member j l)) (< j (len (ofree h))) (< j (len (onext h))))
           (and (implies (equal x (ofree h))
                         (equal (all-fslot l (update-nth *h-ofreei* (update-nth j v x) h)) (all-fslot l h)))
                (implies (equal x (onext h))
                         (equal (all-fslot l (update-nth *h-onexti* (update-nth j v x) h)) (all-fslot l h)))))
  :hints (("Goal" :in-theory (enable nth update-nth))))

; every slot of a well-formed list is a free slot, at most used (al-inv
; carries all-fslot itself, so this stays closed)
(defthm fl-ok-all-fslot (implies (fl-ok l head h) (all-fslot l h)))
(in-theory (disable fl-ok-all-fslot))
(defthm all-fslot-member
  (implies (and (all-fslot l h) (member i l)) (fslot i h)))
(defthm all-fslot-above-used
  (implies (and (all-fslot l h) (integerp (oused h)) (< (oused h) i)) (not (member i l))))
(defthm all-fslot-unflagged
  (implies (and (all-fslot l h) (natp i) (< i (len (ofree h))) (equal (nth i (ofree h)) 0)) (not (member i l))))

; ---- THE THEOREMS -----------------------------------------------------------------------------

(defmacro bl (h) `(b-list (nth *h-nob* ,h) ,h))

(defthm no-dups-append-cons
  (implies (no-duplicatesp (append (cons a x) y))
           (and (no-duplicatesp (append x y)) (not (member a (append x y))))))

(defthm member-of-append
  (iff (member e (append x y)) (or (member e x) (member e y))))

(defthm no-dups-append-middle
  (implies (no-duplicatesp (append x (cons a y)))
           (and (no-duplicatesp (append x y)) (not (member a (append x y))))))

(defthm no-dups-append-middle-intro
  (implies (and (no-duplicatesp (append x y)) (not (member a (append x y))))
           (no-duplicatesp (append x (cons a y)))))

; A TAKE: the list's head, the list its rest; or the slot past used, which
; is on neither the list nor in the batch
(defthm hpg-obj-take-safe
  (implies (and (hpgp h) (hpg-al-ok h) (al-inv l h))
           (let ((i (mv-nth 0 (hpg-obj-take h))) (h2 (mv-nth 1 (hpg-obj-take h))))
             (if (consp l)
                 (and (equal i (car l)) (al-inv (cdr l) h2) (not (member i (append (cdr l) (bl h2)))))
               (and (al-inv l h2)
                    (or (equal i 0)
                        (and (equal i (+ 1 (oused h))) (not (member i (append l (bl h2))))))))))
  :hints (("Goal" :in-theory (enable hpg-obj-take) :expand ((fl-ok l (nth *h-ohead* h) h)))))

; A POP: the batch's last; the batch its rest
(defthm hpg-obj-pop-safe
  (implies (and (hpg-al-ok h) (al-inv l h) (< 0 (nth *h-nob* h)))
           (let ((i (mv-nth 0 (hpg-obj-pop h))) (h2 (mv-nth 1 (hpg-obj-pop h))))
             (and (equal i (car (bl h))) (al-inv l h2) (not (member i (append l (bl h2)))))))
  :hints (("Goal" :in-theory (enable hpg-obj-pop) :expand ((b-list (nth *h-nob* h) h)))))

; USE of a slot neither on the list nor in the batch
(defthm hpg-obj-use-safe
  (implies (and (al-inv l h) (natp i) (< i (len (ofree h))) (< i (len (onext h))) (< i (len (nth *h-omarki* h)))
                (not (member i (append l (bl h)))))
           (al-inv l (hpg-obj-use i h)))
  :hints (("Goal" :in-theory (enable hpg-obj-use))))

; THE SWEEP'S FREE of a slot not free: on the list's front
(defthm hpg-free-obj-safe
  (implies (and (hpgp h) (al-inv l h) (natp i) (< 0 i) (<= i (oused h)) (integerp (oused h))
                (< i (len (ofree h))) (< i (len (onext h))) (< i (len (nth *h-okindi* h))) (< i (len (nth *h-ofini* h)))
                (equal (nth i (ofree h)) 0))
           (al-inv (cons i l) (hpg-free-obj i h)))
  :hints (("Goal" :in-theory (enable hpg-free-obj))))

; ---- THE FILL ---------------------------------------------------------------------------------

(defthm b-list-write-above
  (implies (and (equal x (nth *h-obi* h)) (natp k) (natp n) (< k n))
           (equal (b-list k (update-nth *h-obi* (update-nth n v x) h)) (b-list k h)))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm b-list-step
  (implies (natp k) (equal (b-list (+ 1 k) h) (cons (nth (+ 1 k) (nth *h-obi* h)) (b-list k h)))))

(defthm fl-ok-head-consp
  (implies (and (fl-ok l head h) (not (equal head 0))) (consp l)))

; the list's head moved into the batch
(defthm hpg-obj-fill-list-safe
  (implies (and (hpgp h) (hpg-al-ok h) (al-inv l h) (< (+ 1 (nth *h-nob* h)) (len (nth *h-obi* h)))
                (< 0 (ohead h)) (< (ohead h) (len (onext h))))
           (al-inv (cdr l) (hpg-obj-fill-list h)))
  :hints (("Goal" :in-theory (enable hpg-obj-fill-list) :expand ((fl-ok l (nth *h-ohead* h) h)))))

; the slot past used moved into the batch
(defthm hpg-obj-fill-end-safe
  (implies (and (hpgp h) (hpg-al-ok h) (al-inv l h) (< (+ 1 (nth *h-nob* h)) (len (nth *h-obi* h)))
                (< (oused h) (nth *h-ocap* h)) (< (+ 1 (oused h)) (len (ofree h))) (< (+ 1 (oused h)) (len (onext h))))
           (al-inv l (hpg-obj-fill-end h)))
  :hints (("Goal" :in-theory (enable hpg-obj-fill-end))))

(in-theory (disable al-inv hpg-obj-fill-list hpg-obj-fill-end))

; what is left of the list as the fill takes from its front
(defun-nx fill-rest (l fuel hpg)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (< (+ 1 (h-nob hpg)) (h-ob-length hpg))))
      l
    (if (and (< 0 (h-ohead hpg)) (< (h-ohead hpg) (h-onext-length hpg)))
        (let ((hpg (hpg-obj-fill-list hpg))) (fill-rest (cdr l) (- fuel 1) hpg))
      (if (and (< (h-oused hpg) (h-ocap hpg)) (< (+ 1 (h-oused hpg)) (h-ofree-length hpg))
               (< (+ 1 (h-oused hpg)) (h-onext-length hpg)))
          (let ((hpg (hpg-obj-fill-end hpg))) (fill-rest l (- fuel 1) hpg))
        l))))

; A FILL keeps the invariant: the slots it moved are the batch's, what it
; left the list
(defthm hpg-obj-fill-safe
  (implies (and (hpgp h) (hpg-al-ok h) (al-inv l h))
           (al-inv (fill-rest l fuel h) (hpg-obj-fill fuel h)))
  :hints (("Goal" :induct (fill-rest l fuel h) :in-theory (enable hpg-obj-fill))))

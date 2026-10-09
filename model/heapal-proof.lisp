; Allocation (model/heapal.lisp) proved, for each pool: no slot is handed
; out twice.
;
; THE INVARIANT over a ghost list L, the free list's slots in order, and B,
; the batch's: L runs from the head through the next links to 0; every slot
; of L and of B is free (flagged), in the pool and at most `used`; and L and
; B together have no slot twice. Then:
;   hpg-%-take-safe  a take hands out L's head (and the list is L's rest)
;                    or the slot just past `used` (and L is as it was)
;   hpg-%-pop-safe   a batch pop hands out B's last, B's rest left
;   hpg-%-fill-safe  a fill moves slots from L's front, or from past
;                    `used`, onto B: the invariant holds of what is left
;   hpg-%-use-safe   using a slot in neither L nor B keeps the invariant
;   hpg-free-%-safe  the sweep's free of a slot not free puts it on L
; and so a slot handed out is in neither L nor B: nobody else gets it.
;
; One text for the three pools, as heapal's: @ is the pool's letter (o, v,
; s) and % its name (obj, vec, str).

(in-package "ACL2")

(include-book "heapal")

(in-theory (disable nth update-nth hpgp hpg-ok hpg-sw-ok hpg-al-ok))

(defthm hpg-s64-id (implies (sb64ip x) (equal (hpg-s64 x) x)) :hints (("Goal" :in-theory (enable hpg-s64))))

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

(defconst *pool-alloc-proof*
  '(
(defmacro @free (h) `(nth *h-@freei* ,h))
(defmacro @next (h) `(nth *h-@nexti* ,h))
(defmacro @used (h) `(nth *h-@used* ,h))
(defmacro @head (h) `(nth *h-@head* ,h))

; a slot that may be on the free list or in the batch: in the pool, at most
; used, flagged free
(defun @fslot (i h)
  (and (natp i) (< 0 i) (< i (len (@free h))) (< i (len (@next h)))
       (integerp (@used h)) (<= i (@used h)) (not (equal (nth i (@free h)) 0))))

(defun @fl-ok (l head h)
  (if (endp l)
      (equal head 0)
    (and (equal head (car l)) (@fslot (car l) h)
         (@fl-ok (cdr l) (nth (car l) (@next h)) h))))

(defun @all-fslot (l h) (if (endp l) t (and (@fslot (car l) h) (@all-fslot (cdr l) h))))

; the batch's slots, last first: b[k], b[k-1], .. b[1]
(defun @b-list (k h) (if (zp k) nil (cons (nth k (nth *h-@bi* h)) (@b-list (1- k) h))))

(defun @al-inv (l h)
  (and (true-listp l)
       (@fl-ok l (@head h) h)
       (@all-fslot l h)
       (@all-fslot (@b-list (nth *h-n@b* h) h) h)
       (no-duplicatesp (append l (@b-list (nth *h-n@b* h) h)))))

; ---- FRAME: WHAT THE INVARIANT READS ----

(defthm @next-elem-sb64
  (implies (and (hpgp h) (< (nfix i) (len (@next h))))
           (sb64ip (nth i (@next h))))
  :hints (("Goal" :use ((:instance hpg-@next-elem (hpg h) (j i))))))

(defthm hpg-s64-@next
  (implies (and (hpgp h) (< (nfix i) (len (@next h))))
           (equal (hpg-s64 (nth i (@next h))) (nth i (@next h))))
  :hints (("Goal" :in-theory (disable hpg-s64-id @next-elem-sb64)
           :use ((:instance hpg-s64-id (x (nth i (@next h)))) (:instance @next-elem-sb64)))))

(defthm hpg-s64-@head
  (implies (hpgp h) (equal (hpg-s64 (nth *h-@head* h)) (nth *h-@head* h)))
  :hints (("Goal" :in-theory (enable hpgp hpg-s64))))

; fields the invariant does not read, written: the pool's head, batch and
; marks, and whatever the frees of every pool write
(defmacro @frames (&rest flds)
  (cons 'progn
        (append
         (pool-frame-thms flds '@fslot '@fl-ok '@all-fslot)
         nil)))
(@frames *h-@head* *h-n@b* *h-@bi* *h-@marki* *h-okindi* *h-ofini* *h-nswo* *h-afree* *h-atagi* *h-arefi*
         *h-aivali* *h-cheadi* *h-voffi* *h-vleni* *h-nswv* *h-sreli* *h-nsws*)
(defthm @all-fslot-frame-head (equal (@all-fslot l (update-nth *h-@head* v h)) (@all-fslot l h)))

(defthm @b-list-frame
  (implies (and (natp fld) (not (equal fld *h-@bi*)))
           (equal (@b-list k (update-nth fld v h)) (@b-list k h))))

; `used` raised: what was at most used still is
(defthm @fslot-used-up
  (implies (and (@fslot i h) (integerp u) (<= (@used h) u)) (@fslot i (update-nth *h-@used* u h))))
(defthm @fl-ok-used-up
  (implies (and (@fl-ok l head h) (integerp u) (<= (@used h) u)) (@fl-ok l head (update-nth *h-@used* u h))))
(defthm @all-fslot-used-up
  (implies (and (@all-fslot l h) (integerp u) (<= (@used h) u)) (@all-fslot l (update-nth *h-@used* u h))))

; a slot's flag or link written: the slots of a list without it are as they were
(defthm @fslot-other-flag
  (implies (and (equal x (@free h)) (natp j) (< j (len (@free h))) (not (equal j i)))
           (equal (@fslot i (update-nth *h-@freei* (update-nth j v x) h)) (@fslot i h)))
  :hints (("Goal" :in-theory (enable nth update-nth))))
(defthm @fl-ok-other
  (implies (and (natp j) (not (member j l)) (< j (len (@free h))) (< j (len (@next h))))
           (and (implies (equal x (@free h))
                         (equal (@fl-ok l head (update-nth *h-@freei* (update-nth j v x) h)) (@fl-ok l head h)))
                (implies (equal x (@next h))
                         (equal (@fl-ok l head (update-nth *h-@nexti* (update-nth j v x) h)) (@fl-ok l head h)))))
  :hints (("Goal" :induct (@fl-ok l head h) :in-theory (enable nth update-nth))))
(defthm @all-fslot-other
  (implies (and (natp j) (not (member j l)) (< j (len (@free h))) (< j (len (@next h))))
           (and (implies (equal x (@free h))
                         (equal (@all-fslot l (update-nth *h-@freei* (update-nth j v x) h)) (@all-fslot l h)))
                (implies (equal x (@next h))
                         (equal (@all-fslot l (update-nth *h-@nexti* (update-nth j v x) h)) (@all-fslot l h)))))
  :hints (("Goal" :in-theory (enable nth update-nth))))

; every slot of a well-formed list is a free slot, at most used (al-inv
; carries all-fslot itself, so this stays closed)
(defthm @fl-ok-all-fslot (implies (@fl-ok l head h) (@all-fslot l h)))
(in-theory (disable @fl-ok-all-fslot))
(defthm @all-fslot-member
  (implies (and (@all-fslot l h) (member i l)) (@fslot i h)))
(defthm @all-fslot-above-used
  (implies (and (@all-fslot l h) (integerp (@used h)) (< (@used h) i)) (not (member i l))))
(defthm @all-fslot-unflagged
  (implies (and (@all-fslot l h) (natp i) (< i (len (@free h))) (equal (nth i (@free h)) 0)) (not (member i l))))

; ---- THE THEOREMS ----

(defmacro @bl (h) `(@b-list (nth *h-n@b* ,h) ,h))

; A TAKE: the list's head, the list its rest; or the slot past used, which
; is on neither the list nor in the batch
(defthm hpg-%-take-safe
  (implies (and (hpgp h) (hpg-al-ok h) (@al-inv l h))
           (let ((i (mv-nth 0 (hpg-%-take h))) (h2 (mv-nth 1 (hpg-%-take h))))
             (if (consp l)
                 (and (equal i (car l)) (@al-inv (cdr l) h2) (not (member i (append (cdr l) (@bl h2)))))
               (and (@al-inv l h2)
                    (or (equal i 0)
                        (and (equal i (+ 1 (@used h))) (not (member i (append l (@bl h2))))))))))
  :hints (("Goal" :in-theory (enable hpg-%-take) :expand ((@fl-ok l (nth *h-@head* h) h)))))

; A POP: the batch's last; the batch its rest
(defthm hpg-%-pop-safe
  (implies (and (hpg-al-ok h) (@al-inv l h) (< 0 (nth *h-n@b* h)))
           (let ((i (mv-nth 0 (hpg-%-pop h))) (h2 (mv-nth 1 (hpg-%-pop h))))
             (and (equal i (car (@bl h))) (@al-inv l h2) (not (member i (append l (@bl h2)))))))
  :hints (("Goal" :in-theory (enable hpg-%-pop) :expand ((@b-list (nth *h-n@b* h) h)))))

; USE of a slot neither on the list nor in the batch
(defthm hpg-%-use-safe
  (implies (and (@al-inv l h) (natp i) (< i (len (@free h))) (< i (len (@next h))) (< i (len (nth *h-@marki* h)))
                (not (member i (append l (@bl h)))))
           (@al-inv l (hpg-%-use i h)))
  :hints (("Goal" :in-theory (enable hpg-%-use))))

; ---- THE FILL ----

(defthm @b-list-write-above
  (implies (and (equal x (nth *h-@bi* h)) (natp k) (natp n) (< k n))
           (equal (@b-list k (update-nth *h-@bi* (update-nth n v x) h)) (@b-list k h)))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm @b-list-step
  (implies (natp k) (equal (@b-list (+ 1 k) h) (cons (nth (+ 1 k) (nth *h-@bi* h)) (@b-list k h)))))

(defthm @fl-ok-head-consp
  (implies (and (@fl-ok l head h) (not (equal head 0))) (consp l)))

; the list's head moved into the batch
(defthm hpg-%-fill-list-safe
  (implies (and (hpgp h) (hpg-al-ok h) (@al-inv l h) (< (+ 1 (nth *h-n@b* h)) (len (nth *h-@bi* h)))
                (< 0 (@head h)) (< (@head h) (len (@next h))))
           (@al-inv (cdr l) (hpg-%-fill-list h)))
  :hints (("Goal" :in-theory (enable hpg-%-fill-list) :expand ((@fl-ok l (nth *h-@head* h) h)))))

; the slot past used moved into the batch
(defthm hpg-%-fill-end-safe
  (implies (and (hpgp h) (hpg-al-ok h) (@al-inv l h) (< (+ 1 (nth *h-n@b* h)) (len (nth *h-@bi* h)))
                (< (@used h) (nth *h-@cap* h)) (< (+ 1 (@used h)) (len (@free h))) (< (+ 1 (@used h)) (len (@next h))))
           (@al-inv l (hpg-%-fill-end h)))
  :hints (("Goal" :in-theory (enable hpg-%-fill-end))))

; what is left of the list as the fill takes from its front
(defun-nx %-fill-rest (l fuel hpg)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (< (+ 1 (h-n@b hpg)) (h-@b-length hpg))))
      l
    (if (and (< 0 (h-@head hpg)) (< (h-@head hpg) (h-@next-length hpg)))
        (let ((hpg (hpg-%-fill-list hpg))) (%-fill-rest (cdr l) (- fuel 1) hpg))
      (if (and (< (h-@used hpg) (h-@cap hpg)) (< (+ 1 (h-@used hpg)) (h-@free-length hpg))
               (< (+ 1 (h-@used hpg)) (h-@next-length hpg)))
          (let ((hpg (hpg-%-fill-end hpg))) (%-fill-rest l (- fuel 1) hpg))
        l))))

; A FILL keeps the invariant: the slots it moved are the batch's, what it
; left the list
(defthm hpg-%-fill-safe
  (implies (and (hpgp h) (hpg-al-ok h) (@al-inv l h))
           (@al-inv (%-fill-rest l fuel h) (hpg-%-fill fuel h)))
  :hints (("Goal" :induct (%-fill-rest l fuel h)
           :in-theory (e/d (hpg-%-fill) (@al-inv hpg-%-fill-list hpg-%-fill-end)))))
))

; the frame theorems for a list of fields: each written, the invariant's
; three readers unchanged
(defun pool-frame-thms (flds fslot fl-ok all-fslot)
  (declare (xargs :mode :program))
  (if (endp flds)
      nil
    (let ((nm (intern-in-package-of-symbol
               (concatenate 'string (symbol-name fslot) "-FRAME-" (symbol-name (car flds))) 'hpg)))
      (cons `(defthm ,nm
               (and (equal (,fslot i (update-nth ,(car flds) v h)) (,fslot i h))
                    (equal (,fl-ok l head (update-nth ,(car flds) v h)) (,fl-ok l head h))
                    (equal (,all-fslot l (update-nth ,(car flds) v h)) (,all-fslot l h)))
               :hints (("Goal" :induct (,fl-ok l head h))))
            (pool-frame-thms (cdr flds) fslot fl-ok all-fslot)))))

(make-event (list 'for-pools *pool-alloc-proof*))

; THE SWEEP'S FREE of a slot not free: on the list's front (each pool's
; free writes what its own does: a finalizer, a run, a text released)
(defthm hpg-free-obj-safe
  (implies (and (hpgp h) (oal-inv l h) (natp i) (< 0 i) (<= i (oused h)) (integerp (oused h))
                (< i (len (ofree h))) (< i (len (onext h))) (< i (len (nth *h-okindi* h))) (< i (len (nth *h-ofini* h)))
                (equal (nth i (ofree h)) 0))
           (oal-inv (cons i l) (hpg-free-obj i h)))
  :hints (("Goal" :in-theory (enable hpg-free-obj oal-inv))))

(defthm hpg-free-vec-safe
  (implies (and (hpgp h) (val-inv l h) (natp i) (< 0 i) (<= i (vused h)) (integerp (vused h))
                (< i (len (vfree h))) (< i (len (vnext h))) (< i (len (nth *h-voffi* h))) (< i (len (nth *h-vleni* h)))
                (equal (nth i (vfree h)) 0))
           (val-inv (cons i l) (hpg-free-vec i h)))
  :hints (("Goal" :in-theory (enable hpg-free-vec hpg-slab-free val-inv))))

(defthm hpg-free-str-safe
  (implies (and (hpgp h) (sal-inv l h) (natp i) (< 0 i) (<= i (sused h)) (integerp (sused h))
                (< i (len (sfree h))) (< i (len (snext h))) (< i (len (nth *h-sreli* h)))
                (equal (nth i (sfree h)) 0))
           (sal-inv (cons i l) (hpg-free-str i h)))
  :hints (("Goal" :in-theory (enable hpg-free-str sal-inv))))

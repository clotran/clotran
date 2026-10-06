; clotran's allocator, formally (PLAN step 30): the heap stays well
; formed, and THE OLD SPACE'S OWN COLLECTION.
;
;   young-gc-heap-ok      a young collection over a good L leaves a
;                         well-formed heap: every reference in bounds,
;                         the nursery empty, no young reference anywhere
;   old-gc-invisible      a mark and a sweep change nothing the program
;                         can observe, for any marked set holding the
;                         roots' objects and closed under fields
;   free-reuse-invisible  and storing anything into a freed slot -- what
;                         reusing it for a new object does -- changes
;                         nothing either
;   mark-set-ok           the mark the collector computes is such a set
;   full-gc-invisible     a young collection, then a mark and a sweep,
;                         changes nothing
;
; The old space is collected in place, NOT moved: a reference to an old
; object stays valid for as long as the object lives, so a collection of
; the old space rewrites no reference. It runs right after a young
; collection, when the nursery is empty and no young reference exists.
; A freed object becomes nil here; in the Fortran it goes on the free
; list.

(in-package "ACL2")

(include-book "alloc")

; young-in stays itself here, not its subset form
(in-theory (disable young-in-is-subset))

; ---- A YOUNG COLLECTION KEEPS THE HEAP WELL FORMED -------------------------------

; forwarding a value the collection may meet: shaped, in bounds, and a
; young reference only into L
(defthm pos-in-below
  (implies (member-equal j l) (< (pos-in j l) (len l)))
  :rule-classes :linear)

(defthm fwd-shaped-in-bounds
  (implies (and (imm-or-ref v) (or (not (orefp v)) (< (cdr v) nold))
                (or (not (yrefp v)) (member-equal (cdr v) l)) (natp nold))
           (and (imm-or-ref (fwd v nold l))
                (or (not (orefp (fwd v nold l))) (< (cdr (fwd v nold l)) (+ nold (len l))))
                (not (yrefp (fwd v nold l)))))
  :hints (("Goal" :in-theory (enable fwd))))

(defthm fwd-vals-ok
  (implies (and (vals-shaped vs) (refs-in-bounds vs nold ny) (young-in vs l) (natp nold))
           (and (vals-shaped (fwd-vals vs nold l))
                (refs-in-bounds (fwd-vals vs nold l) (+ nold (len l)) 0)
                (true-listp (fwd-vals vs nold l))))
  :hints (("Goal" :induct (fwd-vals vs nold l) :in-theory (enable fwd))))

; an object with no young reference has every young reference in any L
(defthm no-young-young-in
  (implies (not (has-young vs)) (young-in vs l)))

; objects all of whose fields' young references are in L
(defun objs-young-in (objs l)
  (if (atom objs) t (and (young-in (car objs) l) (objs-young-in (cdr objs) l))))

; the first object that is not, if any
(defun bad-young (objs l)
  (cond ((atom objs) 0)
        ((not (young-in (car objs) l)) 0)
        (t (1+ (bad-young (cdr objs) l)))))

(defthm bad-young-is-bad
  (implies (not (objs-young-in objs l))
           (and (< (bad-young objs l) (len objs))
                (not (young-in (nth (bad-young objs l) objs) l))))
  :rule-classes nil)

(defthm fwd-objs-ok
  (implies (and (objs-ok objs no ny) (objs-young-in objs l) (natp no))
           (objs-ok (fwd-objs objs no l) (+ no (len l)) 0)))

(defthm objs-ok-append
  (equal (objs-ok (append a b) no ny) (and (objs-ok a no ny) (objs-ok b no ny))))

(defthm objs-ok-copies
  (implies (and (objs-ok (st-young st) no ny) (subsetp-equal lrest l) (all-below lrest (len (st-young st)))
                (closed-ok l st) (natp no))
           (objs-ok (copies lrest l (st-young st) no) (+ no (len l)) 0))
  :hints (("Goal" :induct (copies lrest l (st-young st) no) :in-theory (disable closed-ok-necc objs-ok-nth fwd-vals-ok))
          ("Subgoal *1/2" :use ((:instance closed-ok-necc (i (car lrest)))
                                (:instance objs-ok-nth (objs (st-young st)) (i (car lrest)))
                                (:instance fwd-vals-ok (vs (nth (car lrest) (st-young st))) (nold no))))))

; the old space: a remembered object's young references are in L
; (closed-ok), an unremembered one has none (the barrier)
(defthm old-young-in
  (implies (and (barrier-ok st) (closed-ok l st))
           (objs-young-in (st-old st) l))
  :hints (("Goal" :use ((:instance bad-young-is-bad (objs (st-old st)))
                        (:instance closed-ok-necc (i (bad-young (st-old st) l)))
                        (:instance barrier-ok-necc (i (bad-young (st-old st) l)))))))

(defthm true-listp-copies (true-listp (copies lrest l young nold)))

; THE YOUNG COLLECTION KEEPS THE HEAP WELL FORMED: every object and root
; shaped and in bounds in the new old space, the nursery empty
(defthm young-gc-heap-ok
  (implies (and (heap-ok st) (l-ok l st))
           (heap-ok (young-gc l st)))
  :hints (("Goal" :in-theory (e/d (heap-ok l-ok young-gc) (barrier-ok-barrier2 fwd-vals-ok fwd-objs-ok old-young-in young-gc-barrier))
                  :use ((:instance objs-ok-copies (lrest l) (no (len (st-old st)))
                                   (ny (len (st-young st))))
                        (:instance young-gc-barrier)
                        (:instance old-young-in)
                        (:instance fwd-vals-ok (vs (st-roots st)) (nold (len (st-old st))) (ny (len (st-young st))))
                        (:instance fwd-objs-ok (objs (st-old st)) (no (len (st-old st))) (ny (len (st-young st))))))))

; ---- THE OLD SPACE'S COLLECTION: A MARK AND A SWEEP ------------------------------

; the old objects a list of values references
(defun old-refs (vs)
  (cond ((atom vs) nil)
        ((orefp (car vs)) (cons (cdr (car vs)) (old-refs (cdr vs))))
        (t (old-refs (cdr vs)))))

; a value the marked set M covers
(defun in-m (v m) (or (not (orefp v)) (member-equal (cdr v) m)))

; M is closed: a marked object's old references are marked
(defun-sk m-closed (m old)
  (forall i (implies (member-equal i m) (subsetp-equal (old-refs (nth i old)) m))))
(in-theory (disable m-closed))

; what M must hold: the roots' objects, closed under fields
(defun m-ok (m st)
  (and (subsetp-equal (old-refs (st-roots st)) m) (m-closed m (st-old st))))

; THE SWEEP: every unmarked object freed, every marked one where it was
(defun sweep (old m i)
  (if (atom old) nil (cons (if (member-equal i m) (car old) nil) (sweep (cdr old) m (1+ i)))))

(defun old-gc (m st) (mk-st (sweep (st-old st) m 0) (st-young st) (st-rem st) (st-roots st)))

; two old spaces alike on M
(defun-sk agree-on (m a b) (forall i (implies (member-equal i m) (equal (nth i a) (nth i b)))))
(in-theory (disable agree-on))

(defthm old-refs-nth
  (implies (orefp (nth k vs)) (member-equal (cdr (nth k vs)) (old-refs vs))))

(defthm in-m-field
  (implies (and (m-closed m old) (member-equal i m)) (in-m (nth k (nth i old)) m))
  :hints (("Goal" :in-theory (disable m-closed-necc old-refs-nth member-subsetp)
                  :use ((:instance m-closed-necc)
                        (:instance old-refs-nth (vs (nth i old)))
                        (:instance member-subsetp (x (cdr (nth k (nth i old)))) (a (old-refs (nth i old))) (b m))))))

(defthm in-m-atom (implies (atom v) (in-m v m)))
(in-theory (disable in-m))

; a reference M covers names the same object in both
(defthm deref-agree
  (implies (and (in-m v m) (agree-on m (st-old st) (st-old st2)) (equal (st-young st2) (st-young st)))
           (equal (deref v st2) (deref v st)))
  :hints (("Goal" :in-theory (enable deref in-m) :use ((:instance agree-on-necc (i (cdr v)) (a (st-old st)) (b (st-old st2)))))))

; and its fields are covered too: an old one's by closure; a young one
; has none, the nursery being empty
(defthm in-m-deref-field
  (implies (and (in-m v m) (m-closed m (st-old st)) (atom (st-young st)))
           (in-m (nth k (deref v st)) m))
  :hints (("Goal" :in-theory (e/d (deref) (in-m-field))
                  :cases ((orefp v))
                  :use ((:instance in-m-field (i (cdr v)) (old (st-old st)))))
          ("Subgoal 1" :in-theory (enable deref in-m))))

; WHAT M DOES NOT HOLD CANNOT BE OBSERVED: two heaps alike on a closed M
; read the same along every path from a value M covers
(defthm obs-agree
  (implies (and (m-closed m (st-old st)) (agree-on m (st-old st) (st-old st2))
                (equal (st-young st2) (st-young st)) (atom (st-young st)) (in-m v m))
           (equal (obs v path st2) (obs v path st)))
  :hints (("Goal" :induct (obs v path st) :in-theory (disable in-m))))

(defun sw-ind (i old k)
  (if (or (atom old) (zp i)) (list i old k) (sw-ind (1- i) (cdr old) (1+ k))))

(defthm nth-sweep
  (implies (and (natp i) (natp k))
           (equal (nth i (sweep old m k))
                  (if (member-equal (+ k i) m) (nth i old) nil)))
  :hints (("Goal" :induct (sw-ind i old k) :expand ((sweep old m k)))))

(defthm agree-sweep
  (implies (all-below m (len old)) (agree-on m old (sweep old m 0)))
  :hints (("Goal" :in-theory (e/d (agree-on) (sweep member-all-below))
                  :use ((:instance member-all-below (l m) (n (len old)) (j (agree-on-witness m old (sweep old m 0))))))))

(defthm agree-write-free
  (implies (and (natp i) (not (member-equal i m)) (all-below m n)) (agree-on m old (update-nth i x old)))
  :hints (("Goal" :in-theory (e/d (agree-on) (member-all-below))
                  :use ((:instance member-all-below (l m) (j (agree-on-witness m old (update-nth i x old))))))))

(defthm in-m-root
  (implies (subsetp-equal (old-refs roots) m) (in-m (nth r roots) m))
  :hints (("Goal" :in-theory (e/d (in-m) (old-refs-nth)) :use ((:instance old-refs-nth (vs roots) (k r))))))

; THE MARK AND SWEEP IS INVISIBLE
(defthm old-gc-invisible
  (implies (and (m-ok m st) (all-below m (len (st-old st))) (atom (st-young st)))
           (equal (obs (nth r (st-roots (old-gc m st))) path (old-gc m st))
                  (obs (nth r (st-roots st)) path st)))
  :hints (("Goal" :in-theory (disable obs-agree agree-sweep in-m)
                  :use ((:instance obs-agree (v (nth r (st-roots st))) (st2 (old-gc m st)))
                        (:instance agree-sweep (old (st-old st)))))))

; AND SO IS REUSING A FREED SLOT: store anything there, and nothing
; reachable sees it
(defthm free-reuse-invisible
  (implies (and (m-ok m st) (all-below m (len (st-old st))) (atom (st-young st)) (natp i) (not (member-equal i m)))
           (equal (obs (nth r (st-roots st)) path
                       (mk-st (update-nth i x (st-old st)) (st-young st) (st-rem st) (st-roots st)))
                  (obs (nth r (st-roots st)) path st)))
  :hints (("Goal" :in-theory (disable obs-agree agree-write-free in-m)
                  :use ((:instance obs-agree (v (nth r (st-roots st)))
                                   (st2 (mk-st (update-nth i x (st-old st)) (st-young st) (st-rem st) (st-roots st))))
                        (:instance agree-write-free (old (st-old st)) (n (len (st-old st))))))))

; the sweep keeps M good, so a freed slot of the swept heap may be reused
(defthm old-gc-m-ok
  (implies (and (m-ok m st) (all-below m (len (st-old st))))
           (m-ok m (old-gc m st)))
  :hints (("Goal" :expand ((m-closed m (sweep (st-old st) m 0)))
                  :use ((:instance m-closed-necc (old (st-old st)) (i (m-closed-witness m (sweep (st-old st) m 0))))))))

; ---- THE MARK, computed -----------------------------------------------------------
;
; A worklist from the roots' old references, as the young collection's
; L is (alloc.lisp's reach), with fuel; when the fuel runs out every
; old object is marked, which frees nothing and is always safe.

; (mv done M)
(defun mark (todo m old fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) (mv nil m))
        ((atom todo) (mv t m))
        ((member-equal (car todo) m) (mark (cdr todo) m old (1- fuel)))
        (t (mark (append (old-refs (nth (car todo) old)) (cdr todo)) (cons (car todo) m) old (1- fuel)))))

; enough for every root and every field of every object to be taken once
(defun field-count (objs) (if (atom objs) 0 (+ (len (car objs)) (field-count (cdr objs)))))
(defun mark-fuel (st) (+ 1 (len (st-roots st)) (len (st-old st)) (field-count (st-old st))))

(defun mark-set (st)
  (mv-let (done m) (mark (old-refs (st-roots st)) nil (st-old st) (mark-fuel st))
    (if done m (count-to (len (st-old st))))))

; every member's old references are marked or still to do
(defun m-members-closed (ls m todo old)
  (if (atom ls)
      t
    (and (subsetp-equal (old-refs (nth (car ls) old)) (append m todo))
         (m-members-closed (cdr ls) m todo old))))

(defthm m-members-closed-more
  (implies (and (m-members-closed ls m todo old) (subsetp-equal (append m todo) (append m2 todo2)))
           (m-members-closed ls m2 todo2 old))
  :hints (("Goal" :induct (m-members-closed ls m todo old))))

(defthm m-members-closed-member
  (implies (and (m-members-closed ls m todo old) (member-equal j ls))
           (subsetp-equal (old-refs (nth j old)) (append m todo))))

(defthm mark-closed
  (implies (and (m-members-closed m m todo old) (subsetp-equal start (append m todo)) (true-listp m)
                (mv-nth 0 (mark todo m old fuel)))
           (and (m-members-closed (mv-nth 1 (mark todo m old fuel)) (mv-nth 1 (mark todo m old fuel)) nil old)
                (subsetp-equal start (mv-nth 1 (mark todo m old fuel)))
                (true-listp (mv-nth 1 (mark todo m old fuel)))))
  :hints (("Goal" :induct (mark todo m old fuel))))

(defthm refs-old-below
  (implies (refs-in-bounds vs no ny) (all-below (old-refs vs) no)))
(defthm objs-old-below
  (implies (objs-ok objs no ny) (all-below (old-refs (nth j objs)) no))
  :hints (("Goal" :cases ((< (nfix j) (len objs))))
          ("Subgoal 1" :in-theory (disable objs-ok-nth) :use ((:instance objs-ok-nth (i (nfix j)))))))

; the mark holds only old objects
(defthm mark-below
  (implies (and (all-below m n) (all-below todo n) (objs-ok old n ny))
           (all-below (mv-nth 1 (mark todo m old fuel)) n))
  :hints (("Goal" :induct (mark todo m old fuel))))

(defthm m-ok-from-members
  (implies (and (m-members-closed m m nil (st-old st)) (subsetp-equal (old-refs (st-roots st)) m) (true-listp m))
           (m-ok m st))
  :hints (("Goal" :expand ((m-closed m (st-old st)))
                  :use ((:instance m-members-closed-member (ls m) (todo nil) (old (st-old st))
                                   (j (m-closed-witness m (st-old st))))))))

(defthm mark-set-finished
  (implies (and (heap-ok st)
                (mv-nth 0 (mark (old-refs (st-roots st)) nil (st-old st) (mark-fuel st))))
           (let ((m (mv-nth 1 (mark (old-refs (st-roots st)) nil (st-old st) (mark-fuel st)))))
             (and (m-ok m st) (all-below m (len (st-old st))))))
  :hints (("Goal" :in-theory (e/d (heap-ok) (mark-closed mark-below m-ok m-ok-from-members mark-fuel))
                  :use ((:instance mark-closed (m nil) (todo (old-refs (st-roots st))) (start (old-refs (st-roots st)))
                                   (old (st-old st)) (fuel (mark-fuel st)))
                        (:instance mark-below (m nil) (todo (old-refs (st-roots st))) (old (st-old st)) (fuel (mark-fuel st))
                                   (n (len (st-old st))) (ny (len (st-young st))))
                        (:instance m-ok-from-members
                                   (m (mv-nth 1 (mark (old-refs (st-roots st)) nil (st-old st) (mark-fuel st)))))))))

(defthm mark-set-fallback
  (implies (heap-ok st)
           (and (m-ok (count-to (len (st-old st))) st) (all-below (count-to (len (st-old st))) (len (st-old st)))))
  :hints (("Goal" :in-theory (enable heap-ok)
                  :expand ((m-closed (count-to (len (st-old st))) (st-old st)))
                  :use ((:instance objs-old-below (objs (st-old st)) (no (len (st-old st))) (ny (len (st-young st)))
                                   (j (m-closed-witness (count-to (len (st-old st))) (st-old st))))))))

; THE MARK IS ALWAYS GOOD: holding the roots' objects, closed, old
(defthm mark-set-ok
  (implies (heap-ok st)
           (and (m-ok (mark-set st) st) (all-below (mark-set st) (len (st-old st)))))
  :hints (("Goal" :in-theory (disable mark-set-finished mark-set-fallback m-ok mark-fuel)
                  :use (mark-set-finished mark-set-fallback))))

; ---- THE FULL COLLECTION ---------------------------------------------------------

; a young collection, then the old space's mark and sweep over the heap
; it leaves -- the nursery empty, every reference old
(defun full-gc (st)
  (let ((st1 (young-gc-alg (live-set st) st)))
    (old-gc (mark-set st1) st1)))

(defthm young-gc-nursery-empty
  (equal (st-young (young-gc l st)) nil)
  :hints (("Goal" :in-theory (enable young-gc))))

(defthm young-gc-roots
  (equal (st-roots (young-gc l st)) (fwd-vals (st-roots st) (len (st-old st)) l))
  :hints (("Goal" :in-theory (enable young-gc))))

(defthm old-gc-roots (equal (st-roots (old-gc m st)) (st-roots st)))

; THE FULL COLLECTION IS INVISIBLE: every path from every root reads the
; same after a young collection and a mark and sweep as before
(defthm full-gc-invisible
  (implies (and (heap-ok st) (rem-ok st))
           (equal (obs (nth r (st-roots (full-gc st))) path (full-gc st))
                  (obs (nth r (st-roots st)) path st)))
  :hints (("Goal" :in-theory (e/d (full-gc)
                                  (old-gc-invisible collection-invisible mark-set-ok young-gc-heap-ok live-set-ok
                                   alg-is-spec old-gc mark-set live-set young-gc-roots old-gc-roots))
                  :use ((:instance alg-is-spec (l (live-set st)))
                        (:instance live-set-ok)
                        (:instance young-gc-heap-ok (l (live-set st)))
                        (:instance mark-set-ok (st (young-gc (live-set st) st)))
                        (:instance old-gc-invisible (m (mark-set (young-gc (live-set st) st)))
                                   (st (young-gc (live-set st) st)))
                        (:instance old-gc-roots (m (mark-set (young-gc (live-set st) st)))
                                   (st (young-gc (live-set st) st)))
                        (:instance collection-invisible)))))

; ---- ITS COST --------------------------------------------------------------------
;
; The mark's steps, as the young worklist's: its starts and the old
; references of what it marked -- the live objects. The sweep visits
; every old object once, live or not: a mark and a sweep is linear in
; the old space, which is why the young collection exists. It runs
; often and never pays that.

(defun mark-steps (todo m old fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) 0)
        ((atom todo) 0)
        ((member-equal (car todo) m) (1+ (mark-steps (cdr todo) m old (1- fuel))))
        (t (1+ (mark-steps (append (old-refs (nth (car todo) old)) (cdr todo))
                           (cons (car todo) m) old (1- fuel))))))

; the old references the members of m hold
(defun or-sum (m old)
  (if (atom m) 0 (+ (len (old-refs (nth (car m) old))) (or-sum (cdr m) old))))

(defthm mark-steps-exact
  (implies (mv-nth 0 (mark todo m old fuel))
           (equal (mark-steps todo m old fuel)
                  (+ (len todo) (- (or-sum (mv-nth 1 (mark todo m old fuel)) old) (or-sum m old))))))

(defun old-gc-steps (st)
  (+ (mark-steps (old-refs (st-roots st)) nil (st-old st) (mark-fuel st))
     (len (st-old st))))

(defthm len-old-refs (<= (len (old-refs vs)) (len vs)) :rule-classes :linear)
(defthm or-sum-fields (<= (or-sum m old) (fields-of m old)) :rule-classes :linear)
(defthm or-sum-natp (<= 0 (or-sum m old)) :rule-classes :linear)

; THE COST: the roots, the marked objects' fields, and one step per old
; object for the sweep
(defthm old-gc-cost
  (implies (mv-nth 0 (mark (old-refs (st-roots st)) nil (st-old st) (mark-fuel st)))
           (<= (old-gc-steps st)
               (+ (len (st-roots st)) (fields-of (mark-set st) (st-old st)) (len (st-old st)))))
  :hints (("Goal" :in-theory (disable mark mark-fuel))))

; clotran's allocator, formally (PLAN step 30, the runtime; James
; 2026-10-05: "we definitely want to also model our allocator"). The
; design before the Fortran, as the VM's was: a nursery filled by
; bumping, a moving young collector, a write barrier and its remembered
; set -- and the theorem that makes the rest safe:
;
;   gc-invisible   a young collection changes nothing the program can
;                  observe: every path of fields from every root reads
;                  the same after as before
;
; THE HEAP has two spaces. The old space is a list of objects, the
; nursery another; an object is the list of its fields; a field or a
; root is a value, an immediate (an atom) or a reference (:o . i) /
; (:y . j) into a space. Allocation appends to the nursery -- a bump,
; O(1) in the thing modelled (the list's walk is the logic's, as nth's
; is in the VM books).
;
; THE BARRIER: storing a young reference into an old object records the
; object in the remembered set. Its invariant -- every old object that
; holds a young reference is remembered -- is what lets a young
; collection look at the roots, the remembered objects and the nursery,
; and never at the rest of the old space (fwd-unremembered).
;
; THE COLLECTION copies a set L of nursery objects to the end of the
; old space and rewrites every reference through the forwarding map:
; the copies' fields, the remembered objects' fields, the roots. The
; theorem holds for ANY L that holds every young object a root or a
; remembered object references and is closed under young fields;
; everything else in the nursery is garbage and goes with it.
;
; Below: L computed (live-set-ok), the collector that touches only the
; remembered objects (alg-is-spec) and its cost (alg-cost).
; model/alloc-old.lisp: the heap stays well formed, and the old space's
; own collection. Owed: several threads' nurseries.

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

; ---- VALUES AND THE HEAP ---------------------------------------------------------

(defun oref (i) (cons :o i))
(defun yref (j) (cons :y j))
(defun orefp (v) (and (consp v) (eq (car v) :o) (natp (cdr v))))
(defun yrefp (v) (and (consp v) (eq (car v) :y) (natp (cdr v))))
(defun imm-or-ref (v) (or (atom v) (orefp v) (yrefp v)))

; a state: (old young remset roots)
(defun st-old (st) (car st))
(defun st-young (st) (cadr st))
(defun st-rem (st) (caddr st))
(defun st-roots (st) (cadddr st))
(defun mk-st (old young rem roots) (list old young rem roots))
(defthm st-of-mk-st
  (and (equal (st-old (mk-st a b c d)) a) (equal (st-young (mk-st a b c d)) b)
       (equal (st-rem (mk-st a b c d)) c) (equal (st-roots (mk-st a b c d)) d)))
(in-theory (disable st-old st-young st-rem st-roots mk-st))

; the object a reference names
(defun deref (v st)
  (cond ((orefp v) (nth (cdr v) (st-old st)))
        ((yrefp v) (nth (cdr v) (st-young st)))
        (t nil)))

; WHAT THE PROGRAM CAN OBSERVE: from a value, a path of field indices;
; at its end an immediate reads as itself and a reference as :obj and
; its field count. Two heaps that agree on every path from every root
; are the same graph, wherever its objects sit.
(defun obs (v path st)
  (declare (xargs :measure (len path)))
  (cond ((not (or (orefp v) (yrefp v))) (if (atom path) v :none))
        ((atom path) (list :obj (len (deref v st))))
        (t (obs (nth (nfix (car path)) (deref v st)) (cdr path) st))))

; ---- THE INVARIANTS ---------------------------------------------------------------

(defun vals-shaped (vs)
  (if (atom vs) t (and (imm-or-ref (car vs)) (vals-shaped (cdr vs)))))
(defun refs-in-bounds (vs nold nyoung)
  (if (atom vs)
      t
    (and (or (not (orefp (car vs))) (< (cdr (car vs)) nold))
         (or (not (yrefp (car vs))) (< (cdr (car vs)) nyoung))
         (refs-in-bounds (cdr vs) nold nyoung))))
(defun objs-ok (objs nold nyoung)
  (if (atom objs)
      t
    (and (true-listp (car objs)) (vals-shaped (car objs)) (refs-in-bounds (car objs) nold nyoung)
         (objs-ok (cdr objs) nold nyoung))))

(defun has-young (vs)
  (if (atom vs) nil (or (yrefp (car vs)) (has-young (cdr vs)))))

; THE BARRIER'S INVARIANT: an old object holding a young reference is
; remembered
(defun-sk barrier-ok (st)
  (forall i (implies (and (natp i) (< i (len (st-old st))) (has-young (nth i (st-old st))))
                     (member-equal i (st-rem st)))))
(in-theory (disable barrier-ok))

(defun heap-ok (st)
  (let ((no (len (st-old st))) (ny (len (st-young st))))
    (and (true-listp (st-old st)) (true-listp (st-young st))
         (objs-ok (st-old st) no ny) (objs-ok (st-young st) no ny)
         (vals-shaped (st-roots st)) (refs-in-bounds (st-roots st) no ny)
         (barrier-ok st))))

; ---- THE MUTATOR'S OPERATIONS -------------------------------------------------

; allocate: a bump; the new object's reference is the mutator's, a root
(defun alloc (fields st)
  (mk-st (st-old st) (append (st-young st) (list fields)) (st-rem st)
         (append (st-roots st) (list (yref (len (st-young st)))))))

; store v into field k of the object root r names, with THE BARRIER
(defun write-field (r k v st)
  (let ((x (nth r (st-roots st))))
    (cond ((orefp x)
           (mk-st (update-nth (cdr x) (update-nth k v (nth (cdr x) (st-old st))) (st-old st))
                  (st-young st)
                  (if (yrefp v) (cons (cdr x) (st-rem st)) (st-rem st))
                  (st-roots st)))
          ((yrefp x)
           (mk-st (st-old st)
                  (update-nth (cdr x) (update-nth k v (nth (cdr x) (st-young st))) (st-young st))
                  (st-rem st) (st-roots st)))
          (t st))))

; ---- THE YOUNG COLLECTION ---------------------------------------------------------

; where nursery object j goes: the old space's length plus j's place in L
(defun pos-in (j l)
  (cond ((atom l) 0)
        ((equal j (car l)) 0)
        (t (1+ (pos-in j (cdr l))))))

(defun fwd (v nold l)
  (if (yrefp v) (oref (+ nold (pos-in (cdr v) l))) v))

(defun fwd-vals (vs nold l)
  (if (atom vs) nil (cons (fwd (car vs) nold l) (fwd-vals (cdr vs) nold l))))

(defun fwd-objs (objs nold l)
  (if (atom objs) nil (cons (fwd-vals (car objs) nold l) (fwd-objs (cdr objs) nold l))))

; the copies of L's members, in L's order
(defun copies (lrest l young nold)
  (if (atom lrest)
      nil
    (cons (fwd-vals (nth (car lrest) young) nold l) (copies (cdr lrest) l young nold))))

; THE YOUNG COLLECTION over L: the old space's objects with their young
; references forwarded (only the remembered ones have any:
; fwd-unremembered), then the copies; the nursery and the remembered set
; empty; the roots forwarded
(defun young-gc (l st)
  (let ((nold (len (st-old st))))
    (mk-st (append (fwd-objs (st-old st) nold l) (copies l l (st-young st) nold))
           nil nil
           (fwd-vals (st-roots st) nold l))))

; what L must hold: every young object a root or a remembered object
; references, and every young object a member references
(defun young-in (vs l)
  (if (atom vs) t (and (or (not (yrefp (car vs))) (member-equal (cdr (car vs)) l)) (young-in (cdr vs) l))))

(defun-sk closed-ok (l st)
  (forall i (and (implies (member-equal i (st-rem st)) (young-in (nth i (st-old st)) l))
                 (implies (member-equal i l) (young-in (nth i (st-young st)) l)))))
(in-theory (disable closed-ok))

; L's members are nursery objects
(defun all-below (l n)
  (if (atom l) t (and (natp (car l)) (< (car l) n) (all-below (cdr l) n))))

(defun l-ok (l st)
  (and (true-listp l) (all-below l (len (st-young st))) (young-in (st-roots st) l) (closed-ok l st)))

(defthm member-all-below
  (implies (and (all-below l n) (member-equal j l)) (and (natp j) (< j n))))

; ---- LEMMAS: the lists ------------------------------------------------------------

(defthm nth-fwd-vals
  (equal (nth k (fwd-vals vs nold l)) (fwd (nth k vs) nold l)))
(defthm len-fwd-vals (equal (len (fwd-vals vs nold l)) (len vs)))
(defthm nth-fwd-objs
  (equal (nth i (fwd-objs objs nold l)) (fwd-vals (nth i objs) nold l)))
(defthm len-fwd-objs (equal (len (fwd-objs objs nold l)) (len objs)))
(defthm len-copies (equal (len (copies lrest l young nold)) (len lrest)))

(defthm nth-append-low
  (implies (and (natp i) (< i (len a))) (equal (nth i (append a b)) (nth i a))))
(defthm len-zero-atom (equal (equal (len x) 0) (not (consp x))))
(defun nah-ind (i a)
  (if (or (zp i) (atom a)) (list i a) (nah-ind (1- i) (cdr a))))
(defthm nth-append-high
  (implies (and (natp i) (<= (len a) i)) (equal (nth i (append a b)) (nth (- i (len a)) b)))
  :hints (("Goal" :induct (nah-ind i a))))

(defthm nth-copies
  (implies (member-equal j lrest)
           (equal (nth (pos-in j lrest) (copies lrest l young nold))
                  (fwd-vals (nth j young) nold l))))

; a young reference's forwarding lands on its copy
(defthm deref-fwd-young
  (implies (and (yrefp v) (member-equal (cdr v) l) (true-listp old))
           (equal (nth (+ (len old) (pos-in (cdr v) l))
                       (append (fwd-objs old (len old) l) (copies l l young (len old))))
                  (fwd-vals (nth (cdr v) young) (len old) l)))
  :hints (("Goal" :in-theory (disable nth-append-high nth-copies)
                  :use ((:instance nth-append-high (i (+ (len old) (pos-in (cdr v) l)))
                                   (a (fwd-objs old (len old) l)) (b (copies l l young (len old))))
                        (:instance nth-copies (j (cdr v)) (lrest l) (nold (len old)))))))

; the fields of a shaped, bounded object
(defthm nth-shaped
  (implies (vals-shaped vs) (imm-or-ref (nth k vs))))
(defthm nth-in-bounds
  (implies (refs-in-bounds vs no ny)
           (and (implies (orefp (nth k vs)) (< (cdr (nth k vs)) no))
                (implies (yrefp (nth k vs)) (< (cdr (nth k vs)) ny)))))
(defthm nth-young-in
  (implies (and (young-in vs l) (yrefp (nth k vs))) (member-equal (cdr (nth k vs)) l)))
(defthm objs-ok-nth
  (implies (and (objs-ok objs no ny) (natp i) (< i (len objs)))
           (and (vals-shaped (nth i objs)) (refs-in-bounds (nth i objs) no ny) (true-listp (nth i objs)))))

(defthm has-young-nth
  (implies (and (yrefp (nth k vs)) (natp k)) (has-young vs)))

; THE BARRIER AT WORK: an object the barrier never recorded has no young
; reference, so forwarding leaves it as it is -- a young collection
; touches the remembered objects and no other old one
(defthm fwd-no-young
  (implies (and (not (has-young vs)) (true-listp vs))
           (equal (fwd-vals vs nold l) vs)))

(defthm fwd-unremembered
  (implies (and (barrier-ok st) (natp i) (< i (len (st-old st))) (true-listp (nth i (st-old st)))
                (not (member-equal i (st-rem st))))
           (equal (fwd-vals (nth i (st-old st)) nold l) (nth i (st-old st))))
  :hints (("Goal" :use ((:instance barrier-ok-necc)))))

; ---- THE THEOREM ----------------------------------------------------------------

; a value the collection must keep meaning the same: an immediate, an
; old reference in bounds, or a young reference into L
(defun good-v (v st l)
  (and (imm-or-ref v)
       (or (not (orefp v)) (< (cdr v) (len (st-old st))))
       (or (not (yrefp v)) (member-equal (cdr v) l))))

(defun obs-ind (v path st l)
  (declare (xargs :measure (len path)))
  (cond ((not (or (orefp v) (yrefp v))) (list v path st l))
        ((atom path) nil)
        (t (obs-ind (nth (nfix (car path)) (deref v st)) (cdr path) st l))))

; a field of an object a good value names is good: an old object's young
; fields are in L because the barrier remembered it; a copied object's
; because L is closed
(defthm good-field-old
  (implies (and (heap-ok st) (l-ok l st) (orefp v) (< (cdr v) (len (st-old st))))
           (good-v (nth k (nth (cdr v) (st-old st))) st l))
  :hints (("Goal" :in-theory (disable objs-ok-nth nth-shaped nth-in-bounds nth-young-in has-young-nth
                                      barrier-ok-necc closed-ok-necc objs-ok young-in vals-shaped refs-in-bounds)
                  :use ((:instance objs-ok-nth (objs (st-old st)) (i (cdr v)) (no (len (st-old st))) (ny (len (st-young st))))
                        (:instance nth-shaped (vs (nth (cdr v) (st-old st))))
                        (:instance nth-in-bounds (vs (nth (cdr v) (st-old st))) (no (len (st-old st))) (ny (len (st-young st))))
                        (:instance has-young-nth (vs (nth (cdr v) (st-old st))) (k (nfix k)))
                        (:instance barrier-ok-necc (i (cdr v)))
                        (:instance closed-ok-necc (i (cdr v)))
                        (:instance nth-young-in (vs (nth (cdr v) (st-old st))))))))

(defthm good-field-young
  (implies (and (heap-ok st) (l-ok l st) (yrefp v) (member-equal (cdr v) l))
           (good-v (nth k (nth (cdr v) (st-young st))) st l))
  :hints (("Goal" :in-theory (disable objs-ok-nth nth-shaped nth-in-bounds nth-young-in member-all-below
                                      closed-ok-necc objs-ok young-in vals-shaped refs-in-bounds)
                  :use ((:instance member-all-below (j (cdr v)) (n (len (st-young st))))
                        (:instance objs-ok-nth (objs (st-young st)) (i (cdr v)) (no (len (st-old st))) (ny (len (st-young st))))
                        (:instance nth-shaped (vs (nth (cdr v) (st-young st))))
                        (:instance nth-in-bounds (vs (nth (cdr v) (st-young st))) (no (len (st-old st))) (ny (len (st-young st))))
                        (:instance closed-ok-necc (i (cdr v)))
                        (:instance nth-young-in (vs (nth (cdr v) (st-young st))))))))

(defthm good-field
  (implies (and (heap-ok st) (l-ok l st) (good-v v st l) (or (orefp v) (yrefp v)))
           (good-v (nth k (deref v st)) st l))
  :hints (("Goal" :in-theory (disable good-field-old good-field-young heap-ok l-ok good-v)
                  :use (good-field-old good-field-young)
                  :expand ((good-v v st l) (deref v st)))))

(defthm fwd-imm (implies (not (yrefp v)) (equal (fwd v nold l) v)))
(defthm fwd-ref
  (implies (and (or (orefp v) (yrefp v)) (natp nold)) (orefp (fwd v nold l))))
(defthm fwd-not-yref (implies (natp nold) (not (yrefp (fwd v nold l)))))

; ONE STEP: in the collected heap a good reference's forwarded self
; names its object's fields, forwarded
(defthm deref-gc
  (implies (and (heap-ok st) (l-ok l st) (good-v v st l) (or (orefp v) (yrefp v)))
           (equal (deref (fwd v (len (st-old st)) l) (young-gc l st))
                  (fwd-vals (deref v st) (len (st-old st)) l)))
  :hints (("Goal" :in-theory (disable deref-fwd-young)
                  :use ((:instance deref-fwd-young (old (st-old st)) (young (st-young st)))))))

(defthm deref-gc-old
  (implies (and (heap-ok st) (l-ok l st) (orefp v) (< (cdr v) (len (st-old st))))
           (equal (deref v (young-gc l st)) (fwd-vals (deref v st) (len (st-old st)) l)))
  :hints (("Goal" :in-theory (disable deref-gc) :use ((:instance deref-gc)))))
(defthm deref-gc-young
  (implies (and (heap-ok st) (l-ok l st) (yrefp v) (member-equal (cdr v) l))
           (equal (deref (fwd v (len (st-old st)) l) (young-gc l st)) (fwd-vals (deref v st) (len (st-old st)) l)))
  :hints (("Goal" :in-theory (disable deref-gc) :use ((:instance deref-gc)))))
(in-theory (disable deref-gc))

; the first field, as the prover writes (nth 0 x)
(defthm good-field-car
  (implies (and (heap-ok st) (l-ok l st) (good-v v st l) (or (orefp v) (yrefp v)))
           (good-v (car (deref v st)) st l))
  :hints (("Goal" :in-theory (disable good-field good-v) :use ((:instance good-field (k 0))))))

(defthm good-v-old-bound
  (implies (and (good-v v st l) (orefp v)) (< (cdr v) (len (st-old st)))))
(defthm good-v-young-member
  (implies (and (good-v v st l) (yrefp v)) (member-equal (cdr v) l)))

(in-theory (disable fwd young-gc deref heap-ok l-ok))

; THE COLLECTION KEEPS WHAT A GOOD VALUE MEANS: every path from it reads
; the same in the collected heap from its forwarded self
(defthm obs-fwd
  (implies (and (heap-ok st) (l-ok l st) (good-v v st l))
           (equal (obs (fwd v (len (st-old st)) l) path (young-gc l st))
                  (obs v path st)))
  :hints (("Goal" :induct (obs-ind v path st l) :in-theory (disable good-v)
                  :expand ((obs v path (young-gc l st)) (obs (fwd v (len (st-old st)) l) path (young-gc l st))
                           (obs v path st)))))

(defthm roots-of-young-gc
  (equal (st-roots (young-gc l st)) (fwd-vals (st-roots st) (len (st-old st)) l))
  :hints (("Goal" :in-theory (enable young-gc))))

(defthm nth-roots-good
  (implies (and (vals-shaped vs) (refs-in-bounds vs no ny) (young-in vs l))
           (and (imm-or-ref (nth r vs))
                (implies (orefp (nth r vs)) (< (cdr (nth r vs)) no))
                (implies (yrefp (nth r vs)) (member-equal (cdr (nth r vs)) l)))))

(defthm roots-good
  (implies (and (heap-ok st) (l-ok l st)) (good-v (nth r (st-roots st)) st l))
  :hints (("Goal" :in-theory (e/d (heap-ok l-ok) (nth-roots-good))
                  :use ((:instance nth-roots-good (vs (st-roots st)) (no (len (st-old st))) (ny (len (st-young st))))))))

; THE THEOREM: A YOUNG COLLECTION IS INVISIBLE. Every path of fields from
; every root reads the same after it as before, so long as the heap was
; well formed with the barrier's invariant, and L holds the young objects
; the roots and the remembered objects reach
(defthm gc-invisible
  (implies (and (heap-ok st) (l-ok l st))
           (equal (obs (nth r (st-roots (young-gc l st))) path (young-gc l st))
                  (obs (nth r (st-roots st)) path st)))
  :hints (("Goal" :in-theory (disable obs-fwd roots-good good-v)
                  :use ((:instance obs-fwd (v (nth r (st-roots st))))
                        (:instance roots-good)))))

; ---- THE OPERATIONS KEEP THE BARRIER'S INVARIANT --------------------------------

(defun hu-ind (k vs) (if (zp k) vs (hu-ind (1- k) (cdr vs))))
(defthm has-young-update-nth
  (implies (has-young (update-nth k v vs)) (or (yrefp v) (has-young vs)))
  :hints (("Goal" :induct (hu-ind k vs))))

; the barrier's invariant is about the old space and the remembered set
; alone
(defun-sk barrier2 (old rem)
  (forall i (implies (and (natp i) (< i (len old)) (has-young (nth i old)))
                     (member-equal i rem))))
(in-theory (disable barrier2))

(defthm barrier-ok-barrier2
  (equal (barrier-ok st) (barrier2 (st-old st) (st-rem st)))
  :hints (("Goal" :in-theory (enable barrier-ok barrier2)
                  :use ((:instance barrier-ok-necc (i (barrier2-witness (st-old st) (st-rem st))))
                        (:instance barrier2-necc (old (st-old st)) (rem (st-rem st)) (i (barrier-ok-witness st)))))))

; THE BARRIER: storing into old object i records i when the value is a
; young reference, so every old object holding one is still remembered
(defthm nth-past-end
  (implies (and (natp n) (<= (len l) n)) (equal (nth n l) nil)))

(defthm barrier2-write-young
  (implies (and (barrier2 old rem) (natp i) (yrefp v))
           (barrier2 (update-nth i (update-nth k v (nth i old)) old) (cons i rem)))
  :hints (("Goal" :in-theory (e/d (barrier2) (has-young-update-nth barrier2-necc))
                  :do-not-induct t
                  :expand ((barrier2 (update-nth i (update-nth k v (nth i old)) old) (cons i rem)))
                  :cases ((equal (barrier2-witness (update-nth i (update-nth k v (nth i old)) old) (cons i rem)) i))
                  :use ((:instance barrier2-necc
                                   (i (barrier2-witness (update-nth i (update-nth k v (nth i old)) old) (cons i rem))))
                        (:instance barrier2-necc (i i))
                        (:instance has-young-update-nth (vs (nth i old)))))))

(defthm barrier2-write-other
  (implies (and (barrier2 old rem) (natp i) (not (yrefp v)))
           (barrier2 (update-nth i (update-nth k v (nth i old)) old) rem))
  :hints (("Goal" :in-theory (e/d (barrier2) (has-young-update-nth barrier2-necc))
                  :do-not-induct t
                  :expand ((barrier2 (update-nth i (update-nth k v (nth i old)) old) rem))
                  :cases ((equal (barrier2-witness (update-nth i (update-nth k v (nth i old)) old) rem) i))
                  :use ((:instance barrier2-necc
                                   (i (barrier2-witness (update-nth i (update-nth k v (nth i old)) old) rem)))
                        (:instance barrier2-necc (i i))
                        (:instance has-young-update-nth (vs (nth i old)))))))

(defthm barrier2-write
  (implies (and (barrier2 old rem) (natp i))
           (barrier2 (update-nth i (update-nth k v (nth i old)) old)
                     (if (yrefp v) (cons i rem) rem)))
  :hints (("Goal" :in-theory (disable barrier2-write-young barrier2-write-other)
                  :use (barrier2-write-young barrier2-write-other))))

(defthm write-keeps-barrier
  (implies (barrier-ok st) (barrier-ok (write-field r k v st)))
  :hints (("Goal" :in-theory (enable write-field))))

; an allocation touches neither the old space nor the remembered set
(defthm alloc-keeps-barrier
  (implies (barrier-ok st) (barrier-ok (alloc fields st)))
  :hints (("Goal" :in-theory (enable alloc))))

; after a young collection nothing holds a young reference: the nursery
; is empty and every reference was forwarded
(defthm fwd-no-yref (implies (natp nold) (not (has-young (fwd-vals vs nold l)))))
(defthm nth-copies-any
  (implies (natp i) (equal (nth i (copies lrest l young nold))
                           (if (< i (len lrest)) (fwd-vals (nth (nth i lrest) young) nold l) nil))))

(defthm young-gc-no-young
  (implies (natp i)
           (not (has-young (nth i (st-old (young-gc l st))))))
  :hints (("Goal" :in-theory (enable young-gc)
                  :cases ((< i (len (st-old st)))))))

(defthm young-gc-barrier
  (barrier-ok (young-gc l st))
  :hints (("Goal" :in-theory (enable barrier2)
                  :use ((:instance young-gc-no-young
                                   (i (barrier2-witness (st-old (young-gc l st)) (st-rem (young-gc l st)))))))))

; ---- THE LIVE SET, computed -----------------------------------------------------
;
; L from a worklist: the young objects the roots and the remembered
; objects reference, then every young object a member references. With
; fuel, so it is a function of the logic; when the fuel runs out first
; the whole nursery is copied instead -- every collection is safe
; either way (live-set-ok), and a finished worklist copies only what is
; reachable, which is the point of it.

(defun young-refs (vs)
  (cond ((atom vs) nil)
        ((yrefp (car vs)) (cons (cdr (car vs)) (young-refs (cdr vs))))
        (t (young-refs (cdr vs)))))

(defun rem-refs (rem old)
  (if (atom rem) nil (append (young-refs (nth (car rem) old)) (rem-refs (cdr rem) old))))

; (mv done L)
(defun reach (todo l young fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) (mv nil l))
        ((atom todo) (mv t l))
        ((member-equal (car todo) l) (reach (cdr todo) l young (1- fuel)))
        (t (reach (append (young-refs (nth (car todo) young)) (cdr todo))
                  (cons (car todo) l) young (1- fuel)))))

(defun count-to (n) (if (zp n) nil (cons (1- n) (count-to (1- n)))))

(defun live-fuel (st) (* 4 (1+ (len (st-young st))) (1+ (len (st-old st)))))

(defun live-set (st)
  (mv-let (done l)
    (reach (append (young-refs (st-roots st)) (rem-refs (st-rem st) (st-old st))) nil (st-young st) (live-fuel st))
    (if done l (count-to (len (st-young st))))))

; ---- young-in, as a subset ------------------------------------------------------

(defthm young-in-is-subset
  (equal (young-in vs l) (subsetp-equal (young-refs vs) l)))

(defthm subsetp-append-right
  (implies (subsetp-equal a b) (subsetp-equal a (append b c))))
(defthm subsetp-append-left
  (implies (subsetp-equal a c) (subsetp-equal a (append b c))))
(defthm subsetp-cons-more (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm subsetp-refl (subsetp-equal a a))
(defthm subsetp-append-both
  (equal (subsetp-equal (append a b) c) (and (subsetp-equal a c) (subsetp-equal b c))))

(defthm member-subsetp
  (implies (and (subsetp-equal a b) (member-equal x a)) (member-equal x b)))
(defthm subsetp-trans
  (implies (and (subsetp-equal a b) (subsetp-equal b c)) (subsetp-equal a c)))

(defthm member-append-iff
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))
(defthm subsetp-consp
  (implies (and (consp a) (member-equal (car a) b) (subsetp-equal (cdr a) b)) (subsetp-equal a b)))

; ---- the worklist's invariant -----------------------------------------------------

; every member's young references are in L or still to do
(defun members-closed (ls l todo young)
  (if (atom ls)
      t
    (and (subsetp-equal (young-refs (nth (car ls) young)) (append l todo))
         (members-closed (cdr ls) l todo young))))

(defthm members-closed-more
  (implies (and (members-closed ls l todo young) (subsetp-equal (append l todo) (append l2 todo2)))
           (members-closed ls l2 todo2 young))
  :hints (("Goal" :induct (members-closed ls l todo young))))

(defthm members-closed-member
  (implies (and (members-closed ls l todo young) (member-equal j ls))
           (subsetp-equal (young-refs (nth j young)) (append l todo))))

(defthm append-nil-right (implies (true-listp l) (equal (append l nil) l)))

; what the worklist ends with: closed, and holding every start
(defthm reach-closed
  (implies (and (members-closed l l todo young) (subsetp-equal start (append l todo)) (true-listp l)
                (mv-nth 0 (reach todo l young fuel)))
           (and (members-closed (mv-nth 1 (reach todo l young fuel)) (mv-nth 1 (reach todo l young fuel)) nil young)
                (subsetp-equal start (mv-nth 1 (reach todo l young fuel)))
                (true-listp (mv-nth 1 (reach todo l young fuel)))))
  :hints (("Goal" :induct (reach todo l young fuel))))

; ---- THE LIVE SET IS A GOOD L ----------------------------------------------------

(defthm all-below-append
  (equal (all-below (append a b) n) (and (all-below a n) (all-below b n))))
(defthm refs-young-below
  (implies (refs-in-bounds vs no ny) (all-below (young-refs vs) ny)))
(defthm objs-young-below
  (implies (objs-ok objs no ny) (all-below (young-refs (nth j objs)) ny))
  :hints (("Goal" :cases ((< (nfix j) (len objs))))
          ("Subgoal 1" :in-theory (disable objs-ok-nth) :use ((:instance objs-ok-nth (i (nfix j)))))))
(defthm rem-refs-below
  (implies (objs-ok old no ny) (all-below (rem-refs rem old) ny)))

; the worklist adds only nursery objects
(defthm reach-below
  (implies (and (all-below l n) (all-below todo n) (objs-ok young no n))
           (all-below (mv-nth 1 (reach todo l young fuel)) n))
  :hints (("Goal" :induct (reach todo l young fuel))))

(defthm rem-refs-cover
  (implies (member-equal i rem) (subsetp-equal (young-refs (nth i old)) (rem-refs rem old))))

(defthm member-count-to
  (implies (and (natp j) (natp n) (< j n)) (member-equal j (count-to n))))
(defthm all-below-count-to-gen
  (implies (and (natp n) (<= (nfix m) n)) (all-below (count-to m) n)))
(defthm all-below-count-to
  (implies (natp n) (all-below (count-to n) n)))
(defthm below-subset-count-to
  (implies (and (all-below l n) (natp n)) (subsetp-equal l (count-to n))))
(defthm true-listp-count-to (true-listp (count-to n)))

(defmacro ls-start ()
  '(append (young-refs (st-roots st)) (rem-refs (st-rem st) (st-old st))))

; a list closed over its members, holding the roots' and the remembered
; objects' young references, of nursery objects, is a good L
(defthm l-ok-from-members
  (implies (and (members-closed l l nil (st-young st)) (subsetp-equal (young-refs (st-roots st)) l)
                (subsetp-equal (rem-refs (st-rem st) (st-old st)) l) (true-listp l)
                (all-below l (len (st-young st))))
           (l-ok l st))
  :hints (("Goal" :in-theory (enable l-ok)
                  :expand ((closed-ok l st))
                  :use ((:instance members-closed-member (ls l) (todo nil) (young (st-young st))
                                   (j (closed-ok-witness l st)))
                        (:instance rem-refs-cover (rem (st-rem st)) (old (st-old st)) (i (closed-ok-witness l st)))))))

; the finished worklist: closed, holding every start, all nursery objects
(defthm live-set-finished
  (implies (and (heap-ok st) (mv-nth 0 (reach (ls-start) nil (st-young st) (live-fuel st))))
           (l-ok (mv-nth 1 (reach (ls-start) nil (st-young st) (live-fuel st))) st))
  :hints (("Goal" :in-theory (e/d (heap-ok) (reach-closed reach-below l-ok l-ok-from-members live-fuel))
                  :use ((:instance reach-closed (l nil) (todo (ls-start)) (start (ls-start)) (young (st-young st))
                                   (fuel (live-fuel st)))
                        (:instance reach-below (l nil) (todo (ls-start)) (young (st-young st)) (fuel (live-fuel st))
                                   (n (len (st-young st))) (no (len (st-old st))))
                        (:instance l-ok-from-members (l (mv-nth 1 (reach (ls-start) nil (st-young st) (live-fuel st)))))))))

; the fallback: the whole nursery
(defthm live-set-fallback
  (implies (heap-ok st) (l-ok (count-to (len (st-young st))) st))
  :hints (("Goal" :in-theory (enable heap-ok l-ok)
                  :expand ((closed-ok (count-to (len (st-young st))) st))
                  :use ((:instance objs-young-below (objs (st-old st)) (no (len (st-old st))) (ny (len (st-young st)))
                                   (j (closed-ok-witness (count-to (len (st-young st))) st)))
                        (:instance objs-young-below (objs (st-young st)) (no (len (st-old st))) (ny (len (st-young st)))
                                   (j (closed-ok-witness (count-to (len (st-young st))) st)))))))

; THE LIVE SET IS ALWAYS A GOOD L: so a young collection over it is
; invisible (gc-invisible), whether the worklist finished or not
(defthm live-set-ok
  (implies (heap-ok st) (l-ok (live-set st) st))
  :hints (("Goal" :in-theory (disable live-set-finished live-set-fallback l-ok)
                  :use (live-set-finished live-set-fallback))))

(defthm collection-invisible
  (implies (heap-ok st)
           (equal (obs (nth r (st-roots (young-gc (live-set st) st))) path (young-gc (live-set st) st))
                  (obs (nth r (st-roots st)) path st)))
  :hints (("Goal" :in-theory (disable live-set gc-invisible)
                  :use ((:instance gc-invisible (l (live-set st)))))))

; ---- THE ALGORITHM AND ITS COST ---------------------------------------------------
;
; young-gc above is the specification: it forwards every old object. The
; collector fixes up only the remembered ones -- the barrier's whole
; point -- and young-gc-alg does exactly that. It computes the same heap
; (alg-is-spec), so gc-invisible is about the algorithm; and its work is
; the roots, the remembered objects' fields and the live young objects'
; fields (alg-cost), so a young collection's cost is the live data's and
; not the old space's or the garbage's.

; forwarding twice is forwarding once: an old reference stays put
(defthm fwd-fwd (implies (natp nold) (equal (fwd (fwd v nold l) nold l) (fwd v nold l)))
  :hints (("Goal" :in-theory (enable fwd))))
(defthm fwd-vals-idem
  (implies (natp nold) (equal (fwd-vals (fwd-vals vs nold l) nold l) (fwd-vals vs nold l))))

; fix up the remembered objects only, in place
(defun fix-rem (rem old nold l)
  (if (atom rem)
      old
    (fix-rem (cdr rem) (update-nth (car rem) (fwd-vals (nth (car rem) old) nold l) old) nold l)))

(defthm len-fix-rem
  (implies (all-below rem (len old)) (equal (len (fix-rem rem old nold l)) (len old))))

(defthm nth-fix-rem
  (implies (and (natp i) (natp nold) (all-below rem n))
           (equal (nth i (fix-rem rem old nold l))
                  (if (member-equal i rem) (fwd-vals (nth i old) nold l) (nth i old))))
  :hints (("Goal" :induct (fix-rem rem old nold l))))

(defun young-gc-alg (l st)
  (let ((nold (len (st-old st))))
    (mk-st (append (fix-rem (st-rem st) (st-old st) nold l) (copies l l (st-young st) nold))
           nil nil
           (fwd-vals (st-roots st) nold l))))

; two true lists of one length that agree at every index are equal
(defun-sk nth-agree (a b) (forall i (implies (natp i) (equal (nth i a) (nth i b)))))
(defun nae-ind (a b) (if (or (atom a) (atom b)) (list a b) (nae-ind (cdr a) (cdr b))))
(defthm nth-agree-cdr
  (implies (nth-agree a b) (nth-agree (cdr a) (cdr b)))
  :hints (("Goal" :expand ((nth-agree (cdr a) (cdr b)))
                  :use ((:instance nth-agree-necc (i (1+ (nth-agree-witness (cdr a) (cdr b)))))))))
(defthm nth-agree-equal
  (implies (and (true-listp a) (true-listp b) (equal (len a) (len b)) (nth-agree a b))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :induct (nae-ind a b))
          ("Subgoal *1/2" :use ((:instance nth-agree-necc (i 0))))))

; THE ALGORITHM IS THE SPECIFICATION: with the barrier's invariant, fixing
; up the remembered objects forwards the whole old space. Pointwise first:
; a remembered object is forwarded; an unremembered one holds no young
; reference, so forwarding leaves it alone (fwd-no-young); past the end
; both are nil.
(defthm nth-fix-rem-is-fwd
  (implies (and (barrier2 old rem) (all-below rem (len old))
                (objs-ok old no ny) (natp nold) (natp i))
           (equal (nth i (fix-rem rem old nold l)) (fwd-vals (nth i old) nold l)))
  :hints (("Goal" :cases ((< i (len old)))
                  :use ((:instance barrier2-necc) (:instance objs-ok-nth (objs old))))))

(defthm nth-agree-fix-rem
  (implies (and (barrier2 old rem) (all-below rem (len old))
                (objs-ok old no ny) (natp nold))
           (nth-agree (fix-rem rem old nold l) (fwd-objs old nold l)))
  :hints (("Goal" :in-theory (disable fix-rem))))

(defthm true-listp-fix-rem
  (implies (true-listp old) (true-listp (fix-rem rem old nold l))))
(defthm true-listp-fwd-objs (true-listp (fwd-objs objs nold l)))

(defthm fix-rem-is-fwd-objs
  (implies (and (barrier2 old rem) (all-below rem (len old)) (true-listp old)
                (objs-ok old no ny) (natp nold))
           (equal (fix-rem rem old nold l) (fwd-objs old nold l)))
  :hints (("Goal" :in-theory (disable fix-rem fwd-objs nth-agree)
                  :use ((:instance nth-agree-equal (a (fix-rem rem old nold l)) (b (fwd-objs old nold l)))))))

; the remembered set names old objects: the barrier records only the
; object it stored into, which a root named
(defun rem-ok (st) (all-below (st-rem st) (len (st-old st))))

(defthm write-keeps-rem-ok
  (implies (and (heap-ok st) (rem-ok st)) (rem-ok (write-field r k v st)))
  :hints (("Goal" :in-theory (e/d (write-field heap-ok) (nth-in-bounds))
                  :use ((:instance nth-in-bounds (vs (st-roots st)) (k r)
                                   (no (len (st-old st))) (ny (len (st-young st))))))))
(defthm alloc-keeps-rem-ok
  (implies (rem-ok st) (rem-ok (alloc fields st))))
(defthm young-gc-rem-ok (rem-ok (young-gc l st)) :hints (("Goal" :in-theory (enable young-gc))))

; THE ALGORITHM IS THE COLLECTION: so gc-invisible and collection-invisible
; are about the collector that touches only the remembered objects
(defthm alg-is-spec
  (implies (and (heap-ok st) (rem-ok st))
           (equal (young-gc-alg l st) (young-gc l st)))
  :hints (("Goal" :in-theory (e/d (heap-ok young-gc) (fix-rem))
                  :use ((:instance fix-rem-is-fwd-objs (old (st-old st)) (rem (st-rem st))
                                   (nold (len (st-old st))) (no (len (st-old st)))
                                   (ny (len (st-young st))))))))

; ---- ITS COST ---------------------------------------------------------------------
;
; Counted in steps of O(1) each: a field read and forwarded, an object
; visited. The worklist's "already in L?" is one step -- the collector
; asks the object's forwarding word, not a list. A remembered entry was
; paid for by the write that made it; the set empties at every collection.

; the worklist's steps: one per entry taken
(defun reach-steps (todo l young fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) 0)
        ((atom todo) 0)
        ((member-equal (car todo) l) (1+ (reach-steps (cdr todo) l young (1- fuel))))
        (t (1+ (reach-steps (append (young-refs (nth (car todo) young)) (cdr todo))
                            (cons (car todo) l) young (1- fuel))))))

; the young references the members of l hold
(defun yr-sum (l young)
  (if (atom l) 0 (+ (len (young-refs (nth (car l) young))) (yr-sum (cdr l) young))))

(defthm len-append-sum (equal (len (append a b)) (+ (len a) (len b))))

; THE WORKLIST'S WORK: its starts and the young fields of what it added
; -- the live young objects, never the garbage
(defthm reach-steps-exact
  (implies (mv-nth 0 (reach todo l young fuel))
           (equal (reach-steps todo l young fuel)
                  (+ (len todo) (- (yr-sum (mv-nth 1 (reach todo l young fuel)) young) (yr-sum l young))))))

; an object's fields, one step for the object itself
(defun fields-of (is objs)
  (if (atom is) 0 (+ 1 (len (nth (car is) objs)) (fields-of (cdr is) objs))))

; the collection's steps: the trace, the remembered objects fixed up,
; the copies, the roots forwarded
(defun gc-steps (st)
  (let ((start (append (young-refs (st-roots st)) (rem-refs (st-rem st) (st-old st)))))
    (+ (reach-steps start nil (st-young st) (live-fuel st))
       (fields-of (st-rem st) (st-old st))
       (fields-of (live-set st) (st-young st))
       (len (st-roots st)))))

(defthm len-young-refs (<= (len (young-refs vs)) (len vs)) :rule-classes :linear)
(defthm len-rem-refs (<= (len (rem-refs rem old)) (fields-of rem old)) :rule-classes :linear)
(defthm yr-sum-fields (<= (yr-sum l young) (fields-of l young)) :rule-classes :linear)
(defthm yr-sum-natp (<= 0 (yr-sum l young)) :rule-classes :linear)

; THE COST: when the worklist finishes, a young collection is linear in
; the roots, the remembered objects' fields and the live young objects'
; fields. The old space's size and the nursery's garbage do not appear.
(defthm alg-cost
  (implies (mv-nth 0 (reach (append (young-refs (st-roots st)) (rem-refs (st-rem st) (st-old st)))
                            nil (st-young st) (live-fuel st)))
           (<= (gc-steps st)
               (* 2 (+ (len (st-roots st))
                       (fields-of (st-rem st) (st-old st))
                       (fields-of (live-set st) (st-young st))))))
  :hints (("Goal" :in-theory (disable reach live-fuel))))

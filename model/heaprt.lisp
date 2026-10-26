; The rest of the heap, formally (docs/model-coverage.md): the value stack
; and its frames, the roots a collection starts from, the global roots and
; their handles, the spare frames, the pools' growth, the texts, and the
; heap image -- src/f/GC.f90 beside what the other heap books prove.
;
; Those books prove the collector's parts: heapg/heapgn the marking (from
; the roots it is handed, every marked object's references marked:
; hpg-drain-closed, and the young marking's), heapsw the sweep (only the
; unmarked freed), heapal a slot taken (never one in use, on the free list
; or in a batch), heaprn the arena's runs, heapmt the threads (a rooted
; cell is on no free list, no batch, no pending list). What they take as
; given is WHAT THE ROOTS ARE, and that is this book's:
;
;   push_roots   the roots of a collection: every global root, every
;                thread's value stack up to its top, and the allocation's
;                own (gc_obj: its roots and the slots it is about to fill;
;                gc_vec, new_text: its roots)
;
; and THE ROOTING CONVENTION, which ~970 call sites keep: a value held in
; a Fortran local across a call that may allocate is lost to the
; collector unless it is in that call's roots(:), in a slot of an active
; frame on the value stack (vs_enter/vs_set/vs_leave), or reachable from a
; global root. The model's discipline, which the code keeps by hand:
;
;   D1  a frame writes only its own slots: base+1 .. base+n of the
;       vs_enter that made it (s%vstack(base + k) = v, vs_set);
;   D2  a frame leaves to its own base, once, LIFO (vs_leave(base));
;       vm_run's shortcut -- top lowered to its high-water sp + 8 before
;       the leave -- relies on the VM run writing nothing above that
;       (the VM runtime row's to prove);
;   D3  a value held across an allocation is in its roots, in an active
;       frame's slot, or reachable from a global root;
;   D4  a frame given back as a spare (gc_frame_give) is one its call
;       allocated and nothing references any more;
;   D5  an image is read before this process claims any global root
;       (main.f90 reads it straight after gc_init), and taken with one
;       thread (gc_image_write refuses more).
;
; Theorems:
;   VALUE STACK  every slot above the top is nil (vs-ok, kept by enter,
;                leave, set and a stack's reset), so a frame vs_enter makes
;                is all nil without clearing it (vs-enter-fresh); a frame,
;                whatever it runs inside it under D1 and D2, leaves the
;                stack exactly as it found it (frame-balance), and never
;                changes a slot of the frames below it while it runs
;                (ops-keep-callers), so a value its caller put in a slot
;                is on the stack -- a root -- at every allocation the frame
;                makes; a leave below the frame's own base drops its
;                caller's slots (leave-below-base-drops)
;   ROOTS        anything reachable from a root -- a global, a value
;                stack's slot, the allocation's own -- is kept by any
;                collection whose marked set holds the roots and is closed
;                (rooted-path-survives; heapg/heapgn prove the marking is
;                such a set), the slots gc_obj stores among them
;                (alloc-slots-kept); and a value held in a local and in no
;                root is freed and its cell handed to the next allocation
;                (unrooted-is-reused: the "two allocations as arguments to
;                one call" hazard)
;   GLOBALS      a claimed slot's index never moves as the table grows
;                (glob-new-keeps), gc_global_keep leaves its handle live
;                holding its value and every other live handle's value as
;                it was (keep-roots, keep-others), gc_init makes every
;                handle stale so the next keep claims again
;                (init-stales-handles), and an image read makes a handle
;                whose generation matches the image's live on the image's
;                slot -- why D5 (image-gen-aliases)
;   SPARES       every spare frame is a used cell (spares-used, kept by
;                give, take, every collection, an allocation and a new
;                heap), so one taken is in use and no allocation since it
;                was given can have handed it out (spare-taken-is-live);
;                before the fix a new heap (gc_init, an image read) kept
;                stack 1's spares, cells of the old heap
;                (spare-survives-reset-is-stale; test/f/gc_test.f90 20b)
;   POOLS        growing a pool keeps every slot it had and adds unused
;                ones past the used end (grow-keeps, grow-fresh,
;                pool-ok-grow): which cells a pool owns is heapal/heapmt's
;   TEXTS        a text slot holds its text and the index made from it
;                (texts-indexed, kept by new_text, a release and growth)
;   IMAGE        an image read gives back the pools, the arena, the texts,
;                the global roots and their generation exactly as written
;                (image-roundtrip), so the graph reachable from the roots
;                is the one saved (image-same-graph); the full collection
;                it is taken after leaves no remembered, aged or young set
;                to lose (full-empties-rem)
;   COST         by counting: vs_enter 1 step, vs_leave top - base + 1,
;                a reset hi + 1, push_roots the globals plus every stack's
;                top plus the own roots, gc_global_new at most count + 2,
;                gc_frame_give n + 1, a pool's growth 2n, an image's texts
;                one turn a slot and its bytes

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

; ---- LISTS ---------------------------------------------------------------------------

(defun nils (n) (if (zp n) nil (cons nil (nils (1- n)))))
(defun all-nil (x) (if (atom x) t (and (null (car x)) (all-nil (cdr x)))))

(defthm len-nils (equal (len (nils n)) (nfix n)))
(defthm all-nil-nils (all-nil (nils n)))
(defthm true-listp-nils (true-listp (nils n)))
(defthm all-nil-append (equal (all-nil (append a b)) (and (all-nil a) (all-nil b))))
(defthm all-nil-nthcdr (implies (all-nil x) (all-nil (nthcdr n x))))
(defthm all-nil-take (implies (all-nil x) (equal (take n x) (nils n)))
  :hints (("Goal" :in-theory (enable take))))
(defthm all-nil-is-nils (implies (and (all-nil x) (true-listp x)) (equal (nils (len x)) x))
  :rule-classes nil)
(defthm len-take (equal (len (take n x)) (nfix n)) :hints (("Goal" :in-theory (enable take))))
(defthm true-listp-take (true-listp (take n x)) :hints (("Goal" :in-theory (enable take))))
(defthm len-nthcdr (implies (<= (nfix n) (len x)) (equal (len (nthcdr n x)) (- (len x) (nfix n)))))
(defthm take-append-len (implies (and (true-listp a) (equal n (len a))) (equal (take n (append a b)) a))
  :hints (("Goal" :in-theory (enable take))))
(defthm nthcdr-append-len (implies (equal n (len a)) (equal (nthcdr n (append a b)) b)))
(defthm take-take (implies (<= (nfix i) (nfix j)) (equal (take i (take j x)) (take i x)))
  :hints (("Goal" :in-theory (enable take))))
(defthm take-len-true (implies (true-listp x) (equal (take (len x) x) x))
  :hints (("Goal" :in-theory (enable take))))
(defthm take-update-nth-above
  (implies (and (natp i) (natp k) (<= k i)) (equal (take k (update-nth i v x)) (take k x)))
  :hints (("Goal" :in-theory (enable take))))
(defthm len-update-nth-in (implies (< (nfix i) (len x)) (equal (len (update-nth i v x)) (len x))))
(defthm true-listp-update-nth-tl (implies (true-listp x) (true-listp (update-nth i v x))))
(defthm len-append-hr (equal (len (append a b)) (+ (len a) (len b))))
(defthm nils-append (equal (append (nils a) (nils b)) (nils (+ (nfix a) (nfix b)))))

(defthm nils-nthcdr-all-nil
  (implies (and (all-nil r) (natp m) (<= m (len r)))
           (equal (append (nils m) (nthcdr m r)) r)))
(defthm cons-car-cdr-hr (implies (consp st) (equal (cons (car st) (cdr st)) st)))

; ---- THE VALUE STACK -------------------------------------------------------------------
;
; A thread's stack, s%vstack with s%vs_top: st = (live . rest), live the
; slots 1 .. top in order and rest the slots above it, its length the
; room left (size(vstack) - vs_top). A slot is a value; nil is nilv.

(defun vs-ok (st) (and (consp st) (true-listp (car st)) (true-listp (cdr st)) (all-nil (cdr st))))
(defun vs-cap (st) (+ (len (car st)) (len (cdr st))))

; vs_enter_on: the frame base+1 .. base+n above the top, base the old top;
; :full is its error stop. NOT CLEARED: vs-enter-fresh is why it need not.
(defun vs-enter (n st)
  (if (< (len (cdr st)) (nfix n)) :full
    (cons (append (car st) (take (nfix n) (cdr st))) (nthcdr (nfix n) (cdr st)))))

; vs_leave_on: back to base, the slots it pops cleared; a base outside
; 0 .. top does nothing
(defun vs-leave (base st)
  (if (or (not (natp base)) (< (len (car st)) base)) st
    (cons (take base (car st)) (append (nils (- (len (car st)) base)) (cdr st)))))

; vs_set_on, vs_get_on: slots 1 .. top only
(defun vs-set (k v st)
  (if (and (posp k) (<= k (len (car st)))) (cons (update-nth (1- k) v (car st)) (cdr st)) st))
(defun vs-get (k st) (if (and (posp k) (<= k (len (car st)))) (nth (1- k) (car st)) nil))

; gc_stack_new on a reused stack: vstack(1:vs_hi) = nilv, top 0 -- the
; slots above vs_hi >= top are nil already
(defun vs-reset (st) (cons nil (append (nils (len (car st))) (cdr st))))

(defthm vs-ok-enter (implies (and (vs-ok st) (not (equal (vs-enter n st) :full))) (vs-ok (vs-enter n st))))
(defthm vs-ok-leave (implies (vs-ok st) (vs-ok (vs-leave b st))))
(defthm vs-ok-set (implies (vs-ok st) (vs-ok (vs-set k v st))))
(defthm vs-ok-reset (implies (vs-ok st) (vs-ok (vs-reset st))))
(defthm vs-reset-empty (equal (car (vs-reset st)) nil))
(defthm vs-cap-enter (implies (and (vs-ok st) (not (equal (vs-enter n st) :full)))
                              (equal (vs-cap (vs-enter n st)) (vs-cap st))))
(defthm vs-cap-leave (implies (vs-ok st) (equal (vs-cap (vs-leave b st)) (vs-cap st))))
(defthm vs-cap-reset (equal (vs-cap (vs-reset st)) (vs-cap st)))

; the new frame's slots are nil, and the slots below it are as they were
(defthm vs-enter-fresh
  (implies (and (vs-ok st) (not (equal (vs-enter n st) :full)))
           (and (equal (nthcdr (len (car st)) (car (vs-enter n st))) (nils n))
                (equal (take (len (car st)) (car (vs-enter n st))) (car st))
                (equal (len (car (vs-enter n st))) (+ (len (car st)) (nfix n))))))

; a leave below the frame's base: the top is that base, the caller's
; slots above it gone from the stack
(defthm leave-below-base-drops
  (implies (and (natp b) (<= b (len (car st))))
           (equal (car (vs-leave b st)) (take b (car st)))))

; ---- FRAMES -------------------------------------------------------------------------
;
; What a frame does, under D1 and D2: fl = :frame, x = (n . ops) -- enter
; n, run ops, leave to its base; fl = :ops, x the ops of a frame whose
; base and size are base and n: (:set k v) writes its slot k (D1: 1..n,
; anything else is no write), (:frame m . ops) runs a frame inside it,
; and anything else -- an allocation, a call that writes no slot of this
; stack -- leaves it alone. :full is the value stack's error stop.

(defun run (fl x base n st)
  (declare (xargs :measure (acl2-count x)))
  (cond ((equal st :full) :full)
        ((eq fl :frame)
         (if (atom x) st
           (let* ((b (len (car st))) (st1 (vs-enter (nfix (car x)) st)))
             (if (equal st1 :full) :full
               (let ((st2 (run :ops (cdr x) b (nfix (car x)) st1)))
                 (if (equal st2 :full) :full (vs-leave b st2)))))))
        ((atom x) st)
        (t (let* ((op (car x))
                  (st1 (cond ((and (consp op) (eq (car op) :set))
                              (let ((k (cadr op)))
                                (if (and (posp k) (<= k (nfix n))) (vs-set (+ (nfix base) k) (caddr op) st) st)))
                             ((and (consp op) (eq (car op) :frame)) (run :frame (cdr op) 0 0 st))
                             (t st))))
             (run :ops (cdr x) base n st1)))))

(defun keeps (st r b)
  (and (vs-ok r) (equal (len (car r)) (len (car st))) (equal (take b (car r)) (take b (car st)))
       (equal (cdr r) (cdr st))))

(defthm all-nil-same-len
  (implies (and (all-nil a) (all-nil b) (true-listp a) (true-listp b) (equal (len a) (len b)))
           (equal a b))
  :hints (("Goal" :use ((:instance all-nil-is-nils (x a)) (:instance all-nil-is-nils (x b)))))
  :rule-classes nil)

(defthm take-of-append-take
  (implies (and (true-listp a) (natp m) (<= m (len a)))
           (equal (take m (append a c)) (take m a)))
  :hints (("Goal" :in-theory (enable take))))

; a frame's leave, after ops that kept what its enter made: the stack as before
(defthm frame-close
  (implies (and (vs-ok st) (natp m) (not (equal (vs-enter m st) :full))
                (keeps (vs-enter m st) r (len (car st))))
           (equal (vs-leave (len (car st)) r) st))
  :hints (("Goal" :use ((:instance all-nil-same-len (a (cdr st))
                                    (b (append (nils m) (nthcdr m (cdr st)))))))))

(defthm run-keeps
  (implies (and (vs-ok st) (not (equal (run fl x base n st) :full)))
           (if (eq fl :frame)
               (equal (run fl x base n st) st)
             (implies (and (natp base) (natp n) (equal (len (car st)) (+ base n)))
                      (keeps st (run fl x base n st) base))))
  :hints (("Goal" :induct (run fl x base n st)))
  :rule-classes nil)

; a frame leaves the stack exactly as it found it
(defthm frame-balance
  (implies (and (vs-ok st) (not (equal (run :frame x 0 0 st) :full)))
           (equal (run :frame x 0 0 st) st))
  :hints (("Goal" :use ((:instance run-keeps (fl :frame) (base 0) (n 0))))))

; while a frame's ops run -- any prefix of them, so at every allocation
; among them -- the slots below its own frame are its callers', unchanged
(defthm ops-keep-callers
  (implies (and (vs-ok st) (natp base) (natp n) (equal (len (car st)) (+ base n))
                (not (equal (run :ops ops base n st) :full)))
           (and (equal (take base (car (run :ops ops base n st))) (take base (car st)))
                (equal (len (car (run :ops ops base n st))) (len (car st)))))
  :hints (("Goal" :use ((:instance run-keeps (fl :ops) (x ops))))))

(defthm member-take-member
  (implies (and (member-equal v (take k l)) (<= (nfix k) (len l))) (member-equal v l))
  :hints (("Goal" :in-theory (enable take))))

; a value a caller put in a slot below the running frame is still on the
; stack after any of the frame's ops -- so at every allocation they make
(defthm caller-slot-stays
  (implies (and (vs-ok st) (natp base) (natp n) (equal (len (car st)) (+ base n))
                (not (equal (run :ops ops base n st) :full))
                (member-equal v (take base (car st))))
           (member-equal v (car (run :ops ops base n st))))
  :hints (("Goal" :use ((:instance ops-keep-callers)
                        (:instance member-take-member (k base) (l (car (run :ops ops base n st)))))
           :in-theory (disable ops-keep-callers member-take-member))))

; ---- THE ROOTS AND A COLLECTION -----------------------------------------------------
;
; push_roots: global_root(1:global_count), then every stack's vstack(1:vs_top),
; then the allocation's own -- gc_obj's all_roots = roots ++ slots.

(defun lives (stacks) (if (atom stacks) nil (append (car (car stacks)) (lives (cdr stacks)))))
(defun rootset (globals stacks own) (append globals (lives stacks) own))

(defthm member-append-hr (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm stack-slot-rooted
  (implies (and (member-equal st stacks) (member-equal v (car st)))
           (member-equal v (rootset g stacks own))))

; The heap as a graph: heap an alist, a cell to the cells its slots or
; words reference (texts and immediates reference none). A collection
; marks a set M and the sweep keeps exactly the used cells in it
; (heapsw-proof). The marking's set holds the roots it was handed and is
; closed: every marked cell's references marked (heapg-proof's
; hpg-drain-closed; heapgn-proof's, for the young one with the
; remembered set) -- here any such M, so every collection the code makes.

(defun kids (c heap) (cdr (assoc-equal c heap)))
(defun closed (m mm heap)
  (if (atom m) t (and (subsetp-equal (kids (car m) heap) mm) (closed (cdr m) mm heap))))
(defun path-ok (p heap)
  (if (or (atom p) (atom (cdr p))) t
    (and (member-equal (cadr p) (kids (car p) heap)) (path-ok (cdr p) heap))))
(defun survivors (u m)
  (cond ((atom u) nil)
        ((member-equal (car u) m) (cons (car u) (survivors (cdr u) m)))
        (t (survivors (cdr u) m))))
(defun freed (u m)
  (cond ((atom u) nil)
        ((member-equal (car u) m) (freed (cdr u) m))
        (t (cons (car u) (freed (cdr u) m)))))

(defthm closed-member
  (implies (and (closed m mm heap) (member-equal x m)) (subsetp-equal (kids x heap) mm)))
(defthm subsetp-member-hr
  (implies (and (member-equal x a) (subsetp-equal a b)) (member-equal x b)))
(defthm path-step-marked
  (implies (and (closed mm mm heap) (member-equal c mm) (member-equal d (kids c heap)))
           (member-equal d mm))
  :hints (("Goal" :in-theory (disable closed-member subsetp-member-hr kids)
           :use ((:instance closed-member (m mm) (x c))
                 (:instance subsetp-member-hr (x d) (a (kids c heap)) (b mm))))))
(defthm path-in-marked
  (implies (and (closed mm mm heap) (member-equal (car p) mm) (path-ok p heap) (member-equal y p))
           (member-equal y mm))
  :hints (("Goal" :induct (path-ok p heap) :in-theory (disable closed kids subsetp-member-hr closed-member))))
(defthm survivors-member
  (iff (member-equal y (survivors u m)) (and (member-equal y u) (member-equal y m))))
(defthm freed-member
  (iff (member-equal y (freed u m)) (and (member-equal y u) (not (member-equal y m)))))

; whatever is reachable from a root survives the collection
(defthm rooted-path-survives
  (let ((r (rootset g stacks own)))
    (implies (and (subsetp-equal r mm) (closed mm mm heap)
                  (member-equal (car p) r) (path-ok p heap) (member-equal y p) (member-equal y u))
             (member-equal y (survivors u mm))))
  :hints (("Goal" :in-theory (disable rootset path-in-marked)
           :use ((:instance path-in-marked)))))

; gc_obj collects with its roots and the slots it is about to store, so
; the object it makes references only survivors
(defthm alloc-slots-kept
  (implies (and (subsetp-equal (rootset g stacks (append roots slots)) mm)
                (member-equal y slots) (member-equal y u))
           (member-equal y (survivors u mm))))

; THE HAZARD: x, held in a local, is in no root -- passed to neither the
; allocation's roots nor a frame's slot. The marking from the roots is
; the closed set (2); the sweep frees x, and the allocation takes the
; freed cell (heapal: the free list's head), so x now names the new object.
(defthm unrooted-is-reused
  (let ((heap '((1) (2))) (u '(1 2)) (mm '(2)) (x 1))
    (and (subsetp-equal (rootset '(2) nil nil) mm) (closed mm mm heap)
         (not (member-equal x (survivors u mm)))
         (equal (car (freed u mm)) x))))

; COST: push_roots pushes each root once -- the globals, each stack to its
; top, the own -- and marking is heap-cost's
(defun tops (stacks) (if (atom stacks) 0 (+ (len (car (car stacks))) (tops (cdr stacks)))))
(defun push-roots-steps (globals stacks own)
  (+ (len globals) (tops stacks) (len own)))
(defthm push-roots-cost
  (equal (len (rootset globals stacks own)) (push-roots-steps globals stacks own))
  :hints (("Goal" :induct (lives stacks))))

; vs_leave's clearing loop, base+1 .. top, and vs_enter with no loop
(defun clear-turns (i top) (declare (xargs :measure (nfix (- (1+ (ifix top)) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp top)) (< top i)) 0 (1+ (clear-turns (1+ i) top))))
(defthm clear-turns-closed
  (implies (and (integerp i) (integerp top) (<= i (1+ top)))
           (equal (clear-turns i top) (- (1+ top) i)))
  :hints (("Goal" :induct (clear-turns i top))))
(defthm clear-turns-count
  (implies (and (natp base) (natp top) (<= base top))
           (equal (clear-turns (1+ base) top) (- top base))))
(defun vs-enter-steps (n st) (declare (ignore n st)) 1)
(defun vs-leave-steps (base st) (1+ (clear-turns (1+ (nfix base)) (len (car st)))))
(defthm vs-leave-cost
  (implies (and (natp base) (<= base (len (car st))))
           (equal (vs-leave-steps base st) (+ 1 (- (len (car st)) base)))))
; gc_stack_new on a reused stack clears 1 .. vs_hi
(defthm vs-reset-cost (implies (natp hi) (equal (1+ (clear-turns 1 hi)) (1+ hi)))
  :hints (("Goal" :use ((:instance clear-turns-count (base 0) (top hi))))))

; ---- THE GLOBAL ROOTS ------------------------------------------------------------------
;
; gl = (gen count tbl): global_gen, global_count, global_root(:). A handle
; (gc_root) is h = (hgen . idx); live when its generation is this heap's
; and idx a claimed slot.

(defun gl-gen (g) (nth 0 g))
(defun gl-count (g) (nth 1 g))
(defun gl-tbl (g) (nth 2 g))
(defun gl-ok (g)
  (and (true-listp g) (equal (len g) 3) (natp (gl-gen g)) (natp (gl-count g)) (true-listp (gl-tbl g))
       (<= (gl-count g) (len (gl-tbl g)))))
(defun gl-globals (g) (take (gl-count g) (gl-tbl g)))   ; what push_roots pushes

; grow_global_roots: max(8, 2 size), the claimed slots at their indices
(defun gl-grow (tbl count) (append (take count tbl) (nils (- (max 8 (* 2 (len tbl))) count))))
; gc_global_new: the next slot, the table grown first if full
(defun gl-new (v g)
  (let* ((c (gl-count g)) (tbl (gl-tbl g))
         (tbl1 (if (<= (len tbl) c) (gl-grow tbl c) tbl)))
    (list (gl-gen g) (1+ c) (update-nth c v tbl1))))
(defun live (h g) (and (consp h) (equal (car h) (gl-gen g)) (posp (cdr h)) (<= (cdr h) (gl-count g))))
(defun root-get (h g) (if (live h g) (nth (1- (cdr h)) (gl-tbl g)) nil))
; gc_global_keep: the slot rewritten when the handle is live, else claimed anew
(defun keep-h (h g) (if (live h g) h (cons (gl-gen g) (1+ (gl-count g)))))
(defun keep-g (h v g) (if (live h g) (list (gl-gen g) (gl-count g) (update-nth (1- (cdr h)) v (gl-tbl g))) (gl-new v g)))
; gc_init: a new generation, an empty table of 8
(defun gl-init (g) (list (1+ (nfix (gl-gen g))) 0 (nils 8)))

(defthm nth-update-nth-hr
  (equal (nth i (update-nth j v x)) (if (equal (nfix i) (nfix j)) v (nth i x))))
(defthm nth-append-hr
  (equal (nth i (append a b)) (if (< (nfix i) (len a)) (nth i a) (nth (- (nfix i) (len a)) b))))
(defthm nth-take-hr (implies (< (nfix i) (nfix k)) (equal (nth i (take k x)) (nth i x)))
  :hints (("Goal" :in-theory (enable take))))
(defthm len-update-nth-hr (equal (len (update-nth i v x)) (max (len x) (1+ (nfix i)))))

(defthm gl-ok-new (implies (gl-ok g) (gl-ok (gl-new v g))))
(defthm gl-ok-keep (implies (gl-ok g) (gl-ok (keep-g h v g))))
(defthm gl-ok-init (gl-ok (gl-init g)))

; a claimed slot's index never moves, whatever the growth
(defthm glob-new-keeps
  (implies (and (gl-ok g) (posp i) (<= i (gl-count g)))
           (equal (nth (1- i) (gl-tbl (gl-new v g))) (nth (1- i) (gl-tbl g)))))

; gc_global_keep: the handle live, holding v, and every other live
; handle's value as it was
(defthm keep-roots
  (implies (gl-ok g)
           (and (live (keep-h h g) (keep-g h v g))
                (equal (root-get (keep-h h g) (keep-g h v g)) v))))
(defthm keep-others
  (implies (and (gl-ok g) (live h2 g) (not (equal (cdr h2) (cdr (keep-h h g)))))
           (and (live h2 (keep-g h v g))
                (equal (root-get h2 (keep-g h v g)) (root-get h2 g)))))

; a live handle's value is one push_roots pushes
(defthm member-nth-take
  (implies (and (natp i) (natp k) (< i k)) (member-equal (nth i x) (take k x)))
  :hints (("Goal" :in-theory (enable take))))
(defthm live-handle-rooted
  (implies (and (gl-ok g) (live h g))
           (member-equal (root-get h g) (gl-globals g))))

; gc_init: every handle made before it -- its generation at most the
; heap's -- is stale, so gc_global_keep claims again rather than writing a
; slot of the new table it does not own (the silent bug three modules had)
(defthm init-stales-handles
  (implies (and (gl-ok g) (consp h) (<= (car h) (gl-gen g)))
           (not (live h (gl-init g)))))

; an image read takes the image's table AND generation (gc_image_read), so
; a handle of this process with that generation reads the image's slot --
; someone else's root -- which is why D5: nothing claims a root first
(defun gl-read (saved) saved)
(defthm image-gen-aliases
  (implies (and (gl-ok saved) (consp h) (equal (car h) (gl-gen saved))
                (posp (cdr h)) (<= (cdr h) (gl-count saved)))
           (equal (root-get h (gl-read saved)) (nth (1- (cdr h)) (gl-tbl saved)))))

; COST: gc_global_new is one step, or the growth's copy of count slots
; and its fill, then the claim
(defun gl-new-steps (g) (if (<= (len (gl-tbl g)) (gl-count g)) (+ 2 (gl-count g)) 1))
(defthm gl-new-cost (implies (gl-ok g) (<= (gl-new-steps g) (+ 2 (gl-count g)))) :rule-classes :linear)
(defun keep-steps (h g) (if (live h g) 1 (1+ (gl-new-steps g))))
(defthm keep-cost (implies (gl-ok g) (<= (keep-steps h g) (+ 3 (gl-count g)))) :rule-classes :linear)

; ---- THE SPARE FRAMES ---------------------------------------------------------------
;
; s%spare/s%nspare (gc_frame_give, gc_frame_take): sp = (u . spares), u
; the heap's used cells. Not roots: every collection empties them
; (forget_young). An allocation takes a cell not in use (heapal-proof). A
; new heap (gc_init, gc_image_read) has no used cell, and empties stack
; 1's spares (clear_batches) -- `fixed`; before the fix it did not.

(defconst *spare-depth* 8)
(defun sp-step (e sp fixed)
  (let ((u (car sp)) (s (cdr sp)))
    (case (car e)
      (:give (if (and (member-equal (cadr e) u) (< (len s) *spare-depth*)) (cons u (cons (cadr e) s)) sp))
      (:take (cons u (cdr s)))
      (:collect (cons (survivors u (cadr e)) nil))
      (:alloc (if (member-equal (cadr e) u) sp (cons (cons (cadr e) u) s)))
      (:reset (cons nil (if fixed nil s)))
      (t sp))))
(defun sp-run (evs sp fixed)
  (if (atom evs) sp (sp-run (cdr evs) (sp-step (car evs) sp fixed) fixed)))

(defthm subsetp-cons-hr (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm subsetp-cdr-hr (implies (subsetp-equal a b) (subsetp-equal (cdr a) b)))

; every spare is a used cell, whatever happens
(defthm spares-used
  (implies (subsetp-equal (cdr sp) (car sp))
           (subsetp-equal (cdr (sp-run evs sp t)) (car (sp-run evs sp t)))))

; so the spare a take hands out is in use, and no allocation can have
; handed it to anyone since it was given (an allocation's cell is not in use)
(defthm spare-taken-is-live
  (implies (and (subsetp-equal (cdr sp) (car sp)) (consp (cdr (sp-run evs sp t))))
           (let ((v (car (cdr (sp-run evs sp t)))))
             (and (member-equal v (car (sp-run evs sp t)))
                  (equal (sp-step (list :alloc v) (sp-run evs sp t) t) (sp-run evs sp t)))))
  :hints (("Goal" :use ((:instance spares-used)) :in-theory (disable spares-used sp-run))))

; before the fix: a frame given, a new heap, and the spare names a cell
; the new heap does not hold -- one it will hand to someone else
(defthm spare-survives-reset-is-stale
  (let ((sp (sp-run '((:alloc 5) (:give 5) (:reset)) '(nil) nil)))
    (and (equal (cdr sp) '(5)) (not (member-equal 5 (car sp))))))

; COST: gc_frame_take one step; gc_frame_give clears its n slots
(defun frame-take-steps (n) (declare (ignore n)) 1)
(defun frame-give-steps (n) (1+ (clear-turns 1 n)))
(defthm frame-give-cost (implies (natp n) (equal (frame-give-steps n) (1+ n)))
  :hints (("Goal" :use ((:instance clear-turns-count (base 0) (top n))))))

; ---- THE POOLS' GROWTH -------------------------------------------------------------
;
; A pool's slot: (contents mark free next) -- obj_pool(i), vec_pool(i) or
; str_pool(i)'s text, with its obj_mark, obj_free, obj_free_next. Past the
; used end (obj_used) a slot is the default: never handed out, on no
; list, not marked (heapal's "the pool's unused end"). grow_obj,
; grow_vec, grow_str: the pool doubled, the old slots copied (grow_str
; moves the texts: move_alloc), the new ones default.

(defconst *slot0* '(nil nil nil 0))
(defun defaults (n) (if (zp n) nil (cons *slot0* (defaults (1- n)))))
(defun all-default (x) (if (atom x) t (and (equal (car x) *slot0*) (all-default (cdr x)))))
(defun pool-ok (cells used)
  (and (true-listp cells) (natp used) (<= used (len cells)) (all-default (nthcdr used cells))))
(defun grow-pool (cells) (append cells (defaults (len cells))))

(defthm len-defaults (equal (len (defaults n)) (nfix n)))
(defthm all-default-append (equal (all-default (append a b)) (and (all-default a) (all-default b))))
(defthm all-default-defaults (all-default (defaults n)))
(defthm nthcdr-append-le
  (implies (<= (nfix k) (len a)) (equal (nthcdr k (append a b)) (append (nthcdr k a) b))))
(defun ind-in (i n) (if (or (zp i) (zp n)) (list i n) (ind-in (1- i) (1- n))))
(defthm nth-defaults (implies (< (nfix i) (nfix n)) (equal (nth i (defaults n)) *slot0*))
  :hints (("Goal" :induct (ind-in i n))))

(defthm grow-keeps
  (implies (< (nfix i) (len cells)) (equal (nth i (grow-pool cells)) (nth i cells))))
(defthm grow-fresh
  (implies (and (true-listp cells) (<= (len cells) (nfix i)) (< (nfix i) (* 2 (len cells))))
           (equal (nth i (grow-pool cells)) *slot0*)))
(defthm pool-ok-grow
  (implies (pool-ok cells used) (pool-ok (grow-pool cells) used)))
; COST: n copied and n filled
(defthm grow-cost (equal (len (grow-pool cells)) (* 2 (len cells))))

; ---- THE TEXTS ----------------------------------------------------------------------
;
; str_pool(i): its text (:none when not allocated -- released, or never
; made) and the code-point index str_index makes from it (ncp, ck),
; abstract here. new_text stores the text and indexes it; the sweep's
; release (hp_release_str) deallocates both; grow_str moves both.

(defstub str-ix (*) => *)
(defun text-ok (c) (and (consp c) (or (eq (car c) :none) (and (stringp (car c)) (equal (cdr c) (str-ix (car c)))))))
(defun texts-ok (ts) (if (atom ts) (null ts) (and (text-ok (car ts)) (texts-ok (cdr ts)))))
(defun new-text (i text ts) (update-nth i (cons text (str-ix text)) ts))
(defun release-text (i ts) (update-nth i (cons :none nil) ts))
(defun none-texts (n) (if (zp n) nil (cons (cons :none nil) (none-texts (1- n)))))
(defun grow-texts (ts) (append ts (none-texts (len ts))))

(defthm texts-ok-update (implies (and (texts-ok ts) (text-ok c) (< (nfix i) (len ts))) (texts-ok (update-nth i c ts))))
(defthm texts-ok-append (implies (and (texts-ok a) (texts-ok b)) (texts-ok (append a b))))
(defthm texts-ok-none (texts-ok (none-texts n)))
(defthm texts-indexed
  (implies (texts-ok ts)
           (and (implies (and (stringp text) (< (nfix i) (len ts))) (texts-ok (new-text i text ts)))
                (implies (< (nfix i) (len ts)) (texts-ok (release-text i ts)))
                (texts-ok (grow-texts ts)))))

; ---- THE IMAGE ---------------------------------------------------------------------
;
; The heap as gc_image_write writes it, after gc_collect with one thread:
; h = (objs vecs store sused chead texts flags g live b) -- the object
; pool as its graph (each object's references), the vector pool, the
; arena and its used length, the free runs' heads (class_head), the text
; pool, the pools' marks, free flags and free lists, the global roots,
; the live counts, and stack 1's binding frame.

(defun h-objs (h) (nth 0 h))
(defun h-vecs (h) (nth 1 h))
(defun h-store (h) (nth 2 h))
(defun h-sused (h) (nth 3 h))
(defun h-chead (h) (nth 4 h))
(defun h-texts (h) (nth 5 h))
(defun h-flags (h) (nth 6 h))
(defun h-g (h) (nth 7 h))
(defun h-live (h) (nth 8 h))
(defun h-b (h) (nth 9 h))
(defun heap-ok (h)
  (and (true-listp (h-store h)) (natp (h-sused h)) (<= (h-sused h) (len (h-store h)))
       (all-nil (nthcdr (h-sused h) (h-store h)))   ; past store_used the arena is nil
       (texts-ok (h-texts h)) (gl-ok (h-g h))))

; a text slot as written: -1 when not allocated, else its length and bytes
(defun enc-texts (ts)
  (if (atom ts) nil
    (cons (if (eq (car (car ts)) :none) -1 (cons (length (car (car ts))) (car (car ts))))
          (enc-texts (cdr ts)))))
; read back: allocated with its text, then str_index
(defun dec-texts (es)
  (if (atom es) nil
    (cons (if (equal (car es) -1) (cons :none nil) (cons (cdr (car es)) (str-ix (cdr (car es)))))
          (dec-texts (cdr es)))))
; what a text slot says: an unallocated one's leftover index is never read
(defun tview (ts)
  (if (atom ts) nil (cons (if (eq (car (car ts)) :none) :none (car ts)) (tview (cdr ts)))))

(defun image-write (h)
  (list :v1 (h-objs h) (h-vecs h) (len (h-store h)) (take (h-sused h) (h-store h)) (h-sused h)
        (h-chead h) (enc-texts (h-texts h)) (h-flags h) (h-g h) (h-live h) (h-b h)))

; gc_image_read: the pools replaced; the arena past store_used nil; the
; young, remembered and aged sets empty, stack 1 fresh, its spares and
; batches gone (clear_batches) -- the parts not modelled as fields; and
; its binding frame kept as a root (D5: its handle is stale, so the keep
; claims the next slot)
(defun image-read (img)
  (let* ((n (nfix (nth 3 img))) (pre (nth 4 img)) (g (nth 9 img)) (b (nth 11 img)))
    (list (nth 1 img) (nth 2 img) (append pre (nils (- n (len pre)))) (nth 5 img) (nth 6 img)
          (dec-texts (nth 7 img)) (nth 8 img) (keep-g nil b g) (nth 10 img) b)))

(defthm tview-dec-enc (implies (texts-ok ts) (equal (tview (dec-texts (enc-texts ts))) (tview ts))))

(defthm take-update-nth-last
  (implies (and (natp c) (< c (len l)))
           (equal (take (1+ c) (update-nth c v l)) (append (take c l) (list v))))
  :hints (("Goal" :induct (ind-in c l) :in-theory (enable take))))
(defthm take-gl-grow (implies (and (natp c) (<= c (len tbl))) (equal (take c (gl-grow tbl c)) (take c tbl))))
(defthm len-gl-grow (implies (and (natp c) (<= c (len tbl))) (< c (len (gl-grow tbl c))))
  :rule-classes :linear)
(in-theory (disable gl-grow))

(defthm nils-len-all-nil
  (implies (and (all-nil x) (true-listp x)) (equal (nils (len x)) x))
  :hints (("Goal" :use ((:instance all-nil-is-nils)))))

(defthm store-roundtrip
  (implies (and (true-listp s) (natp k) (<= k (len s)) (all-nil (nthcdr k s)))
           (equal (append (take k s) (nils (- (len s) k))) s))
  :hints (("Goal" :in-theory (enable take))))

; the pools, the arena, the texts and the roots come back as written; the
; global table and its generation exactly, the binding frame one more root
(defthm image-roundtrip
  (implies (heap-ok h)
           (let ((r (image-read (image-write h))))
             (and (equal (h-objs r) (h-objs h)) (equal (h-vecs r) (h-vecs h))
                  (equal (h-store r) (h-store h)) (equal (h-sused r) (h-sused h))
                  (equal (h-chead r) (h-chead h)) (equal (tview (h-texts r)) (tview (h-texts h)))
                  (equal (h-flags r) (h-flags h)) (equal (h-live r) (h-live h))
                  (equal (gl-gen (h-g r)) (gl-gen (h-g h)))
                  (equal (gl-globals (h-g r)) (append (gl-globals (h-g h)) (list (h-b h)))))))
  :hints (("Goal" :in-theory (disable store-roundtrip) :use ((:instance store-roundtrip (s (h-store h)) (k (h-sused h)))))))

; so the graph the roots reach is the one saved: every path from a root
; of the written heap is a path from a root of the read one
(defthm image-same-graph
  (implies (and (heap-ok h) (path-ok p (h-objs h)) (member-equal (car p) (gl-globals (h-g h))))
           (let ((r (image-read (image-write h))))
             (and (path-ok p (h-objs r)) (member-equal (car p) (gl-globals (h-g r))))))
  :hints (("Goal" :use ((:instance image-roundtrip)) :in-theory (disable image-roundtrip image-read image-write gl-globals))))

; gc_collect before the write: forget_young keeps a remembered object
; only while it holds an aged one, and the full collection unaged every
; one (unage_all) -- so no remembered, aged or young set is left to lose
(defun rem-keep (rem aged heap)
  (cond ((atom rem) nil)
        ((intersectp-equal (kids (car rem) heap) aged) (cons (car rem) (rem-keep (cdr rem) aged heap)))
        (t (rem-keep (cdr rem) aged heap))))
(defthm full-empties-rem (equal (rem-keep rem nil heap) nil))

; COST: one turn a text slot, and its bytes
(defun enc-turns (ts) (if (atom ts) 0 (1+ (enc-turns (cdr ts)))))
(defun enc-bytes (ts)
  (if (atom ts) 0 (+ (if (stringp (car (car ts))) (length (car (car ts))) 0) (enc-bytes (cdr ts)))))
(defthm image-texts-cost
  (and (equal (enc-turns ts) (len ts)) (equal (len (enc-texts ts)) (len ts))))
; the rest are whole arrays: each pool's slots, the arena's used words,
; the global table, and a dozen scalars
(defun image-steps (h)
  (+ (len (h-objs h)) (len (h-vecs h)) (h-sused h) (enc-turns (h-texts h)) (enc-bytes (h-texts h))
     (len (gl-tbl (h-g h))) 12))
(defthm image-cost
  (implies (heap-ok h)
           (<= (image-steps h)
               (+ (len (h-objs h)) (len (h-vecs h)) (len (h-store h)) (len (h-texts h))
                  (enc-bytes (h-texts h)) (len (gl-tbl (h-g h))) 12)))
  :rule-classes :linear)

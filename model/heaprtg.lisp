; The value stack and the global roots at the level the Fortran is
; generated from: heaprt's stack and gl (model/heaprt.lisp) as GC.f90 holds
; them, guard-verified, so scripts/acl2-fortran -b heaprtg writes
; src/f/gen/heaprt_gen.inc and GC.f90's vs_enter_on, vs_leave_on, vs_set_on,
; vs_get_on, gc_stack_new's reset, gc_global_new, gc_global_keep,
; gc_root_get, gc_root_live, gc_global_set, gc_global_get and gc_init's
; table are named shims round it (the global roots: the second half).
;
; The stobj is a thread's gc_stack: s-top its vs_top, s-hi its vs_hi (the
; highest top reached), s-slots0 its slots, 0-based -- slots0(j) is
; vstack(j + 1), the same storage (vstack_make points both at it), so
; slot k of heaprt's stack is index k - 1 here.
;
; Theorems:
;   vsg-abs          the stack heaprt's theorems are about: (live . rest),
;                    live the slots 1 .. top, rest the ones above
;   vsg-inv          top <= hi <= the slots, every slot above the top nil;
;                    it gives heaprt's vs-ok (vsg-inv-vs-ok) and every
;                    operation keeps it
;   vsg-enter-refines, vsg-leave-refines, vsg-set-refines, vsg-get-refines,
;   vsg-reset-refines
;                    each operation is heaprt's on the abstraction: enter
;                    answers the old top as the base, or -1 where heaprt's
;                    is :full (the shim's error stop), and so heaprt's
;                    vs-enter-fresh, frame-balance and ops-keep-callers hold
;                    of the generated stack
;   vsg-clear-cost   the clearing loop turns as heaprt's clear-turns counts:
;                    a leave top - base, a reset hi

(in-package "ACL2")

(include-book "heaprt")
(include-book "heapg")

; no stack has 2^40 slots: CLOTRAN_STACK_SLOTS is a default integer, so
; top + n is inside 64 bits
(defconst *vsb* 1099511627776)

(defstobj vsg
  (s-top :type (signed-byte 64) :initially 0)
  (s-hi :type (signed-byte 64) :initially 0)
  (s-slots0 :type (array t (0)) :initially nil :resizable t))

; ---- THE OPERATIONS (generated) ---------------------------------------------------------

; Every operation's guard asks 0 <= top <= the slots <= 2^40: vsg-inv, which
; each one keeps (the refinement theorems below), so the bounds are proved
; once rather than tested at every call. vs_get is the evaluator's
; commonest call, and a bigger one stopped gfortran inlining it into
; gce_apply_slots (bench/micro.cljf, 2026-11-03: reduce over a range
; 34 ns an element to 50).
(defmacro vsg-bounds (vsg)
  `(and (<= 0 (s-top ,vsg)) (<= (s-top ,vsg) (s-slots0-length ,vsg)) (<= (s-slots0-length ,vsg) *vsb*)))

; vs_enter_on: n slots above the top, the base answered; -1 when they do
; not fit (heaprt's :full). Not cleared: above the top is nil (vsg-inv).
(defun vsg-enter (n vsg)
  (declare (xargs :stobjs vsg :guard (and (integerp n) (vsg-bounds vsg))))
  (let ((top (s-top vsg)) (m (nfix n)))
    (if (< (- (s-slots0-length vsg) top) m)
        (mv -1 vsg)
      (let* ((vsg (update-s-top (+ top m) vsg))
             (vsg (if (< (s-hi vsg) (+ top m)) (update-s-hi (+ top m) vsg) vsg)))
        (mv top vsg)))))

; indices i .. e-1 to nil
(defun vsg-clear (i e vsg)
  (declare (xargs :stobjs vsg
                  :guard (and (natp i) (natp e) (<= e (s-slots0-length vsg)))
                  :measure (nfix (- (ifix e) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp e)) (<= e i)) vsg
    (let ((vsg (update-s-slots0i i nil vsg))) (vsg-clear (1+ i) e vsg))))

; vs_leave_on: back to base, the slots popped cleared -- a stale value
; above the top would be marked; a base outside 0 .. top does nothing
(defun vsg-leave (base vsg)
  (declare (xargs :stobjs vsg :guard (and (integerp base) (vsg-bounds vsg))))
  (let ((top (s-top vsg)))
    (if (or (< base 0) (< top base)) vsg
      (let ((vsg (vsg-clear base top vsg))) (update-s-top base vsg)))))

; vs_set_on, vs_get_on: slots 1 .. top only
(defun vsg-set (k v vsg)
  (declare (xargs :stobjs vsg :guard (and (integerp k) (vsg-bounds vsg))))
  (if (and (<= 1 k) (<= k (s-top vsg)))
      (update-s-slots0i (1- k) v vsg)
    vsg))

(defun vsg-get (k vsg)
  (declare (xargs :stobjs vsg :guard (and (integerp k) (vsg-bounds vsg))))
  (if (and (<= 1 k) (<= k (s-top vsg)))
      (s-slots0i (1- k) vsg)
    nil))

; gc_stack_new on a reused stack: the slots up to the high-water nil, top
; 0. The high-water is not in the bounds: a stack's is tested here, once.
(defun vsg-reset (vsg)
  (declare (xargs :stobjs vsg))
  (let* ((hi (s-hi vsg))
         (vsg (if (and (<= 0 hi) (<= hi (s-slots0-length vsg))) (vsg-clear 0 hi vsg) vsg))
         (vsg (update-s-top 0 vsg)))
    (update-s-hi 0 vsg)))

; ---- THE ABSTRACTION ---------------------------------------------------------------------

(defun vsg-abs (x)
  (let ((a (nth *s-slots0i* x)) (top (nfix (nth 0 x))))
    (cons (take top a) (nthcdr top a))))

(defun vsg-inv (x)
  (let ((a (nth *s-slots0i* x)) (top (nth 0 x)) (hi (nth 1 x)))
    (and (natp top) (integerp hi) (<= top hi) (<= hi (len a)) (<= (len a) *vsb*)
         (all-nil (nthcdr top a)))))

; ---- LISTS -------------------------------------------------------------------------------

(defun clr (i e a)
  (declare (xargs :measure (nfix (- (ifix e) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp e)) (<= e i)) a (clr (1+ i) e (update-nth i nil a))))

(defthm take-1+-update-nth
  (implies (and (natp i) (< i (len a)))
           (equal (take (+ 1 i) (update-nth i v a)) (append (take i a) (list v))))
  :hints (("Goal" :in-theory (enable take) :induct (update-nth i v a))))

(defun ind-ia (i e a) (if (or (zp i) (zp e)) (list i e a) (ind-ia (1- i) (1- e) (cdr a))))

(defthm nthcdr-update-nth-below
  (implies (and (natp i) (natp e) (< i e)) (equal (nthcdr e (update-nth i v a)) (nthcdr e a)))
  :hints (("Goal" :induct (ind-ia i e a))))

(defthm append-assoc-hr (equal (append (append a b) c) (append a (append b c))))

(defthm clr-closed
  (implies (and (natp i) (natp e) (<= i e) (<= e (len a)))
           (equal (clr i e a) (append (take i a) (nils (- e i)) (nthcdr e a))))
  :hints (("Goal" :induct (clr i e a))
          ("Subgoal *1/2" :use ((:instance take-1+-update-nth (v nil))) :expand ((nils (+ e (- i)))))))

(defthm take-nthcdr-append
  (implies (and (natp i) (natp m) (<= (+ i m) (len a)))
           (equal (append (take i a) (take m (nthcdr i a))) (take (+ i m) a)))
  :hints (("Goal" :in-theory (enable take) :induct (nthcdr i a))))

(defthm nthcdr-nthcdr-hr
  (implies (and (natp i) (natp m)) (equal (nthcdr m (nthcdr i a)) (nthcdr (+ i m) a)))
  :hints (("Goal" :induct (nthcdr i a))))

(defthm take-update-nth-in
  (implies (and (natp j) (< j (nfix k)))
           (equal (take k (update-nth j v a)) (update-nth j v (take k a))))
  :hints (("Goal" :in-theory (enable take))))

(defthm nthcdr-take-same (implies (natp n) (equal (nthcdr n (take n x)) nil))
  :hints (("Goal" :in-theory (enable take))))

(defthm true-listp-append-hr (implies (true-listp y) (true-listp (append x y))))

(defthm vsg-all-nil-above
  (implies (and (all-nil (nthcdr top a)) (natp top) (natp hi) (<= top hi))
           (all-nil (nthcdr hi a)))
  :hints (("Goal" :use ((:instance all-nil-nthcdr (x (nthcdr top a)) (n (- hi top)))))))

; ---- THE STOBJ'S FIELDS --------------------------------------------------------------------

(defthm vsg-clear-fields
  (and (equal (nth *s-slots0i* (vsg-clear i e x)) (clr i e (nth *s-slots0i* x)))
       (equal (nth 0 (vsg-clear i e x)) (nth 0 x))
       (equal (nth 1 (vsg-clear i e x)) (nth 1 x)))
  :hints (("Goal" :induct (vsg-clear i e x))))
(defthm vsg-clear-shape
  (implies (< 2 (len x))
           (and (equal (len (vsg-clear i e x)) (len x))
                (consp (vsg-clear i e x)) (consp (cdr (vsg-clear i e x))) (consp (cddr (vsg-clear i e x)))
                (implies (true-listp x) (true-listp (vsg-clear i e x)))))
  :hints (("Goal" :induct (vsg-clear i e x))))
; as the prover meets them once an update of field 0 opens
(defthm vsg-clear-fields-cdr
  (and (equal (nth 1 (cdr (vsg-clear i e x))) (clr i e (nth 2 x)))
       (equal (car (cdr (vsg-clear i e x))) (nth 1 x))
       (equal (car (cddr (vsg-clear i e x))) (clr i e (nth 2 x))))
  :hints (("Goal" :use vsg-clear-fields :in-theory (disable vsg-clear-fields))))

(defthm s-slots0p-true (implies (s-slots0p l) (true-listp l)))
(defthm true-listp-nthcdr-hr (implies (true-listp x) (true-listp (nthcdr n x))))

(defthm vsg-inv-vs-ok
  (implies (and (vsgp x) (vsg-inv x)) (vs-ok (vsg-abs x))))

; ---- REFINEMENT ----------------------------------------------------------------------------

(defthm vsg-enter-refines
  (implies (and (vsgp x) (vsg-inv x) (integerp n))
           (let ((r (vsg-enter n x)))
             (if (equal (vs-enter n (vsg-abs x)) :full)
                 (and (equal (mv-nth 0 r) -1) (equal (mv-nth 1 r) x))
               (and (equal (mv-nth 0 r) (nth 0 x))
                    (equal (vsg-abs (mv-nth 1 r)) (vs-enter n (vsg-abs x)))
                    (vsg-inv (mv-nth 1 r))))))
  :hints (("Goal" :in-theory (disable all-nil-take))))

(defthm vsg-leave-refines
  (implies (and (vsgp x) (vsg-inv x) (integerp base))
           (and (equal (vsg-abs (vsg-leave base x)) (vs-leave base (vsg-abs x)))
                (vsg-inv (vsg-leave base x)))))

(defthm vsg-set-refines
  (implies (and (vsgp x) (vsg-inv x) (integerp k))
           (and (equal (vsg-abs (vsg-set k v x)) (vs-set k v (vsg-abs x)))
                (vsg-inv (vsg-set k v x)))))

(defthm vsg-get-refines
  (implies (and (vsgp x) (vsg-inv x) (integerp k))
           (equal (vsg-get k x) (vs-get k (vsg-abs x)))))

(defthm vsg-reset-refines
  (implies (and (vsgp x) (vsg-inv x))
           (and (equal (vsg-abs (vsg-reset x)) (vs-reset (vsg-abs x)))
                (vsg-inv (vsg-reset x))))
  :hints (("Goal" :use ((:instance all-nil-same-len
                                   (a (append (nils (nth 1 x)) (nthcdr (nth 1 x) (nth *s-slots0i* x))))
                                   (b (append (nils (nth 0 x)) (nthcdr (nth 0 x) (nth *s-slots0i* x)))))))))

; ---- COST ----------------------------------------------------------------------------------

(defun vsg-clear-turns (i e)
  (declare (xargs :measure (nfix (- (ifix e) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp e)) (<= e i)) 0 (1+ (vsg-clear-turns (1+ i) e))))

; the generated loop turns as heaprt counts vs_leave's (base+1 .. top) and
; a reset's (1 .. hi)
(defthm vsg-clear-cost
  (implies (integerp i) (equal (vsg-clear-turns i e) (clear-turns (1+ i) e)))
  :hints (("Goal" :induct (vsg-clear-turns i e))))

; ---- THE GLOBAL ROOTS (generated) ---------------------------------------------------------
;
; heaprt's gl = (gen count tbl) is GC.f90's groots: its gen, its count and
; its table, 0-based -- root idx is tbl(idx - 1). The stobj is that list,
; so each operation is proved EQUAL to heaprt's (glg-new-refines, ...):
; the abstraction is the identity. The state lock round each is the
; host's, hand-written.

(defstobj glg
  (g-gen :type (signed-byte 64) :initially 0)
  (g-count :type (signed-byte 64) :initially 0)
  (g-tbl :type (array t (0)) :initially nil :resizable t))

(defmacro glg-bounds (glg)
  `(and (<= 0 (g-count ,glg)) (<= (g-count ,glg) (g-tbl-length ,glg)) (<= (g-tbl-length ,glg) *vsb*)))

; no table reaches 2^39 roots; past it a claim answers 0, the shim's error stop
(defconst *glb* 549755813888)

; gc_global_new: the next slot, the table grown first if full (max(8, 2 size),
; every slot kept: grow_global_roots)
(defun glg-new (v glg)
  (declare (xargs :stobjs glg :guard (glg-bounds glg)))
  (let ((c (g-count glg)) (n (g-tbl-length glg)))
    (if (and (<= n c) (<= *glb* n)) (mv 0 glg)
      (let ((glg (if (<= n c) (resize-g-tbl (if (< n 4) 8 (* 2 n)) glg) glg)))
        (if (<= (g-tbl-length glg) c) (mv 0 glg)
          (let* ((glg (update-g-tbli c v glg)) (glg (update-g-count (1+ c) glg)))
            (mv (1+ c) glg)))))))

; a handle (hgen . hidx) is live when its generation is this heap's and
; hidx a claimed slot
(defun glg-live (hgen hidx glg)
  (declare (xargs :stobjs glg :guard (and (integerp hgen) (integerp hidx))))
  (and (equal hgen (g-gen glg)) (<= 1 hidx) (<= hidx (g-count glg))))

; gc_root_get: the slot, or nil when the handle is stale
(defun glg-get (hgen hidx glg)
  (declare (xargs :stobjs glg :guard (and (integerp hgen) (integerp hidx) (glg-bounds glg))))
  (if (glg-live hgen hidx glg) (g-tbli (1- hidx) glg) nil))

; gc_global_keep: the slot rewritten when the handle is live, else claimed
; anew; the handle answered
(defun glg-keep (hgen hidx v glg)
  (declare (xargs :stobjs glg :guard (and (integerp hgen) (integerp hidx) (glg-bounds glg))))
  (if (glg-live hgen hidx glg)
      (let ((glg (update-g-tbli (1- hidx) v glg))) (mv hgen hidx glg))
    (mv-let (i glg) (glg-new v glg) (mv (g-gen glg) i glg))))

; gc_global_set, gc_global_get: by index, this heap's
(defun glg-set (idx v glg)
  (declare (xargs :stobjs glg :guard (and (integerp idx) (glg-bounds glg))))
  (if (and (<= 1 idx) (<= idx (g-count glg))) (update-g-tbli (1- idx) v glg) glg))

(defun glg-at (idx glg)
  (declare (xargs :stobjs glg :guard (and (integerp idx) (glg-bounds glg))))
  (if (and (<= 1 idx) (<= idx (g-count glg))) (g-tbli (1- idx) glg) nil))

; gc_init: a new generation, an empty table of 8
(defun glg-init (glg)
  (declare (xargs :stobjs glg))
  (let* ((gen (g-gen glg))
         (glg (update-g-gen (if (and (<= 0 gen) (< gen *glb*)) (1+ gen) 1) glg))
         (glg (update-g-count 0 glg))
         (glg (resize-g-tbl 0 glg)))
    (resize-g-tbl 8 glg)))

; ---- the global roots: refinement

(defun glg-inv (x)
  (and (natp (nth 0 x)) (< (nth 0 x) *glb*) (natp (nth 1 x)) (<= (nth 1 x) (len (nth 2 x)))
       (<= (len (nth 2 x)) *vsb*) (all-nil (nthcdr (nth 1 x) (nth 2 x)))))

(defthm resize-list-grows
  (implies (and (true-listp l) (natp n) (<= (len l) n))
           (equal (resize-list l n nil) (append l (nils (- n (len l))))))
  :hints (("Goal" :induct (resize-list l n nil))))

(defthm all-nil-nils-hr (all-nil (nils n)))

(defthm append-take-nthcdr-hr
  (implies (and (natp c) (<= c (len l))) (equal (append (take c l) (nthcdr c l)) l))
  :hints (("Goal" :in-theory (enable take))))

(defthm append-nils-absorb
  (implies (and (all-nil b) (true-listp b) (natp j))
           (equal (append b (nils j)) (nils (+ (len b) j))))
  :hints (("Goal" :use ((:instance all-nil-is-nils (x b))))))

; grow_global_roots keeps the whole table; heaprt's gl-grow the claimed
; slots and nils: the same table when the slots past the count are nil
(defthm append-take-all-nil
  (implies (and (true-listp l) (natp c) (<= c (len l)) (all-nil (nthcdr c l)) (natp m) (<= (len l) m))
           (equal (append (take c l) (nils (- m c))) (append l (nils (- m (len l))))))
  :hints (("Goal" :use ((:instance append-take-nthcdr-hr)
                        (:instance append-nils-absorb (b (nthcdr c l)) (j (- m (len l)))))
                  :in-theory (disable append-take-nthcdr-hr append-nils-absorb))))

(defthm nthcdr-cdr-hr (implies (natp c) (equal (nthcdr c (cdr l)) (cdr (nthcdr c l)))))
(defthm all-nil-cdr-hr (implies (all-nil x) (all-nil (cdr x))))

; a stobj of three fields is the list of them
(defthm update-nth-2-of-3
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (update-nth 2 b x) (list (nth 0 x) (nth 1 x) b)))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x))))))
(defthm update-nth-0-of-3
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (update-nth 0 b x) (list b (nth 1 x) (nth 2 x))))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x))))))
(defthm update-nth-1-of-3
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (update-nth 1 b x) (list (nth 0 x) b (nth 2 x))))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x))))))

(defthm take-len-equal (implies (and (true-listp l) (equal c (len l))) (equal (take c l) l)))

(defthm len-cdr-hr (equal (len (cdr y)) (if (consp y) (1- (len y)) 0)))

(defthm append-empty-hr (implies (and (true-listp l) (equal (len l) 0)) (equal (append l y) y)))

(defthm len-gl-grow-is
  (implies (and (natp c) (<= c (len tbl)))
           (equal (len (gl-grow tbl c)) (max 8 (* 2 (len tbl)))))
  :hints (("Goal" :in-theory (enable gl-grow))))

(defthm g-tblp-true (implies (g-tblp l) (true-listp l)))

(defthm glg-new-refines
  (implies (and (glgp x) (glg-inv x) (< (len (nth 2 x)) *glb*))
           (and (equal (mv-nth 0 (glg-new v x)) (1+ (nth 1 x)))
                (equal (mv-nth 1 (glg-new v x)) (gl-new v x))
                (glg-inv (mv-nth 1 (glg-new v x)))))
  :hints (("Goal" :in-theory (enable gl-grow))))

(defthm glg-inv-gl-new
  (implies (and (glgp x) (glg-inv x) (< (len (nth 2 x)) *glb*))
           (and (natp (nth 1 (gl-new v x))) (<= (nth 1 (gl-new v x)) (len (nth 2 (gl-new v x))))
                (<= (len (nth 2 (gl-new v x))) *vsb*)
                (all-nil (nthcdr (nth 1 (gl-new v x)) (nth 2 (gl-new v x))))))
  :hints (("Goal" :use glg-new-refines :in-theory (disable glg-new-refines glg-new gl-new))))

(defthm gl-new-fields
  (and (equal (car (gl-new v g)) (nth 0 g))
       (equal (nth 0 (gl-new v g)) (nth 0 g))
       (equal (nth 1 (gl-new v g)) (1+ (nth 1 g)))))

(defthm glg-live-is-live
  (implies (integerp hidx) (equal (glg-live hgen hidx x) (live (cons hgen hidx) x))))

(defthm glg-get-refines
  (implies (and (glgp x) (glg-inv x) (integerp hidx))
           (equal (glg-get hgen hidx x) (root-get (cons hgen hidx) x))))

(defthm glg-keep-refines
  (implies (and (glgp x) (glg-inv x) (integerp hidx) (< (len (nth 2 x)) *glb*))
           (let ((r (glg-keep hgen hidx v x)))
             (and (equal (cons (mv-nth 0 r) (mv-nth 1 r)) (keep-h (cons hgen hidx) x))
                  (equal (mv-nth 2 r) (keep-g (cons hgen hidx) v x))
                  (glg-inv (mv-nth 2 r)))))
  :hints (("Goal" :use ((:instance glg-inv-gl-new)) :in-theory (disable glg-new gl-new glg-inv-gl-new))))

(defthm glg-set-refines
  (implies (and (glgp x) (glg-inv x) (integerp idx))
           (and (equal (glg-set idx v x) (if (live (cons (nth 0 x) idx) x) (keep-g (cons (nth 0 x) idx) v x) x))
                (glg-inv (glg-set idx v x)))))

(defthm glg-at-refines
  (implies (and (glgp x) (glg-inv x) (integerp idx))
           (equal (glg-at idx x) (root-get (cons (nth 0 x) idx) x))))

(defthm glg-init-refines
  (implies (and (glgp x) (glg-inv x) (< (1+ (nth 0 x)) *glb*))
           (and (equal (glg-init x) (gl-init x))
                (glg-inv (glg-init x)))))

; ---- THE ROOTS PUSHED (generated) ----------------------------------------------------------
;
; push_roots: every global root, then every thread's stack to its top, then
; the allocation's own, each pushed onto the collector's mark stack by
; heapg's hpg-push (push_mark). The two loops over the stobjs are
; generated; the walk over the threads (stacks(i)%s, a thread with no
; stack skipped) and over the allocation's roots(:) is the shim's.
;
; A value reaches the marker as its tag and its ref: gv-tag, gv-ref, the
; host's v%tag and v%ref (a nil slot is tag 0, ref 0, which hpg-push
; ignores).

(defun gv-tag (v) (declare (xargs :guard t)) (if (and (consp v) (sb64p (car v))) (car v) 0))
(defun gv-ref (v) (declare (xargs :guard t)) (if (and (consp v) (sb64p (cdr v))) (cdr v) 0))

; values vs pushed in order: what push_roots does with the rootset
(defun push-vals (vs hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (if (atom vs) hpg
    (let ((hpg (hpg-push (gv-tag (car vs)) (gv-ref (car vs)) hpg)))
      (push-vals (cdr vs) hpg))))

; a stack's slots i .. top-1 (slots i+1 .. top)
(defun vsg-push (i vsg hpg)
  (declare (xargs :stobjs (vsg hpg)
                  :guard (and (natp i) (vsg-bounds vsg) (hpg-ok hpg))
                  :measure (nfix (- (ifix (s-top vsg)) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp (s-top vsg))) (<= (s-top vsg) i))
      hpg
    (let* ((v (s-slots0i i vsg))
           (hpg (hpg-push (gv-tag v) (gv-ref v) hpg)))
      (vsg-push (1+ i) vsg hpg))))

; the global roots i .. count-1
(defun glg-push (i glg hpg)
  (declare (xargs :stobjs (glg hpg)
                  :guard (and (natp i) (glg-bounds glg) (hpg-ok hpg))
                  :measure (nfix (- (ifix (g-count glg)) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp (g-count glg))) (<= (g-count glg) i))
      hpg
    (let* ((v (g-tbli i glg))
           (hpg (hpg-push (gv-tag v) (gv-ref v) hpg)))
      (glg-push (1+ i) glg hpg))))

; ---- the roots pushed: refinement

(defthm nthcdr-cons-nth-hr
  (implies (and (natp i) (< i (len l))) (equal (nthcdr i l) (cons (nth i l) (nthcdr (1+ i) l))))
  :rule-classes nil :hints (("Goal" :induct (nthcdr i l))))

(defthm nthcdr-take-past
  (implies (and (natp i) (natp k) (<= k i)) (not (consp (nthcdr i (take k a)))))
  :hints (("Goal" :in-theory (enable take) :induct (ind-ia i k a))))

(defthm vsg-push-is
  (implies (and (natp i) (natp (nth 0 x)) (<= (nth 0 x) (len (nth *s-slots0i* x))))
           (equal (vsg-push i x h) (push-vals (nthcdr i (take (nth 0 x) (nth *s-slots0i* x))) h)))
  :hints (("Goal" :induct (vsg-push i x h))
          ("Subgoal *1/2" :use ((:instance nthcdr-cons-nth-hr (l (take (nth 0 x) (nth *s-slots0i* x))))))))

; a stack's push is its live slots' -- heaprt's (car (vsg-abs x)), what
; rootset takes of each stack
(defthm vsg-push-refines
  (implies (and (vsgp x) (vsg-inv x))
           (equal (vsg-push 0 x h) (push-vals (car (vsg-abs x)) h))))

(defthm glg-push-is
  (implies (and (natp i) (natp (nth 1 x)) (<= (nth 1 x) (len (nth 2 x))))
           (equal (glg-push i x h) (push-vals (nthcdr i (take (nth 1 x) (nth 2 x))) h)))
  :hints (("Goal" :induct (glg-push i x h))
          ("Subgoal *1/2" :use ((:instance nthcdr-cons-nth-hr (l (take (nth 1 x) (nth 2 x))))))))

; the globals' push is heaprt's gl-globals'
(defthm glg-push-refines
  (implies (and (glgp x) (glg-inv x))
           (equal (glg-push 0 x h) (push-vals (gl-globals x) h))))

(defthm push-vals-append
  (equal (push-vals (append a b) h) (push-vals b (push-vals a h))))

; each stack's push in turn, as the shim walks the threads
(defun push-stacks (stacks hpg)
  (declare (xargs :stobjs hpg :verify-guards nil))
  (if (atom stacks) hpg (let ((hpg (push-vals (car (car stacks)) hpg))) (push-stacks (cdr stacks) hpg))))

(defthm push-stacks-is-lives
  (equal (push-stacks stacks h) (push-vals (lives stacks) h)))

; push_roots -- the globals' push, each stack's, then the own -- pushes
; exactly heaprt's rootset, the set heaprt's rooted-path-survives keeps
(defthm push-roots-refines
  (equal (push-vals own (push-stacks stacks (push-vals globals h)))
         (push-vals (rootset globals stacks own) h)))

; COST: one turn a root, heaprt's push-roots-steps
(defun push-turns (i e)
  (declare (xargs :measure (nfix (- (ifix e) (ifix i)))))
  (if (or (not (integerp i)) (not (integerp e)) (<= e i)) 0 (1+ (push-turns (1+ i) e))))
(defthm push-turns-count
  (implies (and (natp i) (natp e) (<= i e)) (equal (push-turns i e) (- e i)))
  :hints (("Goal" :induct (push-turns i e))))
(defthm vsg-push-cost
  (implies (and (vsgp x) (vsg-inv x)) (equal (push-turns 0 (nth 0 x)) (len (car (vsg-abs x))))))
(defthm glg-push-cost
  (implies (and (glgp x) (glg-inv x)) (equal (push-turns 0 (nth 1 x)) (len (gl-globals x)))))

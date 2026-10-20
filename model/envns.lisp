; clotran's environments and namespaces, formally (docs/model-coverage.md).
;
; src/f/Env.f90 keeps the lexical environment as frames on the heap, each
; an array map of bindings, the frame outside it (nil for a root) and
; the namespace it was defined in (gce_new, gce_set, gce_find,
; gce_set_ns, gce_defining_ns). gce_set MUTATES its frame: a closure
; holding the frame sees a later binding. Here the heap is a list of
; frames, a frame's id its 1-based place, 0 nil; gce_new appends one,
; whose outer is 0 or an older frame.
;
; src/f/Namespace.f90 keeps the namespace registry (name -> namespace) in
; a global root and each namespace's mappings (name -> Var) and aliases
; in its slots 2 and 3. Every write of one of those is a compare-and-swap
; retried from what is there now (model/casloop.lisp): gcn_intern,
; register (gcn_find_or_create), gcn_remove, gcn_slot_assoc (.refer,
; .addAlias), gcn_slot_dissoc (.unmap) and gce_refer_core (Eval.f90).
; Here a map is an alist -- the registry and the mappings are gca maps,
; whatever their shape, and answer as one -- and each operation is ns-next
; (the new map, from the one read), ns-noop (nothing to write) and
; ns-result (what it answers).
;
; What it proves:
;
;   ENV        frames' outers only point older (env-wf), which gce_new and
;              gce_set keep, so gce_find's walk ends; a new frame changes
;              no older frame's lookups and starts as its outer; after
;              gce_set e k v, k is v from e, other keys are as they were
;              from every frame, and k from any frame e2 is v exactly when
;              e is on e2's walk up to where k was found -- the sharing a
;              closure's frame relies on; a new frame's namespace is its
;              outer's
;   NS         intern in a namespace that owns the Var keeps the Var
;              (redefinition reaches every closure holding it); intern
;              over a Var only referred from another namespace maps a new
;              one and leaves the other alone (the clojure.zip bug);
;              register returns the namespace a name already has, so two
;              find-or-creates between removes give one namespace
;   CONCURRENT every one of those, from any number of threads at once, is
;              linearizable, each exactly once, lock-free, with at most
;              2N + 2 steps a thread (casloop's theorems, instantiated);
;              the read-assoc-store it replaced loses an update
;              (rmw-loses-an-update) -- 40% of eight threads' create-ns did
;   COST       gce_find takes at most 2 B + 2 e steps from frame e, B the
;              bindings in frames 1..e: each frame at most once, as the ids
;              fall outward; the CAS loops' 2N + 2 a thread as above
;
; Not modelled: the rooting (vs_enter), and the Var's root cell (its own
; atomic write under the state lock).

(in-package "ACL2")

(include-book "arraymap")
(include-book "casloop")

; the array map through arraymap's theorems only
(in-theory (disable am-wf am-assoc am-keys am-vals am-count am-make am-get-is-lookup))

(defthm member-keys-am-assoc
  (iff (member-equal k2 (am-keys (am-assoc m k v))) (or (equal k2 k) (member-equal k2 (am-keys m))))
  :hints (("Goal" :use ((:instance am-assoc-contains) (:instance am-contains-is-member (m (am-assoc m k v)) (k k2))
                        (:instance am-contains-is-member (k k2)))
                  :in-theory (disable am-assoc-contains am-contains-is-member))))

(defthm am-index-steps-count
  (implies (am-wf m) (<= (am-index-steps (am-keys m) k) (am-count m)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance am-cost)) :in-theory (disable am-cost))))

; ---- ENV ---------------------------------------------------------------------

(defun fr-map (fr) (car fr))
(defun fr-outer (fr) (nfix (cadr fr)))
(defun fr-ns (fr) (nfix (caddr fr)))

(defconst *am-empty* (list 0 nil nil))

; frames 1..k: each map well formed, each outer older than its frame
(defun env-wf-k (k h)
  (if (zp k) t
    (and (am-wf (fr-map (nth (1- k) h))) (< (fr-outer (nth (1- k) h)) k)
         (env-wf-k (1- k) h))))

(defun env-wf (h) (env-wf-k (len h) h))

(defthm env-wf-k-frame
  (implies (and (env-wf-k k h) (natp k) (posp j) (<= j k))
           (and (am-wf (car (nth (1- j) h))) (< (nfix (cadr (nth (1- j) h))) j))))

; gce_find: the first frame outward that binds k -- found and its value
(defun env-find (h e k)
  (declare (xargs :measure (nfix e)))
  (if (or (zp e) (< (len h) e)) (mv nil nil)
    (let ((fr (nth (1- e) h)))
      (if (am-contains (fr-map fr) k) (mv t (am-get (fr-map fr) k))
        (if (< (fr-outer fr) e) (env-find h (fr-outer fr) k) (mv nil nil))))))

; the frames that walk reads, up to the one that binds k
(defun env-walk (h e k)
  (declare (xargs :measure (nfix e)))
  (if (or (zp e) (< (len h) e)) nil
    (let ((fr (nth (1- e) h)))
      (if (am-contains (fr-map fr) k) (list e)
        (if (< (fr-outer fr) e) (cons e (env-walk h (fr-outer fr) k)) (list e))))))

; gce_new: a frame with no bindings, outside it outer; its id is len + 1
(defun env-new (h outer) (append h (list (list *am-empty* outer 0))))

; gce_set: the frame's bindings map replaced by the assoc, in place
(defun env-set (h e k v)
  (if (or (zp e) (< (len h) e)) h
    (let ((fr (nth (1- e) h)))
      (update-nth (1- e) (list (am-assoc (fr-map fr) k v) (cadr fr) (caddr fr)) h))))

; gce_set_ns and gce_defining_ns: the first frame outward with a namespace
(defun env-set-ns (h e idx)
  (if (or (zp e) (< (len h) e)) h
    (let ((fr (nth (1- e) h))) (update-nth (1- e) (list (car fr) (cadr fr) idx) h))))

(defun env-ns (h e)
  (declare (xargs :measure (nfix e)))
  (if (or (zp e) (< (len h) e)) 0
    (let ((fr (nth (1- e) h)))
      (if (not (equal (fr-ns fr) 0)) (fr-ns fr)
        (if (< (fr-outer fr) e) (env-ns h (fr-outer fr)) 0)))))

(defthm env-wf-k-append
  (implies (<= (nfix k) (len h)) (equal (env-wf-k k (append h x)) (env-wf-k k h))))

(defthm am-wf-empty (am-wf *am-empty*) :hints (("Goal" :in-theory (enable am-wf am-keys am-vals))))

(defthm env-new-wf
  (implies (and (env-wf h) (<= (nfix outer) (len h))) (env-wf (env-new h outer))))

(defthm env-find-append
  (implies (<= (nfix e) (len h)) (equal (env-find (append h x) e k) (env-find h e k)))
  :hints (("Goal" :induct (env-find h e k) :expand ((env-find (append h x) e k)))))

(defthm env-ns-append
  (implies (<= (nfix e) (len h)) (equal (env-ns (append h x) e) (env-ns h e)))
  :hints (("Goal" :induct (env-ns h e) :expand ((env-ns (append h x) e)))))

; a new frame changes no older frame's lookups ...
(defthm env-new-old-find
  (implies (<= (nfix e) (len h)) (equal (env-find (env-new h o) e k) (env-find h e k))))

; ... and starts as its outer, its namespace too
(defthm am-contains-empty (not (am-contains *am-empty* k)) :hints (("Goal" :in-theory (enable am-contains am-index))))

(defthm env-new-find
  (implies (<= (nfix o) (len h))
           (equal (env-find (env-new h o) (1+ (len h)) k) (env-find h (nfix o) k)))
  :hints (("Goal" :do-not-induct t :expand ((env-find (append h (list (list *am-empty* o 0))) (1+ (len h)) k)))))

(defthm env-new-ns
  (implies (<= (nfix o) (len h))
           (equal (env-ns (env-new h o) (1+ (len h))) (env-ns h (nfix o))))
  :hints (("Goal" :do-not-induct t :expand ((env-ns (append h (list (list *am-empty* o 0))) (1+ (len h)))))))

(defthm env-wf-k-set
  (implies (and (env-wf-k k h) (posp e) (<= e (len h)) (<= k (len h)))
           (env-wf-k k (env-set h e key v))))

(defthm env-set-wf
  (implies (env-wf h) (env-wf (env-set h e k v)))
  :hints (("Goal" :use ((:instance env-wf-k-set (k (len h)) (key k))) :in-theory (disable env-wf-k-set) :do-not-induct t)))

(defthm len-env-set (equal (len (env-set h e k v)) (len h)))

(defthm nth-env-set
  (equal (nth i (env-set h e k v))
         (if (and (posp e) (<= e (len h)) (equal (nfix i) (1- e)))
             (list (am-assoc (car (nth (1- e) h)) k v) (cadr (nth (1- e) h)) (caddr (nth (1- e) h)))
           (nth i h))))

(in-theory (disable env-set))

; after gce_set e k v: k is v from e ...
(defthm env-set-find-same
  (implies (and (env-wf h) (posp e) (<= e (len h)))
           (equal (env-find (env-set h e k v) e k) (mv t v)))
  :hints (("Goal" :do-not-induct t :expand ((env-find (env-set h e k v) e k)))))

; ... other keys as they were, from every frame ...
(defthm env-set-find-other
  (implies (and (env-wf h) (not (equal k2 k)))
           (equal (env-find (env-set h e k v) e2 k2) (env-find h e2 k2)))
  :hints (("Goal" :induct (env-find h e2 k2) :expand ((env-find (env-set h e k v) e2 k2)))))

; ... and k from any frame e2 is v exactly when e is on e2's walk to k
(defthm env-set-shared
  (implies (and (env-wf h) (posp e) (<= e (len h)))
           (equal (env-find (env-set h e k v) e2 k)
                  (if (member-equal e (env-walk h e2 k)) (mv t v) (env-find h e2 k))))
  :hints (("Goal" :induct (env-find h e2 k) :expand ((env-find (env-set h e k v) e2 k)))))

(defthm env-set-ns-own
  (implies (and (posp e) (<= e (len h)) (posp idx))
           (equal (env-ns (env-set-ns h e idx) e) idx))
  :hints (("Goal" :expand ((env-ns (env-set-ns h e idx) e)))))

; COST: gce_find reads, a frame, gcm_contains's scan and one step, and
; where it binds k gcm_get's scan and one more
(defun env-find-steps (h e k)
  (declare (xargs :measure (nfix e)))
  (if (or (zp e) (< (len h) e)) 0
    (let* ((fr (nth (1- e) h)) (s (am-index-steps (am-keys (fr-map fr)) k)))
      (if (am-contains (fr-map fr) k) (+ s 1 s 1)
        (if (< (fr-outer fr) e) (+ s 1 (env-find-steps h (fr-outer fr) k)) (+ s 1))))))

; the bindings in frames 1..e
(defun env-total (h e)
  (if (zp e) 0 (+ (am-count (fr-map (nth (1- e) h))) (env-total h (1- e)))))

(defthm am-count-natp (natp (am-count m)) :rule-classes :type-prescription :hints (("Goal" :in-theory (enable am-count))))

(defthm env-total-mono
  (implies (and (natp a) (natp b) (<= a b)) (<= (env-total h a) (env-total h b)))
  :rule-classes :linear
  :hints (("Goal" :induct (env-total h b))))

(defthm env-total-below
  (implies (and (natp a) (natp b) (< a b)) (<= (env-total h a) (env-total h (+ -1 b))))
  :rule-classes ((:linear :trigger-terms ((env-total h a)))))

(defthm env-find-cost
  (implies (and (env-wf h) (natp e))
           (<= (env-find-steps h e k) (+ (env-total h e) (env-total h e) e e)))
  :hints (("Goal" :induct (env-find-steps h e k))
          (and stable-under-simplificationp
               (quote (:use ((:instance env-total-below (a (nfix (cadr (nth (+ -1 e) h)))) (b e))
                             (:instance am-index-steps-count (m (car (nth (+ -1 e) h))))
                             (:instance env-wf-k-frame (k (len h)) (j e))))))))

; ---- NS: the operations on a namespace's mappings and on the registry ----------
;
; a Var (:var id owner); an op one of
;   (:intern sym var ns)  gcn_intern: a Var ns owns is kept (its root is
;                         written, not the map); else var is mapped
;   (:assoc k v)          gcn_slot_assoc: .refer, .addAlias
;   (:dissoc k)           gcn_slot_dissoc, gcn_remove: .unmap, remove-ns
;   (:register name ns)   register: the namespace already there, else ns
;   (:refer-all es)       gce_refer_core: es core's public Vars (k v private),
;                         a private one dropped where it is still mapped,
;                         the rest mapped where the name is free

(defun ns-var-p (x) (and (consp x) (eq (car x) :var)))
(defun ns-var-owner (x) (caddr x))

(defun ns-own-var (sym ns m)
  (let ((ex (cdr (assoc-equal sym m)))) (and (ns-var-p ex) (equal (ns-var-owner ex) ns))))

(defun ns-refer-all (es m)
  (if (atom es) m
    (let* ((e (car es)) (k (car e)) (v (cadr e)) (priv (caddr e)))
      (ns-refer-all (cdr es)
                    (cond (priv (if (equal (cdr (assoc-equal k m)) v) (remove1-assoc-equal k m) m))
                          ((assoc-equal k m) m)
                          (t (put-assoc-equal k v m)))))))

(defun ns-next (op m)
  (case (car op)
    (:intern (if (ns-own-var (cadr op) (cadddr op) m) m (put-assoc-equal (cadr op) (caddr op) m)))
    (:assoc (put-assoc-equal (cadr op) (caddr op) m))
    (:dissoc (remove1-assoc-equal (cadr op) m))
    (:register (if (consp (assoc-equal (cadr op) m)) m (put-assoc-equal (cadr op) (caddr op) m)))
    (:refer-all (ns-refer-all (cadr op) m))
    (otherwise m)))

; where the Fortran finds nothing to write and returns without a CAS
(defun ns-noop (op m)
  (case (car op)
    (:intern (ns-own-var (cadr op) (cadddr op) m))
    (:dissoc (equal (remove1-assoc-equal (cadr op) m) m))
    (:register (consp (assoc-equal (cadr op) m)))
    (otherwise nil)))

(defun ns-result (op m)
  (case (car op)
    (:intern (if (ns-own-var (cadr op) (cadddr op) m) (cdr (assoc-equal (cadr op) m)) (caddr op)))
    (:register (if (consp (assoc-equal (cadr op) m)) (cdr (assoc-equal (cadr op) m)) (caddr op)))
    (:dissoc (cdr (assoc-equal (cadr op) m)))
    (otherwise nil)))

(defthm ns-noop-writes-nothing
  (implies (ns-noop op m) (equal (ns-next op m) m)))

(defthm assoc-put-assoc-ns
  (equal (assoc-equal k2 (put-assoc-equal k v m))
         (if (equal k2 k) (cons k v) (assoc-equal k2 m))))

(defthm assoc-remove1-assoc-ns
  (implies (not (equal k2 k))
           (equal (assoc-equal k2 (remove1-assoc-equal k m)) (assoc-equal k2 m))))

; intern in the namespace that owns the Var: the same Var, nothing written
; -- a redefinition reaches every closure that holds it
(defthm ns-intern-keeps-the-var
  (implies (and (ns-var-p v1) (equal (ns-var-owner v1) ns))
           (let* ((op1 (list :intern s v1 ns)) (op2 (list :intern s v2 ns))
                  (m1 (ns-next op1 m)))
             (and (ns-noop op2 m1)
                  (equal (ns-result op2 m1) (ns-result op1 m))))))

; intern over a Var another namespace owns (a refer): a new Var mapped,
; the other one's own namespace not touched -- a different cell
(defthm ns-intern-shadows-a-refer
  (implies (and (ns-var-p (cdr (assoc-equal s m)))
                (not (equal (ns-var-owner (cdr (assoc-equal s m))) ns)))
           (let ((op (list :intern s v ns)))
             (and (not (ns-noop op m))
                  (equal (ns-result op m) v)
                  (equal (cdr (assoc-equal s (ns-next op m))) v)))))

; ops in order, and ops that leave name n alone
(defun ns-apply (os m) (if (atom os) m (ns-apply (cdr os) (ns-next (car os) m))))

(defun ns-avoid (n os)
  (if (atom os) t
    (and (member-equal (car (car os)) '(:intern :assoc :dissoc :register))
         (not (equal (cadr (car os)) n))
         (ns-avoid n (cdr os)))))

(defthm ns-avoid-keeps-assoc
  (implies (ns-avoid n os) (equal (assoc-equal n (ns-apply os m)) (assoc-equal n m))))

; ONE NAMESPACE A NAME: two find-or-creates of n with nothing between them
; that maps or removes n answer the same namespace
(defthm ns-one-namespace-per-name
  (implies (ns-avoid n mid)
           (equal (ns-result (list :register n y) (ns-apply mid (ns-next (list :register n x) m)))
                  (ns-result (list :register n x) m))))

; ---- CONCURRENT: casloop's theorems, for these ops -------------------------------
;
; casloop's machine with ns-next, ns-noop and ns-result for its op-next,
; op-noop and op-result: the copies a functional instance needs

(defun ns-replay-ok (hist s ops)
  (if (atom hist) t
    (and (consp (car hist)) (equal (cdar hist) s)
         (ns-replay-ok (cdr hist) (ns-next (nth (caar hist) ops) s) ops))))

(defun ns-replay-final (hist s ops)
  (if (atom hist) s
    (ns-replay-final (cdr hist) (ns-next (nth (caar hist) ops) (cdar hist)) ops)))

(defun ns-cas-step (i b st ops)
  (let* ((cell (nth 0 st)) (count (nth 1 st)) (hist (nth 2 st)) (ths (nth 3 st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let* ((x (nth i ths)) (op (nth i ops)))
        (case (th-pc x)
          (:read (if (ns-noop op cell)
                     (list cell count (append hist (list (cons i cell)))
                           (update-nth i (mk-th :done cell 0 (th-fails x) (1+ (th-steps x)) (ns-result op cell)) ths))
                   (list cell count hist
                         (update-nth i (mk-th :cas cell count (th-fails x) (1+ (th-steps x)) nil) ths))))
          (:cas (if (and (equal cell (th-snap x)) (or (equal count (th-snapc x)) (not b)))
                    (list (ns-next op cell) (1+ count) (append hist (list (cons i cell)))
                          (update-nth i (mk-th :done cell 0 (th-fails x) (1+ (th-steps x)) (ns-result op cell)) ths))
                  (list cell count hist
                        (update-nth i (mk-th :read nil 0 (1+ (th-fails x)) (1+ (th-steps x)) nil) ths))))
          (otherwise st))))))

(defun ns-cas-run (sched st ops)
  (if (atom sched) st
    (ns-cas-run (cdr sched) (ns-cas-step (caar sched) (cdar sched) st ops) ops)))


; LINEARIZABLE, each op on the value it read, answering from it
(defthm ns-linearizable
  (let ((st (ns-cas-run sched (cas-start n cell0) ops)))
    (and (ns-replay-ok (nth 2 st) cell0 ops)
         (equal (ns-replay-final (nth 2 st) cell0 ops) (nth 0 st))))
  :hints (("Goal" :use ((:functional-instance cas-linearizable
                         (op-next ns-next) (op-noop ns-noop) (op-result ns-result)
                         (replay-ok ns-replay-ok) (replay-final ns-replay-final)
                         (cas-step ns-cas-step) (cas-run ns-cas-run))))))

(defthm ns-results
  (let ((st (ns-cas-run sched (cas-start n cell0) ops)))
    (implies (and (natp i) (< i (nfix n)) (equal (th-pc (nth i (nth 3 st))) :done))
             (equal (th-result (nth i (nth 3 st)))
                    (ns-result (nth i ops) (cdr (assoc-equal i (nth 2 st)))))))
  :hints (("Goal" :use ((:functional-instance cas-results
                         (op-next ns-next) (op-noop ns-noop) (op-result ns-result)
                         (replay-ok ns-replay-ok) (replay-final ns-replay-final)
                         (cas-step ns-cas-step) (cas-run ns-cas-run))))))

; EXACTLY ONCE: no lost update, none doubled
(defthm ns-exactly-once
  (let ((st (ns-cas-run sched (cas-start n cell0) ops)))
    (and (no-duplicatesp-equal (strip-cars (nth 2 st)))
         (implies (and (natp i) (< i (nfix n)))
                  (iff (assoc-equal i (nth 2 st))
                       (equal (th-pc (nth i (nth 3 st))) :done)))))
  :hints (("Goal" :use ((:functional-instance cas-exactly-once
                         (op-next ns-next) (op-noop ns-noop) (op-result ns-result)
                         (replay-ok ns-replay-ok) (replay-final ns-replay-final)
                         (cas-step ns-cas-step) (cas-run ns-cas-run))))))

; COST: at most 2N + 2 steps a thread
(defthm ns-cas-cost
  (let ((st (ns-cas-run sched (cas-start n cell0) ops)))
    (implies (and (natp i) (< i (nfix n)))
             (and (<= (th-fails (nth i (nth 3 st))) (nfix n))
                  (<= (th-steps (nth i (nth 3 st))) (+ 2 (* 2 (nfix n)))))))
  :hints (("Goal" :use ((:functional-instance cas-cost
                         (op-next ns-next) (op-noop ns-noop) (op-result ns-result)
                         (replay-ok ns-replay-ok) (replay-final ns-replay-final)
                         (cas-step ns-cas-step) (cas-run ns-cas-run))))))

; ---- the read-assoc-store it replaced -------------------------------------------
;
; register and gcn_remove read the registry, made the new map and stored
; it; .refer, .unmap, .addAlias and gce_refer_core the same on a
; namespace's slot. A thread: :read (snapshot), then :write (store the
; new map whatever is there).
(defun rmw-step (i st ops)
  (let ((cell (car st)) (ths (cdr st)))
    (if (not (and (natp i) (< i (len ths)))) st
      (let ((x (nth i ths)))
        (case (car x)
          (:read (cons cell (update-nth i (list :write cell) ths)))
          (:write (cons (ns-next (nth i ops) (cadr x)) (update-nth i (list :done) ths)))
          (otherwise st))))))

(defun rmw-run (sched st ops) (if (atom sched) st (rmw-run (cdr sched) (rmw-step (car sched) st ops) ops)))

; two .refer of different names into an empty namespace, both reading
; before either writes: the first's mapping is gone
(defthm rmw-loses-an-update
  (let ((st (rmw-run '(0 1 0 1) (cons nil '((:read) (:read))) '((:assoc a 1) (:assoc b 2)))))
    (and (equal (cdr st) '((:done) (:done)))
         (not (assoc-equal 'a (car st)))))
  :rule-classes nil)

; the same two threads and the same interleaving through the CAS: the
; second's CAS fails, it reads again, and both mappings are there
(defthm cas-keeps-both
  (let ((st (ns-cas-run '((0 . nil) (1 . nil) (0 . nil) (1 . nil) (1 . nil) (1 . nil))
                        (cas-start 2 nil) '((:assoc a 1) (:assoc b 2)))))
    (and (equal (th-pc (nth 0 (nth 3 st))) :done) (equal (th-pc (nth 1 (nth 3 st))) :done)
         (equal (cdr (assoc-equal 'a (nth 0 st))) 1) (equal (cdr (assoc-equal 'b (nth 0 st))) 2)))
  :rule-classes nil)

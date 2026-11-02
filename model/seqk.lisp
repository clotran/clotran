; SEQ KINDS: what apply's last argument is walked as -- B_APPLY's walk
; (src/f/Eval.f90: the shims ap_kind, ap_first, ap_next, generated
; sk_step deciding), the model's tree (exec.lisp's ex-spread, ex-apwalk)
; and vmx2's :applyv spread (x2-vals) alike. model/exec-PLAN.md's 2c-iv.
;
; A SEQ VALUE, read at its top: nil the empty seq; (:vec . elems) a vector,
; read by index (a seq of it is a view, the vector and an index -- clj's
; APersistentVector.Seq, clotran's OBJ_SEQ); (:lazy . c) a lazy seq, read
; by realising c first; (:cons x . more) a cell whose rest is a seq read
; at its top (clj's Cons, a realised LazySeq -- clotran's LAZY_CONS);
; any other cons a list, its rest a list's tail; anything else no seq.
; :vec, :lazy and :cons tag a value as :clo does, so a list that heads
; with one of them is that kind.
;
; THE REALISATION of a lazy seq's thunk is the runtime's (clotran's
; gce_force, the thunk's own computation -- docs/model-coverage.md's lazy
; seq row): sk-real is constrained by nothing -- as vmx2's prim, the
; theorems hold whatever it returns. What it gives is read at its top,
; but a lazy seq again is none: LazySeq.seq collapses a lazy seq of a
; lazy seq into its realisation, the host's.

(in-package "ACL2")

(encapsulate (((sk-real *) => *))
  (local (defun sk-real (c) c)))

; a cursor (v i top): v read at its top (top t), as a realisation's
; answer (top :r) or as a list's tail (top nil); i a vector's index
(defun sk-kind (v top)
  (declare (xargs :guard t))
  (cond ((null v) 0)
        ((atom v) 4)
        ((not top) 1)
        ((eq (car v) :vec) 2)
        ((eq (car v) :lazy) (if (eq top :r) 4 3))
        ((eq (car v) :cons) (if (consp (cdr v)) 5 4))
        (t 1)))

; THE STEP (generated: sk_step, B_APPLY's walk). kd the cursor's kind, i
; its index, cnt a vector's count. 0: the seq is done; 1: a list's cell,
; its car the element, the walk on to its tail; 2: a vector's element i,
; on to i + 1 (the view past its end is done: ASeq.more's ()); 3: realise,
; then look again at what it gives; 4: no seq (RT.seq's refusal); 5: a
; cell, its head the element, on to its rest.
(defun sk-step (kd i cnt)
  (declare (xargs :guard t))
  (cond ((equal kd 1) 1)
        ((equal kd 2) (if (and (integerp i) (integerp cnt) (<= 0 i) (< i cnt)) 2 0))
        ((equal kd 3) 3)
        ((equal kd 5) 5)
        ((equal kd 0) 0)
        (t 4)))

; whether a step has an element: 1, 2 and 5
(defun sk-more (d) (declare (xargs :guard t)) (or (equal d 1) (equal d 2) (equal d 5)))

(defun sk-cur (v) (list v 0 t))
(defun sk-d (c) (sk-step (sk-kind (car c) (caddr c)) (cadr c) (len (cdr (car c)))))
(defun sk-first (c)
  (let ((v (car c)))
    (case (sk-d c) (1 (car v)) (2 (nth (nfix (cadr c)) (cdr v))) (5 (cadr v)) (otherwise nil))))
(defun sk-next (c)
  (let ((v (car c)))
    (case (sk-d c)
      (1 (list (cdr v) 0 nil))
      (2 (list v (1+ (nfix (cadr c))) t))
      (3 (list (sk-real (cdr v)) 0 :r))
      (5 (list (cddr v) 0 t))
      (otherwise c))))

(defthm sk-real-not-again (implies (equal (sk-d c) 3) (not (equal (sk-d (sk-next c)) 3))))
(defun sk-rank (c) (if (equal (sk-d c) 3) 1 0))

; THE ELEMENTS, at most l of them (B_APPLY's spread: coll_to_vector's
; limit, more is an error, not a hang): (status . elements), status :ok,
; :none (what is no seq met) or :long (more than l).
(defun sk-els (c l)
  (declare (xargs :measure (+ (* 2 (nfix l)) (sk-rank c))))
  (let ((d (sk-d c)))
    (cond ((equal d 0) (cons :ok nil))
          ((equal d 3) (sk-els (sk-next c) l))
          ((sk-more d) (if (zp l)
                           (cons :long nil)
                         (let ((r (sk-els (sk-next c) (1- l)))) (cons (car r) (cons (sk-first c) (cdr r))))))
          (t (cons :none nil)))))
(defconst *sk-lim* 1000000)

(defthm sk-els-true-listp (true-listp (cdr (sk-els c l))) :rule-classes (:rewrite :type-prescription))
(defun sk-ind2 (c l l2)
  (declare (xargs :measure (+ (* 2 (nfix l)) (sk-rank c))))
  (let ((d (sk-d c)))
    (cond ((equal d 3) (sk-ind2 (sk-next c) l l2))
          ((and (sk-more d) (not (zp l))) (sk-ind2 (sk-next c) (1- l) (1- l2)))
          (t (list c l l2)))))
(defthm sk-els-mono
  (implies (and (equal (car (sk-els c l)) :ok) (<= (nfix l) (nfix l2)))
           (equal (sk-els c l2) (sk-els c l)))
  :rule-classes nil
  :hints (("Goal" :induct (sk-ind2 c l l2) :expand ((sk-els c l) (sk-els c l2)))))

; a list is its own elements
(defun sk-plain (l) (if (atom l) (null l) (and (not (member (car l) '(:vec :lazy :cons))) (true-listp l))))
(defthm sk-els-list
  (implies (and (true-listp v) (<= (len v) (nfix l)))
           (equal (sk-els (list v 0 nil) l) (cons :ok v)))
  :hints (("Goal" :induct (nthcdr l v) :expand ((:free (l) (sk-els (list v 0 nil) l))))))
(defthm sk-els-top-list
  (implies (and (sk-plain v) (<= (len v) (nfix l)))
           (equal (sk-els (sk-cur v) l) (cons :ok v)))
  :hints (("Goal" :expand ((sk-els (list v 0 t) l))
                  :use ((:instance sk-els-list (v (cdr v)) (l (1- l)))))))
(in-theory (disable sk-d sk-first sk-next sk-cur))

; A VALUE'S ELEMENTS, as apply spreads them (the tree's ex-spread, vmx2's
; x2-vals): read from its top, at most *sk-lim*
(defun sk-elems (v) (sk-els (sk-cur v) *sk-lim*))
(defthm sk-elems-true-listp (true-listp (cdr (sk-elems v))) :rule-classes (:rewrite :type-prescription))
(defthm sk-elems-plain
  (implies (and (sk-plain v) (<= (len v) *sk-lim*)) (equal (sk-elems v) (cons :ok v))))
(in-theory (disable sk-elems))

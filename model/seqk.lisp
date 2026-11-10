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

; a cursor's parts, read safely: the definitions below read them as car,
; cadr and caddr do (their :logic), and run on anything (their :exec), so
; a step can be evaluated on whatever a value is -- a top-level
; evaluation of a non-list is no guard violation
(defun sk-safe-car (x) (declare (xargs :guard t)) (mbe :logic (car x) :exec (if (consp x) (car x) nil)))
(defun sk-safe-cdr (x) (declare (xargs :guard t)) (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))
(defun sk-safe-nth (n l)
  (declare (xargs :guard (natp n)))
  (cond ((atom l) nil) ((zp n) (car l)) (t (sk-safe-nth (1- n) (cdr l)))))
(defun sk-safe-len (l) (declare (xargs :guard t)) (if (atom l) 0 (+ 1 (sk-safe-len (cdr l)))))
(in-theory (disable sk-safe-car sk-safe-cdr sk-safe-nth sk-safe-len))
(defthm sk-safe-is
  (and (equal (sk-safe-car x) (car x)) (equal (sk-safe-cdr x) (cdr x)))
  :hints (("Goal" :in-theory (enable sk-safe-car sk-safe-cdr))))
(defthm sk-safe-nth-is (equal (sk-safe-nth n l) (nth n l)) :hints (("Goal" :in-theory (enable sk-safe-nth))))
(defthm sk-safe-len-is (equal (sk-safe-len l) (len l)) :hints (("Goal" :in-theory (enable sk-safe-len))))

(defun sk-cur (v) (declare (xargs :guard t)) (list v 0 t))
(defun sk-d (c)
  (declare (xargs :guard t))
  (mbe :logic (sk-step (sk-kind (car c) (caddr c)) (cadr c) (len (cdr (car c))))
       :exec (let ((v (sk-safe-car c)))
               (sk-step (sk-kind v (sk-safe-car (sk-safe-cdr (sk-safe-cdr c)))) (sk-safe-car (sk-safe-cdr c))
                        (sk-safe-len (sk-safe-cdr v))))))
(defun sk-first (c)
  (declare (xargs :guard t))
  (mbe :logic (let ((v (car c)))
                (case (sk-d c) (1 (car v)) (2 (nth (nfix (cadr c)) (cdr v))) (5 (cadr v)) (otherwise nil)))
       :exec (let ((v (sk-safe-car c)))
               (case (sk-d c)
                 (1 (sk-safe-car v)) (2 (sk-safe-nth (nfix (sk-safe-car (sk-safe-cdr c))) (sk-safe-cdr v)))
                 (5 (sk-safe-car (sk-safe-cdr v))) (otherwise nil)))))
(defun sk-next (c)
  (declare (xargs :guard t))
  (mbe :logic (let ((v (car c)))
                (case (sk-d c)
                  (1 (list (cdr v) 0 nil))
                  (2 (list v (1+ (nfix (cadr c))) t))
                  (3 (list (sk-real (cdr v)) 0 :r))
                  (5 (list (cddr v) 0 t))
                  (otherwise c)))
       :exec (let ((v (sk-safe-car c)))
               (case (sk-d c)
                 (1 (list (sk-safe-cdr v) 0 nil))
                 (2 (list v (1+ (nfix (sk-safe-car (sk-safe-cdr c)))) t))
                 (3 (list (sk-real (sk-safe-cdr v)) 0 :r))
                 (5 (list (sk-safe-cdr (sk-safe-cdr v)) 0 t))
                 (otherwise c)))))

(defthm sk-real-not-again (implies (equal (sk-d c) 3) (not (equal (sk-d (sk-next c)) 3))))
(defun sk-rank (c) (declare (xargs :guard t)) (if (equal (sk-d c) 3) 1 0))

; THE ELEMENTS, at most l of them (B_APPLY's spread: coll_to_vector's
; limit, more is an error, not a hang): (status . elements), status :ok,
; :none (what is no seq met) or :long (more than l).
(defun sk-els (c l)
  (declare (xargs :measure (+ (* 2 (nfix l)) (sk-rank c)) :guard (natp l)))
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
(defun sk-elems (v) (declare (xargs :guard t)) (sk-els (sk-cur v) *sk-lim*))
(defthm sk-elems-true-listp (true-listp (cdr (sk-elems v))) :rule-classes (:rewrite :type-prescription))
(defthm sk-elems-plain
  (implies (and (sk-plain v) (<= (len v) *sk-lim*)) (equal (sk-elems v) (cons :ok v))))
(in-theory (disable sk-elems))

; ---- APPLY'S WALK (moved from exec.lisp: one definition, the tree's, B_APPLY's and vmx2's) ----

; APPLY'S WALK (B_APPLY; clj's RestFn.applyTo): a closure with a variadic
; arity of req fixed parameters (req -1: none) takes elements off the
; seq's front only while it has fewer than req -- k taken so far, more 1
; while the seq has another -- so a lazy seq is realised no further. 1:
; take one more; 2: the variadic arity, its rest the seq as it is (the
; arguments past req consed back onto it); 3: spread what there is, the
; count's dispatch (no variadic arity, or req or fewer and none left).
(defun ex-apstep (req k more)
  (declare (xargs :guard t))
  (cond ((not (and (integerp req) (<= 0 req) (integerp k))) 3)
        ((and (< k req) (equal more 1)) 1)
        ((or (< req k) (equal more 1)) 2)
        (t 3)))

; HOW FAR THE WALK READS (generated): the position k -- the arguments taken
; so far -- while k <= req + 1. RestFn.applyTo's RT.boundedLength reads
; req + 1 positions and its last next() realises the one after, so clj
; realises apply's seq through position req + 1 and no further. 1: read
; it, 0: not (past it, or no variadic arity). k <= req + 1 is tested as k <=
; req, else k - 1 = req: the generated Fortran evaluates k - 1 only when k >
; req >= 0, so no intermediate leaves 64 bits for 64-bit inputs (req + 1
; overflowed at req = 2^63 - 1). ex-aplook-is gives the old form.
(defun ex-aplook (req k)
  (declare (xargs :guard t))
  (if (and (integerp req) (<= 0 req) (integerp k) (or (<= k req) (equal (- k 1) req))) 1 0))
(defthm ex-aplook-is
  (equal (ex-aplook req k) (if (and (integerp req) (<= 0 req) (integerp k) (<= k (+ req 1))) 1 0))
  :rule-classes nil)

; APPLY'S WALK, as B_APPLY takes it, over the seq's cursor c (seqk): (way
; fixed extras c nr). way ex-apstep's 2 or 3: 2 the variadic arity's fixed
; arguments, the arguments past them (consed back onto the rest) and the
; rest's cursor as it is; 3 every argument taken and the cursor where the
; walk stopped (the seq's end, for a variadic arity), then nil. nr the realisations
; it makes: one each time a position it reads is a lazy seq, and when it
; hands over at position req, the one past it (boundedLength's last
; next(), the peek).
(local (defthm ex-len-append-w (equal (len (append a b)) (+ (len a) (len b)))))
(defun ex-apwalk (req fx c)
  (declare (xargs :measure (+ (* 2 (nfix (- (ifix req) (len fx)))) (sk-rank c))))
  (let* ((k (len fx)) (d (if (equal (ex-aplook req k) 1) (sk-d c) 1)))
    (if (equal d 3)
        (let ((r (ex-apwalk req fx (sk-next c)))) (update-nth 4 (1+ (nfix (nth 4 r))) r))
      (let ((w (ex-apstep req k (if (sk-more d) 1 0))))
        (cond ((and (equal w 1) (sk-more d) (< k (ifix req))) (ex-apwalk req (append fx (list (sk-first c))) (sk-next c)))
              ((equal w 2) (list 2 (take (nfix req) fx) (nthcdr (nfix req) fx) c
                                 (if (and (equal (ex-aplook req (1+ k)) 1) (equal (sk-d (sk-next c)) 3)) 1 0)))
              (t (list 3 fx c nil 0)))))))

; ---- APPLY'S SPREAD: the walk's answer as a call's arguments (model/exec-PLAN.md's 2c-vi) ----
;
; WHAT THE WALK HANDS OVER, as a value: the seq at the cursor where it
; stopped (at a step 1, 2 or 5), read at its top. A list's tail is itself,
; but a tail that heads with a tag (:vec, :lazy, :cons) would read at its
; top as that kind, so those heads go into cells; a vector's view at i is
; the vector of its elements from i (APersistentVector.Seq's elements); a
; cell or a list read at its top, or a realisation's answer (no lazy seq
; at a step that has an element), is itself. Nothing here is realised.
(defun sk-topv (v)
  (if (and (consp v) (member-eq (car v) '(:vec :lazy :cons))) (list* :cons (car v) (sk-topv (cdr v))) v))
(defun sk-cval (c)
  (cond ((not (caddr c)) (sk-topv (car c)))
        ((equal (sk-d c) 2) (cons :vec (nthcdr (nfix (cadr c)) (cdr (car c)))))
        (t (car c))))
; the arguments past req consed back onto it (RestFn.applyTo's ArraySeq
; of them before the seq: cells)
(defun sk-consv (xs s) (if (atom xs) s (list* :cons (car xs) (sk-consv (cdr xs) s))))

; APPLY'S SPREAD of fx (the arguments between apply's fn and its last) and
; v (its last) for a fn whose variadic arity has req fixed parameters (-1:
; none): (status args). :hand -- the walk handed over (way 2): args the
; req fixed ones and then the rest as ONE seq value, read no further than
; the walk read it (the variadic arity's call, its rest bound to that
; value); :ok -- every argument, the seq read to its end (way 3, the
; count's dispatch); :none -- no seq (v none at its top -- core.clj's
; apply seqs its last argument first -- or met on the way); :long -- more
; than *sk-lim* elements left to read (B_APPLY's bound, the host's call).
(defun sk-spread (req fx v)
  (if (equal (sk-d (sk-cur v)) 4)
      (list :none nil)
    (let ((w (ex-apwalk req fx (sk-cur v))))
      (if (equal (car w) 2)
          (list :hand (append (nth 1 w) (list (sk-consv (nth 2 w) (sk-cval (nth 3 w))))))
        (let ((r (sk-els (nth 2 w) *sk-lim*)))
          (list (car r) (append (nth 1 w) (cdr r))))))))
(defthm sk-spread-true-listp (true-listp (cadr (sk-spread req fx v))))

; HOW FAR THE SPREAD REALISES: a variadic fn handed the seq, positions k ..
; req + 1 at most -- clj's boundedLength -- one realisation each (k the
; arguments before the seq), and that the walk's whole count
(defthm ex-apwalk-realises
  (implies (natp req)
           (<= (nfix (nth 4 (ex-apwalk req fx c))) (+ (nfix (- (+ req 1) (len fx))) (if (equal (sk-d c) 3) 1 0))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-apwalk req fx c) :in-theory (enable ex-apstep ex-aplook)
                  :expand ((ex-apwalk req fx c)))))
(defthm ex-apwalk-realise-bound
  (implies (natp req) (<= (nfix (nth 4 (ex-apwalk req fx c))) (+ 1 (nfix (- (+ req 1) (len fx))))))
  :hints (("Goal" :use ex-apwalk-realises)))

; AN INFINITE SEQ (more than *sk-lim* elements: sk-elems's :long, which no
; spread of all of it takes) handed to a variadic fn of finitely many
; fixed parameters is spread: the walk hands it over (:hand), reading
; req + 1 positions of it -- clj's (apply (fn [& xs] (first xs)) (range))
(defun sk-long-ind (req fx c l)
  (declare (xargs :measure (+ (* 2 (nfix (- (ifix req) (len fx)))) (sk-rank c))))
  (let* ((k (len fx)) (d (if (equal (ex-aplook req k) 1) (sk-d c) 1)))
    (cond ((equal d 3) (sk-long-ind req fx (sk-next c) l))
          ((and (equal (ex-apstep req k (if (sk-more d) 1 0)) 1) (sk-more d) (< k (ifix req)))
           (sk-long-ind req (append fx (list (sk-first c))) (sk-next c) (1- l)))
          (t (list req fx c l)))))
(defthm ex-apwalk-long
  (implies (and (natp req) (equal (car (sk-els c l)) :long) (<= req (+ (len fx) (nfix l))))
           (equal (car (ex-apwalk req fx c)) 2))
  :hints (("Goal" :induct (sk-long-ind req fx c l) :in-theory (enable ex-apstep ex-aplook)
                  :expand ((ex-apwalk req fx c) (sk-els c l)))))
(defthm sk-els-none (implies (equal (sk-d c) 4) (equal (car (sk-els c l)) :none)) :hints (("Goal" :expand ((sk-els c l)))))
(defthm sk-spread-long
  (implies (and (natp req) (<= req *sk-lim*) (equal (car (sk-elems v)) :long))
           (equal (car (sk-spread req fx v)) :hand))
  :hints (("Goal" :in-theory (e/d (sk-elems) (ex-apwalk))
                  :use ((:instance ex-apwalk-long (c (sk-cur v)) (l *sk-lim*)) (:instance sk-els-none (c (sk-cur v)) (l *sk-lim*))))))
; and what the spread realises is the walk's, so within that bound
(defthm sk-spread-hand-realises
  (implies (and (natp req) (equal (car (sk-spread req fx v)) :hand))
           (<= (nfix (nth 4 (ex-apwalk req fx (sk-cur v)))) (+ 1 (nfix (- (+ req 1) (len fx))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable sk-spread ex-apwalk) :use ((:instance ex-apwalk-realise-bound (c (sk-cur v)))))))

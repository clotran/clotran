; THE TREE EVALUATOR'S CORE, COUNTED (model/exec.lisp). A turn of
; run_loop is one ex-step: the generated decisions are a fixed number of
; comparisons (ex-own, at most 16 on any path), and its action a push, a
; tail, a finish or a slot written, each a constant number of steps but a
; recur's last, which writes its k slots, a closure's making, which copies
; its c captures, and a call's entry, which makes a frame of its callee's
; s slots and writes its arguments and captures into it (s + c steps).
; ex-ev counts the turns (exec-proof proves the machine takes exactly
; them); here they are bounded: a loop-free, call-free core tree of n
; nodes takes at most 3n - 2 turns -- a constant, a Var or a fn 1, an if
; 2, a do one a child, a let two a binding and one for its body, each
; node's children their own. A loop's turns are its inits', then each
; iteration's -- its body's and a recur's 2k + 2; a call's of k arguments
; its head's (none, and one turn fewer, when direct-linked), its
; arguments' and 2k + 4, and its callee's body's (ex-call-turns). The
; arity a call picks is at most two walks of its callee's a arities, one
; ex-arfit (10 comparisons) each: at most 2a (ex-arity-steps-bound).

(in-package "ACL2")

(include-book "exec-vm")

; the comparisons on each decision's longest path
(defun ex-own (f) (case f (ex-act 16) (ex-kid 6) (ex-pc 11) (ex-i 9) (ex-fin 2) (ex-arfit 10) (ex-entry 2) (ex-apentry 5) (ex-apstep 7) (ex-aplook 4) (sk-step 7) (otherwise 0)))
(defthm ex-own-bound (<= (ex-own f) 16) :rule-classes :linear)

; the arity's walk: the arities ex-arfit is asked of, the fixed pass and,
; when it found none, the variadic one (exec.inc pick_arity)
(defun ex-arity-pass-steps (ars n pass)
  (cond ((atom ars) 0)
        ((equal (ex-arfit pass (nth 0 (car ars)) (if (truthy (nth 1 (car ars))) 1 0) n) 1) 1)
        (t (1+ (ex-arity-pass-steps (cdr ars) n pass)))))
(defun ex-arity-steps (ars n)
  (+ (ex-arity-pass-steps ars n 0) (if (ex-arity-pass ars n 0) 0 (ex-arity-pass-steps ars n 1))))
(defthm ex-arity-pass-steps-bound (<= (ex-arity-pass-steps ars n pass) (len ars)) :rule-classes :linear)
(defthm ex-arity-steps-bound (<= (ex-arity-steps ars n) (* 2 (len ars))) :rule-classes :linear)

; the nodes: flg :kids the children from i on, else the node and its children
(defun ex-sz (flg e i)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (if (eq flg :kids) 1 2) (if (eq flg :kids) (nfix (- (ex-nk e) (nfix i))) 0)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (cond ((not (consp e)) 0)
        ((not (eq flg :kids)) (+ 1 (ex-sz :kids e 0)))
        ((< (nfix i) (ex-nk e)) (+ (ex-sz :m (ex-kid-of e (nfix i)) 0) (ex-sz :kids e (1+ (nfix i)))))
        (t 0)))

(defthm ex-sz-natp (natp (ex-sz flg e i)) :rule-classes :type-prescription)

(defthm ex-sz-node-pos (implies (and (consp e) (not (eq flg :kids))) (<= 1 (ex-sz flg e i))) :rule-classes :linear)

(defthm ex-sz-kids-step
  (implies (and (consp e) (natp i) (< i (ex-nk e)))
           (equal (ex-sz :kids e i) (+ (ex-sz :m (ex-kid-of e i) 0) (ex-sz :kids e (+ 1 i))))))

(defthm ex-sz-kids-end (implies (and (natp i) (<= (ex-nk e) i)) (equal (ex-sz :kids e i) 0)))

(defthm ex-sz-node (implies (and (consp e) (not (eq flg :kids))) (equal (ex-sz flg e i) (+ 1 (ex-sz :kids e 0)))))

(in-theory (disable ex-sz))


(defthm ex-lfwf-consp (implies (ex-lfwf flg e i cm) (consp e)) :rule-classes :forward-chaining
  :hints (("Goal" :expand ((ex-lfwf flg e i cm)))))

(defthm ex-ev-turns-natp (natp (caddr (ex-ev flg e i tmp fr fuel))) :rule-classes :type-prescription
  :hints (("Goal" :induct (ex-ev flg e i tmp fr fuel) :in-theory (e/d (c+) (ex-kid-of)))))

(defthm ex-nth-consp-len (implies (consp (nth j l)) (< (nfix j) (len l))) :rule-classes nil)
(defthm ex-kid-in-range (implies (and (natp j) (consp (ex-kid-of e j))) (< j (ex-nk e))) :rule-classes :linear
  :hints (("Goal" :in-theory (enable ex-nk ex-kids) :use ((:instance ex-nth-consp-len (l (ex-kids e)))))))

(defun ex-cgood (flg e i tmp fr fuel cm)
  (implies (and (ex-lfwf flg e i cm) (member-equal flg '(:m :do :let)) (natp i)
                (implies (eq flg :let) (<= i (ex-i2 e))) (implies (eq flg :do) (or (zp (ex-nk e)) (< i (ex-nk e)))))
           (<= (caddr (ex-ev flg e i tmp fr fuel))
               (if (eq flg :m) (- (* 3 (ex-sz :m e 0)) 2) (+ 1 (* 3 (ex-sz :kids e i)))))))

(defthm ex-turns-bound-flag
  (ex-cgood flg e i tmp fr fuel cm)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vind flg e i tmp cm env fr fuel caps defs nil)
                  :in-theory (e/d (c+) (ex-kid-of))
                  :expand ((:free (flg cm) (ex-lfwf flg e i cm))
                           (:free (flg fr tmp) (ex-ev flg e i tmp fr fuel))))))

; A LOOP-FREE CORE TREE OF n NODES TAKES AT MOST 3n - 2 TURNS
(defthm ex-turns-bound
  (implies (ex-lfwf :m e 0 cm)
           (<= (caddr (ex-ev :m e 0 nil fr fuel)) (- (* 3 (ex-sz :m e 0)) 2)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance ex-turns-bound-flag (flg :m) (i 0) (tmp nil))))))

; A CALL'S TURNS: from its i-th argument, 2 for each argument left and 3
; for the entry, the body's answer and the finish, beyond what its
; arguments and its callee's body take (ex-call-parts)
(defun ex-call-parts (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (< (nfix i) (ex-nk e))
      (let ((r (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (+ (caddr r) (ex-call-parts e (1+ (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel)))
    (caddr (ex-ev :iter (ex-fbody (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) 0 nil (ex-bind (car (ex-callee tmp)) (cdr (ex-callee tmp))) (1- fuel)))))

(defthm ex-call-turns
  (implies (and (consp e) (valp (car (ex-ev :call e i tmp fr fuel))))
           (equal (caddr (ex-ev :call e i tmp fr fuel))
                  (+ (* 2 (nfix (- (ex-nk e) (nfix i)))) 3 (ex-call-parts e i tmp fr fuel))))
  :hints (("Goal" :induct (ex-call-parts e i tmp fr fuel)
                  :in-theory (e/d (c+) (ex-kid-of ex-bind ex-fbody ex-enters))
                  :expand ((ex-ev :call e i tmp fr fuel)))))


; APPLY, COUNTED. B_APPLY's walk (ex-apwalk, over a seq of any kind) is a
; turn of its loop a step: a realisation or an element taken, one ex-aplook
; (4 comparisons), one sk-step (7) and one ex-apstep (7) each, and one more
; for the decision that ends it, with the peek. A realisation's answer is
; never a lazy seq to realise again (seqk), so each element costs at most
; two turns: at most 2t + 3 for t taken (ex-apwalk-turns-taken), and the
; walk takes no more than req - k (ex-apwalk-taken-req) -- (apply f 1
; (range)) in a constant number of turns, whatever the seq's kind.
(defun ex-apwalk-turns (req fx c)
  (declare (xargs :measure (+ (* 2 (nfix (- (ifix req) (len fx)))) (sk-rank c))))
  (let* ((k (len fx)) (d (if (equal (ex-aplook req k) 1) (sk-d c) 1)))
    (if (equal d 3)
        (1+ (ex-apwalk-turns req fx (sk-next c)))
      (let ((w (ex-apstep req k (if (sk-more d) 1 0))))
        (cond ((and (equal w 1) (sk-more d) (< k (ifix req))) (1+ (ex-apwalk-turns req (append fx (list (sk-first c))) (sk-next c))))
              ((equal w 2) (if (and (equal (ex-aplook req (1+ k)) 1) (equal (sk-d (sk-next c)) 3)) 2 1))
              (t 1))))))
(defun ex-apwalk-taken (req fx c)
  (declare (xargs :measure (+ (* 2 (nfix (- (ifix req) (len fx)))) (sk-rank c))))
  (let* ((k (len fx)) (d (if (equal (ex-aplook req k) 1) (sk-d c) 1)))
    (if (equal d 3)
        (ex-apwalk-taken req fx (sk-next c))
      (if (and (equal (ex-apstep req k (if (sk-more d) 1 0)) 1) (sk-more d) (< k (ifix req)))
          (1+ (ex-apwalk-taken req (append fx (list (sk-first c))) (sk-next c)))
        0))))
(defthm ex-apwalk-turns-taken0
  (<= (ex-apwalk-turns req fx c) (+ 2 (* 2 (ex-apwalk-taken req fx c)) (if (equal (sk-d c) 3) 1 0)))
  :rule-classes nil
  :hints (("Goal" :induct (ex-apwalk-turns req fx c))))
(defthm ex-apwalk-turns-taken
  (<= (ex-apwalk-turns req fx c) (+ 3 (* 2 (ex-apwalk-taken req fx c))))
  :rule-classes :linear
  :hints (("Goal" :use ex-apwalk-turns-taken0)))
(defthm ex-apwalk-taken-req
  (<= (ex-apwalk-taken req fx c) (nfix (- (ifix req) (len fx))))
  :rule-classes :linear
  :hints (("Goal" :induct (ex-apwalk-taken req fx c) :in-theory (enable ex-apstep))))

; THE SPREAD reads the last argument's elements (sk-els): a turn a step, a
; realisation or an element, and one for its end -- at most 2n + 2 for n
; elements (2n + 3 from a lazy seq not yet realised) -- then copies each
; argument but the last and those elements, once: a step an element and
; one to end each copy, n + 2 for n spread.
(defun sk-els-turns (c l)
  (declare (xargs :measure (+ (* 2 (nfix l)) (sk-rank c))))
  (let ((d (sk-d c)))
    (cond ((equal d 3) (1+ (sk-els-turns (sk-next c) l)))
          ((and (sk-more d) (not (zp l))) (1+ (sk-els-turns (sk-next c) (1- l))))
          (t 1))))
(defthm sk-els-turns-bound
  (<= (sk-els-turns c l) (+ 2 (* 2 (len (cdr (sk-els c l)))) (if (equal (sk-d c) 3) 1 0)))
  :rule-classes nil
  :hints (("Goal" :induct (sk-els-turns c l) :expand ((sk-els c l)))))
(defthm sk-elems-turns
  (<= (sk-els-turns (sk-cur v) *sk-lim*) (+ 3 (* 2 (len (cdr (sk-elems v))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sk-elems) :use ((:instance sk-els-turns-bound (c (sk-cur v)) (l *sk-lim*))))))
(defun ex-copy-steps (l) (if (atom l) 1 (1+ (ex-copy-steps (cdr l)))))
(defthm ex-copy-steps-len (equal (ex-copy-steps l) (1+ (len l))))
(defthm ex-len-append-c (equal (len (append a b)) (+ (len a) (len b))))
(defthm ex-spread-steps
  (equal (+ (ex-copy-steps (butlast args 1)) (ex-copy-steps (cdr (sk-elems (car (last args))))))
         (+ 2 (len (ex-spread args)))))

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
; arguments' and 2k + 4, and its callee's body's (ex-call-turns).

(in-package "ACL2")

(include-book "exec-vm")

; the comparisons on each decision's longest path
(defun ex-own (f) (case f (ex-act 16) (ex-kid 6) (ex-pc 11) (ex-i 9) (ex-fin 2) (otherwise 0)))
(defthm ex-own-bound (<= (ex-own f) 16) :rule-classes :linear)

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
    (caddr (ex-ev :iter (ex-fbody (car tmp) (len (cdr tmp))) 0 nil (ex-bind (car tmp) (cdr tmp)) (1- fuel)))))

(defthm ex-call-turns
  (implies (and (consp e) (valp (car (ex-ev :call e i tmp fr fuel))))
           (equal (caddr (ex-ev :call e i tmp fr fuel))
                  (+ (* 2 (nfix (- (ex-nk e) (nfix i)))) 3 (ex-call-parts e i tmp fr fuel))))
  :hints (("Goal" :induct (ex-call-parts e i tmp fr fuel)
                  :in-theory (e/d (c+) (ex-kid-of ex-bind ex-fbody ex-enters))
                  :expand ((ex-ev :call e i tmp fr fuel)))))

; THE TREE EVALUATOR'S CORE, COUNTED (model/exec.lisp). A turn of
; run_loop is one ex-step: the generated decisions are a fixed number of
; comparisons (ex-own, at most 9 on any path), and its action a push, a
; tail, a finish or a slot written, each a constant number of steps but a
; recur's last, which writes its k slots. ex-ev counts the turns
; (exec-proof proves the machine takes exactly them); here they are
; bounded: a loop-free core tree of n nodes takes at most 3n - 2 turns --
; a constant 1, an if 2, a do one a child, a let two a binding and one for
; its body, each node's children their own. A loop's turns are its
; inits', then each iteration's -- its body's and a recur's 2k + 2.

(in-package "ACL2")

(include-book "exec-vm")

; the comparisons on each decision's longest path
(defun ex-own (f) (case f (ex-act 9) (ex-kid 6) (ex-pc 4) (ex-i 5) (ex-fin 2) (otherwise 0)))
(defthm ex-own-bound (<= (ex-own f) 9) :rule-classes :linear)

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

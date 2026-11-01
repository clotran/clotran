; THE TREE EVALUATOR'S CORE, PROVED (model/exec.lisp): run_loop, a turn at
; a time with the generated decisions, does what the meaning says.
;
; THE THEOREM (ex-machine-correct): for a well-formed core node and any
; records below it, running the machine for the meaning's count of turns
; from a record of the node
;   - when the meaning is a value v: pops that record, v in flight, the
;     records below untouched and the frame the meaning's;
;   - when it is a recur (only in a loop body's tail): leaves the loop's
;     record back at its body, restarting, the loop's slots rebound;
; and never makes the recur marker a value or puts it in a slot. So a
; local's read answers the slot its binding wrote (ex-local-reads-binding):
; the meaning's frame is the machine's.

(in-package "ACL2")

(include-book "exec")

; ---- what the theorem assumes -----------------------------------------------------------------
;
; every node a core kind; an if 2 or 3 children; a let or loop its
; bindings' inits and its body; a recur only in a loop body's tail
; position (tl), as anpass's tail check passes it, with as many arguments
; as its loop's slots; no constant the recur marker

(defun ex-wf (flg e i tl)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (and (consp e) (< nk *ex40*) (< n2 *ex40*)
         (case flg
           (:iter (ex-wf :m e 0 t))
           (:do (cond ((not (equal k 5)) nil)
                      ((zp nk) t)
                      ((< i (- nk 1)) (and (ex-wf :m (ex-kid-of e i) 0 nil) (ex-wf :do e (1+ i) tl)))
                      (t (ex-wf :m (ex-kid-of e (- nk 1)) 0 tl))))
           (:let (cond ((not (or (equal k 11) (equal k 12))) nil)
                       ((< i n2) (and (ex-wf :m (ex-kid-of e i) 0 nil) (ex-wf :let e (1+ i) tl)))
                       ((equal k 12) (ex-wf :m (ex-kid-of e n2) 0 t))
                       (t (ex-wf :m (ex-kid-of e n2) 0 tl))))
           (:rec (cond ((not (equal k 16)) nil)
                       ((< i nk) (and (ex-wf :m (ex-kid-of e i) 0 nil) (ex-wf :rec e (1+ i) tl)))
                       (t tl)))
           (otherwise
            (cond ((equal k 1) (not (equal (ex-c e) *ex-mk*)))
                  ((equal k 2) t)
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-wf :m (ex-kid-of e 0) 0 nil) (ex-wf :m (ex-kid-of e 1) 0 tl)
                                    (or (equal nk 2) (ex-wf :m (ex-kid-of e 2) 0 tl))))
                  ((equal k 5) (ex-wf :do e 0 tl))
                  ((or (equal k 11) (equal k 12)) (and (equal nk (1+ n2)) (ex-wf :let e 0 tl)))
                  ((equal k 16) (and tl (equal (ex-rn e) nk) (ex-wf :rec e 0 tl)))
                  (t nil)))))))

(defthm ex-wf-facts (implies (ex-wf flg e i tl) (and (consp e) (< (ex-nk e) *ex40*) (< (ex-i2 e) *ex40*)))
  :rule-classes :forward-chaining :hints (("Goal" :expand ((ex-wf flg e i tl)))))

(defthm ex-wf-iter (equal (ex-wf :iter e i tl) (and (consp e) (< (ex-nk e) *ex40*) (< (ex-i2 e) *ex40*) (ex-wf :m e 0 t)))
  :hints (("Goal" :expand ((ex-wf :iter e i tl)))))

(defun no-mk (l) (not (member-equal *ex-mk* l)))

; the record a flag's meaning starts from
(defun ex-start (flg e i tmp fl rs)
  (case flg
    (:iter (ex-rec e 0 0 t e nil))
    (:rec (ex-rec e 1 i fl rs tmp))
    ((:do :let) (ex-rec e 0 i fl rs tmp))
    (otherwise (ex-rec e 0 0 fl rs nil))))

(defun ex-good (flg e i tmp fr fuel fl rs ks v0 tl)
  (implies (and (ex-wf flg e i tl) (implies tl fl) (no-mk fr) (no-mk tmp) (natp i))
           (let* ((r (ex-ev flg e i tmp fr fuel)) (res (car r)) (fr2 (cadr r))
                  (s2 (ex-run (list (cons (ex-start flg e i tmp fl rs) ks) v0 fr) (caddr r))))
             (and (no-mk fr2)
                  (implies (valp res) (and (not (equal (val res) *ex-mk*)) (equal s2 (list ks (val res) fr2))))
                  (implies (equal (car res) :recur)
                           (and tl (equal s2 (list (cons (ex-rec rs 0 0 fl rs nil) ks) nil fr2))))))))

; ---- the machine, a turn at a time -------------------------------------------------------------

(defthm ex-run-plus (implies (and (natp a) (natp b)) (equal (ex-run s (+ a b)) (ex-run (ex-run s a) b)))
  :hints (("Goal" :in-theory (disable ex-step) :induct (ex-run s a))))
(defthm ex-run-nfix (equal (ex-run s (nfix a)) (ex-run s a)) :hints (("Goal" :in-theory (disable ex-step))))
(defthm ex-run-0 (equal (ex-run s 0) s))
(defthm ex-run-c+ (equal (ex-run s (c+ a b)) (ex-run (ex-run s a) b))
  :hints (("Goal" :in-theory (e/d (c+) (ex-step ex-run ex-run-nfix))
                  :use ((:instance ex-run-plus (a (nfix a)) (b (nfix b))) (:instance ex-run-nfix (s (ex-run s a)) (a b))
                        (:instance ex-run-nfix (a a))))))
(defthm ex-run-1 (equal (ex-run s 1) (ex-step s)) :hints (("Goal" :in-theory (disable ex-step))))
(in-theory (disable c+))
(defthm ex-step-list (implies (consp ks) (equal (ex-step (list ks v fr)) (ex-turn ks v fr))))
(in-theory (disable ex-step))

(defthm no-mk-update (implies (and (no-mk l) (not (equal v *ex-mk*))) (no-mk (update-nth n v l))))
(defthm no-mk-nth (implies (no-mk l) (not (equal (nth n l) *ex-mk*))))
(defthm no-mk-append (implies (and (no-mk a) (not (equal v *ex-mk*))) (no-mk (append a (list v)))))
(defthm no-mk-take (implies (no-mk l) (no-mk (take n l))))
(defthm no-mk-cdr (implies (no-mk l) (no-mk (cdr l))))
(defthm no-mk-car (implies (and (no-mk l) (consp l)) (not (equal (car l) *ex-mk*))))
(defthm no-mk-cons (equal (no-mk (cons a l)) (and (not (equal a *ex-mk*)) (no-mk l))))
(in-theory (disable no-mk))
(defthm no-mk-write (implies (and (no-mk l) (no-mk vs)) (no-mk (ex-write s vs l)))
  :hints (("Goal" :induct (ex-write s vs l))))

; the induction: ex-ev's recursion, each call with the records it runs on
(set-irrelevant-formals-ok t)
(defun ex-ind (flg e i tmp fr fuel fl rs ks v0 tl)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (case flg
      (:iter (if (not (consp e))
                 nil
               (let ((r (ex-ev :m e 0 nil fr fuel)))
                 (if (zp fuel)
                     (ex-ind :m e 0 nil fr fuel t e ks v0 t)
                   (list (ex-ind :m e 0 nil fr fuel t e ks v0 t)
                         (ex-ind :iter e 0 nil (cadr r) (1- fuel) fl rs ks nil tl))))))
      (:do (cond ((not (consp e)) nil)
                 ((zp nk) nil)
                 ((< i (- nk 1))
                  (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (list (ex-ind :m (ex-kid-of e i) 0 nil fr fuel nil nil (cons (ex-rec e 0 (1+ i) fl rs tmp) ks) v0 nil)
                          (ex-ind :do e (1+ i) tmp (cadr r) fuel fl rs ks (val (car r)) tl))))
                 (t (ex-ind :m (ex-kid-of e (- nk 1)) 0 nil fr fuel fl rs ks v0 tl))))
      (:let (cond ((not (consp e)) nil)
                  ((< i n2)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (list (ex-ind :m (ex-kid-of e i) 0 nil fr fuel nil nil (cons (ex-rec e 1 i fl rs tmp) ks) v0 nil)
                           (ex-ind :let e (1+ i) tmp (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel fl rs ks
                                   (val (car r)) tl))))
                  ((equal k 12) (ex-ind :iter (ex-kid-of e n2) 0 nil fr fuel fl rs ks v0 tl))
                  (t (ex-ind :m (ex-kid-of e n2) 0 nil fr fuel fl rs ks v0 tl))))
      (:rec (cond ((not (consp e)) nil)
                  ((< i nk)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (list (ex-ind :m (ex-kid-of e i) 0 nil fr fuel nil nil (cons (ex-rec e 2 i fl rs tmp) ks) v0 nil)
                           (ex-ind :rec e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel fl rs ks (val (car r)) tl))))
                  (t nil)))
      (otherwise
       (cond ((not (consp e)) nil)
             ((equal k 4)
              (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                (list (ex-ind :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil)
                      (ex-ind :m (ex-kid-of e 1) 0 nil (cadr r) fuel fl rs ks (val (car r)) tl)
                      (ex-ind :m (ex-kid-of e 2) 0 nil (cadr r) fuel fl rs ks (val (car r)) tl))))
             ((equal k 5) (ex-ind :do e 0 nil fr fuel fl rs ks v0 tl))
             ((or (equal k 11) (equal k 12)) (ex-ind :let e 0 nil fr fuel fl rs ks v0 tl))
             ((equal k 16) (ex-ind :rec e 0 nil fr fuel fl rs ks v0 tl))
             (t nil))))))

; ---- each construct, given what its parts do ----------------------------------------------------

(defthm ex-i2-natp (natp (ex-i2 e)) :rule-classes :type-prescription)
(defthm ex-s2-natp (natp (ex-s2 e)) :rule-classes :type-prescription)
(defthm ex-nk-natp (natp (ex-nk e)) :rule-classes :type-prescription)
(defthm ex-rstart-natp (natp (ex-rstart e)) :rule-classes :type-prescription)
(defthm ex-rn-natp (natp (ex-rn e)) :rule-classes :type-prescription)
(in-theory (disable ex-kind ex-i2 ex-s2 ex-nk ex-c ex-mark ex-rstart ex-rn ex-kids))

(defmacro ex-other (flg) `(not (member-equal ,flg '(:iter :do :let :rec))))
(defmacro ex-r (kid fr fuel) `(ex-ev :m ,kid 0 nil ,fr ,fuel))

(defmacro ex-case (name hyps &key (flg 'flg))
  `(defthm ,name
     (implies (and ,@hyps) (ex-good ,flg e i tmp fr fuel fl rs ks v0 tl))
     :hints (("Goal" :expand ((:free (fr fuel tmp) (ex-ev ,flg e i tmp fr fuel)) (:free (tl) (ex-wf ,flg e i tl)))
                     :in-theory (disable ex-ev ex-wf c+ ex-run ex-kid-of)))))

(ex-case ex-good-atom ((not (consp e))))

(ex-case ex-good-leaf ((ex-other flg) (not (member-equal (ex-kind e) '(4 5 11 12 16)))))

; an if, a case for each way its test goes
(defmacro ex-if-test () '(ex-good :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil))
(defmacro ex-if-branch (j)
  `(ex-good :m (ex-kid-of e ,j) 0 nil (cadr (ex-r (ex-kid-of e 0) fr fuel)) fuel fl rs ks (val (car (ex-r (ex-kid-of e 0) fr fuel))) tl))
(ex-case ex-good-if-out ((ex-other flg) (consp e) (equal (ex-kind e) 4) (not (valp (car (ex-r (ex-kid-of e 0) fr fuel))))))
(ex-case ex-good-if-then ((ex-other flg) (consp e) (equal (ex-kind e) 4) (valp (car (ex-r (ex-kid-of e 0) fr fuel)))
                          (truthy (val (car (ex-r (ex-kid-of e 0) fr fuel)))) (ex-if-test) (ex-if-branch 1)))
(ex-case ex-good-if-else ((ex-other flg) (consp e) (equal (ex-kind e) 4) (valp (car (ex-r (ex-kid-of e 0) fr fuel)))
                          (not (truthy (val (car (ex-r (ex-kid-of e 0) fr fuel))))) (< 2 (ex-nk e)) (ex-if-test) (ex-if-branch 2)))
(ex-case ex-good-if-nil ((ex-other flg) (consp e) (equal (ex-kind e) 4) (valp (car (ex-r (ex-kid-of e 0) fr fuel)))
                         (not (truthy (val (car (ex-r (ex-kid-of e 0) fr fuel))))) (not (< 2 (ex-nk e))) (ex-if-test)))
(defthm ex-good-if
  (implies (and (ex-other flg) (consp e) (equal (ex-kind e) 4) (ex-if-test) (ex-if-branch 1) (ex-if-branch 2))
           (ex-good flg e i tmp fr fuel fl rs ks v0 tl))
  :hints (("Goal" :in-theory (disable ex-good ex-ev ex-wf ex-kid-of ex-nk truthy valp val ex-rec)
                  :cases ((not (valp (car (ex-r (ex-kid-of e 0) fr fuel))))
                          (and (valp (car (ex-r (ex-kid-of e 0) fr fuel))) (truthy (val (car (ex-r (ex-kid-of e 0) fr fuel)))))
                          (and (valp (car (ex-r (ex-kid-of e 0) fr fuel))) (not (truthy (val (car (ex-r (ex-kid-of e 0) fr fuel))))) (< 2 (ex-nk e)))
                          (and (valp (car (ex-r (ex-kid-of e 0) fr fuel))) (not (truthy (val (car (ex-r (ex-kid-of e 0) fr fuel))))) (not (< 2 (ex-nk e))))))))

(ex-case ex-good-m-do ((ex-other flg) (consp e) (equal (ex-kind e) 5) (ex-good :do e 0 nil fr fuel fl rs ks v0 tl)))
(ex-case ex-good-m-let ((ex-other flg) (consp e) (member-equal (ex-kind e) '(11 12)) (ex-good :let e 0 nil fr fuel fl rs ks v0 tl)))
(ex-case ex-good-m-rec ((ex-other flg) (consp e) (equal (ex-kind e) 16) (ex-good :rec e 0 nil fr fuel fl rs ks v0 tl)))

(ex-case ex-good-do-none ((consp e) (zp (ex-nk e))) :flg :do)
(ex-case ex-good-do-mid
  ((consp e) (not (zp (ex-nk e))) (< (nfix i) (- (ex-nk e) 1))
   (ex-good :m (ex-kid-of e (nfix i)) 0 nil fr fuel nil nil (cons (ex-rec e 0 (+ 1 (nfix i)) fl rs tmp) ks) v0 nil)
   (ex-good :do e (+ 1 (nfix i)) tmp (cadr (ex-r (ex-kid-of e (nfix i)) fr fuel)) fuel fl rs ks
            (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel))) tl))
  :flg :do)
(ex-case ex-good-do-last
  ((consp e) (not (zp (ex-nk e))) (not (< (nfix i) (- (ex-nk e) 1)))
   (ex-good :m (ex-kid-of e (- (ex-nk e) 1)) 0 nil fr fuel fl rs ks v0 tl))
  :flg :do)

(ex-case ex-good-let-mid
  ((consp e) (< (nfix i) (ex-i2 e))
   (ex-good :m (ex-kid-of e (nfix i)) 0 nil fr fuel nil nil (cons (ex-rec e 1 (nfix i) fl rs tmp) ks) v0 nil)
   (ex-good :let e (+ 1 (nfix i)) tmp
            (update-nth (+ (ex-s2 e) (nfix i)) (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel))) (cadr (ex-r (ex-kid-of e (nfix i)) fr fuel)))
            fuel fl rs ks (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel))) tl))
  :flg :let)
(ex-case ex-good-let-loop
  ((consp e) (not (< (nfix i) (ex-i2 e))) (equal (ex-kind e) 12)
   (ex-good :iter (ex-kid-of e (ex-i2 e)) 0 nil fr fuel fl rs ks v0 tl))
  :flg :let)
(ex-case ex-good-let-body
  ((consp e) (not (< (nfix i) (ex-i2 e))) (not (equal (ex-kind e) 12))
   (ex-good :m (ex-kid-of e (ex-i2 e)) 0 nil fr fuel fl rs ks v0 tl))
  :flg :let)

(ex-case ex-good-rec-mid
  ((consp e) (< (nfix i) (ex-nk e))
   (ex-good :m (ex-kid-of e (nfix i)) 0 nil fr fuel nil nil (cons (ex-rec e 2 (nfix i) fl rs tmp) ks) v0 nil)
   (ex-good :rec e (+ 1 (nfix i)) (append tmp (list (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel)))))
            (cadr (ex-r (ex-kid-of e (nfix i)) fr fuel)) fuel fl rs ks (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel))) tl))
  :flg :rec)
(ex-case ex-good-rec-end ((consp e) (not (< (nfix i) (ex-nk e)))) :flg :rec)

(ex-case ex-good-iter-zp
  ((consp e) (zp fuel) (ex-good :m e 0 nil fr fuel t e ks v0 t))
  :flg :iter)
(ex-case ex-good-iter
  ((consp e) (not (zp fuel)) (ex-good :m e 0 nil fr fuel t e ks v0 t)
   (ex-good :iter e 0 nil (cadr (ex-r e fr fuel)) (+ -1 fuel) fl rs ks nil tl))
  :flg :iter)

; ---- THE THEOREM ----------------------------------------------------------------------------------

(defthm ex-machine-correct-flag
  (ex-good flg e i tmp fr fuel fl rs ks v0 tl)
  :rule-classes nil
  :hints (("Goal" :induct (ex-ind flg e i tmp fr fuel fl rs ks v0 tl)
                  :in-theory (disable ex-good ex-ev ex-wf ex-run ex-step c+ ex-kid-of ex-rec ex-kind ex-nk ex-i2 ex-s2))))

; RUNNING THE MACHINE ANSWERS WHAT THE MEANING DOES: a value pops the
; node's record with it, a recur in a loop body's tail restarts the loop's
; record, and the records below are as they were
(defthm ex-machine-correct
  (implies (and (ex-wf :m e 0 tl) (implies tl fl) (no-mk fr))
           (let* ((r (ex-ev :m e 0 nil fr fuel))
                  (s2 (ex-run (list (cons (ex-rec e 0 0 fl rs nil) ks) v0 fr) (caddr r))))
             (and (no-mk (cadr r))
                  (implies (valp (car r)) (equal s2 (list ks (val (car r)) (cadr r))))
                  (implies (equal (car (car r)) :recur)
                           (equal s2 (list (cons (ex-rec rs 0 0 fl rs nil) ks) nil (cadr r)))))))
  :hints (("Goal" :use ((:instance ex-machine-correct-flag (flg :m) (i 0) (tmp nil)))
                  :in-theory (disable ex-ev ex-wf ex-run ex-rec))))

(defthm ex-val-cons (implies (equal (car x) :val) (equal (cons :val (cdr x)) x)))

; THE SLOT A LOCAL READS HOLDS ITS BINDING'S VALUE: (let* [x init] x),
; x in slot s, answers init's value
(defthm ex-local-reads-binding
  (implies (and (natp s) (valp (car (ex-ev :m init 0 nil fr fuel))))
           (equal (car (ex-ev :m (list 11 1 (list init (list 2 s)) nil s) 0 nil fr fuel))
                  (car (ex-ev :m init 0 nil fr fuel))))
  :hints (("Goal" :in-theory (enable ex-kind ex-i2 ex-s2 ex-nk ex-c ex-mark ex-kids)
                  :expand ((:free (flg i tmp fr) (ex-ev flg (list 11 1 (list init (list 2 s)) nil s) i tmp fr fuel))
                           (:free (fr) (ex-ev :m (list 2 s) 0 nil fr fuel))))))

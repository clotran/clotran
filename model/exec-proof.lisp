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
;   - when it is a throw (a call's arity error, or a part's throw): stops
;     with the throw's record on top, over the records below (k_unwind,
;     milestone 3, takes it from there);
; and never makes the recur marker a value or puts it in a slot. So a
; local's read answers the slot its binding wrote (ex-local-reads-binding):
; the meaning's frame is the machine's.

(in-package "ACL2")

(include-book "exec")

; what the theorem assumes is exec.lisp's ex-wf, which a call's meaning
; also asks of the body it enters

(defthm ex-wf-facts (implies (ex-wf flg e i tl) (and (consp e) (< (ex-nk e) *ex40*) (< (ex-i2 e) *ex40*)))
  :rule-classes :forward-chaining :hints (("Goal" :expand ((ex-wf flg e i tl)))))

(defthm ex-wf-iter (equal (ex-wf :iter e i tl) (and (consp e) (< (ex-nk e) *ex40*) (< (ex-i2 e) *ex40*) (ex-wf :m e 0 t)))
  :hints (("Goal" :expand ((ex-wf :iter e i tl)))))


; the record a flag's meaning starts from
(defun ex-start (flg e i tmp fl rs)
  (case flg
    (:iter (ex-rec e 0 0 t e nil))
    (:rec (ex-rec e 1 i fl rs tmp))
    (:call (ex-rec e 2 i fl rs tmp))
    ((:do :let) (ex-rec e 0 i fl rs tmp))
    (otherwise (ex-rec e 0 0 fl rs nil))))

; ks is l or a tail of it
(defun ex-below (ks l) (cond ((equal l ks) t) ((atom l) nil) (t (ex-below ks (cdr l)))))

(defun ex-good (flg e i tmp fr fuel fl rs ks v0 tl)
  (implies (and (not (member-equal flg '(:cs :fin))) (ex-wf flg e i tl) (implies tl fl) (no-mk fr) (no-mk tmp) (true-listp tmp) (natp i))
           (let* ((r (ex-ev flg e i tmp fr fuel)) (res (car r)) (fr2 (cadr r))
                  (s2 (ex-run (list (cons (ex-start flg e i tmp fl rs) ks) v0 fr) (caddr r))))
             (and (no-mk fr2)
                  (implies (valp res) (and (not (equal (val res) *ex-mk*)) (equal s2 (list ks (val res) fr2))))
                  (implies (equal (car res) :recur)
                           (and tl (equal s2 (list (cons (ex-rec rs 0 0 fl rs nil) ks) nil fr2))))
                  (implies (ex-thp res)
                           (and (not (equal (val res) *ex-mk*))
                                (equal s2 (list (cons (ex-throwr (val res)) ks) nil fr2))))))))

(defthm ex-below-cons (ex-below ks (cons x ks)))
(defthm ex-below-weaken (implies (ex-below (cons x ks) l) (ex-below ks l)))

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
(defthm ex-run-2 (equal (ex-run s 2) (ex-step (ex-step s)))
  :hints (("Goal" :in-theory (disable ex-step) :expand ((ex-run s 2) (ex-run (ex-step s) 1)))))
(defthm ex-run-3 (equal (ex-run s 3) (ex-step (ex-step (ex-step s))))
  :hints (("Goal" :in-theory (disable ex-step) :expand ((ex-run s 3)))))
(in-theory (disable c+))
(defthm ex-step-list (implies (consp ks) (equal (ex-step (list ks v fr)) (ex-turn ks v fr))))
; a throw's record: k_unwind takes the record under it
(defthm ex-turn-throwr (equal (ex-turn (cons (ex-throwr v) l) val fr) (ex-unwind (cons (ex-throwr v) l) val fr)))
(defthm ex-throwr-v (equal (cadr (car (ex-throwr v))) v))
(defthm ex-throwr-kind (equal (ex-kind (nth 0 (ex-throwr v))) :thrown))
(in-theory (disable ex-step ex-throwr))

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
; a call's new frame: nils, the arguments, the captures and the closure
(defthm no-mk-make-list-ac (implies (no-mk acc) (no-mk (make-list-ac n nil acc))))
(defthm no-mk-bind-caps (implies (and (no-mk fr) (no-mk caps)) (no-mk (ex-bind-caps capv caps fr)))
  :hints (("Goal" :induct (ex-bind-caps capv caps fr))))
(defthm no-mk-nthcdr (implies (no-mk l) (no-mk (nthcdr n l))) :hints (("Goal" :in-theory (enable no-mk))))
(defthm ex-mk-not-true-list (implies (true-listp x) (not (equal x *ex-mk*))))
(defthm no-mk-bargs (implies (and (no-mk args) (true-listp args)) (no-mk (ex-bargs ar args)))
  :hints (("Goal" :in-theory (enable ex-bargs ex-rest-args))))
(defthm no-mk-bind
  (implies (and (no-mk args) (true-listp args) (no-mk (caddr f)) (equal (car f) :clo)) (no-mk (ex-bind f args)))
  :hints (("Goal" :in-theory (disable ex-bind-caps ex-write ex-arity ex-bargs))))

; apply's spread call: its arguments no marker, a true list, when the record's are
(defthm no-mk-append2 (implies (and (no-mk a) (no-mk b)) (no-mk (append a b))) :hints (("Goal" :in-theory (enable no-mk))))
(defthm no-mk-butlast (implies (no-mk l) (no-mk (butlast l n))))
(defthm ex-last-cdr (implies (consp (cdr l)) (equal (last (cdr l)) (last l))))
(defthm ex-callee-no-mk
  (implies (and (no-mk tmp) (true-listp tmp)) (and (no-mk (cdr (ex-callee tmp))) (true-listp (cdr (ex-callee tmp)))))
  :hints (("Goal" :in-theory (e/d (ex-callee ex-apway ex-apentry ex-seqp) (sk-spread)))))
(defthm ex-apway-not-apply (implies (not (equal (car tmp) :apply)) (equal (ex-apway tmp) 0))
  :hints (("Goal" :in-theory (enable ex-apway ex-apentry))))
(defthm ex-apway-callee-clo
  (implies (equal (ex-apway tmp) 1)
           (and (consp (car (ex-callee tmp))) (equal (car (car (ex-callee tmp))) :clo)
                (consp (cdr (car (ex-callee tmp)))) (consp (cddr (car (ex-callee tmp))))))
  :hints (("Goal" :in-theory (enable ex-apway ex-callee ex-apentry ex-clo-shape))))
(defthm ex-apway-callee
  (implies (equal (ex-apway tmp) 1) (equal (ex-apway (ex-callee tmp)) 0))
  :hints (("Goal" :in-theory (enable ex-apway ex-callee ex-apentry ex-clo-shape))))
(defthm ex-callee-callee
  (implies (equal (ex-apway tmp) 1) (equal (ex-callee (ex-callee tmp)) (ex-callee tmp)))
  :hints (("Goal" :use ex-apway-callee :in-theory (e/d (ex-callee) (ex-apway-callee)))))
(defthm ex-callee-id (implies (not (equal (ex-apway tmp) 1)) (equal (ex-callee tmp) tmp))
  :hints (("Goal" :in-theory (enable ex-callee))))

(in-theory (disable ex-callee ex-apway))

; the induction: ex-ev's recursion, each call with the records it runs on
(set-irrelevant-formals-ok t)
(defun ex-ind (flg e i tmp fr fuel fl rs ks v0 tl)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of ex-callee ex-apway ex-enters ex-arerr ex-catchw ex-fbody ex-bind ex-mkclo
                                                 ex-linked ex-write truthy valp val ex-thp take update-nth ex-ev)))))
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
      ((:cs :fin) nil)
      (:call (cond ((not (consp e)) nil)
                   ((< i nk)
                    (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (list (ex-ind :m (ex-kid-of e i) 0 nil fr fuel nil nil (cons (ex-rec e 3 i fl rs tmp) ks) v0 nil)
                            (ex-ind :call e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel fl rs ks (val (car r)) tl))))
                   ((zp fuel) nil)
                   (t (let ((bd (ex-fbody (car (ex-callee tmp)) (len (cdr (ex-callee tmp))))))
                        (ex-ind :iter bd 0 nil (ex-bind (car (ex-callee tmp)) (cdr (ex-callee tmp))) (1- fuel) t bd
                                (cons (ex-rec e 5 i fl rs fr) ks) v0 nil)))))
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
             ((equal k 17) (ex-ind :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil))
             ((equal k 18)
              (let* ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)) (x (val (car r))) (w (ex-catchw (ex-c e) x 0))
                     (fh (update-nth (ex-cslot e (cdr w)) x (cadr r)))
                     (rh (ex-ev :m (ex-cbody e (cdr w)) 0 nil fh fuel)) (f (ex-kid-of e 1)))
                (list (ex-ind :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil)
                      (ex-ind :m f 0 nil (cadr r) fuel nil nil (cons (ex-rec e 2 0 fl rs (list x)) ks) x nil)
                      (ex-ind :m f 0 nil (cadr r) fuel nil nil (cons (ex-rec e 4 0 fl rs (list x)) ks) nil nil)
                      (ex-ind :m (ex-cbody e (cdr w)) 0 nil fh fuel nil nil (cons (ex-rec e 3 0 fl rs nil) ks) nil nil)
                      (ex-ind :m f 0 nil (cadr rh) fuel nil nil (cons (ex-rec e 2 0 fl rs (list (val (car rh)))) ks) (val (car rh)) nil)
                      (ex-ind :m f 0 nil (cadr rh) fuel nil nil (cons (ex-rec e 4 0 fl rs (list (val (car rh)))) ks) nil nil))))
             ((equal k 6)
              (let* ((h (ex-kid-of e 0)) (r (ex-ev :m h 0 nil fr fuel)))
                (if (ex-linked h)
                    (ex-ind :call e 1 (list (ex-c h)) fr fuel fl rs ks (ex-c h) tl)
                  (list (ex-ind :m h 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil)
                        (ex-ind :call e 1 (list (val (car r))) (cadr r) fuel fl rs ks (val (car r)) tl)))))
             (t nil))))))

; ---- each construct, given what its parts do ----------------------------------------------------

(defthm ex-i2-natp (natp (ex-i2 e)) :rule-classes :type-prescription)
(defthm ex-s2-natp (natp (ex-s2 e)) :rule-classes :type-prescription)
(defthm ex-nk-natp (natp (ex-nk e)) :rule-classes :type-prescription)
(defthm ex-rstart-natp (natp (ex-rstart e)) :rule-classes :type-prescription)
(defthm ex-rn-natp (natp (ex-rn e)) :rule-classes :type-prescription)
(in-theory (disable ex-kind ex-i2 ex-s2 ex-nk ex-c ex-mark ex-rstart ex-rn ex-kids))

(defmacro ex-other (flg) `(not (member-equal ,flg '(:iter :do :let :rec :call :cs :fin))))
(defmacro ex-r (kid fr fuel) `(ex-ev :m ,kid 0 nil ,fr ,fuel))

(defmacro ex-case (name hyps &key (flg 'flg) (off 'nil) (ex 'nil) (cases 'nil))
  `(defthm ,name
     (implies (and ,@hyps) (ex-good ,flg e i tmp fr fuel fl rs ks v0 tl))
     :hints (("Goal" :expand ((:free (fr fuel tmp) (ex-ev ,flg e i tmp fr fuel)) (:free (tl) (ex-wf ,flg e i tl)) ,@ex)
                     ,@(and cases `(:cases ,cases))
                     :in-theory (disable ex-ev ex-wf c+ ex-run ex-kid-of ,@off)))))

(ex-case ex-good-atom ((not (consp e))))

(ex-case ex-good-leaf ((ex-other flg) (not (member-equal (ex-kind e) '(4 5 6 11 12 16 17 18)))))

; an if, a case for each way its test goes
(defmacro ex-if-test () '(ex-good :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil))
(defmacro ex-if-branch (j)
  `(ex-good :m (ex-kid-of e ,j) 0 nil (cadr (ex-r (ex-kid-of e 0) fr fuel)) fuel fl rs ks (val (car (ex-r (ex-kid-of e 0) fr fuel))) tl))
(ex-case ex-good-if-out ((ex-other flg) (consp e) (equal (ex-kind e) 4) (not (valp (car (ex-r (ex-kid-of e 0) fr fuel)))) (ex-if-test)))
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

; a call: its head (direct-linked or run), each argument, the entry
(defthm ex-wf-var-not-mk (implies (and (ex-wf :m h 0 tl) (equal (ex-kind h) 3)) (not (equal (ex-c h) *ex-mk*)))
  :hints (("Goal" :expand ((ex-wf :m h 0 tl)))))
(ex-case ex-good-m-call-linked
  ((ex-other flg) (consp e) (equal (ex-kind e) 6) (ex-linked (ex-kid-of e 0))
   (ex-good :call e 1 (list (ex-c (ex-kid-of e 0))) fr fuel fl rs ks (ex-c (ex-kid-of e 0)) tl))
  :cases ((ex-ifn (ex-c (ex-kid-of e 0)))))
(ex-case ex-good-m-call
  ((ex-other flg) (consp e) (equal (ex-kind e) 6) (not (ex-linked (ex-kid-of e 0)))
   (ex-good :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil)
   (ex-good :call e 1 (list (val (car (ex-r (ex-kid-of e 0) fr fuel)))) (cadr (ex-r (ex-kid-of e 0) fr fuel)) fuel fl rs ks
            (val (car (ex-r (ex-kid-of e 0) fr fuel))) tl))
  :cases ((ex-ifn (val (car (ex-r (ex-kid-of e 0) fr fuel))))))
(ex-case ex-good-call-mid
  ((consp e) (< (nfix i) (ex-nk e))
   (ex-good :m (ex-kid-of e (nfix i)) 0 nil fr fuel nil nil (cons (ex-rec e 3 (nfix i) fl rs tmp) ks) v0 nil)
   (ex-good :call e (+ 1 (nfix i)) (append tmp (list (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel)))))
            (cadr (ex-r (ex-kid-of e (nfix i)) fr fuel)) fuel fl rs ks (val (car (ex-r (ex-kid-of e (nfix i)) fr fuel))) tl))
  :flg :call)
(ex-case ex-good-call-zp ((consp e) (not (< (nfix i) (ex-nk e))) (zp fuel)) :flg :call)
(ex-case ex-good-call-enter
  ((consp e) (not (< (nfix i) (ex-nk e))) (not (zp fuel))
   (ex-good :iter (ex-fbody (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) 0 nil (ex-bind (car (ex-callee tmp)) (cdr (ex-callee tmp))) (+ -1 fuel) t
            (ex-fbody (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (cons (ex-rec e 5 (nfix i) fl rs fr) ks) v0 nil))
  :flg :call :off (ex-bind))

(ex-case ex-good-iter-zp
  ((consp e) (zp fuel) (ex-good :m e 0 nil fr fuel t e ks v0 t))
  :flg :iter)
(ex-case ex-good-iter
  ((consp e) (not (zp fuel)) (ex-good :m e 0 nil fr fuel t e ks v0 t)
   (ex-good :iter e 0 nil (cadr (ex-r e fr fuel)) (+ -1 fuel) fl rs ks nil tl))
  :flg :iter)

;; a throw: its value, then the throw over its record, which k_unwind pops
(ex-case ex-good-m-throw
  ((ex-other flg) (consp e) (equal (ex-kind e) 17)
   (ex-good :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil)))

; a try: its body; a throw from it caught by a clause, whose body runs;
; the finally after either, when there is one
(defthm ex-catchw-j
  (implies (equal (car (ex-catchw cs v j)) 1)
           (and (natp (cdr (ex-catchw cs v j))) (<= (nfix j) (cdr (ex-catchw cs v j)))
                (< (cdr (ex-catchw cs v j)) (+ (nfix j) (len cs)))))
  :rule-classes nil)
(defun ex-csind (e i j)
  (declare (xargs :measure (nfix (- (len (ex-c e)) (nfix i)))))
  (if (and (< (nfix i) (len (ex-c e))) (< (nfix i) (nfix j))) (ex-csind e (1+ (nfix i)) j) i))
(defthm ex-wf-cs-body
  (implies (and (ex-wf :cs e i tl) (natp i) (natp j) (<= i j) (< j (len (ex-c e))))
           (ex-wf :m (ex-cbody e j) 0 nil))
  :hints (("Goal" :induct (ex-csind e i j) :expand ((ex-wf :cs e i tl)) :in-theory (disable ex-kid-of))))
(defthm ex-wf-catch
  (implies (and (ex-wf :cs e 0 tl) (equal (car (ex-catchw (ex-c e) v 0)) 1))
           (ex-wf :m (ex-cbody e (cdr (ex-catchw (ex-c e) v 0))) 0 nil))
  :hints (("Goal" :use ((:instance ex-catchw-j (cs (ex-c e)) (j 0))) :in-theory (disable ex-wf))))
(in-theory (disable ex-catchw))

(defmacro ex-tB () '(ex-r (ex-kid-of e 0) fr fuel))
(defmacro ex-tw () '(ex-catchw (ex-c e) (val (car (ex-tB))) 0))
(defmacro ex-tfh () '(update-nth (ex-cslot e (cdr (ex-tw))) (val (car (ex-tB))) (cadr (ex-tB))))
(defmacro ex-tH () '(ex-r (ex-cbody e (cdr (ex-tw))) (ex-tfh) fuel))
(defmacro ex-tcase (name hyps) `(ex-case ,name ,hyps :ex ((:free (tmp fr) (ex-ev :fin e 0 tmp fr fuel)))))
(defmacro ex-tgB () '(ex-good :m (ex-kid-of e 0) 0 nil fr fuel nil nil (cons (ex-rec e 1 0 fl rs nil) ks) v0 nil))
(defmacro ex-tgF (fr pc v v0)
  `(ex-good :m (ex-kid-of e 1) 0 nil ,fr fuel nil nil (cons (ex-rec e ,pc 0 fl rs (list ,v)) ks) ,v0 nil))
(defmacro ex-tgH () '(ex-good :m (ex-cbody e (cdr (ex-tw))) 0 nil (ex-tfh) fuel nil nil (cons (ex-rec e 3 0 fl rs nil) ks) nil nil))

(ex-tcase ex-good-try-val
  ((ex-other flg) (consp e) (equal (ex-kind e) 18) (valp (car (ex-tB))) (ex-tgB) (ex-tgF (cadr (ex-tB)) 2 (val (car (ex-tB))) (val (car (ex-tB))))))
(ex-tcase ex-good-try-uncaught
  ((ex-other flg) (consp e) (equal (ex-kind e) 18) (ex-thp (car (ex-tB))) (not (equal (car (ex-tw)) 1)) (ex-tgB)
   (ex-tgF (cadr (ex-tB)) 4 (val (car (ex-tB))) nil)))
(ex-tcase ex-good-try-caught
  ((ex-other flg) (consp e) (equal (ex-kind e) 18) (ex-thp (car (ex-tB))) (equal (car (ex-tw)) 1) (ex-tgB) (ex-tgH)
   (ex-tgF (cadr (ex-tH)) 2 (val (car (ex-tH))) (val (car (ex-tH))))
   (ex-tgF (cadr (ex-tH)) 4 (val (car (ex-tH))) nil)))
(ex-tcase ex-good-try-out
  ((ex-other flg) (consp e) (equal (ex-kind e) 18) (not (valp (car (ex-tB)))) (not (ex-thp (car (ex-tB)))) (ex-tgB)))
(defthm ex-good-try
  (implies (and (ex-other flg) (consp e) (equal (ex-kind e) 18) (ex-tgB)
                (ex-tgF (cadr (ex-tB)) 2 (val (car (ex-tB))) (val (car (ex-tB))))
                (ex-tgF (cadr (ex-tB)) 4 (val (car (ex-tB))) nil) (ex-tgH)
                (ex-tgF (cadr (ex-tH)) 2 (val (car (ex-tH))) (val (car (ex-tH))))
                (ex-tgF (cadr (ex-tH)) 4 (val (car (ex-tH))) nil))
           (ex-good flg e i tmp fr fuel fl rs ks v0 tl))
  :hints (("Goal" :in-theory (disable ex-good ex-ev ex-wf ex-kid-of ex-nk valp val ex-rec ex-thp
                                      ex-good-try-val ex-good-try-uncaught ex-good-try-caught ex-good-try-out)
                  :use (ex-good-try-val ex-good-try-uncaught ex-good-try-caught ex-good-try-out))))

; ---- THE THEOREM ----------------------------------------------------------------------------------

(defthm ex-good-cs-fin (implies (member-equal flg '(:cs :fin)) (ex-good flg e i tmp fr fuel fl rs ks v0 tl)))

(defthm ex-machine-correct-flag
  (ex-good flg e i tmp fr fuel fl rs ks v0 tl)
  :rule-classes nil
  :hints (("Goal" :induct (ex-ind flg e i tmp fr fuel fl rs ks v0 tl)
                  :in-theory (disable ex-good ex-ev ex-wf ex-run ex-step c+ ex-kid-of ex-rec ex-kind ex-nk ex-i2 ex-s2 ex-bind ex-fbody))))

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

; ---- APPLY ----------------------------------------------------------------------------------------
;
; APPLY OF A CLOSURE IS THE CALL OF IT ON THE SPREAD ARGUMENTS: at a call's
; entry, a record whose callee is apply answers -- in the meaning, and so
; (ex-machine-correct) by the machine -- what the record of f and the
; spread arguments does; and the machine's entry turn, when an arity fits,
; is that record's (when none does, both throw the arity error).

(defthm ex-apply-is-call
  (implies (and (equal (ex-apway tmp) 1) (consp e) (<= (ex-nk e) (nfix i)))
           (equal (ex-ev :call e i tmp fr fuel) (ex-ev :call e i (ex-callee tmp) fr fuel)))
  :hints (("Goal" :expand ((ex-ev :call e i tmp fr fuel) (ex-ev :call e i (ex-callee tmp) fr fuel))
                  :in-theory (disable ex-ev ex-enters ex-arerr ex-fbody ex-bind))))

(defthm ex-apply-turn
  (implies (and (equal (ex-apway tmp) 1) (equal (ex-kind e) 6)
                (consp (ex-arity (nth 1 (cadr (car (ex-callee tmp)))) (len (cdr (ex-callee tmp))))))
           (equal (ex-turn (cons (ex-rec e 4 i fl rs tmp) ks) v fr)
                  (ex-turn (cons (ex-rec e 4 i fl rs (ex-callee tmp)) ks) v fr)))
  :hints (("Goal" :in-theory (disable ex-fbody ex-bind ex-arity))))

; APPLY'S WALK IS THE CALL'S DISPATCH. For a closure's arities as clj
; allows them (Compiler FnExpr: every arity's count a natural, no fixed one
; of more parameters than the variadic one's), B_APPLY's walk with req the
; variadic arity's count either hands over (way 2) -- and then the arity the
; spread call's count picks is the variadic one, its locals exactly the
; walk's fixed arguments and rest -- or spreads everything (way 3), the
; call itself.
(defun ex-arsane (ars req)
  (if (atom ars)
      t
    (and (natp (nth 0 (car ars)))
         (or (truthy (nth 1 (car ars))) (<= (nth 0 (car ars)) (ifix req)))
         (ex-arsane (cdr ars) req))))

(defthm ex-arsane-no-fixed
  (implies (and (ex-arsane ars req) (integerp req) (integerp m) (< req m)) (not (ex-arity-pass ars m 0)))
  :hints (("Goal" :in-theory (enable ex-arfit))))
(defthm ex-arsane-variadic
  (implies (and (ex-arsane ars r) (equal req (ex-varnf ars)) (<= 0 req) (<= req m) (integerp m))
           (and (truthy (nth 1 (ex-arity-pass ars m 1))) (equal (nth 0 (ex-arity-pass ars m 1)) req)))
  :hints (("Goal" :in-theory (enable ex-arfit))))

(defthm ex-take-append (implies (<= (nfix n) (len a)) (equal (take n (append a b)) (take n a))))
(defthm ex-nthcdr-append (implies (<= (nfix n) (len a)) (equal (nthcdr n (append a b)) (append (nthcdr n a) b))))
(defthm ex-len-append (equal (len (append a b)) (+ (len a) (len b))))

(defthm ex-append-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm ex-len-consp (implies (consp s) (< 0 (len s))) :rule-classes :linear)
(defthm ex-arity-variadic-pass
  (implies (and (ex-arsane ars (ex-varnf ars)) (<= 0 (ex-varnf ars)) (integerp m) (<= (ex-varnf ars) m))
           (and (consp (ex-arity-pass ars m 1)) (nth 1 (ex-arity-pass ars m 1)) (not (equal (nth 1 (ex-arity-pass ars m 1)) :false))
                (equal (car (ex-arity-pass ars m 1)) (ex-varnf ars))))
  :hints (("Goal" :use ((:instance ex-arsane-variadic (r (ex-varnf ars)) (req (ex-varnf ars))))
                  :in-theory (disable ex-arsane-variadic))))
(defthm ex-arity-variadic
  (implies (and (ex-arsane ars (ex-varnf ars)) (<= 0 (ex-varnf ars)) (integerp m) (< (ex-varnf ars) m))
           (equal (ex-arity ars m) (ex-arity-pass ars m 1)))
  :hints (("Goal" :use ((:instance ex-arsane-no-fixed (req (ex-varnf ars))))
                  :in-theory (disable ex-arsane-no-fixed))))

(defthm ex-aplwalk-call
  (implies (and (ex-arsane ars req) (equal req (ex-varnf ars)) (true-listp fx) (true-listp s))
           (let ((w (ex-aplwalk req fx s)) (args (append fx s)))
             (and (implies (equal (car w) 2)
                           (let ((ar (ex-arity ars (len args))))
                             (and (truthy (nth 1 ar)) (equal (nth 0 ar) req)
                                  (equal (ex-bargs ar args) (append (cadr w) (list (caddr w)))))))
                  (implies (not (equal (car w) 2)) (and (equal (car w) 3) (equal (cadr w) args))))))
  :hints (("Goal" :induct (ex-aplwalk req fx s) :in-theory (e/d (ex-apstep ex-bargs ex-rest-args) (ex-arity)))))

; OVER EVERY KIND (seqk): the walk over a seq's cursor is the walk over its
; elements -- the same way and fixed arguments, the rest's elements the
; arguments past them and what the cursor it hands over still holds -- for
; a seq of finitely many (sk-els's :ok, at any bound l).
(defun ex-apw-ind (req fx c l)
  (declare (xargs :measure (+ (* 2 (nfix (- (ifix req) (len fx)))) (sk-rank c))))
  (let* ((k (len fx)) (d (if (equal (ex-aplook req k) 1) (sk-d c) 1)))
    (if (equal d 3)
        (ex-apw-ind req fx (sk-next c) l)
      (if (and (equal (ex-apstep req k (if (sk-more d) 1 0)) 1) (sk-more d) (< k (ifix req)))
          (ex-apw-ind req (append fx (list (sk-first c))) (sk-next c) l)
        (list fx c l)))))

(defthm ex-sk-els-step
  (implies (and (equal (car (sk-els c l)) :ok) (sk-more (sk-d c)))
           (and (equal (car (sk-els (sk-next c) l)) :ok)
                (equal (cdr (sk-els c l)) (cons (sk-first c) (cdr (sk-els (sk-next c) l))))))
  :hints (("Goal" :expand ((sk-els c l)) :use ((:instance sk-els-mono (c (sk-next c)) (l (1- l)) (l2 l))))))
(defthm ex-sk-els-real
  (implies (equal (sk-d c) 3) (equal (sk-els c l) (sk-els (sk-next c) l)))
  :hints (("Goal" :expand ((sk-els c l)))))
(defthm ex-sk-els-end
  (implies (and (equal (car (sk-els c l)) :ok) (not (sk-more (sk-d c))) (not (equal (sk-d c) 3)))
           (equal (cdr (sk-els c l)) nil))
  :hints (("Goal" :expand ((sk-els c l)))))

(defthm ex-apwalk-els
  (implies (and (equal (car (sk-els c l)) :ok) (true-listp fx))
           (let ((w (ex-apwalk req fx c)) (v (ex-aplwalk req fx (cdr (sk-els c l)))))
             (and (equal (car w) (car v))
                  (implies (equal (car w) 2)
                           (and (equal (cadr w) (cadr v)) (equal (car (sk-els (cadddr w) l)) :ok)
                                (equal (append (caddr w) (cdr (sk-els (cadddr w) l))) (caddr v))))
                  (implies (not (equal (car w) 2))
                           (and (equal (car (sk-els (caddr w) l)) :ok)
                                (equal (append (cadr w) (cdr (sk-els (caddr w) l))) (cadr v)))))))
  :hints (("Goal" :induct (ex-apw-ind req fx c l)
                  :in-theory (enable ex-apstep ex-aplook)
                  :expand ((ex-apwalk req fx c) (:free (s) (ex-aplwalk req fx s))))))

(defthm ex-apwalk-call
  (implies (and (ex-arsane ars req) (equal req (ex-varnf ars)) (true-listp fx) (equal (car (sk-els c l)) :ok))
           (let ((w (ex-apwalk req fx c)) (args (append fx (cdr (sk-els c l)))))
             (and (implies (equal (car w) 2)
                           (let ((ar (ex-arity ars (len args))))
                             (and (truthy (nth 1 ar)) (equal (nth 0 ar) req)
                                  (equal (ex-bargs ar args)
                                         (append (cadr w) (list (append (caddr w) (cdr (sk-els (cadddr w) l)))))))))
                  (implies (not (equal (car w) 2))
                           (and (equal (car w) 3) (equal (append (cadr w) (cdr (sk-els (caddr w) l))) args))))))
  :hints (("Goal" :use (ex-apwalk-els (:instance ex-aplwalk-call (s (cdr (sk-els c l)))))
                  :in-theory (disable ex-apwalk-els ex-aplwalk-call ex-arity ex-bargs))))

; HOW FAR IT REALISES: positions k .. req + 1 at most -- clj's
; boundedLength exactly -- one realisation each (seqk's
; ex-apwalk-realise-bound, with the walk); a vector's walk, and a list's,
; none.
; a cursor no step of which realises anything: a vector's view, a list, or a
; list's tail -- every step stays one
(defun ex-noreal (c) (or (not (caddr c)) (and (consp (car c)) (not (member (caar c) (quote (:lazy :cons)))) (eq (caddr c) t))))
(defthm ex-noreal-next
  (implies (ex-noreal c) (and (ex-noreal (sk-next c)) (not (equal (sk-d c) 3))))
  :hints (("Goal" :in-theory (enable sk-d sk-next))))
(defthm ex-apwalk-noreal
  (implies (ex-noreal c) (equal (nth 4 (ex-apwalk req fx c)) 0))
  :hints (("Goal" :induct (ex-apwalk req fx c) :expand ((ex-apwalk req fx c)) :in-theory (disable ex-noreal))))
(defthm ex-apwalk-vector (equal (nth 4 (ex-apwalk req fx (list (cons :vec e) i t))) 0)
  :hints (("Goal" :use ((:instance ex-apwalk-noreal (c (list (cons :vec e) i t)))))))
(defthm ex-apwalk-list
  (implies (and (consp v) (not (member (car v) '(:lazy :cons))))
           (equal (nth 4 (ex-apwalk req fx (sk-cur v))) 0))
  :hints (("Goal" :in-theory (enable sk-cur) :use ((:instance ex-apwalk-noreal (c (list v 0 t)))))))

; THE TREE EVALUATOR'S CORE (src/f/exec.inc run_loop), at the level the
; Fortran is GENERATED from (src/f/gen/exec_gen.inc, scripts/acl2-fortran
; -b exec), guard-verified. Milestone 1 of model/exec-PLAN.md.
;
; exec.inc runs the analyzer's tree on a stack of records, one a node
; pending: the node, a program counter pc, a counter i, the restart flag
; (KF_RESTART) and the restart node, all in one frame of local slots the
; records of a fn body share. Each turn of run_loop looks at the top
; record and does one thing. For the CORE KINDS -- a constant, a local,
; if, do, let*, loop* and recur -- what it does is decided here:
;
;   ex-act   the action, from the node's kind, the record's pc and i, the
;            node's count of children nk and its operand i2 (a let's or
;            loop's count of bindings), and whether the value in flight is
;            truthy:
;              1 finish with the constant     2 finish with the local's slot
;              3 push a child (a fresh record, no restart)
;              4 become a child (k_tail: the record's restart kept)
;              5 finish with nil              6 bind the value to slot s2+i
;              7 become the loop's body, the record restarting at it
;              8 open a recur's temporaries   9 keep the value in them
;             10 write them to the loop's slots and finish with the
;                recur marker               0 not a core kind
;   ex-kid   which child a push or a tail takes
;   ex-pc    the record's pc after it, ex-i its i
;   ex-fin   k_finish: 1 when the record restarts (its flag set and the
;            value the recur marker), 0 when it is popped
;
; and run_loop's shim (exec.inc exec_core) does it. THE MACHINE below is
; that shim, a turn at a time, the decisions these functions; THE MEANING
; is what each core node answers, big-step, counting the turns it takes.
; Theorems, in exec-proof.lisp: the machine run for a node's count of turns
; from a record of it reaches what the meaning says -- the record popped
; with the node's value, or, for a recur in a loop body's tail, the loop's
; record back at its body with the loop's slots rebound -- so the slot a
; local reads holds the value its binding gave it; and in exec-vm.lisp,
; the meaning is vmx's mx (model/vmx.lisp) on the tree's translation, the
; one vmx-proof proves the VM runs. exec-cost.lisp counts the turns.

(in-package "ACL2")

(defconst *ex40* 1099511627776)

(defmacro ex40p (x) `(and (natp ,x) (< ,x *ex40*)))

; ---- THE DECISIONS (generated) ---------------------------------------------------------------
;
; kinds as Eval.f90 numbers them: N_CONST 1, N_LOCAL 2, N_IF 4, N_DO 5,
; N_LET 11, N_LOOP 12, N_RECUR 16; tv 1 when the value in flight is truthy

(defun ex-act (k pc i nk n2 tv)
  (declare (xargs :guard t))
  (cond ((equal k 1) 1)
        ((equal k 2) 2)
        ((equal k 4) (cond ((equal pc 0) 3) ((equal tv 1) 4) ((and (integerp nk) (< 2 nk)) 4) (t 5)))
        ((equal k 5) (cond ((not (and (integerp nk) (< 0 nk))) 5)
                           ((and (integerp i) (< i (- nk 1))) 3)
                           (t 4)))
        ((or (equal k 11) (equal k 12))
         (cond ((equal pc 1) 6)
               ((and (integerp i) (integerp n2) (< i n2)) 3)
               ((equal k 12) 7)
               (t 4)))
        ((equal k 16) (cond ((equal pc 0) 8)
                            ((equal pc 2) 9)
                            ((and (integerp i) (integerp nk) (< i nk)) 3)
                            (t 10)))
        (t 0)))

(defun ex-kid (k pc i nk n2 tv)
  (declare (xargs :guard t))
  (cond ((equal k 4) (cond ((equal pc 0) 0) ((equal tv 1) 1) (t 2)))
        ((equal k 5) (if (and (integerp i) (integerp nk) (< i (- nk 1))) i (if (and (ex40p nk) (< 0 nk)) (- nk 1) 0)))
        ((or (equal k 11) (equal k 12)) (if (and (integerp i) (integerp n2) (< i n2)) i (if (ex40p n2) n2 0)))
        (t (if (ex40p i) i 0))))

(defun ex-pc (k pc i nk n2 tv)
  (declare (xargs :guard t) (ignore i nk n2 tv))
  (cond ((equal k 4) 1)
        ((or (equal k 11) (equal k 12)) (if (equal pc 1) 0 1))
        ((equal k 16) (if (equal pc 1) 2 1))
        (t 0)))

(defun ex-i (k pc i nk n2 tv)
  (declare (xargs :guard t) (ignore nk n2 tv))
  (let ((i1 (if (ex40p i) (+ i 1) 0)))
    (cond ((equal k 5) i1)
          ((or (equal k 11) (equal k 12)) (if (equal pc 1) i1 i))
          ((equal k 16) (cond ((equal pc 0) 0) ((equal pc 2) i1) (t i)))
          (t i))))

(defun ex-fin (rf mk)
  (declare (xargs :guard t))
  (if (and (equal rf 1) (equal mk 1)) 1 0))

; ---- THE TREE, as exec.inc reads it ------------------------------------------------------------
;
; a node (kind i2 kids c s2 mark rstart rn): gc_i1, gc_i2, its children
; (slot 1); a constant's value (slot 2), a let's or loop's first slot
; (int_of slot 2), a local marked for clearing (slot 3 a boolean: anpass's
; last read), a recur's target slots (its rinfo's start and count)

(defun ex-kind (e) (nth 0 e))
(defun ex-i2 (e) (nfix (nth 1 e)))
(defun ex-kids (e) (nth 2 e))
(defun ex-c (e) (nth 3 e))
(defun ex-s2 (e) (nfix (nth 4 e)))
(defun ex-mark (e) (nth 5 e))
(defun ex-rstart (e) (nfix (nth 6 e)))
(defun ex-rn (e) (nfix (nth 7 e)))
(defun ex-nk (e) (len (ex-kids e)))
(defun ex-kid-of (e j) (nth j (ex-kids e)))

(defun truthy (x) (not (or (null x) (eq x :false))))
(defun val (r) (cdr r))
(defun valp (r) (eq (car r) :val))

; the recur marker (exec.inc recur_marker): one object, no value the
; program can hold
(defconst *ex-mk* '(:recur-marker))

; ---- THE MACHINE: run_loop's turn for the core kinds -----------------------------------------
;
; a state (records val frame); a record (node pc i restart rnode tmp), tmp
; a recur's temporaries (the value-stack region exec_core opens)

(defun ex-rec (e pc i fl rs tmp) (list e pc i fl rs tmp))

; vals into slots start, start+1, ... (exec_core's action 10)
(defun ex-write (start vals fr)
  (if (atom vals) fr (ex-write (1+ (nfix start)) (cdr vals) (update-nth (nfix start) (car vals) fr))))

; k_finish
(defun ex-finish (v ks fr)
  (let* ((r (car ks)) (fl (nth 3 r)) (rs (nth 4 r)))
    (if (equal (ex-fin (if fl 1 0) (if (equal v *ex-mk*) 1 0)) 1)
        (list (cons (ex-rec rs 0 0 fl rs nil) (cdr ks)) nil fr)
      (list (cdr ks) v fr))))

; one turn with records ks, at least one
(defun ex-turn (ks val fr)
  (let ((s (list ks val fr)))
    (if (atom ks)
        s
      (let* ((r (car ks)) (e (nth 0 r)) (pc (nth 1 r)) (i (nth 2 r)) (fl (nth 3 r)) (rs (nth 4 r)) (tmp (nth 5 r))
             (k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (tv (if (truthy val) 1 0))
             (j (ex-kid k pc i nk n2 tv)) (pc2 (ex-pc k pc i nk n2 tv)) (i2 (ex-i k pc i nk n2 tv)))
        (case (ex-act k pc i nk n2 tv)
          (1 (ex-finish (ex-c e) ks fr))
          (2 (ex-finish (nth n2 fr) ks (if (ex-mark e) (update-nth n2 nil fr) fr)))
          (3 (list (cons (ex-rec (ex-kid-of e j) 0 0 nil nil nil) (cons (ex-rec e pc2 i2 fl rs tmp) (cdr ks))) val fr))
          (4 (list (cons (ex-rec (ex-kid-of e j) 0 0 fl rs nil) (cdr ks)) val fr))
          (5 (ex-finish nil ks fr))
          (6 (list (cons (ex-rec e pc2 i2 fl rs tmp) (cdr ks)) val (update-nth (+ (ex-s2 e) (nfix i)) val fr)))
          (7 (list (cons (ex-rec (ex-kid-of e j) 0 0 t (ex-kid-of e j) nil) (cdr ks)) val fr))
          (8 (list (cons (ex-rec e pc2 i2 fl rs nil) (cdr ks)) val fr))
          (9 (list (cons (ex-rec e pc2 i2 fl rs (append tmp (list val))) (cdr ks)) val fr))
          (10 (ex-finish *ex-mk* ks (ex-write (ex-rstart e) (take (min (ex-rn e) nk) tmp) fr)))
          (otherwise s))))))

(defun ex-step (s) (if (atom (car s)) s (ex-turn (car s) (cadr s) (caddr s))))

(defun ex-run (s n)
  (if (zp n) s (ex-run (ex-step s) (1- n))))

; ---- THE MEANING --------------------------------------------------------------------------------
;
; (ex-ev flg e i tmp fr fuel) is (res fr2 turns): what a record of e
; answers, the frame after, and how many turns it takes; res (:val . v),
; (:recur) for a recur that went back to its loop, or (:out) -- fuel ran
; out, or something no core kind. The flags are the record's places:
;   :m     a fresh record of e
;   :do    a do's record at its i-th child
;   :let   a let's or loop's record at its i-th binding
;   :rec   a recur's record at its i-th argument, tmp the values so far
;   :iter  a loop's record at its body e, restarting at it
; a loop's iterations take fuel, as vmx's do.

(defun c+ (a b) (+ (nfix a) (nfix b)))

(defun ex-rank (flg) (case flg (:iter 2) ((:do :let :rec) 0) (otherwise 1)))

(defun ex-left (flg e i)
  (case flg
    (:let (nfix (- (ex-i2 e) (nfix i))))
    ((:do :rec) (nfix (- (ex-nk e) (nfix i))))
    (otherwise 0)))

(defthm ex-nth-count (<= (acl2-count (nth j l)) (acl2-count l)) :rule-classes :linear)
(defthm ex-nth-count-strict (implies (consp l) (< (acl2-count (nth j l)) (acl2-count l))) :rule-classes :linear)
(defthm ex-kid-count (implies (consp e) (< (acl2-count (ex-kid-of e j)) (acl2-count e))) :rule-classes :linear
  :hints (("Goal" :in-theory (disable ex-nth-count ex-nth-count-strict)
                  :use ((:instance ex-nth-count (l (nth 2 e))) (:instance ex-nth-count-strict (j 2) (l e))))))

(defun ex-ev (flg e i tmp fr fuel)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (case flg
      (:iter (if (not (consp e))
                 (list (list :out) fr 0)
               (let* ((r (ex-ev :m e 0 nil fr fuel)) (res (car r)))
                 (cond ((not (eq (car res) :recur)) r)
                       ((zp fuel) (list (list :out) fr 0))
                       (t (let ((r2 (ex-ev :iter e 0 nil (cadr r) (1- fuel))))
                            (list (car r2) (cadr r2) (c+ (caddr r) (caddr r2)))))))))
      (:do (cond ((not (consp e)) (list (list :out) fr 0))
                 ((zp nk) (list (cons :val nil) fr 1))
                 ((< i (- nk 1))
                  (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (if (not (valp (car r)))
                        (list (list :out) fr 0)
                      (let ((r2 (ex-ev :do e (1+ i) tmp (cadr r) fuel)))
                        (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (caddr r2))))))))
                 (t (let ((r (ex-ev :m (ex-kid-of e (- nk 1)) 0 nil fr fuel)))
                      (list (car r) (cadr r) (c+ 1 (caddr r)))))))
      (:let (cond ((not (consp e)) (list (list :out) fr 0))
                  ((< i n2)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (if (not (valp (car r)))
                         (list (list :out) fr 0)
                       (let ((r2 (ex-ev :let e (1+ i) tmp (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                  ((equal k 12)
                   (let ((r (ex-ev :iter (ex-kid-of e n2) 0 nil fr fuel)))
                     (list (car r) (cadr r) (c+ 1 (caddr r)))))
                  (t (let ((r (ex-ev :m (ex-kid-of e n2) 0 nil fr fuel)))
                       (list (car r) (cadr r) (c+ 1 (caddr r)))))))
      (:rec (cond ((not (consp e)) (list (list :out) fr 0))
                  ((< i nk)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (if (not (valp (car r)))
                         (list (list :out) fr 0)
                       (let ((r2 (ex-ev :rec e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                  (t (list (list :recur) (ex-write (ex-rstart e) (take (min (ex-rn e) nk) tmp) fr) 1))))
      (otherwise
       (cond ((not (consp e)) (list (list :out) fr 0))
             ((equal k 1) (list (cons :val (ex-c e)) fr 1))
             ((equal k 2) (list (cons :val (nth n2 fr)) (if (ex-mark e) (update-nth n2 nil fr) fr) 1))
             ((equal k 4)
              (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                (cond ((not (valp (car r))) (list (list :out) fr 0))
                      ((truthy (val (car r)))
                       (let ((r2 (ex-ev :m (ex-kid-of e 1) 0 nil (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))
                      ((< 2 nk)
                       (let ((r2 (ex-ev :m (ex-kid-of e 2) 0 nil (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))
                      (t (list (cons :val nil) (cadr r) (c+ 1 (c+ (caddr r) 1)))))))
             ((equal k 5) (ex-ev :do e 0 nil fr fuel))
             ((or (equal k 11) (equal k 12)) (ex-ev :let e 0 nil fr fuel))
             ((equal k 16) (let ((r (ex-ev :rec e 0 nil fr fuel)))
                             (list (car r) (cadr r) (c+ 1 (caddr r)))))
             (t (list (list :out) fr 0)))))))

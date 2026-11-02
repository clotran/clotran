; THE TREE EVALUATOR'S CORE (src/f/exec.inc run_loop), at the level the
; Fortran is GENERATED from (src/f/gen/exec_gen.inc, scripts/acl2-fortran
; -b exec), guard-verified. Milestones 1 and 2 of model/exec-PLAN.md.
;
; exec.inc runs the analyzer's tree on a stack of records, one a node
; pending: the node, a program counter pc, a counter i, the restart flag
; (KF_RESTART) and the restart node, in a frame of local slots the records
; of a fn body share. Each turn of run_loop looks at the top record and
; does one thing. For the CORE KINDS -- a constant, a local, a Var, if,
; do, let*, loop*, recur, fn and a call -- what it does is decided here:
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
;                                               (a recur's, a call's)
;             10 write them to the loop's slots and finish with the
;                recur marker
;             11 finish with the Var's value  12 finish with a closure
;             13 a call's head: push it, or take a direct-linked fn
;             14 keep the callee              15 the record's pc and i only
;             16 enter the callee: its body pushed, restarting, in a
;                frame of its own, the caller's kept in the record (or,
;                as ex-entry decides, throw the arity error)
;             17 the body answered: the caller's frame back, finish
;                                              0 not a core kind
;   ex-kid   which child a push or a tail takes
;   ex-pc    the record's pc after it, ex-i its i
;   ex-fin   k_finish: 1 when the record restarts (its flag set and the
;            value the recur marker), 0 when it is popped
;   ex-arfit an arity's fit to a call's count, ex-entry the entry's way
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
; kinds as Eval.f90 numbers them: N_CONST 1, N_LOCAL 2, N_VAR 3, N_IF 4,
; N_DO 5, N_CALL 6, N_LET 11, N_LOOP 12, N_FN 14, N_RECUR 16; tv 1 when the
; value in flight is truthy. A call's record: pc 0 its head, 1 the callee
; kept, 2 and 3 its arguments (i the next), 4 the entry, 5 the body done.

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
        ((equal k 3) 11)
        ((equal k 14) 12)
        ((equal k 6) (cond ((equal pc 0) 13)
                           ((equal pc 1) 14)
                           ((equal pc 2) (if (and (integerp i) (integerp nk) (< i nk)) 3 15))
                           ((equal pc 3) 9)
                           ((equal pc 4) 16)
                           ((equal pc 5) 17)
                           (t 0)))
        (t 0)))

(defun ex-kid (k pc i nk n2 tv)
  (declare (xargs :guard t))
  (cond ((equal k 4) (cond ((equal pc 0) 0) ((equal tv 1) 1) (t 2)))
        ((equal k 5) (if (and (integerp i) (integerp nk) (< i (- nk 1))) i (if (and (ex40p nk) (< 0 nk)) (- nk 1) 0)))
        ((or (equal k 11) (equal k 12)) (if (and (integerp i) (integerp n2) (< i n2)) i (if (ex40p n2) n2 0)))
        (t (if (ex40p i) i 0))))

(defun ex-pc (k pc i nk n2 tv)
  (declare (xargs :guard t) (ignore n2 tv))
  (cond ((equal k 4) 1)
        ((or (equal k 11) (equal k 12)) (if (equal pc 1) 0 1))
        ((equal k 16) (if (equal pc 1) 2 1))
        ((equal k 6) (cond ((equal pc 0) 1)
                           ((equal pc 1) 2)
                           ((equal pc 2) (if (and (integerp i) (integerp nk) (< i nk)) 3 4))
                           ((equal pc 3) 2)
                           ((equal pc 4) 5)
                           (t pc)))
        (t 0)))

(defun ex-i (k pc i nk n2 tv)
  (declare (xargs :guard t) (ignore nk n2 tv))
  (let ((i1 (if (ex40p i) (+ i 1) 0)))
    (cond ((equal k 5) i1)
          ((or (equal k 11) (equal k 12)) (if (equal pc 1) i1 i))
          ((equal k 16) (cond ((equal pc 0) 0) ((equal pc 2) i1) (t i)))
          ((equal k 6) (cond ((equal pc 1) 1) ((equal pc 3) i1) (t i)))
          (t i))))

(defun ex-fin (rf mk)
  (declare (xargs :guard t))
  (if (and (equal rf 1) (equal mk 1)) 1 0))

; A CALL'S ARITY (bind_closure's pick, clj's: Compiler FnExpr's arities):
; ex-arfit answers 1 when an arity of nf fixed parameters, variadic when vr
; is 1, is pass's pick for m arguments -- pass 0 the fixed arity of exactly
; m, pass 1 the variadic one of nf <= m, tried only when pass 0 found none.
(defun ex-arfit (pass nf vr m)
  (declare (xargs :guard t))
  (cond ((and (equal pass 0) (equal vr 0) (integerp nf) (equal nf m)) 1)
        ((and (equal pass 1) (equal vr 1) (integerp nf) (integerp m) (<= 0 nf) (<= nf m)) 1)
        (t 0)))

; A CALL'S ENTRY (exec_core's action 16): cl 1 when the callee is one of
; the machine's closures, fit 1 when an arity fits the count. 1: enter
; it; 2: throw the arity error (clj's ArityException); 0: not a closure
; -- the host's apply (a builtin, a Var's fn).
(defun ex-entry (cl fit)
  (declare (xargs :guard t))
  (cond ((not (equal cl 1)) 0) ((equal fit 1) 1) (t 2)))

; APPLY (clj's: core.clj's apply builds its last argument's seq after the
; others -- list*, the language's own -- and IFn.applyTo spreads it into
; the call: exec.inc's B_APPLY). ap 1 when the callee is apply, n its count
; of arguments, fk 1 when the fn it applies is one of the machine's
; closures, sq 1 when its last argument is a seq. 1: spread, then the
; call's own dispatch (ex-entry) on that fn; 2: apply's own arity error,
; fewer than two arguments (clj's ArityException); 3: the last is no seq,
; clj's RT.seq IllegalArgumentException; 0: not apply, or a fn the host
; applies -- a builtin, a Var's fn, or what is no fn at all, whose
; ClassCastException clj raises before it looks at the seq.
(defun ex-apentry (ap n fk sq)
  (declare (xargs :guard t))
  (cond ((not (equal ap 1)) 0)
        ((not (and (integerp n) (<= 2 n))) 2)
        ((not (equal fk 1)) 0)
        ((not (equal sq 1)) 3)
        (t 1)))

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
; program can hold -- not even a list of values, a variadic call's rest
; (so a dotted pair, no true list)
(defconst *ex-mk* '(:recur-marker . :recur-marker))
(defun no-mk (l) (not (member-equal *ex-mk* l)))

; ---- FNS AND CALLS, as exec.inc reads them ---------------------------------------------------
;
; An N_VAR's value is its Var's (exec.inc's var_deref, the host's: the
; namespace is not modelled, and nothing in these kinds defs, so it is the
; node's slot 2 here). A call's head is DIRECT-LINKED (DEVIATIONS 55) when
; it is an N_VAR with i2 1: its fn is taken at once, no record pushed.
; An N_FN's slot 2 is its template (name arities caps nslots self), as
; analyze.inc builds it: an arity (nfixed variadic start body), caps the
; capture records' slots in pairs (outer inner), oldest first (anbuild-props
; anb-fn-caps). A closure is vmx's (:clo template capvals), the values the
; outer slots held when it was made (make_closure_from). A call ENTERS a
; closure (is_node_closure) by the arity its count picks (ex-arity, the
; generated ex-arfit: the fixed arity of the count, else the variadic one
; of at most as many fixed parameters): a frame of nslots with the
; arguments from the arity's start -- a variadic arity's fixed ones, then
; the rest as one list, nil when none are left -- the captures in their
; inner slots and the closure in its self slot (bind_closure,
; bind_captures), and the arity's body run in it, restarting on a recur.
; A closure no arity fits THROWS the arity error (raise_arity, clj's
; ArityException). Any other callee -- a builtin, a Var's fn -- is the
; host's apply, not modelled here.

(defun ex-linked (h) (and (consp h) (equal (ex-kind h) 3) (equal (ex-i2 h) 1)))

(defun ex-caps (capv fr)
  (if (or (atom capv) (atom (cdr capv))) nil (cons (nth (nfix (car capv)) fr) (ex-caps (cddr capv) fr))))
(defun ex-mkclo (tm fr) (list :clo tm (ex-caps (nth 2 tm) fr)))

(defun ex-arity-pass (ars n pass)
  (cond ((atom ars) nil)
        ((equal (ex-arfit pass (nth 0 (car ars)) (if (truthy (nth 1 (car ars))) 1 0) n) 1) (car ars))
        (t (ex-arity-pass (cdr ars) n pass))))
(defun ex-arity (ars n) (or (ex-arity-pass ars n 0) (ex-arity-pass ars n 1)))
(defun ex-clo-shape (f) (and (consp f) (eq (car f) :clo) (consp (cdr f)) (consp (cddr f))))
(defun ex-callable (f n) (and (ex-clo-shape f) (consp (ex-arity (nth 1 (cadr f)) n))))
; a closure with no arity of the count: the arity error
(defun ex-arerr (f n) (and (ex-clo-shape f) (not (consp (ex-arity (nth 1 (cadr f)) n)))))
(defun ex-fbody (f n) (nth 3 (ex-arity (nth 1 (cadr f)) n)))

; vals into slots start, start+1, ... (exec_core's action 10, a call's arguments)
(defun ex-write (start vals fr)
  (if (atom vals) fr (ex-write (1+ (nfix start)) (cdr vals) (update-nth (nfix start) (car vals) fr))))
(defun ex-bind-caps (capv caps fr)
  (if (or (atom capv) (atom (cdr capv))) fr (ex-bind-caps (cddr capv) (cdr caps) (update-nth (nfix (cadr capv)) (car caps) fr))))
; a variadic arity's locals: its nf fixed arguments, then the rest as one
; list, nil when there are none (bind_closure; clj's RestFn: nil, not ())
(defun ex-rest-args (nf args) (append (take nf args) (list (nthcdr nf args))))
(defun ex-bargs (ar args) (if (truthy (nth 1 ar)) (ex-rest-args (nfix (nth 0 ar)) args) args))
(defun ex-bind (f args)
  (let* ((tm (cadr f)) (ar (ex-arity (nth 1 tm) (len args)))
         (fr (ex-bind-caps (nth 2 tm) (caddr f) (ex-write (nth 2 ar) (ex-bargs ar args) (make-list (nfix (nth 3 tm)) :initial-element nil)))))
    (if (natp (nth 4 tm)) (update-nth (nth 4 tm) f fr) fr)))

; APPLY, as a callee: the value :apply is clojure.core/apply (core.clj's
; fn, its list* and the applyTo it ends in, B_APPLY). A call of it with
; (f a1 .. an coll) is the call of f on a1 .. an and then coll's elements
; (ex-spread), dispatched as any call is; a seq is the model's list, nil
; the empty one -- a closure is none, and no list a program holds has the
; recur marker in it, as no value is it. A vector's or a lazy seq's walk
; (to_seq, sq_first, sq_rest) is the host's.
(defun ex-seqp (v) (and (true-listp v) (not (ex-clo-shape v)) (no-mk v)))
(defun ex-spread (args) (append (butlast args 1) (car (last args))))
(defun ex-apway (tmp)
  (ex-apentry (if (equal (car tmp) :apply) 1 0) (len (cdr tmp)) (if (ex-clo-shape (cadr tmp)) 1 0)
              (if (ex-seqp (car (last (cdr tmp)))) 1 0)))
; the call a record's callee and arguments make: apply's (f . spread) when
; it spreads, else themselves
(defun ex-callee (tmp) (if (equal (ex-apway tmp) 1) (cons (cadr tmp) (ex-spread (cddr tmp))) tmp))

; APPLY'S WALK, as B_APPLY takes it: (way fixed rest), way ex-apstep's 2
; or 3 -- 2 the variadic arity's fixed arguments and its rest, 3 every
; argument, spread. fx the arguments taken so far, s the seq's elements.
(defun ex-apwalk (req fx s)
  (declare (xargs :measure (len s)))
  (let ((w (ex-apstep req (len fx) (if (consp s) 1 0))))
    (cond ((and (equal w 1) (consp s)) (ex-apwalk req (append fx (list (car s))) (cdr s)))
          ((equal w 2) (list 2 (take (nfix req) fx) (append (nthcdr (nfix req) fx) s)))
          (t (list 3 (append fx s) nil)))))
; the variadic arity's count of fixed parameters, -1 for none (B_APPLY's
; req: exec.inc variadic_req, the first variadic arity's, as the variadic
; pass of ex-arity takes)
(defun ex-varnf (ars)
  (cond ((atom ars) -1) ((truthy (nth 1 (car ars))) (nfix (nth 0 (car ars)))) (t (ex-varnf (cdr ars)))))

; ---- THE MACHINE: run_loop's turn for the core kinds -----------------------------------------
;
; a state (records val frame); a record (node pc i restart rnode tmp), tmp
; a recur's temporaries (the value-stack region exec_core opens)

(defun ex-rec (e pc i fl rs tmp) (list e pc i fl rs tmp))

; a throw in flight: a record of no kind, so the machine stops at it;
; unwinding it is k_unwind's (milestone 3)
(defun ex-throwr (v) (ex-rec (list :thrown v) 0 0 nil nil nil))


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
          (11 (ex-finish (ex-c e) ks fr))
          (12 (ex-finish (ex-mkclo (ex-c e) fr) ks fr))
          (13 (let ((h (ex-kid-of e j)))
                (if (ex-linked h)
                    (list (cons (ex-rec e pc2 i2 fl rs tmp) (cdr ks)) (ex-c h) fr)
                  (list (cons (ex-rec h 0 0 nil nil nil) (cons (ex-rec e pc2 i2 fl rs tmp) (cdr ks))) val fr))))
          (14 (list (cons (ex-rec e pc2 i2 fl rs (list val)) (cdr ks)) val fr))
          (15 (list (cons (ex-rec e pc2 i2 fl rs tmp) (cdr ks)) val fr))
          (16 (let* ((ct (ex-callee tmp)) (f (car ct)) (n (len (cdr ct))))
                (case (ex-entry (if (ex-clo-shape f) 1 0) (if (consp (ex-arity (nth 1 (cadr f)) n)) 1 0))
                  (1 (list (cons (ex-rec (ex-fbody f n) 0 0 t (ex-fbody f n) nil) (cons (ex-rec e pc2 i2 fl rs fr) (cdr ks)))
                           val (ex-bind f (cdr ct))))
                  (2 (list (cons (ex-throwr :arity) ks) val fr))
                  (otherwise (case (ex-apway tmp)
                               (2 (list (cons (ex-throwr :arity) ks) val fr))
                               (3 (list (cons (ex-throwr :not-seq) ks) val fr))
                               (otherwise s))))))
          (17 (ex-finish val ks tmp))
          (otherwise s))))))

(defun ex-step (s) (if (atom (car s)) s (ex-turn (car s) (cadr s) (caddr s))))

(defun ex-run (s n)
  (if (zp n) s (ex-run (ex-step s) (1- n))))

; ---- THE MEANING --------------------------------------------------------------------------------
;
; (ex-ev flg e i tmp fr fuel) is (res fr2 turns): what a record of e
; answers, the frame after, and how many turns it takes; res (:val . v),
; (:recur) for a recur that went back to its loop, (:thrown . v) for a
; throw -- a call of a closure with no arity of its count throws :arity,
; clj's ArityException, and a throw goes on out of every place, a part's
; throw its node's -- or (:out): fuel ran out, or something no core kind. The flags are the record's places:
;   :m     a fresh record of e
;   :do    a do's record at its i-th child
;   :let   a let's or loop's record at its i-th binding
;   :rec   a recur's record at its i-th argument, tmp the values so far
;   :iter  a loop's record at its body e, restarting at it (and a fn
;          body's, entered by a call)
;   :call  a call's record at its i-th argument, tmp the callee and the
;          arguments so far; past the last it enters the callee, whose
;          body takes fuel, as vmx's calls do, and answers in the
;          caller's frame
; a loop's iterations take fuel, as vmx's do.

(defun c+ (a b) (+ (nfix a) (nfix b)))

; a part that did not answer a value: a throw goes on, its turns and the
; one that pushed the part counted; anything else is out
(defun ex-thp (r) (eq (car r) :thrown))
(defmacro ex-nv (r fr)
  `(if (ex-thp (car ,r)) (list (car ,r) (cadr ,r) (c+ 1 (caddr ,r))) (list (list :out) ,fr 0)))

(defun ex-rank (flg) (case flg (:iter 2) ((:do :let :rec :call) 0) (otherwise 1)))

(defun ex-left (flg e i)
  (case flg
    (:let (nfix (- (ex-i2 e) (nfix i))))
    ((:do :rec :call) (nfix (- (ex-nk e) (nfix i))))
    (otherwise 0)))

(defthm ex-nth-count (<= (acl2-count (nth j l)) (acl2-count l)) :rule-classes :linear)
(defthm ex-nth-count-strict (implies (consp l) (< (acl2-count (nth j l)) (acl2-count l))) :rule-classes :linear)
(defthm ex-kid-count (implies (consp e) (< (acl2-count (ex-kid-of e j)) (acl2-count e))) :rule-classes :linear
  :hints (("Goal" :in-theory (disable ex-nth-count ex-nth-count-strict)
                  :use ((:instance ex-nth-count (l (nth 2 e))) (:instance ex-nth-count-strict (j 2) (l e))))))

; WELL FORMED, as the machine theorem assumes and a call asks of the body
; it enters: every node a modelled kind; an if 2 or 3 children; a let or
; loop its bindings' inits and its body; a call a head and its arguments;
; a recur only in a loop's or fn body's tail position (tl), as anpass's
; tail check passes it, with as many arguments as its target's slots; no
; constant nor Var's value the recur marker
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
           (:call (cond ((not (equal k 6)) nil)
                        ((< i nk) (and (ex-wf :m (ex-kid-of e i) 0 nil) (ex-wf :call e (1+ i) tl)))
                        (t t)))
           (otherwise
            (cond ((or (equal k 1) (equal k 3)) (not (equal (ex-c e) *ex-mk*)))
                  ((or (equal k 2) (equal k 14)) t)
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-wf :m (ex-kid-of e 0) 0 nil) (ex-wf :m (ex-kid-of e 1) 0 tl)
                                    (or (equal nk 2) (ex-wf :m (ex-kid-of e 2) 0 tl))))
                  ((equal k 5) (ex-wf :do e 0 tl))
                  ((or (equal k 11) (equal k 12)) (and (equal nk (1+ n2)) (ex-wf :let e 0 tl)))
                  ((equal k 16) (and tl (equal (ex-rn e) nk) (ex-wf :rec e 0 tl)))
                  ((equal k 6) (and (< 0 nk) (ex-wf :m (ex-kid-of e 0) 0 nil) (ex-wf :call e 1 tl)))
                  (t nil)))))))

; a call enters f with n arguments, in the meaning: a closure with that
; fixed arity, its body well formed and no capture the marker
(defun ex-enters (f n)
  (and (ex-callable f n) (no-mk (caddr f)) (ex-wf :iter (ex-fbody f n) 0 nil)))

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
                        (ex-nv r fr)
                      (let ((r2 (ex-ev :do e (1+ i) tmp (cadr r) fuel)))
                        (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (caddr r2))))))))
                 (t (let ((r (ex-ev :m (ex-kid-of e (- nk 1)) 0 nil fr fuel)))
                      (list (car r) (cadr r) (c+ 1 (caddr r)))))))
      (:let (cond ((not (consp e)) (list (list :out) fr 0))
                  ((< i n2)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (if (not (valp (car r)))
                         (ex-nv r fr)
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
                         (ex-nv r fr)
                       (let ((r2 (ex-ev :rec e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                  (t (list (list :recur) (ex-write (ex-rstart e) (take (min (ex-rn e) nk) tmp) fr) 1))))
      (:call (cond ((not (consp e)) (list (list :out) fr 0))
                   ((< i nk)
                    (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (if (not (valp (car r)))
                          (ex-nv r fr)
                        (let ((r2 (ex-ev :call e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel)))
                          (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                   ((and (ex-enters (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (not (zp fuel)))
                    (let ((rb (ex-ev :iter (ex-fbody (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) 0 nil
                                     (ex-bind (car (ex-callee tmp)) (cdr (ex-callee tmp))) (1- fuel))))
                      (list (car rb) fr (c+ 1 (c+ 1 (c+ (caddr rb) (if (ex-thp (car rb)) 0 1)))))))
                   ((ex-arerr (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (list (cons :thrown :arity) fr (c+ 1 1)))
                   ((equal (ex-apway tmp) 2) (list (cons :thrown :arity) fr (c+ 1 1)))
                   ((equal (ex-apway tmp) 3) (list (cons :thrown :not-seq) fr (c+ 1 1)))
                   (t (list (list :out) fr 0))))
      (otherwise
       (cond ((not (consp e)) (list (list :out) fr 0))
             ((equal k 1) (list (cons :val (ex-c e)) fr 1))
             ((equal k 2) (list (cons :val (nth n2 fr)) (if (ex-mark e) (update-nth n2 nil fr) fr) 1))
             ((equal k 4)
              (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                (cond ((not (valp (car r))) (ex-nv r fr))
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
             ((equal k 3) (list (cons :val (ex-c e)) fr 1))
             ((equal k 14) (list (cons :val (ex-mkclo (ex-c e) fr)) fr 1))
             ((equal k 6)
              (if (ex-linked (ex-kid-of e 0))
                  (let ((r2 (ex-ev :call e 1 (list (ex-c (ex-kid-of e 0))) fr fuel)))
                    (list (car r2) (cadr r2) (c+ 1 (c+ 1 (caddr r2)))))
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (if (not (valp (car r)))
                      (ex-nv r fr)
                    (let ((r2 (ex-ev :call e 1 (list (val (car r))) (cadr r) fuel)))
                      (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2))))))))))
             (t (list (list :out) fr 0)))))))

; THE TREE EVALUATOR'S CORE, its data (model/exec.lisp's, split from it for
; size): the tree as exec.inc reads it; throw and try's catch walk; case*'s
; table walk; the collections' and the host's builds.

(in-package "ACL2")

(include-book "seqk")
(include-book "vmx2")

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

;; THROW AND TRY. An N_THROW's child is the value thrown; an N_TRY's
; children its body and, when it has one, its finally (nk 1 or 2), slot 2
; its catches, each (class slot body) (analyze.inc anb_trynode). A catch's
; test is clj's instance? of its class -- the runtime's type system, so
; vmx2's prim (op :isa), whatever it answers (instance? throws nothing:
; exec-vm asks that of it) -- walked in order (k_unwind): (1 . j) clause j
; matched, (0) none did.
(defun ex-catchw (cs v j)
  (cond ((atom cs) (list 0))
        ((truthy (prim :isa (list (nth 0 (car cs)) v))) (cons 1 (nfix j)))
        (t (ex-catchw (cdr cs) v (1+ (nfix j))))))
(defun ex-cbody (e j) (nth 2 (nth j (ex-c e))))
(defun ex-cslot (e j) (nfix (nth 1 (nth j (ex-c e)))))

;; CASE (case*, exec-PLAN 3b). An N_CASE's children its test and its
; default (nk 2); slot 2 its table, read as data: each entry (test then),
; then the branch's node (analyze.inc anb_casenode). Which entry takes the
; test's value is the runtime's -- case_branch's hash probe (shift, mask,
; the int or hashCode key, a merged bucket's skip-check) and Util.equiv,
; vmx2's prim (op :case) of the entry's test and the value, whatever it
; answers -- walked in order: (1 . j) entry j took it, (0) none did. The
; macro's tests are distinct, so at most one entry takes a value and the
; walk's first is the probe's only one.
(defun ex-casew (ct v j)
  (cond ((atom ct) (list 0))
        ((truthy (prim :case (list (nth 0 (car ct)) v))) (cons 1 (nfix j)))
        (t (ex-casew (cdr ct) v (1+ (nfix j))))))
(defun ex-cthen (e j) (nth 1 (nth j (ex-c e))))
; the branch: the taken entry's then, else the default
(defun ex-csbr (e v)
  (let ((w (ex-casew (ex-c e) v 0))) (if (equal (car w) 1) (ex-cthen e (cdr w)) (ex-kid-of e 1))))

;; COLLECTIONS (N_VECTOR 7, N_MAP 8, N_SET 9, exec-PLAN 3b): children their
; elements (a map's keys and values in turn), each value kept in the
; record (exec.inc's slot 4), then the collection built of them. A vector
; is seqk's (:vec . elems), as B_APPLY reads one; a map's and a set's build
; is the runtime's (vec_to_map, vec_to_set), vmx2's prim (op :map or :set)
; of the values, whatever it answers -- a value, or a throw (clj's
; duplicate key)
;
; NEW (N_NEW 22, N_NEWTYPE 23, milestone 5): its arguments as a
; collection's elements, then the construction -- exec.inc's new_cached,
; eval_new or the deftype's constructor, the runtime's -- vmx2's prim of
; op (:host k C), C the class (the node's slot 2), a value or a throw
;
; THE HOST'S ACTIONS (N_DEF 10, N_DEFTYPE 20, N_SETBANG 24, milestone 5):
; the same -- the node's children run in turn as a collection's elements,
; then the host's action on their values (exec.inc's def_finish: the
; Var's root and metadata; deftype_finish: the type of its methods'
; closures; setbang_finish: the Var's binding or the field), vmx2's prim
; of op (:host k C), C the node's operand. A def's children are its init
; (when it has one) and then its metadata (when evaluated), as clj's
; DefExpr runs them; a deftype's its methods' fns; a set!'s its target
; (when a field's) and its value. What the action does to the namespace,
; the type registry or the field is the runtime's: a named hypothesis
; (exec-vm's ex-collok), not a theorem. A `.` (N_DOT 21) the same: its
; children (its target when evaluated, then its arguments) kept, then the
; host's dispatch on their values (exec.inc dot_finish) -- what the member
; does, a deftype's method entered in the loop or a yield re-dispatching,
; the runtime's. A hinted target's cast (DEVIATIONS 84) is no action of its
; own: the analyzer makes the target child (clotran-class-cast target C),
; an ordinary call, so it runs before the arguments as clj's checkcast.
(defun ex-cop (e) (case (ex-kind e) (7 :vector) (8 :map) (9 :set) (otherwise (list :host (ex-kind e) (ex-c e)))))
(defun ex-cbuild (e vals)
  (if (equal (ex-kind e) 7)
      (cons :val (cons :vec vals))
    (let ((a (prim (ex-cop e) vals))) (if (throwp a) (cons :thrown (cdr a)) (cons :val a)))))


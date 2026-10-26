; THE ANALYZER'S PASSES OVER ITS TREE (src/f/analyze.inc): what runs on a
; fn body once the analyzer has built it -- the TAIL CHECK (every recur in
; tail position of its own target, none across a try) and LOCALS CLEARING
; (each local nil-ed at its last read, as Clojure's compiler does) -- at the
; level the Fortran is GENERATED from (src/f/gen/anpass_gen.inc,
; scripts/acl2-fortran -b anpass), guard-verified.
;
; THE TREE is the analyzer's (analyze.inc's header): a node has a kind (the
; N_* of Eval.f90), an integer operand i2, its children, and payloads. The
; passes read it through ten host reads, each a thin hand-written shim in
; analyze.inc on the OBJ_AST object: ast-kind (i1, 0 for no node),
; ast-i2, ast-nkids / ast-kid (the children vector), ast-s3 (slot 3, a
; def's metadata node), ast-ncaps / ast-cap (a fn's capture pairs, the
; outer slot of each), ast-nalts / ast-alt (a case's branch bodies, a try's
; catch bodies, a deftype's method fns, by kind) and ast-rfn (a recur's
; target: nonzero the fn). Here a node is the list (:ast id kind i2 kids s3
; caps alts rfn) those reads decode it to; nothing else is read.
;
; THE PASSES, each hand-written in analyze.inc before and generated now:
;   anp-tc      the tail check: 0, or 1 "Can only recur from tail position",
;               2 "Cannot recur across try" -- as clj's compiler refuses them
;   anp-hfr     has_fn_recur: a recur to the fn under the body
;   anp-rd      reads_in: every slot read under a node, into a live set
;   anp-live    liveness: backwards, the live set after each node, marking
;               each read of a slot not live after it -- its last read
;   anp-clears  apply_clears: no clearing in a body that recurs to its fn
; A live set is a region of n words of one array (anp-lv): an alternative's
; set a copy above the current one, merged back by an or. The marked reads
; are left in anp-mk, the shim sets their slot 3 for exec.inc.
;
; THE MEANING, in the books that prove things of these definitions:
; model/anpass-proof.lisp's sp-out and sp-mk, the same passes on live sets
; as lists; model/anpass-runs.lisp's tr, the reads a node makes as exec.inc
; runs it -- an if's test then one branch, a case's test then one branch, a
; try's body (or a prefix of it, a catch and) its finally, a loop's inits
; then its body again while it ends in its recur, letfn's fns then their
; captures copied again, a def's init then its metadata, anything else its
; children in order -- each read annotated with the clearing decision; and
; fn-tr, a fn body run again for each recur to the fn.
;
; Theorems:
;   anp-live-spec, anp-clears-spec (anpass-proof)  the generated pass
;              computes sp-out and sp-mk when it ends with no error (a region
;              full: the shim grows the arrays and runs it again)
;   tr-sound (anpass-sound)  no read annotated for clearing is followed, in
;              any run, by another read of its slot, nor is the slot live
;              after the node
;   anp-clears-sound  so a fn body's clearing is sound for every run of it,
;              the recurs to the fn included
;   tr-tail    a body the tail check passes makes a recur only as the very
;              last thing it does, to its own target, never across a try:
;              exec.inc's restart loses nothing
;   anp-*-steps-* (anpass-cost)  the step counts: the tail check, has_fn_recur
;              and reads_in linear in the nodes they visit, liveness 2n + 1
;              steps for each of a walk of 3 a node, a node counted once more
;              for every loop it sits in

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defconst *anp40* 1099511627776)

(defmacro anp40p (x) `(and (natp ,x) (< ,x *anp40*)))

; ---- THE TREE ------------------------------------------------------------------------------

(defun anp-fix (v) (declare (xargs :guard t)) (if (signed-byte-p 64 v) v 0))

(defun anp-nth (i l)
  (declare (xargs :guard t))
  (if (and (natp i) (consp l)) (if (equal i 0) (car l) (anp-nth (- i 1) (cdr l))) nil))

(defun anp-len (l) (declare (xargs :guard t)) (if (consp l) (+ 1 (anp-len (cdr l))) 0))

(defun anp-sat (k) (declare (xargs :guard (natp k))) (if (< k *anp40*) k (- *anp40* 1)))

; a node: (:ast id kind i2 kids s3 caps alts rfn), its kind a nonzero integer
(defun ast-p (x)
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) :ast) (signed-byte-p 64 (anp-nth 2 x)) (not (equal (anp-nth 2 x) 0))))

(defun ast-kind (x) (declare (xargs :guard t)) (if (ast-p x) (anp-nth 2 x) 0))
(defun ast-i2 (x) (declare (xargs :guard t)) (if (ast-p x) (anp-fix (anp-nth 3 x)) 0))
(defun ast-nkids (x) (declare (xargs :guard t)) (if (ast-p x) (anp-sat (anp-len (anp-nth 4 x))) 0))
(defun ast-kid (x i) (declare (xargs :guard t)) (if (and (ast-p x) (natp i) (< i (ast-nkids x))) (anp-nth i (anp-nth 4 x)) nil))
(defun ast-s3 (x) (declare (xargs :guard t)) (if (ast-p x) (anp-nth 5 x) nil))
(defun ast-ncaps (x) (declare (xargs :guard t)) (if (ast-p x) (anp-sat (anp-len (anp-nth 6 x))) 0))
(defun ast-cap (x i) (declare (xargs :guard t)) (if (and (ast-p x) (natp i) (< i (ast-ncaps x))) (anp-fix (anp-nth i (anp-nth 6 x))) 0))
(defun ast-nalts (x) (declare (xargs :guard t)) (if (ast-p x) (anp-sat (anp-len (anp-nth 7 x))) 0))
(defun ast-alt (x i) (declare (xargs :guard t)) (if (and (ast-p x) (natp i) (< i (ast-nalts x))) (anp-nth i (anp-nth 7 x)) nil))
(defun ast-rfn (x) (declare (xargs :guard t)) (if (ast-p x) (anp-fix (anp-nth 8 x)) 0))

(defthm anp-nth-count (<= (acl2-count (anp-nth i l)) (acl2-count l)) :rule-classes :linear)

(defthm ast-p-count
  (implies (ast-p x)
           (and (< (acl2-count (ast-kid x i)) (acl2-count x))
                (< (acl2-count (ast-s3 x)) (acl2-count x))
                (< (acl2-count (ast-alt x i)) (acl2-count x))))
  :hints (("Goal" :in-theory (enable anp-nth)
           :use ((:instance anp-nth-count (l (anp-nth 4 x)))
                 (:instance anp-nth-count (l (anp-nth 7 x)))
                 (:instance anp-nth-count (i 4) (l x))
                 (:instance anp-nth-count (i 5) (l x))
                 (:instance anp-nth-count (i 7) (l x))
                 (:instance anp-nth-count (i 3) (l (cdr x)))
                 (:instance anp-nth-count (i 4) (l (cdr x)))
                 (:instance anp-nth-count (i 6) (l (cdr x))))))
  :rule-classes :linear)

(defthm ast-kind-ast-p (equal (equal (ast-kind x) 0) (not (ast-p x))))

(defthm ast-reads-sb64
  (and (signed-byte-p 64 (ast-kind x)) (signed-byte-p 64 (ast-i2 x)) (anp40p (ast-nkids x))
       (anp40p (ast-ncaps x)) (signed-byte-p 64 (ast-cap x i)) (anp40p (ast-nalts x))
       (signed-byte-p 64 (ast-rfn x))))

(defthm ast-reads-int
  (and (integerp (ast-kind x)) (integerp (ast-i2 x)) (natp (ast-nkids x)) (natp (ast-ncaps x))
       (integerp (ast-cap x i)) (natp (ast-nalts x)) (integerp (ast-rfn x)))
  :rule-classes ((:type-prescription :corollary (integerp (ast-kind x)))
                 (:type-prescription :corollary (integerp (ast-i2 x)))
                 (:type-prescription :corollary (natp (ast-nkids x)))
                 (:type-prescription :corollary (natp (ast-ncaps x)))
                 (:type-prescription :corollary (integerp (ast-cap x i)))
                 (:type-prescription :corollary (natp (ast-nalts x)))
                 (:type-prescription :corollary (integerp (ast-rfn x)))))


(defthm ast-kind-count
  (implies (not (equal (ast-kind x) 0))
           (and (< (acl2-count (ast-kid x i)) (acl2-count x))
                (< (acl2-count (ast-s3 x)) (acl2-count x))
                (< (acl2-count (ast-alt x i)) (acl2-count x))))
  :hints (("Goal" :in-theory (enable ast-kind)))
  :rule-classes :linear)

(in-theory (disable ast-p ast-kind ast-i2 ast-nkids ast-kid ast-s3 ast-ncaps ast-cap ast-nalts ast-alt ast-rfn))

; how many inits a let, loop or letfn has: i2, but no more than its
; children (those past them are no nodes; this keeps every walk linear in
; the tree)
(defthm ast-i2-bounds (and (<= -9223372036854775808 (ast-i2 x)) (< (ast-i2 x) 9223372036854775808))
  :hints (("Goal" :in-theory (enable ast-i2 anp-fix))) :rule-classes :linear)

(defun anp-nn (x)
  (declare (xargs :guard t))
  (let ((nn (ast-i2 x)) (m (ast-nkids x))) (if (< nn m) nn m)))

(defthm anp-nn-sb64 (and (signed-byte-p 64 (anp-nn x)) (integerp (anp-nn x)) (<= (anp-nn x) (ast-nkids x)))
  :hints (("Goal" :use ((:instance ast-reads-sb64 (i 0)))))
  :rule-classes ((:rewrite) (:type-prescription :corollary (integerp (anp-nn x)))
                 (:linear :corollary (<= (anp-nn x) (ast-nkids x)))))
(in-theory (disable anp-nn))

; the children a sequence walks: fl 3 the alternatives, else the children
(defun anp-ch (fl x i)
  (declare (xargs :guard t))
  (if (equal fl 3) (ast-alt x i) (ast-kid x i)))

(defthm anp-ch-count (implies (not (equal (ast-kind x) 0)) (< (acl2-count (anp-ch fl x i)) (acl2-count x))) :rule-classes :linear)

; the node kinds (Eval.f90's N_*)
(defconst *n-const* 1) (defconst *n-local* 2) (defconst *n-var* 3) (defconst *n-if* 4) (defconst *n-do* 5)
(defconst *n-def* 10) (defconst *n-let* 11) (defconst *n-loop* 12) (defconst *n-letfn* 13) (defconst *n-fn* 14)
(defconst *n-lazy* 15) (defconst *n-recur* 16) (defconst *n-try* 18) (defconst *n-case* 19) (defconst *n-deftype* 20)

; THE MEASURE every pass shares: a node above the sequences of its own
; children, which are above their elements; a loop's iterations (the
; meaning's) above the body they run
(defun anp-meas (fl x j m os)
  (declare (xargs :guard t))
  (make-ord 2 (+ 1 (acl2-count x))
            (cond ((equal fl 0) (make-ord 1 3 0))
                  (t (make-ord 1 (if (equal fl 4) 4 2) (+ (acl2-count os) (nfix (- (nfix m) (nfix j)))))))))

(defthm anp-meas-o-p (o-p (anp-meas fl x j m os)))

; ---- THE TAIL CHECK ------------------------------------------------------------------------
;
; tt says where the node stands: 0 not in tail position, 1 in tail position
; of the fn, 2 of a loop, 3 in tail position but inside a try's body. A recur
; is refused in 0 (1, "Can only recur from tail position"), in 3 (2, "Cannot
; recur across try"), and where its target is not the one it stands in tail
; position of. As clj's compiler parses: a test, an init, an argument, a
; catch, a finally are expressions; an if's branches, a do's last form, a
; let's, a letfn's and a case's bodies keep the context; a loop's body is
; the loop's; a try's body keeps it but recurs across nothing. A fn, a lazy
; seq and a deftype's methods have bodies of their own, checked when the
; analyzer makes them. The first refusal in evaluation order is answered.

; the tail check of one node (fl 0): a macro, so that the proofs' opener says the same
(defmacro anp-tc-node ()
  (quote
      (let ((k (ast-kind x)))
        (cond ((equal k *n-recur*)
               (cond ((equal tt 0) 1)
                     ((equal tt 3) 2)
                     ((and (equal tt 1) (equal (ast-rfn x) 0)) 1)
                     ((and (equal tt 2) (not (equal (ast-rfn x) 0))) 1)
                     (t (anp-tc 1 x 0 (ast-nkids x) 0))))
              ((equal k *n-if*)
               (let ((a (anp-tc 0 (ast-kid x 0) 0 0 0)))
                 (if (equal a 0)
                     (let ((b (anp-tc 0 (ast-kid x 1) 0 0 tt)))
                       (if (equal b 0) (anp-tc 0 (ast-kid x 2) 0 0 tt) b))
                   a)))
              ((or (equal k *n-do*) (equal k *n-let*))
               ; a let's body is its last child, as a do's last form
               (let ((m2 (ast-nkids x)))
                 (if (equal m2 0) 0
                   (let ((a (anp-tc 1 x 0 (- m2 1) 0)))
                     (if (equal a 0) (anp-tc 0 (ast-kid x (- m2 1)) 0 0 tt) a)))))
              ((or (equal k *n-letfn*) (equal k *n-loop*))
               (let* ((nn (anp-nn x)) (a (anp-tc 1 x 0 nn 0)))
                 (if (equal a 0) (anp-tc 0 (ast-kid x nn) 0 0 (if (equal k *n-loop*) 2 tt)) a)))
              ((equal k *n-case*)
               (let ((a (anp-tc 0 (ast-kid x 0) 0 0 0)))
                 (if (equal a 0)
                     (let ((b (anp-tc 0 (ast-kid x 1) 0 0 tt)))
                       (if (equal b 0) (anp-tc 3 x 0 (ast-nalts x) tt) b))
                   a)))
              ((equal k *n-try*)
               (let ((a (anp-tc 0 (ast-kid x 0) 0 0 (if (equal tt 0) 0 3))))
                 (if (equal a 0)
                     (let ((b (anp-tc 3 x 0 (ast-nalts x) 0)))
                       (if (equal b 0) (anp-tc 0 (ast-kid x 1) 0 0 0) b))
                   a)))
              ((equal k *n-def*)
               (let ((a (anp-tc 1 x 0 (ast-nkids x) 0)))
                 (if (equal a 0) (anp-tc 0 (ast-s3 x) 0 0 0) a)))
              ; a deftype's methods are fns: nothing to look into but they
              ((equal k *n-deftype*) (anp-tc 3 x 0 (ast-nalts x) 0))
              ((or (equal k 0) (equal k *n-local*) (equal k *n-const*) (equal k *n-var*)
                   (equal k *n-fn*) (equal k *n-lazy*))
               0)
              (t (anp-tc 1 x 0 (ast-nkids x) 0))))
))

(defun anp-tc (fl x j m tt)
  (declare (xargs :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m)
                              (signed-byte-p 64 tt))
                  :measure (anp-meas fl x j m nil)
                  :verify-guards nil))
  (if (equal fl 0)
      (anp-tc-node)
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (let ((a (anp-tc 0 (anp-ch fl x j) 0 0 tt)))
          (if (equal a 0) (anp-tc fl x (+ 1 j) m tt) a))
      0)))

; ---- A RECUR TO THE FN ---------------------------------------------------------------------
;
; has_fn_recur: a recur to the fn under the node, nested fns excluded. A
; recur's arguments are looked into too, which the hand-written pass did not:
; under the tail check they hold no recur, so the answer is the same, and the
; meaning below needs no tail check to be sound.

; has_fn_recur of one node (fl 0)
(defmacro anp-hfr-node ()
  (quote
      (let ((k (ast-kind x)))
        (cond ((equal k *n-recur*) (if (equal (ast-rfn x) 0) (anp-hfr 1 x 0 (ast-nkids x)) t))
              ((equal k *n-try*)
               (if (anp-hfr 0 (ast-kid x 0) 0 0) t
                 (if (anp-hfr 3 x 0 (ast-nalts x)) t (anp-hfr 0 (ast-kid x 1) 0 0))))
              ((equal k *n-case*) (if (anp-hfr 3 x 0 (ast-nalts x)) t (anp-hfr 1 x 0 (ast-nkids x))))
              ((equal k *n-def*) (if (anp-hfr 0 (ast-s3 x) 0 0) t (anp-hfr 1 x 0 (ast-nkids x))))
              ((equal k *n-deftype*) (anp-hfr 3 x 0 (ast-nalts x)))
              ((or (equal k 0) (equal k *n-local*) (equal k *n-const*) (equal k *n-var*)
                   (equal k *n-fn*) (equal k *n-lazy*))
               nil)
              (t (anp-hfr 1 x 0 (ast-nkids x)))))
))

(defun anp-hfr (fl x j m)
  (declare (xargs :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m))
                  :measure (anp-meas fl x j m nil)
                  :verify-guards nil))
  (if (equal fl 0)
      (anp-hfr-node)
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (if (anp-hfr 0 (anp-ch fl x j) 0 0) t (anp-hfr fl x (+ 1 j) m))
      nil)))

(verify-guards anp-tc)
(verify-guards anp-hfr)

; ---- THE LIVE SETS: regions of one array ---------------------------------------------------
;
; anp-lv holds the live sets, n words each, a word nonzero when its slot is
; read later; anp-mk the marked reads, anp-nmk of them; anp-err nonzero when
; a region or the marks ran past their arrays. A write past an array writes
; nothing and sets anp-err; a read past one answers 0.

(defstobj anps
  (anp-lv :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (anp-mk :type (array t (0)) :initially nil :resizable t)
  (anp-nmk :type (signed-byte 64) :initially 0)
  (anp-err :type (signed-byte 64) :initially 0))

(defthm anp-lvp-nth
  (implies (and (anp-lvp l) (natp i) (< i (len l)))
           (and (integerp (nth i l)) (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808))))

(defun anp-get (i anps)
  (declare (xargs :stobjs anps :guard (signed-byte-p 64 i)))
  (if (and (integerp i) (<= 0 i) (< i (anp-lv-length anps))) (anp-lvi i anps) 0))

(defthm anp-get-sb64 (implies (anpsp anps) (signed-byte-p 64 (anp-get i anps))))
(defthm anp-get-int (implies (anpsp anps) (integerp (anp-get i anps))) :rule-classes :type-prescription)

(defun anp-put (i v anps)
  (declare (xargs :stobjs anps :guard (and (signed-byte-p 64 i) (signed-byte-p 64 v))))
  (if (and (integerp i) (<= 0 i) (< i (anp-lv-length anps))) (update-anp-lvi i v anps) (update-anp-err 1 anps)))

; region to := region from, words k .. n-1
(defun anp-copy (k n from to anps)
  (declare (xargs :stobjs anps :measure (nfix (- (nfix n) (nfix k)))
                  :guard (and (anp40p k) (anp40p n) (anp40p from) (anp40p to))))
  (if (and (natp k) (natp n) (< k n))
      (let ((anps (anp-put (+ to k) (anp-get (+ from k) anps) anps))) (anp-copy (+ 1 k) n from to anps))
    anps))

; region to := region from or region to
(defun anp-or (k n from to anps)
  (declare (xargs :stobjs anps :measure (nfix (- (nfix n) (nfix k)))
                  :guard (and (anp40p k) (anp40p n) (anp40p from) (anp40p to))))
  (if (and (natp k) (natp n) (< k n))
      (let ((anps (anp-put (+ to k) (if (equal (anp-get (+ from k) anps) 0) (anp-get (+ to k) anps) 1) anps)))
        (anp-or (+ 1 k) n from to anps))
    anps))

(defun anp-zero (k n anps)
  (declare (xargs :stobjs anps :measure (nfix (- (nfix n) (nfix k))) :guard (and (anp40p k) (anp40p n))))
  (if (and (natp k) (natp n) (< k n)) (let ((anps (anp-put k 0 anps))) (anp-zero (+ 1 k) n anps)) anps))

; slot s live in the region at b
(defun anp-set (s b n anps)
  (declare (xargs :stobjs anps :guard (and (signed-byte-p 64 s) (anp40p b) (anp40p n))))
  (if (and (integerp s) (<= 0 s) (< s n)) (anp-put (+ b s) 1 anps) anps))

(defun anp-mark (x anps)
  (declare (xargs :stobjs anps))
  (let ((k (anp-nmk anps)))
    (if (and (integerp k) (<= 0 k) (< k (anp-mk-length anps)) (< k *anp40*))
        (let ((anps (update-anp-mki k x anps))) (update-anp-nmk (+ 1 k) anps))
      (update-anp-err 1 anps))))

; a read of slot s: the clearing read when s is not live after it
(defun anp-local (x b n anps)
  (declare (xargs :stobjs anps :guard (and (anp40p b) (anp40p n))))
  (let ((s (ast-i2 x)))
    (if (and (integerp s) (<= 0 s) (< s n))
        (let ((anps (if (equal (anp-get (+ b s) anps) 0) (anp-mark x anps) anps)))
          (anp-put (+ b s) 1 anps))
      anps)))

; a fn's captures i .. k-1, read when the closure is made
(defun anp-caps (x i k b n anps)
  (declare (xargs :stobjs anps :measure (nfix (- (nfix k) (nfix i)))
                  :guard (and (anp40p i) (anp40p k) (anp40p b) (anp40p n))))
  (if (and (natp i) (natp k) (< i k)) (let ((anps (anp-set (ast-cap x i) b n anps))) (anp-caps x (+ 1 i) k b n anps)) anps))

; letfn's fns i .. k-1: their captures, copied again once all are made
(defun anp-fncaps (x i k b n anps)
  (declare (xargs :stobjs anps :measure (nfix (- (ifix k) (nfix i)))
                  :guard (and (natp i) (signed-byte-p 64 i) (signed-byte-p 64 k) (anp40p b) (anp40p n))))
  (if (and (natp i) (integerp k) (< i k))
      (let* ((c (ast-kid x i)) (anps (anp-caps c 0 (ast-ncaps c) b n anps))) (anp-fncaps x (+ 1 i) k b n anps))
    anps))

; ---- READS_IN --------------------------------------------------------------------------------
;
; every slot read under the node into the region at b, nested fns but their
; captures excluded: fl 0 the node, 1 its children j .. m-1, 3 its
; alternatives j .. m-1

(defun anp-rd (fl x j m b n anps)
  (declare (xargs :stobjs anps :measure (anp-meas fl x j m nil) :verify-guards nil
                  :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m)
                              (anp40p b) (anp40p n))))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k 0) anps)
              ((equal k *n-local*) (anp-set (ast-i2 x) b n anps))
              ((or (equal k *n-fn*) (equal k *n-lazy*)) (anp-caps x 0 (ast-ncaps x) b n anps))
              ((equal k *n-deftype*) (anp-rd 3 x 0 (ast-nalts x) b n anps))
              ((equal k *n-try*)
               (let* ((anps (anp-rd 0 (ast-kid x 0) 0 0 b n anps))
                      (anps (anp-rd 3 x 0 (ast-nalts x) b n anps)))
                 (anp-rd 0 (ast-kid x 1) 0 0 b n anps)))
              ((equal k *n-case*)
               (let* ((anps (anp-rd 0 (ast-kid x 0) 0 0 b n anps))
                      (anps (anp-rd 0 (ast-kid x 1) 0 0 b n anps)))
                 (anp-rd 3 x 0 (ast-nalts x) b n anps)))
              ((equal k *n-def*)
               (let ((anps (anp-rd 0 (ast-s3 x) 0 0 b n anps))) (anp-rd 1 x 0 (ast-nkids x) b n anps)))
              (t (anp-rd 1 x 0 (ast-nkids x) b n anps))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (let ((anps (anp-rd 0 (anp-ch fl x j) 0 0 b n anps))) (anp-rd fl x (+ 1 j) m b n anps))
      anps)))

; ---- LIVENESS --------------------------------------------------------------------------------
;
; backwards: on entry the region at b is the live set after the node, on
; exit before it; regions from top up are free. fl 0 the node; 1 its
; children j .. m-1 and 3 its alternatives, the last first; 2 its
; alternatives j .. m-1 each from the region at b, or-ed into the region at
; top (its scratch at top + n).

(defun anp-live (fl x j m b top n anps)
  (declare (xargs :stobjs anps :measure (anp-meas fl x j m nil) :verify-guards nil
                  :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m)
                              (anp40p b) (anp40p top) (anp40p n))))
  (cond
   ((not (equal (anp-err anps) 0)) anps)
   ((equal fl 0)
    (let ((k (ast-kind x)))
      (cond
       ((equal k 0) anps)
       ((equal k *n-local*) (anp-local x b n anps))
       ((or (equal k *n-fn*) (equal k *n-lazy*)) (anp-caps x 0 (ast-ncaps x) b n anps))
       ((equal k *n-deftype*) (anp-live 3 x 0 (ast-nalts x) b top n anps))
       ((or (equal k *n-if*) (equal k *n-case*) (equal k *n-try*))
        (if (< (+ top (* 3 n)) *anp40*)
            (cond
             ((equal k *n-if*)
              ; the then branch on a copy, the else in place, or-ed
              (let* ((anps (anp-copy 0 n b top anps))
                     (anps (anp-live 0 (ast-kid x 1) 0 0 top (+ top n) n anps))
                     (anps (anp-live 0 (ast-kid x 2) 0 0 b (+ top n) n anps))
                     (anps (anp-or 0 n top b anps)))
                (anp-live 0 (ast-kid x 0) 0 0 b top n anps)))
             ((equal k *n-case*)
              ; the branches or-ed into a copy, the default in place, or-ed
              (let* ((anps (anp-copy 0 n b top anps))
                     (anps (anp-live 2 x 0 (ast-nalts x) b top n anps))
                     (anps (anp-live 0 (ast-kid x 1) 0 0 b (+ top n) n anps))
                     (anps (anp-or 0 n top b anps)))
                (anp-live 0 (ast-kid x 0) 0 0 b top n anps)))
             (t
              ; the finally in place; a catch can follow any point of the body
              (let* ((anps (anp-live 0 (ast-kid x 1) 0 0 b top n anps))
                     (anps (anp-copy 0 n b top anps))
                     (anps (anp-live 2 x 0 (ast-nalts x) b top n anps))
                     (anps (anp-copy 0 n top b anps)))
                (anp-live 0 (ast-kid x 0) 0 0 b top n anps))))
          (update-anp-err 1 anps)))
       ((equal k *n-loop*)
        ; every slot the body reads is live throughout it: it runs again
        (let* ((nn (anp-nn x)) (bd (ast-kid x nn))
               (anps (anp-rd 0 bd 0 0 b n anps))
               (anps (anp-live 0 bd 0 0 b top n anps)))
          (anp-live 1 x 0 nn b top n anps)))
       ((equal k *n-letfn*)
        (let* ((nn (anp-nn x))
               (anps (anp-live 0 (ast-kid x nn) 0 0 b top n anps))
               (anps (anp-fncaps x 0 nn b n anps)))
          (anp-live 1 x 0 nn b top n anps)))
       ((equal k *n-def*)
        (let ((anps (anp-live 0 (ast-s3 x) 0 0 b top n anps))) (anp-live 1 x 0 (ast-nkids x) b top n anps)))
       (t (anp-live 1 x 0 (ast-nkids x) b top n anps)))))
   ((equal fl 2)
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (if (< (+ top (* 3 n)) *anp40*)
            (let* ((anps (anp-copy 0 n b (+ top n) anps))
                   (anps (anp-live 0 (ast-alt x j) 0 0 (+ top n) (+ top (* 2 n)) n anps))
                   (anps (anp-or 0 n (+ top n) top anps)))
              (anp-live 2 x (+ 1 j) m b top n anps))
          (update-anp-err 1 anps))
      anps))
   (t
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (let ((anps (anp-live 0 (anp-ch fl x (- m 1)) 0 0 b top n anps))) (anp-live fl x j (- m 1) b top n anps))
      anps))))

; apply_clears: a body of n slots, its live set at 0, the regions above it
; free. A body that recurs to its fn runs again with its captures as they
; were, so it is left uncleared.
(defun anp-clears (x n anps)
  (declare (xargs :stobjs anps :guard (anp40p n) :verify-guards nil))
  (let* ((anps (update-anp-err 0 anps))
         (anps (update-anp-nmk 0 anps)))
    (cond ((anp-hfr 0 x 0 0) anps)
          ((< (anp-lv-length anps) n) (update-anp-err 1 anps))
          (t (let ((anps (anp-zero 0 n anps))) (anp-live 0 x 0 0 0 n n anps))))))

(verify-guards anp-rd)
(verify-guards anp-live)
(verify-guards anp-clears)

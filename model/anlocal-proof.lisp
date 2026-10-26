; THE ANALYZER'S LOCALS, PROVED (model/anlocal.lisp's generated functions).
;
; WHAT A NAME MEANS. anl-lex is the lexical meaning of name s in block b:
; the newest binding of s in b, else in the block around it, ... up to the
; fn's root block, then on in the block the fn is written in -- crossing
; fns, ignoring captures. A binding is its record's index, so two
; bindings of one name are told apart.
;
; THE INVARIANT. anl-ccc b: each capture of b's fn, and of every fn around
; it, is of the binding its name means where that fn is written. anl-wf:
; every block's newest binding and every fn's newest capture is a record,
; every block's fn a fn.
;
; THE THEOREMS, for anl-lookup, the analyzer's lookup_local, in any state it
; leaves without its error flag set:
;   anl-lookup-lex        it answers the binding anl-lex means: every local
;                         reference resolves to the innermost binding in scope
;   anl-lookup-ccc        it keeps the invariant at b (anl-lookup-ccc-any: at
;                         every block), the captures it makes being of what
;                         their names mean; anl-bind-ccc, anl-child-ccc,
;                         anl-new-fn-ccc, anl-reserve-ccc: so do the
;                         analyzer's other operations at the block it is in --
;                         binding a name there, a block nested in it, a fn
;                         written in it, slots reserved -- and every one keeps
;                         anl-wf (anl-*-wf)
;   anl-lookup-caps-own   what it adds to b's own fn's captures: the name,
;                         exactly when no block of the fn from b out binds it,
;                         the fn has not captured it, and it is bound outside
;                         -- a free local of the fn, used; nothing otherwise
;   anl-lookup-caps-any   to any fn: that name, not there before, or nothing;
;                         anl-lookup-caps-nodup: no fn captures a name twice
; So a fn's captures are exactly the free locals used in it and in the fns
; inside it, each once. The checks are in anlocal-checks.lisp, the step
; counts in anlocal-cost.lisp, the reads through the writes they stand on in
; anlocal-frames.lisp.
;
; Assumed, not proved: the host reads (frm-*) answer what they decode to,
; and a symbol's id names it alone (anl_sym_id, one per text). Not here:
; that the slot a lookup answers holds the binding's value when the code
; runs -- the captures copied into a closure's frame -- which is the tree
; evaluator's (exec.inc) to prove, against the VM model.

(in-package "ACL2")

(include-book "anlocal-frames")

; ---- WHAT A NAME MEANS ---------------------------------------------------------------------

; the newest binding of name s in block b's chain of blocks, then in the
; block its fn is written in, on out: crossing fns, ignoring captures
(defun anl-lex (b s anls)
  (declare (xargs :stobjs anls :measure (nfix b) :verify-guards nil))
  (let ((x (anl-chain-find b s anls)))
    (if (<= 0 x) x
      (let* ((f (anl-g-bfn b anls)) (o (anl-g-fout f anls)))
        (if (and (natp b) (natp o) (< o b) (< (anl-g-bfn o anls) f)) (anl-lex o s anls) -1)))))

(defthm anl-lex-range
  (implies (anlsp anls)
           (or (equal (anl-lex b s anls) -1) (natp (anl-lex b s anls))))
  :rule-classes nil)

(defthm anl-lex-int (implies (anlsp anls) (integerp (anl-lex b s anls)))
  :hints (("Goal" :use anl-lex-range)))

(defthm anl-lex-neg (implies (and (anlsp anls) (< (anl-lex b s anls) 0)) (equal (anl-lex b s anls) -1))
  :hints (("Goal" :use anl-lex-range)))

; every capture in the list from c is of a binding, the one its name means
; in block o
(defun anl-cc-caps (c o anls)
  (declare (xargs :stobjs anls :measure (nfix c) :verify-guards nil))
  (if (and (natp c) (< c (anl-nc anls)))
      (and (<= 0 (anl-g-cbx c anls))
           (equal (anl-g-cbx c anls) (anl-lex o (anl-g-cnm c anls) anls))
           (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (anl-cc-caps j o anls) t)))
    t))

; THE INVARIANT: so for the captures of block b's fn, and of each fn around it
(defun anl-ccc (b anls)
  (declare (xargs :stobjs anls :measure (nfix b) :verify-guards nil))
  (let* ((f (anl-g-bfn b anls)) (o (anl-g-fout f anls)))
    (if (and (natp b) (natp o) (< o b) (< (anl-g-bfn o anls) f))
        (and (anl-cc-caps (anl-g-fcap f anls) o anls) (anl-ccc o anls))
      t)))

(defthm anl-cfind-cc
  (implies (and (anl-cc-caps c o anls) (<= 0 (anl-cfind c s anls)))
           (and (equal (anl-g-cbx (anl-cfind c s anls) anls) (anl-lex o s anls))
                (<= 0 (anl-g-cbx (anl-cfind c s anls) anls))))
  :hints (("Goal" :in-theory (enable anl-cfind))))

; the error flag, once set, stays set
(defthm anl-push-n-err
  (implies (not (equal (anl-err anls) 0)) (not (equal (anl-err (anl-push-n f s k anls)) 0)))
  :hints (("Goal" :in-theory (enable anl-push-n))))

(defthm anl-push-c-err
  (implies (not (equal (anl-err anls) 0)) (not (equal (anl-err (anl-push-c f s k slot bx anls)) 0)))
  :hints (("Goal" :in-theory (enable anl-push-c))))

(defthm anl-lookup-err
  (implies (not (equal (anl-err anls) 0)) (not (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0)))
  :hints (("Goal" :induct (anl-lookup b s anls) :in-theory (disable anl-push-c))))

; RESOLUTION: the binding anl-lookup answers is the one the name means
(defthm anl-lookup-lex
  (implies (and (anlsp anls) (anl-ccc b anls) (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0))
           (equal (mv-nth 1 (anl-lookup b s anls)) (anl-lex b s anls)))
  :hints (("Goal" :induct (anl-lookup b s anls) :in-theory (disable anl-push-c))))

; ---- THE HEADS ARE RECORDS ------------------------------------------------------------------
;
; anl-wf: every block's newest binding is a binding (or none), every fn's
; newest capture a capture (or none). What every operation keeps, and what
; makes an operation that adds a record unable to change an old list.

(defun anl-wf-b (i anls)
  (declare (xargs :stobjs anls :measure (nfix i) :verify-guards nil))
  (if (zp i) t
    (and (< (anl-g-bhead (- i 1) anls) (anl-nx anls)) (< (anl-g-bfn (- i 1) anls) (anl-nf anls))
         (anl-wf-b (- i 1) anls))))

(defun anl-wf-f (i anls)
  (declare (xargs :stobjs anls :measure (nfix i) :verify-guards nil))
  (if (zp i) t
    (and (< (anl-g-fcap (- i 1) anls) (anl-nc anls)) (anl-wf-f (- i 1) anls))))

(defun anl-wf (anls)
  (declare (xargs :stobjs anls :verify-guards nil))
  (and (anl-wf-b (anl-nb anls) anls) (anl-wf-f (anl-nf anls) anls)
       (natp (anl-nb anls)) (natp (anl-nx anls)) (natp (anl-nc anls)) (natp (anl-nf anls))))

(defthm anl-wf-b-nth
  (implies (and (anl-wf-b n anls) (natp n) (natp b) (< b n))
           (and (< (anl-g-bhead b anls) (anl-nx anls)) (< (anl-g-bfn b anls) (anl-nf anls))))
  :hints (("Goal" :induct (anl-wf-b n anls)))
  :rule-classes (:rewrite :linear))

(defthm anl-wf-f-nth
  (implies (and (anl-wf-f n anls) (natp n) (natp f) (< f n)) (< (anl-g-fcap f anls) (anl-nc anls)))
  :hints (("Goal" :induct (anl-wf-f n anls)))
  :rule-classes (:rewrite :linear))

(defthm anl-wf-bfn
  (implies (and (anl-wf anls) (natp b) (< b (anl-nb anls))) (< (anl-g-bfn b anls) (anl-nf anls)))
  :hints (("Goal" :use ((:instance anl-wf-b-nth (n (anl-nb anls))))))
  :rule-classes (:rewrite :linear))

(defthm anl-wf-bhead
  (implies (anl-wf anls) (< (anl-g-bhead b anls) (anl-nx anls)))
  :hints (("Goal" :in-theory (e/d (anl-g-bhead-is) (anl-r-bhead-as-g)) :cases ((and (natp b) (< b (anl-nb anls))))
          :use ((:instance anl-wf-b-nth (n (anl-nb anls))))))
  :rule-classes (:rewrite :linear))

(defthm anl-wf-fcap
  (implies (anl-wf anls) (< (anl-g-fcap f anls) (anl-nc anls)))
  :hints (("Goal" :in-theory (e/d (anl-g-fcap-is) (anl-r-fcap-as-g)) :cases ((and (natp f) (< f (anl-nf anls))))
          :use ((:instance anl-wf-f-nth (n (anl-nf anls))))))
  :rule-classes (:rewrite :linear))

; ---- WHAT THE OPERATIONS LEAVE AS IT WAS -----------------------------------------------------
;
; The writes a slot count and a slot name make touch no block, binding or
; capture; a capture touches no block or binding.

(defthm anl-xfind-s-fctr (equal (anl-xfind x s (anl-s-fctr f v anls)) (anl-xfind x s anls))
  :hints (("Goal" :in-theory (enable anl-xfind))))
(defthm anl-chain-find-s-fctr (equal (anl-chain-find b s (anl-s-fctr f v anls)) (anl-chain-find b s anls))
  :hints (("Goal" :in-theory (enable anl-chain-find))))
(defthm anl-lex-s-fctr (equal (anl-lex b s (anl-s-fctr f v anls)) (anl-lex b s anls)))
(defthm anl-cc-caps-s-fctr (equal (anl-cc-caps c o (anl-s-fctr f v anls)) (anl-cc-caps c o anls)))
(defthm anl-ccc-s-fctr (equal (anl-ccc b (anl-s-fctr f v anls)) (anl-ccc b anls)))
(defthm anl-wf-b-s-fctr (equal (anl-wf-b n (anl-s-fctr f v anls)) (anl-wf-b n anls))
  :hints (("Goal" :induct (anl-wf-b n anls))))
(defthm anl-wf-f-s-fctr (equal (anl-wf-f n (anl-s-fctr f v anls)) (anl-wf-f n anls))
  :hints (("Goal" :induct (anl-wf-f n anls))))
(defthm anl-wf-s-fctr (equal (anl-wf (anl-s-fctr f v anls)) (anl-wf anls)))

(defthm anl-push-n-reads
  (and (equal (anl-g-bhead i (anl-push-n f s k anls)) (anl-g-bhead i anls))
       (equal (anl-g-bpar i (anl-push-n f s k anls)) (anl-g-bpar i anls))
       (equal (anl-g-bfn i (anl-push-n f s k anls)) (anl-g-bfn i anls))
       (equal (anl-g-xnm i (anl-push-n f s k anls)) (anl-g-xnm i anls))
       (equal (anl-g-xnext i (anl-push-n f s k anls)) (anl-g-xnext i anls))
       (equal (anl-g-xsl i (anl-push-n f s k anls)) (anl-g-xsl i anls))
       (equal (anl-g-fout i (anl-push-n f s k anls)) (anl-g-fout i anls))
       (equal (anl-g-fcap i (anl-push-n f s k anls)) (anl-g-fcap i anls))
       (equal (anl-g-cnm i (anl-push-n f s k anls)) (anl-g-cnm i anls))
       (equal (anl-g-cbx i (anl-push-n f s k anls)) (anl-g-cbx i anls))
       (equal (anl-g-cnext i (anl-push-n f s k anls)) (anl-g-cnext i anls))
       (equal (anl-g-cin i (anl-push-n f s k anls)) (anl-g-cin i anls))
       (equal (anl-g-cout i (anl-push-n f s k anls)) (anl-g-cout i anls))
       (equal (anl-g-fctr i (anl-push-n f s k anls)) (anl-g-fctr i anls))
       (equal (anl-nb (anl-push-n f s k anls)) (anl-nb anls))
       (equal (anl-nx (anl-push-n f s k anls)) (anl-nx anls))
       (equal (anl-nc (anl-push-n f s k anls)) (anl-nc anls))
       (equal (anl-nf (anl-push-n f s k anls)) (anl-nf anls)))
  :hints (("Goal" :in-theory (enable anl-push-n))))
(in-theory (disable anl-push-n))

(defthm anl-xfind-push-n (equal (anl-xfind x s2 (anl-push-n f s k anls)) (anl-xfind x s2 anls))
  :hints (("Goal" :in-theory (enable anl-xfind))))
(defthm anl-chain-find-push-n (equal (anl-chain-find b s2 (anl-push-n f s k anls)) (anl-chain-find b s2 anls))
  :hints (("Goal" :in-theory (enable anl-chain-find))))
(defthm anl-lex-push-n (equal (anl-lex b s2 (anl-push-n f s k anls)) (anl-lex b s2 anls)))
(defthm anl-cc-caps-push-n (equal (anl-cc-caps c o (anl-push-n f s k anls)) (anl-cc-caps c o anls)))
(defthm anl-ccc-push-n (equal (anl-ccc b (anl-push-n f s k anls)) (anl-ccc b anls)))
(defthm anl-wf-b-push-n (equal (anl-wf-b n (anl-push-n f s k anls)) (anl-wf-b n anls))
  :hints (("Goal" :induct (anl-wf-b n anls))))
(defthm anl-wf-f-push-n (equal (anl-wf-f n (anl-push-n f s k anls)) (anl-wf-f n anls))
  :hints (("Goal" :induct (anl-wf-f n anls))))
(defthm anl-wf-push-n (equal (anl-wf (anl-push-n f s k anls)) (anl-wf anls)))

; a capture: record nc, at the head of fn f's list
(defthm anl-push-c-reads
  (and (equal (anl-g-bhead i (anl-push-c f s k slot bx anls)) (anl-g-bhead i anls))
       (equal (anl-g-bpar i (anl-push-c f s k slot bx anls)) (anl-g-bpar i anls))
       (equal (anl-g-bfn i (anl-push-c f s k slot bx anls)) (anl-g-bfn i anls))
       (equal (anl-g-xnm i (anl-push-c f s k slot bx anls)) (anl-g-xnm i anls))
       (equal (anl-g-xnext i (anl-push-c f s k slot bx anls)) (anl-g-xnext i anls))
       (equal (anl-g-xsl i (anl-push-c f s k slot bx anls)) (anl-g-xsl i anls))
       (equal (anl-g-fout i (anl-push-c f s k slot bx anls)) (anl-g-fout i anls))
       (equal (anl-nb (anl-push-c f s k slot bx anls)) (anl-nb anls))
       (equal (anl-nx (anl-push-c f s k slot bx anls)) (anl-nx anls))
       (equal (anl-nf (anl-push-c f s k slot bx anls)) (anl-nf anls)))
  :hints (("Goal" :in-theory (enable anl-push-c))))
(in-theory (disable anl-push-c))

(defthm anl-xfind-push-c (equal (anl-xfind x s2 (anl-push-c f s k slot bx anls)) (anl-xfind x s2 anls))
  :hints (("Goal" :in-theory (enable anl-xfind))))
(defthm anl-chain-find-push-c (equal (anl-chain-find b s2 (anl-push-c f s k slot bx anls)) (anl-chain-find b s2 anls))
  :hints (("Goal" :in-theory (enable anl-chain-find))))
(defthm anl-lex-push-c (equal (anl-lex b s2 (anl-push-c f s k slot bx anls)) (anl-lex b s2 anls)))

; what a push-c that did not fail did: the counts, the new record's fields
(defthm anl-push-c-new
  (implies (and (natp (anl-nc anls)) (< (anl-nc anls) (- *anl40* 1)) (natp f) (< f (anl-nf anls))
                (< f (anl-fcap-length anls)))
           (let ((a2 (anl-push-c f s k slot bx anls)) (c (anl-nc anls)))
             (and (equal (anl-nc a2) (+ 1 c))
                  (equal (anl-g-fcap f a2) c)
                  (equal (anl-g-cnm c a2) s) (equal (anl-g-cbx c a2) bx)
                  (equal (anl-g-cnext c a2) (anl-g-fcap f anls)))))
  :hints (("Goal" :in-theory (enable anl-push-c))))

; ... and the old records' fields, and the other fns' heads, as they were
(defthm anl-push-c-old
  (implies (and (natp (anl-nc anls)) (natp i) (< i (anl-nc anls)))
           (let ((a2 (anl-push-c f s k slot bx anls)))
             (and (equal (anl-g-cnm i a2) (anl-g-cnm i anls)) (equal (anl-g-cbx i a2) (anl-g-cbx i anls))
                  (equal (anl-g-cnext i a2) (anl-g-cnext i anls)) (equal (anl-g-cin i a2) (anl-g-cin i anls))
                  (equal (anl-g-cout i a2) (anl-g-cout i anls)))))
  :hints (("Goal" :in-theory (enable anl-push-c))))

(defthm anl-push-c-other-heads
  (implies (not (equal g f)) (equal (anl-g-fcap g (anl-push-c f s k slot bx anls)) (anl-g-fcap g anls)))
  :hints (("Goal" :in-theory (enable anl-push-c))))

(defthm anl-push-c-nc
  (implies (natp (anl-nc anls)) (<= (anl-nc anls) (anl-nc (anl-push-c f s k slot bx anls))))
  :hints (("Goal" :in-theory (enable anl-push-c)))
  :rule-classes :linear)

(defthm anl-push-c-nc-int
  (implies (natp (anl-nc anls)) (natp (anl-nc (anl-push-c f s k slot bx anls))))
  :hints (("Goal" :in-theory (enable anl-push-c)))
  :rule-classes (:rewrite :type-prescription))

; an old list of captures reads as it did after a capture is made
(defthm anl-cc-caps-push-c-old
  (implies (and (natp (anl-nc anls)) (< c (anl-nc anls)))
           (equal (anl-cc-caps c o (anl-push-c f s k slot bx anls)) (anl-cc-caps c o anls)))
  :hints (("Goal" :induct (anl-cc-caps c o anls))))

; the push-c's that do not fail, as lookup makes them
(defmacro anl-push-c-ok (f anls)
  `(and (natp (anl-nc ,anls)) (< (anl-nc ,anls) (- *anl40* 1)) (natp ,f) (< ,f (anl-nf ,anls))
        (< ,f (anl-fcap-length ,anls))))

; fn f's new list: the new capture, then its old list
(defthm anl-cc-caps-push-c-own
  (implies (and (anl-wf anls) (anl-push-c-ok f anls))
           (equal (anl-cc-caps (anl-nc anls) o (anl-push-c f s k slot bx anls))
                  (and (<= 0 bx) (equal bx (anl-lex o s anls)) (anl-cc-caps (anl-g-fcap f anls) o anls))))
  :hints (("Goal" :expand ((anl-cc-caps (anl-nc anls) o (anl-push-c f s k slot bx anls))
                           (anl-cc-caps (anl-g-fcap f anls) o anls)))))

(defthm anl-fcap-push-c
  (implies (anl-push-c-ok f anls)
           (equal (anl-g-fcap g (anl-push-c f s k slot bx anls))
                  (if (equal g f) (anl-nc anls) (anl-g-fcap g anls)))))

; a capture of what its name means keeps the invariant at every block
(defthm anl-ccc-push-c
  (implies (and (anl-wf anls) (anl-ccc b anls) (anl-push-c-ok f anls)
                (<= 0 bx) (equal bx (anl-lex (anl-g-fout f anls) s anls)))
           (anl-ccc b (anl-push-c f s k slot bx anls)))
  :hints (("Goal" :induct (anl-ccc b anls))))

; the error flag's write leaves what a name means
(defthm anl-xfind-err (equal (anl-xfind x s (update-anl-err v anls)) (anl-xfind x s anls))
  :hints (("Goal" :in-theory (enable anl-xfind))))
(defthm anl-chain-find-err (equal (anl-chain-find b s (update-anl-err v anls)) (anl-chain-find b s anls))
  :hints (("Goal" :in-theory (enable anl-chain-find))))
(defthm anl-lex-err (equal (anl-lex b s (update-anl-err v anls)) (anl-lex b s anls)))
(defthm anl-cc-caps-err (equal (anl-cc-caps c o (update-anl-err v anls)) (anl-cc-caps c o anls)))
(defthm anl-ccc-err (equal (anl-ccc b (update-anl-err v anls)) (anl-ccc b anls)))
(defthm anl-wf-b-err (equal (anl-wf-b n (update-anl-err v anls)) (anl-wf-b n anls))
  :hints (("Goal" :induct (anl-wf-b n anls))))
(defthm anl-wf-f-err (equal (anl-wf-f n (update-anl-err v anls)) (anl-wf-f n anls))
  :hints (("Goal" :induct (anl-wf-f n anls))))
(defthm anl-wf-err (equal (anl-wf (update-anl-err v anls)) (anl-wf anls)))

(defthm anl-push-c-own-head
  (implies (and (natp (anl-nc anls)) (< (anl-g-fcap f anls) (anl-nc anls)))
           (< (anl-g-fcap f (anl-push-c f s k slot bx anls)) (anl-nc (anl-push-c f s k slot bx anls))))
  :hints (("Goal" :in-theory (enable anl-push-c))))

; a capture keeps the heads records
(defthm anl-wf-b-push-c (equal (anl-wf-b n (anl-push-c f s k slot bx anls)) (anl-wf-b n anls))
  :hints (("Goal" :induct (anl-wf-b n anls))))
(defthm anl-wf-f-push-c
  (implies (and (natp (anl-nc anls)) (anl-wf-f n anls))
           (anl-wf-f n (anl-push-c f s k slot bx anls)))
  :hints (("Goal" :induct (anl-wf-f n anls))
          ("Subgoal *1/2" :cases ((equal (+ -1 n) f)))))
(defthm anl-wf-push-c (implies (anl-wf anls) (anl-wf (anl-push-c f s k slot bx anls))))

; a push-c that does not fit sets the error flag
(defthm anl-push-c-fails
  (implies (and (natp f) (< f (anl-nf anls))
                (not (and (natp (anl-nc anls)) (< (anl-nc anls) (- *anl40* 1)) (< f (anl-fcap-length anls)))))
           (not (equal (anl-err (anl-push-c f s k slot bx anls)) 0)))
  :hints (("Goal" :in-theory (enable anl-push-c))))

(defthm anl-push-c-unseen-heads
  (implies (not (and (natp f) (< f (anl-nf anls))))
           (equal (anl-g-fcap g (anl-push-c f s k slot bx anls)) (anl-g-fcap g anls)))
  :hints (("Goal" :in-theory (enable anl-push-c))))

; one to a fn no read can see (past the fns count) changes no list
(defthm anl-ccc-push-c-unseen
  (implies (and (anl-wf anls) (anl-ccc b anls) (not (and (natp f) (< f (anl-nf anls)))))
           (anl-ccc b (anl-push-c f s k slot bx anls)))
  :hints (("Goal" :induct (anl-ccc b anls))))

; so any capture of what its name means, made with no error, keeps it
(defthm anl-ccc-push-c-noerr
  (implies (and (anl-wf anls) (anl-ccc b anls) (equal (anl-err (anl-push-c f s k slot bx anls)) 0)
                (<= 0 bx) (equal bx (anl-lex (anl-g-fout f anls) s anls)))
           (anl-ccc b (anl-push-c f s k slot bx anls)))
  :hints (("Goal" :cases ((and (natp f) (< f (anl-nf anls))))
                  :use (anl-ccc-push-c anl-ccc-push-c-unseen anl-push-c-fails)
                  :in-theory (disable anl-ccc-push-c anl-ccc-push-c-unseen anl-push-c-fails))))

; a state left with no error was entered with none
(defthm anl-push-c-err-fc
  (implies (equal (anl-err (anl-push-c f s k slot bx anls)) 0) (equal (anl-err anls) 0))
  :hints (("Goal" :use anl-push-c-err))
  :rule-classes :forward-chaining)
(defthm anl-s-fctr-err-fc
  (implies (equal (anl-err (anl-s-fctr f v anls)) 0) (equal (anl-err anls) 0))
  :rule-classes :forward-chaining)
(defthm anl-lookup-err-fc
  (implies (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0) (equal (anl-err anls) 0))
  :hints (("Goal" :use anl-lookup-err))
  :rule-classes :forward-chaining)

; THROUGH A LOOKUP: what a name means, the fns' outer blocks, the heads
(defthm anl-lookup-reads
  (and (equal (anl-g-fout i (mv-nth 2 (anl-lookup b s anls))) (anl-g-fout i anls))
       (equal (anl-g-bfn i (mv-nth 2 (anl-lookup b s anls))) (anl-g-bfn i anls))
       (equal (anl-nf (mv-nth 2 (anl-lookup b s anls))) (anl-nf anls))
       (equal (anl-lex b2 s2 (mv-nth 2 (anl-lookup b s anls))) (anl-lex b2 s2 anls)))
  :hints (("Goal" :induct (anl-lookup b s anls))))

(defthm anl-lookup-wf (implies (anl-wf anls) (anl-wf (mv-nth 2 (anl-lookup b s anls))))
  :hints (("Goal" :induct (anl-lookup b s anls))))

(defthm anl-lookup-nc (implies (natp (anl-nc anls)) (natp (anl-nc (mv-nth 2 (anl-lookup b s anls)))))
  :hints (("Goal" :induct (anl-lookup b s anls)))
  :rule-classes (:rewrite :type-prescription))

; the step: after the lookup in the fn around, the capture lookup makes
(defthm anl-lookup-ccc-step
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc o anls)
                (anl-ccc b2 (mv-nth 2 (anl-lookup o s anls)))
                (<= 0 (anl-lex o s anls)) (equal o (anl-g-fout f anls)) (equal bx (anl-lex o s anls))
                (equal (anl-err (anl-push-c f s k slot (mv-nth 1 (anl-lookup o s anls))
                                            (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls))))) 0))
           (anl-ccc b2 (anl-push-c f s k slot bx
                                   (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls))))))
  :hints (("Goal" :use ((:instance anl-ccc-push-c-noerr (b b2) (bx (anl-lex o s anls))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                         (:instance anl-lookup-lex (b o)) (:instance anl-s-fctr-err-fc (anls (mv-nth 2 (anl-lookup o s anls))))
                         (:instance anl-push-c-err-fc (bx (mv-nth 1 (anl-lookup o s anls))) (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls))))))
                  :in-theory (disable anl-ccc-push-c-noerr anl-lookup anl-lex anl-ccc))))

; THE INVARIANT KEPT: the captures a lookup makes are each of what their
; names mean, so every block's invariant holds after it as before
(defthm anl-lookup-ccc-any
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc b2 anls) (anl-ccc b anls)
                (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0))
           (anl-ccc b2 (mv-nth 2 (anl-lookup b s anls))))
  :hints (("Goal" :induct (anl-lookup b s anls))
))

(defthm anl-lookup-ccc
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc b anls) (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0))
           (anl-ccc b (mv-nth 2 (anl-lookup b s anls)))))

; ---- THE ANALYZER'S OTHER OPERATIONS KEEP THE INVARIANT --------------------------------------
;
; at the block it works in: reserving slots anywhere, binding a name in
; that block, a block nested in it, a fn written in it

(in-theory (disable (:definition anl-lex) (:definition anl-ccc) (:definition anl-lookup)))

(defthm anl-ccc-no-block (implies (not (natp b)) (anl-ccc b anls))
  :hints (("Goal" :in-theory (enable anl-ccc))))

(defthm anl-reserve-ccc
  (equal (anl-ccc b2 (mv-nth 1 (anl-reserve b n anls))) (anl-ccc b2 anls)))
(defthm anl-reserve-wf
  (equal (anl-wf (mv-nth 1 (anl-reserve b n anls))) (anl-wf anls)))

; a binding: record nx, at the head of block a's list
(defthm anl-bind-reads
  (and (implies (and (natp i) (< i (anl-nx anls)))
                (and (equal (anl-g-xnm i (anl-bind a s k anls)) (anl-g-xnm i anls))
                     (equal (anl-g-xnext i (anl-bind a s k anls)) (anl-g-xnext i anls))
                     (equal (anl-g-xsl i (anl-bind a s k anls)) (anl-g-xsl i anls))))
       (implies (not (equal i a)) (equal (anl-g-bhead i (anl-bind a s k anls)) (anl-g-bhead i anls)))
       (equal (anl-g-bpar i (anl-bind a s k anls)) (anl-g-bpar i anls))
       (equal (anl-g-bfn i (anl-bind a s k anls)) (anl-g-bfn i anls))
       (equal (anl-g-fout i (anl-bind a s k anls)) (anl-g-fout i anls))
       (equal (anl-g-fcap i (anl-bind a s k anls)) (anl-g-fcap i anls))
       (equal (anl-g-cnm i (anl-bind a s k anls)) (anl-g-cnm i anls))
       (equal (anl-g-cbx i (anl-bind a s k anls)) (anl-g-cbx i anls))
       (equal (anl-g-cnext i (anl-bind a s k anls)) (anl-g-cnext i anls))
       (equal (anl-nb (anl-bind a s k anls)) (anl-nb anls))
       (equal (anl-nc (anl-bind a s k anls)) (anl-nc anls))
       (equal (anl-nf (anl-bind a s k anls)) (anl-nf anls))
       (implies (natp (anl-nx anls)) (and (natp (anl-nx (anl-bind a s k anls)))
                                          (<= (anl-nx anls) (anl-nx (anl-bind a s k anls))))))
  :hints (("Goal" :in-theory (enable anl-bind))))

(defthm anl-bind-own-head
  (implies (and (natp (anl-nx anls)) (< (anl-g-bhead a anls) (anl-nx anls)))
           (< (anl-g-bhead a (anl-bind a s k anls)) (anl-nx (anl-bind a s k anls))))
  :hints (("Goal" :in-theory (enable anl-bind))))

(defthm anl-bind-nx-natp (implies (natp (anl-nx anls)) (natp (anl-nx (anl-bind a s k anls))))
  :hints (("Goal" :in-theory (enable anl-bind))) :rule-classes (:rewrite :type-prescription))
(defthm anl-bind-nx-grows (implies (natp (anl-nx anls)) (<= (anl-nx anls) (anl-nx (anl-bind a s k anls))))
  :hints (("Goal" :in-theory (enable anl-bind))) :rule-classes :linear)
(in-theory (disable anl-bind))

(defthm anl-xfind-bind
  (implies (and (natp (anl-nx anls)) (< x (anl-nx anls)))
           (equal (anl-xfind x s2 (anl-bind a s k anls)) (anl-xfind x s2 anls)))
  :hints (("Goal" :in-theory (enable anl-xfind))))

(defthm anl-chain-find-bind
  (implies (and (anl-wf anls) (< b a))
           (equal (anl-chain-find b s2 (anl-bind a s k anls)) (anl-chain-find b s2 anls)))
  :hints (("Goal" :in-theory (enable anl-chain-find))))

(defthm anl-lex-bind
  (implies (and (anl-wf anls) (< b a))
           (equal (anl-lex b s2 (anl-bind a s k anls)) (anl-lex b s2 anls)))
  :hints (("Goal" :in-theory (enable anl-lex))))

(defthm anl-cc-caps-bind
  (implies (and (anl-wf anls) (< o a))
           (equal (anl-cc-caps c o (anl-bind a s k anls)) (anl-cc-caps c o anls))))

(defthm anl-ccc-bind
  (implies (and (anl-wf anls) (<= b a))
           (equal (anl-ccc b (anl-bind a s k anls)) (anl-ccc b anls)))
  :hints (("Goal" :in-theory (enable anl-ccc))))

(defthm anl-wf-b-bind
  (implies (and (anl-wf-b n anls) (natp (anl-nx anls)))
           (anl-wf-b n (anl-bind a s k anls)))
  :hints (("Goal" :induct (anl-wf-b n anls))
          ("Subgoal *1/2" :cases ((equal (+ -1 n) a)))))
(defthm anl-wf-f-bind (equal (anl-wf-f n (anl-bind a s k anls)) (anl-wf-f n anls))
  :hints (("Goal" :induct (anl-wf-f n anls))))
(defthm anl-wf-bind (implies (anl-wf anls) (anl-wf (anl-bind a s k anls))))

; THE INVARIANT AT THE BLOCK A NAME IS BOUND IN, and every block before it
(defthm anl-bind-ccc
  (implies (and (anl-wf anls) (anl-ccc a anls)) (anl-ccc a (anl-bind a s k anls))))

; a nested block: record nb, the fns and every old record as they were
(defthm anl-child-reads
  (let ((a2 (mv-nth 1 (anl-child p anls))))
    (and (implies (and (natp i) (< i (anl-nb anls)))
                  (and (equal (anl-g-bhead i a2) (anl-g-bhead i anls))
                       (equal (anl-g-bpar i a2) (anl-g-bpar i anls))
                       (equal (anl-g-bfn i a2) (anl-g-bfn i anls))))
         (equal (anl-g-xnm i a2) (anl-g-xnm i anls))
         (equal (anl-g-xnext i a2) (anl-g-xnext i anls))
         (equal (anl-g-fout i a2) (anl-g-fout i anls))
         (equal (anl-g-fcap i a2) (anl-g-fcap i anls))
         (equal (anl-g-cnm i a2) (anl-g-cnm i anls))
         (equal (anl-g-cbx i a2) (anl-g-cbx i anls))
         (equal (anl-g-cnext i a2) (anl-g-cnext i anls))
         (equal (anl-nx a2) (anl-nx anls)) (equal (anl-nc a2) (anl-nc anls)) (equal (anl-nf a2) (anl-nf anls))))
  :hints (("Goal" :in-theory (enable anl-child))))

(defthm anl-child-new
  (implies (and (natp (anl-nb anls)) (< (anl-nb anls) (- *anl40* 1)) (natp (anl-g-bfn p anls)))
           (let ((a2 (mv-nth 1 (anl-child p anls))) (c (anl-nb anls)))
             (and (equal (mv-nth 0 (anl-child p anls)) c)
                  (equal (anl-nb a2) (+ 1 c))
                  (equal (anl-g-bfn c a2) (anl-g-bfn p anls)) (equal (anl-g-bpar c a2) p)
                  (equal (anl-g-bhead c a2) -1))))
  :hints (("Goal" :in-theory (enable anl-child))))

(defthm anl-child-nb
  (implies (natp (anl-nb anls)) (natp (anl-nb (mv-nth 1 (anl-child p anls)))))
  :hints (("Goal" :in-theory (enable anl-child)))
  :rule-classes (:rewrite :type-prescription))

(defthm anl-child-nb-linear
  (implies (natp (anl-nb anls)) (<= (anl-nb anls) (anl-nb (mv-nth 1 (anl-child p anls)))))
  :hints (("Goal" :in-theory (enable anl-child)))
  :rule-classes :linear)

(defthm anl-child-fails
  (implies (not (and (natp (anl-nb anls)) (< (anl-nb anls) (- *anl40* 1)) (natp (anl-g-bfn p anls))))
           (and (equal (mv-nth 1 (anl-child p anls)) (update-anl-err 1 anls))
                (equal (mv-nth 0 (anl-child p anls)) -1)))
  :hints (("Goal" :in-theory (enable anl-child))))

(in-theory (disable anl-child))

(defthm anl-xfind-child (equal (anl-xfind x s (mv-nth 1 (anl-child p anls))) (anl-xfind x s anls))
  :hints (("Goal" :in-theory (enable anl-xfind))))
(defthm anl-chain-find-child
  (implies (and (natp (anl-nb anls)) (< b (anl-nb anls)))
           (equal (anl-chain-find b s (mv-nth 1 (anl-child p anls))) (anl-chain-find b s anls)))
  :hints (("Goal" :in-theory (enable anl-chain-find))))
(defthm anl-lex-child
  (implies (and (natp (anl-nb anls)) (< b (anl-nb anls)))
           (equal (anl-lex b s (mv-nth 1 (anl-child p anls))) (anl-lex b s anls)))
  :hints (("Goal" :induct (anl-lex b s anls)
                  :expand ((anl-lex b s (mv-nth 1 (anl-child p anls))) (anl-lex b s anls)))))
(defthm anl-cc-caps-child
  (implies (and (natp (anl-nb anls)) (< o (anl-nb anls)))
           (equal (anl-cc-caps c o (mv-nth 1 (anl-child p anls))) (anl-cc-caps c o anls))))
(defthm anl-ccc-child-old
  (implies (and (natp (anl-nb anls)) (< b (anl-nb anls)))
           (equal (anl-ccc b (mv-nth 1 (anl-child p anls))) (anl-ccc b anls)))
  :hints (("Goal" :induct (anl-ccc b anls)
                  :expand ((anl-ccc b (mv-nth 1 (anl-child p anls))) (anl-ccc b anls)))))
(defthm anl-wf-b-child
  (implies (and (anl-wf-b n anls) (natp (anl-nb anls)) (<= n (anl-nb anls)))
           (anl-wf-b n (mv-nth 1 (anl-child p anls))))
  :hints (("Goal" :induct (anl-wf-b n anls))))
(defthm anl-wf-f-child (equal (anl-wf-f n (mv-nth 1 (anl-child p anls))) (anl-wf-f n anls))
  :hints (("Goal" :induct (anl-wf-f n anls))))
(defthm anl-wf-child (implies (anl-wf anls) (anl-wf (mv-nth 1 (anl-child p anls))))
  :hints (("Goal" :cases ((and (natp (anl-nb anls)) (< (anl-nb anls) (- *anl40* 1)) (natp (anl-g-bfn p anls))))
           :use ((:instance anl-wf-b-nth (n (anl-nb anls)) (b p)))
           :expand ((anl-wf-b (+ 1 (anl-nb anls)) (mv-nth 1 (anl-child p anls)))))))

; THE INVARIANT AT A NESTED BLOCK, as at the block around it (whose fn is
; written in a block before it, as every block of a fn is)
(defthm anl-child-ccc
  (implies (and (anlsp anls) (anl-wf anls) (anl-ccc p anls) (natp p) (< p (anl-nb anls))
                (< (anl-g-fout (anl-g-bfn p anls) anls) p))
           (anl-ccc (mv-nth 0 (anl-child p anls)) (mv-nth 1 (anl-child p anls))))
  :hints (("Goal" :cases ((and (< (anl-nb anls) (- *anl40* 1)) (natp (anl-g-bfn p anls))))
           :expand ((anl-ccc p anls)
                    (anl-ccc (mv-nth 0 (anl-child p anls)) (mv-nth 1 (anl-child p anls)))
                    (anl-ccc (anl-nb anls) (mv-nth 1 (anl-child p anls)))))))

; a fn written in block o: fn nf and its root block nb, every old record as it was
(defmacro anl-new-fn-ok (anls)
  `(and (natp (anl-nf ,anls)) (< (anl-nf ,anls) (- *anl40* 1)) (natp (anl-nb ,anls)) (< (anl-nb ,anls) (- *anl40* 1))))

(defthm anl-new-fn-reads
  (let ((a2 (mv-nth 1 (anl-new-fn o anls))))
    (and (implies (and (natp i) (< i (anl-nb anls)))
                  (and (equal (anl-g-bhead i a2) (anl-g-bhead i anls))
                       (equal (anl-g-bpar i a2) (anl-g-bpar i anls))
                       (equal (anl-g-bfn i a2) (anl-g-bfn i anls))))
         (implies (and (natp i) (< i (anl-nf anls)))
                  (and (equal (anl-g-fout i a2) (anl-g-fout i anls))
                       (equal (anl-g-fcap i a2) (anl-g-fcap i anls))))
         (equal (anl-g-xnm i a2) (anl-g-xnm i anls))
         (equal (anl-g-xnext i a2) (anl-g-xnext i anls))
         (equal (anl-g-cnm i a2) (anl-g-cnm i anls))
         (equal (anl-g-cbx i a2) (anl-g-cbx i anls))
         (equal (anl-g-cnext i a2) (anl-g-cnext i anls))
         (equal (anl-nx a2) (anl-nx anls)) (equal (anl-nc a2) (anl-nc anls))))
  :hints (("Goal" :in-theory (enable anl-new-fn))))

(defthm anl-new-fn-new
  (implies (anl-new-fn-ok anls)
           (let ((a2 (mv-nth 1 (anl-new-fn o anls))) (b (anl-nb anls)) (f (anl-nf anls)))
             (and (equal (mv-nth 0 (anl-new-fn o anls)) b)
                  (equal (anl-nb a2) (+ 1 b)) (equal (anl-nf a2) (+ 1 f))
                  (equal (anl-g-bfn b a2) f) (equal (anl-g-bpar b a2) -1) (equal (anl-g-bhead b a2) -1)
                  (equal (anl-g-fout f a2) o) (equal (anl-g-fcap f a2) -1))))
  :hints (("Goal" :in-theory (enable anl-new-fn))))

(defthm anl-new-fn-fails
  (implies (not (anl-new-fn-ok anls))
           (and (equal (mv-nth 1 (anl-new-fn o anls)) (update-anl-err 1 anls))
                (equal (mv-nth 0 (anl-new-fn o anls)) -1)))
  :hints (("Goal" :in-theory (enable anl-new-fn))))

(defthm anl-new-fn-nb-natp
  (implies (natp (anl-nb anls)) (natp (anl-nb (mv-nth 1 (anl-new-fn o anls)))))
  :hints (("Goal" :in-theory (enable anl-new-fn)))
  :rule-classes (:rewrite :type-prescription))
(defthm anl-new-fn-nf-natp
  (implies (natp (anl-nf anls)) (natp (anl-nf (mv-nth 1 (anl-new-fn o anls)))))
  :hints (("Goal" :in-theory (enable anl-new-fn)))
  :rule-classes (:rewrite :type-prescription))

(defthm anl-new-fn-counts-linear
  (implies (and (natp (anl-nb anls)) (natp (anl-nf anls)))
           (and (<= (anl-nb anls) (anl-nb (mv-nth 1 (anl-new-fn o anls))))
                (<= (anl-nf anls) (anl-nf (mv-nth 1 (anl-new-fn o anls))))))
  :hints (("Goal" :in-theory (enable anl-new-fn)))
  :rule-classes :linear)

(in-theory (disable anl-new-fn))

(defthm anl-xfind-new-fn (equal (anl-xfind x s (mv-nth 1 (anl-new-fn o anls))) (anl-xfind x s anls))
  :hints (("Goal" :in-theory (enable anl-xfind))))
(defthm anl-chain-find-new-fn
  (implies (and (natp (anl-nb anls)) (natp (anl-nf anls)) (< b (anl-nb anls)))
           (equal (anl-chain-find b s (mv-nth 1 (anl-new-fn o anls))) (anl-chain-find b s anls)))
  :hints (("Goal" :in-theory (enable anl-chain-find))))
(defthm anl-new-fn-fn-of-block
  (implies (and (anl-wf anls) (natp b) (< b (anl-nb anls)))
           (and (equal (anl-g-fout (anl-g-bfn b anls) (mv-nth 1 (anl-new-fn o anls))) (anl-g-fout (anl-g-bfn b anls) anls))
                (equal (anl-g-fcap (anl-g-bfn b anls) (mv-nth 1 (anl-new-fn o anls))) (anl-g-fcap (anl-g-bfn b anls) anls))))
  :hints (("Goal" :cases ((natp (anl-g-bfn b anls))))))

(defthm anl-lex-new-fn
  (implies (and (anl-wf anls) (< b (anl-nb anls)))
           (equal (anl-lex b s (mv-nth 1 (anl-new-fn o anls))) (anl-lex b s anls)))
  :hints (("Goal" :induct (anl-lex b s anls)
                  :expand ((anl-lex b s (mv-nth 1 (anl-new-fn o anls))) (anl-lex b s anls)))))
(defthm anl-cc-caps-new-fn
  (implies (and (anl-wf anls) (< o2 (anl-nb anls)))
           (equal (anl-cc-caps c o2 (mv-nth 1 (anl-new-fn o anls))) (anl-cc-caps c o2 anls))))
(defthm anl-ccc-new-fn-old
  (implies (and (anl-wf anls) (< b (anl-nb anls)))
           (equal (anl-ccc b (mv-nth 1 (anl-new-fn o anls))) (anl-ccc b anls)))
  :hints (("Goal" :induct (anl-ccc b anls)
                  :expand ((anl-ccc b (mv-nth 1 (anl-new-fn o anls))) (anl-ccc b anls)))))

(defthm anl-wf-b-new-fn
  (implies (and (anl-wf-b n anls) (natp (anl-nb anls)) (natp (anl-nf anls)) (<= n (anl-nb anls)))
           (anl-wf-b n (mv-nth 1 (anl-new-fn o anls))))
  :hints (("Goal" :induct (anl-wf-b n anls))))
(defthm anl-wf-f-new-fn
  (implies (and (anl-wf-f n anls) (natp (anl-nf anls)) (<= n (anl-nf anls)))
           (anl-wf-f n (mv-nth 1 (anl-new-fn o anls))))
  :hints (("Goal" :induct (anl-wf-f n anls))))
(defthm anl-wf-new-fn (implies (anl-wf anls) (anl-wf (mv-nth 1 (anl-new-fn o anls))))
  :hints (("Goal" :cases ((anl-new-fn-ok anls))
           :expand ((anl-wf-b (+ 1 (anl-nb anls)) (mv-nth 1 (anl-new-fn o anls)))
                    (anl-wf-f (+ 1 (anl-nf anls)) (mv-nth 1 (anl-new-fn o anls)))))))

; THE INVARIANT AT A FN'S ROOT BLOCK, as at the block it is written in
(defthm anl-new-fn-ccc
  (implies (and (anlsp anls) (anl-wf anls) (anl-ccc o anls) (< o (anl-nb anls)))
           (anl-ccc (mv-nth 0 (anl-new-fn o anls)) (mv-nth 1 (anl-new-fn o anls))))
  :hints (("Goal" :cases ((anl-new-fn-ok anls))
           :expand ((anl-ccc (mv-nth 0 (anl-new-fn o anls)) (mv-nth 1 (anl-new-fn o anls)))
                    (anl-ccc (anl-nb anls) (mv-nth 1 (anl-new-fn o anls)))
                    (anl-cc-caps -1 o (mv-nth 1 (anl-new-fn o anls)))))))

; ---- THE CAPTURES: EXACTLY THE FREE LOCALS USED ---------------------------------------------

; the names a list of captures holds, newest first; a fn's
(defun anl-capnames (c anls)
  (declare (xargs :stobjs anls :measure (nfix c) :ruler-extenders :all :verify-guards nil))
  (if (and (natp c) (< c (anl-nc anls)))
      (cons (anl-g-cnm c anls)
            (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (anl-capnames j anls) nil)))
    nil))

(defun anl-fcaps (f anls)
  (declare (xargs :stobjs anls :verify-guards nil))
  (anl-capnames (anl-g-fcap f anls) anls))

(defthm anl-cfind-member
  (equal (<= 0 (anl-cfind c s anls)) (if (member-equal s (anl-capnames c anls)) t nil))
  :hints (("Goal" :in-theory (enable anl-cfind))))

(defthm anl-capnames-push-c-old
  (implies (and (natp (anl-nc anls)) (< c (anl-nc anls)))
           (equal (anl-capnames c (anl-push-c f s k slot bx anls)) (anl-capnames c anls)))
  :hints (("Goal" :induct (anl-capnames c anls))))

(defthm anl-capnames-s-fctr (equal (anl-capnames c (anl-s-fctr f v anls)) (anl-capnames c anls)))
(defthm anl-capnames-err (equal (anl-capnames c (update-anl-err v anls)) (anl-capnames c anls)))

(defthm anl-fcaps-push-c
  (implies (and (anl-wf anls) (anl-push-c-ok f anls))
           (equal (anl-fcaps g (anl-push-c f s k slot bx anls))
                  (if (equal g f) (cons s (anl-fcaps f anls)) (anl-fcaps g anls))))
  :hints (("Goal" :expand ((anl-capnames (anl-nc anls) (anl-push-c f s k slot bx anls))))))

(defthm anl-fcaps-push-c-unseen
  (implies (and (anl-wf anls) (not (and (natp f) (< f (anl-nf anls)))))
           (equal (anl-fcaps g (anl-push-c f s k slot bx anls)) (anl-fcaps g anls))))

(defthm anl-fcaps-push-c-other
  (implies (and (anl-wf anls) (not (equal g f)))
           (equal (anl-fcaps g (anl-push-c f s k slot bx anls)) (anl-fcaps g anls))))

(defthm anl-fcaps-cfind
  (iff (member-equal s (anl-fcaps f anls)) (<= 0 (anl-cfind (anl-g-fcap f anls) s anls))))
(in-theory (disable anl-cfind-member))

(defthm anl-fcaps-s-fctr (equal (anl-fcaps g (anl-s-fctr f v anls)) (anl-fcaps g anls)))
(defthm anl-fcaps-err (equal (anl-fcaps g (update-anl-err v anls)) (anl-fcaps g anls)))
(in-theory (disable anl-fcaps))

; the invariant at b holds at the block its fn is written in
(defthm anl-ccc-outer
  (implies (and (anl-ccc b anls) (natp b) (natp (anl-g-fout (anl-g-bfn b anls) anls))
                (< (anl-g-fout (anl-g-bfn b anls) anls) b)
                (< (anl-g-bfn (anl-g-fout (anl-g-bfn b anls) anls) anls) (anl-g-bfn b anls)))
           (and (anl-ccc (anl-g-fout (anl-g-bfn b anls) anls) anls)
                (anl-cc-caps (anl-g-fcap (anl-g-bfn b anls) anls) (anl-g-fout (anl-g-bfn b anls) anls) anls)))
  :hints (("Goal" :expand ((anl-ccc b anls)))))

; a capture made with no error is at the head of its fn's list
(defthm anl-fcaps-push-c-noerr
  (implies (and (anl-wf anls) (natp f) (< f (anl-nf anls))
                (equal (anl-err (anl-push-c f s k slot bx anls)) 0))
           (equal (anl-fcaps f (anl-push-c f s k slot bx anls)) (cons s (anl-fcaps f anls))))
  :hints (("Goal" :use (anl-push-c-fails (:instance anl-fcaps-push-c (g f)))
                  :in-theory (disable anl-push-c-fails anl-fcaps-push-c))))

; a lookup in a block of fn f0 touches no fn after f0's
(defthm anl-lookup-fcaps-later
  (implies (and (anl-wf anls) (< (anl-g-bfn b anls) g))
           (equal (anl-fcaps g (mv-nth 2 (anl-lookup b s anls))) (anl-fcaps g anls)))
  :hints (("Goal" :induct (anl-lookup b s anls) :expand ((anl-lookup b s anls)))))

; the step: the capture made after the lookup in the fn around
(defthm anl-lookup-fcaps-step
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc o anls) (natp f) (< f (anl-nf anls))
                (< (anl-g-bfn o anls) f) (equal bx (anl-lex o s anls))
                (equal (anl-err (anl-push-c f s k slot (mv-nth 1 (anl-lookup o s anls))
                                            (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls))))) 0))
           (equal (anl-fcaps f (anl-push-c f s k slot bx (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                  (cons s (anl-fcaps f anls))))
  :hints (("Goal" :use ((:instance anl-fcaps-push-c-noerr (bx (anl-lex o s anls))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                         (:instance anl-lookup-lex (b o))
                         (:instance anl-s-fctr-err-fc (anls (mv-nth 2 (anl-lookup o s anls))))
                         (:instance anl-push-c-err-fc (bx (mv-nth 1 (anl-lookup o s anls)))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                         (:instance anl-lookup-fcaps-later (b o) (g f)))
                  :in-theory (disable anl-fcaps-push-c-noerr anl-lookup anl-lex anl-ccc anl-lookup-fcaps-later))))

; WHAT A LOOKUP ADDS TO ITS OWN FN'S CAPTURES: the name, exactly when no
; block of the fn around b binds it, the fn has not captured it, and it is
; bound outside -- a free local of the fn, used; nothing otherwise
(defthm anl-lookup-caps-own
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc b anls) (natp b) (< b (anl-nb anls))
                (natp (anl-g-bfn b anls))
                (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0))
           (equal (anl-fcaps (anl-g-bfn b anls) (mv-nth 2 (anl-lookup b s anls)))
                  (if (and (< (anl-chain-find b s anls) 0) (<= 0 (anl-lex b s anls))
                           (not (member-equal s (anl-fcaps (anl-g-bfn b anls) anls))))
                      (cons s (anl-fcaps (anl-g-bfn b anls) anls))
                    (anl-fcaps (anl-g-bfn b anls) anls))))
  :hints (("Goal" :expand ((anl-lookup b s anls) (anl-lex b s anls)))))

; the step for any fn: the capture's own gains the name, the rest are as they were
(defthm anl-lookup-fcaps-step-any
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc o anls) (equal bx (anl-lex o s anls))
                (equal (anl-err (anl-push-c f s k slot (mv-nth 1 (anl-lookup o s anls))
                                            (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls))))) 0))
           (equal (anl-fcaps g (anl-push-c f s k slot bx (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                  (if (and (equal g f) (natp f) (< f (anl-nf anls)))
                      (cons s (anl-fcaps f (mv-nth 2 (anl-lookup o s anls))))
                    (anl-fcaps g (mv-nth 2 (anl-lookup o s anls))))))
  :hints (("Goal" :cases ((and (equal g f) (natp f) (< f (anl-nf anls))))
                  :use ((:instance anl-fcaps-push-c-noerr (bx (anl-lex o s anls))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                         (:instance anl-fcaps-push-c-other (bx (anl-lex o s anls))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                         (:instance anl-fcaps-push-c-unseen (bx (anl-lex o s anls))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls)))))
                         (:instance anl-lookup-lex (b o))
                         (:instance anl-s-fctr-err-fc (anls (mv-nth 2 (anl-lookup o s anls))))
                         (:instance anl-push-c-err-fc (bx (mv-nth 1 (anl-lookup o s anls)))
                                    (anls (anl-s-fctr f v (mv-nth 2 (anl-lookup o s anls))))))
                  :in-theory (disable anl-fcaps-push-c-noerr anl-fcaps-push-c-other anl-fcaps-push-c-unseen
                                      anl-fcaps-push-c anl-lookup anl-lex anl-ccc))))

; WHAT IT ADDS TO ANY FN'S: that name, or nothing
(defthm anl-lookup-caps-any
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc b anls)
                (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0))
           (or (equal (anl-fcaps g (mv-nth 2 (anl-lookup b s anls))) (anl-fcaps g anls))
               (and (equal (anl-fcaps g (mv-nth 2 (anl-lookup b s anls))) (cons s (anl-fcaps g anls)))
                    (not (member-equal s (anl-fcaps g anls))))))
  :hints (("Goal" :induct (anl-lookup b s anls) :expand ((anl-lookup b s anls))))
  :rule-classes nil)

; so a fn never captures a name twice
(defthm anl-lookup-caps-nodup
  (implies (and (anlsp anls) (signed-byte-p 64 s) (anl-wf anls) (anl-ccc b anls)
                (equal (anl-err (mv-nth 2 (anl-lookup b s anls))) 0)
                (no-duplicatesp-equal (anl-fcaps g anls)))
           (no-duplicatesp-equal (anl-fcaps g (mv-nth 2 (anl-lookup b s anls)))))
  :hints (("Goal" :use anl-lookup-caps-any)))

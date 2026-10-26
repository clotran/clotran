; THE ANALYZER'S LOCALS (src/f/analyze.inc): binding forms checked as clj's
; Compiler checks them, the scopes a fn* / let* / loop* / letfn* / catch
; makes, a name resolved to the slot of its innermost binding, and the
; captures a closure takes -- at the level the Fortran is GENERATED from
; (src/f/gen/anlocal_gen.inc, scripts/acl2-fortran -b anlocal),
; guard-verified.
;
; THE FORMS are read through five host reads, thin hand-written shims in
; analyze.inc on clotran's values (metadata stripped): frm-kind (1 a vector,
; 2 a symbol, 0 anything else), frm-count / frm-nth (a vector's elements),
; frm-qual (a symbol with a namespace) and frm-amp (the symbol &). Here a
; form is what those reads decode it to: (:vec x1 .. xn), (:sym id qual amp),
; anything else. A name is an integer, the symbol's id from the interning
; shim (analyze.inc anl_sym_id: one id per symbol text, per context).
;
; THE CHECKS, as clj's Compiler makes them (clojure-1.12.6, the Compiler class):
;   anl-shape      LetExpr.Parser / LetFnExpr.Parser: 1 "Bad binding form,
;                  expected vector", 2 "... expected matched symbol
;                  expression pairs"
;   anl-name-code  a let / loop / letfn / catch name: 3 "Bad binding form,
;                  expected symbol, got: x", 4 "Can't let qualified name: x"
;                  (a catch's: "Can't bind qualified name:x")
;   anl-params     FnMethod.parse's PSTATE walk: 5 "fn params must be
;                  Symbols", 6 "Can't use qualified name as parameter: p",
;                  7 "Invalid parameter list", 8 "Unexpected parameter", 9
;                  "Can't specify more than 20 params"; its index, the
;                  required count and whether a rest parameter follows &
;   anl-arity      FnExpr.parse, after each method: 10 "Can't have more than
;                  1 variadic overload", 11 "Can't have 2 overloads with same
;                  arity"; anl-arity-end 12 "Can't have fixed arity function
;                  with more params than variadic function"
; The wording, each code's class and the printed form are the shim's
; (anl_refuse); the decision is here.
;
; THE SCOPES, a stobj of records, each record an index below its count:
;   fn      fctr (the frame's slot counter), fout (the block it is written
;           in, -1 at the top), fcap (its newest capture), fvar / fah (its
;           variadic arity's required count, its fixed arities)
;   block   bpar (the enclosing block in the same fn, -1 at a fn's root),
;           bfn, bhead (its newest binding)
;   binding xnm (name), xsl (slot), xblk, xnext (the block's previous one)
;   capture cnm, cout (the slot in the enclosing fn's frame), cin (the slot
;           in this fn's, filled when the closure is made), cbx (the binding
;           it reaches), cnext
; A link always points to an older record (a smaller index), and every walk
; checks it, so each walk ends on any state. Records are only added; the
; analyzer drops a top-level form's records when it is done (anl_top_*).
;
; THE OPERATIONS, each hand-written before (new_fn_scope, child_scope,
; reserve_slots, bind_name, lookup_local, locals_env) and generated now:
;   anl-new-fn / anl-child   a fn's root block / a nested block
;   anl-reserve / anl-bind   slots, and a name bound to one in a block
;   anl-lookup               the slot a name has here: this fn's blocks
;                            innermost first, then its captures, then the fn
;                            it is written in -- where a hit becomes a capture,
;                            a fresh slot here filled from the outer one
;   anl-env                  every name visible, innermost binding winning
;   anl-caps-of / anl-names-of   a fn's capture pairs, its slot names
;
; The theorems are in anlocal-proof.lisp (resolution, captures),
; anlocal-checks.lisp (the checks) and anlocal-cost.lisp (step counts).

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defconst *anl40* 1099511627776)

(defmacro anl40p (x) `(and (natp ,x) (< ,x *anl40*)))

(defun anl-fix (v) (declare (xargs :guard t)) (if (signed-byte-p 64 v) v 0))

(defun anl-nth (i l)
  (declare (xargs :guard t))
  (if (and (natp i) (consp l)) (if (equal i 0) (car l) (anl-nth (- i 1) (cdr l))) nil))

(defun anl-len (l) (declare (xargs :guard t)) (if (consp l) (+ 1 (anl-len (cdr l))) 0))

(defun anl-sat (k) (declare (xargs :guard (natp k))) (if (< k *anl40*) k (- *anl40* 1)))

; ---- THE FORMS -----------------------------------------------------------------------------

(defun frm-kind (x)
  (declare (xargs :guard t))
  (cond ((and (consp x) (eq (car x) :vec)) 1) ((and (consp x) (eq (car x) :sym)) 2) (t 0)))
(defun frm-count (x) (declare (xargs :guard t)) (if (equal (frm-kind x) 1) (anl-sat (anl-len (cdr x))) 0))
(defun frm-nth (x i)
  (declare (xargs :guard t))
  (if (and (equal (frm-kind x) 1) (natp i) (< i (frm-count x))) (anl-nth i (cdr x)) nil))
(defun frm-qual (x) (declare (xargs :guard t)) (if (and (equal (frm-kind x) 2) (equal (anl-nth 2 x) 1)) 1 0))
(defun frm-amp (x) (declare (xargs :guard t)) (if (and (equal (frm-kind x) 2) (equal (anl-nth 3 x) 1)) 1 0))

(defthm frm-reads-int
  (and (natp (frm-kind x)) (natp (frm-count x)) (natp (frm-qual x)) (natp (frm-amp x)))
  :rule-classes ((:type-prescription :corollary (natp (frm-kind x)))
                 (:type-prescription :corollary (natp (frm-count x)))
                 (:type-prescription :corollary (natp (frm-qual x)))
                 (:type-prescription :corollary (natp (frm-amp x)))))

(defthm frm-count-bound (< (frm-count x) *anl40*) :rule-classes :linear)

(in-theory (disable frm-kind frm-count frm-nth frm-qual frm-amp))

; ---- THE CHECKS ----------------------------------------------------------------------------

(defun anl-odd (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (if (equal n 1) 1 (anl-odd (- n 2)))))

; a let*, loop* or letfn* binding vector
(defun anl-shape (bv)
  (declare (xargs :guard t))
  (cond ((not (equal (frm-kind bv) 1)) 1)
        ((equal (anl-odd (frm-count bv)) 1) 2)
        (t 0)))

; a name a let*, loop*, letfn* or catch binds
(defun anl-name-code (x)
  (declare (xargs :guard t))
  (cond ((not (equal (frm-kind x) 2)) 3) ((equal (frm-qual x) 1) 4) (t 0)))

(defun anl-pans (w code i nreq rest)
  (declare (xargs :guard t))
  (cond ((equal w 0) code) ((equal w 1) i) ((equal w 2) nreq) (t rest)))

; FnMethod.parse: st 0 REQ, 1 REST, 2 DONE; w picks the answer: 0 the code,
; 1 where it stopped, 2 the required count, 3 whether a rest parameter came
(defun anl-pw (pv i n st nreq rest w)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))
                  :guard (and (anl40p i) (anl40p n) (natp st) (natp nreq) (<= nreq i) (natp rest) (natp w))))
  (if (and (natp i) (natp n) (< i n))
      (let ((p (frm-nth pv i)))
        (cond ((not (equal (frm-kind p) 2)) (anl-pans w 5 i nreq rest))
              ((equal (frm-qual p) 1) (anl-pans w 6 i nreq rest))
              ((equal (frm-amp p) 1)
               (if (equal st 0) (anl-pw pv (+ 1 i) n 1 nreq rest w) (anl-pans w 7 i nreq rest)))
              ((equal st 0) (anl-pw pv (+ 1 i) n 0 (+ 1 nreq) rest w))
              ((equal st 1) (anl-pw pv (+ 1 i) n 2 nreq 1 w))
              (t (anl-pans w 8 i nreq rest))))
    (if (< 20 (nfix nreq)) (anl-pans w 9 i nreq rest) (anl-pans w 0 i nreq rest))))

(defun anl-params (pv w)
  (declare (xargs :guard (natp w)))
  (anl-pw pv 0 (frm-count pv) 0 0 0 w))

; ---- THE SCOPES ----------------------------------------------------------------------------

(defstobj anls
  (anl-fctr :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-fout :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-fcap :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-fvar :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-fah :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-fnl :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-bpar :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-bfn :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-bhead :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-xnm :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-xsl :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-xblk :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-xnext :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-cnm :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-cout :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-cin :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-cbx :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-cnext :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-nsl :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-nnm :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-nnext :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-an :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-anext :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-ev :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-es :type (array (signed-byte 64) (0)) :initially -1 :resizable t)
  (anl-nf :type (signed-byte 64) :initially 0)
  (anl-nb :type (signed-byte 64) :initially 0)
  (anl-nx :type (signed-byte 64) :initially 0)
  (anl-nc :type (signed-byte 64) :initially 0)
  (anl-na :type (signed-byte 64) :initially 0)
  (anl-nn :type (signed-byte 64) :initially 0)
  (anl-nev :type (signed-byte 64) :initially 0)
  (anl-err :type (signed-byte 64) :initially 0))

; a field's reader and writer: a read of a record below its count, else -1;
; a write inside the array, else the error flag
(defmacro anl-field (a cnt)
  (let* ((nm (symbol-name a))
         (g (intern$ (concatenate 'string "ANL-G-" nm) "ACL2"))
         (s (intern$ (concatenate 'string "ANL-S-" nm) "ACL2"))
         (acc (intern$ (concatenate 'string "ANL-" nm "I") "ACL2"))
         (upd (intern$ (concatenate 'string "UPDATE-ANL-" nm "I") "ACL2"))
         (len (intern$ (concatenate 'string "ANL-" nm "-LENGTH") "ACL2"))
         (p (intern$ (concatenate 'string "ANL-" nm "P") "ACL2"))
         (lem (intern$ (concatenate 'string "ANL-" nm "P-NTH") "ACL2"))
         (lem2 (intern$ (concatenate 'string "ANL-G-" nm "-SB64") "ACL2"))
         (lem3 (intern$ (concatenate 'string "ANL-S-" nm "-ANLSP") "ACL2")))
    `(progn
       (defthm ,(intern$ (concatenate 'string "ANL-" nm "P-UPDATE-NTH") "ACL2")
         (implies (and (,p l) (natp i) (< i (len l)) (signed-byte-p 64 v)) (,p (update-nth i v l))))
       (defthm ,(intern$ (concatenate 'string "ANL-" nm "P-RESIZE") "ACL2")
         (implies (,p l) (,p (resize-list l n -1))))
       (defthm ,lem
         (implies (and (,p l) (natp i) (< i (len l)))
                  (and (integerp (nth i l)) (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808))))
       (defun ,g (i anls)
         (declare (xargs :stobjs anls :guard (signed-byte-p 64 i)))
         (if (and (integerp i) (<= 0 i) (< i (,cnt anls)) (< i (,len anls))) (,acc i anls) -1))
       (defthm ,lem2 (implies (anlsp anls) (and (integerp (,g i anls)) (rationalp (,g i anls)) (acl2-numberp (,g i anls)) (signed-byte-p 64 (,g i anls))))
         :rule-classes (:rewrite (:type-prescription :corollary (implies (anlsp anls) (integerp (,g i anls))))))
       (defthm ,(intern$ (concatenate 'string "ANL-G-" nm "-BOUNDS") "ACL2")
         (implies (anlsp anls) (and (<= -9223372036854775808 (,g i anls)) (< (,g i anls) 9223372036854775808)))
         :rule-classes :linear)
       (defun ,s (i v anls)
         (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 i) (signed-byte-p 64 v))))
         (if (and (integerp i) (<= 0 i) (< i (,len anls))) (,upd i v anls) (update-anl-err 1 anls)))
       (defthm ,lem3 (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (,s i v anls))))
       (defthm ,(intern$ (concatenate 'string "RESIZE-ANL-" nm "-ANLSP") "ACL2")
         (implies (anlsp anls) (anlsp (,(intern$ (concatenate 'string "RESIZE-ANL-" nm) "ACL2") n anls)))))))

(anl-field fctr anl-nf)
(anl-field fout anl-nf)
(anl-field fcap anl-nf)
(anl-field fvar anl-nf)
(anl-field fah anl-nf)
(anl-field fnl anl-nf)
(anl-field bpar anl-nb)
(anl-field bfn anl-nb)
(anl-field bhead anl-nb)
(anl-field xnm anl-nx)
(anl-field xsl anl-nx)
(anl-field xblk anl-nx)
(anl-field xnext anl-nx)
(anl-field cnm anl-nc)
(anl-field cout anl-nc)
(anl-field cin anl-nc)
(anl-field cbx anl-nc)
(anl-field cnext anl-nc)
(anl-field nsl anl-nn)
(anl-field nnm anl-nn)
(anl-field nnext anl-nn)
(anl-field an anl-na)
(anl-field anext anl-na)
(anl-field ev anl-nev)
(anl-field es anl-nev)

(in-theory (disable anl-g-fctr anl-g-fout anl-g-fcap anl-g-fvar anl-g-fah anl-g-fnl anl-g-bpar anl-g-bfn anl-g-bhead anl-g-xnm anl-g-xsl anl-g-xblk anl-g-xnext anl-g-cnm anl-g-cout anl-g-cin anl-g-cbx anl-g-cnext anl-g-nsl anl-g-nnm anl-g-nnext anl-g-an anl-g-anext anl-g-ev anl-g-es
                    anl-s-fctr anl-s-fout anl-s-fcap anl-s-fvar anl-s-fah anl-s-fnl anl-s-bpar anl-s-bfn anl-s-bhead anl-s-xnm anl-s-xsl anl-s-xblk anl-s-xnext anl-s-cnm anl-s-cout anl-s-cin anl-s-cbx anl-s-cnext anl-s-nsl anl-s-nnm anl-s-nnext anl-s-an anl-s-anext anl-s-ev anl-s-es))

(defthm update-anl-nf-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-nf v anls))))
(defthm update-anl-nb-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-nb v anls))))
(defthm update-anl-nx-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-nx v anls))))
(defthm update-anl-nc-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-nc v anls))))
(defthm update-anl-na-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-na v anls))))
(defthm update-anl-nn-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-nn v anls))))
(defthm update-anl-nev-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-nev v anls))))
(defthm update-anl-err-anlsp (implies (and (anlsp anls) (signed-byte-p 64 v)) (anlsp (update-anl-err v anls))))
(defthm anl-counts-sb64 (implies (anlsp anls) (and (signed-byte-p 64 (anl-nf anls)) (integerp (anl-nf anls)) (signed-byte-p 64 (anl-nb anls)) (integerp (anl-nb anls)) (signed-byte-p 64 (anl-nx anls)) (integerp (anl-nx anls)) (signed-byte-p 64 (anl-nc anls)) (integerp (anl-nc anls)) (signed-byte-p 64 (anl-na anls)) (integerp (anl-na anls)) (signed-byte-p 64 (anl-nn anls)) (integerp (anl-nn anls)) (signed-byte-p 64 (anl-nev anls)) (integerp (anl-nev anls)) (signed-byte-p 64 (anl-err anls)) (integerp (anl-err anls))))
  :rule-classes (:rewrite (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-nf anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-nb anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-nx anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-nc anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-na anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-nn anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-nev anls)))) (:type-prescription :corollary (implies (anlsp anls) (integerp (anl-err anls))))))

(defthm anl-counts-bounds (implies (anlsp anls) (and (< (anl-nf anls) 9223372036854775808) (<= -9223372036854775808 (anl-nf anls)) (< (anl-nb anls) 9223372036854775808) (<= -9223372036854775808 (anl-nb anls)) (< (anl-nx anls) 9223372036854775808) (<= -9223372036854775808 (anl-nx anls)) (< (anl-nc anls) 9223372036854775808) (<= -9223372036854775808 (anl-nc anls)) (< (anl-na anls) 9223372036854775808) (<= -9223372036854775808 (anl-na anls)) (< (anl-nn anls) 9223372036854775808) (<= -9223372036854775808 (anl-nn anls)) (< (anl-nev anls) 9223372036854775808) (<= -9223372036854775808 (anl-nev anls)) (< (anl-err anls) 9223372036854775808) (<= -9223372036854775808 (anl-err anls))))
  :rule-classes :linear)
(in-theory (disable update-anl-nf update-anl-nb update-anl-nx update-anl-nc update-anl-na update-anl-nn update-anl-nev update-anl-err anl-nf anl-nb anl-nx anl-nc anl-na anl-nn anl-nev anl-err))
(in-theory (disable anlsp resize-anl-fctr resize-anl-fout resize-anl-fcap resize-anl-fvar resize-anl-fah resize-anl-fnl resize-anl-bpar resize-anl-bfn resize-anl-bhead resize-anl-xnm resize-anl-xsl resize-anl-xblk resize-anl-xnext resize-anl-cnm resize-anl-cout resize-anl-cin resize-anl-cbx resize-anl-cnext resize-anl-nsl resize-anl-nnm resize-anl-nnext resize-anl-an resize-anl-anext resize-anl-ev resize-anl-es))

; room for record n in each of a kind's arrays
(defmacro anl-grow-1 (a n)
  (let* ((nm (symbol-name a))
         (len (intern$ (concatenate 'string "ANL-" nm "-LENGTH") "ACL2"))
         (rs (intern$ (concatenate 'string "RESIZE-ANL-" nm) "ACL2")))
    `(if (< ,n (,len anls)) anls (,rs (+ 16 (* 2 ,n)) anls))))

(defun anl-grow-f (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 fctr n)) (anls (anl-grow-1 fout n)) (anls (anl-grow-1 fcap n))
         (anls (anl-grow-1 fvar n)))
    (let* ((anls (anl-grow-1 fah n))) (anl-grow-1 fnl n))))

(defun anl-grow-b (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 bpar n)) (anls (anl-grow-1 bfn n))) (anl-grow-1 bhead n)))

(defun anl-grow-x (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 xnm n)) (anls (anl-grow-1 xsl n)) (anls (anl-grow-1 xblk n))) (anl-grow-1 xnext n)))

(defun anl-grow-c (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 cnm n)) (anls (anl-grow-1 cout n)) (anls (anl-grow-1 cin n))
         (anls (anl-grow-1 cbx n)))
    (anl-grow-1 cnext n)))

(defun anl-grow-a (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 an n))) (anl-grow-1 anext n)))

(defun anl-grow-n (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 nsl n)) (anls (anl-grow-1 nnm n))) (anl-grow-1 nnext n)))

(defun anl-grow-e (n anls)
  (declare (xargs :stobjs anls :guard (anl40p n)))
  (let* ((anls (anl-grow-1 ev n))) (anl-grow-1 es n)))

(defthm anl-grow-preserves
  (implies (and (anlsp anls) (anl40p n))
           (and (anlsp (anl-grow-f n anls)) (anlsp (anl-grow-b n anls)) (anlsp (anl-grow-x n anls))
                (anlsp (anl-grow-c n anls)) (anlsp (anl-grow-a n anls)) (anlsp (anl-grow-e n anls)) (anlsp (anl-grow-n n anls)))))

(in-theory (disable anl-grow-f anl-grow-b anl-grow-x anl-grow-c anl-grow-a anl-grow-e anl-grow-n))

; a fn written in block o (-1: at the top): its root block
(defun anl-new-fn (o anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 o)))
  (let ((f (anl-nf anls)) (b (anl-nb anls)))
    (if (and (natp f) (< f (- *anl40* 1)) (natp b) (< b (- *anl40* 1)))
        (let* ((anls (anl-grow-f f anls)) (anls (anl-grow-b b anls))
               (anls (anl-s-fctr f 0 anls)) (anls (anl-s-fout f o anls)) (anls (anl-s-fcap f -1 anls))
               (anls (anl-s-fvar f -1 anls)) (anls (anl-s-fah f -1 anls)) (anls (anl-s-fnl f -1 anls)) (anls (update-anl-nf (+ 1 f) anls))
               (anls (anl-s-bpar b -1 anls)) (anls (anl-s-bfn b f anls)) (anls (anl-s-bhead b -1 anls))
               (anls (update-anl-nb (+ 1 b) anls)))
          (mv b anls))
      (let ((anls (update-anl-err 1 anls))) (mv -1 anls)))))

; a block nested in block p, in p's fn
(defun anl-child (p anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 p)))
  (let ((f (anl-g-bfn p anls)) (b (anl-nb anls)))
    (if (and (natp f) (natp b) (< b (- *anl40* 1)))
        (let* ((anls (anl-grow-b b anls))
               (anls (anl-s-bpar b p anls)) (anls (anl-s-bfn b f anls)) (anls (anl-s-bhead b -1 anls))
               (anls (update-anl-nb (+ 1 b) anls)))
          (mv b anls))
      (let ((anls (update-anl-err 1 anls))) (mv -1 anls)))))

; the frame's size so far, of block b's fn
(defun anl-nslots (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (anl-g-fctr (anl-g-bfn b anls) anls))

; n consecutive slots of block b's fn: the first
(defun anl-reserve (b n anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 b) (signed-byte-p 64 n))))
  (let* ((f (anl-g-bfn b anls)) (k (anl-g-fctr f anls)))
    (if (and (natp k) (natp n) (< (+ k n) *anl40*))
        (let ((anls (anl-s-fctr f (+ k n) anls))) (mv k anls))
      (let ((anls (update-anl-err 1 anls))) (mv -1 anls)))))

; slot k the inner slot of a capture in the list from c
(defun anl-cin-has (c k anls)
  (declare (xargs :stobjs anls :measure (nfix c) :guard (and (signed-byte-p 64 c) (signed-byte-p 64 k))))
  (if (and (natp c) (< c (anl-nc anls)))
      (if (equal (anl-g-cin c anls) k) t
        (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (anl-cin-has j k anls) nil)))
    nil))

; fn f's slot k named s, for the debugger: newest first
(defun anl-push-n (f s k anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 f) (signed-byte-p 64 s) (signed-byte-p 64 k))))
  (let ((n (anl-nn anls)))
    (if (and (natp n) (< n (- *anl40* 1)))
        (let* ((anls (anl-grow-n n anls))
               (anls (anl-s-nsl n k anls)) (anls (anl-s-nnm n s anls)) (anls (anl-s-nnext n (anl-g-fnl f anls) anls))
               (anls (update-anl-nn (+ 1 n) anls)))
          (anl-s-fnl f n anls))
      (update-anl-err 1 anls))))

(defthm anl-push-n-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 s) (signed-byte-p 64 k)) (anlsp (anl-push-n f s k anls)))
  :hints (("Goal" :in-theory (disable anl-grow-n))))

; name s bound to slot k in block b: a reserved slot, never a capture's
(defun anl-bind (b s k anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 b) (signed-byte-p 64 s) (signed-byte-p 64 k))))
  (let* ((f (anl-g-bfn b anls)) (n (anl-nx anls)))
    (if (and (natp f) (natp k) (< k (anl-g-fctr f anls)) (not (anl-cin-has (anl-g-fcap f anls) k anls))
             (natp n) (< n (- *anl40* 1)))
        (let* ((anls (anl-grow-x n anls))
               (anls (anl-s-xnm n s anls)) (anls (anl-s-xsl n k anls)) (anls (anl-s-xblk n b anls))
               (anls (anl-s-xnext n (anl-g-bhead b anls) anls)) (anls (update-anl-nx (+ 1 n) anls)))
          (let ((anls (anl-s-bhead b n anls))) (anl-push-n f s k anls)))
      (update-anl-err 2 anls))))

; the binding of name s in the list from x, newest first, or -1
(defun anl-xfind (x s anls)
  (declare (xargs :stobjs anls :measure (nfix x) :guard (and (signed-byte-p 64 x) (signed-byte-p 64 s))))
  (if (and (natp x) (< x (anl-nx anls)))
      (if (equal (anl-g-xnm x anls) s) x
        (let ((j (anl-g-xnext x anls))) (if (and (natp j) (< j x)) (anl-xfind j s anls) -1)))
    -1))

; ... in block b and the blocks around it in its fn
(defun anl-chain-find (b s anls)
  (declare (xargs :stobjs anls :measure (nfix b) :guard (and (signed-byte-p 64 b) (signed-byte-p 64 s))))
  (if (and (natp b) (< b (anl-nb anls)))
      (let ((x (anl-xfind (anl-g-bhead b anls) s anls)))
        (if (<= 0 x) x
          (let ((p (anl-g-bpar b anls))) (if (and (natp p) (< p b)) (anl-chain-find p s anls) -1))))
    -1))

; the capture of name s in the list from c, or -1
(defun anl-cfind (c s anls)
  (declare (xargs :stobjs anls :measure (nfix c) :guard (and (signed-byte-p 64 c) (signed-byte-p 64 s))))
  (if (and (natp c) (< c (anl-nc anls)))
      (if (equal (anl-g-cnm c anls) s) c
        (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (anl-cfind j s anls) -1)))
    -1))

; fn f captures name s, binding bx, from slot k of the fn around it, into slot
(defun anl-push-c (f s k slot bx anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 f) (signed-byte-p 64 s) (signed-byte-p 64 k)
                                           (signed-byte-p 64 slot) (signed-byte-p 64 bx))))
  (let ((c (anl-nc anls)))
    (if (and (natp c) (< c (- *anl40* 1)))
        (let* ((anls (anl-grow-c c anls))
               (anls (anl-s-cnm c s anls)) (anls (anl-s-cout c k anls)) (anls (anl-s-cin c slot anls))
               (anls (anl-s-cbx c bx anls)) (anls (anl-s-cnext c (anl-g-fcap f anls) anls))
               (anls (update-anl-nc (+ 1 c) anls)))
          (let ((anls (anl-s-fcap f c anls))) (anl-push-n f s slot anls)))
      (update-anl-err 1 anls))))

(defthm anl-push-c-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 s) (signed-byte-p 64 k) (signed-byte-p 64 slot) (signed-byte-p 64 bx))
           (anlsp (anl-push-c f s k slot bx anls)))
  :hints (("Goal" :in-theory (disable anl-grow-c anl-push-n))))

(defthm anl-xfind-int (integerp (anl-xfind x s anls)) :rule-classes :type-prescription)
(defthm anl-xfind-lo (<= -1 (anl-xfind x s anls)) :rule-classes :linear)
(defthm anl-xfind-hi (implies (<= 0 (anl-xfind x s anls)) (< (anl-xfind x s anls) (anl-nx anls))) :rule-classes :linear)
(defthm anl-chain-find-int (integerp (anl-chain-find b s anls)) :rule-classes :type-prescription)
(defthm anl-chain-find-lo (<= -1 (anl-chain-find b s anls)) :rule-classes :linear)
(defthm anl-chain-find-hi (implies (<= 0 (anl-chain-find b s anls)) (< (anl-chain-find b s anls) (anl-nx anls)))
  :rule-classes :linear)
(defthm anl-cfind-int (integerp (anl-cfind c s anls)) :rule-classes :type-prescription)
(defthm anl-cfind-lo (<= -1 (anl-cfind c s anls)) :rule-classes :linear)
(defthm anl-cfind-hi (implies (<= 0 (anl-cfind c s anls)) (< (anl-cfind c s anls) (anl-nc anls))) :rule-classes :linear)
(in-theory (disable anl-xfind anl-chain-find anl-cfind))
; THE LOOKUP: the slot name s has in block b's fn, and the binding it is,
; or -1 -1. A binding in the fn's blocks, innermost first; else a capture
; the fn has; else the fn written in block o: a hit there is captured, a
; fresh slot here -- transitively, as each fn around resolves the same way.
(defun anl-lookup (b s anls)
  (declare (xargs :stobjs anls :measure (nfix b) :guard (and (signed-byte-p 64 b) (signed-byte-p 64 s))
                  :verify-guards nil))
  (let ((x (anl-chain-find b s anls)))
    (if (<= 0 x) (mv (anl-g-xsl x anls) x anls)
      (let* ((f (anl-g-bfn b anls)) (o (anl-g-fout f anls)))
        ; a fn written in a block, of a fn before it, has captures to look in
        (if (and (natp b) (natp o) (< o b) (< (anl-g-bfn o anls) f))
            (let ((c (anl-cfind (anl-g-fcap f anls) s anls)))
              (if (<= 0 c) (mv (anl-g-cin c anls) (anl-g-cbx c anls) anls)
                (mv-let (k bx anls) (anl-lookup o s anls)
                  (if (< bx 0) (mv -1 -1 anls)
                    (let ((slot (anl-g-fctr f anls)))
                      (if (and (natp slot) (< slot (- *anl40* 1)))
                          (let* ((anls (anl-s-fctr f (+ 1 slot) anls)) (anls (anl-push-c f s k slot bx anls)))
                            (mv slot bx anls))
                        (let ((anls (update-anl-err 1 anls))) (mv -1 -1 anls))))))))
          (mv -1 -1 anls))))))
(defthm anl-lookup-types
  (implies (and (anlsp anls) (signed-byte-p 64 s))
           (and (signed-byte-p 64 (mv-nth 0 (anl-lookup b s anls))) (signed-byte-p 64 (mv-nth 1 (anl-lookup b s anls)))
                (anlsp (mv-nth 2 (anl-lookup b s anls)))))
  :hints (("Goal" :induct (anl-lookup b s anls)
           :in-theory (disable anl-push-c))))

(defthm anl-lookup-int
  (implies (and (anlsp anls) (signed-byte-p 64 s))
           (and (integerp (car (anl-lookup b s anls))) (signed-byte-p 64 (car (anl-lookup b s anls)))
                (integerp (mv-nth 1 (anl-lookup b s anls)))))
  :hints (("Goal" :use anl-lookup-types :in-theory (disable anl-lookup-types anl-lookup))))
(verify-guards anl-lookup
  :hints (("Goal" :in-theory (disable anl-push-c anl-s-fctr))))

; ---- ARITIES -------------------------------------------------------------------------------

(defun anl-has-fixed (a n anls)
  (declare (xargs :stobjs anls :measure (nfix a) :guard (and (signed-byte-p 64 a) (signed-byte-p 64 n))))
  (if (and (natp a) (< a (anl-na anls)))
      (if (equal (anl-g-an a anls) n) t
        (let ((j (anl-g-anext a anls))) (if (and (natp j) (< j a)) (anl-has-fixed j n anls) nil)))
    nil))

(defun anl-gt-fixed (a n anls)
  (declare (xargs :stobjs anls :measure (nfix a) :guard (and (signed-byte-p 64 a) (signed-byte-p 64 n))))
  (if (and (natp a) (< a (anl-na anls)))
      (if (< n (anl-g-an a anls)) t
        (let ((j (anl-g-anext a anls))) (if (and (natp j) (< j a)) (anl-gt-fixed j n anls) nil)))
    nil))

; a method of nreq required parameters (and a rest one when rest is 1) of
; block b's fn, after its body: 0, 10 a second variadic one, 11 a fixed
; arity already there
; fn f has a fixed arity of n required parameters: at the head of its list
(defun anl-push-a (f n anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 f) (signed-byte-p 64 n))))
  (let ((a (anl-na anls)))
    (if (and (natp a) (< a (- *anl40* 1)))
        (let* ((anls (anl-grow-a a anls)) (anls (anl-s-an a n anls))
               (anls (anl-s-anext a (anl-g-fah f anls) anls)) (anls (update-anl-na (+ 1 a) anls)))
          (anl-s-fah f a anls))
      (update-anl-err 1 anls))))

(defthm anl-push-a-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 n)) (anlsp (anl-push-a f n anls)))
  :hints (("Goal" :in-theory (disable anl-grow-a))))

(defun anl-arity (b nreq rest anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 b) (signed-byte-p 64 nreq) (signed-byte-p 64 rest))))
  (let ((f (anl-g-bfn b anls)))
    (cond ((not (natp f)) (let ((anls (update-anl-err 1 anls))) (mv 0 anls)))
          ((equal rest 1)
           (if (<= 0 (anl-g-fvar f anls)) (mv 10 anls) (let ((anls (anl-s-fvar f nreq anls))) (mv 0 anls))))
          ((anl-has-fixed (anl-g-fah f anls) nreq anls) (mv 11 anls))
          (t (let ((anls (anl-push-a f nreq anls))) (mv 0 anls))))))

; after the last method: 12 a fixed arity above the variadic one's
(defun anl-arity-end (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (let* ((f (anl-g-bfn b anls)) (v (anl-g-fvar f anls)))
    (if (and (<= 0 v) (anl-gt-fixed (anl-g-fah f anls) v anls)) 12 0)))

; ---- WHAT THE ANALYZER READS BACK ----------------------------------------------------------
;
; Into ev / es, nev of them: the shim turns them into the map or vector the
; analyzer keeps.

; where name s is in ev, from i on, or -1
(defun anl-ev-find (i s anls)
  (declare (xargs :stobjs anls :measure (nfix (- (nfix (anl-nev anls)) (nfix i)))
                  :guard (and (signed-byte-p 64 i) (signed-byte-p 64 s))))
  (if (and (natp i) (natp (anl-nev anls)) (< i (anl-nev anls)))
      (if (equal (anl-g-ev i anls) s) i (anl-ev-find (+ 1 i) s anls))
    -1))

(defthm anl-ev-find-int (integerp (anl-ev-find i s anls)) :rule-classes :type-prescription)
(defthm anl-ev-find-lo (<= -1 (anl-ev-find i s anls)) :rule-classes :linear)
(defthm anl-ev-find-hi (implies (<= 0 (anl-ev-find i s anls)) (< (anl-ev-find i s anls) (anl-nev anls)))
  :rule-classes :linear)

(defun anl-push-e (s k anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 s) (signed-byte-p 64 k))))
  (let ((n (anl-nev anls)))
    (if (and (natp n) (< n (- *anl40* 1)))
        (let* ((anls (anl-grow-e n anls)) (anls (anl-s-ev n s anls)) (anls (anl-s-es n k anls)))
          (update-anl-nev (+ 1 n) anls))
      (update-anl-err 1 anls))))

(defthm anl-push-e-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 s) (signed-byte-p 64 k)) (anlsp (anl-push-e s k anls))))

; name s at slot k, as an array map is assoc'ed: new, it goes at the end;
; already there from this block (at lo or after), its slot is the new one;
; there from a block inside, the inner one stays
(defun anl-env-put (s k lo anls)
  (declare (xargs :stobjs anls :guard (and (signed-byte-p 64 s) (signed-byte-p 64 k) (signed-byte-p 64 lo))))
  (let ((i (anl-ev-find 0 s anls)))
    (cond ((< i 0) (anl-push-e s k anls))
          ((<= lo i) (anl-s-es i k anls))
          (t anls))))

(defthm anl-env-put-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 s) (signed-byte-p 64 k)) (anlsp (anl-env-put s k lo anls))))

; a block's bindings, oldest first (the order its map had them in)
(defun anl-env-x (x lo anls)
  (declare (xargs :stobjs anls :measure (nfix x) :ruler-extenders :all :verify-guards nil :guard (and (signed-byte-p 64 x) (signed-byte-p 64 lo))))
  (if (and (natp x) (< x (anl-nx anls)))
      (let* ((j (anl-g-xnext x anls))
             (anls (if (and (natp j) (< j x)) (anl-env-x j lo anls) anls)))
        (anl-env-put (anl-g-xnm x anls) (anl-g-xsl x anls) lo anls))
    anls))

(defthm anl-env-x-anlsp (implies (anlsp anls) (anlsp (anl-env-x x lo anls)))
  :hints (("Goal" :in-theory (disable anl-env-put))))
(verify-guards anl-env-x)

; a fn's captures, oldest first, a name already there staying
(defun anl-env-c (c anls)
  (declare (xargs :stobjs anls :measure (nfix c) :ruler-extenders :all :verify-guards nil :guard (signed-byte-p 64 c)))
  (if (and (natp c) (< c (anl-nc anls)))
      (let* ((j (anl-g-cnext c anls))
             (anls (if (and (natp j) (< j c)) (anl-env-c j anls) anls))
             (s (anl-g-cnm c anls)))
        (if (<= 0 (anl-ev-find 0 s anls)) anls (anl-push-e s (anl-g-cin c anls) anls)))
    anls))

(defthm anl-env-c-anlsp (implies (anlsp anls) (anlsp (anl-env-c c anls)))
  :hints (("Goal" :in-theory (disable anl-push-e))))
(verify-guards anl-env-c)

(defun anl-env-b (b anls)
  (declare (xargs :stobjs anls :measure (nfix b) :guard (signed-byte-p 64 b)))
  (if (and (natp b) (< b (anl-nb anls)))
      (let* ((anls (anl-env-x (anl-g-bhead b anls) (anl-nev anls) anls)) (p (anl-g-bpar b anls)))
        (if (and (natp p) (< p b)) (anl-env-b p anls) anls))
    anls))

(defthm anl-env-b-anlsp (implies (anlsp anls) (anlsp (anl-env-b b anls)))
  :hints (("Goal" :in-theory (disable anl-env-x))))

(defun anl-env-from (b anls)
  (declare (xargs :stobjs anls :measure (nfix b) :guard (signed-byte-p 64 b)))
  (let* ((anls (anl-env-b b anls)) (f (anl-g-bfn b anls)) (anls (anl-env-c (anl-g-fcap f anls) anls))
         (o (anl-g-fout f anls)))
    (if (and (natp b) (natp o) (< o b) (< (anl-g-bfn o anls) f)) (anl-env-from o anls) anls)))

(defthm anl-env-from-anlsp (implies (anlsp anls) (anlsp (anl-env-from b anls)))
  :hints (("Goal" :in-theory (disable anl-env-b anl-env-c))))

; every name visible in block b, the innermost binding's slot each
(defun anl-env (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (let ((anls (update-anl-nev 0 anls))) (anl-env-from b anls)))

(defun anl-caps-c (c anls)
  (declare (xargs :stobjs anls :measure (nfix c) :guard (signed-byte-p 64 c)))
  (if (and (natp c) (< c (anl-nc anls)))
      (let* ((anls (anl-push-e (anl-g-cout c anls) (anl-g-cin c anls) anls)) (j (anl-g-cnext c anls)))
        (if (and (natp j) (< j c)) (anl-caps-c j anls) anls))
    anls))

(defthm anl-caps-c-anlsp (implies (anlsp anls) (anlsp (anl-caps-c c anls)))
  :hints (("Goal" :in-theory (disable anl-push-e))))

; block b's fn's captures, newest first: the outer slot in ev, the inner in es
(defun anl-caps-of (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (let* ((c (anl-g-fcap (anl-g-bfn b anls) anls)) (anls (update-anl-nev 0 anls))) (anl-caps-c c anls)))

(defun anl-names-n (n anls)
  (declare (xargs :stobjs anls :measure (nfix n) :guard (signed-byte-p 64 n)))
  (if (and (natp n) (< n (anl-nn anls)))
      (let* ((anls (anl-push-e (anl-g-nnm n anls) (anl-g-nsl n anls) anls)) (j (anl-g-nnext n anls)))
        (if (and (natp j) (< j n)) (anl-names-n j anls) anls))
    anls))

; block b's fn's named slots, newest first: the name in ev, the slot in es
(defun anl-names-of (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (let* ((n (anl-g-fnl (anl-g-bfn b anls) anls)) (anls (update-anl-nev 0 anls))) (anl-names-n n anls)))

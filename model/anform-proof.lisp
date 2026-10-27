; THE ANALYZER'S SPECIAL FORMS, PROVED: the node each special form builds
; (src/f/analyze.inc's analyze_if, analyze_def, analyze_let, analyze_fn,
; analyze_try and the rest), driven by the generated checks of
; model/anform.lisp and the generated locals of model/anlocal.lisp, is a
; node anpass's reads decode as its passes assume (model/anpass.lisp); a
; symbol's local is anlocal's lookup, the binding its lexical meaning is;
; and the checks refuse exactly what their specifications -- clj's parsers,
; stated apart -- refuse.
;
; THE ANALYZER here is one step of it, anf-step: the node a form makes,
; given what analysing its subforms answers. A subform is analysed by
; anf-sub, constrained, not defined: it stands for the analyzer itself on a
; smaller form (and for what is the host's -- a call, a collection, a
; literal, a macro expanded through the evaluator, a var resolved), answering
; an error code, a node and the locals. Its one constraint, that a node it
; answers with no error is well-formed, is anf-step-wf itself one form
; down: anf-step-wf is the induction step of "every tree the analyzer
; builds is well-formed", by induction on the form's depth. What is
; modelled, as clotran's analyzer builds it (Eval.f90's N_* kinds):
;   a symbol    N_LOCAL of the slot anl-lookup answers, when it finds a
;               binding; else the host's (a var)
;   if          N_IF, its two or three forms; do N_DO
;   def         N_DEF, its init if it has one (anf-def says where), i2 the
;               number of inits plus 2 for defmacro*
;   quote       N_CONST; var N_VAR; throw N_THROW, its one form
;   let* loop*  a child block, the slots reserved, each name checked
;               (anl-name-code), its init analysed in the block, then bound;
;               the body in the block: N_LET / N_LOOP, the inits then the
;               body, i2 their number, slot 3 the first slot
;   letfn*      every name bound first, then each fn and the body: N_LETFN
;   fn*         a fn's root block (anl-new-fn), each method a child block
;               of it, its parameters checked (anl-params), reserved and
;               bound, its arity recorded (anl-arity); after the last, the
;               variadic check (anl-arity-end): N_FN, its bodies apart (the
;               shim's template), no children
;   recur       N_RECUR, its arguments, i2 their number
;   try         the body forms before the first clause analysed, then each
;               clause as TryExpr walks it (anf-try-step): a catch's class
;               and name checked (anf-catch), the name bound in a child
;               block, its handler; the finally: N_TRY, [body, finally or
;               nil], the handlers its alternatives
;   set!        N_SETBANG, the value (a var or local target) or the object
;               and the value (a field target)
;   . / new     N_DOT, the target then the arguments; N_NEW its arguments
; Not modelled: a fn's own name (bound to its self slot by the shim), a
; def's metadata (analysed by the host), a fn's captures (anlocal's,
; anl-caps-of: anl-lookup-caps-own proves them exactly the free locals),
; prim kinds and array hints (a later lane), and a local named like a
; special form, which the shim treats as a call before asking the head.
;
; Theorems:
;   anf-step-wf       a node anf-step answers with no error is well-formed
;                     (anf-wf): its kind one of the analyzer's, its children
;                     as many as its kind has (an if two or three, a let one
;                     more than i2, a throw one, a try two, ...), each
;                     well-formed -- so anpass's passes read it as their
;                     theorems assume
;   anf-step-local    a symbol bound locally is N_LOCAL of anl-lookup's slot,
;                     and the binding found is its lexical meaning (anl-lex),
;                     given anlocal's invariant (anl-ccc)
;   anf-try-code-spec the try's walk refuses exactly the clause lists the
;                     grammar body* catch* finally? does not generate
;   anf-dot-member-spec  the member is refused exactly when HostExpr.Parser's
;                     call (the third form if a seq, else the rest from it)
;                     does not begin with a symbol, and it is no field
;   anf-def-places    an accepted def's init and docstring are where
;                     DefExpr.Parser takes them

(in-package "ACL2")

(include-book "anform")
(include-book "anlocal-proof")
(include-book "anpass")

; ---- THE TREE THE ANALYZER BUILDS ------------------------------------------------------------

; anpass's node (:ast id kind i2 kids s3 caps alts rfn), and a fn's bodies after it
(defun anf-node (kind i2 kids s3 alts) (declare (xargs :guard t)) (list :ast 0 kind i2 kids s3 nil alts 0))
(defun anf-fn-node (bodies) (declare (xargs :guard t)) (list :ast 0 14 0 nil nil nil nil 0 bodies))

(defthm anf-node-reads
  (implies (and (integerp kind) (not (equal kind 0)) (signed-byte-p 64 kind))
           (and (ast-p (anf-node kind i2 kids s3 alts)) (equal (ast-kind (anf-node kind i2 kids s3 alts)) kind)))
  :hints (("Goal" :in-theory (enable ast-p ast-kind))))

; the kinds the analyzer makes, and how many children each has
(defun anf-kind-ok (k i2 nk)
  (cond ((member k '(1 2 3 14)) (equal nk 0))
        ((equal k 4) (or (equal nk 2) (equal nk 3)))
        ((equal k 10) (and (natp i2) (<= i2 3) (equal nk (mod i2 2))))
        ((member k '(11 12 13)) (and (natp i2) (equal nk (+ 1 i2))))
        ((equal k 16) (and (natp i2) (equal nk i2)))
        ((equal k 17) (equal nk 1))
        ((equal k 18) (equal nk 2))
        ((equal k 24) (or (equal nk 1) (equal nk 2)))
        ; a do, a dot, a new, and the host's: a call, a collection, a lazy
        ; seq, a case, a deftype, a new of one, a failure, a late var
        ((member k '(5 6 7 8 9 15 19 20 21 22 23 25 28)) t)
        (t nil)))

(defthm anf-nth-count (implies (consp x) (< (acl2-count (nth n x)) (acl2-count x)))
  :rule-classes :linear)
(defthm anf-car-count (<= (acl2-count (car l)) (acl2-count l)) :rule-classes :linear)
(defthm anf-cdr-count (<= (acl2-count (cdr l)) (acl2-count l)) :rule-classes :linear)

(mutual-recursion
 (defun anf-wf (x)
   (declare (xargs :measure (acl2-count x)))
   (and (consp x) (eq (car x) :ast)
        (let ((k (nth 2 x)) (i2 (nth 3 x)) (kids (nth 4 x)))
          (and (anf-kind-ok k i2 (len kids))
               (if (equal k 18)
                   (and (anf-wf (car kids)) (or (null (cadr kids)) (anf-wf (cadr kids))))
                 (anf-wfs kids))
               (anf-wfs (nth 7 x))
               (if (equal k 14) (anf-wfs (nth 9 x)) t)))))
 (defun anf-wfs (l)
   (declare (xargs :measure (acl2-count l)))
   (if (atom l) (null l) (and (anf-wf (car l)) (anf-wfs (cdr l))))))

(defthm anf-kind-ok-kind (implies (anf-kind-ok k i2 nk) (and (integerp k) (<= 1 k) (<= k 28)))
  :rule-classes :forward-chaining)
(defthm anp-nth-is-nth (implies (natp i) (equal (anp-nth i l) (nth i l))))

(defthm anf-wf-ast-p (implies (anf-wf x) (ast-p x))
  :hints (("Goal" :expand ((anf-wf x)) :in-theory (e/d (ast-p) (anf-kind-ok)))))

(defthm anf-len-append (equal (len (append a b)) (+ (len a) (len b))))
(defthm anf-wfs-append (implies (true-listp a) (equal (anf-wfs (append a b)) (and (anf-wfs a) (anf-wfs b)))))
(defthm anf-wfs-true-listp (implies (anf-wfs l) (true-listp l)) :rule-classes :forward-chaining)

; ---- WHAT ANALYSING A SUBFORM ANSWERS ------------------------------------------------------------

(encapsulate
  (((anf-sub * * anls) => (mv * * anls)))
  (local (defun anf-sub (x b anls) (declare (xargs :stobjs anls) (ignore x b)) (mv 0 (anf-node 1 0 nil nil nil) anls)))
  (defthm anf-sub-wf
    (implies (equal (mv-nth 0 (anf-sub x b anls)) 0) (anf-wf (mv-nth 1 (anf-sub x b anls))))))

; the host's read of a list's head: 1 if, 2 do, 3 def, 4 quote, 5 throw,
; 6 try, 7 set!, 8 ., 9 new, 10 var, 11 let*, 12 loop*, 13 recur, 14 fn*,
; 15 letfn*, 16 defmacro*, else 0 (analyze_special's dispatch on the name)
(defun anf-sp (x) (if (equal (frm-kind x) 2) (nfix (nth 7 x)) 0))

; forms in order, each in block b, stopping at the first error
(defun anf-subs (xs b anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (if (atom xs) (mv 0 nil anls)
    (mv-let (e n anls) (anf-sub (car xs) b anls)
      (if (not (equal e 0)) (mv e nil anls)
        (mv-let (e ns anls) (anf-subs (cdr xs) b anls) (mv e (cons n ns) anls))))))

(defthm anf-subs-wf
  (implies (equal (mv-nth 0 (anf-subs xs b anls)) 0)
           (and (anf-wfs (mv-nth 1 (anf-subs xs b anls))) (true-listp (mv-nth 1 (anf-subs xs b anls)))))
  :hints (("Goal" :induct (anf-subs xs b anls))))

(defun anf-body (xs b anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (mv-let (e ns anls) (anf-subs xs b anls) (mv e (anf-node 5 0 ns nil nil) anls)))

(defthm anf-body-wf
  (implies (equal (mv-nth 0 (anf-body xs b anls)) 0) (anf-wf (mv-nth 1 (anf-body xs b anls)))))

; ---- THE BINDING FORMS -------------------------------------------------------------------------

; let* / loop*: each name checked, its init analysed in block c, then bound to slot k
(defun anf-binds (ps c k anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (if (or (atom ps) (atom (cdr ps))) (mv 0 nil anls)
    (let ((code (anl-name-code (car ps))))
      (if (not (equal code 0)) (mv code nil anls)
        (mv-let (e n anls) (anf-sub (cadr ps) c anls)
          (if (not (equal e 0)) (mv e nil anls)
            (let ((anls (anl-bind c (nth 1 (car ps)) k anls)))
              (mv-let (e ns anls) (anf-binds (cddr ps) c (+ 1 k) anls) (mv e (cons n ns) anls)))))))))

(defthm anf-binds-wf
  (implies (equal (mv-nth 0 (anf-binds ps c k anls)) 0)
           (and (anf-wfs (mv-nth 1 (anf-binds ps c k anls))) (true-listp (mv-nth 1 (anf-binds ps c k anls)))))
  :hints (("Goal" :induct (anf-binds ps c k anls) :in-theory (disable anl-bind anl-name-code))))

; letfn*: every name first, each checked, bound to slots k on
(defun anf-names (ps c k anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (if (or (atom ps) (atom (cdr ps))) (mv 0 anls)
    (let ((code (anl-name-code (car ps))))
      (if (not (equal code 0)) (mv code anls)
        (let ((anls (anl-bind c (nth 1 (car ps)) k anls))) (anf-names (cddr ps) c (+ 1 k) anls))))))

(defun anf-inits (ps) (if (or (atom ps) (atom (cdr ps))) nil (cons (cadr ps) (anf-inits (cddr ps)))))

(defun anf-let (x b kind anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (let* ((bv (frf-nth x 1)) (code (anl-shape bv)))
    (if (not (equal code 0)) (mv code nil anls)
      (mv-let (c anls) (anl-child b anls)
        (mv-let (start anls) (anl-reserve c (floor (len (cdr bv)) 2) anls)
          (mv-let (e inits anls)
            (if (equal kind 13)
                (mv-let (e anls) (anf-names (cdr bv) c start anls)
                  (if (not (equal e 0)) (mv e nil anls) (anf-subs (anf-inits (cdr bv)) c anls)))
              (anf-binds (cdr bv) c start anls))
            (if (not (equal e 0)) (mv e nil anls)
              (mv-let (e body anls) (anf-body (cdddr x) c anls)
                (if (not (equal e 0)) (mv e nil anls)
                  (mv 0 (anf-node kind (len inits) (append inits (list body)) start nil) anls))))))))))

(defthm anf-let-wf
  (implies (and (member kind '(11 12 13)) (equal (mv-nth 0 (anf-let x b kind anls)) 0))
           (anf-wf (mv-nth 1 (anf-let x b kind anls))))
  :hints (("Goal" :in-theory (disable anl-child anl-reserve anl-shape anf-names anf-binds anf-subs anf-body))))

; a method's parameters bound, & skipped, slots k on
(defun anf-params-bind (ps c k anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (cond ((atom ps) anls)
        ((equal (frm-amp (car ps)) 1) (anf-params-bind (cdr ps) c k anls))
        (t (let ((anls (anl-bind c (nth 1 (car ps)) k anls))) (anf-params-bind (cdr ps) c (+ 1 k) anls)))))

; fn*'s methods, each ([params] body*), in blocks under the fn's root r
(defun anf-methods (ms r anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (if (atom ms) (mv (anl-arity-end r anls) nil anls)
    (let* ((m (car ms)) (pv (frf-nth m 0)) (code (anl-params pv 0)))
      (if (not (equal code 0)) (mv code nil anls)
        (let ((nreq (anl-params pv 2)) (rest (anl-params pv 3)))
          (mv-let (mb anls) (anl-child r anls)
            (mv-let (start anls) (anl-reserve mb (+ nreq rest) anls)
              (let ((anls (anf-params-bind (cdr pv) mb start anls)))
                (mv-let (code anls) (anl-arity r nreq rest anls)
                  (if (not (equal code 0)) (mv code nil anls)
                    (mv-let (e body anls) (anf-body (cddr m) mb anls)
                      (if (not (equal e 0)) (mv e nil anls)
                        (mv-let (e bodies anls) (anf-methods (cdr ms) r anls)
                          (mv e (cons body bodies) anls))))))))))))))

(defthm anf-methods-wf
  (implies (equal (mv-nth 0 (anf-methods ms r anls)) 0)
           (and (anf-wfs (mv-nth 1 (anf-methods ms r anls))) (true-listp (mv-nth 1 (anf-methods ms r anls)))))
  :hints (("Goal" :induct (anf-methods ms r anls)
           :in-theory (disable anl-child anl-reserve anl-arity anl-arity-end anl-params anf-params-bind anf-body))))

(defun anf-fn (x b anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (let* ((xs (cddr x)) (xs (if (equal (frm-kind (car xs)) 2) (cdr xs) xs))
         (ms (if (equal (frm-kind (car xs)) 1) (list (cons :list xs)) xs)))
    (mv-let (r anls) (anl-new-fn b anls)
      (mv-let (e bodies anls) (anf-methods ms r anls)
        (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-fn-node bodies) anls))))))

(defthm anf-fn-wf
  (implies (equal (mv-nth 0 (anf-fn x b anls)) 0) (anf-wf (mv-nth 1 (anf-fn x b anls))))
  :hints (("Goal" :in-theory (disable anf-methods anl-new-fn))))

; ---- TRY -----------------------------------------------------------------------------------------

; the forms before the first clause, and the clauses from it
(defun anf-try-body (cls) (if (or (atom cls) (not (equal (anf-try-op (car cls)) 0))) nil (cons (car cls) (anf-try-body (cdr cls)))))
(defun anf-try-rest (cls) (if (or (atom cls) (not (equal (anf-try-op (car cls)) 0))) cls (anf-try-rest (cdr cls))))

; TryExpr's walk from the first clause: st 0 before a catch, 1 after;
; the catches' handlers and the finally
(defun anf-try-walk (cls st b anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (if (atom cls) (mv 0 nil nil anls)
    (let* ((f (car cls)) (lastp (if (atom (cdr cls)) 1 0))
           (code (anf-try-step st f lastp 0)) (op (anf-try-step st f lastp 1)) (st2 (anf-try-step st f lastp 2)))
      (cond ((not (equal code 0)) (mv code nil nil anls))
            ((equal op 1)
             (let ((code (anf-catch f)))
               (if (not (equal code 0)) (mv code nil nil anls)
                 (mv-let (c anls) (anl-child b anls)
                   (mv-let (slot anls) (anl-reserve c 1 anls)
                     (let ((anls (anl-bind c (nth 1 (frf-nth f 2)) slot anls)))
                       (mv-let (e h anls) (anf-body (nthcdr 4 f) c anls)
                         (if (not (equal e 0)) (mv e nil nil anls)
                           (mv-let (e hs fin anls) (anf-try-walk (cdr cls) st2 b anls)
                             (mv e (cons h hs) fin anls))))))))))
            ((equal op 2)
             (mv-let (e fin anls) (anf-body (cddr f) b anls)
               (if (not (equal e 0)) (mv e nil nil anls) (mv 0 nil fin anls))))
            (t (anf-try-walk (cdr cls) st2 b anls))))))

(defthm anf-try-walk-wf
  (implies (equal (mv-nth 0 (anf-try-walk cls st b anls)) 0)
           (and (anf-wfs (mv-nth 1 (anf-try-walk cls st b anls)))
                (implies (mv-nth 2 (anf-try-walk cls st b anls)) (anf-wf (mv-nth 2 (anf-try-walk cls st b anls))))))
  :hints (("Goal" :induct (anf-try-walk cls st b anls)
           :in-theory (disable anf-try-step anf-catch anf-body anl-child anl-reserve anl-bind))))

(defun anf-try (x b anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (let ((cls (cddr x)))
    (mv-let (e body anls) (anf-body (anf-try-body cls) b anls)
      (if (not (equal e 0)) (mv e nil anls)
        (mv-let (e hs fin anls) (anf-try-walk (anf-try-rest cls) 0 b anls)
          (if (not (equal e 0)) (mv e nil anls)
            (mv 0 (anf-node 18 0 (list body fin) nil hs) anls)))))))

(defthm anf-try-wf
  (implies (equal (mv-nth 0 (anf-try x b anls)) 0) (anf-wf (mv-nth 1 (anf-try x b anls))))
  :hints (("Goal" :in-theory (disable anf-body anf-try-walk))))

; ---- ONE STEP OF THE ANALYZER ----------------------------------------------------------------------

(defun anf-step (x b anls)
  (declare (xargs :stobjs anls :verify-guards nil :normalize nil))
  (cond
   ((equal (frm-kind x) 2)
    (mv-let (slot bx anls) (anl-lookup b (nth 1 x) anls)
      (if (<= 0 bx) (mv 0 (anf-node 2 slot nil nil nil) anls) (anf-sub x b anls))))
   ((not (equal (frf-kind x) 3)) (anf-sub x b anls))
   (t
    (let ((sp (anf-sp (frf-nth x 0))) (n (frf-len x)) (args (cddr x)))
      (case sp
        (1 (let ((code (anf-if n)))
             (if (not (equal code 0)) (mv code nil anls)
               (mv-let (e kids anls) (anf-subs args b anls)
                 (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 4 0 kids nil nil) anls))))))
        (2 (anf-body args b anls))
        ((3 16) (let ((code (anf-def x 0)) (init (anf-def x 1)) (mac (if (equal sp 16) 2 0)))
                  (cond ((not (equal code 0)) (mv code nil anls))
                        ((< 0 init)
                         (mv-let (e v anls) (anf-sub (frf-nth x init) b anls)
                           (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 10 (+ 1 mac) (list v) nil nil) anls))))
                        (t (mv 0 (anf-node 10 mac nil nil nil) anls)))))
        (4 (let ((code (anf-quote n))) (if (not (equal code 0)) (mv code nil anls) (mv 0 (anf-node 1 0 nil nil nil) anls))))
        (5 (let ((code (anf-throw n)))
             (if (not (equal code 0)) (mv code nil anls)
               (mv-let (e v anls) (anf-sub (frf-nth x 1) b anls)
                 (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 17 0 (list v) nil nil) anls))))))
        (6 (anf-try x b anls))
        (7 (let* ((code (anf-set n)) (code (if (equal code 0) (anf-set-target (frf-nth x 1)) code)))
             (if (not (equal code 0)) (mv code nil anls)
               (mv-let (e v anls) (anf-sub (frf-nth x 2) b anls)
                 (cond ((not (equal e 0)) (mv e nil anls))
                       ((equal (frf-kind (frf-nth x 1)) 3)
                        (mv-let (e o anls) (anf-sub (frf-nth (frf-nth x 1) 1) b anls)
                          (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 24 2 (list o v) nil nil) anls))))
                       (t (mv 0 (anf-node 24 0 (list v) nil nil) anls)))))))
        (8 (let* ((code (anf-dot x)) (code (if (equal code 0) (anf-dot-member n (frf-nth x 2)) code)))
             (if (not (equal code 0)) (mv code nil anls)
               (mv-let (e kids anls) (anf-subs (cons (frf-nth x 1) (cdddr (cdr x))) b anls)
                 (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 21 0 kids nil nil) anls))))))
        (9 (let ((code (anf-new x)))
             (if (not (equal code 0)) (mv code nil anls)
               (mv-let (e kids anls) (anf-subs (cdddr x) b anls)
                 (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 22 0 kids nil nil) anls))))))
        (10 (mv 0 (anf-node 3 0 nil nil nil) anls))
        ((11 12 15) (anf-let x b (if (equal sp 15) 13 sp) anls))
        (13 (mv-let (e kids anls) (anf-subs args b anls)
              (if (not (equal e 0)) (mv e nil anls) (mv 0 (anf-node 16 (len kids) kids nil nil) anls))))
        (14 (anf-fn x b anls))
        (otherwise (anf-sub x b anls)))))))

; ---- WELL-FORMED -----------------------------------------------------------------------------------

(defthm anf-subs-len
  (implies (equal (mv-nth 0 (anf-subs xs b anls)) 0) (equal (len (mv-nth 1 (anf-subs xs b anls))) (len xs))))

(defthm anl-len-len (equal (anl-len l) (len l)))

(defthm frf-len-list
  (implies (and (consp x) (eq (car x) :list) (< (len (cdr x)) *anl40*)) (equal (frf-len x) (len (cdr x))))
  :hints (("Goal" :in-theory (enable frf-len frf-kind))))

(defthm frf-len-small
  (implies (and (consp x) (eq (car x) :list) (< (frf-len x) (- *anl40* 1))) (equal (frf-len x) (len (cdr x))))
  :hints (("Goal" :in-theory (enable frf-len frf-kind))))

(defthm anf-step-wf
  (implies (equal (mv-nth 0 (anf-step x b anls)) 0) (anf-wf (mv-nth 1 (anf-step x b anls))))
  :hints (("Goal" :in-theory (e/d (frf-kind) (anf-subs anl-lookup anf-def anf-quote anf-throw anf-set
                                        anf-set-target anf-dot anf-dot-member anf-new anf-try anf-fn anf-let anf-body)))))

; ---- A SYMBOL'S LOCAL IS ANLOCAL'S ------------------------------------------------------------------

(defthm anf-step-local
  (implies (and (equal (frm-kind x) 2) (anlsp anls) (anl-ccc b anls)
                (equal (anl-err (mv-nth 2 (anl-lookup b (nth 1 x) anls))) 0)
                (<= 0 (anl-lex b (nth 1 x) anls)))
           (and (equal (mv-nth 1 (anf-step x b anls)) (anf-node 2 (mv-nth 0 (anl-lookup b (nth 1 x) anls)) nil nil nil))
                (equal (mv-nth 1 (anl-lookup b (nth 1 x) anls)) (anl-lex b (nth 1 x) anls))))
  :hints (("Goal" :use ((:instance anl-lookup-lex (s (nth 1 x)))) :in-theory (disable anl-lookup-lex anl-lookup))))

; ---- THE TRY'S CLAUSES -------------------------------------------------------------------------------

(defthm anf-try-op-range (and (natp (anf-try-op f)) (< (anf-try-op f) 3))
  :hints (("Goal" :in-theory (enable frf-word)))
  :rule-classes ((:type-prescription :corollary (natp (anf-try-op f))) (:linear :corollary (< (anf-try-op f) 3))))
(in-theory (disable anf-try-op))

; the grammar: body* catch* finally?, the finally last
(defun tg-cat (l)
  (cond ((atom l) t)
        ((equal (anf-try-op (car l)) 1) (tg-cat (cdr l)))
        ((equal (anf-try-op (car l)) 2) (atom (cdr l)))
        (t nil)))
(defun tg-body (l)
  (cond ((atom l) t)
        ((equal (anf-try-op (car l)) 0) (tg-body (cdr l)))
        (t (tg-cat l))))

; the generated step's codes along the clauses: the first refusal, or 0
(defun anf-try-code (cls st)
  (if (atom cls) 0
    (let* ((lastp (if (atom (cdr cls)) 1 0)) (code (anf-try-step st (car cls) lastp 0)))
      (if (equal code 0) (anf-try-code (cdr cls) (anf-try-step st (car cls) lastp 2)) code))))

(defthm anf-try-code-cat (equal (equal (anf-try-code l 1) 0) (tg-cat l)))
(defthm anf-try-code-spec (equal (equal (anf-try-code l 0) 0) (tg-body l)))

; and the refusal is 31 or 32
(defthm anf-try-code-codes (member (anf-try-code l st) '(0 31 32)))

; ---- THE MEMBER OF A DOT ------------------------------------------------------------------------------

; HostExpr.Parser: (. x f) with a symbol f is a field; else the call is the
; third form if a seq, else the forms from the third, and must begin with a symbol
(defun hp-call-head (n m) (declare (ignore n)) (if (equal (frf-kind m) 3) (frf-nth m 0) m))

(defthm anf-dot-member-spec
  (equal (equal (anf-dot-member n m) 0)
         (or (and (equal n 3) (equal (frm-kind m) 2)) (equal (frm-kind (hp-call-head n m)) 2)))
  :hints (("Goal" :in-theory (enable frf-kind))))

; ---- A DEF'S PARTS --------------------------------------------------------------------------------------

; accepted, (def name init?) or (def name "doc" init): the name a symbol,
; the init the form's last, after the docstring when there is one
(defthm anf-def-places
  (implies (equal (anf-def f 0) 0)
           (and (equal (frm-kind (frf-nth f 1)) 2)
                (member (frf-len f) '(2 3 4))
                (equal (anf-def f 1) (if (equal (frf-len f) 2) 0 (- (frf-len f) 1)))
                (iff (equal (anf-def f 2) 2) (equal (frf-len f) 4))
                (implies (equal (frf-len f) 4) (equal (frf-kind (frf-nth f 2)) 4)))))

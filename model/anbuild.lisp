; THE ANALYZER'S NODE ASSEMBLY (src/f/analyze.inc): the analyzer itself,
; from a form to its node, at the level the Fortran is GENERATED from
; (src/f/gen/anbuild_gen.inc, scripts/acl2-fortran -b anbuild),
; guard-verified.
;
; anb-an is the analysis of one form in block b, and Fortran's analyze runs
; it on every form: a symbol bound locally is N_LOCAL of anl-lookup's slot;
; a list headed by one of Clojure's special forms is that form's node, built
; here -- if, do, def, quote, throw, let*, loop*, letfn*, try, and by the
; drivers of set!, ., new, recur and fn* (anb-set, anb-dot, anb-new,
; anb-recur, anb-fn), what the host decides of their forms read through the
; hooks anb-*-kind and the rest; everything else -- a var, a call,
; a macro expanded through the evaluator, a collection, a literal, var,
; case*, deftype*, reify* and clotran's own special forms -- is the host's
; (anb-host, constrained). A subform is analysed by anb-sub, which is anb-an
; on it: the hand-written shim runs Fortran's analyze around it (metadata
; stripped, a seq realised, the source position stamped on the node), none
; of which changes what is modelled here.
;
; THE NODES are built on a stack, the builder anb, so the generated code
; never holds a node in a variable: a subform's analysis leaves its node on
; top, and a node is made by taking its children off the top (anb-node).
; In clotran the builder is the context's value stack, which the collector
; scans; the generated code holds only forms, each a part of the form being
; analysed, which its caller holds -- and integers. The host's operations on
; it are the hand-written shims of analyze.inc, each stated here:
;   anb-const anb-local anb-node anb-node-s   push a leaf, or a node of the
;                     top n: N_CONST, N_LOCAL, any kind (anb-node-s also
;                     names the first slot, a let's or letfn's)
;   anb-def anb-defvar anb-meta   a def's var interned (DefExpr interns it
;                     before the init is analysed), its metadata analysed
;                     (the name's, with the docstring as :doc), its node
;   anb-catch anb-trynode    a catch's entry, the try's node
;   anb-child         a child block: anl-child, and the heap object the
;                     host keeps for it (recur target, prim kinds, hints)
;   anb-refuse anb-refuse-catch anb-hint   the refusal's words and class; the
;                     name a fn* reaches through a let or def (Compiler's
;                     analyze(init, name))
;   anb-loop-open anb-let-kind anb-let-ret   a loop*'s recur target and a
;                     return-hinted fn's argument kinds, a local's prim kind
;                     and array hint, a hinted loop's return: prim kinds and
;                     array hints, constrained to answer an error code and
;                     nothing else: what each kind decides is anprim.lisp's,
;                     generated (src/f/gen/anprim_gen.inc)
; And the form reads, beside anform's and anlocal's: frf-sp (the head's
; special form), frf-meta (a def's name has metadata), frf-rest (a list
; without its first element), frm-sid / frm-bid (a symbol's id, looked up
; / interned), frm-pairs (a binding vector's pairs).
;
; Theorems, in anbuild-proof.lisp: a whole analysis with no error leaves
; exactly one node on the builder, well-formed by anpass's reads, with every
; subtree so (anb-an-wf: the induction anform's one step left open, closed
; over every special form; the host's nodes assumed so); a def's node
; carries its metadata's node, a fn's its own name bound to its self slot
; and its captures exactly the capture records anlocal keeps for it
; (anlocal-proof's anl-lookup-caps-*: the free locals it uses); a symbol
; bound locally is the binding its lexical meaning is. anbuild-cost.lisp
; counts the steps.

(in-package "ACL2")

(include-book "anform")

; ---- THE FORM READS ADDED HERE ---------------------------------------------------------------

; the special form a list's head names, as analyze_seq's dispatch reads it:
; Clojure's, by name, never a local -- 1 if, 2 do, 3 def, 4 quote, 5 throw,
; 6 try, 7 set!, 8 ., 9 new, 10 var, 11 let*, 12 loop*, 13 recur, 14 fn*,
; 15 letfn* -- else 0 (case*, deftype*, reify* and the rest are the host's).
; A symbol here is (:sym id qual amp word class defvar sp meta)
(defun frf-sp (x)
  (declare (xargs :guard t))
  (if (and (equal (frf-kind x) 3) (< 0 (frf-len x)))
      (let* ((h (frf-nth x 0)) (s (anl-nth 7 h)))
        (if (and (equal (frm-kind h) 2) (natp s) (< s 16)) s 0))
    0))
; 1 when a symbol carries metadata
(defun frf-meta (x) (declare (xargs :guard t)) (if (and (equal (frm-kind x) 2) (equal (anl-nth 8 x) 1)) 1 0))
; a list without its first element, when it has a second; else nothing
(defun frf-rest (x)
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (enable frf-kind frf-len frm-kind)))))
  (if (and (equal (frf-kind x) 3) (< 1 (frf-len x))) (cons :list (cddr x)) nil))
; a symbol's id, as the binding was made (interned) and as a lookup asks
; (found, -1 when never interned: no binding has it)
(defun frm-sid (x) (declare (xargs :guard t)) (anl-fix (anl-nth 1 x)))
(defun frm-bid (x) (declare (xargs :guard t)) (anl-fix (anl-nth 1 x)))
(defun frm-pairs (x) (declare (xargs :guard t)) (floor (frm-count x) 2))

(defthm frf-sp-range (and (natp (frf-sp x)) (< (frf-sp x) 16))
  :rule-classes ((:type-prescription :corollary (natp (frf-sp x))) (:linear :corollary (< (frf-sp x) 16))))
(defthm frm-sid-sb64 (and (integerp (frm-sid x)) (signed-byte-p 64 (frm-sid x)) (integerp (frm-bid x)) (signed-byte-p 64 (frm-bid x))))
(defthm frm-pairs-range (and (natp (frm-pairs x)) (< (frm-pairs x) *anl40*))
  :rule-classes ((:type-prescription :corollary (natp (frm-pairs x))) (:linear :corollary (< (frm-pairs x) *anl40*))))
(defthm frf-meta-range (natp (frf-meta x)) :rule-classes :type-prescription)

; ---- THE TREE ---------------------------------------------------------------------------------

; anpass's node (:ast id kind i2 kids s3 caps alts rfn), and a fn's bodies after it
(defun anf-node (kind i2 kids s3 alts) (declare (xargs :guard t)) (list :ast 0 kind i2 kids s3 nil alts 0))
(defun anf-fn-node (caps bodies) (declare (xargs :guard t)) (list :ast 0 14 0 nil nil caps nil 0 bodies))

; the kinds the analyzer makes, and how many children each has
(defun anf-kind-ok (k i2 nk)
  (declare (xargs :guard t))
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

(defthm anf-nth-count (implies (consp x) (< (acl2-count (nth n x)) (acl2-count x))) :rule-classes :linear)
(defthm anf-car-count (<= (acl2-count (car l)) (acl2-count l)) :rule-classes :linear)
(defthm anf-cdr-count (<= (acl2-count (cdr l)) (acl2-count l)) :rule-classes :linear)

; a node well-formed by anpass's reads: its kind one of the analyzer's, as
; many children as the kind has, each well-formed; a try's finally may be
; nil, a def's metadata (slot 3) nil or a node; its alternatives nodes; a
; fn's bodies nodes and its captures slots
(mutual-recursion
 (defun anf-wf (x)
   (declare (xargs :measure (acl2-count x) :verify-guards nil))
   (and (consp x) (eq (car x) :ast)
        (let ((k (nth 2 x)) (i2 (nth 3 x)) (kids (nth 4 x)))
          (and (anf-kind-ok k i2 (len kids))
               (if (equal k 18)
                   (and (anf-wf (car kids)) (or (null (cadr kids)) (anf-wf (cadr kids))))
                 (anf-wfs kids))
               (if (equal k 10) (or (null (nth 5 x)) (anf-wf (nth 5 x))) t)
               (anf-wfs (nth 7 x))
               (if (equal k 14) (and (anf-wfs (nth 9 x)) (integer-listp (nth 6 x))) t)))))
 (defun anf-wfs (l)
   (declare (xargs :measure (acl2-count l)))
   (if (atom l) (null l) (and (anf-wf (car l)) (anf-wfs (cdr l))))))

; ---- THE BUILDER ------------------------------------------------------------------------------

(defstobj anb (anb-stk :type t :initially nil))

(defun anb-push (v anb) (declare (xargs :stobjs anb :guard t)) (update-anb-stk (cons v (anb-stk anb)) anb))

; n items off the top of l, the deepest first, and what is under them
(defun anb-popn (n l acc)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) (mv acc l) (anb-popn (- n 1) (cdr l) (cons (car l) acc))))

; the top of a stack, and what is under it
(defun anb-top (l) (declare (xargs :guard t)) (if (consp l) (car l) nil))
(defun anb-under (l) (declare (xargs :guard t)) (if (consp l) (cdr l) nil))

; N_CONST of a quoted form (analyze.inc anb_const: const_node)
(defun anb-const (x anb) (declare (xargs :stobjs anb :guard t) (ignore x)) (anb-push (anf-node 1 0 nil nil nil) anb))
; N_LOCAL of slot (anb_local: the symbol kept for the debugger)
(defun anb-local (x slot anb) (declare (xargs :stobjs anb :guard (signed-byte-p 64 slot)) (ignore x))
  (anb-push (anf-node 2 slot nil nil nil) anb))
; a node of kind, its n children the top n (anb_node: mk_node)
(defun anb-node (kind i2 n anb)
  (declare (xargs :stobjs anb :guard (and (signed-byte-p 64 kind) (signed-byte-p 64 i2) (signed-byte-p 64 n))))
  (mv-let (kids rest) (anb-popn (nfix n) (anb-stk anb) nil)
    (update-anb-stk (cons (anf-node kind i2 kids nil nil) rest) anb)))
; and one that names its first slot s, a let's, loop's or letfn's
(defun anb-node-s (kind i2 n s anb)
  (declare (xargs :stobjs anb :guard (and (signed-byte-p 64 kind) (signed-byte-p 64 i2) (signed-byte-p 64 n) (signed-byte-p 64 s)))
           (ignore s))
  (anb-node kind i2 n anb))

; the refusal: code's words and class (anf_refuse for anform's codes,
; anl_refuse for anlocal's), about form f; a catch's (the class, or the name)
(defun anb-refuse (code f anb) (declare (xargs :stobjs anb :guard (signed-byte-p 64 code)) (ignore code f)) anb)
(defun anb-refuse-catch (code f anb) (declare (xargs :stobjs anb :guard (signed-byte-p 64 code)) (ignore code f)) anb)
; the name the next fn* analysed is given (a let's or def's)
(defun anb-hint (x anb) (declare (xargs :stobjs anb :guard t) (ignore x)) anb)
; a def's var, interned now if new, so the init can refer to it
(defun anb-defvar (x anb) (declare (xargs :stobjs anb :guard t) (ignore x)) anb)
; the def's node: its init (i2's bit 1) then its metadata (m 1) on top
(defun anb-def (x i2 m anb)
  (declare (xargs :stobjs anb :guard (and (signed-byte-p 64 i2) (signed-byte-p 64 m))) (ignore x))
  (let* ((st (anb-stk anb))
         (md (if (equal m 1) (anb-top st) nil)) (st (if (equal m 1) (anb-under st) st))
         (kids (if (equal (mod (nfix i2) 2) 1) (list (anb-top st)) nil)) (st (if (equal (mod (nfix i2) 2) 1) (anb-under st) st)))
    (update-anb-stk (cons (anf-node 10 i2 kids md nil) st) anb)))
; a catch: its handler, on top, becomes the entry (class, slot, handler)
(defun anb-catch (f slot anb)
  (declare (xargs :stobjs anb :guard (signed-byte-p 64 slot)) (ignore f))
  (let ((st (anb-stk anb))) (update-anb-stk (cons (list :catch slot (anb-top st)) (anb-under st)) anb)))
(defun anb-handlers (l) (declare (xargs :guard t)) (if (atom l) nil (cons (anl-nth 2 (car l)) (anb-handlers (cdr l)))))
; the catches on top of l, the deepest first, and what is under them
(defun anb-catchp (v) (declare (xargs :guard t)) (and (consp v) (eq (car v) :catch)))
(defun anb-popc (l acc)
  (declare (xargs :guard t))
  (if (and (consp l) (anb-catchp (car l))) (anb-popc (cdr l) (cons (car l) acc)) (mv acc l)))
; the try's node: its body, the catches over it, and the finally (fin 1) on top
(defun anb-trynode (fin anb)
  (declare (xargs :stobjs anb :guard (signed-byte-p 64 fin)))
  (let* ((st (anb-stk anb))
         (fn (if (equal fin 1) (anb-top st) nil)) (st (if (equal fin 1) (anb-under st) st)))
    (mv-let (cs st) (anb-popc st nil)
      (update-anb-stk (cons (anf-node 18 0 (list (anb-top st) fn) nil (anb-handlers cs)) (anb-under st)) anb))))
; a child block of b, and its heap object
(defun anb-child (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (anl-child b anls))
; a fn's node: its n bodies, the top n, and its captures
(defun anb-fnnode (n caps anb)
  (declare (xargs :stobjs anb :guard (signed-byte-p 64 n)))
  (mv-let (bodies rest) (anb-popn (nfix n) (anb-stk anb) nil)
    (update-anb-stk (cons (anf-fn-node caps bodies) rest) anb)))
; a fn's captures, as its node lists them (caps_vec): the outer slots, oldest first
(defun anb-caps (i anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 i) :measure (nfix (- (nfix (anl-nev anls)) (nfix i)))))
  (if (and (natp i) (natp (anl-nev anls)) (< i (anl-nev anls)))
      (append (anb-caps (+ 1 i) anls) (list (anl-g-ev i anls)))
    nil))

; THE DRIVERS' NODES, each the host's node of its kind made of the top n
; (analyze.inc's shims build clotran's: a set!'s var, static or field, a
; .'s member and target, a new's class, a recur's target and a method's
; `this`), and what a method and a fn leave
; (set! target value): N_SETBANG of its value, or of a field's object and value
(defun anb-setnode (x n anb)
  (declare (xargs :stobjs anb :guard (member n '(1 2))) (ignore x))
  (anb-node 24 (if (equal n 2) 2 0) n anb))
; (. target member args*): of kind k (0 an instance's, 1 a class's), the
; target then the arguments
(defun anb-dotnode (x k n anb)
  (declare (xargs :stobjs anb :guard (and (signed-byte-p 64 k) (signed-byte-p 64 n))) (ignore x k))
  (anb-node 21 0 n anb))
(defun anb-newnode (x n anb)
  (declare (xargs :stobjs anb :guard (signed-byte-p 64 n)) (ignore x))
  (anb-node 22 0 n anb))
; (recur args*) in block b: its arguments
(defun anb-recurnode (x b n anb)
  (declare (xargs :stobjs anb :guard (signed-byte-p 64 n)) (ignore x b))
  (anb-node 16 n n anb))
; a method's body, on top, becomes its arity: its parameters' count and
; first slot, the body (the host's [nfixed variadic first-slot body])
(defun anb-arity (m mb start nreq rest anb)
  (declare (xargs :stobjs anb :guard t) (ignore m mb start nreq rest))
  anb)
; a fn's root block in block b, and its heap object
(defun anb-newfn (b anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 b)))
  (anl-new-fn b anls))
; the fn x in root block r, its n arities on top: its node, with the
; captures anl-caps-of left (the host's template: the arities' tail
; checks passed, their locals cleared, the VM's or flat compilation)
(defun anb-fnclose (x r n anls anb)
  (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 n)) (ignore x r))
  (anb-fnnode n (anb-caps 0 anls) anb))
; a clause as the drivers read it: a seq realised (analyze.inc
; norm_form); the form itself here, where every list is one
(defun frf-norm (x) (declare (xargs :guard t)) x)

; ---- THE HOST'S ---------------------------------------------------------------------------------

; what the host analyses (a var, a call, a macro's expansion, a collection,
; a literal, case*, deftype*, reify*, clotran's own special forms) and a
; def's metadata map: a node, well-formed when there is no error
(encapsulate
  (((anb-host * * anls anb) => (mv * anls anb) :formals (x b anls anb) :guard (signed-byte-p 64 b))
   ((anb-host-meta * * anls anb) => (mv * anls anb) :formals (x b anls anb) :guard (signed-byte-p 64 b)))
  (local (defun anb-host (x b anls anb)
           (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b)) (ignore x b))
           (let ((anb (anb-push (anf-node 1 0 nil nil nil) anb))) (mv 0 anls anb))))
  (local (defun anb-host-meta (x b anls anb)
           (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b)) (ignore x b))
           (let ((anb (anb-push (anf-node 1 0 nil nil nil) anb))) (mv 0 anls anb))))
  (defthm anb-host-push
    (implies (equal (car (anb-host x b anls anb)) 0)
             (and (equal (cdr (anb-stk (mv-nth 2 (anb-host x b anls anb)))) (anb-stk anb))
                  (consp (anb-stk (mv-nth 2 (anb-host x b anls anb))))
                  (anf-wf (car (anb-stk (mv-nth 2 (anb-host x b anls anb))))))))
  (defthm anb-host-meta-push
    (implies (equal (car (anb-host-meta x b anls anb)) 0)
             (and (equal (cdr (anb-stk (mv-nth 2 (anb-host-meta x b anls anb)))) (anb-stk anb))
                  (consp (anb-stk (mv-nth 2 (anb-host-meta x b anls anb))))
                  (anf-wf (car (anb-stk (mv-nth 2 (anb-host-meta x b anls anb))))))))
  (defthm anb-host-types
    (and (consp (anb-host x b anls anb)) (consp (anb-host-meta x b anls anb))
         (implies (anlsp anls) (anlsp (mv-nth 1 (anb-host x b anls anb))))
         (implies (anbp anb) (anbp (mv-nth 2 (anb-host x b anls anb))))
         (implies (anlsp anls) (anlsp (mv-nth 1 (anb-host-meta x b anls anb))))
         (implies (anbp anb) (anbp (mv-nth 2 (anb-host-meta x b anls anb)))))))

; what a driver leaves to the host, w which: 1 a set! of a deftype's
; mutable field, rewritten (set! (.-f this) v); 2 a . whose target names a
; host class (a static member, a box, or a member of the class); 3 the
; lazy seq a (new clotran.host.lazy_seq (fn* [] ..)) is; 4 a method body
; its primitive hints rewrite (a let* or loop* of the casts) -- each
; analysed by the host, its node constrained as anb-host's is
(encapsulate
  (((anb-host2 * * * anls anb) => (mv * anls anb) :formals (w x b anls anb)
    :guard (and (signed-byte-p 64 w) (signed-byte-p 64 b))))
  (local (defun anb-host2 (w x b anls anb)
           (declare (xargs :stobjs (anls anb) :guard (and (signed-byte-p 64 w) (signed-byte-p 64 b))) (ignore w x b))
           (let ((anb (anb-push (anf-node 1 0 nil nil nil) anb))) (mv 0 anls anb))))
  (defthm anb-host2-push
    (implies (equal (car (anb-host2 w x b anls anb)) 0)
             (and (equal (cdr (anb-stk (mv-nth 2 (anb-host2 w x b anls anb)))) (anb-stk anb))
                  (consp (anb-stk (mv-nth 2 (anb-host2 w x b anls anb))))
                  (anf-wf (car (anb-stk (mv-nth 2 (anb-host2 w x b anls anb))))))))
  (defthm anb-host2-types
    (and (consp (anb-host2 w x b anls anb))
         (implies (anlsp anls) (anlsp (mv-nth 1 (anb-host2 w x b anls anb))))
         (implies (anbp anb) (anbp (mv-nth 2 (anb-host2 w x b anls anb)))))))

; a def's metadata, analysed when its name has some or a docstring is given:
; e, and 1 when a node was left
(defun anb-meta (x b anls anb)
  (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b)))
  (if (and (equal (frf-meta (frf-nth x 1)) 0) (equal (anf-def x 2) 0)) (mv 0 0 anls anb)
    (mv-let (e anls anb) (anb-host-meta x b anls anb) (mv e 1 anls anb))))

; prim kinds and array hints: an error code each (their decisions anprim.lisp's)
(encapsulate
  (((anb-loop-open * * *) => * :formals (c start n) :guard t)
   ((anb-let-kind * * * *) => * :formals (k c slot loopp) :guard t)
   ((anb-let-ret * *) => * :formals (c ret) :guard t))
  (local (defun anb-loop-open (c start n) (declare (xargs :guard t) (ignore c start n)) 0))
  (local (defun anb-let-kind (k c slot loopp) (declare (xargs :guard t) (ignore k c slot loopp)) 0))
  (local (defun anb-let-ret (c ret) (declare (xargs :guard t) (ignore c ret)) 0))
  (defthm anb-prim-sb64
    (and (integerp (anb-loop-open c start n)) (signed-byte-p 64 (anb-loop-open c start n))
         (integerp (anb-let-kind k c slot loopp)) (signed-byte-p 64 (anb-let-kind k c slot loopp))
         (integerp (anb-let-ret c ret)) (signed-byte-p 64 (anb-let-ret c ret)))))

; THE DRIVERS' HOST READS: what the host decides of a set!, ., new, recur
; and fn*, an integer each -- a kind, or an error code whose words the host
; raised. anb-set-kind: 0 a var or a static field (the value only), 1 a
; host field (its object, then the value), 2 a deftype's mutable field
; (anb-host2 1), else refused (a local, an immutable field, an unresolved
; symbol); anb-dot-kind: 0 an instance member, 1 a class's (the target
; kept as its name), 2 a host class's (anb-host2 2), else refused (a class
; nothing knows); anb-new-kind: 2 a lazy seq's (anb-host2 3), else a new;
; anb-recur-open: the recur's target found (RecurExpr: a loop or fn, the
; count it expects noted); anb-recur-check: its arguments' primitive kinds
; as its target's locals need them; anb-fn-open: the fn's display name and
; its hint rules (a deftype method's clauses exempt), its self slot noted;
; anb-method-open: a method's array hints, recur target and argument
; kinds, and its primitive hints -- 1 refused, 2 the body rewritten
; (anb-host2 4), else 0; anb-method-check: a recur argument that did not
; match its primitive; anb-fn-check: every arity's tail check and its
; recurs' counts
(encapsulate
  (((anb-set-kind * *) => * :formals (x b) :guard t)
   ((anb-dot-kind * *) => * :formals (x b) :guard t)
   ((anb-new-kind *) => * :formals (x) :guard t)
   ((anb-recur-open * *) => * :formals (x b) :guard t)
   ((anb-recur-check * * *) => * :formals (x b n) :guard t)
   ((anb-fn-open * * *) => * :formals (x r self) :guard t)
   ((anb-method-open * * * * * *) => * :formals (m r mb start nreq rest) :guard t)
   ((anb-method-check *) => * :formals (mb) :guard t)
   ((anb-fn-check * * *) => * :formals (x r n) :guard t))
  (local (defun anb-set-kind (x b) (declare (xargs :guard t) (ignore x b)) 0))
  (local (defun anb-dot-kind (x b) (declare (xargs :guard t) (ignore x b)) 0))
  (local (defun anb-new-kind (x) (declare (xargs :guard t) (ignore x)) 0))
  (local (defun anb-recur-open (x b) (declare (xargs :guard t) (ignore x b)) 0))
  (local (defun anb-recur-check (x b n) (declare (xargs :guard t) (ignore x b n)) 0))
  (local (defun anb-fn-open (x r self) (declare (xargs :guard t) (ignore x r self)) 0))
  (local (defun anb-method-open (m r mb start nreq rest) (declare (xargs :guard t) (ignore m r mb start nreq rest)) 0))
  (local (defun anb-method-check (mb) (declare (xargs :guard t) (ignore mb)) 0))
  (local (defun anb-fn-check (x r n) (declare (xargs :guard t) (ignore x r n)) 0))
  (defthm anb-drv-sb64
    (and (integerp (anb-set-kind x b)) (signed-byte-p 64 (anb-set-kind x b))
         (integerp (anb-dot-kind x b)) (signed-byte-p 64 (anb-dot-kind x b))
         (integerp (anb-new-kind x)) (signed-byte-p 64 (anb-new-kind x))
         (integerp (anb-recur-open x b)) (signed-byte-p 64 (anb-recur-open x b))
         (integerp (anb-recur-check x b n)) (signed-byte-p 64 (anb-recur-check x b n))
         (integerp (anb-fn-open x r self)) (signed-byte-p 64 (anb-fn-open x r self))
         (integerp (anb-method-open m r mb start nreq rest)) (signed-byte-p 64 (anb-method-open m r mb start nreq rest))
         (integerp (anb-method-check mb)) (signed-byte-p 64 (anb-method-check mb))
         (integerp (anb-fn-check x r n)) (signed-byte-p 64 (anb-fn-check x r n)))))

; ---- THE LOCALS' OPERATIONS: WHAT THEY ANSWER -------------------------------------------------

(defthm anl-child-types
  (implies (and (anlsp anls) (signed-byte-p 64 p))
           (and (anlsp (mv-nth 1 (anl-child p anls))) (integerp (car (anl-child p anls)))
                (signed-byte-p 64 (car (anl-child p anls)))))
  :hints (("Goal" :in-theory (enable anl-child))))
(defthm anl-reserve-types
  (implies (and (anlsp anls) (signed-byte-p 64 n))
           (and (anlsp (mv-nth 1 (anl-reserve b n anls))) (integerp (car (anl-reserve b n anls)))
                (<= -1 (car (anl-reserve b n anls))) (< (car (anl-reserve b n anls)) *anl40*)))
  :hints (("Goal" :in-theory (enable anl-reserve))))
(defthm anl-bind-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 b) (signed-byte-p 64 s) (signed-byte-p 64 k)) (anlsp (anl-bind b s k anls)))
  :hints (("Goal" :in-theory (e/d (anl-bind) (anl-grow-x anl-push-n)))))
(defthm anl-new-fn-types
  (implies (and (anlsp anls) (signed-byte-p 64 o))
           (and (anlsp (mv-nth 1 (anl-new-fn o anls))) (integerp (car (anl-new-fn o anls)))
                (signed-byte-p 64 (car (anl-new-fn o anls)))))
  :hints (("Goal" :in-theory (enable anl-new-fn))))
(defthm anl-arity-types
  (implies (and (anlsp anls) (signed-byte-p 64 nreq))
           (and (anlsp (mv-nth 1 (anl-arity b nreq rest anls))) (integerp (car (anl-arity b nreq rest anls)))))
  :hints (("Goal" :in-theory (e/d (anl-arity) (anl-push-a)))))
(defthm anl-caps-of-anlsp (implies (anlsp anls) (anlsp (anl-caps-of b anls))))
; and the blocks and slots they answer, as bounds for linear arithmetic
(defthm anl-child-range (and (<= -1 (car (anl-child p anls))) (< (car (anl-child p anls)) *anl40*))
  :hints (("Goal" :in-theory (enable anl-child))) :rule-classes :linear)
(defthm anl-child-int (integerp (car (anl-child p anls))) :hints (("Goal" :in-theory (enable anl-child))) :rule-classes :type-prescription)
(defthm anl-new-fn-range (and (<= -1 (car (anl-new-fn o anls))) (< (car (anl-new-fn o anls)) *anl40*))
  :hints (("Goal" :in-theory (enable anl-new-fn))) :rule-classes :linear)
(defthm anl-new-fn-int (integerp (car (anl-new-fn o anls))) :hints (("Goal" :in-theory (enable anl-new-fn))) :rule-classes :type-prescription)
(defthm anl-reserve-range (and (<= -1 (car (anl-reserve b n anls))) (< (car (anl-reserve b n anls)) *anl40*))
  :hints (("Goal" :in-theory (enable anl-reserve))) :rule-classes :linear)
(defthm anl-reserve-int (integerp (car (anl-reserve b n anls))) :hints (("Goal" :in-theory (enable anl-reserve))) :rule-classes :type-prescription)
(in-theory (disable anl-child anl-reserve anl-bind anl-new-fn anl-arity anl-caps-of anl-arity-end anl-lookup))

; ---- THE ANALYZER --------------------------------------------------------------------------------
;
; The measure: a form's acl2-count, four levels to it (a subform's analysis
; above the form's own, above the drivers', above the walks), and a walk of a
; vector's index after it

(defmacro anb-m (x lvl k r) `(if (consp ,x) (make-ord 1 (+ 1 (* 4 (acl2-count ,x)) ,lvl) ,k) ,r))

(defthm anl-nth-count-le (<= (acl2-count (anl-nth i l)) (acl2-count l)) :rule-classes :linear)
(defthm frf-nth-count (implies (consp x) (< (acl2-count (frf-nth x i)) (acl2-count x)))
  :hints (("Goal" :in-theory (enable frf-nth frf-kind frf-len))) :rule-classes :linear)
(defthm frm-nth-count (implies (consp x) (< (acl2-count (frm-nth x i)) (acl2-count x)))
  :hints (("Goal" :in-theory (enable frm-nth frm-kind frm-count))) :rule-classes :linear)
(defthm frf-rest-count (implies (frf-rest x) (< (acl2-count (frf-rest x)) (acl2-count x)))
  :hints (("Goal" :in-theory (enable frf-kind frf-len))) :rule-classes :linear)
(defthm frf-nth-atom (implies (atom x) (equal (frf-nth x i) nil)) :hints (("Goal" :in-theory (enable frf-nth frf-kind frm-kind))))
(defthm frm-nth-atom (implies (atom x) (equal (frm-nth x i) nil)) :hints (("Goal" :in-theory (enable frm-nth frm-kind))))
(defthm frf-len-atom (implies (atom x) (equal (frf-len x) 0)) :hints (("Goal" :in-theory (enable frf-len frf-kind frm-kind))))
(in-theory (disable frf-sp frf-meta frm-sid frm-bid))
(defthm frf-len-consp (implies (< 0 (frf-len x)) (consp x)) :hints (("Goal" :in-theory (enable frf-len frf-kind frm-kind))) :rule-classes :forward-chaining)
(defthm frf-kind-3-consp (implies (equal (frf-kind x) 3) (consp x)) :hints (("Goal" :in-theory (enable frf-kind frm-kind))) :rule-classes :forward-chaining)
(defthm frm-pairs-consp (implies (< 0 (frm-pairs x)) (consp x)) :hints (("Goal" :in-theory (enable frm-pairs frm-count frm-kind))) :rule-classes :forward-chaining)
(defthm frf-rest-count-le (<= (acl2-count (frf-rest x)) (acl2-count x)) :hints (("Goal" :in-theory (enable frf-rest))) :rule-classes :linear)

(defthm frf-rest-consp (implies (consp (frf-rest x)) (consp x)) :hints (("Goal" :in-theory (enable frf-rest))) :rule-classes :forward-chaining)
(defthm frm-pairs-atom (implies (not (consp x)) (equal (frm-pairs x) 0)) :hints (("Goal" :in-theory (enable frm-pairs frm-count frm-kind))))
(in-theory (disable frf-rest frm-pairs))
(defthm frf-rest-count-2 (implies (< 1 (frf-len x)) (< (acl2-count (frf-rest x)) (acl2-count x)))
  :hints (("Goal" :in-theory (enable frf-rest frf-len frf-kind frm-kind))) :rule-classes :linear)

; letfn*'s names from pair i, each checked and bound to slot start + i
(defun anb-lfnames (bv i c start anls anb)
  (declare (xargs :stobjs (anls anb) :guard (and (natp i) (signed-byte-p 64 c) (integerp start)
                                                 (<= -1 start) (< start *anl40*))
                  :measure (nfix (- (frm-pairs bv) (nfix i)))))
  (if (and (natp i) (< i (frm-pairs bv)))
      (let* ((k (frm-nth bv (* 2 i))) (code (anl-name-code k)))
        (if (not (equal code 0)) (let ((anb (anb-refuse code k anb))) (mv code anls anb))
          (let ((anls (anl-bind c (frm-bid k) (+ start i) anls))) (anb-lfnames bv (+ 1 i) c start anls anb))))
    (mv 0 anls anb)))

(defthm anb-lfnames-types
  (implies (and (anlsp anls) (signed-byte-p 64 c) (integerp start) (<= -1 start) (< start *anl40*))
           (and (anlsp (mv-nth 1 (anb-lfnames bv i c start anls anb)))
                (equal (mv-nth 2 (anb-lfnames bv i c start anls anb)) anb))))

; the number of body forms list xs begins with, before a try's first clause
(defun anb-try-n (xs)
  (declare (xargs :guard t :measure (acl2-count xs)))
  (if (or (equal (frf-len xs) 0) (not (equal (anf-try-op (frf-nth xs 0)) 0))) 0
    (if (< (frf-len xs) 2) 1
      (let ((k (anb-try-n (frf-rest xs)))) (if (< k (- *anl40* 2)) (+ 1 k) k)))))
(defthm anb-try-n-range (and (natp (anb-try-n xs)) (< (anb-try-n xs) (- *anl40* 1)))
  :rule-classes ((:type-prescription :corollary (natp (anb-try-n xs))) (:linear :corollary (< (anb-try-n xs) (- *anl40* 1)))))

; list xs without its first n forms
(defun anb-drop (xs n)
  (declare (xargs :guard (integerp n) :measure (nfix n)))
  (if (or (not (natp n)) (equal n 0)) xs (anb-drop (frf-rest xs) (- n 1))))
(defthm anb-drop-count (<= (acl2-count (anb-drop xs n)) (acl2-count xs)) :rule-classes :linear)
(defthm anb-drop-consp (implies (consp (anb-drop xs n)) (consp xs)) :rule-classes :forward-chaining)

; a method's parameters from i bound in block c, slots k on, & skipped
(defun anb-params (pv i c k anls)
  (declare (xargs :stobjs anls :measure (nfix (- (frm-count pv) (nfix i)))
                  :guard (and (natp i) (signed-byte-p 64 c) (integerp k) (<= -1 k) (<= k (+ (- *anl40* 1) i)))))
  (if (and (natp i) (< i (frm-count pv)))
      (let ((p (frm-nth pv i)))
        (if (equal (frm-amp p) 1) (anb-params pv (+ 1 i) c k anls)
          (let ((anls (anl-bind c (frm-bid p) k anls))) (anb-params pv (+ 1 i) c (+ 1 k) anls))))
    anls))
(defthm anb-params-anlsp
  (implies (and (anlsp anls) (signed-byte-p 64 c) (natp i) (integerp k) (<= -1 k) (<= k (+ (- *anl40* 1) i)))
           (anlsp (anb-params pv i c k anls))))

; a fn's own name nm, when it has one, bound in its root block r to the
; self slot reserved there; -1 when it has none
(defun anb-self (r nm anls)
  (declare (xargs :stobjs anls :guard (signed-byte-p 64 r)))
  (if (equal (frm-kind nm) 2)
      (mv-let (s anls) (anl-reserve r 1 anls)
        (let ((anls (anl-bind r (frm-bid nm) s anls))) (mv s anls)))
    (mv -1 anls)))
(defthm anb-self-types
  (implies (and (anlsp anls) (signed-byte-p 64 r))
           (and (anlsp (mv-nth 1 (anb-self r nm anls))) (integerp (car (anb-self r nm anls)))
                (signed-byte-p 64 (car (anb-self r nm anls))))))

(defthm anl-pw-bounds
  (implies (and (natp i) (natp n) (<= i n) (< n *anl40*) (natp nreq) (<= nreq i) (natp rest) (<= rest 1))
           (and (natp (anl-pw pv i n st nreq rest 2)) (< (anl-pw pv i n st nreq rest 2) *anl40*)
                (natp (anl-pw pv i n st nreq rest 3)) (<= (anl-pw pv i n st nreq rest 3) 1))))
(defthm anl-params-bounds
  (and (natp (anl-params pv 2)) (< (anl-params pv 2) *anl40*) (natp (anl-params pv 3)) (<= (anl-params pv 3) 1))
  :hints (("Goal" :use ((:instance anl-pw-bounds (i 0) (n (frm-count pv)) (st 0) (nreq 0) (rest 0))) :in-theory (disable anl-pw-bounds)))
  :rule-classes ((:type-prescription :corollary (natp (anl-params pv 2))) (:linear :corollary (< (anl-params pv 2) *anl40*))
                 (:type-prescription :corollary (natp (anl-params pv 3))) (:linear :corollary (<= (anl-params pv 3) 1))))
(in-theory (disable anl-params))


; a def's metadata analysed (after its init), then its node; i2 1 with an init
(defun anb-defend (x b i2 anls anb)
  (declare (xargs :stobjs (anls anb) :guard (and (signed-byte-p 64 b) (signed-byte-p 64 i2))))
  (mv-let (e m anls anb) (anb-meta x b anls anb)
    (if (not (equal e 0)) (mv e anls anb)
      (let ((anb (anb-def x i2 m anb))) (mv 0 anls anb)))))

; whether a try has a finally, from its first clause on
(defun anb-try-fin (cls)
  (declare (xargs :guard t :measure (acl2-count cls)))
  (cond ((equal (frf-len cls) 0) 0)
        ((equal (anf-try-op (frf-nth cls 0)) 2) 1)
        ((< (frf-len cls) 2) 0)
        (t (anb-try-fin (frf-rest cls)))))

(mutual-recursion

 ; a subform, through Fortran's analyze (the shim anb_sub)
 (defun anb-sub (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 3 0 7)))
   (anb-an x b anls anb))

 ; ONE FORM, in block b: its node left on the builder
 (defun anb-an (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 2 0 6)))
   (cond
    ((equal (frf-kind x) 2)
     (mv-let (slot bx anls) (anl-lookup b (frm-sid x) anls)
       (if (<= 0 bx) (let ((anb (anb-local x slot anb))) (mv 0 anls anb)) (anb-host x b anls anb))))
    ((not (equal (frf-kind x) 3)) (anb-host x b anls anb))
    (t
     (let ((sp (frf-sp x)) (n (frf-len x)))
       (case sp
         ; (if test then else?)
         (1 (let ((code (anf-if n)))
              (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
                (mv-let (e anls anb) (anb-listn (frf-rest x) (- n 1) b anls anb)
                  (if (not (equal e 0)) (mv e anls anb)
                    (let ((anb (anb-node 4 0 (- n 1) anb))) (mv 0 anls anb)))))))
         ; (do body*)
         (2 (anb-body (frf-rest x) b anls anb))
         (3 (anb-deff x b anls anb))
         ; (quote form)
         (4 (let ((code (anf-quote n)))
              (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
                (let ((anb (anb-const (frf-nth x 1) anb))) (mv 0 anls anb)))))
         ; (throw form)
         (5 (let ((code (anf-throw n)))
              (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
                (mv-let (e anls anb) (anb-sub (frf-nth x 1) b anls anb)
                  (if (not (equal e 0)) (mv e anls anb)
                    (let ((anb (anb-node 17 0 1 anb))) (mv 0 anls anb)))))))
         (6 (anb-try x b anls anb))
         ; (set! target value): AssignExpr's checks, then the driver
         (7 (let* ((code (anf-set n)) (code (if (equal code 0) (anf-set-target (frf-nth x 1)) code)))
              (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
                (anb-set x b anls anb))))
         ; (. target member args*): the count, then the driver
         (8 (let ((code (anf-dot x)))
              (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
                (anb-dot x b anls anb))))
         ; (new Class args*)
         (9 (let ((code (anf-new x)))
              (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
                (anb-new x b anls anb))))
         (11 (anb-let x b 11 anls anb))
         (12 (anb-let x b 12 anls anb))
         (13 (anb-recur x b anls anb))
         (14 (anb-fn x b anls anb))
         (15 (anb-letfn x b anls anb))
         (otherwise (anb-host x b anls anb)))))))

 ; (def name init?) / (def name "doc" init): DefExpr.Parser's checks, the var
 ; interned, the init analysed under the name, then the metadata
 (defun anb-deff (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 2 8)))
   (let ((code (anf-def x 0)))
     (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb))
       (let* ((init (anf-def x 1)) (anb (anb-defvar x anb)))
         (if (< 0 init)
             (let ((anb (anb-hint (frf-nth x 1) anb)))
               (mv-let (e anls anb) (anb-sub (frf-nth x init) b anls anb)
                 (if (not (equal e 0)) (mv e anls anb) (anb-defend x b 1 anls anb))))
           (anb-defend x b 0 anls anb))))))

 ; the first n forms of list xs, each analysed in block b, left in order on the builder
 (defun anb-listn (xs n b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (and (integerp n) (signed-byte-p 64 b)) :verify-guards nil
                   :measure (anb-m xs 1 0 2)))
   (if (or (not (natp n)) (equal n 0) (equal (frf-len xs) 0)) (mv 0 anls anb)
     (mv-let (e anls anb) (anb-sub (frf-nth xs 0) b anls anb)
       (if (or (not (equal e 0)) (< (frf-len xs) 2)) (mv e anls anb)
         (anb-listn (frf-rest xs) (- n 1) b anls anb)))))

 ; the forms of list xs as one N_DO
 (defun anb-body (xs b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m xs 1 1 3)))
   (mv-let (e anls anb) (anb-listn xs (frf-len xs) b anls anb)
     (if (not (equal e 0)) (mv e anls anb)
       (let ((anb (anb-node 5 0 (frf-len xs) anb))) (mv 0 anls anb)))))

 ; let* / loop*'s pairs from i: each name checked, its init analysed in block
 ; c, then the name bound to slot start + i (LetExpr.Parser's order)
 (defun anb-binds (bv i c start loopp anls anb)
   (declare (xargs :stobjs (anls anb) :verify-guards nil
                   :guard (and (natp i) (signed-byte-p 64 c) (integerp start) (<= -1 start)
                               (< start *anl40*) (signed-byte-p 64 loopp))
                   :measure (anb-m bv 1 (nfix (- *anl40* (nfix i))) 2)))
   (if (and (natp i) (< i (frm-pairs bv)))
       (let* ((k (frm-nth bv (* 2 i))) (code (anl-name-code k)))
         (if (not (equal code 0)) (let ((anb (anb-refuse code k anb))) (mv code anls anb))
           (let ((anb (anb-hint k anb)))
             (mv-let (e anls anb) (anb-sub (frm-nth bv (+ 1 (* 2 i))) c anls anb)
               (if (not (equal e 0)) (mv e anls anb)
                 (let* ((slot (+ start i)) (anls (anl-bind c (frm-bid k) slot anls))
                        (e (anb-let-kind k c slot loopp)))
                   (if (not (equal e 0)) (mv e anls anb)
                     (anb-binds bv (+ 1 i) c start loopp anls anb))))))))
     (mv 0 anls anb)))

 ; (let* [bindings] body*) and (loop* ...): kind 11 or 12; a child block,
 ; the slots reserved together, the bindings, the body; the node the inits
 ; then the body, i2 their number, its first slot named
 (defun anb-let (x b kind anls anb)
   (declare (xargs :stobjs (anls anb) :guard (and (signed-byte-p 64 b) (member kind '(11 12))) :verify-guards nil
                   :measure (anb-m x 1 2 8)))
   (let* ((bv (frf-nth x 1)) (code (anl-shape bv)))
     (if (not (equal code 0)) (let ((anb (anb-refuse code bv anb))) (mv code anls anb))
       (mv-let (c anls) (anb-child b anls)
         (let* ((n (frm-pairs bv)) (loopp (if (equal kind 12) 1 0)))
           (mv-let (start anls) (anl-reserve c n anls)
             (let ((ret (if (equal loopp 1) (anb-loop-open c start n) 0)))
               (mv-let (e anls anb) (anb-binds bv 0 c start loopp anls anb)
                 (if (not (equal e 0)) (mv e anls anb)
                   (mv-let (e anls anb) (anb-body (frf-rest (frf-rest x)) c anls anb)
                     (if (not (equal e 0)) (mv e anls anb)
                       (let ((e (if (equal loopp 1) (anb-let-ret c ret) 0)))
                         (if (not (equal e 0)) (mv e anls anb)
                           (let ((anb (anb-node-s kind n (+ 1 n) start anb))) (mv 0 anls anb)))))))))))))))

 ; letfn*'s inits from pair i, each in block c, after every name is bound
 (defun anb-lfinits (bv i c anls anb)
   (declare (xargs :stobjs (anls anb) :verify-guards nil
                   :guard (and (natp i) (signed-byte-p 64 c))
                   :measure (anb-m bv 1 (nfix (- *anl40* (nfix i))) 2)))
   (if (and (natp i) (< i (frm-pairs bv)))
       (mv-let (e anls anb) (anb-sub (frm-nth bv (+ 1 (* 2 i))) c anls anb)
         (if (not (equal e 0)) (mv e anls anb) (anb-lfinits bv (+ 1 i) c anls anb)))
     (mv 0 anls anb)))

 ; (letfn* [name fn ...] body*)
 (defun anb-letfn (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 2 8)))
   (let* ((bv (frf-nth x 1)) (code (anl-shape bv)))
     (if (not (equal code 0)) (let ((anb (anb-refuse code bv anb))) (mv code anls anb))
       (mv-let (c anls) (anb-child b anls)
         (let ((n (frm-pairs bv)))
           (mv-let (start anls) (anl-reserve c n anls)
             (mv-let (code anls anb) (anb-lfnames bv 0 c start anls anb)
               (if (not (equal code 0)) (mv code anls anb)
                 (mv-let (e anls anb) (anb-lfinits bv 0 c anls anb)
                   (if (not (equal e 0)) (mv e anls anb)
                     (mv-let (e anls anb) (anb-body (frf-rest (frf-rest x)) c anls anb)
                       (if (not (equal e 0)) (mv e anls anb)
                         (let ((anb (anb-node-s 13 n (+ 1 n) start anb))) (mv 0 anls anb))))))))))))))

 ; (try body* (catch C e h*)* (finally f*)?): the body forms before the first
 ; clause, then the clauses as TryExpr.Parser walks them
 (defun anb-try (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 2 8)))
   (let* ((xs (frf-rest x)) (nb (anb-try-n xs)))
     (mv-let (e anls anb) (anb-listn xs nb b anls anb)
       (if (not (equal e 0)) (mv e anls anb)
         (let* ((anb (anb-node 5 0 nb anb)) (cls (anb-drop xs nb)))
           (mv-let (e anls anb) (anb-try-walk cls 0 b anls anb)
             (if (not (equal e 0)) (mv e anls anb)
               (let ((anb (anb-trynode (anb-try-fin cls) anb))) (mv 0 anls anb)))))))))

 ; the clauses from cls, st 0 before a catch, 1 after one: each catch's
 ; entry left on the builder, then the finally's body
 (defun anb-try-walk (cls st b anls anb)
   (declare (xargs :stobjs (anls anb) :verify-guards nil
                   :guard (and (signed-byte-p 64 st) (signed-byte-p 64 b))
                   :measure (anb-m cls 1 0 2)))
   (if (equal (frf-len cls) 0) (mv 0 anls anb)
     (let* ((f (frf-nth cls 0)) (lastp (if (< (frf-len cls) 2) 1 0))
            (code (anf-try-step st f lastp 0)) (op (anf-try-step st f lastp 1)) (st2 (anf-try-step st f lastp 2)))
       (cond
        ((not (equal code 0)) (let ((anb (anb-refuse code f anb))) (mv code anls anb)))
        ((equal op 1)
         (let ((code (anf-catch f)))
           (if (not (equal code 0)) (let ((anb (anb-refuse-catch code f anb))) (mv code anls anb))
             (mv-let (c anls) (anb-child b anls)
               (mv-let (slot anls) (anl-reserve c 1 anls)
                 (let ((anls (anl-bind c (frm-bid (frf-nth f 2)) slot anls)))
                   (mv-let (e anls anb) (anb-body (frf-rest (frf-rest (frf-rest f))) c anls anb)
                     (if (not (equal e 0)) (mv e anls anb)
                       (let ((anb (anb-catch f slot anb)))
                         (if (< (frf-len cls) 2) (mv 0 anls anb)
                           (anb-try-walk (frf-rest cls) st2 b anls anb)))))))))))
        ((equal op 2) (anb-body (frf-rest f) b anls anb))
        ((< (frf-len cls) 2) (mv 0 anls anb))
        (t (anb-try-walk (frf-rest cls) st2 b anls anb))))))

 ; THE DRIVERS of set!, ., new, recur and fn*, after anb-an's checks: the
 ; order clj's parsers analyse their parts in, what the host decides of them
 ; read through anb-*-kind and the other hooks above

 ; (set! target value): AssignExpr.Parser's order -- the target, then the
 ; value; a host field's object is the target's part
 (defun anb-set (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 3 8)))
   (let ((k (anb-set-kind x b)))
     (cond ((equal k 2) (anb-host2 1 x b anls anb))
           ((and (equal k 1) (equal (frf-kind (frf-nth x 1)) 3))
            (mv-let (e anls anb) (anb-sub (frf-nth (frf-nth x 1) 1) b anls anb)
              (if (not (equal e 0)) (mv e anls anb)
                (mv-let (e anls anb) (anb-sub (frf-nth x 2) b anls anb)
                  (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-setnode x 2 anb))) (mv 0 anls anb)))))))
           ((equal k 0)
            (mv-let (e anls anb) (anb-sub (frf-nth x 2) b anls anb)
              (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-setnode x 1 anb))) (mv 0 anls anb)))))
           (t (mv 1 anls anb)))))

 ; (. target member args*) or (. target (member args*)): HostExpr.Parser's
 ; order -- a member it cannot read refused after the target is analysed
 ; (unless it names a class, maybeClass); then what the target is (the
 ; host's), the target unless a class names it, and the arguments
 (defun anb-dot (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 3 8)))
   (if (not (equal (anf-dot-member (frf-len x) (frf-norm (frf-nth x 2))) 0))
       (if (equal (frf-class (frf-nth x 1)) 1) (let ((anb (anb-refuse 37 x anb))) (mv 37 anls anb))
         (mv-let (e anls anb) (anb-sub (frf-nth x 1) b anls anb)
           (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-refuse 37 x anb))) (mv 37 anls anb)))))
     (let ((k (anb-dot-kind x b)))
       (cond ((equal k 2) (anb-host2 2 x b anls anb))
             ((equal k 1) (let ((anb (anb-const (frf-nth x 1) anb))) (let ((args (if (equal (frf-kind (frf-norm (frf-nth x 2))) 3) (frf-rest (frf-norm (frf-nth x 2))) (frf-rest (frf-rest (frf-rest x))))))
                  (mv-let (e anls anb) (anb-listn args (frf-len args) b anls anb)
                    (if (not (equal e 0)) (mv e anls anb)
                      (let ((anb (anb-dotnode x 1 (+ 1 (frf-len args)) anb))) (mv 0 anls anb)))))))
             ((equal k 0)
              (mv-let (e anls anb) (anb-sub (frf-nth x 1) b anls anb)
                (if (not (equal e 0)) (mv e anls anb) (let ((args (if (equal (frf-kind (frf-norm (frf-nth x 2))) 3) (frf-rest (frf-norm (frf-nth x 2))) (frf-rest (frf-rest (frf-rest x))))))
                  (mv-let (e anls anb) (anb-listn args (frf-len args) b anls anb)
                    (if (not (equal e 0)) (mv e anls anb)
                      (let ((anb (anb-dotnode x 0 (+ 1 (frf-len args)) anb))) (mv 0 anls anb))))))))
             (t (mv 1 anls anb))))))
 ; (new Class args*)
 (defun anb-new (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 3 8)))
   (if (equal (anb-new-kind x) 2) (anb-host2 3 x b anls anb)
     (let ((args (frf-rest (frf-rest x))))
       (mv-let (e anls anb) (anb-listn args (frf-len args) b anls anb)
         (if (not (equal e 0)) (mv e anls anb)
           (let ((anb (anb-newnode x (frf-len args) anb))) (mv 0 anls anb)))))))

 ; (recur args*): RecurExpr.Parser's -- its target, the arguments, then
 ; their kinds against the target's locals
 (defun anb-recur (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 3 8)))
   (let ((args (frf-rest x)))
     (if (not (equal (anb-recur-open x b) 0)) (mv 1 anls anb)
       (mv-let (e anls anb) (anb-listn args (frf-len args) b anls anb)
         (cond ((not (equal e 0)) (mv e anls anb))
               ((not (equal (anb-recur-check x b (frf-len args)) 0)) (mv 1 anls anb))
               (t (let ((anb (anb-recurnode x b (frf-len args) anb))) (mv 0 anls anb))))))))

 ; (fn* name? [params] body*) or (fn* name? ([params] body*)+): the fn's root
 ; block, its own name bound to its self slot there, each method a child
 ; block of it; after the last, the variadic check; the node its bodies and
 ; its captures (FnExpr.parse)
 (defun anb-fn (x b anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 b) :verify-guards nil
                   :measure (anb-m x 1 3 9)))
   (let* ((nm (frf-nth x 1)) (named (if (equal (frm-kind nm) 2) 1 0)))
     (mv-let (r anls) (anb-newfn b anls)
       (mv-let (self anls) (anb-self r nm anls)
         (let* ((h (anb-fn-open x r self))
                (xs (if (equal named 1) (frf-rest (frf-rest x)) (frf-rest x)))
                (n (if (equal (frm-kind (frf-nth xs 0)) 1) 1 (frf-len xs))))
           (cond ((not (equal h 0)) (mv h anls anb))
                 ((equal (frm-kind (frf-nth xs 0)) 1)
                  (mv-let (e anls anb) (anb-method xs r anls anb)
                    (cond ((not (equal e 0)) (mv e anls anb))
                          ((not (equal (anl-arity-end r anls) 0)) (let ((anb (anb-refuse 12 x anb))) (mv 12 anls anb)))
                          ((not (equal (anb-fn-check x r n) 0)) (mv 1 anls anb))
                          (t (let* ((anls (anl-caps-of r anls)) (anb (anb-fnclose x r n anls anb))) (mv 0 anls anb))))))
                 (t
                  (mv-let (e anls anb) (anb-methods xs (frf-len xs) r anls anb)
                    (cond ((not (equal e 0)) (mv e anls anb))
                          ((not (equal (anl-arity-end r anls) 0)) (let ((anb (anb-refuse 12 x anb))) (mv 12 anls anb)))
                          ((not (equal (anb-fn-check x r n) 0)) (mv 1 anls anb))
                          (t (let* ((anls (anl-caps-of r anls)) (anb (anb-fnclose x r n anls anb))) (mv 0 anls anb))))))))))))

 ; the first n methods of list ms
 (defun anb-methods (ms n r anls anb)
   (declare (xargs :stobjs (anls anb) :verify-guards nil :guard (and (integerp n) (signed-byte-p 64 r))
                   :measure (anb-m ms 1 0 2)))
   (if (or (not (natp n)) (equal n 0) (equal (frf-len ms) 0)) (mv 0 anls anb)
     (mv-let (e anls anb) (anb-method (frf-nth ms 0) r anls anb)
       (if (or (not (equal e 0)) (< (frf-len ms) 2)) (mv e anls anb)
         (anb-methods (frf-rest ms) (- n 1) r anls anb)))))

 ; ([params] body*): a parameter vector (13: "fn* needs a parameter
 ; vector"), its parameters checked (the refusal about the one at fault),
 ; reserved and bound in a child block of the fn's root r; the host's
 ; reading of them (anb-method-open), its body -- or the host's, when
 ; primitive hints rewrite it -- the recurs' kinds, then its arity recorded
 (defun anb-method (m r anls anb)
   (declare (xargs :stobjs (anls anb) :guard (signed-byte-p 64 r) :verify-guards nil
                   :measure (anb-m m 0 0 4)))
   (let* ((cl (frf-norm m)) (pv (frf-nth cl 0)))
     (if (not (equal (frm-kind pv) 1)) (let ((anb (anb-refuse 13 cl anb))) (mv 13 anls anb))
       (let ((code (anl-params pv 0)))
         (if (not (equal code 0)) (let ((anb (anb-refuse code (frm-nth pv (anl-params pv 1)) anb))) (mv code anls anb))
           (let ((nreq (anl-params pv 2)) (rest (anl-params pv 3)))
             (mv-let (mb anls) (anb-child r anls)
               (mv-let (start anls) (anl-reserve mb (+ nreq rest) anls)
                 (let* ((anls (anb-params pv 0 mb start anls))
                        (h (anb-method-open cl r mb start nreq rest)))
                   (cond
                    ((equal h 1) (mv 1 anls anb))
                    ((equal h 2)
                     (mv-let (e anls anb) (anb-host2 4 cl mb anls anb)
                       (cond ((not (equal e 0)) (mv e anls anb))
                             ((not (equal (anb-method-check mb) 0)) (mv 1 anls anb))
                             (t (mv-let (code anls) (anl-arity r nreq rest anls)
                                  (if (not (equal code 0)) (let ((anb (anb-refuse code cl anb))) (mv code anls anb))
                                    (let ((anb (anb-arity cl mb start nreq rest anb))) (mv 0 anls anb))))))))
                    (t
                     (mv-let (e anls anb) (anb-body (frf-rest cl) mb anls anb)
                       (cond ((not (equal e 0)) (mv e anls anb))
                             ((not (equal (anb-method-check mb) 0)) (mv 1 anls anb))
                             (t (mv-let (code anls) (anl-arity r nreq rest anls)
                                  (if (not (equal code 0)) (let ((anb (anb-refuse code cl anb))) (mv code anls anb))
                                    (let ((anb (anb-arity cl mb start nreq rest anb))) (mv 0 anls anb)))))))))))))))))))

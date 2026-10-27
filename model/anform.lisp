; THE ANALYZER'S SPECIAL FORMS (src/f/analyze.inc): what each special form
; is refused for, as clj's Compiler refuses it, and the shape of the node it
; builds -- at the level the Fortran is GENERATED from
; (src/f/gen/anform_gen.inc, scripts/acl2-fortran -b anform),
; guard-verified.
;
; THE FORMS are read as model/anlocal.lisp reads them (frm-kind, frm-qual
; on vectors and symbols) and through six more host reads, thin
; hand-written shims in analyze.inc (metadata stripped): frf-kind (1 a
; vector, 2 a symbol, 3 a list or seq, 4 a string, 0 anything else),
; frf-len / frf-nth (a list's elements), frf-word (a symbol that is
; unqualified catch 1, finally 2, else 0), frf-class (a symbol naming a
; class the host resolves: HostExpr.maybeClass) and frf-defvar (what
; DefExpr's lookupVar answers for a def's name: 0 a var of this namespace
; or none yet, 1 no such var -- "doesn't exist", 2 another namespace's).
; Here a form is what those reads decode it to: (:list x1 .. xn), (:str),
; (:vec x1 .. xn), (:sym id qual amp word class defvar), anything else.
;
; THE CHECKS, as clj's Compiler makes them (clojure-1.12.6, the Compiler class),
; each answering 0 or a refusal code that analyze.inc's anl_refuse words:
;   anf-if          IfExpr.Parser: 21 "Too many arguments to if", 22 "Too few"
;   anf-def         DefExpr.Parser: the docstring form, then 23 "Too many
;                   arguments to def", 24 "Too few", 25 "First argument to
;                   def must be a Symbol", 26 "Can't refer to qualified var
;                   that doesn't exist", 27 "Can't create defs outside of
;                   current ns"; and where the init and the docstring are
;   anf-quote       ConstantExpr.Parser: 28 "Wrong number of args (n) passed
;                   to quote" (an ExceptionInfo)
;   anf-throw       ThrowExpr.Parser: 29 "Too few arguments to throw, throw
;                   expects a single Throwable instance", 30 "Too many"
;   anf-try-step    TryExpr.Parser's walk, one clause at a time: what the
;                   clause is (a body form, a catch, the finally), the state
;                   after it, and 31 "Only catch or finally clause can follow
;                   catch in try expression", 32 "finally clause must be last
;                   in try expression"
;   anf-catch       a catch: 33 "Unable to resolve classname: c", then the
;                   name's check (anl-name-code, 3 or 4)
;   anf-set         AssignExpr.Parser: 34 "Malformed assignment, expecting
;                   (set! target val)"; anf-set-target 35 "Invalid assignment
;                   target" for a target no analysis makes assignable
;   anf-dot         HostExpr.Parser: 36 "Malformed member expression,
;                   expecting (. target member ...)"; anf-dot-member 37
;                   "Malformed member expression"
;   anf-new         NewExpr.Parser: 38 "wrong number of arguments,
;                   expecting: (new Classname args...)", 33 the class
; The binding forms' checks (let*, loop*, letfn*, fn*, a catch's name) are
; anlocal's, the recur's anpass's; this book uses them, it does not repeat
; them.
;
; Theorems, in the books after this one:
;   anform-proof   the analyzer these checks drive (anf-an: each special
;                  form's node, the locals through anlocal's lookup) builds a
;                  tree well-formed by anpass's reads (anf-an-wf), a symbol's
;                  local its anl-lookup answer, so the binding its lexical
;                  meaning is (anf-an-local), and each check refuses exactly
;                  what its specification says (anf-*-spec; the try's walk
;                  against the clause grammar body* catch* finally?)
;   anform-cost    the step counts: each check a constant number of reads, a
;                  try's walk one step a clause

(in-package "ACL2")

(include-book "anlocal")

; ---- THE FORMS -----------------------------------------------------------------------------

(defthm frm-kind-le-2 (<= (frm-kind x) 2) :hints (("Goal" :in-theory (enable frm-kind))) :rule-classes :linear)

(defun frf-kind (x)
  (declare (xargs :guard t))
  (cond ((and (consp x) (eq (car x) :list)) 3) ((and (consp x) (eq (car x) :str)) 4) (t (frm-kind x))))
(defun frf-len (x) (declare (xargs :guard t)) (if (equal (frf-kind x) 3) (anl-sat (anl-len (cdr x))) 0))
(defun frf-nth (x i)
  (declare (xargs :guard t))
  (if (and (equal (frf-kind x) 3) (natp i) (< i (frf-len x))) (anl-nth i (cdr x)) nil))
(defun frf-word (x)
  (declare (xargs :guard t))
  (let ((w (anl-nth 4 x))) (if (and (equal (frm-kind x) 2) (natp w) (< w 3)) w 0)))
(defun frf-class (x) (declare (xargs :guard t)) (if (and (equal (frm-kind x) 2) (equal (anl-nth 5 x) 1)) 1 0))
(defun frf-defvar (x)
  (declare (xargs :guard t))
  (let ((d (anl-nth 6 x))) (if (and (equal (frm-kind x) 2) (natp d) (< d 3)) d 0)))

(defthm frf-reads-int
  (and (natp (frf-kind x)) (natp (frf-len x)) (natp (frf-word x)) (natp (frf-class x)) (natp (frf-defvar x)))
  :rule-classes ((:type-prescription :corollary (natp (frf-kind x)))
                 (:type-prescription :corollary (natp (frf-len x)))
                 (:type-prescription :corollary (natp (frf-word x)))
                 (:type-prescription :corollary (natp (frf-class x)))
                 (:type-prescription :corollary (natp (frf-defvar x)))))

(defthm frf-len-bound (< (frf-len x) *anl40*) :rule-classes :linear)

(in-theory (disable frf-kind frf-len frf-nth frf-word frf-class frf-defvar))

; ---- THE CHECKS ----------------------------------------------------------------------------

; (if test then else?): n the form's count, the head included
(defun anf-if (n)
  (declare (xargs :guard (integerp n)))
  (cond ((< 4 n) 21) ((< n 3) 22) (t 0)))

; (def name init?) or (def name "doc" init): w 0 the code, 1 the init's
; index in the form (0 none), 2 the docstring's (0 none)
(defun anf-def (f w)
  (declare (xargs :guard (natp w)))
  (let* ((n (frf-len f))
         (doc (if (and (equal n 4) (equal (frf-kind (frf-nth f 2)) 4)) 1 0))
         (m (if (equal doc 1) 3 n))
         (s (frf-nth f 1)))
    (cond ((equal w 1) (if (equal doc 1) 3 (if (equal m 3) 2 0)))
          ((equal w 2) (if (equal doc 1) 2 0))
          ((< 3 m) 23)
          ((< m 2) 24)
          ((not (equal (frm-kind s) 2)) 25)
          ((equal (frf-defvar s) 1) 26)
          ((equal (frf-defvar s) 2) 27)
          (t 0))))

(defun anf-quote (n) (declare (xargs :guard (integerp n))) (if (equal n 2) 0 28))

(defun anf-throw (n)
  (declare (xargs :guard (integerp n)))
  (cond ((< n 2) 29) ((< 2 n) 30) (t 0)))

; a try clause's operator: 1 (catch ..), 2 (finally ..), 0 a body form
(defun anf-try-op (f)
  (declare (xargs :guard t))
  (if (and (equal (frf-kind f) 3) (< 0 (frf-len f))) (frf-word (frf-nth f 0)) 0))

; TryExpr.Parser's walk: st 0 before a catch, 1 after one; lastp 1 when f is
; the last clause. w 0 the code, 1 the clause's kind (anf-try-op), 2 the state after
(defun anf-try-step (st f lastp w)
  (declare (xargs :guard (and (integerp st) (integerp lastp) (natp w))))
  (let ((op (anf-try-op f)))
    (cond ((equal w 1) op)
          ((equal w 2) (if (equal op 1) 1 st))
          ((equal op 0) (if (equal st 1) 31 0))
          ((equal op 2) (if (equal lastp 1) 0 32))
          (t 0))))

; (catch class name body*): the class, then the name
(defun anf-catch (f)
  (declare (xargs :guard t))
  (if (equal (frf-class (frf-nth f 1)) 0) 33 (anl-name-code (frf-nth f 2))))

(defun anf-set (n) (declare (xargs :guard (integerp n))) (if (equal n 3) 0 34))

; a set! target that can be assignable once analysed: a symbol (a var, a
; local, a field) or a list with a symbol at its head (a field access, a
; macro that expands to one); anything else analyses to an expression that
; is not
(defun anf-set-target (x)
  (declare (xargs :guard t))
  (let ((k (frf-kind x)))
    (cond ((equal k 2) 0)
          ((and (equal k 3) (< 0 (frf-len x)) (equal (frm-kind (frf-nth x 0)) 2)) 0)
          (t 35))))

; (. target member ...): its count, before the target is analysed
(defun anf-dot (f) (declare (xargs :guard t)) (if (< (frf-len f) 3) 36 0))

; and its member, m the form's third as a list (a seq realised), n the
; form's count: a field (. x f), or a call whose head is a symbol,
; (. x (m args*)) or (. x m args+)
(defun anf-dot-member (n m)
  (declare (xargs :guard (integerp n)))
  (cond ((and (equal n 3) (equal (frm-kind m) 2)) 0)
        ((equal (frf-kind m) 3) (if (equal (frm-kind (frf-nth m 0)) 2) 0 37))
        ((equal (frm-kind m) 2) 0)
        (t 37)))

; (new Classname args*)
(defun anf-new (f)
  (declare (xargs :guard t))
  (cond ((< (frf-len f) 2) 38) ((equal (frf-class (frf-nth f 1)) 0) 33) (t 0)))

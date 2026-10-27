; THE ANALYZER'S SPECIAL FORMS' CHECKS, PROVED (model/anform.lisp): each
; refuses exactly what its specification -- clj's parser, stated apart --
; refuses. The nodes the forms build, and the analysis that builds them,
; are model/anbuild.lisp's (anbuild-proof.lisp: a whole analysis with no
; error leaves one well-formed node), which replaced the one step of it
; this book held (anf-step).
;
; Theorems:
;   anf-try-code-spec the try's walk refuses exactly the clause lists the
;                     grammar body* catch* finally? does not generate
;   anf-dot-member-spec  the member is refused exactly when HostExpr.Parser's
;                     call (the third form if a seq, else the rest from it)
;                     does not begin with a symbol, and it is no field
;   anf-def-places    an accepted def's init and docstring are where
;                     DefExpr.Parser takes them

(in-package "ACL2")

(include-book "anform")

(defthm anl-len-len (equal (anl-len l) (len l)))

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

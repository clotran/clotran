; THE AHEAD-OF-TIME COMPILER'S ELIGIBILITY SCAN (src/clj/clotran/compiler.cljf,
; decline-reason's recur clause), at the level the Fortran is GENERATED from
; (src/f/gen/aot_gen.inc, scripts/acl2-fortran -b aot), guard-verified.
; model/aot-PLAN.md is the plan this is the first slice of.
;
; The compiler emits code for the node kinds compiler.cljf's compiled-ops
; names (aot-cop); a node of any other kind is pooled and run WHOLE by the
; interpreter. A recur under such a node that is not inside a loop, fn or
; lazy seq below it targets the compiled code around it -- the interpreter
; would hand its recur back as a value and the compiled loop would never go
; round. The compiler declines such a fn (rather than compile it wrong).
;
; THE TREE is anpass's (model/anpass.lisp: a node (:ast id kind i2 kids s3
; caps alts rfn), read through its ten shims), with one more element and two
; more reads: (:ast id kind i2 kids s3 caps alts rfn bods), bods a fn's or a
; lazy seq's arity bodies, in its template's order (aot-nbods / aot-bod,
; Eval.f90's shims on the OBJ_AST: an arity whose body is a flat or VM form
; answers no node, as clotran-ast exports it).
;
;   aot-fr   a recur under the node, not past a loop, fn or lazy seq
;   aot-sc   the scan: some node of a kind not emitted, anywhere under the
;            body -- children, a def's metadata, a case's branches, a try's
;            catches, a deftype's methods, a fn's or lazy seq's bodies --
;            has aot-fr. nil: the fn may be compiled.
;
; model/aot-proof.lisp proves what it means (aot-sc-sound, aot-handed-norec)
; and counts it (aot-sc-steps-bound).

(in-package "ACL2")

(include-book "anpass")

; ---- THE BODIES' READS ----------------------------------------------------------------------

(defun aot-nbods (x) (declare (xargs :guard t)) (if (ast-p x) (anp-sat (anp-len (anp-nth 9 x))) 0))
(defun aot-bod (x i)
  (declare (xargs :guard t))
  (if (and (ast-p x) (natp i) (< i (aot-nbods x))) (anp-nth i (anp-nth 9 x)) nil))

(defthm aot-nbods-sb64 (and (anp40p (aot-nbods x)) (natp (aot-nbods x)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (aot-nbods x)))))

(defthm aot-bod-count
  (implies (not (equal (ast-kind x) 0)) (< (acl2-count (aot-bod x i)) (acl2-count x)))
  :hints (("Goal" :in-theory (enable ast-kind ast-p anp-nth)
           :use ((:instance anp-nth-count (l (anp-nth 9 x)))
                 (:instance anp-nth-count (i 8) (l (cdr x))))))
  :rule-classes :linear)

(in-theory (disable aot-nbods aot-bod))

; the children a sequence walks: 3 the alternatives, 5 the bodies, else the children
(defun aot-ch (fl x i)
  (declare (xargs :guard t))
  (cond ((equal fl 3) (ast-alt x i)) ((equal fl 5) (aot-bod x i)) (t (ast-kid x i))))

(defthm aot-ch-count (implies (not (equal (ast-kind x) 0)) (< (acl2-count (aot-ch fl x i)) (acl2-count x)))
  :rule-classes :linear)

; compiler.cljf's compiled-ops: const local var if do call let loop recur fn lazy new dot
(defun aot-cop (k)
  (declare (xargs :guard t))
  (or (equal k 1) (equal k 2) (equal k 3) (equal k 4) (equal k 5) (equal k 6) (equal k 11) (equal k 12)
      (equal k 14) (equal k 15) (equal k 16) (equal k 21) (equal k 22)))

; ---- A RECUR UNDER A NODE --------------------------------------------------------------------

(defun aot-fr (fl x j m)
  (declare (xargs :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m))
                  :measure (anp-meas fl x j m nil)
                  :verify-guards nil))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k *n-recur*) t)
              ((or (equal k 0) (equal k *n-loop*) (equal k *n-fn*) (equal k *n-lazy*) (equal k *n-deftype*)) nil)
              ((equal k *n-try*)
               (if (aot-fr 0 (ast-kid x 0) 0 0) t (if (aot-fr 3 x 0 (ast-nalts x)) t (aot-fr 0 (ast-kid x 1) 0 0))))
              ((equal k *n-case*) (if (aot-fr 3 x 0 (ast-nalts x)) t (aot-fr 1 x 0 (ast-nkids x))))
              ((equal k *n-def*) (if (aot-fr 0 (ast-s3 x) 0 0) t (aot-fr 1 x 0 (ast-nkids x))))
              (t (aot-fr 1 x 0 (ast-nkids x)))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (if (aot-fr 0 (aot-ch fl x j) 0 0) t (aot-fr fl x (+ 1 j) m))
      nil)))

(verify-guards aot-fr)

; ---- THE SCAN --------------------------------------------------------------------------------

(defun aot-sc (fl x j m)
  (declare (xargs :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m))
                  :measure (anp-meas fl x j m nil)
                  :verify-guards nil))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k 0) nil)
              ((and (not (aot-cop k)) (aot-fr 0 x 0 0)) t)
              ((aot-sc 1 x 0 (ast-nkids x)) t)
              ((equal k *n-def*) (aot-sc 0 (ast-s3 x) 0 0))
              ((or (equal k *n-try*) (equal k *n-case*) (equal k *n-deftype*)) (aot-sc 3 x 0 (ast-nalts x)))
              ((or (equal k *n-fn*) (equal k *n-lazy*)) (aot-sc 5 x 0 (aot-nbods x)))
              (t nil)))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (if (aot-sc 0 (aot-ch fl x j) 0 0) t (aot-sc fl x (+ 1 j) m))
      nil)))

(verify-guards aot-sc)

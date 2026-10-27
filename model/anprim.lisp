; THE ANALYZER'S PRIMITIVE KINDS AND ARRAY HINTS (src/f/analyze.inc), at
; the level the Fortran is GENERATED from (src/f/gen/anprim_gen.inc,
; scripts/acl2-fortran -b anprim), guard-verified.
;
; clj types an expression statically (Compiler.maybePrimitiveType), and
; clotran does so for two of its refusals (DEVIATIONS 48): a hinted let or
; loop local whose init is a primitive (LocalBinding), and a recur to a
; ^long or ^double fn parameter whose argument is not that primitive
; (RecurExpr); and a third, a ^long or ^double return whose body is
; another primitive (ObjMethod.emitBody). A kind is an integer: 1 long,
; 2 double, 3 int, 4 boolean, 5 float, 6 short, 7 byte, 8 char (Eval.f90's
; PK_*), -1 an Object for certain, 0 not known -- and an unknown is never
; refused, so what clotran cannot type it lets through rather than refuse
; what clj accepts.
;
; Here is what each kind decides, as the host's tree reads hand it over
; (a node's kind: analyze.inc static_prim, constrained here as apk-kid):
;   apk-arith    a Numbers op's kind, folded left over its operands as the
;                nary inline nests it (arith_kind)
;   apk-loop     a loop local's kind: its init's, widened as clj's first
;                pass types it (an int a long, a float a double)
;   apk-let      a let or loop local's kind, or the refusal of a hinted
;                local with a primitive init (anb_let_kind)
;   apk-ret      a hinted return's refusal (anb_let_ret)
;   apk-recur-ok a recur argument against its target's primitive
;                (recur_args_ok)
;   apk-elem     an array hint's element kind, by the hint's place in the
;                table of array type names (array_elem_kind, bind_array_hint)
; and what an array hint is: apk-cast, the checkcast clj emits where a
; hinted value is used as an array (clotran-array-cast, Eval.f90
; B_ARRAYCAST) -- the value itself, or a refusal.
;
; Theorems, in anprim-proof.lisp: a hint never changes a value, only how
; it is represented -- the cast is the identity on every value it does not
; refuse, and refuses only what is not an array of its kind; a widening
; keeps a number's class (an integer kind stays one, a floating one stays
; one) and is idempotent; each refusal is exactly clj's rule; the fold's
; answer is a long, a double, an Object or unknown. anprim-cost.lisp
; counts the steps.

(in-package "ACL2")

(include-book "anlocal")

; ---- THE KINDS --------------------------------------------------------------------------------

(defun apk-int-p (k) (declare (xargs :guard t)) (or (equal k 1) (equal k 3) (equal k 6) (equal k 7) (equal k 8)))
(defun apk-float-p (k) (declare (xargs :guard t)) (or (equal k 2) (equal k 5)))
(defun apk-prim-p (k) (declare (xargs :guard t)) (or (apk-int-p k) (apk-float-p k) (equal k 4)))
(defun apk-kind-p (k) (declare (xargs :guard t)) (or (apk-prim-p k) (equal k 0) (equal k -1)))

; the operand of a Numbers op: a primitive integer a long, a float a double
(defun apk-num (a) (declare (xargs :guard t)) (cond ((apk-int-p a) 1) ((equal a 5) 2) (t a)))

; ---- WHAT THE HOST READS OF THE TREE ------------------------------------------------------------

; operand i's kind, of a call's children kids in scope sc (static_prim)
(encapsulate
  (((apk-kid * * *) => * :formals (kids sc i) :guard t))
  (local (defun apk-kid (kids sc i) (declare (xargs :guard t) (ignore kids sc i)) 0))
  (defthm apk-kid-kind (and (integerp (apk-kid kids sc i)) (apk-kind-p (apk-kid kids sc i)))))

; ---- THE DECISIONS ------------------------------------------------------------------------------

; one operand a (already a long, a double or an Object) folded into k, how:
;   1 add, subtract, multiply: two longs a long; a double beside anything
;     typed a double (Numbers.add(double, Object)); else an Object
;   2 divide and the promoting ops: as 1, but two longs an Object (a Number)
;   3 quot, rem: an Object operand makes an Object, else as 1
;   4 one operand: its own
;   5 max, min: a primitive only when both are the same one
;   6 one operand, promoting (inc', dec'): a double stays one
(defun apk-step (how k a)
  (declare (xargs :guard t))
  (cond ((equal how 5) (if (equal k a) k -1))
        ((and (equal how 3) (or (equal k -1) (equal a -1))) -1)
        ((or (equal k 2) (equal a 2)) 2)
        ((or (equal k -1) (equal a -1)) -1)
        ((equal how 2) -1)
        (t k)))

; operands i .. n-1 of kids folded into k (i 1 the first, k unused there);
; an unknown or boolean operand makes the whole unknown
(defun apk-fold (kids sc how i n k)
  (declare (xargs :guard (and (natp i) (natp n) (< n *anl40*)) :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n) (< n *anl40*))
      (let ((a (apk-kid kids sc i)))
        (if (or (equal a 0) (equal a 4)) 0
          (let ((a (apk-num a)))
            (apk-fold kids sc how (+ 1 i) n (if (equal i 1) a (apk-step how k a))))))
    k))

; a Numbers op's kind, its operands kids 1 .. n-1 (kids 0 the op)
(defun apk-arith (kids sc how n)
  (declare (xargs :guard (and (natp n) (< n *anl40*))))
  (let ((k (apk-fold kids sc how 1 n 0)))
    (if (and (equal how 6) (not (equal k 2)) (not (equal k 0))) -1 k)))

; a loop local: its init's kind, an int a long, a float a double
(defun apk-loop (pk) (declare (xargs :guard t)) (cond ((equal pk 3) 1) ((equal pk 5) 2) (t pk)))

; a let (loopp 0) or loop (1) local with an init of kind pk, hinted 1 when
; its name carries a tag, rk its kind as a return-hinted fn's argument (the
; loop* such a fn's body is, prim_hint_body), -100 when it is none: its
; kind, or -2, LocalBinding's refusal of a hinted primitive init
(defun apk-let (pk hinted loopp rk)
  (declare (xargs :guard t))
  (cond ((and (integerp pk) (< 0 pk) (equal hinted 1)) -2)
        ((not (equal loopp 1)) pk)
        ((equal rk -100) (apk-loop pk))
        ((equal rk 0) -1)
        (t rk)))

; a ^long (1) or ^double (2) return, ret, of a body of kind bk: 1 when
; ObjMethod.emitBody refuses it (a long takes an int, a double a float)
(defun apk-ret (ret bk)
  (declare (xargs :guard t))
  (if (and (integerp ret) (< 0 ret) (integerp bk) (< 0 bk) (not (equal bk ret))
           (not (and (equal ret 1) (equal bk 3))) (not (and (equal ret 2) (equal bk 5))))
      1 0))

; a recur argument of kind k to a local of primitive p (0 or less: none):
; 1 when it matches, as RecurExpr's check finds it
(defun apk-recur-ok (p k)
  (declare (xargs :guard t))
  (cond ((not (and (integerp p) (< 0 p))) 1)
        ((equal k 0) 1)
        ((and (equal p 1) (apk-int-p k)) 1)
        ((and (equal p 2) (apk-float-p k)) 1)
        (t 0)))

; an array hint's element kind: the hint's place in the table doubles,
; longs, ints, floats, shorts, bytes, chars, booleans (0 .. 7), anything
; else an Object's array (-1)
(defun apk-elem (i)
  (declare (xargs :guard t))
  (case i (0 2) (1 1) (2 3) (3 5) (4 6) (5 7) (6 8) (7 4) (otherwise -1)))

; ---- WHAT AN ARRAY HINT IS ----------------------------------------------------------------------

; a value as the cast reads it: (:arr ek . elems) an array of element kind
; ek, anything else not an array; (clotran-array-cast v hint) is v, or the
; refusal :cce (a ClassCastException naming both types; nil, the
; NullPointerException the array operation would raise)
(defun apk-cast (ek v)
  (declare (xargs :guard t))
  (if (and (consp v) (eq (car v) :arr) (consp (cdr v)) (equal (cadr v) ek)) v :cce))

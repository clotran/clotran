; THE PRIMITIVE KINDS AND ARRAY HINTS, PROVED (model/anprim.lisp): a hint
; never changes a value, only how it is represented; each kind decides
; exactly clj's rule.
(in-package "ACL2")

(include-book "anprim")

; ---- A HINT NEVER CHANGES A VALUE ---------------------------------------------------------------

; the cast is the value itself whenever it does not refuse
(defthm apk-cast-identity
  (implies (not (equal (apk-cast ek v) :cce)) (equal (apk-cast ek v) v)))

; it refuses exactly what is not an array of the hint's kind, and an array
; of it comes back unchanged, every element where it was
(defthm apk-cast-refuses
  (iff (equal (apk-cast ek v) :cce)
       (not (and (consp v) (eq (car v) :arr) (consp (cdr v)) (equal (cadr v) ek)))))
(defthm apk-cast-array
  (implies (and (consp v) (eq (car v) :arr) (consp (cdr v)) (equal (cadr v) ek))
           (and (equal (apk-cast ek v) v) (equal (cddr (apk-cast ek v)) (cddr v)))))

; a hint names a kind, never an unknown one
(defthm apk-elem-kind (and (apk-kind-p (apk-elem i)) (not (equal (apk-elem i) 0))))

; a widening keeps a number's class -- an integer kind stays one, a
; floating one stays one, the rest are left alone -- and is idempotent:
; it changes the representation (int to long, float to double), not what
; kind of number the value is
(defthm apk-loop-class
  (and (equal (apk-int-p (apk-loop k)) (apk-int-p k))
       (equal (apk-float-p (apk-loop k)) (apk-float-p k))
       (equal (apk-loop (apk-loop k)) (apk-loop k))
       (implies (apk-kind-p k) (apk-kind-p (apk-loop k)))
       (implies (not (apk-prim-p k)) (equal (apk-loop k) k))))
(defthm apk-num-class
  (and (implies (apk-int-p k) (equal (apk-num k) 1))
       (implies (apk-float-p k) (equal (apk-num k) 2))
       (equal (apk-num (apk-num k)) (apk-num k))
       (implies (not (apk-prim-p k)) (equal (apk-num k) k))))

; ---- EACH REFUSAL IS CLJ'S RULE -----------------------------------------------------------------

; LocalBinding: a let or loop local is refused exactly when it is hinted
; and its init is a primitive; else a let local is its init's kind
(defthm apk-let-refuses
  (implies (and (apk-kind-p pk) (not (equal rk -2)))
           (iff (equal (apk-let pk hinted loopp rk) -2)
                (and (integerp pk) (< 0 pk) (equal hinted 1)))))
(defthm apk-let-let
  (implies (and (not (equal loopp 1)) (not (and (integerp pk) (< 0 pk) (equal hinted 1))))
           (equal (apk-let pk hinted loopp rk) pk)))
(defthm apk-let-loop
  (implies (and (equal loopp 1) (equal rk -100) (not (and (integerp pk) (< 0 pk) (equal hinted 1))))
           (equal (apk-let pk hinted loopp rk) (apk-loop pk))))

; ObjMethod.emitBody: a ^long or ^double return takes a body not typed, or
; one whose loop widening is that primitive
(defthm apk-ret-spec
  (implies (member ret '(1 2))
           (iff (equal (apk-ret ret bk) 0)
                (or (not (and (integerp bk) (< 0 bk))) (equal (apk-loop bk) ret)))))

; RecurExpr: an argument matches a ^long or ^double local exactly when it
; is not typed or is that kind of number, and its widening never changes it
(defthm apk-recur-ok-spec
  (implies (member p '(1 2))
           (equal (apk-recur-ok p k) (if (or (equal k 0) (equal (apk-num k) p)) 1 0))))
(defthm apk-recur-ok-widen
  (equal (apk-recur-ok p (apk-loop k)) (apk-recur-ok p k)))

; ---- THE FOLD ---------------------------------------------------------------------------------

; a Numbers op is a long, a double, an Object, or not known
(defthm apk-num-of-kind
  (implies (and (apk-kind-p a) (not (equal a 0)) (not (equal a 4))) (member (apk-num a) '(1 2 -1))))
(defthm apk-step-range
  (implies (and (member k '(0 1 2 -1)) (member a '(1 2 -1))) (member (apk-step how k a) '(0 1 2 -1))))
(defthm apk-fold-range
  (implies (member k '(0 1 2 -1)) (member (apk-fold kids sc how i n k) '(0 1 2 -1)))
  :hints (("Goal" :induct (apk-fold kids sc how i n k) :in-theory (disable apk-step apk-num))
          ("Subgoal *1/2" :use ((:instance apk-num-of-kind (a (apk-kid kids sc i)))
                                (:instance apk-step-range (a (apk-num (apk-kid kids sc i)))))
           :in-theory (disable apk-num-of-kind apk-step-range apk-step apk-num))))
(defthm apk-arith-range (member (apk-arith kids sc how n) '(0 1 2 -1))
  :hints (("Goal" :use ((:instance apk-fold-range (i 1) (k 0))) :in-theory (disable apk-fold-range apk-fold))))

; an operand not known, or a boolean, leaves the whole not known
(defthm apk-fold-unknown
  (implies (and (natp i) (natp n) (< i n) (< n *anl40*) (member (apk-kid kids sc i) '(0 4)))
           (equal (apk-fold kids sc how i n k) 0)))

; two longs added are a long, a long and a double a double
(defthm apk-arith-long-long
  (implies (and (equal (apk-kid kids sc 1) 1) (equal (apk-kid kids sc 2) 1))
           (equal (apk-arith kids sc 1 3) 1)))
(defthm apk-arith-long-double
  (implies (and (equal (apk-kid kids sc 1) 1) (equal (apk-kid kids sc 2) 2))
           (equal (apk-arith kids sc 1 3) 2)))

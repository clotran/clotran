; THE ANALYZER'S BINDING-FORM CHECKS, PROVED (model/anlocal.lisp's anl-shape,
; anl-name-code, anl-params, anl-arity, anl-arity-end): each refuses exactly
; what its specification, written as a statement about the form and not as
; a walk, says clj's Compiler refuses.
;
;   anl-shape-spec    a binding vector is refused exactly when it is no
;                     vector (1), or a vector of odd length (2)
;   anl-name-code-spec  a name exactly when it is no symbol (3), or a
;                     qualified one (4)
;   anl-params-spec   a parameter vector exactly when an element is no
;                     symbol or a qualified one, or it has two &s, or more
;                     than one name after its &, or more than 20 required;
;                     and when it is not, the required count is where its &
;                     stands (or its length) and a rest parameter comes
;                     exactly when one name follows the &
;   anl-arity-spec    a method exactly when it is a second variadic one
;                     (10) or a fixed arity the fn has (11), and a fixed one
;                     is then the fn's; anl-arity-end-spec: a fn exactly when
;                     a fixed arity is above the variadic one's (12)

(in-package "ACL2")

(include-book "anlocal-frames")

; ---- THE SHAPE AND THE NAMES ----------------------------------------------------------------

(defthm anl-odd-is (implies (natp n) (equal (anl-odd n) (if (evenp n) 0 1)))
  :hints (("Goal" :induct (anl-odd n))))

(defthm anl-shape-spec
  (implies (natp (frm-count bv))
           (equal (anl-shape bv)
                  (cond ((not (equal (frm-kind bv) 1)) 1) ((not (evenp (frm-count bv))) 2) (t 0)))))

(defthm anl-name-code-spec
  (equal (anl-name-code x) (cond ((not (equal (frm-kind x) 2)) 3) ((equal (frm-qual x) 1) 4) (t 0))))

; ---- THE PARAMETERS -------------------------------------------------------------------------

; every element an unqualified symbol
(defun anl-syms-ok (l)
  (if (consp l) (and (equal (frm-kind (car l)) 2) (equal (frm-qual (car l)) 0) (anl-syms-ok (cdr l))) t))

(defun anl-amps (l) (if (consp l) (+ (frm-amp (car l)) (anl-amps (cdr l))) 0))

; where the first & stands, or the length
(defun anl-amp-pos (l) (if (consp l) (if (equal (frm-amp (car l)) 1) 0 (+ 1 (anl-amp-pos (cdr l)))) 0))

; THE SPECIFICATION, of the elements a walk in state st with nreq required
; so far has left: REQ, before any &; REST, just after it; DONE, after the
; rest parameter
(defun anl-pspec (l st nreq)
  (cond ((equal st 0)
         (and (anl-syms-ok l)
              (or (and (equal (anl-amps l) 0) (<= (+ nreq (len l)) 20))
                  (and (equal (anl-amps l) 1) (<= (- (len l) (anl-amp-pos l)) 2) (<= (+ nreq (anl-amp-pos l)) 20)))))
        ((equal st 1) (and (anl-syms-ok l) (equal (anl-amps l) 0) (<= (len l) 1) (<= nreq 20)))
        (t (and (atom l) (<= nreq 20)))))

; the walk on the list
(defun anl-pwl (l i st nreq rest w)
  (if (consp l)
      (let ((p (car l)))
        (cond ((not (equal (frm-kind p) 2)) (anl-pans w 5 i nreq rest))
              ((equal (frm-qual p) 1) (anl-pans w 6 i nreq rest))
              ((equal (frm-amp p) 1) (if (equal st 0) (anl-pwl (cdr l) (+ 1 i) 1 nreq rest w) (anl-pans w 7 i nreq rest)))
              ((equal st 0) (anl-pwl (cdr l) (+ 1 i) 0 (+ 1 nreq) rest w))
              ((equal st 1) (anl-pwl (cdr l) (+ 1 i) 2 nreq 1 w))
              (t (anl-pans w 8 i nreq rest))))
    (if (< 20 (nfix nreq)) (anl-pans w 9 i nreq rest) (anl-pans w 0 i nreq rest))))

(defthm anl-anl-len-is-len (equal (anl-len l) (len l)))

(defthm anl-nth-is (implies (natp i) (equal (anl-nth i l) (car (nthcdr i l))))
  :hints (("Goal" :induct (anl-nth i l))))

(defthm anl-frm-nth-nthcdr
  (implies (and (equal (frm-kind pv) 1) (natp i) (< i (frm-count pv)))
           (equal (frm-nth pv i) (car (nthcdr i (cdr pv)))))
  :hints (("Goal" :in-theory (enable frm-nth frm-count frm-kind anl-nth))))

(defun anl-ind-pw (i n l)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n)) (anl-ind-pw (+ 1 i) n (cdr l)) l))

(defthm anl-len-count
  (implies (and (equal (frm-kind pv) 1) (< (len (cdr pv)) *anl40*))
           (equal (frm-count pv) (len (cdr pv))))
  :hints (("Goal" :in-theory (enable frm-count frm-kind anl-len anl-sat))))


(defthm anl-nthcdr-cdr (implies (natp i) (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l))))
(defthm anl-consp-nthcdr (implies (natp i) (equal (consp (nthcdr i l)) (< i (len l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr))))

(defthm anl-pw-is-pwl
  (implies (and (equal (frm-kind pv) 1) (< (len (cdr pv)) *anl40*) (equal n (len (cdr pv))) (natp i) (<= i n) (natp nreq))
           (equal (anl-pw pv i n st nreq rest w) (anl-pwl (nthcdr i (cdr pv)) i st nreq rest w)))
  :hints (("Goal" :induct (anl-pw pv i n st nreq rest w))))

(defthm anl-pwl-spec
  (implies (and (natp nreq) (member st '(0 1 2)))
           (equal (equal (anl-pwl l i st nreq rest 0) 0) (if (anl-pspec l st nreq) t nil)))
  :hints (("Goal" :induct (anl-pwl l i st nreq rest 0))))

(defthm anl-pwl-nreq
  (implies (and (natp nreq) (equal st 0) (anl-pspec l st nreq))
           (equal (anl-pwl l i st nreq rest 2) (+ nreq (anl-amp-pos l))))
  :hints (("Goal" :induct (anl-pwl l i st nreq rest 2))))

(defthm anl-pwl-rest
  (implies (and (natp nreq) (equal st 0) (anl-pspec l st nreq) (equal rest 0))
           (equal (anl-pwl l i st nreq rest 3) (if (equal (- (len l) (anl-amp-pos l)) 2) 1 0)))
  :hints (("Goal" :induct (anl-pwl l i st nreq rest 3))))

; THE THEOREM: FnMethod.parse's refusals, and what it takes
(defthm anl-params-spec
  (implies (and (equal (frm-kind pv) 1) (< (len (cdr pv)) *anl40*))
           (and (equal (equal (anl-params pv 0) 0) (if (anl-pspec (cdr pv) 0 0) t nil))
                (implies (anl-pspec (cdr pv) 0 0)
                         (and (equal (anl-params pv 2) (anl-amp-pos (cdr pv)))
                              (equal (anl-params pv 3) (if (equal (- (len (cdr pv)) (anl-amp-pos (cdr pv))) 2) 1 0)))))))

; ---- THE ARITIES ----------------------------------------------------------------------------

; the fixed arities a list holds, newest first
(defun anl-fixed (a anls)
  (declare (xargs :stobjs anls :measure (nfix a) :ruler-extenders :all :verify-guards nil))
  (if (and (natp a) (< a (anl-na anls)))
      (cons (anl-g-an a anls)
            (let ((j (anl-g-anext a anls))) (if (and (natp j) (< j a)) (anl-fixed j anls) nil)))
    nil))

(defun anl-some-gt (l n) (if (consp l) (or (< n (car l)) (anl-some-gt (cdr l) n)) nil))

(defthm anl-has-fixed-member
  (equal (anl-has-fixed a n anls) (if (member-equal n (anl-fixed a anls)) t nil))
  :hints (("Goal" :induct (anl-fixed a anls))))

(defthm anl-gt-fixed-some-gt
  (equal (anl-gt-fixed a n anls) (if (anl-some-gt (anl-fixed a anls) n) t nil))
  :hints (("Goal" :induct (anl-fixed a anls))))

; fn f's new fixed arity: record na, at the head of its list
(defthm anl-fixed-push-a-old
  (implies (and (natp (anl-na anls)) (< a (anl-na anls)))
           (equal (anl-fixed a (anl-push-a f n anls)) (anl-fixed a anls)))
  :hints (("Goal" :induct (anl-fixed a anls) :expand ((anl-fixed a (anl-push-a f n anls))))
          ("Subgoal *1/1" :in-theory (enable anl-push-a))))

(defthm anl-push-a-new
  (implies (and (natp f) (< f (anl-nf anls)) (< f (anl-fah-length anls))
                (natp (anl-na anls)) (< (anl-na anls) (- *anl40* 1)))
           (let ((a2 (anl-push-a f n anls)) (a (anl-na anls)))
             (and (equal (anl-g-fah f a2) a) (equal (anl-na a2) (+ 1 a))
                  (equal (anl-g-an a a2) n) (equal (anl-g-anext a a2) (anl-g-fah f anls)))))
  :hints (("Goal" :in-theory (enable anl-push-a))))

(defthm anl-push-a-head
  (implies (and (natp f) (< f (anl-nf anls)) (< f (anl-fah-length anls))
                (natp (anl-na anls)) (< (anl-na anls) (- *anl40* 1)) (< (anl-g-fah f anls) (anl-na anls)))
           (equal (anl-fixed (anl-g-fah f (anl-push-a f n anls)) (anl-push-a f n anls))
                  (cons n (anl-fixed (anl-g-fah f anls) anls))))
  :hints (("Goal" :in-theory (disable anl-push-a)
                  :expand ((anl-fixed (anl-na anls) (anl-push-a f n anls))))))

; THE OVERLOAD CHECK, after each method (FnExpr.parse): a second variadic
; one, or a fixed arity the fn has, is refused
(defthm anl-arity-spec
  (implies (natp (anl-g-bfn b anls))
           (equal (mv-nth 0 (anl-arity b nreq rest anls))
                  (let ((f (anl-g-bfn b anls)))
                    (cond ((equal rest 1) (if (<= 0 (anl-g-fvar f anls)) 10 0))
                          ((member-equal nreq (anl-fixed (anl-g-fah f anls) anls)) 11)
                          (t 0))))))

; and a method it takes is the fn's: a variadic one's required count, a
; fixed one at the head of its list
(defthm anl-arity-records
  (implies (and (natp (anl-g-bfn b anls)) (< (anl-g-bfn b anls) (anl-nf anls))
                (< (anl-g-bfn b anls) (anl-fvar-length anls)) (< (anl-g-bfn b anls) (anl-fah-length anls))
                (natp (anl-na anls)) (< (anl-na anls) (- *anl40* 1))
                (< (anl-g-fah (anl-g-bfn b anls) anls) (anl-na anls))
                (equal (mv-nth 0 (anl-arity b nreq rest anls)) 0))
           (let ((f (anl-g-bfn b anls)) (a2 (mv-nth 1 (anl-arity b nreq rest anls))))
             (if (equal rest 1)
                 (equal (anl-g-fvar f a2) nreq)
               (equal (anl-fixed (anl-g-fah f a2) a2) (cons nreq (anl-fixed (anl-g-fah f anls) anls))))))
  :hints (("Goal" :in-theory (disable anl-push-a))))

; THE LAST CHECK: a fixed arity above the variadic one's
(defthm anl-arity-end-spec
  (equal (anl-arity-end b anls)
         (let ((f (anl-g-bfn b anls)))
           (if (and (<= 0 (anl-g-fvar f anls)) (anl-some-gt (anl-fixed (anl-g-fah f anls) anls) (anl-g-fvar f anls)))
               12 0))))

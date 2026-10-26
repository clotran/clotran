; THE COST OF THE ANALYZER'S LOCALS (model/anlocal.lisp), counted as the
; generated Fortran runs them: every call of a walk -- a record of a list,
; a block of a chain, a fn crossed, an element of a vector -- is a step; a
; record's write, and a host read, one step each.
;
;   anl-xfind-steps-bound    a block's bindings: at most x + 1 steps from
;                            record x (each step to an older one)
;   anl-chain-find-steps-bound  a fn's blocks from b: at most (b + 1)(nx + 2)
;   anl-cfind-steps-bound    a fn's captures: at most c + 1
;   anl-lookup-steps-bound   a name resolved: at most (b + 1)((b + 1)(nx + 2)
;                            + nc + 4) -- for each fn crossed (at most b, the
;                            chain's blocks), its blocks and its captures
;                            walked, and a capture made
;   anl-pw-steps-bound       a parameter vector: at most n + 1 (n elements)
;   anl-odd-steps-bound      a binding vector's parity: at most n/2 + 1
;   anl-has-fixed-steps-bound, anl-gt-fixed-steps-bound  a fn's arities:
;                            at most a + 1
;   anl-caps-steps-bound, anl-names-steps-bound  a fn's captures, its named
;                            slots, read back: at most c + 1, n + 1
;   anl-ev-find-steps-bound  a name looked for among the env's: at most
;                            nev + 1; anl-env-walk-steps-bound: the env's walk,
;                            at most (b + 1)((b + 1)(nx + 2) + nc + 2) records,
;                            each with one such search
;
; The bounds are worst cases over every state, records in any order: in the
; analyzer's states a block's list holds only its own bindings, so a lookup
; walks only the bindings visible from b, and the chain is as deep as the
; nesting of the forms.

(in-package "ACL2")

(include-book "anlocal-frames")

(defun anl-xfind-steps (x s anls)
  (declare (xargs :stobjs anls :measure (nfix x) :verify-guards nil))
  (if (and (natp x) (< x (anl-nx anls)))
      (if (equal (anl-g-xnm x anls) s) 1
        (let ((j (anl-g-xnext x anls))) (if (and (natp j) (< j x)) (+ 1 (anl-xfind-steps j s anls)) 1)))
    1))

(defthm anl-xfind-steps-bound
  (<= (anl-xfind-steps x s anls) (+ 1 (nfix x)))
  :rule-classes :linear)

(defthm anl-xfind-steps-nx
  (implies (natp (anl-nx anls)) (<= (anl-xfind-steps x s anls) (+ 1 (anl-nx anls))))
  :hints (("Goal" :use anl-xfind-steps-bound :expand ((anl-xfind-steps x s anls))))
  :rule-classes :linear)

(defun anl-chain-find-steps (b s anls)
  (declare (xargs :stobjs anls :measure (nfix b) :ruler-extenders :all :verify-guards nil))
  (if (and (natp b) (< b (anl-nb anls)))
      (let ((x (anl-xfind (anl-g-bhead b anls) s anls)))
        (+ (anl-xfind-steps (anl-g-bhead b anls) s anls)
           (if (<= 0 x) 1
             (let ((p (anl-g-bpar b anls))) (if (and (natp p) (< p b)) (+ 1 (anl-chain-find-steps p s anls)) 1)))))
    1))

(defthm anl-chain-find-steps-bound
  (implies (natp (anl-nx anls))
           (<= (anl-chain-find-steps b s anls) (* (+ 1 (nfix b)) (+ 2 (anl-nx anls)))))
  :hints (("Goal" :induct (anl-chain-find-steps b s anls) :nonlinearp t)
          ("Subgoal *1/4" :use ((:instance anl-xfind-steps-nx (x (anl-g-bhead b anls))))
                          :nonlinearp t)
          ("Subgoal *1/3" :use ((:instance anl-xfind-steps-nx (x (anl-g-bhead b anls)))) :nonlinearp t)
          ("Subgoal *1/2" :use ((:instance anl-xfind-steps-nx (x (anl-g-bhead b anls)))) :nonlinearp t)
          ("Subgoal *1/1" :use ((:instance anl-xfind-steps-nx (x (anl-g-bhead b anls)))) :nonlinearp t))
  :rule-classes :linear)

(defun anl-cfind-steps (c s anls)
  (declare (xargs :stobjs anls :measure (nfix c) :verify-guards nil))
  (if (and (natp c) (< c (anl-nc anls)))
      (if (equal (anl-g-cnm c anls) s) 1
        (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (+ 1 (anl-cfind-steps j s anls)) 1)))
    1))

(defthm anl-cfind-steps-bound (<= (anl-cfind-steps c s anls) (+ 1 (nfix c))) :rule-classes :linear)

(defthm anl-cfind-steps-nc
  (implies (natp (anl-nc anls)) (<= (anl-cfind-steps c s anls) (+ 1 (anl-nc anls))))
  :hints (("Goal" :use anl-cfind-steps-bound :expand ((anl-cfind-steps c s anls))))
  :rule-classes :linear)

; the lookup: the chain, the captures, and the fn around, as anl-lookup
; walks them; a capture made is 2 steps (the slot counter, the record)
(defun anl-lookup-steps (b s anls)
  (declare (xargs :stobjs anls :measure (nfix b) :ruler-extenders :all :verify-guards nil))
  (let ((x (anl-chain-find b s anls)) (cs (anl-chain-find-steps b s anls)))
    (if (<= 0 x) cs
      (let* ((f (anl-g-bfn b anls)) (o (anl-g-fout f anls)))
        (if (and (natp b) (natp o) (< o b) (< (anl-g-bfn o anls) f))
            (let ((c (anl-cfind (anl-g-fcap f anls) s anls)))
              (+ cs (anl-cfind-steps (anl-g-fcap f anls) s anls)
                 (if (<= 0 c) 0 (+ 2 (anl-lookup-steps o s anls)))))
          cs)))))

(defthm anl-mul-mono
  (implies (and (rationalp x1) (rationalp x2) (rationalp y1) (rationalp y2)
                (<= 0 x1) (<= x1 x2) (<= 0 y1) (<= y1 y2))
           (<= (* x1 y1) (* x2 y2)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

; the bound at an outer block is below the bound at b with one fn less
(defthm anl-lookup-bound-mono
  (implies (and (natp o) (natp b) (< o b) (natp nx) (natp nc) (natp e))
           (<= (* (+ 1 o) (+ (* (+ 1 o) (+ 2 nx)) nc e)) (* b (+ (* (+ 1 b) (+ 2 nx)) nc e))))
  :hints (("Goal" :use ((:instance anl-mul-mono (x1 (+ 1 o)) (x2 b)
                                    (y1 (+ (* (+ 1 o) (+ 2 nx)) nc e)) (y2 (+ (* (+ 1 b) (+ 2 nx)) nc e)))
                         (:instance anl-mul-mono (x1 (+ 1 o)) (x2 (+ 1 b)) (y1 (+ 2 nx)) (y2 (+ 2 nx))))))
  :rule-classes nil)

(defthm anl-lookup-steps-bound
  (implies (and (natp (anl-nx anls)) (natp (anl-nc anls)))
           (<= (anl-lookup-steps b s anls)
               (* (+ 1 (nfix b)) (+ (* (+ 1 (nfix b)) (+ 2 (anl-nx anls))) (anl-nc anls) 4))))
  :hints (("Goal" :induct (anl-lookup-steps b s anls))
          ("Subgoal *1/3" :use ((:instance anl-chain-find-steps-bound)
                                (:instance anl-cfind-steps-nc (c (anl-g-fcap (anl-g-bfn b anls) anls)))
                                (:instance anl-lookup-bound-mono (o (anl-g-fout (anl-g-bfn b anls) anls))
                                           (nx (anl-nx anls)) (nc (anl-nc anls)) (e 4)))
                          :nonlinearp t))
  :rule-classes :linear)

; ---- THE CHECKS -----------------------------------------------------------------------------

; the walk's steps hang on the elements and the state alone
(defun anl-pw-steps (pv i n st)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (let ((p (frm-nth pv i)))
        (cond ((not (equal (frm-kind p) 2)) 1)
              ((equal (frm-qual p) 1) 1)
              ((equal (frm-amp p) 1) (if (equal st 0) (+ 1 (anl-pw-steps pv (+ 1 i) n 1)) 1))
              ((equal st 0) (+ 1 (anl-pw-steps pv (+ 1 i) n 0)))
              ((equal st 1) (+ 1 (anl-pw-steps pv (+ 1 i) n 2)))
              (t 1)))
    1))

(defthm anl-pw-steps-bound
  (<= (anl-pw-steps pv i n st) (+ 1 (nfix (- (nfix n) (nfix i)))))
  :rule-classes :linear)

(defun anl-odd-steps (n) (if (zp n) 1 (if (equal n 1) 1 (+ 1 (anl-odd-steps (- n 2))))))

(defthm anl-odd-steps-bound (<= (anl-odd-steps n) (+ 1 (/ (nfix n) 2))) :rule-classes :linear)

(defun anl-fixed-steps (a anls)
  (declare (xargs :stobjs anls :measure (nfix a) :verify-guards nil))
  (if (and (natp a) (< a (anl-na anls)))
      (let ((j (anl-g-anext a anls))) (if (and (natp j) (< j a)) (+ 1 (anl-fixed-steps j anls)) 1))
    1))

(defthm anl-has-fixed-steps-bound (<= (anl-fixed-steps a anls) (+ 1 (nfix a))) :rule-classes :linear)

; ---- WHAT IS READ BACK ----------------------------------------------------------------------

(defun anl-caps-steps (c anls)
  (declare (xargs :stobjs anls :measure (nfix c) :verify-guards nil))
  (if (and (natp c) (< c (anl-nc anls)))
      (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (+ 1 (anl-caps-steps j anls)) 1))
    1))

(defthm anl-caps-steps-bound (<= (anl-caps-steps c anls) (+ 1 (nfix c))) :rule-classes :linear)

(defthm anl-caps-steps-nc
  (implies (natp (anl-nc anls)) (<= (anl-caps-steps c anls) (+ 1 (anl-nc anls))))
  :hints (("Goal" :use anl-caps-steps-bound :expand ((anl-caps-steps c anls))))
  :rule-classes :linear)

(defun anl-names-steps (n anls)
  (declare (xargs :stobjs anls :measure (nfix n) :verify-guards nil))
  (if (and (natp n) (< n (anl-nn anls)))
      (let ((j (anl-g-nnext n anls))) (if (and (natp j) (< j n)) (+ 1 (anl-names-steps j anls)) 1))
    1))

(defthm anl-names-steps-bound (<= (anl-names-steps n anls) (+ 1 (nfix n))) :rule-classes :linear)

(defun anl-ev-find-steps (i anls)
  (declare (xargs :stobjs anls :measure (nfix (- (nfix (anl-nev anls)) (nfix i))) :verify-guards nil))
  (if (and (natp i) (natp (anl-nev anls)) (< i (anl-nev anls))) (+ 1 (anl-ev-find-steps (+ 1 i) anls)) 1))

(defthm anl-ev-find-steps-bound
  (<= (anl-ev-find-steps i anls) (+ 1 (nfix (- (nfix (anl-nev anls)) (nfix i)))))
  :rule-classes :linear)

; the env's walk, in records: the chain's blocks and their bindings, each
; fn's captures, the fns around
(defun anl-env-walk-steps (b anls)
  (declare (xargs :stobjs anls :measure (nfix b) :ruler-extenders :all :verify-guards nil))
  (let* ((f (anl-g-bfn b anls)) (o (anl-g-fout f anls))
         (w (+ (anl-chain-find-steps b -2 anls) (anl-caps-steps (anl-g-fcap f anls) anls))))
    (if (and (natp b) (natp o) (< o b) (< (anl-g-bfn o anls) f)) (+ w (anl-env-walk-steps o anls)) w)))

(defthm anl-le-times
  (implies (and (natp k) (rationalp m) (<= 0 m)) (<= m (* (+ 1 k) m)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

; a block's own walk, without the fns around
(defthm anl-env-walk-one
  (implies (and (natp (anl-nx anls)) (natp (anl-nc anls)))
           (<= (+ (anl-chain-find-steps b -2 anls) (anl-caps-steps (anl-g-fcap (anl-g-bfn b anls) anls) anls))
               (+ (* (+ 1 (nfix b)) (+ 2 (anl-nx anls))) (anl-nc anls) 2)))
  :hints (("Goal" :use ((:instance anl-chain-find-steps-bound (s -2))
                         (:instance anl-caps-steps-nc (c (anl-g-fcap (anl-g-bfn b anls) anls))))))
  :rule-classes nil)

(defthm anl-env-walk-steps-bound
  (implies (and (natp (anl-nx anls)) (natp (anl-nc anls)))
           (<= (anl-env-walk-steps b anls)
               (* (+ 1 (nfix b)) (+ (* (+ 1 (nfix b)) (+ 2 (anl-nx anls))) (anl-nc anls) 2))))
  :hints (("Goal" :induct (anl-env-walk-steps b anls) :in-theory (disable anl-chain-find-steps anl-caps-steps))
          ("Subgoal *1/1" :use ((:instance anl-env-walk-one)
                                (:instance anl-lookup-bound-mono (o (anl-g-fout (anl-g-bfn b anls) anls))
                                           (nx (anl-nx anls)) (nc (anl-nc anls)) (e 2))))
          ("Subgoal *1/2" :use ((:instance anl-env-walk-one)
                                (:instance anl-le-times (k (nfix b))
                                           (m (+ (* (+ 1 (nfix b)) (+ 2 (anl-nx anls))) (anl-nc anls) 2))))))
  :rule-classes :linear)

; EXEC.LISP'S TREE READ AS ANPASS READS IT (exec-PLAN milestone 4, second
; part): the analyzer's one tree, exec.inc reading it through ex-kind,
; ex-kids, ex-c, ex-i2, ex-mark and anpass through ast-kind, ast-kid,
; ast-alt, ast-i2, ast-cap. ex-ast is that second reading of an exec.lisp
; node: its kind, i2 and children; a fn's capture pairs' outer slots its
; caps; a try's catch bodies or a case's thens its alternatives; and a
; recur's target, rfn, which exec.inc does not read (the node's slot 8:
; nonzero the fn, as the analyzer records it).
;
;   ex-shp       the tree in the shapes exec.inc and anpass both take (a
;                let's or loop's children its inits and its body, a throw's
;                one child, an if's at most three) and the sizes anpass's
;                reads keep exact
;   ex-rds-ast   exec-clr's ex-rds is anpass's rds of the node
;
; exec-clrlv.lisp shows exec-clr's ex-lv is anpass's sp-out of the node.

(in-package "ACL2")

(include-book "exec-clr")

; ---- THE MAP ------------------------------------------------------------------------------------

; fl 0 a node, 1 a list of them, 2 a try's catch clauses (their bodies),
; 3 a case's entries (their thens)
(defun ex-astf (fl x)
  (declare (xargs :measure (acl2-count x)))
  (cond ((equal fl 0)
         (if (atom x)
             nil
           (let ((k (nth 0 x)))
             (list :ast nil k (nfix (nth 1 x)) (ex-astf 1 (nth 2 x)) nil
                   (if (equal k 14) (ex-outers (nth 2 (nth 3 x))) nil)
                   (cond ((equal k 18) (ex-astf 2 (nth 3 x))) ((equal k 19) (ex-astf 3 (nth 3 x))) (t nil))
                   (if (nth 8 x) 1 0)))))
        ((atom x) nil)
        ((equal fl 1) (cons (ex-astf 0 (car x)) (ex-astf 1 (cdr x))))
        ((equal fl 2) (cons (ex-astf 0 (nth 2 (car x))) (ex-astf 2 (cdr x))))
        (t (cons (ex-astf 0 (nth 1 (car x))) (ex-astf 3 (cdr x))))))

(defmacro ex-ast (e) `(ex-astf 0 ,e))

(defun ex-slp (l) (if (atom l) t (and (natp (car l)) (< (car l) *ex40*) (ex-slp (cdr l)))))

(defconst *ex-core* '(1 2 3 4 5 6 7 8 9 11 12 14 16 17 18 19 22 23))

(defun ex-shp (flg e i)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        t
      (and (natp k) (< 0 k) (< k 64) (< nk *ex40*) (< n2 *ex40*) (< (len (ex-c e)) *ex40*)
           (case flg
             (:do (cond ((zp nk) t)
                        ((< i (- nk 1)) (and (ex-shp :m (ex-kid-of e i) 0) (ex-shp :do e (1+ i))))
                        ((equal i (- nk 1)) (ex-shp :m (ex-kid-of e i) 0))
                        (t nil)))
             (:let (cond ((not (and (or (equal k 11) (equal k 12)) (equal nk (1+ n2)))) nil)
                         ((< i n2) (and (ex-shp :m (ex-kid-of e i) 0) (ex-shp :let e (1+ i))))
                         ((equal i n2) (ex-shp :m (ex-kid-of e n2) 0))
                         (t nil)))
             ((:rec :call :coll) (if (< i nk) (and (ex-shp :m (ex-kid-of e i) 0) (ex-shp flg e (1+ i))) t))
             (:cs (if (< i (len (ex-c e))) (and (equal k 18)  (ex-shp :m (ex-cbody e i) 0) (ex-shp :cs e (1+ i))) t))
             (:ct (if (< i (len (ex-c e))) (and (equal k 19)  (ex-shp :m (ex-cthen e i) 0) (ex-shp :ct e (1+ i))) t))
             (:fin (ex-shp :m (ex-kid-of e 1) 0))
             (otherwise
              (cond ((member k '(1 2 3)) (equal nk 0))
                    ((equal k 14) (and (equal nk 0) (ex-slp (ex-outers (nth 2 (ex-c e)))) (< (len (ex-outers (nth 2 (ex-c e)))) *ex40*)))
                    ((equal k 4) (and (<= nk 3) (ex-shp :m (ex-kid-of e 0) 0) (ex-shp :m (ex-kid-of e 1) 0) (ex-shp :m (ex-kid-of e 2) 0)))
                    ((equal k 5) (ex-shp :do e 0))
                    ((or (equal k 11) (equal k 12)) (and (equal nk (1+ n2)) (ex-shp :let e 0)))
                    ((equal k 16) (ex-shp :rec e 0))
                    ((equal k 17) (and (equal nk 1) (ex-shp :m (ex-kid-of e 0) 0)))
                    ((equal k 18) (and (<= nk 2) (ex-shp :m (ex-kid-of e 0) 0) (ex-shp :cs e 0) (ex-shp :fin e 0)))
                    ((member k '(7 8 9 22 23)) (ex-shp :coll e 0))
                    ((equal k 19) (and (equal nk 2) (ex-shp :m (ex-kid-of e 0) 0) (ex-shp :m (ex-kid-of e 1) 0) (ex-shp :ct e 0)))
                    ((equal k 6) (ex-shp :call e 0))
                    (t nil))))))))

; ---- ANPASS'S READS OF IT -----------------------------------------------------------------------

(defthm ex-len-astf (implies (member fl '(1 2 3)) (equal (len (ex-astf fl l)) (len l))))
(defthm ex-nth-astf-1 (implies (natp j) (equal (anp-nth j (ex-astf 1 l)) (ex-astf 0 (nth j l))))
  :hints (("Goal" :induct (nth j l) :expand ((ex-astf 1 l)) :in-theory (enable anp-nth))))
(defthm ex-nth-astf-2 (implies (natp j) (equal (anp-nth j (ex-astf 2 l)) (ex-astf 0 (nth 2 (nth j l)))))
  :hints (("Goal" :induct (nth j l) :expand ((ex-astf 2 l)) :in-theory (enable anp-nth))))
(defthm ex-nth-astf-3 (implies (natp j) (equal (anp-nth j (ex-astf 3 l)) (ex-astf 0 (nth 1 (nth j l)))))
  :hints (("Goal" :induct (nth j l) :expand ((ex-astf 3 l)) :in-theory (enable anp-nth))))
(defthm ex-anp-len (equal (anp-len l) (len l)) :hints (("Goal" :in-theory (enable anp-len))))
(defthm ex-ast-nil (equal (ex-astf 0 nil) nil))

(defthm ex-ast-open
  (implies (consp e)
           (equal (ex-astf 0 e)
                  (list :ast nil (ex-kind e) (ex-i2 e) (ex-astf 1 (ex-kids e)) nil
                        (if (equal (ex-kind e) 14) (ex-outers (nth 2 (ex-c e))) nil)
                        (cond ((equal (ex-kind e) 18) (ex-astf 2 (ex-c e))) ((equal (ex-kind e) 19) (ex-astf 3 (ex-c e))) (t nil))
                        (if (nth 8 e) 1 0))))
  :hints (("Goal" :in-theory (enable ex-kind ex-i2 ex-kids ex-c))))
(in-theory (disable ex-astf))

(defmacro ex-nodep (e) `(and (consp ,e) (natp (ex-kind ,e)) (< 0 (ex-kind ,e)) (< (ex-kind ,e) 64)
                             (< (ex-nk ,e) *ex40*) (< (ex-i2 ,e) *ex40*) (< (len (ex-c ,e)) *ex40*)))

(defthm ex-ast-reads
  (implies (ex-nodep e)
           (and (equal (ast-kind (ex-ast e)) (ex-kind e))
                (equal (ast-i2 (ex-ast e)) (ex-i2 e))
                (equal (ast-nkids (ex-ast e)) (ex-nk e))
                (equal (ast-nalts (ex-ast e)) (if (or (equal (ex-kind e) 18) (equal (ex-kind e) 19)) (len (ex-c e)) 0))
                (equal (ast-ncaps (ex-ast e)) (if (equal (ex-kind e) 14) (anp-sat (len (ex-outers (nth 2 (ex-c e))))) 0))))
  :hints (("Goal" :in-theory (enable ast-kind ast-i2 ast-nkids ast-nalts ast-ncaps ast-p anp-nth anp-sat anp-fix ex-nk))))

(defthm ex-nth-past (implies (and (natp j) (<= (len l) j)) (equal (nth j l) nil)))

(defthm ex-ast-kid
  (implies (and (ex-nodep e) (natp j)) (equal (ast-kid (ex-ast e) j) (ex-ast (ex-kid-of e j))))
  :hints (("Goal" :in-theory (enable ast-kid ast-nkids ast-p anp-nth anp-sat ex-nk))))

(defthm ex-ast-alt
  (implies (and (ex-nodep e) (natp j))
           (equal (ast-alt (ex-ast e) j)
                  (cond ((equal (ex-kind e) 18) (ex-ast (ex-cbody e j))) ((equal (ex-kind e) 19) (ex-ast (ex-cthen e j))) (t nil))))
  :hints (("Goal" :in-theory (enable ast-alt ast-nalts ast-p anp-nth anp-sat ex-cbody ex-cthen))))

(defthm ex-true-outers (true-listp (ex-outers x)))
(defthm ex-nthcdr-past (implies (and (true-listp l) (natp i) (<= (len l) i)) (equal (nthcdr i l) nil)))
(defthm ex-slp-nth (implies (and (ex-slp l) (natp j) (< j (len l))) (and (natp (nth j l)) (< (nth j l) *ex40*))))
(defthm ex-nthcdr-cons (implies (and (natp i) (< i (len l))) (equal (nthcdr i l) (cons (nth i l) (nthcdr (1+ i) l))))
  :rule-classes nil)
(defthm ex-anp-nth (implies (natp j) (equal (anp-nth j l) (nth j l))) :hints (("Goal" :in-theory (enable anp-nth))))

(defthm ex-ast-cap
  (implies (and (ex-nodep e) (equal (ex-kind e) 14) (ex-slp (ex-outers (nth 2 (ex-c e)))) (natp j)
                (< j (len (ex-outers (nth 2 (ex-c e))))) (< (len (ex-outers (nth 2 (ex-c e)))) *ex40*))
           (equal (ast-cap (ex-ast e) j) (nth j (ex-outers (nth 2 (ex-c e))))))
  :hints (("Goal" :in-theory (enable ast-cap ast-ncaps ast-p anp-sat anp-fix))))

(defthm ex-cap-list
  (implies (and (ex-nodep e) (equal (ex-kind e) 14) (< (len (ex-outers (nth 2 (ex-c e)))) *ex40*)
                (ex-slp (ex-outers (nth 2 (ex-c e)))) (natp i))
           (equal (cap-list (ex-ast e) i (len (ex-outers (nth 2 (ex-c e))))) (nthcdr i (ex-outers (nth 2 (ex-c e))))))
  :hints (("Goal" :induct (cap-list (ex-ast e) i (len (ex-outers (nth 2 (ex-c e))))) :in-theory (disable ex-ast-open))
          ("Subgoal *1/1" :use ((:instance ex-nthcdr-cons (l (ex-outers (nth 2 (ex-c e)))))))))

(in-theory (disable ex-ast-open))
(defthm ex-kid-atom (implies (not (consp e)) (equal (ex-kid-of e j) nil)) :hints (("Goal" :in-theory (enable ex-kids))))
(defthm ex-kid-past (implies (and (natp j) (<= (ex-nk e) j)) (equal (ex-kid-of e j) nil)) :hints (("Goal" :in-theory (enable ex-nk))))

; ---- THE BRIDGE -----------------------------------------------------------------------------------

(defthm ex-ast-atom (implies (atom e) (equal (ex-astf 0 e) nil)) :hints (("Goal" :in-theory (enable ex-astf))))
(defthm ex-true-rds (true-listp (rds fl x j m)))
(defthm ex-setl-append (equal (ex-setl (append a b) L n) (ex-setl b (ex-setl a L n) n)))
(defthm ex-sp-caps-setl (equal (sp-caps x i k L n) (ex-setl (cap-list x i k) L n)))
(defthm ex-sp-rd-setl (equal (sp-rd fl x j m L n) (ex-setl (rds fl x j m) L n))
  :hints (("Goal" :induct (sp-rd fl x j m L n) :in-theory (disable rds-0-open) :expand ((rds fl x j m)))))

; the piece of anpass's tree a place of exec.lisp's is
(defun ex-rdp (flg e i)
  (case flg
    (:m (rds 0 (ex-ast e) 0 0))
    ((:do :let :rec :call :coll) (rds 1 (ex-ast e) i (ex-nk e)))
    ((:cs :ct) (rds 3 (ex-ast e) i (len (ex-c e))))
    (:fin (rds 0 (ex-ast (ex-kid-of e 1)) 0 0))
    (otherwise nil)))

(defthm ex-rds-ast
  (implies (and (ex-shp flg e i) (member flg '(:m :do :let :rec :call :coll :cs :ct :fin)) (natp i))
           (equal (ex-rds flg e i) (ex-rdp flg e i)))
  :hints (("Goal" :induct (ex-shp flg e i) :in-theory (disable ex-kid-of rds-0-open)
           :expand ((rds 0 (ex-astf 0 e) 0 0) (ex-rds :m e i) (ex-shp :m e i)))))


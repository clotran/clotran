; EXEC-CLR'S LIVE SETS ARE ANPASS'S (exec-PLAN milestone 4, second part):
; exec-clr's ex-lv, written on exec.lisp's tree, is sp-out -- the live sets
; anpass's liveness pass computes (anpass-proof's anp-live-spec) -- of the
; node as exec-clrmap's ex-ast reads it. So ex-mkok's condition on a marked
; read, its slot not live after it, is the decision sp-mk makes there:
; anp-clears-spec's marks are the reads ex-mkok allows.
;
;   ex-lvp      the piece of anpass's walk a place of exec.lisp's is: :m the
;               node's sp-out; :do :rec :call :coll its children from i
;               (sp-out 1); a let's children from i, a loop's inits from i
;               onto its body's sp-out from the body's reads (sp-rd); :cs
;               :ct its alternatives from i (sp-out 2); :fin the finally's
;   ex-lv-ast   ex-lv is ex-lvp on a tree of ex-shp's shapes
;   ex-mk-local sp-mk marks a local exactly when ex-mkok lets it be marked
;
; sp-out stays disabled throughout: its node case is opened once per kind
; (ex-spo-*), the sequences only by sp-out-seq-front, -seq-done, -2-open and
; -2-done (one induction with sp-out open ran past 400 s).

(in-package "ACL2")

(include-book "exec-clrmap")

(in-theory (disable sp-out sp-out-seq-open))

(defthm ex-spo-nil (equal (sp-out 0 nil j m A L n) L)
  :hints (("Goal" :expand ((sp-out 0 nil j m A L n)) :in-theory (enable ast-kind ast-p))))
(defthm ex-spo-1-nil (equal (sp-out 1 nil j m A L n) L)
  :hints (("Goal" :in-theory (enable ast-kind ast-p))))
(defthm ex-spo-2-nil (equal (sp-out 2 nil j m A L n) A)
  :hints (("Goal" :in-theory (enable ast-kind ast-p))))

; ---- THE NODE, ONE KIND AT A TIME ----------------------------------------------------------------

; a deftype's methods, its alternatives, are its children (ex-ch-deftype): anpass's walk of them is a collection's
(defun ex-mind (x j m A L n)
  (declare (ignore A) (irrelevant x L n) (xargs :measure (nfix (- (ifix m) (nfix j)))))
  (if (and (natp j) (integerp m) (< j m)) (ex-mind x j (1- m) nil (sp-out 0 (anp-ch 1 x (1- m)) 0 0 nil L n) n) t))
(defthm ex-spo-deftype
  (implies (and (ex-nodep e) (equal (ex-kind e) 20)) (equal (sp-out 3 (ex-ast e) j m A L n) (sp-out 1 (ex-ast e) j m nil L n)))
  :hints (("Goal" :induct (ex-mind (ex-ast e) j m A L n) :in-theory (e/d (sp-out-seq-open) (sp-out-seq-front ex-ast-open)))))

(defthm ex-spo-seq
  (implies (and (ex-nodep e) (member (ex-kind e) '(1 3 5 6 7 8 9 11 16 17 22 23 10 20 24 21)))
           (equal (sp-out 0 (ex-ast e) j m A L n) (sp-out 1 (ex-ast e) 0 (ex-nk e) nil L n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)))))

(defthm ex-spo-local
  (implies (and (ex-nodep e) (equal (ex-kind e) 2))
           (equal (sp-out 0 (ex-ast e) j m A L n) (sp-set (ex-i2 e) L n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)))))

(defthm ex-spo-fn
  (implies (and (ex-nodep e) (member-equal (ex-kind e) '(14 15)) (ex-slp (ex-outers (nth 2 (ex-c e))))
                (< (len (ex-outers (nth 2 (ex-c e)))) *ex40*))
           (equal (sp-out 0 (ex-ast e) j m A L n) (ex-setl (ex-outers (nth 2 (ex-c e))) L n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)) :in-theory (enable anp-sat)
           :use ((:instance ex-cap-list (i 0))))))

(defthm ex-spo-if
  (implies (and (ex-nodep e) (equal (ex-kind e) 4))
           (equal (sp-out 0 (ex-ast e) j m A L n)
                  (sp-out 0 (ex-ast (ex-kid-of e 0)) 0 0 nil
                          (sp-or (sp-out 0 (ex-ast (ex-kid-of e 1)) 0 0 nil L n) (sp-out 0 (ex-ast (ex-kid-of e 2)) 0 0 nil L n)) n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)))))

(defthm ex-spo-loop
  (implies (and (ex-nodep e) (equal (ex-kind e) 12) (equal (ex-nk e) (1+ (ex-i2 e))))
           (equal (sp-out 0 (ex-ast e) j m A L n)
                  (sp-out 1 (ex-ast e) 0 (ex-i2 e) nil
                          (sp-out 0 (ex-ast (ex-kid-of e (ex-i2 e))) 0 0 nil (sp-rd 0 (ex-ast (ex-kid-of e (ex-i2 e))) 0 0 L n) n) n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)) :in-theory (enable anp-nn))))

(defthm ex-spo-try
  (implies (and (ex-nodep e) (equal (ex-kind e) 18))
           (equal (sp-out 0 (ex-ast e) j m A L n)
                  (sp-out 0 (ex-ast (ex-kid-of e 0)) 0 0 nil
                          (sp-out 2 (ex-ast e) 0 (len (ex-c e)) (sp-out 0 (ex-ast (ex-kid-of e 1)) 0 0 nil L n)
                                  (sp-out 0 (ex-ast (ex-kid-of e 1)) 0 0 nil L n) n) n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)))))

(defthm ex-spo-case
  (implies (and (ex-nodep e) (equal (ex-kind e) 19))
           (equal (sp-out 0 (ex-ast e) j m A L n)
                  (sp-out 0 (ex-ast (ex-kid-of e 0)) 0 0 nil
                          (sp-or (sp-out 2 (ex-ast e) 0 (len (ex-c e)) L L n) (sp-out 0 (ex-ast (ex-kid-of e 1)) 0 0 nil L n)) n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)))))

; the sequences, read through ex-ast
(defthm ex-spo-front
  (implies (and (ex-nodep e) (natp i) (integerp m) (< i m))
           (equal (sp-out 1 (ex-ast e) i m A L n)
                  (sp-out 0 (ex-ast (ex-kid-of e i)) 0 0 nil (sp-out 1 (ex-ast e) (1+ i) m nil L n) n)))
  :hints (("Goal" :in-theory (disable ex-ast-kid) :use ((:instance ex-ast-kid (j i))))))
(defthm ex-spo-done
  (implies (and (natp i) (integerp m) (not (< i m))) (equal (sp-out 1 x i m A L n) L)))

(defthm ex-spo-cs
  (implies (and (ex-nodep e) (equal (ex-kind e) 18) (natp i) (< i (len (ex-c e))))
           (equal (sp-out 2 (ex-ast e) i (len (ex-c e)) A L n)
                  (sp-out 2 (ex-ast e) (1+ i) (len (ex-c e)) (sp-or (sp-out 0 (ex-ast (ex-cbody e i)) 0 0 nil L n) A) L n)))
  :hints (("Goal" :in-theory (enable sp-out-2-open))))
(defthm ex-spo-ct
  (implies (and (ex-nodep e) (equal (ex-kind e) 19) (natp i) (< i (len (ex-c e))))
           (equal (sp-out 2 (ex-ast e) i (len (ex-c e)) A L n)
                  (sp-out 2 (ex-ast e) (1+ i) (len (ex-c e)) (sp-or (sp-out 0 (ex-ast (ex-cthen e i)) 0 0 nil L n) A) L n)))
  :hints (("Goal" :in-theory (enable sp-out-2-open))))
(defthm ex-spo-2-done
  (implies (and (natp i) (not (< i m))) (equal (sp-out 2 x i m A L n) A)))

; a letfn: anpass's walk reads its fns' captures again after its body
; (sp-fncaps, refresh_captures' second pass), sets its fns' sp-out has set
; already -- so it is a let's walk of its fns and body
(defthm ex-upd-comm
  (implies (and (natp a) (natp b) (not (equal a b)))
           (equal (update-nth a v (update-nth b w L)) (update-nth b w (update-nth a v L)))))
(defthm ex-upd-idem (equal (update-nth a v (update-nth a w L)) (update-nth a v L)))
(defthm ex-set-comm (equal (sp-set a (sp-set b L n) n) (sp-set b (sp-set a L n) n)) :hints (("Goal" :cases ((equal a b)))))
(defthm ex-set-idem (equal (sp-set a (sp-set a L n) n) (sp-set a L n)))
(in-theory (disable sp-set))
(defthm ex-setl-set (equal (ex-setl X (sp-set a L n) n) (sp-set a (ex-setl X L n) n)))
(defthm ex-setl-comm (equal (ex-setl X (ex-setl Y L n) n) (ex-setl Y (ex-setl X L n) n))
  :hints (("Goal" :induct (ex-setl Y L n))))
(defthm ex-setl-idem (equal (ex-setl X (ex-setl X L n) n) (ex-setl X L n)) :hints (("Goal" :induct (len X))))

; the fns' outer slots j .. n-1, in turn
(defun ex-lfoall (e j)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e)) (append (ex-lfos e (nfix j)) (ex-lfoall e (1+ (nfix j)))) nil))
(defun ex-lfoind (e j L n)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (and (natp j) (< j (ex-i2 e))) (ex-lfoind e (1+ j) (ex-setl (ex-lfos e j) L n) n) (list L n)))

; a let's body, past its inits, is in ex-shp's shapes
(defthm ex-shp-let-body
  (implies (and (consp e) (ex-shp :let e j) (natp j) (<= j (ex-i2 e)) (equal n (ex-i2 e))) (ex-shp :m (ex-kid-of e n) 0))
  :hints (("Goal" :induct (ex-lfoall e j) :in-theory (disable ex-kid-of) :expand ((ex-shp :let e j)))))

(defthm ex-spo1-letfn
  (implies (and (ex-nodep e) (equal (ex-kind e) 13) (equal (ex-nk e) (1+ (ex-i2 e))) (ex-shp :let e j) (ex-lffns e j) (natp j))
           (equal (sp-out 1 (ex-ast e) j (ex-i2 e) nil L n) (ex-setl (ex-lfoall e j) L n)))
  :hints (("Goal" :induct (ex-lfoall e j) :in-theory (disable ex-ast-open)
           :expand ((ex-shp :let e j) (ex-shp :m (ex-kid-of e j) 0) (ex-lffns e j) (ex-lfoall e j)))))

(defthm ex-fncaps-letfn
  (implies (and (ex-nodep e) (equal (ex-kind e) 13) (equal (ex-nk e) (1+ (ex-i2 e))) (ex-shp :let e j) (ex-lffns e j) (natp j))
           (equal (sp-fncaps (ex-ast e) j (ex-i2 e) L n) (ex-setl (ex-lfoall e j) L n)))
  :hints (("Goal" :induct (ex-lfoind e j L n) :in-theory (e/d (anp-sat) (ex-ast-open))
           :expand ((ex-shp :let e j) (ex-shp :m (ex-kid-of e j) 0) (ex-lffns e j) (ex-lfoall e j)
                    (sp-fncaps (ex-ast e) j (ex-i2 e) L n)))
          ("Subgoal *1/1" :use ((:instance ex-cap-list (e (ex-kid-of e j)) (i 0))))))

(defthm ex-spo-letfn
  (implies (and (ex-nodep e) (equal (ex-kind e) 13) (equal (ex-nk e) (1+ (ex-i2 e))) (ex-shp :let e 0) (ex-lffns e 0))
           (equal (sp-out 0 (ex-ast e) j m A L n) (sp-out 1 (ex-ast e) 0 (ex-nk e) nil L n)))
  :hints (("Goal" :expand ((sp-out 0 (ex-ast e) j m A L n)) :in-theory (e/d (anp-nn) (ex-ast-open ex-shp ex-lffns ex-lfoall sp-fncaps))
           :use ((:instance sp-out-seq-open (fl 1) (x (ex-ast e)) (j 0) (m (ex-nk e)) (A nil))))))

; ---- THE MAP ----------------------------------------------------------------------------------------

(defun ex-lvp (flg e i A L n)
  (let ((x (ex-ast e)) (i (nfix i)) (b (ex-kid-of e (ex-i2 e))))
    (case flg
      (:m (sp-out 0 x 0 0 nil L n))
      ((:do :rec :call :coll) (sp-out 1 x i (ex-nk e) nil L n))
      (:let (if (equal (ex-kind e) 12)
                (sp-out 1 x i (ex-i2 e) nil (sp-out 0 (ex-ast b) 0 0 nil (sp-rd 0 (ex-ast b) 0 0 L n) n) n)
              (sp-out 1 x i (ex-nk e) nil L n)))
      ((:cs :ct) (sp-out 2 x i (len (ex-c e)) A L n))
      (:fin (sp-out 0 (ex-ast (ex-kid-of e 1)) 0 0 nil L n))
      (otherwise L))))

; ex-lv's walk, but a call's node as its children from 0 (as ex-shp walks it)
(defun ex-lvind (flg e i A L n)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        (list A L)
      (case flg
        (:do (cond ((zp nk) t)
                   ((< i (- nk 1)) (list (ex-lvind :m (ex-kid-of e i) 0 nil (ex-lv :do e (1+ i) nil L n) n) (ex-lvind :do e (1+ i) nil L n)))
                   (t (ex-lvind :m (ex-kid-of e (- nk 1)) 0 nil L n))))
        (:let (cond ((< i n2) (list (ex-lvind :m (ex-kid-of e i) 0 nil (ex-lv :let e (1+ i) nil L n) n) (ex-lvind :let e (1+ i) nil L n)))
                    ((equal k 12) (ex-lvind :m (ex-kid-of e n2) 0 nil (ex-setl (ex-rds :m (ex-kid-of e n2) 0) L n) n))
                    (t (ex-lvind :m (ex-kid-of e n2) 0 nil L n))))
        ((:rec :call :coll) (if (< i nk) (list (ex-lvind :m (ex-kid-of e i) 0 nil (ex-lv flg e (1+ i) nil L n) n) (ex-lvind flg e (1+ i) nil L n)) t))
        (:cs (if (< i (len (ex-c e))) (list (ex-lvind :m (ex-cbody e i) 0 nil L n) (ex-lvind :cs e (1+ i) (sp-or (ex-lv :m (ex-cbody e i) 0 nil L n) A) L n)) t))
        (:ct (if (< i (len (ex-c e))) (list (ex-lvind :m (ex-cthen e i) 0 nil L n) (ex-lvind :ct e (1+ i) (sp-or (ex-lv :m (ex-cthen e i) 0 nil L n) A) L n)) t))
        (:fin (ex-lvind :m (ex-kid-of e 1) 0 nil L n))
        (otherwise
         (cond ((equal k 4) (list (ex-lvind :m (ex-kid-of e 0) 0 nil (sp-or (ex-lv :m (ex-kid-of e 1) 0 nil L n) (ex-lv :m (ex-kid-of e 2) 0 nil L n)) n)
                                  (ex-lvind :m (ex-kid-of e 1) 0 nil L n) (ex-lvind :m (ex-kid-of e 2) 0 nil L n)))
               ((equal k 5) (ex-lvind :do e 0 nil L n))
               ((member k '(11 12 13)) (ex-lvind :let e 0 nil L n))
               ((equal k 16) (ex-lvind :rec e 0 nil L n))
               ((equal k 17) (ex-lvind :m (ex-kid-of e 0) 0 nil L n))
               ((equal k 18) (let ((L1 (ex-lv :fin e 0 nil L n)))
                               (list (ex-lvind :fin e 0 nil L n) (ex-lvind :cs e 0 L1 L1 n)
                                     (ex-lvind :m (ex-kid-of e 0) 0 nil (ex-lv :cs e 0 L1 L1 n) n))))
               ((member k '(7 8 9 22 23 10 20 24 21)) (ex-lvind :coll e 0 nil L n))
               ((equal k 19) (list (ex-lvind :ct e 0 L L n) (ex-lvind :m (ex-kid-of e 1) 0 nil L n)
                                   (ex-lvind :m (ex-kid-of e 0) 0 nil (sp-or (ex-lv :ct e 0 L L n) (ex-lv :m (ex-kid-of e 1) 0 nil L n)) n)))
               ((equal k 6) (ex-lvind :call e 0 nil L n))
               (t t)))))))

(defthm ex-lv-atom (implies (not (consp e)) (equal (ex-lv flg e i A L n) (if (member flg '(:cs :ct)) A L))))
(defthm ex-shp-atom (implies (not (consp e)) (ex-shp flg e i)))
; a call's node is its children from 0
(defthm ex-lv-call-0
  (implies (consp e)
           (equal (ex-lv :call e 0 nil L n)
                  (if (< 0 (ex-nk e)) (ex-lv :m (ex-kid-of e 0) 0 nil (ex-lv :call e 1 nil L n) n) L)))
  :hints (("Goal" :expand ((ex-lv :call e 0 nil L n)) :in-theory (disable ex-kid-of))))
(defthm ex-lv-call-past
  (implies (and (consp e) (not (< 1 (ex-nk e)))) (equal (ex-lv :call e 1 nil L n) L))
  :hints (("Goal" :expand ((ex-lv :call e 1 nil L n)) :in-theory (disable ex-kid-of))))
(in-theory (disable ex-lv ex-shp))

(defthm ex-lv-ast
  (implies (and (ex-shp flg e i) (member flg '(:m :do :let :rec :call :coll :cs :ct :fin)) (natp i))
           (equal (ex-lv flg e i A L n) (ex-lvp flg e i A L n)))
  :hints (("Goal" :induct (ex-lvind flg e i A L n)
           :in-theory (disable ex-kid-of ex-astf ex-ast-open rds-0-open ex-rds)
           :expand ((:free (flg A L n) (ex-lv flg e i A L n)) (:free (flg) (ex-shp flg e i))))))

; ---- THE MARKS --------------------------------------------------------------------------------------

; sp-mk marks a local when its slot is not live after it: ex-mkok's condition
(defthm ex-mk-local
  (implies (and (ex-nodep e) (equal (ex-kind e) 2) (natp n))
           (iff (consp (sp-mk 0 (ex-ast e) 0 0 L n)) (and (< (ex-i2 e) n) (equal (nth (ex-i2 e) L) 0))))
  :hints (("Goal" :expand ((sp-mk 0 (ex-ast e) 0 0 L n)))))

; ANPASS'S MARKS MEET EX-VWF'S CLEARING CONDITIONS (exec-PLAN milestone 4,
; second part): model/anpass-sound.lisp's tr-sound brought over to
; exec.lisp's tree. exec-vmtr's ex-vwf asks three things of the marked reads
; (ex-mark, the slots ex-clr lists): no read of a slot an earlier part may
; have cleared, a loop body clearing nothing of the scope outside it, and a
; fn body clearing nothing of its captures or self slot unless it never
; recurs to the fn (ex-arwf). This book states the first two on exec.lisp's
; tree and proves them of marks anpass's liveness pass puts there;
; exec-clrmap.lisp and exec-clrlv.lisp show that liveness is anpass's (the
; tree read as anpass.lisp reads it), exec-clrfn.lisp proves the third and
; exec-clrvm.lisp joins them to exec-vm.
;
;   ex-rds   every slot a node reads (its locals, a fn's outer slots), as
;            ex-clr walks it
;   ex-lv    the live set before a node, L the one after: anpass's sp-out
;            on exec.lisp's tree (a loop's body with every slot it reads
;            live after it, as it runs again; a branch's sets or-ed)
;   ex-mkok  each marked read's slot is not live after it -- the decision
;            anp-clears-spec's marks are (anp-live marks a read when its
;            slot is not live after it)
;   ex-cwf   ex-vwf's clearing conditions: B the slots the parts before a
;            place may have cleared (ex-vwf blanks them from its scope), no
;            local nor fn's outer slot read of B, and a loop body that
;            clears nothing at all
;
; Theorems:
;   ex-lv-mono   a slot live after a node is live before it
;   ex-lv-rds    a slot a node reads is live before it
;   ex-mkok-clr  a slot a node may clear is not live after it
;   ex-cwf-mkok  so marks anpass's pass made meet ex-cwf: a marked read's
;                slot is not live after it, so no later part reads it
;
; Not covered, as exec-PLAN says: ex-vwf's loop asks its own slots in scope
; at its body, and a later init may clear an earlier init's slot when the
; body never reads it (anpass marks it; the loop translation's copy would
; read it). ex-cwf does not ask it.

(in-package "ACL2")

(include-book "exec-vmtr")
(include-book "anpass-runs")

; ---- THE READS AND THE LIVE SETS ON EXEC.LISP'S TREE -------------------------------------------

(defun ex-setl (ss L n) (if (atom ss) L (ex-setl (cdr ss) (sp-set (car ss) L n) n)))

(defmacro ex-cmeas ()
  '(make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i))))

(defun ex-rds (flg e i)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        nil
      (case flg
        (:do (cond ((zp nk) nil)
                   ((< i (- nk 1)) (append (ex-rds :m (ex-kid-of e i) 0) (ex-rds :do e (1+ i))))
                   (t (ex-rds :m (ex-kid-of e (- nk 1)) 0))))
        (:let (if (< i n2) (append (ex-rds :m (ex-kid-of e i) 0) (ex-rds :let e (1+ i))) (ex-rds :m (ex-kid-of e n2) 0)))
        ((:rec :call :coll) (if (< i nk) (append (ex-rds :m (ex-kid-of e i) 0) (ex-rds flg e (1+ i))) nil))
        (:cs (if (< i (len (ex-c e))) (append (ex-rds :m (ex-cbody e i) 0) (ex-rds :cs e (1+ i))) nil))
        (:ct (if (< i (len (ex-c e))) (append (ex-rds :m (ex-cthen e i) 0) (ex-rds :ct e (1+ i))) nil))
        (:fin (ex-rds :m (ex-kid-of e 1) 0))
        (otherwise
         (cond ((equal k 2) (list n2))
               ((equal k 14) (ex-outers (nth 2 (ex-c e))))
               ((equal k 4) (append (ex-rds :m (ex-kid-of e 0) 0) (ex-rds :m (ex-kid-of e 1) 0) (ex-rds :m (ex-kid-of e 2) 0)))
               ((equal k 5) (ex-rds :do e 0))
               ((or (equal k 11) (equal k 12)) (ex-rds :let e 0))
               ((equal k 16) (ex-rds :rec e 0))
               ((equal k 17) (ex-rds :m (ex-kid-of e 0) 0))
               ((equal k 18) (append (ex-rds :m (ex-kid-of e 0) 0) (ex-rds :cs e 0) (ex-rds :fin e 0)))
               ((member k '(7 8 9 22 23 10 20 24)) (ex-rds :coll e 0))
               ((equal k 19) (append (ex-rds :m (ex-kid-of e 0) 0) (ex-rds :m (ex-kid-of e 1) 0) (ex-rds :ct e 0)))
               ((equal k 6) (append (ex-rds :m (ex-kid-of e 0) 0) (ex-rds :call e 1)))
               (t nil)))))))

; the live set before the parts from i on, L the one after the node; the
; alternatives (:cs a try's catches, :ct a case's thens) each from L, or-ed
; into A, as sp-out's fl 2
(defun ex-lv (flg e i A L n)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        (if (member flg '(:cs :ct)) A L)
      (case flg
        (:do (cond ((zp nk) L)
                   ((< i (- nk 1)) (ex-lv :m (ex-kid-of e i) 0 nil (ex-lv :do e (1+ i) nil L n) n))
                   (t (ex-lv :m (ex-kid-of e (- nk 1)) 0 nil L n))))
        (:let (cond ((< i n2) (ex-lv :m (ex-kid-of e i) 0 nil (ex-lv :let e (1+ i) nil L n) n))
                    ((equal k 12) (ex-lv :m (ex-kid-of e n2) 0 nil (ex-setl (ex-rds :m (ex-kid-of e n2) 0) L n) n))
                    (t (ex-lv :m (ex-kid-of e n2) 0 nil L n))))
        ((:rec :call :coll) (if (< i nk) (ex-lv :m (ex-kid-of e i) 0 nil (ex-lv flg e (1+ i) nil L n) n) L))
        (:cs (if (< i (len (ex-c e))) (ex-lv :cs e (1+ i) (sp-or (ex-lv :m (ex-cbody e i) 0 nil L n) A) L n) A))
        (:ct (if (< i (len (ex-c e))) (ex-lv :ct e (1+ i) (sp-or (ex-lv :m (ex-cthen e i) 0 nil L n) A) L n) A))
        (:fin (ex-lv :m (ex-kid-of e 1) 0 nil L n))
        (otherwise
         (cond ((equal k 2) (sp-set n2 L n))
               ((equal k 14) (ex-setl (ex-outers (nth 2 (ex-c e))) L n))
               ((equal k 4) (ex-lv :m (ex-kid-of e 0) 0 nil
                                   (sp-or (ex-lv :m (ex-kid-of e 1) 0 nil L n) (ex-lv :m (ex-kid-of e 2) 0 nil L n)) n))
               ((equal k 5) (ex-lv :do e 0 nil L n))
               ((or (equal k 11) (equal k 12)) (ex-lv :let e 0 nil L n))
               ((equal k 16) (ex-lv :rec e 0 nil L n))
               ((equal k 17) (ex-lv :m (ex-kid-of e 0) 0 nil L n))
               ((equal k 18) (let ((L1 (ex-lv :fin e 0 nil L n)))
                               (ex-lv :m (ex-kid-of e 0) 0 nil (ex-lv :cs e 0 L1 L1 n) n)))
               ((member k '(7 8 9 22 23 10 20 24)) (ex-lv :coll e 0 nil L n))
               ((equal k 19) (ex-lv :m (ex-kid-of e 0) 0 nil
                                    (sp-or (ex-lv :ct e 0 L L n) (ex-lv :m (ex-kid-of e 1) 0 nil L n)) n))
               ((equal k 6) (ex-lv :m (ex-kid-of e 0) 0 nil (ex-lv :call e 1 nil L n) n))
               (t L)))))))

; each marked read's slot not live after it, L the live set after the node
(defun ex-mkok (flg e i L n)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        t
      (case flg
        (:do (cond ((zp nk) t)
                   ((< i (- nk 1)) (and (ex-mkok :m (ex-kid-of e i) 0 (ex-lv :do e (1+ i) nil L n) n) (ex-mkok :do e (1+ i) L n)))
                   (t (ex-mkok :m (ex-kid-of e (- nk 1)) 0 L n))))
        (:let (cond ((< i n2) (and (ex-mkok :m (ex-kid-of e i) 0 (ex-lv :let e (1+ i) nil L n) n) (ex-mkok :let e (1+ i) L n)))
                    ((equal k 12) (ex-mkok :m (ex-kid-of e n2) 0 (ex-setl (ex-rds :m (ex-kid-of e n2) 0) L n) n))
                    (t (ex-mkok :m (ex-kid-of e n2) 0 L n))))
        ((:rec :call :coll) (if (< i nk) (and (ex-mkok :m (ex-kid-of e i) 0 (ex-lv flg e (1+ i) nil L n) n) (ex-mkok flg e (1+ i) L n)) t))
        (:cs (if (< i (len (ex-c e))) (and (ex-mkok :m (ex-cbody e i) 0 L n) (ex-mkok :cs e (1+ i) L n)) t))
        (:ct (if (< i (len (ex-c e))) (and (ex-mkok :m (ex-cthen e i) 0 L n) (ex-mkok :ct e (1+ i) L n)) t))
        (:fin (ex-mkok :m (ex-kid-of e 1) 0 L n))
        (otherwise
         (cond ((equal k 2) (implies (ex-mark e) (and (< n2 (nfix n)) (equal (nth n2 L) 0))))
               ((equal k 4) (and (ex-mkok :m (ex-kid-of e 0) 0
                                          (sp-or (ex-lv :m (ex-kid-of e 1) 0 nil L n) (ex-lv :m (ex-kid-of e 2) 0 nil L n)) n)
                                 (ex-mkok :m (ex-kid-of e 1) 0 L n) (ex-mkok :m (ex-kid-of e 2) 0 L n)))
               ((equal k 5) (ex-mkok :do e 0 L n))
               ((or (equal k 11) (equal k 12)) (ex-mkok :let e 0 L n))
               ((equal k 16) (ex-mkok :rec e 0 L n))
               ((equal k 17) (ex-mkok :m (ex-kid-of e 0) 0 L n))
               ((equal k 18) (let ((L1 (ex-lv :fin e 0 nil L n)))
                               (and (ex-mkok :m (ex-kid-of e 0) 0 (ex-lv :cs e 0 L1 L1 n) n)
                                    (ex-mkok :cs e 0 L1 n) (ex-mkok :fin e 0 L n))))
               ((member k '(7 8 9 22 23 10 20 24)) (ex-mkok :coll e 0 L n))
               ((equal k 19) (and (ex-mkok :m (ex-kid-of e 0) 0 (sp-or (ex-lv :ct e 0 L L n) (ex-lv :m (ex-kid-of e 1) 0 nil L n)) n)
                                  (ex-mkok :m (ex-kid-of e 1) 0 L n) (ex-mkok :ct e 0 L n)))
               ((equal k 6) (and (ex-mkok :m (ex-kid-of e 0) 0 (ex-lv :call e 1 nil L n) n) (ex-mkok :call e 1 L n)))
               (t t)))))))

; ex-vwf's clearing conditions, its scopes threaded as it threads them: B
; the slots blanked from the scope
(defun ex-cwf (flg e i B)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        t
      (case flg
        (:do (cond ((zp nk) t)
                   ((< i (- nk 1)) (and (ex-cwf :m (ex-kid-of e i) 0 B) (ex-cwf :do e (1+ i) (append (ex-clr :m (ex-kid-of e i) 0) B))))
                   (t (ex-cwf :m (ex-kid-of e (- nk 1)) 0 B))))
        (:let (cond ((< i n2) (and (ex-cwf :m (ex-kid-of e i) 0 B) (ex-cwf :let e (1+ i) (append (ex-clr :m (ex-kid-of e i) 0) B))))
                    ((equal k 12) (and (atom (ex-clr :m (ex-kid-of e n2) 0)) (ex-cwf :m (ex-kid-of e n2) 0 B)))
                    (t (ex-cwf :m (ex-kid-of e n2) 0 B))))
        ((:rec :call :coll) (if (< i nk) (and (ex-cwf :m (ex-kid-of e i) 0 B) (ex-cwf flg e (1+ i) (append (ex-clr :m (ex-kid-of e i) 0) B))) t))
        (:cs (if (< i (len (ex-c e))) (and (ex-cwf :m (ex-cbody e i) 0 B) (ex-cwf :cs e (1+ i) B)) t))
        (:ct (if (< i (len (ex-c e))) (and (ex-cwf :m (ex-cthen e i) 0 B) (ex-cwf :ct e (1+ i) B)) t))
        (:fin (ex-cwf :m (ex-kid-of e 1) 0 B))
        (otherwise
         (cond ((equal k 2) (not (member-equal n2 B)))
               ((equal k 14) (not (intersectp-equal B (ex-outers (nth 2 (ex-c e))))))
               ((equal k 4) (and (ex-cwf :m (ex-kid-of e 0) 0 B)
                                 (ex-cwf :m (ex-kid-of e 1) 0 (append (ex-clr :m (ex-kid-of e 0) 0) B))
                                 (ex-cwf :m (ex-kid-of e 2) 0 (append (ex-clr :m (ex-kid-of e 0) 0) B))))
               ((equal k 5) (ex-cwf :do e 0 B))
               ((or (equal k 11) (equal k 12)) (ex-cwf :let e 0 B))
               ((equal k 16) (ex-cwf :rec e 0 B))
               ((equal k 17) (ex-cwf :m (ex-kid-of e 0) 0 B))
               ((equal k 18) (and (ex-cwf :m (ex-kid-of e 0) 0 B)
                                  (ex-cwf :cs e 0 (append (ex-clr :m (ex-kid-of e 0) 0) B))
                                  (ex-cwf :fin e 0 (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0) B))))
               ((member k '(7 8 9 22 23 10 20 24)) (ex-cwf :coll e 0 B))
               ((equal k 19) (and (ex-cwf :m (ex-kid-of e 0) 0 B)
                                  (ex-cwf :m (ex-kid-of e 1) 0 (append (ex-clr :m (ex-kid-of e 0) 0) B))
                                  (ex-cwf :ct e 0 (append (ex-clr :m (ex-kid-of e 0) 0) B))))
               ((equal k 6) (and (ex-cwf :m (ex-kid-of e 0) 0 B) (ex-cwf :call e 1 (append (ex-clr :m (ex-kid-of e 0) 0) B))))
               (t t)))))))

; ---- WHAT STAYS LIVE, WHAT IS READ ---------------------------------------------------------------

(defthm ex-len-sp-or (equal (len (sp-or a b)) (len a)))
(defthm ex-len-setl (implies (equal (len L) n) (equal (len (ex-setl ss L n)) n)))

(defthm ex-len-lv
  (implies (and (equal (len L) n) (implies (member flg '(:cs :ct)) (equal (len A) n)))
           (equal (len (ex-lv flg e i A L n)) n))
  :hints (("Goal" :induct (ex-lv flg e i A L n) :in-theory (disable ex-kid-of))))

(defthm ex-setl-mono
  (implies (and (natp s) (not (equal (nth s L) 0))) (not (equal (nth s (ex-setl ss L n)) 0))))

(defthm ex-setl-sets
  (implies (and (natp s) (< s n) (equal (len L) n) (member-equal s ss)) (not (equal (nth s (ex-setl ss L n)) 0))))

(defthm ex-sp-or-1
  (implies (and (natp s) (< s (len a)) (not (equal (nth s a) 0))) (not (equal (nth s (sp-or a b)) 0))))
(defthm ex-sp-or-2
  (implies (and (natp s) (< s (len a)) (not (equal (nth s b) 0))) (not (equal (nth s (sp-or a b)) 0))))
(in-theory (disable sp-or))

(defthm ex-lv-mono
  (implies (and (natp s) (< s n) (equal (len L) n)
                (if (member flg '(:cs :ct)) (and (equal (len A) n) (not (equal (nth s A) 0))) (not (equal (nth s L) 0))))
           (not (equal (nth s (ex-lv flg e i A L n)) 0)))
  :hints (("Goal" :induct (ex-lv flg e i A L n) :in-theory (disable ex-kid-of))))

(defthm ex-lv-mono-alt
  (implies (and (natp s) (< s n) (equal (len L) n) (member flg '(:cs :ct)) (equal (len A) n) (not (equal (nth s A) 0)))
           (not (equal (nth s (ex-lv flg e i A L n)) 0)))
  :hints (("Goal" :use ex-lv-mono :in-theory (disable ex-lv-mono ex-lv))))
(defthm ex-lv-mono-1
  (implies (and (natp s) (< s n) (equal (len L) n) (not (member flg '(:cs :ct))) (not (equal (nth s L) 0)))
           (not (equal (nth s (ex-lv flg e i A L n)) 0)))
  :hints (("Goal" :use ex-lv-mono :in-theory (disable ex-lv-mono ex-lv))))
(in-theory (disable ex-lv-mono))

(defthm ex-lv-alt-open
  (implies (and (syntaxp (variablep i)) (member flg '(:cs :ct)) (consp e))
           (equal (ex-lv flg e i A L n)
                  (if (< (nfix i) (len (ex-c e)))
                      (ex-lv flg e (1+ (nfix i))
                             (sp-or (ex-lv :m (if (equal flg :cs) (ex-cbody e (nfix i)) (ex-cthen e (nfix i))) 0 nil L n) A) L n)
                    A))))

(defthm ex-lv-rds
  (implies (and (natp s) (< s n) (equal (len L) n) (implies (member flg '(:cs :ct)) (equal (len A) n))
                (member-equal s (ex-rds flg e i)))
           (not (equal (nth s (ex-lv flg e i A L n)) 0)))
  :hints (("Goal" :induct (ex-lv flg e i A L n) :in-theory (disable ex-kid-of))))

(defthm ex-mkok-clr
  (implies (and (ex-mkok flg e i L n) (equal (len L) n) (member-equal s (ex-clr flg e i)))
           (and (natp s) (< s n) (equal (nth s L) 0)))
  :hints (("Goal" :induct (ex-mkok flg e i L n) :in-theory (disable ex-kid-of))))

; ---- A CLEARED SLOT IS READ NO MORE ----------------------------------------------------------------

(defthm ex-clr-rds
  (implies (member-equal s (ex-clr flg e i)) (member-equal s (ex-rds flg e i)))
  :hints (("Goal" :induct (ex-clr flg e i) :in-theory (disable ex-kid-of)
           :expand ((ex-clr :do e i) (ex-clr :let e i) (ex-clr :rec e i) (ex-clr :call e i) (ex-clr :coll e i) (ex-clr :cs e i) (ex-clr :ct e i) (ex-rds :do e i) (ex-rds :let e i) (ex-rds :rec e i) (ex-rds :call e i) (ex-rds :coll e i) (ex-rds :cs e i) (ex-rds :ct e i)))))

; every slot of R below n live in X; every slot of C dead in it
(defun ex-allnz (R X n)
  (if (atom R) t (and (implies (and (natp (car R)) (< (car R) n)) (not (equal (nth (car R) X) 0))) (ex-allnz (cdr R) X n))))
(defun ex-dead (C X n)
  (if (atom C) t (and (natp (car C)) (< (car C) n) (equal (nth (car C) X) 0) (ex-dead (cdr C) X n))))

(defthm ex-allnz-sub
  (implies (and (subsetp-equal R (ex-rds flg e i)) (equal (len L) n) (implies (member flg '(:cs :ct)) (equal (len A) n)))
           (ex-allnz R (ex-lv flg e i A L n) n))
  :hints (("Goal" :induct (len R) :in-theory (disable ex-lv ex-rds ex-lv-rds))
          ("Subgoal *1/1" :use ((:instance ex-lv-rds (s (car R)))))))
(defthm ex-allnz-lv
  (implies (and (equal (len L) n) (implies (member flg '(:cs :ct)) (equal (len A) n)))
           (ex-allnz (ex-rds flg e i) (ex-lv flg e i A L n) n))
  :hints (("Goal" :in-theory (disable ex-lv ex-rds ex-allnz-sub) :use ((:instance ex-allnz-sub (R (ex-rds flg e i)))))))

(defthm ex-dead-sub
  (implies (and (subsetp-equal C (ex-clr flg e i)) (ex-mkok flg e i X n) (equal (len X) n))
           (ex-dead C X n))
  :hints (("Goal" :induct (len C) :in-theory (disable ex-mkok ex-clr ex-mkok-clr))
          ("Subgoal *1/1" :use ((:instance ex-mkok-clr (s (car C)) (L X))))))
(defthm ex-dead-clr
  (implies (and (ex-mkok flg e i X n) (equal (len X) n)) (ex-dead (ex-clr flg e i) X n))
  :hints (("Goal" :in-theory (disable ex-mkok ex-clr ex-dead-sub) :use ((:instance ex-dead-sub (C (ex-clr flg e i)))))))

(defthm ex-allnz-member
  (implies (and (ex-allnz R X n) (member-equal s R) (natp s) (< s n)) (not (equal (nth s X) 0))))
(defthm ex-dead-allnz
  (implies (and (ex-dead C X n) (ex-allnz R X n)) (not (intersectp-equal C R))))

; the parts after a place: dead what an earlier part cleared, live what they read
(defthm ex-sep
  (implies (and (ex-mkok f1 e1 i1 X n) (equal (len X) n) (ex-allnz R X n))
           (not (intersectp-equal (ex-clr f1 e1 i1) R)))
  :hints (("Goal" :in-theory (disable ex-mkok ex-clr ex-dead-allnz) :use ((:instance ex-dead-allnz (C (ex-clr f1 e1 i1)))))))

(defthm ex-allnz-mono-1
  (implies (and (ex-allnz R X n) (equal (len X) n) (not (member flg '(:cs :ct))))
           (ex-allnz R (ex-lv flg e i A X n) n))
  :hints (("Goal" :in-theory (disable ex-lv))))
(defthm ex-allnz-mono-alt
  (implies (and (ex-allnz R X n) (equal (len X) n) (member flg '(:cs :ct)) (equal (len L) n))
           (ex-allnz R (ex-lv flg e i X L n) n))
  :hints (("Goal" :in-theory (disable ex-lv))))
(defthm ex-allnz-or-1 (implies (and (ex-allnz R a n) (equal (len a) n)) (ex-allnz R (sp-or a b) n)) :hints (("Goal" :induct (len R))))
(defthm ex-allnz-or-2 (implies (and (ex-allnz R b n) (equal (len a) n)) (ex-allnz R (sp-or a b) n)) :hints (("Goal" :induct (len R))))
(defthm ex-allnz-setl (implies (equal (len L) n) (ex-allnz ss (ex-setl ss L n) n)))

(defthm ex-int-app1 (equal (intersectp-equal (append a b) c) (or (intersectp-equal a c) (intersectp-equal b c))))
(defthm ex-int-app2 (equal (intersectp-equal c (append a b)) (or (intersectp-equal c a) (intersectp-equal c b))))
(defthm ex-int-nil (not (intersectp-equal a nil)))
(defthm ex-int-cons (equal (intersectp-equal a (cons x b)) (or (and (member-equal x a) t) (intersectp-equal a b))))

; a loop body clears nothing: every slot it reads is live after it
(defthm ex-loop-noclr
  (implies (and (ex-mkok :m b 0 (ex-setl (ex-rds :m b 0) L n) n) (equal (len L) n))
           (not (consp (ex-clr :m b 0))))
  :hints (("Goal" :in-theory (disable ex-mkok ex-clr ex-rds ex-sep ex-allnz-setl)
           :use ((:instance ex-sep (f1 :m) (e1 b) (i1 0) (X (ex-setl (ex-rds :m b 0) L n)) (R (ex-rds :m b 0)))
                 (:instance ex-allnz-setl (ss (ex-rds :m b 0)))
                 (:instance ex-clr-rds (s (car (ex-clr :m b 0))) (flg :m) (e b) (i 0))))))

; the induction ex-cwf-mkok takes: ex-cwf's, each part with the live set after it
(defun ex-cwf-ind (flg e i B L)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)) (n (len L)))
    (if (not (consp e))
        (list B L)
      (case flg
        (:do (cond ((zp nk) t)
                   ((< i (- nk 1)) (list (ex-cwf-ind :m (ex-kid-of e i) 0 B (ex-lv :do e (1+ i) nil L n))
                                         (ex-cwf-ind :do e (1+ i) (append (ex-clr :m (ex-kid-of e i) 0) B) L)))
                   (t (ex-cwf-ind :m (ex-kid-of e (- nk 1)) 0 B L))))
        (:let (cond ((< i n2) (list (ex-cwf-ind :m (ex-kid-of e i) 0 B (ex-lv :let e (1+ i) nil L n))
                                    (ex-cwf-ind :let e (1+ i) (append (ex-clr :m (ex-kid-of e i) 0) B) L)))
                    ((equal k 12) (ex-cwf-ind :m (ex-kid-of e n2) 0 B (ex-setl (ex-rds :m (ex-kid-of e n2) 0) L n)))
                    (t (ex-cwf-ind :m (ex-kid-of e n2) 0 B L))))
        ((:rec :call :coll) (if (< i nk) (list (ex-cwf-ind :m (ex-kid-of e i) 0 B (ex-lv flg e (1+ i) nil L n))
                                               (ex-cwf-ind flg e (1+ i) (append (ex-clr :m (ex-kid-of e i) 0) B) L))
                              t))
        (:cs (if (< i (len (ex-c e))) (list (ex-cwf-ind :m (ex-cbody e i) 0 B L) (ex-cwf-ind :cs e (1+ i) B L)) t))
        (:ct (if (< i (len (ex-c e))) (list (ex-cwf-ind :m (ex-cthen e i) 0 B L) (ex-cwf-ind :ct e (1+ i) B L)) t))
        (:fin (ex-cwf-ind :m (ex-kid-of e 1) 0 B L))
        (otherwise
         (cond ((equal k 4) (list (ex-cwf-ind :m (ex-kid-of e 0) 0 B (sp-or (ex-lv :m (ex-kid-of e 1) 0 nil L n) (ex-lv :m (ex-kid-of e 2) 0 nil L n)))
                                  (ex-cwf-ind :m (ex-kid-of e 1) 0 (append (ex-clr :m (ex-kid-of e 0) 0) B) L)
                                  (ex-cwf-ind :m (ex-kid-of e 2) 0 (append (ex-clr :m (ex-kid-of e 0) 0) B) L)))
               ((equal k 5) (ex-cwf-ind :do e 0 B L))
               ((or (equal k 11) (equal k 12)) (ex-cwf-ind :let e 0 B L))
               ((equal k 16) (ex-cwf-ind :rec e 0 B L))
               ((equal k 17) (ex-cwf-ind :m (ex-kid-of e 0) 0 B L))
               ((equal k 18) (let ((L1 (ex-lv :fin e 0 nil L n)))
                               (list (ex-cwf-ind :m (ex-kid-of e 0) 0 B (ex-lv :cs e 0 L1 L1 n))
                                     (ex-cwf-ind :cs e 0 (append (ex-clr :m (ex-kid-of e 0) 0) B) L1)
                                     (ex-cwf-ind :fin e 0 (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0) B) L))))
               ((member k '(7 8 9 22 23 10 20 24)) (ex-cwf-ind :coll e 0 B L))
               ((equal k 19) (list (ex-cwf-ind :m (ex-kid-of e 0) 0 B (sp-or (ex-lv :ct e 0 L L n) (ex-lv :m (ex-kid-of e 1) 0 nil L n)))
                                   (ex-cwf-ind :m (ex-kid-of e 1) 0 (append (ex-clr :m (ex-kid-of e 0) 0) B) L)
                                   (ex-cwf-ind :ct e 0 (append (ex-clr :m (ex-kid-of e 0) 0) B) L)))
               ((equal k 6) (list (ex-cwf-ind :m (ex-kid-of e 0) 0 B (ex-lv :call e 1 nil L n))
                                  (ex-cwf-ind :call e 1 (append (ex-clr :m (ex-kid-of e 0) 0) B) L)))
               (t t)))))))

(defthm ex-cwf-mkok-l
  (implies (and (ex-mkok flg e i L (len L)) (not (intersectp-equal B (ex-rds flg e i))))
           (ex-cwf flg e i B))
  :hints (("Goal" :induct (ex-cwf-ind flg e i B L) :in-theory (disable ex-kid-of ex-lv ex-allnz ex-dead)
           :expand ((ex-mkok flg e i L (len L)) (ex-mkok :do e i L (len L)) (ex-mkok :let e i L (len L)) (ex-mkok :rec e i L (len L)) (ex-mkok :call e i L (len L)) (ex-mkok :coll e i L (len L)) (ex-mkok :cs e i L (len L)) (ex-mkok :ct e i L (len L)) (ex-rds flg e i) (ex-rds :do e i) (ex-rds :let e i) (ex-rds :rec e i) (ex-rds :call e i) (ex-rds :coll e i) (ex-rds :cs e i) (ex-rds :ct e i)))))

(defthm ex-cwf-mkok
  (implies (and (ex-mkok flg e i L n) (equal (len L) n) (not (intersectp-equal B (ex-rds flg e i))))
           (ex-cwf flg e i B))
  :hints (("Goal" :in-theory (disable ex-mkok ex-cwf ex-rds))))

; ANPASS'S MARKS RUN ON THE VM AS ON THE TREE (exec-PLAN milestone 4): the
; composition. exec-vm's ex-vm-agree (and exec-vmrun's ex-vm-runs) take a
; tree ex-vwf calls well formed, its marked reads among its conditions;
; exec-clr shows anpass's marks meet those conditions. Here they are put
; together.
;
;   ex-vwf0      well formed with nothing cleared: ex-vwf with no scope
;                blanked and no clearing conditions -- the tree before
;                apply_clears -- but for the one case ex-vwf does not
;                admit, asked here: a loop's init clears no slot of the
;                loop (else the loop translation's copy of an earlier
;                init's slot would read it cleared)
;   ex-bl        a scope cm2 is cm with some entries of B blanked
;   ex-vwf-cwf   ex-vwf0 and ex-cwf (exec-clr: no later part reads what an
;                earlier part may clear, a loop body clears nothing) give
;                ex-vwf
;   ex-anp-runs  so a tree whose marks are anpass's (ex-mkok over its live
;                sets, which exec-clrlv shows are sp-out's) runs on the VM
;                as on the tree: ex-vm-runs' conclusion, ex-vwf replaced by
;                ex-vwf0 and the marks' liveness. The fn templates in defs
;                are taken well formed as ex-vm-runs takes them (ex-defs-ok;
;                exec-clrfn's ex-arwf-body gives a body's fn-recur condition).
;   ex-anmk-hfr  a body whose marked reads (ex-mks) are among apply_clears'
;                over the fn's frame clears nothing when it recurs to its
;                fn: anpass-proof's anp-clears-spec, those marks none
;   ex-anp-runs-defs  ex-anp-runs with the templates as the analyzer leaves
;                them (ex-defs-ok0: each arity's body ex-vwf0 in the fn's
;                scope, of anpass's shapes, the tail check passed, its marks
;                ex-mkok's and apply_clears', over a live set and a pass of
;                its own) in place of ex-defs-ok

(in-package "ACL2")

(include-book "exec-clrfn")
(include-book "exec-vmrun")

(defun ex-vwf0 (flg e i cm lp defs)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (and (consp e)
         (case flg
           (:do (cond ((zp nk) t)
                      ((< i (- nk 1)) (and (ex-vwf0 :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf0 :do e (1+ i) cm lp defs)))
                      (t (ex-vwf0 :m (ex-kid-of e (- nk 1)) 0 cm lp defs))))
           (:let (cond ((< i n2)
                        (and (or (equal k 11) (equal k 12)) (not (member-equal (+ (ex-s2 e) i) cm))
                             (or (equal k 11) (not (intersectp-equal (ex-clr :m (ex-kid-of e i) 0) (ex-slots (ex-s2 e) n2))))
                             (ex-vwf0 :m (ex-kid-of e i) 0 cm nil defs)
                             (ex-vwf0 :let e (1+ i) (append cm (list (+ (ex-s2 e) i))) lp defs)))
                       ((equal k 11) (ex-vwf0 :m (ex-kid-of e n2) 0 cm lp defs))
                       ((equal k 12)
                        (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                          (and (subsetp-equal (cdr ls) cm)
                               (ex-vwf0 :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (cons (ex-s2 e) n2) defs))))
                       (t nil)))
           (:rec (and (equal k 16) (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                      (equal nk (cdr lp))
                      (if (< i nk)
                          (and (ex-vwf0 :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf0 :rec e (1+ i) cm lp defs))
                        (equal i nk))))
           (:call (and (equal k 6)
                       (if (< i nk)
                           (and (ex-vwf0 :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf0 :call e (1+ i) cm lp defs))
                         t)))
           (:cs (and (equal k 18)
                     (if (< i (len (ex-c e)))
                         (and (not (member-equal (ex-cslot e i) cm))
                              (ex-vwf0 :m (ex-cbody e i) 0 (append cm (list (ex-cslot e i))) nil defs)
                              (ex-vwf0 :cs e (1+ i) cm lp defs))
                       t)))
           (:fin (or (not (< 1 nk)) (ex-vwf0 :m (ex-kid-of e 1) 0 (append cm (list nil)) nil defs)))
           (:coll (and (member k '(7 8 9 22 23 10 20 24 21))
                       (if (< i nk)
                           (and (ex-vwf0 :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf0 :coll e (1+ i) cm lp defs))
                         t)))
           (:ct (and (equal k 19)
                     (if (< i (len (ex-c e)))
                         (and (ex-vwf0 :m (ex-cthen e i) 0 cm lp defs) (ex-vwf0 :ct e (1+ i) cm lp defs))
                       t)))
           (otherwise
            (cond ((or (equal k 1) (equal k 3)) (ex-xvs defs (list (ex-c e))))
                  ((equal k 2) (member-equal (ex-i2 e) cm))
                  ((member k '(14 15)) (and (consp (assoc-equal (ex-c e) defs))
                                     (nat-listp (ex-outers (nth 2 (ex-c e))))
                                     (subsetp-equal (ex-outers (nth 2 (ex-c e))) cm)))
                  ((equal k 6) (and (< 0 nk) (ex-vwf0 :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf0 :call e 1 (append cm (list nil)) lp defs)))
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-vwf0 :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf0 :m (ex-kid-of e 1) 0 cm lp defs)
                                    (or (equal nk 2) (ex-vwf0 :m (ex-kid-of e 2) 0 cm lp defs))))
                  ((equal k 5) (ex-vwf0 :do e 0 cm lp defs))
                  ((equal k 11) (and (equal nk (1+ n2)) (ex-vwf0 :let e 0 cm lp defs)))
                  ((equal k 12) (and (equal nk (1+ n2)) (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm)
                                     (ex-vwf0 :let e 0 cm lp defs)))
                  ((equal k 13) (and (equal nk (1+ n2)) (ex-lffns e 0) (ex-lfok e 0 cm defs)
                                     (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm)
                                     (ex-vwf0 :m (ex-kid-of e n2) 0 (append cm (ex-slots (ex-s2 e) n2)) lp defs)))
                  ((equal k 16) (and (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                                     (equal nk (cdr lp)) (ex-vwf0 :rec e 0 cm lp defs)))
                  ((equal k 17) (and (equal nk 1) (ex-vwf0 :m (ex-kid-of e 0) 0 cm nil defs)))
                  ((equal k 18) (and (or (equal nk 1) (equal nk 2)) (ex-vwf0 :m (ex-kid-of e 0) 0 cm nil defs)
                                     (ex-vwf0 :cs e 0 cm nil defs)
                                     (ex-vwf0 :fin e 0 cm nil defs)))
                  ((member k '(7 8 9 22 23 10 20 24 21)) (ex-vwf0 :coll e 0 cm nil defs))
                  ((equal k 19) (and (equal nk 2) (ex-vwf0 :m (ex-kid-of e 0) 0 cm nil defs)
                                     (ex-vwf0 :m (ex-kid-of e 1) 0 (append cm (list nil)) lp defs)
                                     (ex-vwf0 :ct e 0 (append cm (list nil)) lp defs)))
                  (t nil)))))))

; ---- A SCOPE WITH SOME OF B BLANKED --------------------------------------------------------------

(defun ex-bl (B cm cm2)
  (if (atom cm)
      (atom cm2)
    (and (consp cm2)
         (or (equal (car cm2) (car cm)) (and (null (car cm2)) (member-equal (car cm) B)))
         (ex-bl B (cdr cm) (cdr cm2)))))

(defthm ex-bl-blank (implies (ex-bl B cm cm2) (ex-bl (append c B) cm (ex-blank c cm2))))
(defthm ex-bl-blank-app (implies (ex-bl B cm cm2) (ex-bl (append a d B) cm (ex-blank (append a d) cm2)))
  :hints (("Goal" :use ((:instance ex-bl-blank (c (append a d)))) :in-theory (disable ex-bl-blank))))
(defthm ex-bl-blank2 (implies (ex-bl B cm cm2) (ex-bl B (ex-blank c cm) (ex-blank c cm2))))
(defthm ex-bl-app (implies (and (ex-bl B cm cm2) (true-listp l)) (ex-bl B (append cm l) (append cm2 l))))
(defthm ex-bl-more (implies (ex-bl B cm cm2) (ex-bl (append c B) cm cm2)))
(defthm ex-bl-mem
  (implies (and (ex-bl B cm cm2) (member-equal x cm) (not (member-equal x B))) (member-equal x cm2)))
(defthm ex-bl-nomem
  (implies (and (ex-bl B cm cm2) x (not (member-equal x cm))) (not (member-equal x cm2))))
(defthm ex-bl-sub
  (implies (and (ex-bl B cm cm2) (subsetp-equal l cm) (not (intersectp-equal B l))) (subsetp-equal l cm2)))
(defthm ex-bl-nomem-ls (implies (and (ex-bl B cm cm2) (ex-nomem ls cm)) (ex-nomem ls cm2)))

; a loop's slots, each init's appended, stay in scope when no init clears one
(defthm ex-slots-snoc-n
  (implies (and (natp s) (natp i)) (equal (ex-slots s (1+ i)) (append (ex-slots s i) (list (+ s i)))))
  :hints (("Goal" :induct (ex-slots s i) :in-theory (enable ex-slots) :expand ((ex-slots s (1+ i)) (ex-slots s 1)))))
(defthm ex-slots-snoc
  (implies (natp s) (equal (ex-slots s (1+ (nfix i))) (append (ex-slots s (nfix i)) (list (+ s (nfix i))))))
  :hints (("Goal" :use ((:instance ex-slots-snoc-n (i (nfix i)))) :in-theory (disable ex-slots-snoc-n))))
(defthm ex-mem-blank (implies (and (member-equal x cm) (not (member-equal x c))) (member-equal x (ex-blank c cm))))
(defthm ex-sub-blank (implies (and (subsetp-equal a cm) (not (intersectp-equal c a))) (subsetp-equal a (ex-blank c cm))))
(defthm ex-sub-snoc (equal (subsetp-equal (append a (list x)) l) (and (subsetp-equal a l) (member-equal x l) t)))
(defthm ex-mem-slots-iff
  (iff (member-equal x (ex-slots s n)) (and (natp x) (<= (nfix s) x) (< x (+ (nfix s) (nfix n)))))
  :hints (("Goal" :induct (ex-slots s n) :in-theory (enable ex-slots))))
(defthm ex-int-slots-less
  (implies (and (natp s) (natp i) (natp n) (<= i n) (not (intersectp-equal c (ex-slots s n))))
           (not (intersectp-equal c (ex-slots s i))))
  :hints (("Goal" :induct (len c))))
(defun ex-dn (i n) (if (and (natp i) (natp n) (< n i)) (ex-dn (1- i) n) t))
(defthm ex-slots-sub-less
  (implies (and (subsetp-equal (ex-slots s i) l) (natp s) (natp n) (natp i) (<= n i)) (subsetp-equal (ex-slots s n) l))
  :hints (("Goal" :induct (ex-dn i n)) ("Subgoal *1/1" :use ((:instance ex-slots-snoc-n (i (1- i)))) :in-theory (disable ex-slots-snoc-n ex-slots-snoc))))
(defthm ex-nomem-blank-x (implies (and x (not (member-equal x l))) (not (member-equal x (ex-blank c l)))))

; a letfn: ex-cwf walks it as a let, its fns clearing nothing, so its body
; is ex-cwf's at B and each fn's outer slots stay in the scope with B blanked
(defthm ex-lfin-bl
  (implies (and (ex-lfin os s n cm) (not (intersectp-equal B os)) (ex-bl B cm cm2)) (ex-lfin os s n cm2)))
(defthm ex-cwf-lf-body
  (implies (and (consp e) (equal (ex-kind e) 13) (ex-lffns e j) (ex-cwf :let e j B) (natp j) (<= j (ex-i2 e)))
           (ex-cwf :m (ex-kid-of e (ex-i2 e)) 0 B))
  :hints (("Goal" :induct (ex-lfoall e j) :in-theory (disable ex-kid-of ex-cwf ex-clr)
           :expand ((ex-cwf :let e j B) (ex-lffns e j) (ex-clr :m (ex-kid-of e j) 0)))))
(defthm ex-cwf-lf-fns
  (implies (and (consp e) (equal (ex-kind e) 13) (ex-lffns e j) (ex-cwf :let e j B) (ex-lfok e j cm defs) (ex-bl B cm cm2) (natp j))
           (ex-lfok e j cm2 defs))
  :hints (("Goal" :induct (ex-lfoall e j) :in-theory (disable ex-kid-of ex-cwf ex-clr)
           :expand ((ex-cwf :let e j B) (ex-lffns e j) (ex-lfok e j cm defs) (ex-lfok e j cm2 defs) (ex-clr :m (ex-kid-of e j) 0)
                    (ex-cwf :m (ex-kid-of e j) 0 B)))))

; ---- THE COMPOSITION ------------------------------------------------------------------------------

; ex-vwf0's walk, with ex-vwf's scope cm2 and ex-cwf's B threaded beside it
(defun ex-cmpind (flg e i cm cm2 B lp)
  (declare (xargs :measure (ex-cmeas) :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        (list cm cm2 B lp)
      (case flg
        (:do (cond ((zp nk) t)
                   ((< i (- nk 1)) (list (ex-cmpind :m (ex-kid-of e i) 0 cm cm2 B nil)
                                         (ex-cmpind :do e (1+ i) cm (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) (append (ex-clr :m (ex-kid-of e i) 0) B) lp)))
                   (t (ex-cmpind :m (ex-kid-of e (- nk 1)) 0 cm cm2 B lp))))
        (:let (cond ((< i n2) (let ((s (+ (ex-s2 e) i)) (c (ex-clr :m (ex-kid-of e i) 0)))
                                (list (ex-cmpind :m (ex-kid-of e i) 0 cm cm2 B nil)
                                      (ex-cmpind :let e (1+ i) (append cm (list s)) (append (ex-blank c cm2) (list s)) (append c B) lp))))
                    ((equal k 11) (ex-cmpind :m (ex-kid-of e n2) 0 cm cm2 B lp))
                    (t (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                         (ex-cmpind :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (append (ex-blank ls cm2) ls) B (cons (ex-s2 e) n2))))))
        ((:rec :call :coll) (if (< i nk)
                                (list (ex-cmpind :m (ex-kid-of e i) 0 cm cm2 B nil)
                                      (ex-cmpind flg e (1+ i) cm (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) (append (ex-clr :m (ex-kid-of e i) 0) B) lp))
                              t))
        (:cs (if (< i (len (ex-c e)))
                 (list (ex-cmpind :m (ex-cbody e i) 0 (append cm (list (ex-cslot e i))) (append cm2 (list (ex-cslot e i))) B nil)
                       (ex-cmpind :cs e (1+ i) cm cm2 B lp))
               t))
        (:fin (ex-cmpind :m (ex-kid-of e 1) 0 (append cm (list nil)) (append cm2 (list nil)) B nil))
        (:ct (if (< i (len (ex-c e))) (list (ex-cmpind :m (ex-cthen e i) 0 cm cm2 B lp) (ex-cmpind :ct e (1+ i) cm cm2 B lp)) t))
        (otherwise
         (let ((c0 (ex-clr :m (ex-kid-of e 0) 0)))
           (cond ((equal k 4) (list (ex-cmpind :m (ex-kid-of e 0) 0 cm cm2 B nil)
                                    (ex-cmpind :m (ex-kid-of e 1) 0 cm (ex-blank c0 cm2) (append c0 B) lp)
                                    (ex-cmpind :m (ex-kid-of e 2) 0 cm (ex-blank c0 cm2) (append c0 B) lp)))
                 ((equal k 5) (ex-cmpind :do e 0 cm cm2 B lp))
                 ((or (equal k 11) (equal k 12)) (ex-cmpind :let e 0 cm cm2 B lp))
                 ((equal k 13) (ex-cmpind :m (ex-kid-of e n2) 0 (append cm (ex-slots (ex-s2 e) n2)) (append cm2 (ex-slots (ex-s2 e) n2)) B lp))
                 ((equal k 16) (ex-cmpind :rec e 0 cm cm2 B lp))
                 ((equal k 17) (ex-cmpind :m (ex-kid-of e 0) 0 cm cm2 B nil))
                 ((equal k 18) (list (ex-cmpind :m (ex-kid-of e 0) 0 cm cm2 B nil)
                                     (ex-cmpind :cs e 0 cm (ex-blank c0 cm2) (append c0 B) nil)
                                     (ex-cmpind :fin e 0 cm (ex-blank (append c0 (ex-clr :cs e 0)) cm2) (append c0 (ex-clr :cs e 0) B) nil)))
                 ((member k '(7 8 9 22 23 10 20 24 21)) (ex-cmpind :coll e 0 cm cm2 B nil))
                 ((equal k 19) (list (ex-cmpind :m (ex-kid-of e 0) 0 cm cm2 B nil)
                                     (ex-cmpind :m (ex-kid-of e 1) 0 (append cm (list nil)) (append (ex-blank c0 cm2) (list nil)) (append c0 B) lp)
                                     (ex-cmpind :ct e 0 (append cm (list nil)) (append (ex-blank c0 cm2) (list nil)) (append c0 B) lp)))
                 ((equal k 6) (list (ex-cmpind :m (ex-kid-of e 0) 0 cm cm2 B nil)
                                    (ex-cmpind :call e 1 (append cm (list nil)) (append (ex-blank c0 cm2) (list nil)) (append c0 B) lp)))
                 (t t))))))))

(defthm ex-vwf-cwf
  (implies (and (ex-vwf0 flg e i cm lp defs) (ex-cwf flg e i B) (ex-bl B cm cm2)
                (implies (and (equal flg :let) (equal (ex-kind e) 12)) (subsetp-equal (ex-slots (ex-s2 e) (nfix i)) cm2)))
           (ex-vwf flg e i cm2 lp defs))
  :hints (("Goal" :induct (ex-cmpind flg e i cm cm2 B lp)
           :in-theory (disable (:definition ex-vwf) (:definition ex-vwf0) (:definition ex-cwf) ex-kid-of ex-clr ex-astf ex-ast-open
                               ex-vwf-lpfree)
           :expand ((:free (flg cm lp) (ex-vwf flg e i cm lp defs)) (:free (flg cm lp) (ex-vwf0 flg e i cm lp defs))
                    (:free (flg B) (ex-cwf flg e i B))))))

; ---- END TO END -----------------------------------------------------------------------------------

; a tree whose marks are anpass's liveness decision runs on the VM as on the tree
(defthm ex-anp-runs
  (implies (and (ex-vwf0 :m e 0 nil nil defs) (ex-mkok :m e 0 L n) (equal (len L) n)
                (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs)
                (or (valp (car (ex-ev :m e 0 nil fr fuel))) (thrownp (car (ex-ev :m e 0 nil fr fuel)))) (natp k))
           (equal (vcs2-run-program (ex-tr :m e 0 nil) defs (+ (s2clk (ex-tr :m e 0 nil) nil nil defs fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcs2-run-program s2clk ex-ev ex-tr ex-vwf ex-vwf0 ex-cwf ex-mkok mx2 ex-defs-ok
                                      ex-vm-runs ex-vwf-cwf ex-cwf-mkok)
           :use ((:instance ex-vm-runs)
                 (:instance ex-vwf-cwf (flg :m) (i 0) (cm nil) (cm2 nil) (B nil) (lp nil))
                 (:instance ex-cwf-mkok (flg :m) (i 0) (B nil))))))

; ... and a top-level form (N_TOP), whose body anpass marks in its own
; frame (analyze_top's apply_clears): the body's run, in a frame of nils
(defthm ex-top-runs
  (implies (and (consp e) (equal (ex-kind e) 26) (ex-vwf0 :m (ex-c e) 0 nil nil defs) (ex-mkok :m (ex-c e) 0 L n) (equal (len L) n)
                (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs)
                (or (valp (car (ex-ev :m e 0 nil fr fuel))) (thrownp (car (ex-ev :m e 0 nil fr fuel)))) (natp k))
           (equal (vcs2-run-program (ex-tr :m e 0 nil) defs (+ (s2clk (ex-tr :m e 0 nil) nil nil defs fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcs2-run-program s2clk ex-ev ex-tr ex-vwf ex-vwf0 ex-cwf ex-mkok mx2 ex-defs-ok ex-anp-runs)
           :expand ((ex-tr :m e 0 nil) (ex-ev :m e 0 nil fr fuel))
           :use ((:instance ex-anp-runs (e (ex-c e)) (fr (make-list (ex-i2 e) :initial-element nil)))))))

; ---- THE MARKS APPLY_CLEARS MADE ------------------------------------------------------------------
;
; the marked reads of a tree, as anpass's nodes: ex-clr's walk, each
; marked local read its node (ex-ast) where ex-clr has its slot
(defun ex-mks (flg e i)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        nil
      (case flg
        (:do (cond ((zp nk) nil)
                   ((< i (- nk 1)) (append (ex-mks :m (ex-kid-of e i) 0) (ex-mks :do e (1+ i))))
                   (t (ex-mks :m (ex-kid-of e (- nk 1)) 0))))
        (:let (if (< i n2) (append (ex-mks :m (ex-kid-of e i) 0) (ex-mks :let e (1+ i))) (ex-mks :m (ex-kid-of e n2) 0)))
        ((:rec :call :coll) (if (< i nk) (append (ex-mks :m (ex-kid-of e i) 0) (ex-mks flg e (1+ i))) nil))
        (:cs (if (< i (len (ex-c e))) (append (ex-mks :m (ex-cbody e i) 0) (ex-mks :cs e (1+ i))) nil))
        (:ct (if (< i (len (ex-c e))) (append (ex-mks :m (ex-cthen e i) 0) (ex-mks :ct e (1+ i))) nil))
        (:fin (ex-mks :m (ex-kid-of e 1) 0))
        (otherwise
         (cond ((equal k 2) (if (ex-mark e) (list (ex-ast e)) nil))
               ((equal k 4) (append (ex-mks :m (ex-kid-of e 0) 0) (ex-mks :m (ex-kid-of e 1) 0) (ex-mks :m (ex-kid-of e 2) 0)))
               ((equal k 5) (ex-mks :do e 0))
               ((member k '(11 12 13)) (ex-mks :let e 0))
               ((equal k 16) (ex-mks :rec e 0))
               ((equal k 17) (ex-mks :m (ex-kid-of e 0) 0))
               ((equal k 18) (append (ex-mks :m (ex-kid-of e 0) 0) (ex-mks :cs e 0) (ex-mks :fin e 0)))
               ((member k '(7 8 9 22 23 10 20 24 21)) (ex-mks :coll e 0))
               ((equal k 19) (append (ex-mks :m (ex-kid-of e 0) 0) (ex-mks :m (ex-kid-of e 1) 0) (ex-mks :ct e 0)))
               ((equal k 6) (append (ex-mks :m (ex-kid-of e 0) 0) (ex-mks :call e 1)))
               (t nil)))))))
; a tree with no marked read clears nothing
(defthm ex-consp-app (equal (consp (append a b)) (or (consp a) (consp b))))
(defthm ex-mks-clr (equal (consp (ex-clr flg e i)) (consp (ex-mks flg e i)))
  :hints (("Goal" :induct (ex-mks flg e i) :in-theory (e/d ((:definition ex-clr) (:definition ex-mks)) (ex-kid-of ex-astf ex-ast-open))
           :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-mks flg e i))))))
; the marks apply_clears made of a body (anp-clears-spec): none when it
; recurs to its fn, so a body whose marked reads are among them clears nothing
(defun-nx ex-anmk (b n anps)
  (and (natp n) (equal (anp-err (anp-clears (ex-ast b) n anps)) 0)
       (subsetp-equal (ex-mks :m b 0) (mks (anp-clears (ex-ast b) n anps)))))
(defthm ex-anmk-hfr
  (implies (and (ex-anmk b n anps) (anp-hfr 0 (ex-ast b) 0 0)) (atom (ex-clr :m b 0)))
  :hints (("Goal" :in-theory (disable ex-clr ex-mks anp-clears anp-hfr ex-mks-clr ex-astf ex-ast-open)
           :use ((:instance ex-mks-clr (flg :m) (e b) (i 0)) (:instance anp-clears-spec (x (ex-ast b)))))))
(in-theory (disable ex-anmk))

; ---- THE TEMPLATES' BODIES -----------------------------------------------------------------------
;
; ex-defs-ok asks each arity's body well formed after clearing (ex-arwf).
; ex-arwf0 asks it as the analyzer leaves it: well formed before clearing
; (ex-vwf0) in the fn's scope, of anpass's shapes, its marks anpass's
; liveness decision (ex-mkok) and among apply_clears' over the fn's frame
; (ex-anmk), the tail check passed at the fn's tail. A body that recurs to
; its fn then clears nothing (ex-anmk-hfr), as ex-arwf-body wants.
(defun ex-arwf0 (tm ar defs L n anps)
  (and (natp (nth 0 ar)) (natp (nth 2 ar))
       (not (intersectp-equal (ex-inners (nth 2 tm)) (ex-fparams ar)))
       (or (not (natp (nth 4 tm))) (not (member-equal (nth 4 tm) (ex-fparams ar))))
       (ex-vwf0 :m (ex-abody ar) 0 (ex-fcmb tm ar) (ex-flp ar) defs)
       (ex-mkok :m (ex-abody ar) 0 L n) (equal (len L) n)
       (ex-shp :m (ex-abody ar) 0)
       (equal (anp-tc 0 (ex-ast (ex-abody ar)) 0 0 1) 0)
       (ex-anmk (ex-abody ar) n anps)))
(defthm ex-bl-same (ex-bl nil cm cm))
(defthm ex-arwf0-arwf
  (implies (ex-arwf0 tm ar defs L n anps) (ex-arwf tm ar defs))
  :hints (("Goal" :in-theory (disable ex-vwf ex-vwf0 ex-cwf ex-mkok ex-clr ex-vwf-cwf ex-cwf-mkok ex-arwf-body ex-fcmb ex-fcm ex-flp
                                      ex-anmk-hfr anp-hfr)
           :expand ((ex-arwf tm ar defs))
           :use ((:instance ex-vwf-cwf (flg :m) (e (ex-abody ar)) (i 0) (cm (ex-fcmb tm ar)) (cm2 (ex-fcmb tm ar)) (B nil) (lp (ex-flp ar)))
                 (:instance ex-cwf-mkok (flg :m) (e (ex-abody ar)) (i 0) (B nil))
                 (:instance ex-anmk-hfr (b (ex-abody ar)))
                 ex-arwf-body))))
(in-theory (disable ex-arwf0))
; each arity over a live set and a pass of its own
(defun-sk ex-arwf0s (tm ar defs) (exists (L n anps) (ex-arwf0 tm ar defs L n anps)))
(defun ex-arswf0 (tm ars defs) (if (atom ars) t (and (ex-arwf0s tm (car ars) defs) (ex-arswf0 tm (cdr ars) defs))))
(defthm ex-arswf0-arswf (implies (ex-arswf0 tm ars defs) (ex-arswf tm ars defs))
  :hints (("Goal" :induct (ex-arswf0 tm ars defs))
          ("Subgoal *1/2" :use ((:instance ex-arwf0-arwf (ar (car ars)) (L (mv-nth 0 (ex-arwf0s-witness tm (car ars) defs)))
                                           (n (mv-nth 1 (ex-arwf0s-witness tm (car ars) defs)))
                                           (anps (mv-nth 2 (ex-arwf0s-witness tm (car ars) defs))))))))
; every def a template's, each arity's body as the analyzer leaves it
(defun ex-defs-ok0 (ds defs)
  (if (atom ds)
      (null ds)
    (and (consp (car ds)) (equal (cdar ds) (ex-def (caar ds)))
         (nat-listp (ex-inners (nth 2 (caar ds)))) (no-duplicatesp-equal (ex-inners (nth 2 (caar ds))))
         (or (not (natp (nth 4 (caar ds)))) (not (member-equal (nth 4 (caar ds)) (ex-inners (nth 2 (caar ds))))))
         (ex-arswf0 (caar ds) (nth 1 (caar ds)) defs) (ex-defs-ok0 (cdr ds) defs))))
(defthm ex-defs-ok0-ok (implies (ex-defs-ok0 ds defs) (ex-defs-ok ds defs))
  :hints (("Goal" :induct (ex-defs-ok0 ds defs) :in-theory (e/d (ex-tmwf) (ex-def ex-arswf)))))

; END TO END, the templates' bodies too: a tree and its templates as the
; analyzer leaves them run on the VM as on the tree
(defthm ex-anp-runs-defs
  (implies (and (ex-vwf0 :m e 0 nil nil defs) (ex-mkok :m e 0 L n) (equal (len L) n)
                (ex-defs-ok0 defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs)
                (or (valp (car (ex-ev :m e 0 nil fr fuel))) (thrownp (car (ex-ev :m e 0 nil fr fuel)))) (natp k))
           (equal (vcs2-run-program (ex-tr :m e 0 nil) defs (+ (s2clk (ex-tr :m e 0 nil) nil nil defs fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcs2-run-program s2clk ex-ev ex-tr ex-vwf0 ex-mkok ex-defs-ok ex-defs-ok0 ex-anp-runs)
           :use (ex-anp-runs (:instance ex-defs-ok0-ok (ds defs))))))

; THE TREE EVALUATOR'S MEANING IS THE VM'S, first half: the try, case,
; collection, host, top-level and letfn cases (ex-vgood-*), each a lemma of
; its own; exec-vmok.lisp has the old cases and the flag proof.


(in-package "ACL2")

(include-book "exec-vm")

; THE TRY'S CASES, each a lemma of its own (ex-vind's four tips for kind
; 18): the flag proof meets them with ex-vgood still closed, so its
; expansions never see a try
(defthm ex-agree-1 (implies (natp s) (equal (ex-agree (list s) (list v) fr) (equal v (nth s fr)))))
(defmacro ex-tr0 () '(ex-ev :m (ex-kid-of e 0) 0 nil fr fuel))
(defmacro ex-tj () '(cdr (ex-catchw (ex-c e) (val (car (ex-tr0))) 0)))
(defmacro ex-tf1 () '(update-nth (ex-cslot e (ex-tj)) (val (car (ex-tr0))) (cadr (ex-tr0))))
(defmacro ex-th () '(ex-ev :m (ex-cbody e (ex-tj)) 0 nil (ex-tf1) fuel))
(defmacro ex-ttry (&rest hs)
  `(implies (and (consp e) (equal (ex-kind e) 18) (not (member-equal flg '(:iter :do :let :rec :call :fin)))
                 (ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil) ,@hs)
            (ex-vgood flg e i tmp cm env fr fuel caps defs lp)))
(defthm ex-vgood-try-val
  (ex-ttry (valp (car (ex-tr0)))
           (ex-vgood :fin e 0 (list (car (ex-tr0)) (c+ 1 (caddr (ex-tr0)))) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) env (cadr (ex-tr0)) fuel caps defs nil))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))))))
(defthm ex-vgood-try-out
  (ex-ttry (not (valp (car (ex-tr0)))) (not (ex-thp (car (ex-tr0)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))))))
(defthm ex-vgood-try-catch
  (ex-ttry (not (valp (car (ex-tr0)))) (ex-thp (car (ex-tr0))) (equal (car (ex-catchw (ex-c e) (val (car (ex-tr0))) 0)) 1)
           (ex-vgood :m (ex-cbody e (ex-tj)) 0 nil (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list (ex-cslot e (ex-tj))))
                     (append env (list (val (car (ex-tr0))))) (ex-tf1) fuel caps defs nil)
           (ex-vgood :fin e 0 (list (car (ex-th)) (c+ 1 (c+ (caddr (ex-tr0)) (c+ 1 (caddr (ex-th)))))) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) env (cadr (ex-th))
                     fuel caps defs nil))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))))))
(defthm ex-vgood-try-uncaught
  (ex-ttry (not (valp (car (ex-tr0)))) (ex-thp (car (ex-tr0))) (not (equal (car (ex-catchw (ex-c e) (val (car (ex-tr0))) 0)) 1))
           (ex-vgood :fin e 0 (list (car (ex-tr0)) (c+ 1 (caddr (ex-tr0)))) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) env (cadr (ex-tr0)) fuel caps defs nil))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))))))

; THE CASE'S CASES, as the try's: its test's answer not a value, or the
; branch the walk takes
(defmacro ex-tcs (&rest hs)
  `(implies (and (consp e) (equal (ex-kind e) 19) (not (member-equal flg '(:iter :do :let :rec :call :fin)))
                 (ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil) ,@hs)
            (ex-vgood flg e i tmp cm env fr fuel caps defs lp)))
(defthm ex-vgood-case-val
  (ex-tcs (valp (car (ex-tr0)))
          (ex-vgood :m (ex-csbr e (val (car (ex-tr0)))) 0 nil (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append env (list (val (car (ex-tr0)))))
                    (cadr (ex-tr0)) fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :let x) env caps defs fuel))))))
(defthm ex-vgood-case-out
  (ex-tcs (not (valp (car (ex-tr0)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :let x) env caps defs fuel))))))
(defthm ex-vgood-case
  (ex-tcs (ex-vgood :m (ex-csbr e (val (car (ex-tr0)))) 0 nil (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append env (list (val (car (ex-tr0)))))
                    (cadr (ex-tr0)) fuel caps defs lp))
  :hints (("Goal" :do-not-induct t :in-theory (disable ex-vgood ex-vgood-case-val ex-vgood-case-out ex-kid-of ex-ev)
                  :use (ex-vgood-case-val ex-vgood-case-out))))
(in-theory (disable ex-vgood-case-val ex-vgood-case-out))

; THE COLLECTION'S CASES: the node's record opened, each element, the build
(defthm ex-vgood-m-coll
  (implies (and (consp e) (member-equal (ex-kind e) '(7 8 9)) (not (member-equal flg '(:iter :do :let :rec :call :coll :fin)))
                (ex-vgood :coll e 0 nil cm env fr fuel caps defs nil))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
; NEW (milestone 5): its arguments a collection's elements, the build (prim (:host k C))
(defthm ex-vgood-m-new
  (implies (and (consp e) (member-equal (ex-kind e) '(22 23)) (not (member-equal flg '(:iter :do :let :rec :call :coll :fin)))
                (ex-vgood :coll e 0 nil cm env fr fuel caps defs nil))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
; THE HOST'S ACTIONS (milestone 5: def, deftype, set!): their children a
; collection's elements, the action (prim (:host k C)) -- ex-collok's hypothesis
(defthm ex-vgood-m-host
  (implies (and (consp e) (member-equal (ex-kind e) '(10 20 24 21)) (not (member-equal flg '(:iter :do :let :rec :call :coll :fin)))
                (ex-vgood :coll e 0 nil cm env fr fuel caps defs nil))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
; A LAZY SEQ (milestone 5, N_LAZY 15): its closure, as a fn's, wrapped by
; the host (prim (:host 15 C)) -- ex-collok's hypothesis
(defthm ex-vgood-m-lazy
  (implies (and (consp e) (equal (ex-kind e) 15) (not (member-equal flg '(:iter :do :let :rec :call :coll :fin))))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
; A TOP-LEVEL FORM (milestone 5, N_TOP 26): its body in a frame of nils, in
; the scope blanked -- no outer name reaches it -- and the frame below back
(defun ex-ind2 (cm env) (if (atom cm) env (ex-ind2 (cdr cm) (cdr env))))
(defthm ex-agree-blank-sub
  (implies (and (subsetp-equal cm ls) (equal (len env) (len cm))) (ex-agree (ex-blank ls cm) env fr))
  :hints (("Goal" :induct (ex-ind2 cm env) :in-theory (enable ex-agree ex-blank))))
(defthm ex-sub-self-cons (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm ex-sub-self (subsetp-equal a a))
(defthm ex-agree-blank-self (implies (equal (len env) (len cm)) (ex-agree (ex-blank cm cm) env fr)))
(defthm ex-vgood-m-top
  (implies (and (consp e) (equal (ex-kind e) 26) (not (member-equal flg '(:iter :do :let :rec :call :coll :fin)))
                (ex-vgood :m (ex-c e) 0 nil (ex-blank cm cm) env (make-list (ex-i2 e) :initial-element nil) fuel caps defs nil))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr ex-blank))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))))))
; LETFN (milestone 5): the body's case, in the scope its lets make and the
; sealed frame (exec-vmlf's ex-lf-facts)
(defthm ex-agree-app-atom
  (implies (atom b) (equal (ex-agree (append a b) env fr) (ex-agree a env fr)))
  :hints (("Goal" :induct (ex-agree a env fr))))
; the body's scope cut back to the letfn's: its env, the empty letfn's as
; the others' (exec-vmlf's ex-lfenv)
(defthm ex-agree-lfenv
  (implies (and (equal (len a) (len env)) (equal (len b) (ex-i2 e)))
           (equal (ex-agree (append a b) (ex-lfenv e env fr) fr2)
                  (and (ex-agree a env fr2) (or (zp (ex-i2 e)) (ex-agree b (ex-lfsv e 0 fr (ex-lfg e 0 fr nil)) fr2)))))
  :hints (("Goal" :in-theory (e/d (ex-lfenv) (ex-agree ex-lfsv ex-lfg)) :cases ((zp (ex-i2 e))))))
(defthm ex-vgood-m-letfn
  (implies (and (consp e) (not (member-equal flg '(:iter :do :let :rec :call :coll :fin))) (equal (ex-kind e) 13)
                (ex-vgood :m (ex-kid-of e (ex-i2 e)) 0 nil (append cm (ex-slots (ex-s2 e) (ex-i2 e))) (ex-lfenv e env fr)
                          (ex-write (ex-s2 e) (ex-lfsv e 0 fr (ex-lfg e 0 fr nil)) (ex-lfr e 0 fr)) fuel caps defs lp))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-agree ex-vwf ex-ev ex-tr ex-clr ex-lfsv ex-lfg ex-lfr ex-write ex-lsl))
                  :use ((:instance ex-lf-facts (caps caps) (d2 defs))))))
(defthm ex-vgood-coll-mid
  (implies (and (equal flg :coll) (consp e) (< (nfix i) (ex-nk e))
                (ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
                (ex-vgood :coll e (+ 1 (nfix i)) (append tmp (list (val (car (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel))))) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) env
                          (cadr (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)) fuel caps defs lp))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
(defthm ex-vgood-coll-end
  (implies (and (equal flg :coll) (consp e) (not (< (nfix i) (ex-nk e))))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-agree ex-vwf ex-ev ex-tr ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (:free (flg) (ex-ev flg e i tmp fr fuel)) (:free (flg) (ex-tr flg e i cm)) (:free (flg) (ex-vwf flg e i cm lp defs))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))


; THE TREE EVALUATOR'S MEANING IS THE VM'S, the cases and the theorem
; (exec-vm.lisp's, split from it for size): each kind's case a lemma of
; its own, then the flag proof by ex-vind, ex-vm-agree and
; ex-recur-stays. exec-vm.lisp's header says what they state.

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

; THE OLD CASES, each a lemma of its own (ex-vind's tips for the atom,
; :iter, :do, :let, :rec, :call, :fin and kinds 4, 5, 6, 11/12, 16, 17 and
; the rest at :m), proved as the flag proof once proved them all -- ex-vgood
; opened only once stable -- and disabled until the flag proof, which meets
; them with ex-vgood closed, so its induction never expands a case
(defmacro ex-old (name conds hyps &optional use)
  `(progn
     (defthm ,name
       (implies (and ,@conds ,@hyps) (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
       :hints (("Goal" :do-not-induct t :in-theory (disable ex-vgood ex-kid-of ex-xvs ex-catchw ex-csbr ex-cbuild) :use ,use)
               (and stable-under-simplificationp
                '(:in-theory (e/d (ex-vgood) (ex-kid-of ex-xvs ex-catchw ex-clr))
                  :expand ((:free (flg) (ex-clr flg e i)) (ex-clr :fin e 0) (:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp defs))
                           (:free (flg fr tmp) (ex-ev flg e i tmp fr fuel))
                           (:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :let x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :const x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :loop x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :recur x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :throw x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))
                           (:free (x base vs) (mx2-loop (list :loop nil x) base vs caps defs fuel)))))))
     (in-theory (disable ,name))))
(defmacro ex-r0 () '(ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel))
(defmacro ex-k0 () '(ex-ev :m (ex-kid-of e 0) 0 nil fr fuel))
(defmacro ex-mflg () '(not (member-equal flg '(:iter :do :let :rec :call :coll :fin))))

(ex-old ex-vgood-atom ((not (consp e))) ())
(ex-old ex-vgood-iter-zp ((consp e) (equal flg :iter) (zp fuel))
        ((ex-vgood :m e 0 nil (append cm (ex-lsl lp)) (append env tmp) fr fuel caps defs lp)))
(ex-old ex-vgood-iter ((consp e) (equal flg :iter) (not (zp fuel)))
        ((ex-vgood :m e 0 nil (append cm (ex-lsl lp)) (append env tmp) fr fuel caps defs lp)
         (ex-vgood :m e 0 nil (append cm (ex-lsl lp)) (append env tmp) fr fuel caps defs nil)
         (ex-vgood :iter e 0 (cdr (mx2 (ex-tr :m e 0 (append cm (ex-lsl lp))) (append env tmp) caps defs fuel)) cm env
                   (cadr (ex-ev :m e 0 nil fr fuel)) (1- fuel) caps defs lp)))
(ex-old ex-vgood-do-none ((consp e) (equal flg :do) (zp (ex-nk e))) ())
(ex-old ex-vgood-do-mid ((consp e) (equal flg :do) (not (zp (ex-nk e))) (< (nfix i) (- (ex-nk e) 1)))
        ((ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :do e (1+ (nfix i)) tmp (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) env (cadr (ex-r0)) fuel caps defs lp)))
(ex-old ex-vgood-do-last ((consp e) (equal flg :do) (not (zp (ex-nk e))) (not (< (nfix i) (- (ex-nk e) 1))))
        ((ex-vgood :m (ex-kid-of e (- (ex-nk e) 1)) 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-let-mid ((consp e) (equal flg :let) (< (nfix i) (ex-i2 e)))
        ((ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :let e (1+ (nfix i)) tmp (append (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) (list (+ (ex-s2 e) (nfix i)))) (append env (list (val (car (ex-r0)))))
                   (update-nth (+ (ex-s2 e) (nfix i)) (val (car (ex-r0))) (cadr (ex-r0))) fuel caps defs lp)))
(ex-old ex-vgood-let-loop ((consp e) (equal flg :let) (not (< (nfix i) (ex-i2 e))) (equal (ex-kind e) 12))
        ((ex-vgood :iter (ex-kid-of e (ex-i2 e)) 0
                   (cons nil (val (mx2-args (ex-locals (cdr (cons nil (ex-slots (ex-s2 e) (ex-i2 e)))) cm) env caps defs fuel)))
                   (ex-blank (cons nil (ex-slots (ex-s2 e) (ex-i2 e))) cm) env fr fuel caps defs (cons (ex-s2 e) (ex-i2 e)))))
(ex-old ex-vgood-let-body ((consp e) (equal flg :let) (not (< (nfix i) (ex-i2 e))) (not (equal (ex-kind e) 12)))
        ((ex-vgood :m (ex-kid-of e (ex-i2 e)) 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-rec-mid ((consp e) (equal flg :rec) (< (nfix i) (ex-nk e)))
        ((ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :rec e (1+ (nfix i)) (append tmp (list (val (car (ex-r0))))) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) env (cadr (ex-r0)) fuel caps defs lp)))
(ex-old ex-vgood-rec-end ((consp e) (equal flg :rec) (not (< (nfix i) (ex-nk e)))) ())
(ex-old ex-vgood-call-mid ((consp e) (equal flg :call) (< (nfix i) (ex-nk e)))
        ((ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :call e (1+ (nfix i)) (append tmp (list (val (car (ex-r0))))) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) env (cadr (ex-r0)) fuel caps defs lp)))
(ex-old ex-vgood-call-zp ((consp e) (equal flg :call) (not (< (nfix i) (ex-nk e))) (zp fuel)) ())
(ex-old ex-vgood-call-enter ((consp e) (equal flg :call) (not (< (nfix i) (ex-nk e))) (not (zp fuel)))
        ((ex-vgood :iter (ex-fbody (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) 0
                   (cons nil (ex-fvs (car (ex-callee tmp)) (cdr (ex-callee tmp))))
                   (ex-fcm (ex-ftm (car (ex-callee tmp))) (ex-car (car (ex-callee tmp)) (cdr (ex-callee tmp))))
                   (ex-fenv (car (ex-callee tmp)) (cdr (ex-callee tmp))) (ex-bind (car (ex-callee tmp)) (cdr (ex-callee tmp)))
                   (1- fuel) (caddr (car (ex-callee tmp))) defs
                   (cons (ex-astart (ex-car (car (ex-callee tmp)) (cdr (ex-callee tmp))))
                         (ex-anp (ex-car (car (ex-callee tmp)) (cdr (ex-callee tmp)))))))
        ((:instance ex-call-iterok (tmp (ex-callee tmp)))))
(ex-old ex-vgood-fin ((consp e) (equal flg :fin) (< 1 (ex-nk e)))
        ((ex-vgood :m (ex-kid-of e 1) 0 nil (append cm (list nil)) (append env (list (val (car tmp)))) fr fuel caps defs nil)))
(ex-old ex-vgood-fin-end ((consp e) (equal flg :fin) (not (< 1 (ex-nk e)))) ())
; an if, by its test's answer: no value, then, else, or nil
(ex-old ex-vgood-if-out ((consp e) (ex-mflg) (equal (ex-kind e) 4) (not (valp (car (ex-k0))))) ((ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)))
(ex-old ex-vgood-if-then ((consp e) (ex-mflg) (equal (ex-kind e) 4) (valp (car (ex-k0))) (truthy (val (car (ex-k0))))) ((ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :m (ex-kid-of e 1) 0 nil (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) env (cadr (ex-k0)) fuel caps defs lp)))
(ex-old ex-vgood-if-else ((consp e) (ex-mflg) (equal (ex-kind e) 4) (valp (car (ex-k0))) (not (truthy (val (car (ex-k0))))) (< 2 (ex-nk e))) ((ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :m (ex-kid-of e 2) 0 nil (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) env (cadr (ex-k0)) fuel caps defs lp)))
(ex-old ex-vgood-if-nil ((consp e) (ex-mflg) (equal (ex-kind e) 4) (valp (car (ex-k0))) (not (truthy (val (car (ex-k0))))) (not (< 2 (ex-nk e)))) ((ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)))
(defthm ex-vgood-m-if
  (implies (and (consp e) (ex-mflg) (equal (ex-kind e) 4) (ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                (ex-vgood :m (ex-kid-of e 1) 0 nil (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) env (cadr (ex-k0)) fuel caps defs lp)
                (ex-vgood :m (ex-kid-of e 2) 0 nil (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) env (cadr (ex-k0)) fuel caps defs lp))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t :in-theory (disable ex-vgood ex-kid-of ex-ev truthy valp val)
                  :use (ex-vgood-if-out ex-vgood-if-then ex-vgood-if-else ex-vgood-if-nil))))
(in-theory (disable ex-vgood-m-if))
(ex-old ex-vgood-m-do ((consp e) (ex-mflg) (equal (ex-kind e) 5)) ((ex-vgood :do e 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-m-let ((consp e) (ex-mflg) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)))
        ((ex-vgood :let e 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-m-rec ((consp e) (ex-mflg) (equal (ex-kind e) 16)) ((ex-vgood :rec e 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-m-throw ((consp e) (ex-mflg) (equal (ex-kind e) 17)) ((ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)))
(ex-old ex-vgood-m-call ((consp e) (ex-mflg) (equal (ex-kind e) 6))
        ((ex-vgood :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :call e 1 (list (val (car (ex-k0)))) (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append env (list (val (car (ex-k0)))))
                   (cadr (ex-k0)) fuel caps defs lp)))
(ex-old ex-vgood-leaf-plain ((consp e) (ex-mflg) (not (member-equal (ex-kind e) '(4 5 6 7 8 9 11 12 13 16 17 18 19 22 23 10 20 24 21 15 26)))
                         (not (and (equal (ex-kind e) 2) (ex-mark e)))) ())
; a marked read (milestone 4): its slot cleared, blanked in the scope after
(ex-old ex-vgood-m-mark ((consp e) (ex-mflg) (equal (ex-kind e) 2) (ex-mark e)) ())
(defthm ex-vgood-m-leaf
  (implies (and (consp e) (ex-mflg) (not (member-equal (ex-kind e) (quote (4 5 6 7 8 9 11 12 13 16 17 18 19 22 23 10 20 24 21 26)))))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t :in-theory (disable ex-vgood ex-kid-of) :use (ex-vgood-leaf-plain ex-vgood-m-mark ex-vgood-m-lazy))))
(in-theory (disable ex-vgood-m-leaf))
(in-theory (enable ex-vgood-atom ex-vgood-iter-zp ex-vgood-iter ex-vgood-do-none ex-vgood-do-mid ex-vgood-do-last
                   ex-vgood-let-mid ex-vgood-let-loop ex-vgood-let-body ex-vgood-rec-mid ex-vgood-rec-end
                   ex-vgood-call-mid ex-vgood-call-zp ex-vgood-call-enter ex-vgood-fin ex-vgood-fin-end
                   ex-vgood-m-if ex-vgood-m-lazy ex-vgood-m-top ex-vgood-m-do ex-vgood-m-let ex-vgood-m-rec ex-vgood-m-throw ex-vgood-m-call ex-vgood-m-leaf
                   ex-vgood-m-mark))

(defthm ex-vm-agree-flag
  (ex-vgood flg e i tmp cm env fr fuel caps defs lp)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vind flg e i tmp cm env fr fuel caps defs lp)
                  :in-theory (disable ex-vgood ex-kid-of ex-xvs ex-catchw ex-csbr ex-cbuild))))

; A WELL-FORMED TREE ANSWERS WHAT THE VM'S MEANING DOES, its defs the
; templates' and its scope's values good
(defthm ex-vm-agree
  (implies (and (ex-vwf :m e 0 cm nil defs) (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs) (ex-agree cm env fr)
                (ex-xvs defs env) (or (valp (car (ex-ev :m e 0 nil fr fuel))) (thrownp (car (ex-ev :m e 0 nil fr fuel)))))
           (equal (mx2 (ex-tr :m e 0 cm) env caps defs fuel) (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

; ... and outside every loop's tail it never answers a recur: a recur's
; values become its loop's slots, never a value
(defthm ex-recur-stays
  (implies (and (ex-vwf :m e 0 cm nil defs) (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs) (ex-agree cm env fr)
                (ex-xvs defs env))
           (not (equal (car (car (ex-ev :m e 0 nil fr fuel))) :recur)))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

; THE TREE EVALUATOR'S MEANING IS THE VM'S, the cases and the theorem
; (exec-vm.lisp's, split from it for size): each kind's case a lemma of
; its own, then the flag proof by ex-vind, ex-vm-agree and
; ex-recur-stays. exec-vm.lisp's header says what they state.
; Second half: the old cases and the flag proof (the first half, the try, case,
; collection, top, letfn cases, is exec-vmok1.lisp, split for certification time).

(in-package "ACL2")

(include-book "exec-vmok1")
(in-theory (disable ex-vgood-case-val ex-vgood-case-out))

; THE OLD CASES, each a lemma of its own (ex-vind's tips for the atom,
; :iter, :do, :let, :rec, :call, :fin and kinds 4, 5, 6, 11/12, 16, 17 and
; the rest at :m), proved as the flag proof once proved them all -- ex-vgood
; opened only once stable -- and disabled until the flag proof, which meets
; them with ex-vgood closed, so its induction never expands a case
; a loop of no bindings: its scope and values cm ++ nil, env ++ nil
(defthm ex-agree-app-nil-env (equal (ex-agree cm (append env nil) fr) (ex-agree cm env fr)))
(defthm ex-agree-app-nil-cm (equal (ex-agree (append cm nil) env fr) (ex-agree cm env fr)))
(defthm ex-nomem-nil (ex-nomem nil cm))
; ex-mx-loop-body for a loop whose inits may be none
(defthm ex-mx-loop-body0
  (implies (and (consp e) (syntaxp (not (and (consp e) (eq (car e) 'cons) (consp (caddr e)) (equal (cadr (caddr e)) ''nil)))))
           (equal (mx2-loop e base vs caps defs fuel) (mx2-loop (list :loop nil (caddr e)) base vs caps defs fuel)))
  :hints (("Goal" :induct (ex-mxl-ind e base vs caps defs fuel)
                  :expand ((mx2-loop e base vs caps defs fuel)
                           (:free (vs) (mx2-loop (list :loop nil (caddr e)) base vs caps defs fuel))))))

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
         (ex-vgood :do e (1+ (nfix i)) tmp (append (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) (list nil)) (append env (list (val (car (ex-r0))))) (cadr (ex-r0)) fuel caps defs lp)))
(ex-old ex-vgood-do-last ((consp e) (equal flg :do) (not (zp (ex-nk e))) (not (< (nfix i) (- (ex-nk e) 1))))
        ((ex-vgood :m (ex-kid-of e (- (ex-nk e) 1)) 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-let-mid ((consp e) (equal flg :let) (< (nfix i) (ex-i2 e)) (not (and (equal (ex-kind e) 12) (ex-lind e 1))))
        ((ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :let e (1+ (nfix i)) tmp (append (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) (list (+ (ex-s2 e) (nfix i)))) (append env (list (val (car (ex-r0)))))
                   (update-nth (+ (ex-s2 e) (nfix i)) (val (car (ex-r0))) (cadr (ex-r0))) fuel caps defs lp)))
(ex-old ex-vgood-let-loop ((consp e) (equal flg :let) (not (< (nfix i) (ex-i2 e))) (equal (ex-kind e) 12) (not (ex-lind e 1)))
        ((ex-vgood :iter (ex-kid-of e (ex-i2 e)) 0
                   (val (mx2-args (ex-locals (ex-slots (ex-s2 e) (ex-i2 e)) cm) env caps defs fuel))
                   (ex-blank (ex-slots (ex-s2 e) (ex-i2 e)) cm) env fr fuel caps defs (cons (ex-s2 e) (ex-i2 e)))))
;; the loop's slots so far, one more (moved here from exec-clrvm)
(defthm ex-slots-snoc-n
  (implies (and (natp s) (natp i)) (equal (ex-slots s (1+ i)) (append (ex-slots s i) (list (+ s i)))))
  :hints (("Goal" :induct (ex-slots s i) :in-theory (enable ex-slots) :expand ((ex-slots s (1+ i)) (ex-slots s 1)))))
(defthm ex-slots-snoc
  (implies (natp s) (equal (ex-slots s (1+ (nfix i))) (append (ex-slots s (nfix i)) (list (+ s (nfix i))))))
  :hints (("Goal" :use ((:instance ex-slots-snoc-n (i (nfix i)))) :in-theory (disable ex-slots-snoc-n))))
(defthm ex-mem-slots-iff
  (iff (member-equal x (ex-slots s n)) (and (natp x) (<= (nfix s) x) (< x (+ (nfix s) (nfix n)))))
  :hints (("Goal" :induct (ex-slots s n) :in-theory (enable ex-slots))))
(defun ex-sl2-ind (s i n) (if (zp i) (list s n) (ex-sl2-ind (1+ (nfix s)) (1- i) (1- n))))
(defthm ex-nomem-slots-less
  (implies (and (ex-nomem c (ex-slots s n)) (<= (nfix i) (nfix n))) (ex-nomem c (ex-slots s i)))
  :hints (("Goal" :induct (ex-sl2-ind s i n) :in-theory (disable ex-slots-snoc ex-slots-snoc-n) :expand ((ex-slots s i) (ex-slots s n)))))
(defthm ex-agree-slots-snoc
  (implies (and (natp s) (natp i) (ex-agree (ex-slots s i) tmp fr))
           (ex-agree (ex-slots s (1+ i)) (append tmp (list v)) (update-nth (+ s i) v fr))))
; a let's walk reads no tmp; the end of one asks only its body's clears
(defun ex-evl-ind (e i fr fuel)
  (declare (irrelevant fr fuel))
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix i)))))
  (if (< (nfix i) (ex-i2 e))
      (let ((r (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel))) (ex-evl-ind e (1+ (nfix i)) (update-nth (+ (ex-s2 e) (nfix i)) (val (car r)) (cadr r)) fuel))
    t))
(defthm ex-ev-let-tmp
  (implies (syntaxp (not (equal tmp ''nil))) (equal (ex-ev :let e i tmp fr fuel) (ex-ev :let e i nil fr fuel)))
  :hints (("Goal" :induct (ex-evl-ind e i fr fuel) :in-theory (disable ex-kid-of) :expand ((ex-ev :let e i tmp fr fuel) (ex-ev :let e i nil fr fuel)))))
(defthm ex-clr-let-end
  (implies (not (< (nfix i) (ex-i2 e))) (equal (ex-clr :let e i) (if (consp e) (ex-clr :m (ex-kid-of e (ex-i2 e)) 0) (ex-clr :let e i))))
  :hints (("Goal" :expand ((ex-clr :let e i)))))
(defthm ex-clr-let-mid
  (implies (and (consp e) (< (nfix i) (ex-i2 e)))
           (equal (ex-clr :let e i) (append (ex-clr :m (ex-kid-of e (nfix i)) 0) (ex-clr :let e (1+ (nfix i))))))
  :hints (("Goal" :expand ((ex-clr :let e i)))))
(defthm ex-blank-swap (equal (ex-blank (append b a) cm) (ex-blank (append a b) cm)) :rule-classes nil)
(defthm ex-agree-blank-swap
  (implies (ex-agree (ex-blank (append a b) cm) env fr) (ex-agree (ex-blank (append b a) cm) env fr))
  :hints (("Goal" :use ex-blank-swap)))
; an independent-inits loop (exec-PLAN Lane 3 item 3(a)): each init in the
; outer scope and again beside the loop's slots so far, then the loop on them all
(ex-old ex-vgood-let-imid ((consp e) (equal flg :let) (< (nfix i) (ex-i2 e)) (equal (ex-kind e) 12) (ex-lind e 1))
        ((ex-vgood :m (ex-kid-of e (nfix i)) 0 nil cm env fr fuel caps defs nil)
         (ex-vgood :m (ex-kid-of e (nfix i)) 0 nil (append cm (ex-slots (ex-s2 e) (nfix i))) (append env tmp) fr fuel caps defs nil)
         (ex-vgood :let e (1+ (nfix i)) (append tmp (list (val (car (ex-r0))))) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm) env
                   (update-nth (+ (ex-s2 e) (nfix i)) (val (car (ex-r0))) (cadr (ex-r0))) fuel caps defs lp)))
(ex-old ex-vgood-let-iend ((consp e) (equal flg :let) (not (< (nfix i) (ex-i2 e))) (equal (ex-kind e) 12) (ex-lind e 1))
        ((ex-vgood :iter (ex-kid-of e (ex-i2 e)) 0 tmp (ex-blank (ex-slots (ex-s2 e) (ex-i2 e)) cm) env fr fuel caps defs (cons (ex-s2 e) (ex-i2 e)))))
(in-theory (disable ex-clr-let-mid ex-clr-let-end ex-ev-let-tmp))
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
                   (ex-fvs (car (ex-callee tmp)) (cdr (ex-callee tmp)))
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
(ex-old ex-vgood-m-let0 ((consp e) (ex-mflg) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (not (and (equal (ex-kind e) 12) (ex-lind e 1))))
        ((ex-vgood :let e 0 nil cm env fr fuel caps defs lp)))
(ex-old ex-vgood-m-ilet ((consp e) (ex-mflg) (equal (ex-kind e) 12) (ex-lind e 1))
        ((ex-vgood :let e 0 nil cm env fr fuel caps defs lp)))
(defthm ex-vgood-m-let
  (implies (and (consp e) (ex-mflg) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12)) (ex-vgood :let e 0 nil cm env fr fuel caps defs lp))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t :in-theory (disable ex-vgood ex-kid-of ex-lind) :use (ex-vgood-m-let0 ex-vgood-m-ilet))))
(in-theory (disable ex-vgood-m-let))
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
                   ex-vgood-let-mid ex-vgood-let-loop ex-vgood-let-imid ex-vgood-let-iend ex-vgood-let-body ex-vgood-rec-mid ex-vgood-rec-end
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

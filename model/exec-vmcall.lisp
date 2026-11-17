; FNS AND CALLS IN THE TRANSLATION (model/exec-vm.lisp's second part):
; a closure's def, an arity's entry and a call's dispatch, as mx2 runs
; them, for ex-vm-agree. Split from exec-vm.lisp for size.

(in-package "ACL2")

(include-book "exec-vmtr")

; ---- VALUES, FNS AND CALLS ------------------------------------------------------------------------

(defthm ex-xvs-cons (implies (syntaxp (not (equal b ''nil)))
                             (equal (ex-xvs defs (cons a b)) (and (ex-xvs defs (list a)) (ex-xvs defs b))))
  :hints (("Goal" :expand ((ex-xvs defs (cons a b)) (ex-xvs defs (list a))))))
(defthm ex-xvs-nth (implies (ex-xvs defs l) (ex-xvs defs (list (nth j l)))))
(defthm ex-xvs-fr
  (implies (and (ex-agree cm env fr) (member-equal s cm) (natp s) (ex-xvs defs env))
           (ex-xvs defs (list (nth s fr))))
  :hints (("Goal" :in-theory (disable ex-xvs ex-agree-local)
                  :use ((:instance ex-xvs-nth (j (ex-pos s cm)) (l env)) ex-agree-local))))
(defthm ex-locals-valp (equal (car (mx2-args (ex-locals ls cm) env caps defs fuel)) :val)
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :local x) env caps defs fuel))))))
(defthm ex-xvs-locals
  (implies (ex-xvs defs env) (ex-xvs defs (cdr (mx2-args (ex-locals ls cm) env caps d2 fuel))))
  :hints (("Goal" :induct (ex-locals ls cm) :in-theory (disable ex-xvs)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps d2 fuel))
                           (:free (x) (mx2 (cons :local x) env caps d2 fuel))
                           (ex-xvs defs nil)))))
(defthm ex-locals-indep
  (implies (syntaxp (not (and (equal caps ''nil) (equal defs ''nil) (equal fuel ''0))))
           (equal (mx2-args (ex-locals ls cm) env caps defs fuel) (mx2-args (ex-locals ls cm) env nil nil 0)))
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y caps defs fuel) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x caps defs fuel) (mx2 (cons :local x) env caps defs fuel))))))

(defthm ex-len-caps (equal (len (ex-caps capv fr)) (len (ex-inners capv))))
(defthm ex-true-listp-caps (true-listp (ex-caps capv fr)))
(defthm ex-caps-mx
  (implies (and (ex-agree cm env fr) (subsetp-equal (ex-outers capv) cm) (nat-listp (ex-outers capv)))
           (equal (mx2-args (ex-locals (ex-outers capv) cm) env caps defs fuel) (cons :val (ex-caps capv fr))))
  :hints (("Goal" :induct (ex-caps capv fr)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :local x) env caps defs fuel))))))
(defthm ex-xvs-caps
  (implies (and (ex-agree cm env fr) (subsetp-equal (ex-outers capv) cm) (nat-listp (ex-outers capv)) (ex-xvs defs env))
           (ex-xvs defs (ex-caps capv fr)))
  :hints (("Goal" :induct (ex-caps capv fr))))

; the frame a call binds
(defthm ex-nth-bind-caps
  (implies (and (natp j) (not (member-equal j (ex-inners capv))) (nat-listp (ex-inners capv)))
           (equal (nth j (ex-bind-caps capv caps fr)) (nth j fr))))
(defthm ex-agree-bind-caps-other
  (implies (and (nat-listp (ex-inners capv)) (not (intersectp-equal (ex-inners capv) cm)))
           (equal (ex-agree cm env (ex-bind-caps capv caps fr)) (ex-agree cm env fr))))
(defthm ex-agree-bind-caps
  (implies (and (nat-listp (ex-inners capv)) (no-duplicatesp-equal (ex-inners capv))
                (equal (len caps) (len (ex-inners capv))))
           (ex-agree (ex-inners capv) caps (ex-bind-caps capv caps fr)))
  :hints (("Goal" :induct (ex-bind-caps capv caps fr))))

; the arity a call picks (ex-arity, its fixed pass then its variadic one)
; and the clause mx2's pick-arity picks are one
(defthm ex-arity-pass-consp (implies (ex-arity-pass ars n p) (consp (ex-arity-pass ars n p))))
(defthm ex-arity-pass0
  (implies (ex-arity-pass ars n 0)
           (and (not (truthy (nth 1 (ex-arity-pass ars n 0)))) (equal (nth 0 (ex-arity-pass ars n 0)) n))))
(defthm ex-arity-pass1
  (implies (ex-arity-pass ars n 1)
           (and (truthy (nth 1 (ex-arity-pass ars n 1))) (natp (nth 0 (ex-arity-pass ars n 1)))
                (<= (nth 0 (ex-arity-pass ars n 1)) n)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (ex-arity-pass ars n 1) (<= (nth 0 (ex-arity-pass ars n 1)) n)))))
(defthm ex-arwf-nat
  (implies (ex-arwf tm ar defs) (and (natp (car ar)) (natp (caddr ar))))
  :rule-classes :forward-chaining)
(defthm ex-arswf-cons
  (equal (ex-arswf tm (cons a ars) defs) (and (ex-arwf tm a defs) (ex-arswf tm ars defs))))
(in-theory (disable ex-arwf))
(defthm ex-arswf-pass
  (implies (and (ex-arswf tm ars defs) (ex-arity-pass ars n p)) (ex-arwf tm (ex-arity-pass ars n p) defs))
  :hints (("Goal" :induct (ex-arity-pass ars n p))))
(defthm ex-arswf-arity
  (implies (and (ex-arswf tm ars defs) (ex-arity ars n)) (ex-arwf tm (ex-arity ars n) defs)))
(defthm ex-pick-fixed
  (implies (and (ex-arswf tm ars defs) (natp m))
           (equal (pick-fixed (ex-clauses tm ars) m)
                  (if (ex-arity-pass ars m 0) (ex-clause tm (ex-arity-pass ars m 0)) nil)))
  :hints (("Goal" :in-theory (e/d (ex-anf ex-avar) (ex-fbtr ex-fbtc)))))
(defthm ex-pick-rest
  (implies (and (ex-arswf tm ars defs) (natp m))
           (equal (pick-rest (ex-clauses tm ars) m)
                  (if (ex-arity-pass ars m 1) (ex-clause tm (ex-arity-pass ars m 1)) nil)))
  :hints (("Goal" :in-theory (e/d (ex-anf ex-avar) (ex-fbtr ex-fbtc)))))
(defthm ex-pick-arity
  (implies (and (ex-arswf tm ars defs) (natp m))
           (equal (pick-arity (ex-clauses tm ars) m) (if (ex-arity ars m) (ex-clause tm (ex-arity ars m)) nil)))
  :hints (("Goal" :in-theory (disable ex-clause ex-clauses ex-arswf))))
(defthm ex-split-rest (equal (split-rest n vs) (ex-rest-args n vs)) :hints (("Goal" :in-theory (enable split-rest ex-rest-args))))

; a variadic call's locals: as many as its parameters, good when the
; arguments are (the rest list of good values is never closure-shaped)
(defthm ex-len-take (equal (len (take n l)) (nfix n)))
(defthm ex-len-bargs
  (implies (and (ex-arity ars (len args)) (true-listp args))
           (equal (len (ex-bargs (ex-arity ars (len args)) args)) (ex-anp (ex-arity ars (len args)))))
  :hints (("Goal" :in-theory (e/d (ex-anp ex-anf ex-avar ex-bargs ex-rest-args) (ex-arity-pass))
                  :cases ((ex-arity-pass ars (len args) 0)))))
(defthm ex-true-listp-bargs (implies (true-listp args) (true-listp (ex-bargs ar args)))
  :hints (("Goal" :in-theory (enable ex-bargs ex-rest-args))))
(defthm ex-xvs-nthcdr (implies (and (ex-xvs defs l) (true-listp l)) (ex-xvs defs (list (nthcdr n l))))
  :hints (("Goal" :induct (nthcdr n l) :expand ((ex-xvs defs l) (:free (a) (ex-xvs defs (list a)))))))
(defthm ex-xvs-bargs (implies (and (ex-xvs defs args) (true-listp args)) (ex-xvs defs (ex-bargs ar args)))
  :hints (("Goal" :in-theory (enable ex-bargs ex-rest-args))))

(defthm ex-defs-ok-assoc
  (implies (and (ex-defs-ok ds defs) (consp (assoc-equal tm ds)))
           (and (equal (cdr (assoc-equal tm ds)) (ex-def tm)) (ex-tmwf tm defs))))
(defthm ex-defs-ok-alistp (implies (ex-defs-ok ds defs) (alistp ds)))

; a callee's mx2: :callv past its head and arguments, and :applyv's, past
; apply's spread
(defun ex-mxcl (f args cls defs fuel)
  (if (not (clop f))
      (let ((a (prim :invoke (cons f args)))) (if (throwp a) (cons :thrown (cdr a)) (cons :val a)))
    (let ((cl (pick-arity cls (len args))))
      (cond ((not (consp cl)) (cons :thrown :arity))
            ((zp fuel) (list :out))
            (t (mx2 (cadr cl) (if (restp cl) (split-rest (nfix (car cl)) args) args) (clo-caps f) defs (1- fuel)))))))
; the clauses a callee dispatches in: its template's def, or for apply's
; hand-over (ex-hclo) the variadic clause of the closure it stands for as
; the fixed one of req + 1 (vmx2's x2-hcls)
(defun ex-mxcls (f defs)
  (if (equal (ex-self f) f) (cdr (assoc-equal (clo-f f) defs)) (x2-hcls (cdr (assoc-equal (clo-f (ex-self f)) defs)))))
(defun ex-mxcall0 (f args defs fuel) (ex-mxcl f args (ex-mxcls f defs) defs fuel))
(defun ex-mxcall (f args defs fuel)
  (let ((c (x2-fn :applyv f args defs)))
    (ex-mxcl c (x2-vals :applyv f args defs) (x2-cls :applyv f args defs (cdr (assoc-equal (clo-f c) defs))) defs fuel)))
(defthm ex-mx-applyv
  (equal (mx2 (cons :applyv x) env caps defs fuel)
         (let ((rs (mx2-args (cdr x) env caps defs fuel)))
           (if (not (valp rs))
               rs
             (let ((rf (mx2 (car x) env caps defs fuel)))
               (if (not (valp rf)) rf (ex-mxcall (val rf) (val rs) defs fuel))))))
  :hints (("Goal" :expand ((mx2 (cons :applyv x) env caps defs fuel)) :in-theory (disable x2-fn x2-vals))))
; a call the tree enters: the VM's spread is the tree's (ex-callee) -- the
; variadic clause's count one in both (x2-req of the def, ex-varnf of the
; template), a hand-over's callee ex-hclo dispatching in x2-hcls
(defthm ex-x2-req-clauses (equal (x2-req (ex-clauses tm ars)) (ex-varnf ars))
  :hints (("Goal" :in-theory (enable ex-clause ex-anf ex-avar restp))))
(defthm ex-hclo-self (implies (ex-clo-shape g) (equal (ex-self (ex-hclo g)) g))
  :hints (("Goal" :in-theory (enable ex-hclo ex-self ex-clo-shape))))
(defthm ex-hclo-count (< (acl2-count g) (acl2-count (ex-hclo g))) :rule-classes nil
  :hints (("Goal" :in-theory (enable ex-hclo))))
(defthm ex-hclo-not-self (not (equal (ex-hclo g) g))
  :hints (("Goal" :in-theory (disable ex-hclo) :use ex-hclo-count)))
(defthm ex-hclo-not-self2 (not (equal g (ex-hclo g)))
  :hints (("Goal" :in-theory (disable ex-hclo) :use ex-hclo-count)))
(defthm ex-self-clo (equal (ex-self (list :clo a b)) (list :clo a b)) :hints (("Goal" :in-theory (enable ex-self))))
(defthm ex-mxcl-hclo (implies (ex-clo-shape g) (equal (ex-mxcl (ex-hclo g) args cls defs fuel) (ex-mxcl g args cls defs fuel)))
  :hints (("Goal" :in-theory (enable ex-hclo ex-clo-shape clop clo-caps))))
; apply's spread (vmx2's x2-* over seqk's sk-spread) opened only where asked
(in-theory (disable x2-spreads x2-hands x2-fn x2-vals x2-cls x2-sp sk-spread))
; the pieces: ex-mxcall when apply does not spread, when it does; ex-mxcall0
; of a closure that is its own self, of a hand-over; and apply's spread one
; in both (x2-sp is ex-apsp of a good closure, its def's variadic count
; the template's)
(defthm ex-xvs-cdr (implies (ex-xvs defs l) (ex-xvs defs (cdr l))) :hints (("Goal" :expand ((ex-xvs defs l)))))
(defthm ex-xvs-self (implies (and (ex-xvs defs (list g)) (ex-clo-shape g)) (equal (ex-self g) g))
  :hints (("Goal" :expand ((ex-xvs defs (list g))) :in-theory (enable ex-self ex-clo-shape clop clo))))
(defthm ex-mxcall-noapply
  (implies (not (equal f :apply))
           (equal (ex-mxcall f args defs fuel) (ex-mxcl f args (cdr (assoc-equal (clo-f f) defs)) defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall x2-fn x2-vals x2-cls x2-hands x2-spreads) (ex-mxcl x2-sp)))))
(defthm ex-mxcall-spread
  (implies (x2-spreads :applyv f args defs)
           (equal (ex-mxcall f args defs fuel)
                  (ex-mxcl (car args) (cadr (x2-sp args defs))
                           (if (equal (car (x2-sp args defs)) :hand)
                               (x2-hcls (cdr (assoc-equal (clo-f (car args)) defs)))
                             (cdr (assoc-equal (clo-f (car args)) defs)))
                           defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall x2-fn x2-vals x2-cls x2-hands) (ex-mxcl x2-sp x2-spreads x2-hcls)))))
(defthm ex-mxcall0-self
  (implies (equal (ex-self f) f)
           (equal (ex-mxcall0 f args defs fuel) (ex-mxcl f args (cdr (assoc-equal (clo-f f) defs)) defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall0 ex-mxcls) (ex-mxcl ex-self)))))
(defthm ex-mxcall0-hclo
  (implies (ex-clo-shape g)
           (equal (ex-mxcall0 (ex-hclo g) args defs fuel)
                  (ex-mxcl g args (x2-hcls (cdr (assoc-equal (clo-f g) defs))) defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall0 ex-mxcls) (ex-mxcl ex-self x2-hcls ex-hclo)))))
(defthm ex-x2-req-good
  (implies (and (ex-defs-ok defs defs) (ex-xvs defs (list g)) (clop g))
           (equal (x2-req (cdr (assoc-equal (clo-f g) defs))) (ex-varnf (nth 1 (cadr g)))))
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr g))))
                  :expand ((ex-xvs defs (list g)))
                  :in-theory (e/d (ex-def clo-f) (ex-defs-ok-assoc ex-defs-ok x2-req ex-varnf ex-clauses)))))
(defthm ex-apway-spreads
  (implies (and (equal (ex-apway tmp) 1) (ex-defs-ok defs defs) (ex-xvs defs (list (cadr tmp))))
           (and (equal (x2-sp (cdr tmp) defs) (ex-apsp tmp))
                (x2-spreads :applyv (car tmp) (cdr tmp) defs)
                (ex-clo-shape (cadr tmp))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance ex-x2-req-good (g (cadr tmp))))
                  :in-theory (e/d (x2-sp ex-apsp x2-spreads ex-apway ex-apentry ex-seqp ex-clo-shape clop)
                                  (sk-spread ex-x2-req-good ex-varnf x2-req ex-xvs no-mk)))))
(defthm ex-mxcall-callee
  (implies (and (ex-enters (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (ex-defs-ok defs defs) (consp tmp) (ex-xvs defs tmp))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel)
                  (ex-mxcall0 (car (ex-callee tmp)) (cdr (ex-callee tmp)) defs fuel)))
  :hints (("Goal" :cases ((equal (ex-apway tmp) 1)) :do-not-induct t
                  :use ((:instance ex-xvs-nth1 (l tmp) (j 0)) (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-xvs-self (g (car tmp))) (:instance ex-xvs-self (g (cadr tmp)))
                        (:instance ex-apway-spreads))
                  :in-theory (e/d (ex-enters ex-callable)
                                  (ex-mxcl ex-mxcall ex-mxcall0 ex-hclo ex-self sk-spread x2-sp x2-spreads ex-apsp ex-xvs ex-arity
                                   ex-wf no-mk ex-xvs-self ex-xvs-nth1 ex-apway-spreads ex-fbody)))
          ("Subgoal 1" :in-theory (e/d (ex-callee ex-enters ex-callable)
                                       (ex-mxcl ex-mxcall ex-mxcall0 ex-hclo ex-self sk-spread x2-sp x2-spreads ex-apsp ex-xvs ex-arity
                                        ex-wf no-mk ex-xvs-self ex-xvs-nth1 ex-apway-spreads ex-fbody)))))
(in-theory (disable ex-mxcall-noapply ex-mxcall-spread ex-mxcall0-self ex-mxcall0-hclo ex-apway-spreads ex-x2-req-good))
(defthm ex-mx-mkclo
  (equal (mx2 (cons :mkclo x) env caps defs fuel)
         (let ((rs (mx2-args (cdr x) env caps defs fuel))) (if (valp rs) (cons :val (clo (car x) (val rs))) rs)))
  :hints (("Goal" :expand ((mx2 (cons :mkclo x) env caps defs fuel)))))

; the body's lets: its captures read, each resolved (x2-res)
(defthm ex-capts-mx (equal (mx2-args (ex-capts j m) env caps defs fuel) (cons :val (ex-nths j m caps)))
  :hints (("Goal" :induct (ex-capts j m)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :capt x) env caps defs fuel))))))
(defun ex-clets-ind (j m env caps)
  (if (zp m) env (ex-clets-ind (1+ (nfix j)) (1- m) (append env (list (x2-res (nth (nfix j) caps)))) caps)))
(defthm ex-clets-mx
  (implies (true-listp env)
           (equal (mx2 (ex-clets j m x) env caps defs fuel) (mx2 x (append env (ex-nths j m caps)) caps defs fuel)))
  :hints (("Goal" :induct (ex-clets-ind j m env caps)
                  :expand ((:free (y env) (mx2 (cons :let y) env caps defs fuel))
                           (:free (y) (mx2 (cons :capt y) env caps defs fuel))))))
(defthm ex-nthcdr-step
  (implies (and (natp j) (< j (len l))) (equal (cons (nth j l) (nthcdr j (cdr l))) (nthcdr j l)))
  :hints (("Goal" :induct (nthcdr j l))))
(defthm ex-nthcdr-len (implies (true-listp l) (not (nthcdr (len l) l))))
(defthm ex-resl-nthcdr-step
  (implies (and (natp j) (< j (len l))) (equal (cons (x2-res (nth j l)) (ex-resl (nthcdr j (cdr l)))) (ex-resl (nthcdr j l))))
  :hints (("Goal" :use ex-nthcdr-step :in-theory (disable ex-nthcdr-step))))
(defthm ex-nths-nthcdr
  (implies (and (natp j) (true-listp l) (equal (+ j (nfix m)) (len l))) (equal (ex-nths j m l) (ex-resl (nthcdr j l))))
  :hints (("Goal" :induct (ex-nths j m l))))
(defthm ex-nths-all
  (implies (and (true-listp l) (equal m (len l))) (equal (ex-nths 0 m l) (ex-resl l)))
  :hints (("Goal" :use ((:instance ex-nths-nthcdr (j 0))))))

; a call of f with args: the arity it picks, mx2's environment for that
; arity's body (the arguments -- a variadic one's rest a list -- the
; captures, the closure), and the values the parameters' copies take. f
; is a closure, or apply's hand-over of one (ex-hclo, its arities the hand
; arity): ex-ftm the template of the closure it stands for (ex-self) --
; the def mx2 runs, the closure its self slot holds
(defun ex-ftm (f) (cadr (ex-self f)))
(defun ex-car (f args) (ex-arity (nth 1 (cadr f)) (len args)))
(defun ex-fenv (f args) (append (ex-bargs (ex-car f args) args) (ex-resl (caddr f)) (list (ex-resclo (ex-self f)))))
(defun ex-fvs (f args)
  (cdr (mx2-args (ex-locals (ex-fparams (ex-car f args)) (ex-fbcm (ex-ftm f) (ex-car f args))) (ex-fenv f args) nil nil 0)))

(defthm ex-len-inners-outers (equal (len (ex-outers capv)) (len (ex-inners capv))))
(defthm ex-subset-app (subsetp-equal a (append a b)))
(defthm ex-anp-natp (natp (ex-anp ar)) :rule-classes :type-prescription)
(defthm ex-anf-natp (natp (ex-anf ar)) :rule-classes :type-prescription)
(defthm ex-astart-natp (natp (ex-astart ar)) :rule-classes :type-prescription)
; THE HAND ARITY (ex-hars): the variadic one as a fixed one of one more
; parameter -- the same parameters, start and body: well formed with it,
; its clause's body the variadic one's, its clauses x2-hcls's
(defun ex-har (ar) (list* (1+ (nfix (nth 0 ar))) nil (cddr ar)))
(defun ex-hars2 (ars)
  (cond ((atom ars) nil) ((truthy (nth 1 (car ars))) (list (ex-har (car ars)))) (t (ex-hars2 (cdr ars)))))
(defthm ex-hars-is (equal (ex-hars ars) (ex-hars2 ars)) :hints (("Goal" :in-theory (enable ex-hars))))
(defthm ex-har-parts
  (implies (truthy (nth 1 ar))
           (and (equal (ex-anp (ex-har ar)) (ex-anp ar)) (equal (ex-astart (ex-har ar)) (ex-astart ar))
                (equal (ex-abody (ex-har ar)) (ex-abody ar)) (not (ex-avar (ex-har ar)))
                (equal (ex-anf (ex-har ar)) (+ 1 (ex-anf ar)))
                (natp (nth 0 (ex-har ar))) (equal (nth 2 (ex-har ar)) (nth 2 ar))))
  :hints (("Goal" :in-theory (enable ex-anp ex-anf ex-avar ex-astart ex-abody))))
(defthm ex-har-car (natp (car (ex-har ar))) :rule-classes :type-prescription)
(defthm ex-har-cddr (equal (cddr (ex-har ar)) (cddr ar)))
(in-theory (disable ex-anf ex-avar ex-anp ex-astart ex-abody ex-har))
(defthm ex-har-fbtr (implies (truthy (nth 1 ar)) (equal (ex-fbtr tm (ex-har ar)) (ex-fbtr tm ar)))
  :hints (("Goal" :in-theory (enable ex-fbtr ex-fparams ex-fbcm ex-flp ex-fcm ex-fcmb))))
(defthm ex-har-fbtc (implies (truthy (nth 1 ar)) (equal (ex-fbtc tm (ex-har ar)) (ex-fbtc tm ar)))
  :hints (("Goal" :in-theory (enable ex-fbin ex-fparams ex-fbcm ex-flp ex-fcm ex-fcmb))))
(defthm ex-har-arwf (implies (and (truthy (nth 1 ar)) (ex-arwf tm ar defs)) (ex-arwf tm (ex-har ar) defs))
  :hints (("Goal" :in-theory (enable ex-arwf ex-fparams ex-fbcm ex-flp ex-fcm ex-fcmb))))
(defthm ex-hars-arswf (implies (ex-arswf tm ars defs) (ex-arswf tm (ex-hars2 ars) defs))
  :hints (("Goal" :induct (ex-hars2 ars))))
(defthm ex-hars-clauses (equal (x2-hcls (ex-clauses tm ars)) (ex-clauses tm (ex-hars2 ars)))
  :hints (("Goal" :induct (ex-hars2 ars) :in-theory (e/d (ex-clause x2-hcls restp ex-avar) (ex-fbtr ex-fbtc)) :expand ((ex-clauses tm ars)))))
(defthm ex-hclo-parts
  (and (equal (cadr (ex-hclo g)) (update-nth 1 (ex-hars2 (nth 1 (cadr g))) (cadr g)))
       (equal (caddr (ex-hclo g)) (caddr g)) (clop (ex-hclo g)) (equal (clo-caps (ex-hclo g)) (caddr g))
       (ex-clo-shape (ex-hclo g)))
  :hints (("Goal" :in-theory (enable ex-hclo clop clo-caps ex-clo-shape))))
(in-theory (disable ex-hclo))

; what a call's entry needs of the callee f: a closure, or apply's
; hand-over of one, the closure a good value whose template's def is
; defs', f callable with the arguments' count
(defun ex-ehyp (f args defs)
  (and (ex-xvs defs (list (ex-self f))) (ex-clo-shape (ex-self f)) (or (equal (ex-self f) f) (equal f (ex-hclo (ex-self f))))
       (ex-defs-ok defs defs) (ex-callable f (len args)) (ex-xvs defs args) (true-listp args)))

(defmacro ex-efacts ()
  '(and (ex-tmwf (ex-ftm f) defs) (ex-arwf (ex-ftm f) (ex-car f args) defs) (ex-arswf (ex-ftm f) (nth 1 (cadr f)) defs)
        (ex-arity (nth 1 (cadr f)) (len args))
        (equal (len (ex-bargs (ex-car f args) args)) (ex-anp (ex-car f args)))
        (true-listp (ex-bargs (ex-car f args) args)) (ex-xvs defs (ex-bargs (ex-car f args) args))
        (equal (ex-self f) (clo (ex-ftm f) (caddr f)))
        (equal (ex-fbody f (len args)) (ex-abody (ex-car f args)))
        (equal (cdr (assoc-equal (ex-ftm f) defs)) (ex-def (ex-ftm f)))
        (equal (ex-mxcls f defs) (ex-clauses (ex-ftm f) (nth 1 (cadr f))))
        (equal (nth 2 (cadr f)) (nth 2 (ex-ftm f))) (equal (nth 3 (cadr f)) (nth 3 (ex-ftm f)))
        (equal (nth 4 (cadr f)) (nth 4 (ex-ftm f)))
        (clop f) (equal (clo-caps f) (caddr f))
        (true-listp (caddr f)) (equal (len (caddr f)) (len (ex-inners (nth 2 (ex-ftm f)))))
        (ex-xvs defs (ex-resl (caddr f))) (true-listp args)))
(defthm ex-ehyp-facts-plain
  (implies (and (ex-ehyp f args defs) (equal (ex-self f) f)) (ex-efacts))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr f))))
                  :do-not-induct t
                  :in-theory (e/d (ex-tmwf ex-car ex-abody ex-fbody ex-callable ex-ftm ex-mxcls ex-def clo-f clop clo-caps
                                   ex-clo-shape)
                                  (ex-defs-ok-assoc ex-arwf ex-bargs ex-arity ex-anp)))))
(defthm ex-ehyp-facts-hclo
  (implies (and (ex-ehyp f args defs) (equal f (ex-hclo g)) (ex-clo-shape g)) (ex-efacts))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr g))))
                  :do-not-induct t
                  :in-theory (e/d (ex-tmwf ex-car ex-abody ex-fbody ex-callable ex-ftm ex-mxcls ex-def clo-f clop clo-caps
                                   ex-clo-shape)
                                  (ex-defs-ok-assoc ex-arwf ex-bargs ex-arity ex-anp ex-self)))))
(defthm ex-ehyp-facts
  (implies (ex-ehyp f args defs) (ex-efacts))
  :rule-classes nil
  :hints (("Goal" :use (ex-ehyp-facts-plain (:instance ex-ehyp-facts-hclo (g (ex-self f))))
                  :in-theory (theory 'minimal-theory) :expand ((ex-ehyp f args defs)))))
; the callee's parts its template's (a hand-over's, the closure's it stands for)
(defthm ex-ehyp-nths
  (implies (ex-ehyp f args defs)
           (and (equal (nth 2 (cadr f)) (nth 2 (ex-ftm f))) (equal (nth 3 (cadr f)) (nth 3 (ex-ftm f)))
                (equal (nth 4 (cadr f)) (nth 4 (ex-ftm f)))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (disable ex-ehyp ex-ftm))))
(in-theory (disable ex-ftm))

; ---- A BODY WITH NO RECUR TO THE FN (exec-PLAN Lane 3 item 3(b)) ------------------------------
;
; ex-fbtr's loop is round the body only when it recurs to the fn (ex-tlr):
; else the body runs in ex-fbcm, no recur in its tail (ex-vwf-tlr-nil), and
; ex-vwf reads a scope only through its entries but nil (ex-vwf-sb), so
; ex-fcmb's well-formedness is ex-fbcm's.
(defun ex-tli (e i) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix i))))) (if (< (nfix i) (ex-i2 e)) (ex-tli e (1+ (nfix i))) t))
(defthm ex-tlr-loop (implies (equal (ex-kind e) 12) (not (ex-tlr :let e i)))
  :hints (("Goal" :induct (ex-tli e i) :in-theory (disable ex-kid-of) :expand ((ex-tlr :let e i)))))
(defthm ex-vwf-tlr-nil
  (implies (and (ex-vwf flg e i cm lp defs) (not (ex-tlr flg e i))) (ex-vwf flg e i cm nil defs))
  :hints (("Goal" :induct (ex-vwf flg e i cm lp defs) :in-theory (disable ex-kid-of ex-clr ex-lind)
                  :expand ((:free (flg lp) (ex-vwf flg e i cm lp defs)) (:free (flg) (ex-tlr flg e i))))))
; every entry of a but nil is in b
(defun ex-sb (a b) (if (atom a) t (and (or (null (car a)) (member-equal (car a) b)) (ex-sb (cdr a) b))))
(defthm ex-sb-mem (implies (and (ex-sb a b) (member-equal x a) x) (member-equal x b)))
(defthm ex-sb-nmem (implies (and (ex-sb a b) x (not (member-equal x b))) (not (member-equal x a))))
(defthm ex-subsetp-sb (implies (subsetp-equal a b) (ex-sb a b)))
(defthm ex-sb-cons (implies (ex-sb a b) (ex-sb a (cons x b))))
(defthm ex-sb-app-r (implies (ex-sb a b) (ex-sb a (append b l))))
(defthm ex-sb-app-l (implies (ex-sb a b) (ex-sb a (append l b))))
(defthm ex-sb-refl (ex-sb a a) :hints (("Goal" :use ((:instance ex-subsetp-sb (b a))))))
(defthm ex-sb-append (implies (and (ex-sb a b) (ex-sb c d)) (ex-sb (append a c) (append b d))))
(defthm ex-blank-mem (implies (and x (member-equal x b) (not (member-equal x ls))) (member-equal x (ex-blank ls b))))
(defthm ex-sb-blank (implies (ex-sb a b) (ex-sb (ex-blank ls a) (ex-blank ls b))))
(defthm ex-sb-blank-all (implies (subsetp-equal c ls) (ex-sb (ex-blank ls c) b)))
(defthm ex-sb-blank-self (ex-sb (ex-blank c c) b) :hints (("Goal" :use ((:instance ex-sb-blank-all (ls c))))))
(defthm ex-sb-nomem (implies (and (ex-sb a b) (ex-nomem ls b)) (ex-nomem ls a)))
(defthm ex-sb-nomem-blank (implies (and (ex-sb a b) (ex-nomem x (ex-blank ls b))) (ex-nomem x (ex-blank ls a)))
  :hints (("Goal" :use ((:instance ex-sb-nomem (a (ex-blank ls a)) (b (ex-blank ls b)) (ls x))) :in-theory (disable ex-sb-nomem))))
(defthm ex-sb-nmem-blank (implies (and (ex-sb a b) x (not (member-equal x (ex-blank ls b)))) (not (member-equal x (ex-blank ls a))))
  :hints (("Goal" :use ((:instance ex-sb-nmem (a (ex-blank ls a)) (b (ex-blank ls b)))) :in-theory (disable ex-sb-nmem))))
(defthm ex-sb-subsetp
  (implies (and (subsetp-equal l a) (ex-sb a b) (not (member-equal nil l))) (subsetp-equal l b)))
(defthm ex-nat-list-nonil (implies (nat-listp l) (not (member-equal nil l))))
(defthm ex-slots-nonil (not (member-equal nil (ex-slots s n))))
(defthm ex-sb-lfin (implies (and (ex-lfin os s n a) (ex-sb a b)) (ex-lfin os s n b)))
(defthm ex-sb-lfok (implies (and (ex-lfok e j a defs) (ex-sb a b)) (ex-lfok e j b defs)))
; ex-vwf's walk on two scopes side by side
(set-irrelevant-formals-ok t)
(defun ex-v2 (flg e i cm cm2 lp) (declare (xargs :ruler-extenders :all :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i))) :well-founded-relation o< :hints (("Goal" :in-theory (e/d (ex-c ex-kind ex-nk ex-kids ex-i2 ex-vrank ex-vleft) (ex-kid-of)))))) (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i))) (if (consp e) (list (case flg (:do (cond ((zp nk) nil) ((< i (- nk 1)) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :do e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list nil)) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) (list nil)) lp))) (t (list (ex-v2 :m (ex-kid-of e (- nk 1)) 0 cm cm2 lp))))) (:let (cond ((and (< i n2) (equal k 12) (ex-lind e 1)) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :m (ex-kid-of e i) 0 (append cm (ex-slots (ex-s2 e) i)) (append cm2 (ex-slots (ex-s2 e) i)) nil) (ex-v2 :let e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) lp))) ((< i n2) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :let e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list (+ (ex-s2 e) i))) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) (list (+ (ex-s2 e) i))) lp))) ((equal k 11) (list (ex-v2 :m (ex-kid-of e n2) 0 cm cm2 lp))) ((and (equal k 12) (ex-lind e 1)) (let ((ls (ex-slots (ex-s2 e) n2))) (list (ex-v2 :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (append (ex-blank ls cm2) ls) (cons (ex-s2 e) n2))))) ((equal k 12) (let ((ls (ex-slots (ex-s2 e) n2))) (list (ex-v2 :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (append (ex-blank ls cm2) ls) (cons (ex-s2 e) n2))))) (t nil))) (:lin (if (< i n2) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :lin e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) lp)) nil)) (:rec (list (if (< i nk) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :rec e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) lp)) nil))) (:call (list (if (< i nk) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :call e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) lp)) nil))) (:cs (list (if (< i (len (ex-c e))) (list (ex-v2 :m (ex-cbody e i) 0 (append cm (list (ex-cslot e i))) (append cm2 (list (ex-cslot e i))) nil) (ex-v2 :cs e (1+ i) cm cm2 lp)) nil))) (:fin (list (ex-v2 :m (ex-kid-of e 1) 0 (append cm (list nil)) (append cm2 (list nil)) nil))) (:coll (list (if (< i nk) (list (ex-v2 :m (ex-kid-of e i) 0 cm cm2 nil) (ex-v2 :coll e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm2) lp)) nil))) (:ct (list (if (< i (len (ex-c e))) (list (ex-v2 :m (ex-cthen e i) 0 cm cm2 lp) (ex-v2 :ct e (1+ i) cm cm2 lp)) nil))) (otherwise (cond ((or (equal k 1) (equal k 3)) nil) ((equal k 2) nil) ((equal k 26) (list (ex-v2 :m (ex-c e) 0 (ex-blank cm cm) (ex-blank cm2 cm2) nil))) ((or (equal k 14) (equal k 15)) nil) ((and (equal k 6) (ex-bipe e)) (list (ex-v2 :m (ex-kid-of e 0) 0 cm cm2 nil) (ex-v2 :call e 1 cm cm2 lp))) ((equal k 6) (list (ex-v2 :m (ex-kid-of e 0) 0 cm cm2 nil) (ex-v2 :call e 1 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm2) (list nil)) lp))) ((equal k 4) (list (ex-v2 :m (ex-kid-of e 0) 0 cm cm2 nil) (ex-v2 :m (ex-kid-of e 1) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm2) lp) (ex-v2 :m (ex-kid-of e 2) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm2) lp))) ((equal k 5) (list (ex-v2 :do e 0 cm cm2 lp))) ((equal k 11) (list (ex-v2 :let e 0 cm cm2 lp))) ((equal k 12) (list (ex-v2 :let e 0 cm cm2 lp) (ex-v2 :lin e 0 cm cm2 lp))) ((equal k 13) (list (ex-v2 :m (ex-kid-of e n2) 0 (append cm (ex-slots (ex-s2 e) n2)) (append cm2 (ex-slots (ex-s2 e) n2)) lp))) ((equal k 16) (list (ex-v2 :rec e 0 cm cm2 lp))) ((equal k 17) (list (ex-v2 :m (ex-kid-of e 0) 0 cm cm2 nil))) ((equal k 18) (list (ex-v2 :m (ex-kid-of e 0) 0 cm cm2 nil) (ex-v2 :cs e 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm2) nil) (ex-v2 :fin e 0 (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm2) nil))) ((member k '(7 8 9 22 23 10 20 24 21)) (list (ex-v2 :coll e 0 cm cm2 nil))) ((equal k 19) (list (ex-v2 :m (ex-kid-of e 0) 0 cm cm2 nil) (ex-v2 :m (ex-kid-of e 1) 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm2) (list nil)) lp) (ex-v2 :ct e 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm2) (list nil)) lp))) (t nil))))) nil)))
(defthm ex-vwf-sb
  (implies (and (ex-vwf flg e i cm lp defs) (ex-sb cm cm2) (ex-sb cm2 cm)) (ex-vwf flg e i cm2 lp defs))
  :hints (("Goal" :induct (ex-v2 flg e i cm cm2 lp) :in-theory (disable ex-kid-of ex-clr ex-lind)
                  :expand ((:free (flg) (ex-vwf flg e i cm lp defs)) (:free (flg) (ex-vwf flg e i cm2 lp defs))))))
(defthm ex-sb-blank-back (ex-sb c (append (ex-blank x c) x)))
(defthm ex-sb-blank-in (ex-sb (ex-blank x c) c))
(defthm ex-sb-app2 (implies (and (ex-sb a c) (ex-sb b c)) (ex-sb (append a b) c)))
(defthm ex-sb-blank-fwd (implies (subsetp-equal x c) (ex-sb (append (ex-blank x c) x) c)))
(defthm ex-fparams-fbcm (subsetp-equal (ex-fparams ar) (ex-fbcm tm ar)) :hints (("Goal" :in-theory (enable ex-fbcm))))
(defthm ex-fcmb-sb (and (ex-sb (ex-fcmb tm ar) (ex-fbcm tm ar)) (ex-sb (ex-fbcm tm ar) (ex-fcmb tm ar)))
  :hints (("Goal" :in-theory (e/d (ex-fcmb ex-fcm ex-flp ex-lsl) (ex-fbcm ex-sb ex-fparams-fbcm ex-sb-blank-fwd ex-sb-blank-back))
                  :use (ex-fparams-fbcm
                        (:instance ex-sb-blank-fwd (x (ex-fparams ar)) (c (ex-fbcm tm ar)))
                        (:instance ex-sb-blank-back (x (ex-fparams ar)) (c (ex-fbcm tm ar))))
                  :expand ((ex-fparams ar)))))

(defthm ex-fbcm-agree
  (implies (ex-ehyp f args defs)
           (ex-agree (ex-fbcm (ex-ftm f) (ex-car f args)) (ex-fenv f args) (ex-bind f args)))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-tmwf ex-arwf ex-astart ex-fself ex-fparams ex-fbcm ex-bind ex-car ex-fenv)
                                  (ex-ehyp ex-bargs ex-arity ex-anp ex-slots ex-vwf)))))

(defthm ex-enter-fbody
  (implies (ex-ehyp f args defs) (equal (ex-fbody f (len args)) (ex-abody (ex-car f args))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (disable ex-ehyp ex-fbody ex-abody ex-car))))
(defthm ex-enter-vwf
  (implies (ex-ehyp f args defs)
           (ex-vwf :m (ex-abody (ex-car f args)) 0
                   (append (ex-fcm (ex-ftm f) (ex-car f args)) (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args))))
                   (cons (ex-astart (ex-car f args)) (ex-anp (ex-car f args))) defs))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-arwf) (ex-ehyp ex-car ex-fcm ex-astart ex-anp ex-abody)))))
(defthm ex-enter-iterok
  (implies (ex-ehyp f args defs)
           (or (ex-nomem (ex-clr :m (ex-abody (ex-car f args)) 0) (ex-fcm (ex-ftm f) (ex-car f args)))
               (ex-vwf :m (ex-abody (ex-car f args)) 0
                       (append (ex-fcm (ex-ftm f) (ex-car f args)) (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args))))
                       nil defs)))
  :rule-classes nil
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-arwf) (ex-ehyp ex-car ex-fcm ex-astart ex-anp ex-abody)))))
(defthm ex-enter-agree-cm
  (implies (ex-ehyp f args defs) (ex-agree (ex-fcm (ex-ftm f) (ex-car f args)) (ex-fenv f args) (ex-bind f args)))
  :hints (("Goal" :in-theory (e/d (ex-fcm) (ex-ehyp ex-fenv ex-bind ex-fbcm ex-car)))))
(defthm ex-enter-agree-params
  (implies (ex-ehyp f args defs)
           (ex-agree (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args))) (ex-fvs f args) (ex-bind f args)))
  :hints (("Goal" :in-theory (e/d (ex-fvs ex-fparams) (ex-ehyp ex-fenv ex-bind ex-locals-indep ex-car))
                  :use (ex-fbcm-agree
                        (:instance ex-locals-mx (ls (ex-fparams (ex-car f args))) (cm (ex-fbcm (ex-ftm f) (ex-car f args)))
                                   (env (ex-fenv f args)) (fr (ex-bind f args)) (caps nil) (defs nil) (fuel 0)))
                  :expand ((ex-fbcm (ex-ftm f) (ex-car f args))))))
(defthm ex-enter-len
  (implies (ex-ehyp f args defs) (equal (len (ex-fenv f args)) (len (ex-fcm (ex-ftm f) (ex-car f args)))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-fcm ex-fbcm ex-fparams ex-fenv) (ex-ehyp ex-car ex-bargs)))))
(defthm ex-enter-xvs-env
  (implies (ex-ehyp f args defs) (ex-xvs defs (ex-fenv f args)))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-fenv ex-ehyp) (ex-tmwf ex-defs-ok ex-callable ex-car ex-bargs)))))
(defthm ex-enter-xvs-vs
  (implies (ex-ehyp f args defs) (ex-xvs defs (ex-fvs f args)))
  :hints (("Goal" :in-theory (e/d (ex-fvs) (ex-ehyp ex-fenv ex-locals-indep ex-car)))))
(defthm ex-enter-nomem (ex-nomem (ex-slots (ex-astart ar) (ex-anp ar)) (ex-fcm tm ar))
  :hints (("Goal" :in-theory (e/d (ex-fcm) (ex-fbcm ex-anp ex-astart ex-blank)))))
(defthm ex-car-assoc (implies (consp (assoc-equal x l)) (equal (car (assoc-equal x l)) x)))
(defthm ex-assoc-def
  (implies (and (ex-defs-ok defs defs) (consp (assoc-equal tm defs)))
           (equal (assoc-equal tm defs) (cons tm (ex-def tm))))
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs)))
                  :in-theory (disable ex-defs-ok-assoc ex-def ex-defs-ok))))
; the clause's body answers what ex-fbtr's does: the captures read in place
(defthm ex-fbtc-mx
  (implies (and (true-listp args) (equal (len args) (ex-anp ar)))
           (equal (mx2 (ex-fbtc tm ar) args caps defs fuel) (mx2 (ex-fbtr tm ar) args caps defs fuel)))
  :hints (("Goal" :use ex-fbtr-fbin :in-theory (disable ex-fbin ex-cs mx2 ex-fbtr))))
(in-theory (disable ex-fbtc))
(defthm ex-enter-mx1
  (implies (and (ex-ehyp f args defs) (not (zp fuel)))
           (equal (ex-mxcall0 f args defs fuel)
                  (mx2 (ex-fbtr (ex-ftm f) (ex-car f args)) (ex-bargs (ex-car f args) args) (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use (ex-ehyp-facts
                        (:instance ex-pick-arity (tm (ex-ftm f)) (ars (nth 1 (cadr f))) (m (len args))))
                  :in-theory (e/d (ex-mxcall0 ex-mxcl ex-car ex-clause ex-bargs ex-anf ex-avar)
                                  (ex-fbtr ex-arwf ex-defs-ok ex-arity ex-pick-arity ex-ehyp ex-arswf ex-rest-args ex-mxcls ex-self
                                   ex-clauses ex-tmwf)))))
(defthm ex-fbtr-mx
  (implies (and (true-listp args) (true-listp caps) (equal (len caps) (len (ex-inners (nth 2 tm)))) (ex-tlr :m (ex-abody ar) 0))
           (equal (mx2 (ex-fbtr tm ar) args caps defs fuel)
                  (mx2-loop (list :loop nil (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))
                            (append args (ex-resl caps) (list (clo tm (ex-resl caps))))
                            (cdr (mx2-args (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                                     (append args (ex-resl caps) (list (clo tm (ex-resl caps)))) nil nil 0))
                            caps defs fuel)))
  :hints (("Goal" :use ((:instance ex-mx-loop-body
                                   (e (list :loop (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                            (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar))))
                                   (base (append args (ex-resl caps) (list (clo tm (ex-resl caps)))))
                                   (vs (cdr (mx2-args (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                                                (append args (ex-resl caps) (list (clo tm (ex-resl caps)))) nil nil 0)))))
                  :in-theory (e/d (ex-fbtr) (ex-mx-loop-body ex-fbcm ex-fparams ex-fcm ex-fcmb ex-abody clo))
                  :expand ((:free (y env) (mx2 (cons :let y) env caps defs fuel))
                           (:free (y env) (mx2 (cons :loop y) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2 '(:const nil) env caps defs fuel))))))
; no recur to the fn: no loop, the body in ex-fbcm
(defthm ex-fbtr-mx-m
  (implies (and (true-listp args) (true-listp caps) (equal (len caps) (len (ex-inners (nth 2 tm)))) (not (ex-tlr :m (ex-abody ar) 0)))
           (equal (mx2 (ex-fbtr tm ar) args caps defs fuel)
                  (mx2 (ex-tr :m (ex-abody ar) 0 (ex-fbcm tm ar)) (append args (ex-resl caps) (list (clo tm (ex-resl caps)))) caps defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-fbtr) (ex-fbcm ex-fparams ex-fcm ex-fcmb ex-abody clo))
                  :expand ((:free (y env) (mx2 (cons :let y) env caps defs fuel))))))
(defthm ex-enter-mx
  (implies (and (ex-ehyp f args defs) (not (zp fuel)) (ex-tlr :m (ex-abody (ex-car f args)) 0))
           (equal (ex-mxcall0 f args defs fuel)
                  (mx2-loop (list :loop nil (ex-tr :m (ex-abody (ex-car f args)) 0
                                                   (append (ex-fcm (ex-ftm f) (ex-car f args))
                                                           (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args))))))
                            (ex-fenv f args) (ex-fvs f args) (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-fvs ex-fenv ex-fcmb) (ex-ehyp ex-fbtr ex-fbcm ex-fparams ex-fcm ex-abody ex-car ex-bargs
                                                            ex-mxcall0)))))

; the callee a good call record's apply makes, as an entered call's
(defthm ex-enter-mx-m
  (implies (and (ex-ehyp f args defs) (not (zp fuel)) (not (ex-tlr :m (ex-abody (ex-car f args)) 0)))
           (equal (ex-mxcall0 f args defs fuel)
                  (mx2 (ex-tr :m (ex-abody (ex-car f args)) 0 (ex-fbcm (ex-ftm f) (ex-car f args)))
                       (ex-fenv f args) (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use (ex-ehyp-facts ex-enter-mx1
                        (:instance ex-fbtr-mx-m (tm (ex-ftm f)) (ar (ex-car f args)) (args (ex-bargs (ex-car f args) args))
                                   (caps (caddr f)) (fuel (+ -1 fuel))))
                  :in-theory (e/d (ex-fenv) (ex-enter-mx1 ex-fbtr-mx-m ex-fbtr-mx ex-enter-mx ex-ehyp ex-fbtr ex-fbcm ex-fparams ex-fcm
                                             ex-abody ex-car ex-bargs ex-mxcall0 ex-tr mx2)))))
(defthm ex-enter-vwf-m
  (implies (and (ex-ehyp f args defs) (not (ex-tlr :m (ex-abody (ex-car f args)) 0)))
           (ex-vwf :m (ex-abody (ex-car f args)) 0 (ex-fbcm (ex-ftm f) (ex-car f args)) nil defs))
  :hints (("Goal" :use (ex-enter-vwf
                        (:instance ex-vwf-tlr-nil (flg :m) (e (ex-abody (ex-car f args))) (i 0)
                                   (cm (ex-fcmb (ex-ftm f) (ex-car f args))) (lp (cons (ex-astart (ex-car f args)) (ex-anp (ex-car f args)))))
                        (:instance ex-vwf-sb (flg :m) (e (ex-abody (ex-car f args))) (i 0) (lp nil)
                                   (cm (ex-fcmb (ex-ftm f) (ex-car f args))) (cm2 (ex-fbcm (ex-ftm f) (ex-car f args)))))
                  :in-theory (e/d (ex-fcmb) (ex-ehyp ex-enter-vwf ex-vwf-tlr-nil ex-vwf-sb ex-vwf ex-tlr ex-car ex-fcm ex-fbcm ex-abody ex-astart ex-anp)))))

(defthm ex-apsp-good
  (implies (and (equal (ex-apway tmp) 1) (ex-xvs defs tmp) (ex-lzok defs))
           (and (ex-xvs defs (cadr (ex-apsp tmp))) (true-listp (cadr (ex-apsp tmp)))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance ex-sk-spread-good (req (ex-varnf (nth 1 (cadr (cadr tmp))))) (fx (butlast (cddr tmp) 1))
                                   (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-noclo (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-last (l (cdr tmp)))
                        (:instance ex-xvs-cdr (l tmp)) (:instance ex-xvs-cdr (l (cdr tmp)))
                        (:instance ex-xvs-butlast (l (cddr tmp)) (n 1)))
                  :in-theory (e/d (ex-apway ex-apentry ex-seqp ex-apsp sk-spread-true-listp)
                                  (ex-lzok ex-xvs sk-spread ex-sk-spread-good ex-xvs-noclo ex-xvs-last ex-xvs-cdr ex-xvs-butlast
                                   last butlast ex-varnf no-mk)))))
(in-theory (disable ex-apsp-good))
(defthm ex-callee-ehyp
  (implies (and (ex-enters (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (consp tmp) (true-listp tmp) (ex-xvs defs tmp)
                (ex-lzok defs) (ex-defs-ok defs defs))
           (ex-ehyp (car (ex-callee tmp)) (cdr (ex-callee tmp)) defs))
  :hints (("Goal" :cases ((equal (ex-apway tmp) 1)) :do-not-induct t
                  :use ((:instance ex-xvs-nth1 (l tmp) (j 0)) (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-xvs-self (g (car tmp))) (:instance ex-xvs-self (g (cadr tmp)))
                        (:instance ex-xvs-cdr (l tmp))
                        (:instance ex-apway-spreads) (:instance ex-apsp-good))
                  :in-theory (e/d (ex-enters ex-callable)
                                  (ex-xvs ex-xvs-self ex-xvs-nth1 ex-xvs-cdr ex-wf no-mk ex-arity ex-apway-spreads ex-apsp-good
                                   ex-apsp ex-hclo ex-self ex-lzok ex-fbody x2-sp ex-defs-ok)))
          ("Subgoal 1" :in-theory (e/d (ex-callee ex-enters ex-callable)
                                       (ex-xvs ex-xvs-self ex-xvs-nth1 ex-xvs-cdr ex-wf no-mk ex-arity ex-apway-spreads ex-apsp-good
                                        ex-apsp ex-hclo ex-self ex-lzok ex-fbody x2-sp ex-defs-ok)))))

; the same, of a call's record: its callee (car tmp), its arguments (cdr tmp)
; (ex-defs-ok first: it binds defs, which the rules' left sides do not name,
; so ex-ehyp of apply's callee is rewritten by ex-callee-ehyp, not looked up)
(defmacro ex-chyp () '(and (ex-defs-ok defs defs) (ex-ehyp (car tmp) (cdr tmp) defs)))
(defmacro ex-cr () '(ex-car (car tmp) (cdr tmp)))
(defthm ex-call-fbody
  (implies (ex-chyp) (equal (ex-fbody (car tmp) (len (cdr tmp))) (ex-abody (ex-cr))))
  :hints (("Goal" :by (:instance ex-enter-fbody (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-vwf
  (implies (ex-chyp)
           (ex-vwf :m (ex-abody (ex-cr)) 0 (append (ex-fcm (ex-ftm (car tmp)) (ex-cr)) (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr))))
                   (cons (ex-astart (ex-cr)) (ex-anp (ex-cr))) defs))
  :hints (("Goal" :by (:instance ex-enter-vwf (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-iterok
  (implies (ex-chyp)
           (or (ex-nomem (ex-clr :m (ex-abody (ex-cr)) 0) (ex-fcm (ex-ftm (car tmp)) (ex-cr)))
               (ex-vwf :m (ex-abody (ex-cr)) 0 (append (ex-fcm (ex-ftm (car tmp)) (ex-cr)) (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr))))
                       nil defs)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ex-enter-iterok (f (car tmp)) (args (cdr tmp)))))))
(defthm ex-call-agree-cm
  (implies (ex-chyp) (ex-agree (ex-fcm (ex-ftm (car tmp)) (ex-cr)) (ex-fenv (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-agree-cm (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-agree-params
  (implies (ex-chyp)
           (ex-agree (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr))) (ex-fvs (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-agree-params (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-len
  (implies (ex-chyp) (equal (len (ex-fenv (car tmp) (cdr tmp))) (len (ex-fcm (ex-ftm (car tmp)) (ex-cr)))))
  :hints (("Goal" :by (:instance ex-enter-len (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-xvs-env
  (implies (ex-chyp) (ex-xvs defs (ex-fenv (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-xvs-env (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-xvs-vs
  (implies (ex-chyp) (ex-xvs defs (ex-fvs (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-xvs-vs (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-mx
  (implies (and (ex-chyp) (not (zp fuel)) (ex-tlr :m (ex-abody (ex-cr)) 0))
           (equal (ex-mxcall0 (car tmp) (cdr tmp) defs fuel)
                  (mx2-loop (list :loop nil (ex-tr :m (ex-abody (ex-cr)) 0
                                                   (append (ex-fcm (ex-ftm (car tmp)) (ex-cr))
                                                           (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr))))))
                            (ex-fenv (car tmp) (cdr tmp)) (ex-fvs (car tmp) (cdr tmp)) (caddr (car tmp)) defs (+ -1 fuel))))
  :hints (("Goal" :by (:instance ex-enter-mx (f (car tmp)) (args (cdr tmp))))))

(defthm ex-call-mx-m
  (implies (and (ex-chyp) (not (zp fuel)) (not (ex-tlr :m (ex-abody (ex-cr)) 0)))
           (equal (ex-mxcall0 (car tmp) (cdr tmp) defs fuel)
                  (mx2 (ex-tr :m (ex-abody (ex-cr)) 0 (ex-fbcm (ex-ftm (car tmp)) (ex-cr)))
                       (ex-fenv (car tmp) (cdr tmp)) (caddr (car tmp)) defs (+ -1 fuel))))
  :hints (("Goal" :by (:instance ex-enter-mx-m (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-vwf-m
  (implies (and (ex-chyp) (not (ex-tlr :m (ex-abody (ex-cr)) 0)))
           (ex-vwf :m (ex-abody (ex-cr)) 0 (ex-fbcm (ex-ftm (car tmp)) (ex-cr)) nil defs))
  :hints (("Goal" :by (:instance ex-enter-vwf-m (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-agree-fbcm
  (implies (ex-chyp) (ex-agree (ex-fbcm (ex-ftm (car tmp)) (ex-cr)) (ex-fenv (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-fbcm-agree (f (car tmp)) (args (cdr tmp))))))

(defthm ex-linked-ev
  (implies (ex-linked h) (equal (ex-ev :m h 0 tmp fr fuel) (list (cons :val (ex-c h)) fr 1)))
  :hints (("Goal" :expand ((ex-ev :m h 0 tmp fr fuel)))))

; a call never answers a recur: its callee's body restarts on one
(defun ex-cind (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (< (nfix i) (ex-nk e))
      (let ((r (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (ex-cind e (1+ (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel))
    (list tmp fr)))
(defthm ex-call-not-recur (not (equal (car (car (ex-ev :call e i tmp fr fuel))) :recur))
  :hints (("Goal" :induct (ex-cind e i tmp fr fuel) :in-theory (disable ex-kid-of)
                  :expand ((ex-ev :call e i tmp fr fuel)))))

(defthm ex-xvs-nil (ex-xvs defs nil))
(defthm ex-xvs-nil1 (ex-xvs defs (list nil)))
(defthm ex-xvs-clo
  (implies (and (consp (assoc-equal tm defs)) (ex-xvs defs caps) (true-listp caps)
                (equal (len caps) (len (ex-inners (nth 2 tm)))))
           (ex-xvs defs (list (list :clo tm caps)))))

(in-theory (disable ex-anf ex-avar ex-anp ex-astart ex-abody ex-fself ex-fbcm ex-fcm ex-fbtr ex-def ex-tmwf ex-arwf
                    ex-car ex-fenv ex-fvs ex-callable ex-enters ex-bind ex-mxcall ex-mxcall0 ex-ehyp ex-fbody ex-arerr ex-bargs ex-mxcl ex-mxcls))


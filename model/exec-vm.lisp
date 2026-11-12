; THE TREE EVALUATOR'S MEANING IS THE VM'S (model/exec.lisp against
; model/vmx2.lisp): for the core -- constants, locals, Vars, if, do, let*,
; loop*, recur, fns of any arities, calls, throw and try -- what ex-ev answers is what
; vmx2's mx2 answers of the tree's translation, and vmx2-proof proves the
; VM runs mx2 (vcs2-correct), so the VM run of the translation answers the
; tree's value (ex-vm-runs, in exec-vmrun).
;
; The tree names a local by its SLOT in the fn's frame, which the analyzer
; numbers by reservation, never reusing one in scope; mx2 names it by its
; POSITION in an environment a let grows by one. The translation (ex-tr)
; carries cm, the slots in scope by position: a local is (:local p) for
; its slot's position p, a let a nest of mx2's one-binding lets, a do an if
; on each value but the last with the rest on both branches (the core is
; pure: a value only chooses between equal branches). The relation
; (ex-agree cm env fr): position p's value is slot (nth p cm)'s, for each
; position whose cm entry is a slot (a nil entry is a position no name
; reaches any more). A MARKED READ clears its slot (milestone 4): what a
; node may clear (ex-clr) is blanked in the scope of every part that runs
; after it, in the translation and in ex-vwf alike, so a well-formed tree
; never reads a cleared slot, and the scope after a node agrees blanked of
; its ex-clr.
;
; A LOOP. The tree binds a loop's inits one after another, each seeing
; the ones before; vmx's :loop binds its inits at once. So a loop of n
; bindings in slots s .. s+n-1 is n of mx2's lets (the inits, in order)
; around (:loop (nil, copies of the n positions) body): the body's scope
; is the lets' positions blanked -- after a recur they hold the first
; round's values, and no name reaches them -- then a dummy and the
; copies, so its slots name the loop's own positions. A recur is (:recur
; nil args...): the dummy makes every loop bind at least one, as x2wf asks,
; and keeps a zero-binding loop one translation.
;
; FNS AND CALLS. A Var is (:const its value) (the namespace is the host's;
; the machine reads the value from the node). A fn is (:mkclo template
; locals of its outer slots): the tree's closure and mx2's are one value. A
; call is head first, as the tree runs it (exec-PLAN 3b, ex-trcall): (:let
; head (:if (:prim :ifn (:local p)) (:applyv (:local p) args) (:throw
; (:const :not-fn)))), p the head's new position, the arguments in scope
; cm ++ (nil) -- :callv's call, or apply's spread when the head's value is
; apply, as the tree's ex-callee spreads it (apply is a value; only the
; head's value tells), after the runtime's cast to IFn the tree's pc 1
; asks (ex-ifn) -- so a throw in the head, the cast or an argument is the
; same throw in both. mx2's
; defs are keyed by the template itself (vcs2-correct asks only x2defs-ok,
; and both look a name up by equal), the def a clause for each arity, (nf
; body) or (nf body :rest): lets of the captures and of the closure remade,
; for the self slot, around the loop translation of the parameters (a
; variadic arity's rest among them, a list, as mx2's split-rest makes it),
; so a recur to the fn is that loop's. The arity a call's count picks is
; the one mx2's pick-arity picks (ex-pick-arity): the fixed one, else the
; variadic one. Templates ask (ex-tmwf) each arity's parameter slots apart
; from the capture and self slots. Every closure-shaped value has its
; template in the defs, and no value is the symbol :clo, so a rest list is
; never closure-shaped (ex-xvs), threaded through the scope, results and
; recur values; no value is the symbol :recur-marker either, so no good
; list holds the tree's recur marker (ex-xvs-no-mk) and apply's spread of
; good values is never refused for one. A call of a closure no arity fits
; throws :arity in both (ex-ev's :thrown, mx2's). The runtime's part
; (prim, unconstrained) is three hypotheses: its cast to IFn throws nothing
; (ex-ifnok), and a call of apply the tree refuses -- fewer than two
; arguments, a closure's with no seq -- it refuses with the tree's :arity
; and :not-seq (ex-apok); and its instance? throws nothing (ex-isaok).
;
; THROW AND TRY. A throw is mx2's (:throw x). A try is (:try B H), H the
; catch walk over prim :isa at the thrown value's position (ex-trh), clause
; j's body in scope cm ++ (slot j), so the clause mx2 runs is ex-catchw's
; and its slot holds the thrown value; a finally F is vmx2's desugaring,
; (:let (:try X (:if F (:throw p) (:throw p))) (:if F p p)) (ex-trfin), F
; in scope cm ++ (nil). ex-mx-trtry says what mx2 makes of it (ex-mxtry),
; so the flag proof's try case is that lemma's, and ex-vpost's :fin place
; is the try's end, as ex-ev's.
;
; THE THEOREM (ex-vm-agree): a well-formed core tree in no loop's tail
; whose scope agrees answers, when ex-ev gives a value or a throw, that
; same answer from mx2 of its translation, the scope still agreeing after
; (a throw's frame the one the tree's unwinding sees); and it
; never answers a recur (ex-recur-stays) -- a recur's values reach only
; its loop's slots, which mx2's recur gives its loop's positions. The
; translation of a well-formed tree is x2wf (ex-tr-xwf), so with
; vcs2-correct: ex-vm-runs (exec-vmrun). With ex-machine-correct (exec-proof), the
; machine exec.inc's run_loop is answers what the VM answers.

(in-package "ACL2")

(include-book "exec-vmcall")
; a part of a sequence clears what it does, then the rest what they do
(defthm ex-clr-seq-open
  (implies (and (member-equal flg (quote (:rec :call :coll))) (consp e) (< (nfix i) (ex-nk e)))
           (equal (ex-clr flg e i) (append (ex-clr :m (ex-kid-of e (nfix i)) 0) (ex-clr flg e (+ 1 (nfix i))))))
  :hints (("Goal" :in-theory (disable ex-kid-of) :expand ((ex-clr flg e i)))))
(defthm ex-clr-seq-end
  (implies (and (member-equal flg (quote (:rec :call :coll))) (not (< (nfix i) (ex-nk e)))) (equal (ex-clr flg e i) nil))
  :hints (("Goal" :in-theory (disable ex-kid-of) :expand ((ex-clr flg e i)))))
(in-theory (disable ex-clr))

; ---- A THROW (exec-PLAN 3b) -------------------------------------------------------------------
;
; The runtime's answers the agreement on a throw asks of it: its cast to
; IFn throws nothing (ex-ifnok: clj's cast either passes or is the tree's
; :not-fn), and a call of apply the tree refuses -- fewer than two
; arguments (ex-apway 2), a closure's with no seq (3) -- it refuses too,
; with the tree's :arity and :not-seq (ex-apok), as clj's apply throws.
(defun-sk ex-ifnok () (forall h (not (throwp (prim :ifn (list h))))))
(defun ex-aperr (tmp) (if (equal (ex-apway tmp) 2) :arity :not-seq))
(defun-sk ex-apok ()
  (forall tmp (implies (or (equal (ex-apway tmp) 2) (equal (ex-apway tmp) 3))
                       (equal (prim :invoke tmp) (cons :throw (ex-aperr tmp))))))
(in-theory (disable ex-ifnok ex-apok))

(defthm ex-nth-len-append (equal (nth (len a) (append a (list v))) v) :hints (("Goal" :induct (len a))))
; a call's translation, head first: the head, then the cast, then :applyv
(defthm ex-mx-trcall
  (implies (and (ex-ifnok) (equal p (len env)))
           (equal (mx2 (ex-trcall h args p) env caps defs fuel)
                  (let ((rh (mx2 h env caps defs fuel)))
                    (cond ((not (valp rh)) rh)
                          ((not (ex-ifn (val rh))) '(:thrown . :not-fn))
                          (t (let ((rs (mx2-args args (append env (list (val rh))) caps defs fuel)))
                               (if (valp rs) (ex-mxcall (val rh) (val rs) defs fuel) rs)))))))
  :hints (("Goal" :in-theory (e/d (ex-ifn ex-trcall) (ex-mxcall))
                  :use ((:instance ex-ifnok-necc (h (val (mx2 h env caps defs fuel)))))
                  :expand ((:free (x env) (mx2 (cons :let x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :throw x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :const x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
(in-theory (disable ex-trcall))

; a good list holds no recur marker (no good value ends in :recur-marker)
(defthm ex-xvs-no-mk (implies (ex-xvs defs l) (no-mk l))
  :hints (("Goal" :induct (ex-xvs defs l) :in-theory (enable clop) :expand ((ex-xvs defs l) (ex-xvs defs (car l))))))

; apply's refusals: fewer than two arguments, never spread
(defthm ex-apway-apply (implies (or (equal (ex-apway tmp) 2) (equal (ex-apway tmp) 3)) (equal (car tmp) :apply))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable ex-apway ex-apentry))))
(defthm ex-mxcall-ap2
  (implies (and (equal (ex-apway tmp) 2) (ex-apok))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel) '(:thrown . :arity)))
  :hints (("Goal" :use ((:instance ex-apok-necc))
                  :in-theory (e/d (ex-mxcall ex-mxcl x2-fn x2-vals x2-spreads ex-apway ex-apentry ex-aperr clop) (ex-apok-necc)))))
; a closure's and no seq: a good spread holds no marker, so its kind is not
; :ok or :hand, or its last value is a closure -- vmx2 does not spread
(defthm ex-ap3-nospread
  (implies (and (equal (ex-apway tmp) 3) (ex-defs-ok defs defs) (ex-lzok defs) (ex-xvs defs tmp))
           (not (x2-spreads :applyv (car tmp) (cdr tmp) defs)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance ex-x2-req-good (g (cadr tmp)))
                        (:instance ex-sk-spread-good (req (ex-varnf (nth 1 (cadr (cadr tmp))))) (fx (butlast (cddr tmp) 1))
                                   (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-no-mk (l (cadr (ex-apsp tmp))))
                        (:instance ex-xvs-noclo (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-last (l (cdr tmp)))
                        (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-xvs-cdr (l tmp)) (:instance ex-xvs-cdr (l (cdr tmp)))
                        (:instance ex-xvs-butlast (l (cddr tmp)) (n 1)))
                  :in-theory (e/d (x2-sp ex-apsp x2-spreads ex-apway ex-apentry ex-seqp ex-clo-shape clop)
                                  (ex-lzok ex-xvs sk-spread ex-sk-spread-good ex-xvs-noclo ex-xvs-last ex-xvs-cdr ex-xvs-butlast
                                   ex-x2-req-good ex-xvs-no-mk ex-xvs-nth1 last butlast ex-varnf x2-req no-mk)))))
(defthm ex-mxcall-ap3
  (implies (and (equal (ex-apway tmp) 3) (ex-apok) (ex-defs-ok defs defs) (ex-lzok defs) (ex-xvs defs tmp) (consp tmp))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel) '(:thrown . :not-seq)))
  :hints (("Goal" :use ((:instance ex-apok-necc) (:instance ex-ap3-nospread) (:instance ex-apway-apply))
                  :in-theory (e/d (ex-mxcall ex-mxcl x2-fn x2-vals ex-aperr clop)
                                  (ex-apok-necc ex-ap3-nospread ex-apway-apply x2-spreads ex-apway ex-defs-ok ex-lzok ex-xvs)))))
; the arity error: a closure with no arity of the count, in the VM no
; clause of it either -- its own, or a hand-over's variadic one as fixed
(defthm ex-mxcl-noarity
  (implies (and (ex-arswf tm ars defs) (not (consp (ex-arity ars (len args)))) (clop f))
           (equal (ex-mxcl f args (ex-clauses tm ars) defs fuel) '(:thrown . :arity)))
  :hints (("Goal" :use ((:instance ex-arswf-arity (n (len args))) (:instance ex-arwf-nat (ar (ex-arity ars (len args)))))
                  :in-theory (e/d (ex-mxcl) (ex-clauses ex-arswf ex-arity ex-arswf-arity ex-arwf-nat ex-arwf)))))
(defthm ex-mxcall-arerr
  (implies (and (ex-arerr (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (ex-defs-ok defs defs) (ex-lzok defs)
                (consp tmp) (ex-xvs defs tmp))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel) '(:thrown . :arity)))
  :hints (("Goal" :cases ((equal (ex-apway tmp) 1)) :do-not-induct t
                  :use ((:instance ex-xvs-nth1 (l tmp) (j 0)) (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-defs-ok-assoc (ds defs) (tm (cadr (car tmp))))
                        (:instance ex-defs-ok-assoc (ds defs) (tm (cadr (cadr tmp))))
                        (:instance ex-apway-spreads))
                  :expand ((ex-xvs defs (list (car tmp))) (ex-xvs defs (list (cadr tmp))))
                  :in-theory (e/d (ex-callee ex-arerr ex-def ex-tmwf clo-f ex-mxcall-noapply ex-mxcall-spread ex-clo-shape clop)
                                  (ex-mxcl ex-mxcall ex-hclo ex-self sk-spread x2-sp x2-spreads ex-apsp ex-arity
                                   ex-xvs-nth1 ex-apway-spreads ex-defs-ok-assoc ex-defs-ok ex-arswf ex-clauses ex-lzok)))))

; A TRY. The runtime's instance? throws nothing (ex-isaok), so the catch
; walk's tests are ex-catchw's: mx2 of the walk is the first matching
; clause's body with the thrown value at p, or the throw again
(defun-sk ex-isaok () (forall (c v) (not (throwp (prim :isa (list c v))))))
(defthm ex-isaok-nothrow (implies (ex-isaok) (not (throwp (prim :isa (list c v)))))
  :hints (("Goal" :use ex-isaok-necc)))
(in-theory (disable ex-isaok))
(defthm ex-catchw-nat (implies (equal (car (ex-catchw cs v j)) 1) (natp (cdr (ex-catchw cs v j))))
  :rule-classes (:rewrite :type-prescription))
(defthm ex-catchw-lo (implies (equal (car (ex-catchw cs v j)) 1) (<= (nfix j) (cdr (ex-catchw cs v j))))
  :rule-classes :linear)
(defthm ex-catchw-hi (implies (equal (car (ex-catchw cs v j)) 1) (< (cdr (ex-catchw cs v j)) (+ (nfix j) (len cs))))
  :rule-classes :linear)
(in-theory (disable ex-catchw))
(defthm ex-nth-diff (implies (and (natp a) (natp b) (< b a)) (equal (nth (- a b) l) (nth (- a (1+ b)) (cdr l))))
  :hints (("Goal" :expand ((nth (- a b) l)))))
(defthm ex-thrown-cons (implies (thrownp r) (equal (cons :thrown (cdr r)) r)))
(defthm ex-val-cons (implies (valp r) (equal (cons :val (cdr r)) r)))
(defun ex-cwind (cs hs j) (if (atom cs) (list hs j) (ex-cwind (cdr cs) (cdr hs) (1+ (nfix j)))))
(defthm ex-mx-trh-j
  (implies (and (ex-isaok) (equal p (len env)) (natp j))
           (equal (mx2 (ex-trh cs hs p) (append env (list v)) caps defs fuel)
                  (if (equal (car (ex-catchw cs v j)) 1)
                      (mx2 (nth (- (cdr (ex-catchw cs v j)) j) hs) (append env (list v)) caps defs fuel)
                    (cons :thrown v))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-cwind cs hs j)
                  :expand ((ex-trh cs hs p) (ex-catchw cs v j)
                           (:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :const x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :throw x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
(defthm ex-mx-trh
  (implies (and (ex-isaok) (equal p (len env)))
           (equal (mx2 (ex-trh cs hs p) (append env (list v)) caps defs fuel)
                  (if (equal (car (ex-catchw cs v 0)) 1)
                      (mx2 (nth (cdr (ex-catchw cs v 0)) hs) (append env (list v)) caps defs fuel)
                    (cons :thrown v))))
  :hints (("Goal" :use ((:instance ex-mx-trh-j (j 0))))))
; the try as mx2 runs it: the body; a throw the walk's clause, else the
; throw; the finally after either, its throw the try's
(defun ex-mxtry (b hs f cs fin env caps defs fuel)
  (let* ((rb (mx2 b env caps defs fuel))
         (rx (if (and (thrownp rb) (equal (car (ex-catchw cs (cdr rb) 0)) 1))
                 (mx2 (nth (cdr (ex-catchw cs (cdr rb) 0)) hs) (append env (list (cdr rb))) caps defs fuel)
               rb)))
    (if (and fin (or (valp rx) (thrownp rx)))
        (let ((mf (mx2 f (append env (list (cdr rx))) caps defs fuel))) (if (valp mf) rx mf))
      rx)))
(defthm ex-mx-trtry
  (implies (and (ex-isaok) (equal p (len env)))
           (equal (mx2 (ex-trtry b hs f cs fin p) env caps defs fuel) (ex-mxtry b hs f cs fin env caps defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-trtry ex-trfin) (ex-trh))
                  :expand ((:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :let x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :try x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :throw x) env caps defs fuel))))))

; A CASE. The runtime's case test throws nothing (ex-caseok), so the
; table's walk is ex-casew's: mx2 of the walk is the taken entry's then,
; else the default -- the branch ex-csbr names, in scope cm ++ (nil)
(defun-sk ex-caseok () (forall (c v) (not (throwp (prim :case (list c v))))))
(defthm ex-caseok-nothrow (implies (ex-caseok) (not (throwp (prim :case (list c v)))))
  :hints (("Goal" :use ex-caseok-necc)))
(in-theory (disable ex-caseok))
(defthm ex-casew-nat (implies (equal (car (ex-casew cs v j)) 1) (natp (cdr (ex-casew cs v j))))
  :rule-classes (:rewrite :type-prescription))
(defthm ex-casew-lo (implies (equal (car (ex-casew cs v j)) 1) (<= (nfix j) (cdr (ex-casew cs v j))))
  :rule-classes :linear)
(defthm ex-casew-hi (implies (equal (car (ex-casew cs v j)) 1) (< (cdr (ex-casew cs v j)) (+ (nfix j) (len cs))))
  :rule-classes :linear)
(defthm ex-mx-trcs-j
  (implies (and (ex-caseok) (equal p (len env)) (natp j))
           (equal (mx2 (ex-trcs cs ts d p) (append env (list v)) caps defs fuel)
                  (if (equal (car (ex-casew cs v j)) 1)
                      (mx2 (nth (- (cdr (ex-casew cs v j)) j) ts) (append env (list v)) caps defs fuel)
                    (mx2 d (append env (list v)) caps defs fuel))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-cwind cs ts j)
                  :in-theory (enable ex-trcs)
                  :expand ((ex-casew cs v j)
                           (:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :const x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
(in-theory (disable ex-casew))
(defthm ex-mx-trcase
  (implies (and (ex-caseok) (consp e) (equal (len env) (len cm)) (equal p (len cm)))
           (equal (mx2 (ex-trcs (ex-c e) (ex-tr :ct e 0 (append cm (list nil))) (ex-tr :m (ex-kid-of e 1) 0 (append cm (list nil))) p)
                       (append env (list v)) caps defs fuel)
                  (mx2 (ex-tr :m (ex-csbr e v) 0 (append cm (list nil))) (append env (list v)) caps defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-csbr) (ex-kid-of ex-tr))
                  :use ((:instance ex-mx-trcs-j (cs (ex-c e)) (ts (ex-tr :ct e 0 (append cm (list nil))))
                                   (d (ex-tr :m (ex-kid-of e 1) 0 (append cm (list nil)))) (p (len cm)) (j 0))))))
(defthm ex-vwf-csbr
  (implies (and (ex-vwf :ct e 0 cm lp defs) (ex-vwf :m (ex-kid-of e 1) 0 cm lp defs) (consp e))
           (ex-vwf :m (ex-csbr e v) 0 cm lp defs))
  :hints (("Goal" :in-theory (e/d (ex-csbr) (ex-kid-of ex-vwf)))))
; what a catch's body or a case's branch clears, the try's or case's clears hold
(defthm ex-clr-cs-nth
  (implies (and (consp e) (natp i) (natp k) (< (+ i k) (len (ex-c e))))
           (subsetp-equal (ex-clr :m (ex-cbody e (+ i k)) 0) (ex-clr :cs e i)))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csind2 k i) :in-theory (disable ex-kid-of ex-clr) :expand ((ex-clr :cs e i)))))
(defthm ex-clr-cs-sub
  (implies (and (consp e) (natp k) (< k (len (ex-c e))))
           (subsetp-equal (ex-clr :m (ex-cbody e k) 0) (ex-clr :cs e 0)))
  :hints (("Goal" :use ((:instance ex-clr-cs-nth (i 0))))))
(defthm ex-clr-ct-nth
  (implies (and (consp e) (natp i) (natp k) (< (+ i k) (len (ex-c e))))
           (subsetp-equal (ex-clr :m (ex-cthen e (+ i k)) 0) (ex-clr :ct e i)))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csind2 k i) :in-theory (disable ex-kid-of ex-clr) :expand ((ex-clr :ct e i)))))
(defthm ex-sub-trans (implies (and (subsetp-equal a b) (subsetp-equal b c)) (subsetp-equal a c)))
(defthm ex-clr-csbr0
  (implies (consp e) (subsetp-equal (ex-clr :m (ex-csbr e v) 0) (append (ex-clr :m (ex-kid-of e 1) 0) (ex-clr :ct e 0))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (ex-csbr) (ex-kid-of ex-clr))
                  :use ((:instance ex-clr-ct-nth (i 0) (k (cdr (ex-casew (ex-c e) v 0))))))))
(defthm ex-clr-csbr
  (implies (and (consp e) (subsetp-equal (append (ex-clr :m (ex-kid-of e 1) 0) (ex-clr :ct e 0)) x))
           (subsetp-equal (ex-clr :m (ex-csbr e v) 0) x))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-sub-app) :use (ex-clr-csbr0 (:instance ex-sub-trans (a (ex-clr :m (ex-csbr e v) 0)) (b (append (ex-clr :m (ex-kid-of e 1) 0) (ex-clr :ct e 0))) (c x))))))
(in-theory (disable ex-sub-trans))
(defthm ex-agree-nil1 (ex-agree (list nil) (list v) fr))

; A COLLECTION. The runtime's vector of the values is seqk's (:vec .
; vals) (prim :vector), and its map or set of good values good, or a good
; throw (ex-collok): so a closure inside a collection is still a good value,
; a call's possible head. A vector of good values is good with no help
; (ex-xvs reads its elements).
(defun-sk ex-collok (defs)
  (forall (vals e) (and (equal (prim :vector vals) (cons :vec vals))
                        (implies (and (ex-xvs defs vals) (member-equal (ex-kind e) '(8 9 22 23)))
                                 (ex-xvs defs (list (cdr (ex-cbuild e vals))))))))
(defthm ex-collok-vector (implies (ex-collok defs) (equal (prim :vector vals) (cons :vec vals)))
  :hints (("Goal" :use ((:instance ex-collok-necc (e nil))) :in-theory (disable ex-cbuild))))
(defthm ex-xvs-vec (implies (ex-xvs defs vals) (ex-xvs defs (list (cons :vec vals))))
  :hints (("Goal" :expand ((ex-xvs defs (list (cons :vec vals))) (ex-xvs defs (cons :vec vals))))))
(defthm ex-collok-good
  (implies (and (ex-collok defs) (ex-xvs defs vals) (member-equal (ex-kind e) '(7 8 9 22 23))) (ex-xvs defs (list (cdr (ex-cbuild e vals)))))
  :hints (("Goal" :use ex-collok-necc :in-theory (disable ex-cbuild))
          (and stable-under-simplificationp '(:in-theory (enable ex-cbuild)))))
; ... and as mx2 answers it, the build opened: a map's, a set's, a new's
(defthm ex-collok-prim
  (implies (and (ex-collok defs) (ex-xvs defs vals) (member-equal op '(:map :set)))
           (and (implies (not (throwp (prim op vals))) (ex-xvs defs (list (prim op vals))))
                (implies (throwp (prim op vals)) (ex-xvs defs (list (cdr (prim op vals)))))))
  :hints (("Goal" :use ((:instance ex-collok-good (e '(8))) (:instance ex-collok-good (e '(9)))))))
(defthm ex-collok-new
  (implies (and (ex-collok defs) (ex-xvs defs vals) (member-equal k '(22 23)))
           (and (implies (not (throwp (prim (list :new k c) vals))) (ex-xvs defs (list (prim (list :new k c) vals))))
                (implies (throwp (prim (list :new k c) vals)) (ex-xvs defs (list (cdr (prim (list :new k c) vals)))))))
  :hints (("Goal" :use ((:instance ex-collok-necc (e (list k nil nil c))))
                  :in-theory (e/d (ex-cbuild ex-cop ex-kind ex-c) (ex-collok ex-collok-good ex-collok-necc ex-xvs)))))
(in-theory (disable ex-collok))

(defun ex-vhyp (flg e i tmp cm env fr lp defs)
  (and (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs)
       (if (equal flg :iter)
           (and (consp lp) (ex-vwf :m e 0 (append cm (ex-lsl lp)) lp defs)
                (ex-agree (append cm (ex-lsl lp)) (append env tmp) fr)
                (ex-nomem (ex-lsl lp) cm) (equal (len env) (len cm)) (ex-xvs defs (append env tmp))
                (or (ex-nomem (ex-clr :m e 0) cm) (ex-vwf :m e 0 (append cm (ex-lsl lp)) nil defs)))
         (and (member-equal flg '(:m :do :let :rec :call :coll :fin)) (ex-vwf flg e i cm lp defs) (ex-agree cm env fr)
              (ex-xvs defs env)
              (or (not (equal flg :rec)) (and (true-listp tmp) (equal (len tmp) (nfix i)) (ex-xvs defs tmp)))
              (or (not (equal flg :call)) (and (consp tmp) (true-listp tmp) (ex-xvs defs tmp)))
              (or (not (equal flg :coll)) (and (true-listp tmp) (ex-xvs defs tmp)))
              (or (not (equal flg :fin))
                  (and (or (valp (car tmp)) (thrownp (car tmp))) (ex-xvs defs (list (val (car tmp))))))))))

(defun ex-vpost (flg e i tmp cm env lp caps defs fuel r)
  (let ((res (car r)) (fr2 (cadr r)) (ls (ex-lsl lp)))
    (case flg
      (:iter (implies (or (valp res) (thrownp res))
                      (and (equal (mx2-loop (list :loop nil (ex-tr :m e 0 (append cm ls))) env tmp caps defs fuel) res)
                           (ex-agree (ex-blank (ex-clr :m e 0) cm) env fr2) (ex-xvs defs (list (val res))))))
      (:rec (let ((m (mx2-args (ex-tr :rec e i cm) env caps defs fuel)))
              (and (implies (equal (car res) :recur)
                            (and (valp m) (ex-agree (cdr ls) (append tmp (val m)) fr2)
                                 (ex-agree (ex-blank ls (ex-blank (ex-clr :rec e i) cm)) env fr2) (ex-xvs defs (append tmp (val m)))))
                   (implies (thrownp res)
                            (and (equal m res) (ex-agree (ex-blank (ex-clr :rec e i) cm) env fr2) (ex-xvs defs (list (val res))))))))
      (:call (let ((m (mx2-args (ex-tr :call e i cm) env caps defs fuel)))
               (and (implies (valp res)
                             (and (valp m) (equal (ex-mxcall (car tmp) (append (cdr tmp) (val m)) defs fuel) res)
                                  (ex-agree (ex-blank (ex-clr flg e i) cm) env fr2) (ex-xvs defs (list (val res)))))
                    (implies (thrownp res)
                             (and (equal (if (valp m) (ex-mxcall (car tmp) (append (cdr tmp) (val m)) defs fuel) m) res)
                                  (ex-agree (ex-blank (ex-clr flg e i) cm) env fr2) (ex-xvs defs (list (val res))))))))
      (:coll (let ((m (mx2-args (ex-tr :coll e i cm) env caps defs fuel)))
               (and (not (equal (car res) :recur))
                    (implies (or (valp res) (thrownp res))
                             (and (equal (if (valp m) (ex-cbuild e (append tmp (val m))) m) res)
                                  (ex-agree (ex-blank (ex-clr flg e i) cm) env fr2) (ex-xvs defs (list (val res))))))))
      (:fin (let ((mf (mx2 (ex-tr :fin e 0 cm) (append env (list (val (car tmp)))) caps defs fuel)))
              (and (not (equal (car res) :recur))
                   (implies (or (valp res) (thrownp res))
                            (and (equal (if (< 1 (ex-nk e)) (if (valp mf) (car tmp) mf) (car tmp)) res)
                                 (ex-agree (ex-blank (ex-clr :fin e 0) cm) env fr2) (ex-xvs defs (list (val res))))))))
      (otherwise
       (let ((m (mx2 (ex-tr flg e i cm) env caps defs fuel)))
         (and (implies (or (valp res) (thrownp res))
                       (and (equal m res) (ex-xvs defs (list (val res)))
                            (if (and (equal flg :let) (equal (ex-kind e) 12))
                                (ex-agree (ex-blank (ex-lsl (cons (ex-s2 e) (ex-i2 e))) (ex-blank (ex-clr flg e i) cm)) env fr2)
                              (ex-agree (ex-blank (ex-clr flg e i) cm) env fr2))))
              (implies (equal (car res) :recur)
                       (and (consp lp) (equal (car m) :recur) (ex-agree ls (cdr m) fr2)
                            (ex-agree (ex-blank ls (ex-blank (ex-clr flg e i) cm)) env fr2) (ex-xvs defs (cdr m))))))))))

(defun ex-vgood (flg e i tmp cm env fr fuel caps defs lp)
  (implies (ex-vhyp flg e i tmp cm env fr lp defs)
           (ex-vpost flg e i tmp cm env lp caps defs fuel
                     (ex-ev flg e i (if (equal flg :iter) nil tmp) fr fuel))))

(set-irrelevant-formals-ok t)
(defun ex-vind (flg e i tmp cm env fr fuel caps defs lp)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        (list tmp)
      (case flg
        (:iter (let* ((bcm (append cm (ex-lsl lp))) (benv (append env tmp))
                      (r (ex-ev :m e 0 nil fr fuel))
                      (m (mx2 (ex-tr :m e 0 bcm) benv caps defs fuel)))
                 (if (zp fuel)
                     (ex-vind :m e 0 nil bcm benv fr fuel caps defs lp)
                   (list (ex-vind :m e 0 nil bcm benv fr fuel caps defs lp) (ex-vind :m e 0 nil bcm benv fr fuel caps defs nil)
                         (ex-vind :iter e 0 (cdr m) cm env (cadr r) (1- fuel) caps defs lp)))))
        (:do (cond ((zp nk) nil)
                   ((< i (- nk 1))
                    (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                            (ex-vind :do e (1+ i) tmp (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) env (cadr r) fuel caps defs lp))))
                   (t (ex-vind :m (ex-kid-of e (- nk 1)) 0 nil cm env fr fuel caps defs lp))))
        (:let (cond ((< i n2)
                     (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                       (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                             (ex-vind :let e (1+ i) tmp (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list (+ (ex-s2 e) i))) (append env (list (val (car r))))
                                      (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel caps defs lp))))
                    ((equal k 12)
                     (let* ((ls (cons nil (ex-slots (ex-s2 e) n2)))
                            (vs (val (mx2-args (ex-locals (cdr ls) cm) env caps defs fuel))))
                       (ex-vind :iter (ex-kid-of e n2) 0 (cons nil vs) (ex-blank ls cm) env fr fuel caps defs
                                (cons (ex-s2 e) n2))))
                    (t (ex-vind :m (ex-kid-of e n2) 0 nil cm env fr fuel caps defs lp))))
        (:rec (if (< i nk)
                  (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                          (ex-vind :rec e (1+ i) (append tmp (list (val (car r)))) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) env (cadr r) fuel caps defs lp)))
                nil))
        (:call (cond ((< i nk)
                      (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                        (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                              (ex-vind :call e (1+ i) (append tmp (list (val (car r)))) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) env (cadr r) fuel caps defs lp))))
                     ((zp fuel) nil)
                     (t (let* ((f (car (ex-callee tmp))) (args (cdr (ex-callee tmp))) (ar (ex-car f args)))
                          (ex-vind :iter (ex-fbody f (len args)) 0 (cons nil (ex-fvs f args)) (ex-fcm (ex-ftm f) ar)
                                   (ex-fenv f args) (ex-bind f args) (1- fuel) (caddr f) defs
                                   (cons (ex-astart ar) (ex-anp ar)))))))
        (:coll (if (< i nk)
                   (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                           (ex-vind :coll e (1+ i) (append tmp (list (val (car r)))) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) env (cadr r) fuel caps defs lp)))
                 nil))
        (:fin (if (< 1 nk)
                  (ex-vind :m (ex-kid-of e 1) 0 nil (append cm (list nil)) (append env (list (val (car tmp)))) fr fuel caps defs nil)
                nil))
        (otherwise
         (cond ((equal k 4)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                        (ex-vind :m (ex-kid-of e 1) 0 nil (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) env (cadr r) fuel caps defs lp)
                        (ex-vind :m (ex-kid-of e 2) 0 nil (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) env (cadr r) fuel caps defs lp))))
               ((equal k 5) (ex-vind :do e 0 nil cm env fr fuel caps defs lp))
               ((or (equal k 11) (equal k 12)) (ex-vind :let e 0 nil cm env fr fuel caps defs lp))
               ((equal k 16) (ex-vind :rec e 0 nil cm env fr fuel caps defs lp))
               ((equal k 17) (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil))
               ((equal k 18)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (cond ((valp (car r))
                         (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                               (ex-vind :fin e 0 (list (car r) (c+ 1 (caddr r))) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) env (cadr r) fuel caps defs nil)))
                        ((not (ex-thp (car r))) (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil))
                        ((equal (car (ex-catchw (ex-c e) (val (car r)) 0)) 1)
                         (let* ((j (cdr (ex-catchw (ex-c e) (val (car r)) 0)))
                                (fr1 (update-nth (ex-cslot e j) (val (car r)) (cadr r)))
                                (rh (ex-ev :m (ex-cbody e j) 0 nil fr1 fuel)))
                           (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                                 (ex-vind :m (ex-cbody e j) 0 nil (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list (ex-cslot e j)))
                                          (append env (list (val (car r)))) fr1 fuel caps defs nil)
                                 (ex-vind :fin e 0 (list (car rh) (c+ 1 (c+ (caddr r) (c+ 1 (caddr rh))))) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) env (cadr rh)
                                          fuel caps defs nil))))
                        (t (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                                 (ex-vind :fin e 0 (list (car r) (c+ 1 (caddr r))) (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) env (cadr r) fuel caps defs nil))))))
               ((member k '(7 8 9 22 23)) (ex-vind :coll e 0 nil cm env fr fuel caps defs nil))
               ((equal k 19)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                        (ex-vind :m (ex-csbr e (val (car r))) 0 nil (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append env (list (val (car r))))
                                 (cadr r) fuel caps defs lp))))
               ((equal k 6)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                        (ex-vind :call e 1 (list (val (car r))) (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) (append env (list (val (car r))))
                                 (cadr r) fuel caps defs lp))))
               (t nil)))))))

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
; NEW (milestone 5): its arguments a collection's elements, the build (prim (:new k C))
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
(ex-old ex-vgood-leaf-plain ((consp e) (ex-mflg) (not (member-equal (ex-kind e) '(4 5 6 7 8 9 11 12 16 17 18 19 22 23)))
                         (not (and (equal (ex-kind e) 2) (ex-mark e)))) ())
; a marked read (milestone 4): its slot cleared, blanked in the scope after
(ex-old ex-vgood-m-mark ((consp e) (ex-mflg) (equal (ex-kind e) 2) (ex-mark e)) ())
(defthm ex-vgood-m-leaf
  (implies (and (consp e) (ex-mflg) (not (member-equal (ex-kind e) (quote (4 5 6 7 8 9 11 12 16 17 18 19 22 23)))))
           (ex-vgood flg e i tmp cm env fr fuel caps defs lp))
  :hints (("Goal" :do-not-induct t :in-theory (disable ex-vgood ex-kid-of) :use (ex-vgood-leaf-plain ex-vgood-m-mark))))
(in-theory (disable ex-vgood-m-leaf))
(in-theory (enable ex-vgood-atom ex-vgood-iter-zp ex-vgood-iter ex-vgood-do-none ex-vgood-do-mid ex-vgood-do-last
                   ex-vgood-let-mid ex-vgood-let-loop ex-vgood-let-body ex-vgood-rec-mid ex-vgood-rec-end
                   ex-vgood-call-mid ex-vgood-call-zp ex-vgood-call-enter ex-vgood-fin ex-vgood-fin-end
                   ex-vgood-m-if ex-vgood-m-do ex-vgood-m-let ex-vgood-m-rec ex-vgood-m-throw ex-vgood-m-call ex-vgood-m-leaf
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

; THE DEFS ARE THE VM'S: every clause's body x2wf at its locals (vmx2's x2defs-ok)
(defthm ex-xwf-capts (x2wf-args (ex-capts j m) n))
(defun ex-clets-ind2 (j m n) (if (zp m) n (ex-clets-ind2 (1+ (nfix j)) (1- m) (1+ n))))
(defthm ex-xwf-clets (implies (natp n) (equal (x2wf (ex-clets j m x) n k) (x2wf x (+ n (nfix m)) k)))
  :hints (("Goal" :induct (ex-clets-ind2 j m n) :expand ((:free (y n) (x2wf (cons :let y) n k))))))
(defthm ex-len-fbcm (equal (len (ex-fbcm tm ar)) (+ (ex-anp ar) (len (ex-inners (nth 2 tm))) 1))
  :hints (("Goal" :in-theory (enable ex-fbcm))))
(defthm ex-len-fcm (equal (len (ex-fcm tm ar)) (len (ex-fbcm tm ar))) :hints (("Goal" :in-theory (enable ex-fcm))))
(defthm ex-params-sub (subsetp-equal (ex-fparams ar) (ex-fbcm tm ar)) :hints (("Goal" :in-theory (enable ex-fbcm))))
(defthm ex-len-fparams (equal (len (ex-fparams ar)) (ex-anp ar)))
(defthm ex-arwf-vwf
  (implies (ex-arwf tm ar defs) (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) (ex-flp ar) defs))
  :hints (("Goal" :in-theory (enable ex-arwf))))
(defthm ex-fbtr-xwf
  (implies (ex-arwf tm ar defs) (x2wf (ex-fbtr tm ar) (ex-anp ar) nil))
  :hints (("Goal" :in-theory (e/d (ex-fbtr) (ex-tr-xwf ex-fparams ex-arwf-vwf))
                  :use ((:instance ex-tr-xwf (e (ex-abody ar)) (cm (ex-fcmb tm ar)) (lp (ex-flp ar))) ex-arwf-vwf
                        (:instance ex-locals-xwf (ls (ex-fparams ar)) (cm (ex-fbcm tm ar))))
                  :expand ((:free (y n) (x2wf (cons :let y) n nil)) (:free (y n k) (x2wf (cons :loop y) n k))
                           (:free (y n) (x2wf (cons :mkclo y) n nil)) (:free (x y n) (x2wf-args (cons x y) n))))))
(defthm ex-clauses-ok (implies (ex-arswf tm ars defs) (clauses-ok (ex-clauses tm ars)))
  :hints (("Goal" :in-theory (e/d (ex-clause ex-anp ex-anf ex-avar ex-arwf) (ex-fbtr-xwf))
                  :induct (ex-clauses tm ars))
          ("Subgoal *1/2" :use ((:instance ex-fbtr-xwf (ar (car ars)))))))
(defthm ex-defs-xdefs (implies (ex-defs-ok ds defs) (x2defs-ok ds))
  :hints (("Goal" :in-theory (enable ex-def ex-tmwf))))

; A FN'S CLAUSES, GENERATED (src/f/gen/vm_tr_gen.inc, scripts/acl2-fortran
; -b vmtrg, which loads this book): vm.inc's vm_clause and the arity-error
; clause of vm_compile_fn, at the level the Fortran is generated from,
; guard-verified, over vmtrg's builder and scope.
;
; vtg-clause: one arity's clause, (n body) or (n body :rest) -- exec-vmtr's
; ex-clause: the body ex-fbtc's, the self slot's let round the loop (when
; the body recurs to the fn, vtg-tlr) or the body, the captures read in place.
; The scope is made first by vtg-scope (vm_clause: the parameters, the
; captures read in place, the self slot: ex-fbcm, vtg-scope-fbcm, at the
; end of this book; vtb-cs the counts, the host's), as vm_tr_gen does for
; vtg-tr. Three shims more: vtg-num a number pushed, vtg-key a
; keyword, vtg-self the self let's value.
; NAMED, not exact (exec-PLAN Lane 3 item 2): vtg_self pushes vm.inc's
; (:capt m) -- the runtime's closure, which holds itself past its captures
; (VmRuntime rt_capt) -- where the model remakes it, (:mkclo tm (:capt 0)
; ..). vtg-clause-ex-clause is at sl 1.
; Gap B closed (the sl-0 clause, no self let, the scope ex-fbcm0 with no
; self position): vtg-clause-ex-clause0, vtg_clause at sl 0 builds
; ex-clause0; ex-fbtc0-mx, ex-clause0's body answers as ex-clause's
; (ex-fbtc) at every args env, by vmshift's x2-drop-mx, ex-cs-sh and
; ex-fbody-drop/ex-floop-drop.
; The sl decision, PROVED (exec-PLAN Lane 3 item 9): vm_clause's sl is
; vtg-sl, generated -- 1 when the body reads or binds the self slot
; (vmtrg's vtg-rds), else 0 -- and vtg-sl-fbinr: on a body vtg-scan takes,
; sl 0 gives ex-fbtc0-mx's hypothesis (not (x2-rd (ex-fnp tm ar) (ex-fbinr
; tm ar))), the body's translation never reading the self slot's position
; (ex-tr-nord: ex-tr reads no position whose slot the tree never reads nor
; binds, the position's entry blanked or not), so vtg-sl-fbtc0-mx: the
; sl-0 clause answers as ex-clause's. NAMED: vm_clause's self_slot is
; ex-fself tm (-1 when it has none).
;
; vtg-fncl: vm_compile_fn's clause list, generated -- each arity's clause
; in order (vtg_arity, vm_clause, a shim), then vtg-arcl, one list:
; vtg-fncl-clauses, (append (ex-clauses tm ars) (list (ex-arcl name))).
; Named in the section below.
;
; vtg-arcl: the last clause, a call of no arity the fn has --
; (0 (:prim :clotran.vm/arity (:const name) (:local 0)) :rest), ex-arcl.
; ex-arcl-mxcl: a callee's clauses with it appended answer as without for
; a count some clause takes, and else throw the prim's throw where
; exec-vmcall's ex-mxcl throws :arity -- clj's ArityException, the host's
; (vm_arity_hook), under the named hypothesis that the prim throws.
;
; Cost: vtg-clause-steps-bound (at sl 0 two less, vtg-clause-steps-sl0),
; vtg-arcl-steps-bound (11).

(in-package "ACL2")

(include-book "vmtrg")
(include-book "exec-vmcall")

; ---- THE SHIMS --------------------------------------------------------------------------------

; a number (vtg_num: gc_int), a keyword (vtg_key: vm_kw), the self let's value (vtg_self)
(defun vtg-num (n vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push n vtb))
(defun vtg-kw (j) (declare (xargs :guard t)) (case j (0 :rest) (1 :clotran.vm/arity) (2 :prim) (otherwise :local)))
(defun vtg-key (j vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (vtg-kw j) vtb))
(defun vtg-self (tm m vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (list* :mkclo tm (ec-call (ex-capts 0 m))) vtb))

; ---- THE CLAUSES ------------------------------------------------------------------------------

; arity (nf, var 1 variadic, its parameters slots s..), its body; sl 1 the
; self let; m the captures
(defun vtg-clause (nf var s body tm sl m vtb)
  (declare (xargs :stobjs vtb
                  :guard (and (natp nf) (natp s) (natp var) (natp sl) (< (+ 1 nf) *vtg40*) (< s *vtg40*))))
  (let* ((np (if (equal var 0) nf (+ 1 nf)))
         (vtb (vtg-num nf vtb))
         (vtb (if (equal sl 0) vtb (vtg-self tm m vtb)))
         (vtb (if (vtg-tlr body)
                  ; (:loop ((:local p) ..) body): the parameters the loop's
                  (let* ((vtb (vtg-locs s 0 np vtb))
                         (vtb (vtg-node 0 np vtb))
                         (vtb (vtg-save vtb))
                         (vtb (vtg-binds s np vtb))
                         (vtb (vtg-tr 0 body 0 vtb))
                         (vtb (vtg-restore vtb)))
                    (vtg-node 4 2 vtb))
                (vtg-tr 0 body 0 vtb)))
         (vtb (if (equal sl 0) vtb (vtg-node 2 2 vtb))))
    (if (equal var 0) (vtg-node 0 2 vtb) (let ((vtb (vtg-key 0 vtb))) (vtg-node 0 3 vtb)))))

; a call of no arity the fn has: the prim's, clj's ArityException
(defun ex-arcl (name) (list 0 (list :prim :clotran.vm/arity (list :const name) '(:local 0)) :rest))
(defun vtg-arcl (name vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let* ((vtb (vtg-num 0 vtb))
         (vtb (vtg-key 2 vtb))
         (vtb (vtg-key 1 vtb))
         (vtb (vtg-const name vtb))
         (vtb (vtg-key 3 vtb))
         (vtb (vtg-num 0 vtb))
         (vtb (vtg-node 0 2 vtb))
         (vtb (vtg-node 0 4 vtb))
         (vtb (vtg-key 0 vtb)))
    (vtg-node 0 3 vtb)))

; ---- IT IS EX-CLAUSE --------------------------------------------------------------------------

(defthm vtcl-shims
  (and (equal (vtg-num n (vtg-st s c sv cs)) (vtg-st (cons n s) c sv cs))
       (equal (vtg-key j (vtg-st s c sv cs)) (vtg-st (cons (vtg-kw j) s) c sv cs))
       (equal (vtg-self tm m (vtg-st s c sv cs)) (vtg-st (cons (list* :mkclo tm (ex-capts 0 m)) s) c sv cs)))
  :hints (("Goal" :in-theory (enable vtg-st))))
(defthm vtcl-nodes
  (and (equal (vtg-node 0 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list x y) s) c sv cs))
       (equal (vtg-node 0 3 (vtg-st (list* z y x s) c sv cs)) (vtg-st (cons (list x y z) s) c sv cs))
       (equal (vtg-node 0 4 (vtg-st (list* w z y x s) c sv cs)) (vtg-st (cons (list x y z w) s) c sv cs)))
  :hints (("Goal" :in-theory (enable vtg-node vtg-st) :expand ((:free (n l acc) (vtg-popn n l acc))))))
(defthm vtcl-cs-capts (equal (ex-cs t (ex-capts j m) np k) (ex-capts j m))
  :hints (("Goal" :induct (ex-capts j m) :in-theory (enable ex-cs))))
(defthm vtcl-cs-mkclo (equal (ex-cs nil (list* :mkclo tm x) np m) (list* :mkclo tm (ex-cs t x np m)))
  :hints (("Goal" :in-theory (enable ex-cs))))
(defthm vtcl-true-fbcm (true-listp (ex-fbcm tm ar)))
(defthm vtcl-true-locals (true-listp (ex-cs t (ex-locals ls c) np m)))
(in-theory (disable vtg-num vtg-key vtg-self vtg-kw ex-fbcm))

(defthm vtg-clause-st
  (implies (and (vtg-frag 0 (ex-abody ar) 0) (vtg-tlr-ok (ex-abody ar)) (natp (ex-astart ar))
                (equal c (ex-fbcm tm ar)) (equal cs (cons (ex-anp ar) (len (ex-inners (nth 2 tm))))))
           (equal (vtg-clause (ex-anf ar) (if (ex-avar ar) 1 0) (ex-astart ar) (ex-abody ar) tm 1 (len (ex-inners (nth 2 tm)))
                              (vtg-st s c sv cs))
                  (vtg-st (cons (ex-clause tm ar) s) c sv cs)))
  :hints (("Goal" :in-theory (e/d (ex-anp ex-clause ex-fbtc ex-fbin ex-fparams ex-fcmb ex-fcm ex-flp ex-lsl vtg-np vtg-nm vtg-kw)
                                  (vtg-tr ex-tr ex-abody ex-astart ex-anf ex-avar ex-locals ex-slots ex-blank ex-capts))
                  :use ((:instance vtg-node-rev (op 0) (n (ex-anp ar)) (c (ex-fbcm tm ar))
                                   (l (ex-cs t (ex-locals (ex-slots (ex-astart ar) (ex-anp ar)) (ex-fbcm tm ar))
                                             (ex-anp ar) (len (ex-inners (nth 2 tm)))))
                                   (s (list* (list* :mkclo tm (ex-capts 0 (len (ex-inners (nth 2 tm))))) (ex-anf ar) s))
                                   (sv sv) (cs cs))))))

(defthm vtg-clause-ex-clause
  (implies (and (vtg-frag 0 (ex-abody ar) 0) (vtg-tlr-ok (ex-abody ar)) (natp (ex-astart ar)) (vtbp vtb)
                (equal (vtb-cm vtb) (ex-fbcm tm ar)) (equal (vtb-cs vtb) (cons (ex-anp ar) (len (ex-inners (nth 2 tm))))))
           (let ((vtb2 (vtg-clause (ex-anf ar) (if (ex-avar ar) 1 0) (ex-astart ar) (ex-abody ar) tm 1 (len (ex-inners (nth 2 tm))) vtb)))
             (and (equal (vtb-stk vtb2) (cons (ex-clause tm ar) (vtb-stk vtb)))
                  (equal (vtb-cm vtb2) (vtb-cm vtb)) (equal (vtb-sv vtb2) (vtb-sv vtb)) (equal (vtb-cs vtb2) (vtb-cs vtb)))))
  :hints (("Goal" :use ((:instance vtg-clause-st (s (vtb-stk vtb)) (c (vtb-cm vtb)) (sv (vtb-sv vtb)) (cs (vtb-cs vtb))))
                  :in-theory (disable vtg-clause-st vtg-clause vtb-stk vtb-cm vtb-sv vtb-cs vtbp))))

(defthm vtg-arcl-st (equal (vtg-arcl name (vtg-st s c sv cs)) (vtg-st (cons (ex-arcl name) s) c sv cs))
  :hints (("Goal" :in-theory (enable vtg-kw))))
(defthm vtg-arcl-ex-arcl
  (implies (vtbp vtb)
           (and (equal (vtb-stk (vtg-arcl name vtb)) (cons (ex-arcl name) (vtb-stk vtb)))
                (equal (vtb-cm (vtg-arcl name vtb)) (vtb-cm vtb)) (equal (vtb-sv (vtg-arcl name vtb)) (vtb-sv vtb))
                (equal (vtb-cs (vtg-arcl name vtb)) (vtb-cs vtb))))
  :hints (("Goal" :use ((:instance vtg-arcl-st (s (vtb-stk vtb)) (c (vtb-cm vtb)) (sv (vtb-sv vtb)) (cs (vtb-cs vtb))))
                  :in-theory (disable vtg-arcl-st vtg-arcl vtb-stk vtb-cm vtb-sv vtb-cs vtbp))))

; ---- THE ARITY CLAUSE ANSWERS EX-MXCL ---------------------------------------------------------

(defthm vtcl-pick-fixed-app (equal (pick-fixed (append cls (list (ex-arcl name))) m) (pick-fixed cls m)))
(defthm vtcl-pick-rest-app
  (implies (natp m) (equal (pick-rest (append cls (list (ex-arcl name))) m) (if (pick-rest cls m) (pick-rest cls m) (ex-arcl name)))))
(defthm ex-arcl-pick
  (implies (natp m) (equal (pick-arity (append cls (list (ex-arcl name))) m) (if (pick-arity cls m) (pick-arity cls m) (ex-arcl name))))
  :hints (("Goal" :in-theory (e/d (pick-arity) (pick-fixed pick-rest ex-arcl)))))
(defthm ex-arcl-body
  (equal (mx2 (cadr (ex-arcl name)) env caps defs fuel)
         (let ((a (prim :clotran.vm/arity (list name (nth 0 env))))) (if (throwp a) (cons :thrown (cdr a)) (cons :val a))))
  :hints (("Goal" :in-theory (disable throwp)
                  :expand ((mx2 (cadr (ex-arcl name)) env caps defs fuel) (mx2 (list :const name) env caps defs fuel)
                           (mx2 '(:local 0) env caps defs fuel)
                           (mx2-args (list (list :const name) '(:local 0)) env caps defs fuel)
                           (mx2-args (list '(:local 0)) env caps defs fuel) (mx2-args nil env caps defs fuel)))))
(defthm ex-arcl-parts (and (consp (ex-arcl name)) (restp (ex-arcl name)) (equal (caddr (ex-arcl name)) :rest) (equal (car (ex-arcl name)) 0)))
(defthm ex-arcl-mxcl
  (implies (and (not (zp fuel)) (true-listp args) (throwp (prim :clotran.vm/arity (list name args))))
           (equal (ex-mxcl f args (append cls (list (ex-arcl name))) defs fuel)
                  (if (or (not (clop f)) (pick-arity cls (len args)))
                      (ex-mxcl f args cls defs fuel)
                    (cons :thrown (cdr (prim :clotran.vm/arity (list name args)))))))
  :hints (("Goal" :use ((:instance ex-arcl-body (env (list args)) (caps (clo-caps f)) (fuel (1- fuel))))
                  :in-theory (e/d (ex-mxcl split-rest) (pick-arity mx2 ex-arcl-body throwp ex-arcl)))))

; ---- THE COST ---------------------------------------------------------------------------------
;
; vtg-clause's work: a step a shim and the call, vtg_tlr's (vtg-tlr-steps),
; the loop's np reads (vtg-locs), np binds (vtg_binds) and vtg_tr's
; (vtg-steps). vtg-clause-steps-bound: linear in the body and the arity.
(defun vtg-clause-steps (nf var body sl)
  (let ((np (if (equal var 0) (nfix nf) (+ 1 (nfix nf)))))
    (+ 8 (if (equal sl 0) 0 2) (vtg-tlr-steps body)
       (if (vtg-tlr body) (+ 6 np np np (vtg-steps 0 body 0)) (+ 1 (vtg-steps 0 body 0))))))
(defthm vtg-clause-steps-bound
  (<= (vtg-clause-steps nf var body sl)
      (+ 16 (* 3 (+ 1 (nfix nf))) (* 5 (vtg-tlr-size body)) (* 16 (vtg-size 0 body 0))))
  :rule-classes :linear)
; vtg-arcl's: its ten shims and the call, whatever the name
(defun vtg-arcl-steps (name) (declare (ignore name)) 11)
(defthm vtg-arcl-steps-bound (<= (vtg-arcl-steps name) 11) :rule-classes :linear)

; ---- GAP B: THE SL-0 CLAUSE -------------------------------------------------------------------
;
; vm_clause passes sl 0 -- no self let, and no self position in the scope
; (ex-fbcm0) -- when the body never reads the self slot. ex-clause0 is that
; clause; vtg-clause-ex-clause0 the generated vtg_clause at sl 0 builds it,
; and ex-fbtc0-mx: its body answers as ex-clause's (ex-fbtc), the self let
; dropped, when the body's translation never reads the self slot's position
; (ex-fnp) -- vmshift's lemmas (2) ex-fbody-drop/ex-floop-drop, (a) ex-cs-sh
; and (1) x2-drop-mx.

(include-book "vmshift")

(defun ex-fbinr (tm ar)
  (if (ex-tlr :m (ex-abody ar) 0)
      (list :loop (ex-locals (ex-fparams ar) (ex-fbcm tm ar)) (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))
    (ex-tr :m (ex-abody ar) 0 (ex-fbcm tm ar))))
(defun ex-fbin0 (tm ar)
  (if (ex-tlr :m (ex-abody ar) 0)
      (list :loop (ex-locals (ex-fparams ar) (ex-fbcm0 tm ar)) (ex-tr :m (ex-abody ar) 0 (ex-fcmb0 tm ar)))
    (ex-tr :m (ex-abody ar) 0 (ex-fbcm0 tm ar))))
(defun ex-fbtc0 (tm ar) (ex-cs nil (ex-fbin0 tm ar) (ex-anp ar) (len (ex-inners (nth 2 tm)))))
(defun ex-clause0 (tm ar)
  (if (ex-avar ar) (list (ex-anf ar) (ex-fbtc0 tm ar) :rest) (list (ex-anf ar) (ex-fbtc0 tm ar))))

(defthm ex-fbin-body
  (equal (ex-fbin tm ar) (list :let (list* :mkclo tm (ex-capts 0 (len (ex-inners (nth 2 tm))))) (ex-fbinr tm ar)))
  :hints (("Goal" :in-theory (enable ex-fbin))))
(defthm ex-fbin0-sh
  (implies (not (x2-rd (ex-fnp tm ar) (ex-fbinr tm ar)))
           (equal (x2-sh (ex-fnp tm ar) (ex-fbinr tm ar)) (ex-fbin0 tm ar)))
  :hints (("Goal" :in-theory (e/d () (ex-fnp ex-fbcm ex-fbcm0 ex-fcmb ex-fcmb0 ex-tr ex-locals ex-fparams ex-tlr ex-abody))
                  :expand ((:free (np) (x2-sh np (list :loop (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                                       (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))))
                           (:free (np) (x2-rd np (list :loop (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                                       (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))))))))

(defthm vtcl-capts-mx
  (equal (mx2-args (ex-capts j m) env caps defs fuel) (cons :val (ex-nths j m caps)))
  :hints (("Goal" :induct (ex-capts j m) :expand ((:free (j) (mx2 (list :capt j) env caps defs fuel))))))

; THE SL-0 BODY ANSWERS AS THE SL-1 BODY: the args env, the self let dropped
(defthm ex-fbtc0-sh
  (implies (not (x2-rd (ex-fnp tm ar) (ex-fbinr tm ar)))
           (and (equal (ex-fbtc0 tm ar) (x2-sh (ex-anp ar) (ex-cs nil (ex-fbinr tm ar) (ex-anp ar) (len (ex-inners (nth 2 tm))))))
                (not (x2-rd (ex-anp ar) (ex-cs nil (ex-fbinr tm ar) (ex-anp ar) (len (ex-inners (nth 2 tm))))))))
  :hints (("Goal" :in-theory (e/d (ex-fnp) (ex-fbinr ex-fbin0 ex-fbin0-sh ex-cs-sh ex-anp))
                  :use (ex-fbin0-sh (:instance ex-cs-sh (np (ex-anp ar)) (m (len (ex-inners (nth 2 tm)))) (e (ex-fbinr tm ar)))))))
(defthm ex-fbtc0-mx
  (implies (and (not (x2-rd (ex-fnp tm ar) (ex-fbinr tm ar))) (equal (len env) (ex-anp ar)) (true-listp env))
           (equal (mx2 (ex-fbtc0 tm ar) env caps defs fuel) (mx2 (ex-fbtc tm ar) env caps defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-fbtc) (ex-fbtc0 ex-fbinr ex-fnp ex-anp x2-drop-mx mx2 ex-cs-sh ex-fbin0-sh))
                  :expand ((:free (x y) (mx2 (list :let x y) env caps defs fuel))
                           (:free (x) (mx2 (list* :mkclo tm x) env caps defs fuel)))
                  :use ((:instance x2-drop-mx (a env) (b nil) (np (ex-anp ar))
                                   (x (clo tm (ex-nths 0 (len (ex-inners (nth 2 tm))) caps)))
                                   (e (ex-cs nil (ex-fbinr tm ar) (ex-anp ar) (len (ex-inners (nth 2 tm))))))))))

; THE GENERATED CLAUSE AT SL 0 IS EX-CLAUSE0: vm_clause's scope then ex-fbcm0
(defthm vtcl-true-fbcm0 (true-listp (ex-fbcm0 tm ar)))
(defthm vtg-clause-st0
  (implies (and (vtg-frag 0 (ex-abody ar) 0) (vtg-tlr-ok (ex-abody ar)) (natp (ex-astart ar))
                (equal c (ex-fbcm0 tm ar)) (equal cs (cons (ex-anp ar) (len (ex-inners (nth 2 tm))))))
           (equal (vtg-clause (ex-anf ar) (if (ex-avar ar) 1 0) (ex-astart ar) (ex-abody ar) tm 0 (len (ex-inners (nth 2 tm)))
                              (vtg-st s c sv cs))
                  (vtg-st (cons (ex-clause0 tm ar) s) c sv cs)))
  :hints (("Goal" :in-theory (e/d (ex-anp ex-clause0 ex-fbtc0 ex-fbin0 ex-fparams ex-fcmb0 ex-flp ex-lsl vtg-np vtg-nm vtg-kw)
                                  (vtg-tr ex-tr ex-abody ex-astart ex-anf ex-avar ex-locals ex-slots ex-blank ex-capts ex-fbcm0))
                  :use ((:instance vtg-node-rev (op 0) (n (ex-anp ar)) (c (ex-fbcm0 tm ar))
                                   (l (ex-cs t (ex-locals (ex-slots (ex-astart ar) (ex-anp ar)) (ex-fbcm0 tm ar))
                                             (ex-anp ar) (len (ex-inners (nth 2 tm)))))
                                   (s (cons (ex-anf ar) s))
                                   (sv sv) (cs cs))))))
(defthm vtg-clause-ex-clause0
  (implies (and (vtg-frag 0 (ex-abody ar) 0) (vtg-tlr-ok (ex-abody ar)) (natp (ex-astart ar)) (vtbp vtb)
                (equal (vtb-cm vtb) (ex-fbcm0 tm ar)) (equal (vtb-cs vtb) (cons (ex-anp ar) (len (ex-inners (nth 2 tm))))))
           (let ((vtb2 (vtg-clause (ex-anf ar) (if (ex-avar ar) 1 0) (ex-astart ar) (ex-abody ar) tm 0 (len (ex-inners (nth 2 tm))) vtb)))
             (and (equal (vtb-stk vtb2) (cons (ex-clause0 tm ar) (vtb-stk vtb)))
                  (equal (vtb-cm vtb2) (vtb-cm vtb)) (equal (vtb-sv vtb2) (vtb-sv vtb)) (equal (vtb-cs vtb2) (vtb-cs vtb)))))
  :hints (("Goal" :use ((:instance vtg-clause-st0 (s (vtb-stk vtb)) (c (vtb-cm vtb)) (sv (vtb-sv vtb)) (cs (vtb-cs vtb))))
                  :in-theory (disable vtg-clause-st0 vtg-clause vtb-stk vtb-cm vtb-sv vtb-cs vtbp))))

; its cost: vtg-clause-steps at sl 1 less the self shim and its let node
(defthm vtg-clause-steps-sl0
  (equal (vtg-clause-steps nf var body 0) (- (vtg-clause-steps nf var body 1) 2)))

; ---- THE SCOPE (Lane 3 item 2) ------------------------------------------------------------------
;
; vm_clause's scope, generated: vtg-scope makes ex-fbcm (sl 1) or ex-fbcm0
; (sl 0) from an empty one -- the parameters' slots s .. s+np-1 (vtg_binds),
; each capture's inner slot read in place (vtg-inrs over vtg_nin / vtg_inr,
; each vtg_capin), then the self slot when sl (vtg_bind). vtg-scope-fbcm.
; NAMED: vtg_nin / vtg_inr read the template's capture pairs vm_compile_fn
; is handed (capv, a vector), where the model reads ex-inners of tm's list;
; vtg_capin is vm.inc's c%capt(s) = j (the capture read in place, no
; local) where the model appends s to the scope -- vtg_local's ex-cs
; reading as before. Which sl, and the self slot, stay vm_clause's (the sl
; decision named above).

; a template's captures: how many, capture j's inner slot (vtg_nin, vtg_inr)
(defun vtg-nin (tm) (declare (xargs :guard t)) (vtg-int (len (ec-call (ex-inners (vtg-nth 2 tm))))))
(defun vtg-inr (tm j) (declare (xargs :guard (natp j))) (vtg-int (vtg-nth j (ec-call (ex-inners (vtg-nth 2 tm))))))
(defthm vtg-nin-range (and (natp (vtg-nin tm)) (< (vtg-nin tm) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-nin tm))) (:linear :corollary (< (vtg-nin tm) *vtg40*))))
; capture j's inner slot read in place (vtg_capin: c%capt(s) = j)
(defun vtg-capin (s j vtb) (declare (xargs :stobjs vtb :guard t) (ignorable j)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list s)) vtb))
(defun vtg-inrs (tm j vtb)
  (declare (xargs :stobjs vtb :guard (and (natp j) (< j *vtg40*)) :measure (nfix (- (vtg-nin tm) (nfix j)))))
  (let ((j (nfix j)))
    (if (< j (vtg-nin tm)) (let ((vtb (vtg-capin (vtg-inr tm j) j vtb))) (vtg-inrs tm (+ 1 j) vtb)) vtb)))
(defun vtg-scope (s np self sl tm vtb)
  (declare (xargs :stobjs vtb :guard (natp sl)))
  (let* ((vtb (vtg-binds s np vtb))
         (vtb (vtg-inrs tm 0 vtb)))
    (if (equal sl 0) vtb (vtg-bind self vtb))))

(defthm vtg-capin-st (equal (vtg-capin x j (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list x)) sv cs))
  :hints (("Goal" :in-theory (enable vtg-st))))
(defun vtg-inrs-ind (j os c)
  (declare (xargs :measure (len os)))
  (if (consp os) (vtg-inrs-ind (+ 1 j) (cdr os) (append c (list (car os)))) (list j c)))
(defthm vtg-app-assoc-1 (equal (append (append a (list x)) b) (append a (cons x b))))
(defthm vtg-inrs-nthcdr
  (implies (and (natp j) (true-listp c) (vtg-fnos os) (< (len (ex-inners (nth 2 tm))) *vtg40*) (equal os (nthcdr j (ex-inners (nth 2 tm)))))
           (equal (vtg-inrs tm j (vtg-st s c sv cs)) (vtg-st s (append c os) sv cs)))
  :hints (("Goal" :induct (vtg-inrs-ind j os c) :in-theory (e/d (vtg-nin vtg-inr vtg-int vtg-nthcdr-cdr) (vtg-capin vtg-nthcdr-parts vtg-nthcdr-end))
                  :expand ((vtg-inrs tm j (vtg-st s c sv cs))))
          (and stable-under-simplificationp '(:use ((:instance vtg-nthcdr-parts (i j) (l (ex-inners (nth 2 tm))))
                                                    (:instance vtg-nthcdr-end (i j) (l (ex-inners (nth 2 tm)))))))))
(defthm vtg-scope-fbcm
  (implies (and (vtg-fnos (ex-inners (nth 2 tm))) (< (len (ex-inners (nth 2 tm))) *vtg40*))
           (and (equal (vtg-scope (ex-astart ar) (ex-anp ar) (ex-fself tm) 1 tm (vtg-st s nil sv cs)) (vtg-st s (ex-fbcm tm ar) sv cs))
                (equal (vtg-scope (ex-astart ar) (ex-anp ar) self 0 tm (vtg-st s nil sv cs)) (vtg-st s (ex-fbcm0 tm ar) sv cs))))
  :hints (("Goal" :in-theory (e/d (ex-fbcm ex-fbcm0 ex-fparams) (vtg-inrs))
                  :use ((:instance vtg-inrs-nthcdr (j 0) (os (ex-inners (nth 2 tm))) (c (ex-slots (ex-astart ar) (ex-anp ar))))))))
; its cost: vtg_binds np + 1, a capture 2, the self bind, three calls
(defun vtg-scope-steps (np nin sl) (+ 3 (nfix np) 1 (* 2 (nfix nin)) (if (equal sl 0) 0 1)))
(defthm vtg-scope-steps-bound (<= (vtg-scope-steps np nin sl) (+ 5 (* 2 (+ (nfix np) (nfix nin))))) :rule-classes :linear)
; ---- THE FN'S CLAUSES (Lane 3 item 9) ---------------------------------------------------------
;
; vm_compile_fn's loop, generated: vtg-fncl pushes the fn's clause list --
; each arity's clause in order (vtg-ars: vtg_arity, vm_clause, a shim), then
; the arity clause (vtg-arcl), made one list (vtg_node 0): ex-clauses's
; order then ex-arcl, the list ex-arcl-mxcl takes (vtg-fncl-clauses). And
; vm_clause's sl decision, generated: vtg-sl -- 1 when the self slot is
; one the body reads or binds (vtg-rds), else 0 -- vtg-sl-fbtc0-mx: at 0
; the sl-0 clause answers as ex-clause (below).
; NAMED: vtg_arity is vm_clause on the arity read by vtg_ar (gcv_nth), its
; tm the template's capture pairs (capv, as vtg_nin's), ns and self the
; template's frame size and self slot, which the model's ex-clause reads
; from tm; the clause it builds is vtg_clause's (vtg-clause-ex-clause, at
; sl 0 ex-clause0, which answers as it: vtg-sl-fbtc0-mx); a refusal pushes
; nil and clears tb%c%ok, and vm_compile_fn drops the whole list (the fn
; stays the tree's).
(defun vtg-ar (ars j) (declare (xargs :guard (natp j))) (vtg-nth j ars))
(defun vtg-nar (ars) (declare (xargs :guard t)) (vtg-int (len ars)))
(defun vtg-arity (ar tm ns self vtb)
  (declare (xargs :stobjs vtb :guard t) (ignorable ns self))
  (vtg-push (ec-call (ex-clause tm ar)) vtb))
(defun vtg-ars (ars j tm ns self vtb)
  (declare (xargs :stobjs vtb :guard (and (natp j) (< j *vtg40*)) :measure (nfix (- (vtg-nar ars) (nfix j)))))
  (let ((j (nfix j)))
    (if (< j (vtg-nar ars)) (let ((vtb (vtg-arity (vtg-ar ars j) tm ns self vtb))) (vtg-ars ars (+ 1 j) tm ns self vtb)) vtb)))
(defun vtg-fncl (ars tm ns self name vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let* ((vtb (vtg-ars ars 0 tm ns self vtb))
         (vtb (vtg-arcl name vtb)))
    (vtg-node 0 (+ 1 (vtg-nar ars)) vtb)))
(defun vtg-sl (body self)
  (declare (xargs :guard (integerp self)))
  (if (and (<= 0 self) (vtg-rds 0 body 0 self)) 1 0))

(defthm vtg-arity-st (equal (vtg-arity ar tm ns self (vtg-st s c sv cs)) (vtg-st (cons (ex-clause tm ar) s) c sv cs))
  :hints (("Goal" :in-theory (enable vtg-st))))
(defun vtg-ars-ind (j os s tm)
  (declare (xargs :measure (len os)))
  (if (consp os) (vtg-ars-ind (+ 1 j) (cdr os) (cons (ex-clause tm (car os)) s) tm) (list j s)))
(defthm vtg-ars-st
  (implies (and (natp j) (true-listp ars) (< (len ars) *vtg40*) (equal os (nthcdr j ars)))
           (equal (vtg-ars ars j tm ns self (vtg-st s c sv cs))
                  (vtg-st (revappend (ex-clauses tm os) s) c sv cs)))
  :hints (("Goal" :induct (vtg-ars-ind j os s tm) :in-theory (e/d (vtg-nar vtg-ar vtg-int vtg-nthcdr-cdr) (ex-clause vtg-arity vtg-nthcdr-parts vtg-nthcdr-end))
                  :expand ((vtg-ars ars j tm ns self (vtg-st s c sv cs))))
          (and stable-under-simplificationp '(:use ((:instance vtg-nthcdr-parts (i j) (l ars))
                                                    (:instance vtg-nthcdr-end (i j) (l ars)))))))
(defthm vtg-len-clauses (and (equal (len (ex-clauses tm ars)) (len ars)) (true-listp (ex-clauses tm ars))))
(defthm vtg-fncl-clauses
  (implies (and (true-listp ars) (< (len ars) *vtg40*))
           (equal (vtg-fncl ars tm ns self name (vtg-st s c sv cs))
                  (vtg-st (cons (append (ex-clauses tm ars) (list (ex-arcl name))) s) c sv cs)))
  :hints (("Goal" :in-theory (e/d (vtg-nar vtg-int) (vtg-ars vtg-arcl ex-clauses ex-arcl))
                  :use ((:instance vtg-node-rev (op 0) (n (+ 1 (len ars))) (l (append (ex-clauses tm ars) (list (ex-arcl name)))))))))
; its cost: a clause's call (vm_clause's own work vtg-clause-steps-bound,
; its host's) and 3 steps an arity, the arity clause's 11, the list's node
(defun vtg-fncl-steps (n) (+ 13 (* 3 (nfix n))))
(defthm vtg-fncl-steps-bound (<= (vtg-fncl-steps n) (+ 13 (* 3 (nfix n)))) :rule-classes :linear)
(in-theory (disable vtg-arity vtg-ars vtg-fncl vtg-sl))
; ---- THE SL DECISION GIVES EX-FBTC0-MX'S HYPOTHESIS ---------------------------------------------
(defthm vtg-fnos-nil (implies (vtg-fnos os) (not (member-equal nil os))))
(defthm ex-pos-nth (implies (< (ex-pos y cm) (len cm)) (equal (nth (ex-pos y cm) cm) y)))
(defthm ex-locals-rd
  (implies (and (natp np) (< np (len cm)) (not (member-equal (nth np cm) os))) (not (x2-rd-args np (ex-locals os cm))))
  :hints (("Goal" :induct (ex-locals os cm) :in-theory (enable ex-locals))))
(defthm ex-lfcaps-rd
  (implies (and (natp np) (< np (len cm)) (not (member-equal (nth np cm) os))) (not (x2-rd-args np (ex-lfcaps os s n cm))))
  :hints (("Goal" :induct (ex-lfcaps os s n cm) :in-theory (enable ex-lfcaps))))
(defthm ex-slots-nomem (implies (and (natp s) (not (and (<= s x) (< x (+ s (nfix n)))))) (not (member-equal x (ex-slots s n))))
  :hints (("Goal" :in-theory (enable ex-slots))))
(defthm ex-slots-nonil (not (member-equal nil (ex-slots s n))) :hints (("Goal" :in-theory (enable ex-slots))))
(defthm ex-locals-nil (equal (ex-locals nil cm) nil) :hints (("Goal" :in-theory (enable ex-locals))))
(defthm vtg-nth-past (implies (<= (len l) (nfix j)) (equal (nth j l) nil)))
(defthm ex-kid-past (implies (and (natp j) (<= (ex-nk e) j)) (not (consp (ex-kid-of e j)))) :hints (("Goal" :in-theory (enable ex-kid-of ex-nk))))
(defthm ex-tr-atom (implies (not (consp e)) (equal (ex-tr flg e i cm) '(:const nil))) :hints (("Goal" :expand ((ex-tr flg e i cm)))))
(defthm ex-slots-mem (implies (member-equal x (ex-slots s n)) (and (natp x) (<= (nfix s) x) (< x (+ (nfix s) (nfix n)))))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable ex-slots))))
(defthm ex-blank-nth (implies (and (natp np) (< np (len cm))) (equal (nth np (ex-blank ls cm)) (if (member-equal (nth np cm) ls) nil (nth np cm))))
  :hints (("Goal" :in-theory (enable ex-blank))))
(defthm ex-len-blank2 (equal (len (ex-blank ls cm)) (len cm)) :hints (("Goal" :in-theory (enable ex-blank))))
(defthm ex-nth-append-lo (implies (and (natp np) (< np (len a))) (equal (nth np (append a b)) (nth np a))))
; what vtg-rds leaves out, each part
(defthm vtg-rds-kids
  (implies (and (not (vtg-rds 1 e i x)) (natp i) (natp j) (<= i j) (< j (vtg-nk e))) (not (vtg-rds 0 (vtg-kid e j) 0 x)))
  :hints (("Goal" :induct (vtg-tli i (vtg-nk e)) :expand ((vtg-rds 1 e i x)) :in-theory (disable vtg-kid-ex))))
(defthm vtg-rds-thens
  (implies (and (not (vtg-rds 2 e i x)) (natp i) (natp j) (<= i j) (< j (vtg-ncs e))) (not (vtg-rds 0 (vtg-cthen e j) 0 x)))
  :hints (("Goal" :induct (vtg-tli i (vtg-ncs e)) :expand ((vtg-rds 2 e i x)) :in-theory (disable vtg-cthen-ex vtg-ncs-ex))))
(defthm vtg-rds-catches
  (implies (and (not (vtg-rds 3 e i x)) (natp i) (natp j) (<= i j) (< j (vtg-ncs e)))
           (and (not (vtg-rds 0 (vtg-cbody e j) 0 x)) (not (equal (vtg-cslot e j) x))))
  :hints (("Goal" :induct (vtg-tli i (vtg-ncs e)) :expand ((vtg-rds 3 e i x)) :in-theory (disable vtg-cbody-ex vtg-ncs-ex vtg-cslot-ex))))
(defun vtg-osind (j os) (declare (xargs :measure (len os))) (if (consp os) (vtg-osind (+ 1 j) (cdr os)) j))
(defthm vtg-rds-caps-nthcdr
  (implies (and (not (vtg-rds 5 e j x)) (natp j) (vtg-fnos os) (< (len (ex-outers (nth 2 (ex-c e)))) *vtg40*)
                (equal os (nthcdr j (ex-outers (nth 2 (ex-c e))))))
           (not (member-equal x os)))
  :hints (("Goal" :induct (vtg-osind j os) :in-theory (e/d (vtg-ncap vtg-capo vtg-int vtg-nthcdr-cdr) (vtg-nthcdr-parts vtg-nthcdr-end))
                  :expand ((vtg-rds 5 e j x)))
          (and stable-under-simplificationp '(:use ((:instance vtg-nthcdr-parts (i j) (l (ex-outers (nth 2 (ex-c e)))))
                                                    (:instance vtg-nthcdr-end (i j) (l (ex-outers (nth 2 (ex-c e))))))))))
(defthm vtg-rds-caps
  (implies (and (not (vtg-rds 5 e 0 x)) (vtg-fnok e)) (not (member-equal x (ex-outers (nth 2 (ex-c e))))))
  :hints (("Goal" :in-theory (enable vtg-fnok) :use ((:instance vtg-rds-caps-nthcdr (j 0) (os (ex-outers (nth 2 (ex-c e)))))))))
; in ex-tr's reads: a node vtg-scan takes, what it leaves to its parts
(defmacro vtg-ex-off () ''(vtg-scan vtg-rds vtg-kid-ex vtg-cthen-ex vtg-cbody-ex vtg-cslot-ex vtg-ncs-ex vtg-okt-reads))
(defthm vtg-ex-scan-kid
  (implies (and (vtg-scan 0 e 0 hi) (natp j) (< j (ex-nk e)) (not (member (ex-kind e) '(1 2 3 13 14 15))))
           (vtg-scan 0 (ex-kid-of e j) 0 hi))
  :hints (("Goal" :use ((:instance vtg-scan-kid0) (:instance vtg-scan-kind-nil (i 0)) (:instance vtg-coll (k (vtg-kind e))))
                  :in-theory (disable vtg-scan-kid0 vtg-scan-kind-nil vtg-scan vtg-rds))))
(defthm vtg-ex-scan-body13
  (implies (and (vtg-scan 0 e 0 hi) (equal (ex-kind e) 13)) (vtg-scan 0 (ex-kid-of e (ex-i2 e)) 0 hi))
  :hints (("Goal" :use ((:instance vtg-scan-body13)) :in-theory (disable vtg-scan-body13 vtg-scan vtg-rds))))
(defthm vtg-ex-scan-then
  (implies (and (vtg-scan 0 e 0 hi) (equal (ex-kind e) 19) (natp j) (< j (len (ex-c e)))) (vtg-scan 0 (ex-cthen e j) 0 hi))
  :hints (("Goal" :use ((:instance vtg-scan-then0)) :in-theory (disable vtg-scan-then0 vtg-scan vtg-rds))))
(defthm vtg-ex-scan-catch
  (implies (and (vtg-scan 0 e 0 hi) (equal (ex-kind e) 18) (natp j) (< j (len (ex-c e)))) (vtg-scan 0 (ex-cbody e j) 0 hi))
  :hints (("Goal" :use ((:instance vtg-scan-catch0)) :in-theory (disable vtg-scan-catch0 vtg-scan vtg-rds))))

(defthm vtg-ex-rds-kid
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (natp j) (< j (ex-nk e)) (not (member (ex-kind e) '(2 14 15))))
           (not (vtg-rds 0 (ex-kid-of e j) 0 x)))
  :hints (("Goal" :use ((:instance vtg-rds-kids (i 0))) :expand ((vtg-rds 0 e 0 x))
                  :in-theory (disable vtg-rds-kids vtg-scan ex-kid-of))))
(defthm vtg-ex-rds-then
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (equal (ex-kind e) 19) (natp j) (< j (len (ex-c e))))
           (not (vtg-rds 0 (ex-cthen e j) 0 x)))
  :hints (("Goal" :use ((:instance vtg-rds-thens (i 0))) :expand ((vtg-rds 0 e 0 x))
                  :in-theory (disable vtg-rds-thens vtg-scan ex-cthen))))
(defthm vtg-ex-rds-catch
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (equal (ex-kind e) 18) (natp j) (< j (len (ex-c e))))
           (and (not (vtg-rds 0 (ex-cbody e j) 0 x)) (not (equal (ex-cslot e j) x))))
  :hints (("Goal" :use ((:instance vtg-rds-catches (i 0)) (:instance vtg-okn-cslot)) :expand ((vtg-rds 0 e 0 x))
                  :in-theory (disable vtg-rds-catches vtg-scan ex-cbody ex-cslot vtg-okn-cslot))))
(defthm vtg-ex-rds-binds
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (member (ex-kind e) '(11 12 13)) (natp x))
           (not (and (<= (ex-s2 e) x) (< x (+ (ex-s2 e) (ex-i2 e))))))
  :hints (("Goal" :expand ((vtg-rds 0 e 0 x)) :in-theory (disable vtg-scan))))
(defthm vtg-ex-rds-local
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (equal (ex-kind e) 2)) (not (equal (ex-i2 e) x)))
  :hints (("Goal" :expand ((vtg-rds 0 e 0 x)) :in-theory (disable vtg-scan))))
(defthm vtg-ex-rds-self (implies (and (vtg-scan 0 e i hi) (equal (ex-kind e) 2)) (vtg-rds 0 e 0 (ex-i2 e)))
  :hints (("Goal" :expand ((vtg-rds 0 e 0 (ex-i2 e)) (vtg-scan 0 e i hi)))))
(defthm vtg-ex-kind-lt (implies (vtg-scan 0 e i hi) (< (ex-kind e) 25)) :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance vtg-scan-kind-nil)) :in-theory (disable vtg-scan-kind-nil vtg-scan))))
(defthm vtg-ex-fn-nonil
  (implies (and (vtg-scan 0 e i hi) (or (equal (ex-kind e) 14) (equal (ex-kind e) 15))) (not (member-equal nil (ex-outers (nth 2 (ex-c e))))))
  :hints (("Goal" :use ((:instance vtg-okn-fnok)) :in-theory (e/d (vtg-fnok) (vtg-scan vtg-okn-fnok)))))
(defthm vtg-ex-local-natp (implies (vtg-scan 0 e 0 hi) (and (natp (ex-i2 e)) (natp (ex-s2 e))))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (e/d (vtg-ok ex-i2 ex-s2) (vtg-scan)))))
(defthm vtg-ex-try-fin
  (implies (and (vtg-scan 0 e 0 hi) (equal (ex-kind e) 18) (not (vtg-scan 0 (ex-kid-of e 1) 0 hi))) (not (consp (ex-kid-of e 1))))
  :hints (("Goal" :use ((:instance vtg-ex-scan-kid (j 1)) (:instance ex-kid-past (j 1))) :in-theory (disable vtg-ex-scan-kid ex-kid-past vtg-scan ex-kid-of))))
(defthm vtg-ex-rds-fn
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (or (equal (ex-kind e) 14) (equal (ex-kind e) 15)))
           (and (not (member-equal x (ex-outers (nth 2 (ex-c e))))) (not (member-equal nil (ex-outers (nth 2 (ex-c e)))))))
  :hints (("Goal" :expand ((vtg-rds 0 e 0 x)) :use ((:instance vtg-okn-fnok)) :in-theory (e/d (vtg-fnok) (vtg-scan vtg-okn-fnok)))))
(defthm vtg-scan-lffns
  (implies (and (vtg-scan 4 e i hi) (natp i) (natp j) (<= i j) (< j (vtg-i2 e)) (equal (vtg-kind e) 13))
           (and (vtg-okn (vtg-kid e j)) (equal (vtg-kind (vtg-kid e j)) 14)))
  :hints (("Goal" :induct (vtg-tli i (vtg-i2 e)) :expand ((vtg-scan 4 e i hi)) :in-theory (disable vtg-kid-ex vtg-reads-ex vtg-okt-reads))))
(defthm vtg-ex-lffn
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (equal (ex-kind e) 13) (natp j) (< j (ex-i2 e)))
           (and (not (member-equal x (ex-lfos e j))) (not (member-equal nil (ex-lfos e j)))))
  :hints (("Goal" :use ((:instance vtg-scan-lffns (i 0)) (:instance vtg-ex-rds-kid) (:instance vtg-scan-i2nk (i 0))
                        (:instance vtg-okn-fnok (e (ex-kid-of e j)))
                        (:instance vtg-rds-caps (e (ex-kid-of e j))))
                  :expand ((vtg-scan 0 e 0 hi) (vtg-rds 0 (ex-kid-of e j) 0 x))
                  :in-theory (e/d (ex-lfos vtg-fnok) (vtg-scan-lffns vtg-ex-rds-kid vtg-okn-fnok vtg-rds-caps vtg-scan-i2nk ex-kid-of vtg-rds vtg-okt-reads)))))
(defthm vtg-ex-lffn-nil
  (implies (and (vtg-scan 0 e 0 hi) (equal (ex-kind e) 13) (natp j) (< j (ex-i2 e))) (not (member-equal nil (ex-lfos e j))))
  :hints (("Goal" :use ((:instance vtg-scan-lffns (i 0)) (:instance vtg-scan-i2nk (i 0)) (:instance vtg-okn-fnok (e (ex-kid-of e j))))
                  :expand ((vtg-scan 0 e 0 hi))
                  :in-theory (e/d (ex-lfos vtg-fnok) (vtg-scan-lffns vtg-okn-fnok vtg-scan-i2nk ex-kid-of vtg-rds vtg-okt-reads)))))
(defthm vtg-ex-lfargs
  (implies (and (vtg-scan 0 e 0 hi) (equal (ex-kind e) 13) (natp np) (< np (len cm))
                (or (null (nth np cm)) (not (vtg-rds 0 e 0 (nth np cm)))))
           (not (x2-rd-args np (ex-lfargs e j cm))))
  :hints (("Goal" :induct (ex-lfargs e j cm) :in-theory (e/d (ex-lfargs) (ex-lfos vtg-scan vtg-rds ex-lfcaps-rd))
                  :expand ((ex-lfargs e j cm)))
          (and stable-under-simplificationp '(:use ((:instance ex-lfcaps-rd (os (ex-lfos e (nfix j))) (s (ex-s2 e)) (n (ex-i2 e)))
                                                    (:instance vtg-ex-lffn (j (nfix j)) (x (nth np cm))) (:instance vtg-ex-lffn-nil (j (nfix j))))))))
(defthm vtg-ex-nk2
  (implies (and (vtg-scan 0 e i hi) (or (equal (ex-kind e) 4) (equal (ex-kind e) 19))) (<= 2 (ex-nk e)))
  :rule-classes (:rewrite :linear) :hints (("Goal" :use vtg-scan-nk2 :in-theory (disable vtg-scan-nk2 vtg-scan))))
(defthm vtg-ex-nk1
  (implies (and (vtg-scan 0 e i hi) (or (equal (ex-kind e) 6) (equal (ex-kind e) 17) (equal (ex-kind e) 18))) (<= 1 (ex-nk e)))
  :rule-classes (:rewrite :linear) :hints (("Goal" :use vtg-scan-nk1 :in-theory (disable vtg-scan-nk1 vtg-scan))))
(defthm vtg-ex-i2nk
  (implies (and (vtg-scan 0 e i hi) (or (equal (ex-kind e) 11) (equal (ex-kind e) 12) (equal (ex-kind e) 13))) (< (ex-i2 e) (ex-nk e)))
  :rule-classes (:rewrite :linear) :hints (("Goal" :use vtg-scan-i2nk :in-theory (disable vtg-scan-i2nk vtg-scan))))
(defthm vtg-ex-slots-nox
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (member (ex-kind e) (quote (11 12 13))) (natp x))
           (not (member-equal x (ex-slots (ex-s2 e) (ex-i2 e)))))
  :hints (("Goal" :use ((:instance vtg-ex-rds-binds) (:instance ex-slots-mem (s (ex-s2 e)) (n (ex-i2 e))))
                  :in-theory (disable vtg-ex-rds-binds ex-slots-mem vtg-scan vtg-rds))))
(defthm vtg-ex-try-fin-rds
  (implies (and (vtg-scan 0 e 0 hi) (not (vtg-rds 0 e 0 x)) (equal (ex-kind e) 18) (vtg-rds 0 (ex-kid-of e 1) 0 x)) (not (consp (ex-kid-of e 1))))
  :hints (("Goal" :use ((:instance vtg-ex-rds-kid (j 1)) (:instance ex-kid-past (j 1))) :in-theory (disable vtg-ex-rds-kid ex-kid-past vtg-scan vtg-rds ex-kid-of))))
(defun ex-flok (flg e)
  (case flg (:do (equal (ex-kind e) 5)) (:let (or (equal (ex-kind e) 11) (equal (ex-kind e) 12))) (:lin (equal (ex-kind e) 12))
    (:rec (equal (ex-kind e) 16)) (:call (equal (ex-kind e) 6)) (:coll (member (ex-kind e) '(7 8 9 22 23 10 20 24 21)))
    ((:cs :fin) (equal (ex-kind e) 18)) (:ct (equal (ex-kind e) 19)) (otherwise t)))
(defthm ex-tr-nord-flag
  (implies (and (vtg-scan 0 e 0 hi) (ex-flok flg e) (natp np) (< np (len cm))
                (or (null (nth np cm)) (and (natp (nth np cm)) (not (vtg-rds 0 e 0 (nth np cm))))))
           (not (ex-trrd flg np (ex-tr flg e i cm))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-tr flg e i cm)
                  :in-theory (e/d ((:induction ex-tr) ex-trtry ex-trfin ex-trcall)
                                  (vtg-scan vtg-rds ex-kid-of ex-lffns ex-lfok ex-trlf ex-lfargs ex-lfshape ex-trh ex-trcs ex-clr ex-lind
                                   ex-slots ex-blank ex-locals ex-cthen ex-cbody ex-cslot ex-lfcaps-rd))
                  :expand ((:free (flg cm) (ex-tr flg e i cm))))))
(defthm ex-tr-nord
  (implies (and (vtg-scan 0 e 0 hi) (natp np) (< np (len cm))
                (or (null (nth np cm)) (and (natp (nth np cm)) (not (vtg-rds 0 e 0 (nth np cm))))))
           (not (x2-rd np (ex-tr :m e i cm))))
  :hints (("Goal" :use ((:instance ex-tr-nord-flag (flg :m))))))

; the clause: the parameters' reads sit before the self slot's position
(defthm ex-pos-app-lt (implies (member-equal p a) (< (ex-pos p (append a b)) (len a))) :rule-classes :linear)
(defthm ex-locals-before
  (implies (and (subsetp-equal ls a) (<= (len a) (nfix np))) (not (x2-rd-args np (ex-locals ls (append a b)))))
  :hints (("Goal" :induct (len ls) :in-theory (e/d (ex-locals) (binary-append)))))
(defthm vtg-len-slots2 (equal (len (ex-slots s n)) (nfix n)) :hints (("Goal" :in-theory (enable ex-slots))))
(defthm ex-nth-fbcm (equal (nth (ex-fnp tm ar) (ex-fbcm tm ar)) (ex-fself tm))
  :hints (("Goal" :in-theory (enable ex-fbcm ex-fparams))))
(defthm ex-nth-fcmb
  (equal (nth (ex-fnp tm ar) (ex-fcmb tm ar)) (if (member-equal (ex-fself tm) (ex-lsl (ex-flp ar))) nil (ex-fself tm)))
  :hints (("Goal" :in-theory (e/d (ex-fcmb ex-fcm) (ex-fnp ex-fbcm ex-lsl ex-flp)))))
(defthm ex-anp-fnp (<= (ex-anp ar) (ex-fnp tm ar)) :rule-classes :linear)
(defthm ex-fparams-locals-fnp (not (x2-rd-args (ex-fnp tm ar) (ex-locals (ex-fparams ar) (ex-fbcm tm ar))))
  :hints (("Goal" :in-theory (e/d (ex-fbcm) (ex-fnp ex-fparams))
                  :use ((:instance ex-locals-before (ls (ex-fparams ar)) (a (ex-fparams ar))
                                   (b (append (ex-inners (nth 2 tm)) (list (ex-fself tm)))) (np (ex-fnp tm ar)))))
          (and stable-under-simplificationp (quote (:in-theory (enable ex-fparams))))))
(defthm ex-fself-natp-or-nil (or (null (ex-fself tm)) (natp (ex-fself tm))) :rule-classes :type-prescription)

; vm_clause's sl decision: a body vtg-scan takes whose self slot vtg-sl
; answers 0 for (none, -1, or one it never reads nor binds) gives
; ex-fbtc0-mx's hypothesis -- its translation never reads the self slot's
; position -- so the sl-0 clause answers as ex-clause's
(defthm vtg-sl-fbinr
  (implies (and (vtg-scan 0 (ex-abody ar) 0 hi)
                (equal (vtg-sl (ex-abody ar) (if (natp (ex-fself tm)) (ex-fself tm) -1)) 0))
           (not (x2-rd (ex-fnp tm ar) (ex-fbinr tm ar))))
  :hints (("Goal" :in-theory (e/d (ex-fbinr vtg-sl) (ex-fnp ex-fbcm ex-fcmb ex-tr ex-lsl ex-flp ex-abody ex-fparams vtg-scan vtg-rds))
                  :expand ((:free (x y) (x2-rd (ex-fnp tm ar) (list :loop x y)))))))
(defthm vtg-sl-fbtc0-mx
  (implies (and (vtg-scan 0 (ex-abody ar) 0 hi)
                (equal (vtg-sl (ex-abody ar) (if (natp (ex-fself tm)) (ex-fself tm) -1)) 0)
                (equal (len env) (ex-anp ar)) (true-listp env))
           (equal (mx2 (ex-fbtc0 tm ar) env caps defs fuel) (mx2 (ex-fbtc tm ar) env caps defs fuel)))
  :hints (("Goal" :use (vtg-sl-fbinr ex-fbtc0-mx) :in-theory (disable vtg-sl-fbinr ex-fbtc0-mx ex-fbtc0 ex-fbtc mx2))))

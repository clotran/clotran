; A FN'S CLAUSES, GENERATED (src/f/gen/vm_tr_gen.inc, scripts/acl2-fortran
; -b vmtrg, which loads this book): vm.inc's vm_clause and the arity-error
; clause of vm_compile_fn, at the level the Fortran is generated from,
; guard-verified, over vmtrg's builder and scope.
;
; vtg-clause: one arity's clause, (n body) or (n body :rest) -- exec-vmtr's
; ex-clause: the body ex-fbtc's, the self slot's let round the loop (when
; the body recurs to the fn, vtg-tlr) or the body, the captures read in place.
; The host makes the scope first (vm_clause: the parameters, the captures
; read in place, the self slot: ex-fbcm; vtb-cs the counts), as vm_tr_gen
; does for vtg-tr. Three shims more: vtg-num a number pushed, vtg-key a
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
; NAMED, not proved (the sl decision): ex-fbtc0-mx's hypothesis (not (x2-rd
; (ex-fnp tm ar) (ex-fbinr tm ar))) -- the body's translation never reads
; the self slot's position -- is what vm_clause's choice of sl 0 (self_slot
; < 0, or vm_scan's c%reads(self_slot) false) is taken to establish:
; vm_scan is hand Fortran over the source tree, and no model predicate of
; it is proved to imply the hypothesis.
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

; THE VM'S TRANSLATION, GENERATED (src/f/gen/vm_tr_gen.inc,
; scripts/acl2-fortran -b vmtrg): exec-vmtr's ex-tr at the level the
; Fortran is generated from, guard-verified, for the kinds whose encoding
; vm.inc and ex-tr share -- a constant, a local, a Var, if, do, let*, loop,
; recur, throw, every call, case*, letfn, try, a collection (def, deftype,
; new of a type and set! among them), a fn and a lazy seq --
; every other kind the host's (vtg-other: vm.inc's hand-written vm_tr,
; which calls back here for these kinds). exec-PLAN's Lane 3 says what
; is left.
;
; THE OUTPUT is built on a stack, as anbuild builds nodes, so the
; generated code never holds an expression in a variable: a node's
; translation leaves one expression on top, and vtg-node makes (op items..)
; of the top n. THE SCOPE is ex-tr's cm, the slots in scope by position,
; kept by the host: vtg-bind appends a slot, vtg-dead a dead position (a
; do's value no one reads), vtg-blank blanks what a node
; may clear (ex-clr), vtg-save / vtg-restore keep and give back the whole
; scope, vtg-local reads a slot's position. In clotran the stack is the
; context's value stack and the scope vm.inc's vm_tr_ctx (its map from
; slot to local, its depth); the shims are vm.inc's vtg_*, each stated
; here. vtg-local reads a fn's capture in place, (:capt j), as the
; clause's body does (exec-vmtr's ex-fbtc, exec-vmcs's ex-cs; the scope's
; vtb-cs the clause's parameter and capture counts). Two shims are named,
; not exact: vtg_blank blanks nothing and vtg_restore undoes only binds --
; a blanked slot is read by no tree ex-vwf admits (exec-vm's ex-vm-agree
; asks it), so the positions it would read agree.
;
; A LOOP is ex-tr's two shapes: inits reading none of the loop's slots
; before them (vtg-lind, generated: ex-lind over ex-rd, vtg_rdcap reading
; a fn's captures) give (:loop (init ..) body); else the inits are lets and
; (:loop ((:local p) ..) body) rebinds the slots (vtg-binds: vtg_bind each).
; A recur is (:recur arg ..). vtg-node 0 makes the inits' list.
;
; Proved: vtg-tr-ex-tr -- on a tree of these kinds (vtg-frag) the
; generated translation pushes exactly ex-tr's, its captures read in place
; (ex-cs), leaving the scope as it found it; vtg-rd-ex, vtg-lind-ex -- the
; loop's test is ex-lind on a tree in the reads' range (vtg-okt).
; vtg-steps-bound -- its work at most 16 steps a node it reaches (vtg-size):
; each node's shims a constant number; vtg-lind-steps-bound -- the loop's
; test at most 6 steps a node it walks.
; vtg-tlr-ex-tlr -- vtg-tlr, vm_clause's loop test, is exec-vmtr's ex-tlr
; (a recur to the fn); vtg-tlr-steps-bound -- 5 steps a node it reaches.
;
; A VAR (exec-PLAN Lane 3 item 3, first slice). Encoding: ex-tr's kind 3 is
; vm.inc's, (:prim :clotran.vm/deref (:const v)), v the tree's (ex-c e);
; generated here by one shim, vtg_deref (vm_deref_of of vm_var_ref).
; Hypotheses, named not proved: exec-vm's ex-derefok -- the host's deref of
; v answers v (the namespace's root, a direct link's epoch re-read); vm.inc's
; constant is the Var or the linked node where the model's is the value; and
; ex-vwf asks a Var's v not shaped as prim's throw, (:throw . x) (exec-clrvm's
; ex-vwf0 the same). ex-vm-agree, ex-recur-stays, ex-vm-runs, ex-anp-runs gain
; (ex-derefok), otherwise unchanged. Cost: a Var 2 steps here as before
; (vtg-steps' default, one shim); mx2 one prim call more a Var read.
;
; A BUILTIN CALL (item 3, N_CALL's first case). Encoding: ex-tr's kind 6
; whose head is a constant the runtime says is a builtin (exec-vmtr's
; ex-bipe: prim :clotran.vm/builtin, an atom, not apply) is vm.inc's
; (:prim f args..), the args in the call's scope (flg 3 from 1, as a recur's);
; generated here by vtg_pk (the test, ex-pk 1) and vtg_hd (f pushed), vtg_node 6.
; Hypotheses, named not proved: exec-vm's ex-bipok -- the runtime's prim of
; a builtin is its :invoke, and a builtin is an IFn; vtg_pk's test is
; vm.inc's OBJ_BUILTIN (not B_APPLY) where the model's is prim
; :clotran.vm/builtin.
;
; A DIRECT-LINKED VAR WHOSE FN WRAPS A BUILTIN (item 4(a), vm_linked_builtin):
; ex-pk 2 -- the head a Var of i2 1 whose v the runtime says wraps a builtin
; f at the call's count (exec-vmtr's ex-wrapf, prim :clotran.vm/wraps) -- is
; (:prim f args..), f fixed at translation; vtg_hd pushes f (wrapper_of).
; Hypotheses, named not proved: exec-vm's ex-wrapok -- such a v is an IFn,
; and its call on n values answers the runtime's prim of f on them unless
; it runs out of fuel; vtg_pk's test is vm_linked_builtin (i2 1 and the
; link epoch, vm_wraps: not B_RTFN or B_UUIDFN) and vtg_hd's f wrapper_of,
; where the model asks i2 1 and prim :clotran.vm/wraps.
;
; A VAR NOT SO LINKED WHOSE FN WRAPS A BUILTIN (item 4(b)): ex-pk 3 is
; (:prim :clotran.vm/callw (:const v) args..); vtg_hd pushes callw and
; (:const var), vtg_node 6 of nk + 1. Hypotheses, named not proved: exec-vm's
; ex-callwok -- the runtime's callw of v on n values is its prim of the
; builtin v wraps at n; vtg_pk's test is vm_wraps where the model asks prim
; :clotran.vm/wraps; vm.inc's constant is vm_var_ref's (the Var, or the
; linked node) where the model's is v.
;
; A CALL OF AN IFn CONSTANT OR VAR, NOT APPLY (item 4(c)): ex-pk 4 is
; vm.inc's (:callv h args..), h the head's own translation ((:const v) or the
; deref), the arguments first as mx2's :callv runs them; vtg_hd pushes h,
; vtg_node 7. No new semantic hypothesis: the head answers v whenever the
; args do (ex-derefok), v is an IFn so the tree's cast passes, and not apply
; so no spread -- :applyv's call (exec-vm's ex-mx-pcallv). Named, not
; proved: vtg_pk's test is vm.inc's is_ifn of the constant, or of the Var's
; value or linked fn at translation (vtg_hv), not B_APPLY, where the model
; asks prim :ifn of v and v not :apply. Cost: 4 steps and the args'
; (vtg-steps), each case.
;
; EVERY OTHER CALL (item 4(c), the rest) -- a local's or any other
; expression's head, a non-IFn constant's or Var's, apply's -- is ex-tr's
; ex-trcall, generated: (:let head (:if (:prim :ifn (:local p)) (:applyv
; (:local p) args..) (:throw (:const :not-fn)))), p the head's dead
; position, the args in that scope (vtg_top, vtg_cast, vtg_notfn, vtg_node
; 8). No new semantic hypothesis: exec-vm's agreement already takes
; ex-trcall under ex-ifnok and ex-apok. Named, not proved: vm.inc's prim
; :ifn is the runtime's kind 9 (vrt-prim-kind), is_ifn, as exec_core's
; cast; its (:const :not-fn) is (:prim :clotran.vm/notfn (:local p)), kind
; 10, refuse_not_fn of the head (the host's error, as exec_core's action
; 23); :applyv's spread of apply is the runtime's :invoke of B_APPLY
; (rt_applyp false) where the model's is sk-spread. vm_tr's hand-written
; :callv is gone. Cost: 13 steps, the head's and the args' (vtg-steps).
;
; A CASE* (item 5, first slice) is ex-tr's kind 19: (:let test W), W the
; table's walk (exec-vmtr's ex-trcs) -- (:if (:prim :case (:const t)
; (:local p)) then .. default), p the test's dead position, the thens and the
; default in that scope (vtg-tr flg 6; vtg_cstest, vtg_top, vtg_node 6 and
; 1); vtg-tlr walks the default and the thens (vtg-tlrw flg 1, ex-tlr :ct).
; No new semantic hypothesis: exec-vm's agreement already takes the case
; under ex-caseok (prim :case throws nothing). Named, not proved: vtg_ncs
; and vtg_cthen read slot 2's entries in gca_entries' order where the
; model's is ex-c's list (the macro's tests are distinct: at most one entry
; takes a value); vtg_cstest's items are the N_CASE node and (:const then_j)
; where the model's are :case and (:const t) -- the op a node, the runtime's
; kind 6, vm_node_hook answering whether case_branch's probe of the value
; takes entry j (its then is then_j), exec-tree's prim :case (case_branch's
; probe and Util.equiv, as the tree's ex-casew). Tests: fuzz-vmtr-gen draws
; cases (entry j's test 50 + j) for vtg_tr, vtg_tlr and vtg_clause. Cost:
; 7 steps a case and 8 an entry, its parts' (vtg-steps).
;
; A LETFN (item 5) is ex-tr's kind 13, exec-vmtr's ex-trlf: n lets, the
; j-th init (:mkgrp (j . shape) caps..) in the letfn's scope -- every fn's
; captures in turn, the group's own (:const (:grp nil m)), any other its
; slot's read -- then the body in that scope and the group's slots
; (vtg-tr flg 7; vtg_lfinit, vtg_lfbinds). No new semantic hypothesis:
; exec-vm's agreement already takes the letfn (ex-lfok, x2-seal). Named,
; not proved: vtg_lfinit's init is vm.inc's (:prim NODE (:const j) caps..
; (:local d) .. (:local d+j-1)) -- the letfn node the op of the runtime's
; kind 6, vm_node_hook building fn j's closure and patching the group's
; captures among it and the earlier lets' closures (exec_letfn's
; refresh_captures: after the last let one group, its fns identical as the
; tree's), a group capture (:const nil) -- where the model's is :mkgrp and
; x2-seal's j-th closure; vtg_lfinit's own work linear in the captures (its
; host's, as vtg_other's). Tests: fuzz-vmtr-gen draws letfns (fns' templates
; (0 0 (o 0 ..)), outer slots the group's or not) for vtg_tr, vtg_tlr and
; vtg_clause. Cost: 3 steps a fn, 4 and a step a slot for the body (vtg-steps).
;
; A TRY (item 5(b)) is ex-tr's kind 18, exec-vmtr's ex-trtry: (:try B H),
; H the catch walk at the thrown value's position p (ex-trh: (:if (:prim
; :isa (:const c_j) (:local p)) body_j .. (:throw (:local p))), body_j in
; the walk's scope and catch j's slot); with a finally F, ex-trfin's (:let
; (:try that (:if F r r)) (:if F p p)), r the rethrow, F in the scope the
; body and catches leave blanked and a dead p (vtg-tr flg 8 the walk;
; vtg_catest, vtg_rethrow, vtg_blankcs; reads vtg_ncs, vtg_cbody, vtg_cslot).
; No new semantic hypothesis: exec-vm's agreement already takes the try
; (ex-isaok, mx2's :try). Named, not proved: vtg_catest's test is vm.inc's
; (:prim NODE (:const j) (:local p)), the try node the runtime's kind 6,
; vm_node_hook's N_TRY answering catch_matches of catch j's class, where the
; model's is prim :isa; vtg_rethrow -- the DISTINCT prim the implicit
; rethrows are (ex-trh's end, ex-trfin's two) -- is vm.inc's (:prim NODE
; (:local p)), vm_node_hook's N_TRY with one value answering p's throw, as
; prim's (:throw . p) unwinds as :throw's, the host's error raised again
; with the message and trace vm_caught kept when p is the value it caught
; (else as N_THROW raises p), where the model's is (:throw (:local p)); an
; explicit (throw e) stays ex-tr's kind 17, (:throw x), raising the printed
; value as the tree does. The host's side, named in vm.inc: a hook entered
; with the host's error raised means the VM caught it (vm_caught clears and
; keeps it, the last four a run, on vm_runref), and a status-0 end clears
; what is left; vtg_nk of an N_TRY is exec_core's nk (its finally slot nil:
; one). Tests: fuzz-vmtr-gen draws trys (catch j's class 60 + j and slot
; s2 + j, a finally or none) for vtg_tr, vtg_tlr and vtg_clause. Cost: 7
; steps a catch, 6 the try and 20 more with a finally, translated twice as
; ex-trfin writes it (vtg-size counts it twice -- ponytail: 2^d for a
; finally nested d deep in finallys; one translation and a stack pick if
; that shows).
;
; A COLLECTION (Lane 3 item 6, first slice) -- a vector, map or set
; literal, a new or a dot call (ex-kinds 7 8 9 22 21) -- is ex-tr's (:prim
; op args..), op exec-tree's ex-cop (:vector, :map, :set, (:host k C)), the
; args the kids in turn, each in the scope the ones before leave blanked (ex-tr
; :coll; vtg-tr flg 3 from 0, as a recur's; vtg_cop, vtg_node 6). No new
; semantic hypothesis: exec-vm's agreement already takes the collection
; (ex-collok). Named, not proved: vtg_cop's op is vm.inc's NODE itself, the
; runtime's kind 6 (vm_node_hook building it: vm_slots_vec, vec_to_set,
; vec_to_map, new_cached, dot_dispatch), where the model's is ex-cop. Def,
; deftype, a new of a type and set! (10 20 23 24) the same (exec-PLAN item
; 7(c)): ex-tr's (:prim (:host k C) kids..), vm_node_hook's N_DEF, N_DEFTYPE,
; N_SETBANG the tree's def_finish, deftype_finish, setbang_finish, N_NEWTYPE
; new_cached, on the kids' values, a def's and a deftype's kids exec_core's
; core_kid (vtg_nk, vtg_kid: ex-kid-of's) (named; ex-collok as before). Tests:
; fuzz-vmtr-gen draws all nine (c nil or a number).
; Cost: 3 steps and the kids' (vtg-steps).
;
; A FN (item 7(b)) is ex-tr's kind 14, (:mkclo tm caps..), tm its template
; (ex-c), caps the reads of its outer slots in the template's capture order
; (ex-locals of ex-outers, each read in place as vtg-local reads it;
; vtg_fnhd, vtg-caps over vtg_ncap / vtg_capo, vtg_node 0). No new semantic
; hypothesis: exec-vm's agreement already takes :mkclo. Named, not proved:
; vtg_fnhd's items are vm.inc's :prim and the N_FN node itself, the
; runtime's kind 6 (vm_node_hook building the closure from the captured
; values, make_closure_from's two shapes), where the model's are :mkclo and
; tm; vtg_ncap / vtg_capo read the template's (outer, inner) pairs, slot 2's
; vector, where the model's is ex-outers of its list. Tests: fuzz-vmtr-gen
; draws fns (templates (0 0 (o 0 ..))). Cost: 3 steps and 2 a capture
; (vtg-steps; vtg-size counts a capture a node).
;
; A LAZY SEQ (item 7) is ex-tr's kind 15, (:prim (:host 15 tm) (:mkclo tm
; caps..)): the host's wrap of a fn's closure (vtg_cop, then a fn's items,
; vtg_node 0, vtg_node 6 2). No new semantic hypothesis: exec-vm's
; agreement already takes it (ex-collok's (prim (:host 15 C))). Named, not
; proved: vtg_cop's op is the N_LAZY node, the runtime's kind 6 wrapping
; its one argument in a pending lazy seq (vm_node_hook, as eval_new's
; clotran.host.lazy_seq); vtg_fnhd's op for it an N_FN node of the same
; template, made at translation (mk_node, analyze_fn's shape), where the
; model's are (:host 15 tm), :mkclo and tm. vm.inc's encoding changed for
; this (it was one flat (:prim NODE caps..)); what runs is the same
; closure, wrapped the same. Tests: fuzz-vmtr-gen draws lazy seqs (kind
; 15, a fn's template). Cost: 5 steps and 2 a capture.

(in-package "ACL2")

(include-book "exec-vmtr")

(defconst *vtg40* 1099511627776)

; ---- THE TREE'S READS (vm.inc's vtg_kind .. vtg_c on the OBJ_AST) -----------------------------

(defun vtg-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x) nil (if (zp n) (car x) (vtg-nth (1- n) (cdr x)))))
(defthm vtg-nth-is-nth (equal (vtg-nth n x) (nth n x)))
(defun vtg-int (x) (declare (xargs :guard t)) (if (and (natp x) (< x *vtg40*)) x 0))
(defun vtg-kind (e) (declare (xargs :guard t)) (vtg-int (vtg-nth 0 e)))
(defun vtg-i2 (e) (declare (xargs :guard t)) (vtg-int (vtg-nth 1 e)))
(defun vtg-s2 (e) (declare (xargs :guard t)) (vtg-int (vtg-nth 4 e)))
(defun vtg-c (e) (declare (xargs :guard t)) (vtg-nth 3 e))
(defun vtg-nk (e) (declare (xargs :guard t)) (vtg-int (len (vtg-nth 2 e))))
(defun vtg-kid (e j) (declare (xargs :guard (natp j))) (vtg-nth j (vtg-nth 2 e)))
; whether a fn's or lazy seq's captures name a slot in lo .. hi-1 (vtg_rdcap:
; vm_reads_in's N_FN case on the template's capture pairs)
(defun vtg-rdcap (e lo hi) (declare (xargs :guard t)) (ec-call (ex-rdin (ec-call (ex-outers (vtg-nth 2 (vtg-c e)))) lo hi)))
; a fn's captures (vtg_ncap, vtg_capo: its template's (outer, inner) pairs):
; how many, capture j's outer slot
(defun vtg-ncap (e) (declare (xargs :guard t)) (vtg-int (len (ec-call (ex-outers (vtg-nth 2 (vtg-c e)))))))
(defun vtg-capo (e j) (declare (xargs :guard (natp j))) (vtg-int (vtg-nth j (ec-call (ex-outers (vtg-nth 2 (vtg-c e)))))))

(defthm vtg-int-range (and (natp (vtg-int x)) (< (vtg-int x) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-int x))) (:linear :corollary (< (vtg-int x) *vtg40*))))
(defthm vtg-ncap-range (and (natp (vtg-ncap e)) (< (vtg-ncap e) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-ncap e))) (:linear :corollary (< (vtg-ncap e) *vtg40*))))
(defthm vtg-capo-range (and (natp (vtg-capo e j)) (< (vtg-capo e j) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-capo e j))) (:linear :corollary (< (vtg-capo e j) *vtg40*))))
(defthm vtg-nth-count (<= (acl2-count (vtg-nth n x)) (acl2-count x)) :rule-classes :linear)
(defthm vtg-nth-count-cons (implies (consp x) (< (acl2-count (vtg-nth n x)) (acl2-count x))) :rule-classes :linear)
(defthm vtg-kid-count (implies (consp e) (< (acl2-count (vtg-kid e j)) (acl2-count e))) :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (disable vtg-nth-is-nth) :expand ((vtg-nth 2 e) (vtg-nth 1 (cdr e))))))
(defthm vtg-kind-consp (implies (not (equal (vtg-kind e) 0)) (consp e)) :rule-classes :forward-chaining)
(defthm vtg-kid-count-k (implies (not (equal (vtg-kind e) 0)) (< (acl2-count (vtg-kid e j)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable vtg-kid-count) :use vtg-kid-count)))
(defthm vtg-i2-range (< (vtg-i2 e) *vtg40*) :rule-classes :linear)
(defthm vtg-nk-range (< (vtg-nk e) *vtg40*) :rule-classes :linear)
(defthm vtg-s2-range (< (vtg-s2 e) *vtg40*) :rule-classes :linear)
; a case's table (vtg_ncs, vtg_cthen: slot 2's entries in gca_entries'
; order -- NAMED: the model's ex-c list order; the macro's tests are
; distinct, so at most one entry takes a value and the order is no matter):
; how many entries, and entry j's then node
(defun vtg-ncs (e) (declare (xargs :guard t)) (vtg-int (len (vtg-c e))))
(defun vtg-cthen (e j) (declare (xargs :guard (natp j))) (vtg-nth 1 (vtg-nth j (vtg-c e))))
(defthm vtg-ncs-range (and (natp (vtg-ncs e)) (< (vtg-ncs e) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-ncs e))) (:linear :corollary (< (vtg-ncs e) *vtg40*))))
(defthm vtg-ncs-consp (implies (< 0 (vtg-ncs e)) (consp e)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable vtg-int vtg-c vtg-nth))))
(defthm vtg-cthen-count (implies (consp e) (< (acl2-count (vtg-cthen e j)) (acl2-count e))) :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (e/d (vtg-c) (vtg-nth-is-nth))
                  :use ((:instance vtg-nth-count (n 1) (x (vtg-nth j (vtg-nth 3 e)))) (:instance vtg-nth-count (n j) (x (vtg-nth 3 e)))
                        (:instance vtg-nth-count-cons (n 3) (x e))))))
(defthm vtg-cthen-count-k (implies (not (equal (vtg-kind e) 0)) (< (acl2-count (vtg-cthen e j)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable vtg-cthen-count vtg-cthen) :use vtg-cthen-count)))
(defthm vtg-cthen-count-n (implies (< 0 (vtg-ncs e)) (< (acl2-count (vtg-cthen e j)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable vtg-cthen-count vtg-cthen vtg-ncs vtg-ncs-consp) :use (vtg-cthen-count vtg-ncs-consp))))
; a try's catches (vtg_ncs on an N_TRY its slot 2's count; vtg_cbody,
; vtg_cslot: catch j's body node and its slot -- each [class slot body]):
; how many, catch j's body, its slot
(defun vtg-cbody (e j) (declare (xargs :guard (natp j))) (vtg-nth 2 (vtg-nth j (vtg-c e))))
(defun vtg-cslot (e j) (declare (xargs :guard (natp j))) (vtg-int (vtg-nth 1 (vtg-nth j (vtg-c e)))))
(defthm vtg-cbody-count (implies (consp e) (< (acl2-count (vtg-cbody e j)) (acl2-count e))) :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (e/d (vtg-c) (vtg-nth-is-nth))
                  :use ((:instance vtg-nth-count (n 2) (x (vtg-nth j (vtg-nth 3 e)))) (:instance vtg-nth-count (n j) (x (vtg-nth 3 e)))
                        (:instance vtg-nth-count-cons (n 3) (x e))))))
(defthm vtg-cbody-count-n (implies (< 0 (vtg-ncs e)) (< (acl2-count (vtg-cbody e j)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable vtg-cbody-count vtg-cbody vtg-ncs vtg-ncs-consp) :use (vtg-cbody-count vtg-ncs-consp))))
(defthm vtg-cslot-range (and (natp (vtg-cslot e j)) (< (vtg-cslot e j) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-cslot e j))) (:linear :corollary (< (vtg-cslot e j) *vtg40*))))
(in-theory (disable vtg-int vtg-kid vtg-kind vtg-i2 vtg-s2 vtg-nk vtg-c vtg-ncs vtg-cthen vtg-cbody vtg-cslot))

; ---- THE BUILDER AND THE SCOPE ----------------------------------------------------------------

(defstobj vtb (vtb-stk :type t :initially nil) (vtb-cm :type t :initially nil) (vtb-sv :type t :initially nil)
  (vtb-cs :type t :initially nil))

(defun vtg-push (v vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-stk (cons v (vtb-stk vtb)) vtb))
(defun vtg-popn (n l acc)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) (mv acc l) (vtg-popn (- n 1) (cdr l) (cons (car l) acc))))
(defun vtg-op (op) (declare (xargs :guard t)) (case op (1 :if) (2 :let) (4 :loop) (5 :recur) (6 :prim) (7 :callv) (8 :applyv) (9 :try) (otherwise :throw)))

; (:const v), (:const nil) (vtg_const, vtg_nil)
(defun vtg-const (v vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (list :const v) vtb))
(defun vtg-nil (vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push '(:const nil) vtb))
; a Var: (:prim :clotran.vm/deref (:const v)), the host's deref (vtg_deref:
; vm_deref_of of vm_var_ref -- named: its constant is the Var, or the
; node itself when direct-linked (the link epoch), where the model's is the
; Var's value; exec-vm's ex-derefok says the deref answers that value)
(defun vtg-deref (e vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (list :prim :clotran.vm/deref (list :const (vtg-c e))) vtb))
; a call whose head is read at translation (exec-vmtr's ex-pk, vtg_pk): 1 a
; constant builtin's (its head a constant the runtime says is a builtin, no
; closure, not apply -- NAMED: vm.inc's OBJ_BUILTIN test where the model asks
; prim :clotran.vm/builtin), 2 a direct-linked Var's whose fn wraps a builtin
; at the call's count (NAMED: vm.inc's vm_linked_builtin -- i2 1 and the link
; epoch, wrapper_of -- where the model asks i2 1 and prim
; :clotran.vm/wraps), 3 any other Var's whose fn wraps one (NAMED: vm.inc's
; vm_wraps), 4 any other constant or Var whose value is an IFn, not apply
; (NAMED: vm.inc's is_ifn of the constant, or of the Var's value or linked fn
; now, where the model asks prim :ifn of v), 0 any other; vtg_hd pushes
; ex-phd's items -- the builtin, the head's own (:const v) or deref, or
; :clotran.vm/callw and the Var's (:const var) (NAMED: vm_var_ref's, the Var or
; the linked node, where the model's is v) -- then (:prim items.. args..)
; (vtg_node 6), at 4 (:callv head args..) (vtg_node 7)
(defun vtg-pk (e) (declare (xargs :guard t)) (ec-call (ex-pk e)))
(defun vtg-hd (e vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-stk (ec-call (revappend (ec-call (ex-phd e)) (vtb-stk vtb))) vtb))
; a collection's kind: a vector, map, set, new or dot (ex-cop's ops; vtg-tr
; walks its kids as a recur's args); its op ex-cop (vtg_cop -- NAMED: vm.inc
; pushes the node itself, the runtime's kind 6, vm_node_hook building it)
(defun vtg-coll (k) (declare (xargs :guard t)) (or (equal k 7) (equal k 8) (equal k 9) (equal k 21) (equal k 22) (equal k 10) (equal k 20) (equal k 23) (equal k 24)))
(defun vtg-cop (e vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (ec-call (ex-cop e)) vtb))
; a fn's head items :mkclo and its template (vtg_fnhd -- NAMED: vm.inc
; pushes :prim and the N_FN node itself, the runtime's kind 6)
(defun vtg-fnhd (e vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-stk (list* (vtg-c e) :mkclo (vtb-stk vtb)) vtb))
; a slot's read: its position in the scope, the fn's captures read in
; place -- cs is (np . m), the clause's np parameters and m captures, the
; captures' positions np .. np+m-1 of the scope -- as exec-vmcs's ex-cs
; reads them: (:capt j) for capture j, a position past them m lower
; (vtg_local: vm_slot_ref, its map the positions so lowered)
(defun vtg-local (s vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (ec-call (ex-cloc (ec-call (ex-pos s (vtb-cm vtb))) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0))) vtb)))
; (op items..) of the top n, the deepest first, op 0 the items alone (vtg_node)
(defun vtg-node (op n vtb)
  (declare (xargs :stobjs vtb :guard (and (signed-byte-p 64 op) (signed-byte-p 64 n))))
  (mv-let (items rest) (vtg-popn (nfix n) (vtb-stk vtb) nil)
    (update-vtb-stk (cons (if (equal op 0) items (cons (vtg-op op) items)) rest) vtb)))
; ex-trcall's parts (every other call: the head bound at the scope's last
; position p, a dead one): (:local p) read, the captures in place (vtg_top:
; the depth's last local -- named: vm.inc's depth is the scope's length
; less the m captures, as vtg_local's map); (:prim :ifn (:local p)) the
; cast (vtg_cast -- named: vm.inc's prim :ifn is the runtime's kind 9,
; is_ifn, the tree's exec_core cast); (:throw (:const :not-fn)) its refusal
; (vtg_notfn -- named: vm.inc's is (:throw (:prim :clotran.vm/notfn
; (:local p))), the runtime's kind 10, refuse_not_fn of the head, as
; exec_core's action 23: it throws the host's error where the model's
; throws :not-fn, and nothing runs between)
(defun vtg-top (vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (ec-call (ex-cloc (- (len (vtb-cm vtb)) 1) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0))) vtb)))
(defun vtg-cast (vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (list :prim :ifn (ec-call (ex-cloc (- (len (vtb-cm vtb)) 1) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0)))) vtb)))
(defun vtg-notfn (vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push '(:throw (:const :not-fn)) vtb))
; a case's entry j's test, its items :case and (:const t), t the entry's
; test, then (:prim :case (:const t) (:local p)) of them and vtg_top
; (vtg_cstest -- NAMED: vm.inc's items are the N_CASE node itself and
; (:const then_j), then_j the entry's then node: the op a node, the
; runtime's kind 6, vm_node_hook answering whether case_branch's probe of
; the value takes entry j (its then is then_j), where the model's are :case
; and (:const t), exec-vm's prim :case of t and the value)
(defun vtg-cstest (e j vtb) (declare (xargs :stobjs vtb :guard (natp j)))
  (let ((vtb (vtg-push :case vtb))) (vtg-push (list :const (vtg-nth 0 (vtg-nth j (vtg-c e)))) vtb)))
;; a letfn's j-th init, (:mkgrp (j . shape) caps..) as exec-vmtr's ex-trlf
; makes it in the letfn's scope, the captures read in place (vtg_lfinit --
; NAMED: vm.inc's is (:prim NODE (:const j) caps.. (:local p_0) ..
; (:local p_j-1)), the op the letfn node itself, the runtime's kind 6,
; vm_node_hook building fn j's closure and patching the group's captures
; among it and the earlier lets' closures p_0 .. p_j-1 (exec_letfn's
; refresh_captures: one group, its fns identical), a group capture
; (:const nil) where the model's is (:const (:grp nil m)) -- the model's
; x2-seal of the j-th; its own work linear in the captures, its host's)
(defun vtg-lfinit (e j vtb)
  (declare (xargs :stobjs vtb :guard (natp j)))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (list* :mkgrp (cons j (ec-call (ex-lfshape e 0)))
                     (ec-call (ex-cs t (ec-call (ex-lfargs e 0 (vtb-cm vtb))) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0))))
              vtb)))
; a letfn's slots s .. s+n-1 new positions, none blanked (vtg_lfbinds: vtg_bind each)
(defun vtg-lfbinds (s n vtb)
  (declare (xargs :stobjs vtb :guard t))
  (update-vtb-cm (ec-call (binary-append (true-list-fix (vtb-cm vtb)) (ec-call (ex-slots s n)))) vtb))
;; a try's parts (exec-vmtr's ex-trh, ex-trfin), the thrown value at the
; scope's next position p: catch j's test (:prim :isa (:const c) (:local p)),
; c its class (vtg_catest -- NAMED: vm.inc's is (:prim NODE (:const j)
; (:local p)), the try node the op of the runtime's kind 6, vm_node_hook's
; N_TRY with two values answering catch_matches of catch j's class and the
; value, where the model's is exec-vm's prim :isa under ex-isaok); the
; rethrow (:throw (:local p)) at the walk's end and twice in a finally's
; handler (vtg_rethrow -- NAMED: vm.inc's is (:prim NODE (:local p)), the
; runtime's kind 6, vm_node_hook's N_TRY with one value answering its throw,
; (:throw . p) as prim's throw unwinds as :throw's, the host's error raised
; again from what vm_caught kept of it when p is the value it caught -- its
; message and trace, as the tree's implicit rethrows keep kst%msg -- else as
; N_THROW raises p); what the catches may clear blanked (vtg_blankcs:
; nothing, as vtg_blank)
(defun vtg-catest (e j vtb)
  (declare (xargs :stobjs vtb :guard (natp j)))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (list :prim :isa (list :const (vtg-nth 0 (vtg-nth j (vtg-c e))))
                    (ec-call (ex-cloc (len (vtb-cm vtb)) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0))))
              vtb)))
(defun vtg-rethrow (e vtb)
  (declare (xargs :stobjs vtb :guard t) (ignore e))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (list :throw (ec-call (ex-cloc (len (vtb-cm vtb)) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0)))) vtb)))
(defun vtg-blankcs (e vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (ec-call (ex-blank (ec-call (ex-clr :cs e 0)) (vtb-cm vtb))) vtb))
; slot s a new position (vtg_bind: the slot's local the depth, the depth one more)
(defun vtg-bind (s vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list s)) vtb))
; a dead local: a new position no slot names (vtg_dead: the depth one more)
(defun vtg-dead (vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list nil)) vtb))
; what x may clear blanked (vtg_blank: nothing, named above)
(defun vtg-blank (x vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (ec-call (ex-blank (ec-call (ex-clr :m x 0)) (vtb-cm vtb))) vtb))
; a loop's slots s .. s+n-1 new positions, their old ones blanked (vtg_binds:
; vtg_bind each, its map the slot's new local)
(defun vtg-binds (s n vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((ls (ec-call (ex-slots s n)))) (update-vtb-cm (ec-call (binary-append (ec-call (ex-blank ls (true-list-fix (vtb-cm vtb)))) ls)) vtb)))
; the scope kept, and given back (vtg_save, vtg_restore: the depth and the binds since)
(defun vtg-save (vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-sv (cons (vtb-cm vtb) (vtb-sv vtb)) vtb))
(defun vtg-restore (vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let* ((sv (vtb-sv vtb)) (vtb (update-vtb-cm (if (consp sv) (car sv) nil) vtb)))
    (update-vtb-sv (if (consp sv) (cdr sv) nil) vtb)))

; every other kind: vm.inc's own translation (vtg_other: vm_tr), pushing
; one expression and leaving the scope as it was
(encapsulate (((vtg-other * vtb) => vtb :formals (x vtb) :guard t))
  (local (defun vtg-other (x vtb) (declare (xargs :stobjs vtb :guard t) (ignore x)) (vtg-nil vtb))))

; ---- THE TRANSLATION --------------------------------------------------------------------------

;; WHETHER A LOOP'S INITS ARE INDEPENDENT (exec-vmtr's ex-rd, ex-lind): vtg-rd
; flg 0 whether node e reads a slot in lo .. hi-1, flg 1 whether children i..
; of e do; vtg-lind whether init i.. reads none of the loop's slots before it
(defthm vtg-nk-consp (implies (< 0 (vtg-nk e)) (consp e)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable vtg-nk vtg-int vtg-nth))))
(defthm vtg-kid-count-nk (implies (< (nfix i) (vtg-nk e)) (< (acl2-count (vtg-kid e i)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :use vtg-nk-consp :in-theory (disable vtg-nk-consp))))
(defun vtg-rd (flg e i lo hi)
  (declare (xargs :guard (and (natp flg) (natp i) (< i *vtg40*) (natp lo) (natp hi)) :verify-guards nil
                  :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-nk e) (nfix i))) *vtg40*))
                  :well-founded-relation o<))
  (if (equal flg 1)
      (let ((i (nfix i)))
        (if (< i (vtg-nk e))
            (if (vtg-rd 0 (vtg-kid e i) 0 lo hi) t (vtg-rd 1 e (+ 1 i) lo hi))
          nil))
    (let ((k (vtg-kind e)))
      (cond ((or (equal k 1) (equal k 3)) nil)
            ((equal k 2) (and (<= lo (vtg-i2 e)) (< (vtg-i2 e) hi)))
            ((or (equal k 14) (equal k 15)) (vtg-rdcap e lo hi))
            ((or (equal k 4) (equal k 5) (equal k 17) (equal k 7) (equal k 8) (equal k 9) (equal k 22) (equal k 21)
                 (equal k 6) (equal k 11) (equal k 12) (equal k 16))
             (vtg-rd 1 e 0 lo hi))
            (t t)))))
(verify-guards vtg-rd)
(defun vtg-lind (e i)
  (declare (xargs :guard (and (natp i) (< i *vtg40*)) :measure (nfix (- (vtg-i2 e) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (vtg-i2 e))
        (if (vtg-rd 0 (vtg-kid e i) 0 (vtg-s2 e) (+ (vtg-s2 e) i)) nil (vtg-lind e (+ 1 i)))
      t)))
; the reads of slots s+j .. s+n-1, in order (a dependent loop's (:local p)s)
(defun vtg-locs (s j n vtb)
  (declare (xargs :stobjs vtb :guard (and (natp s) (natp j) (natp n) (< s *vtg40*) (< n *vtg40*))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (let ((j (nfix j)))
    (if (< j (nfix n)) (let ((vtb (vtg-local (+ s j) vtb))) (vtg-locs s (+ 1 j) n vtb)) vtb)))
; a fn's captures from j, each its outer slot's read, in the template's order
(defun vtg-caps (e j vtb)
  (declare (xargs :stobjs vtb :guard (and (natp j) (< j *vtg40*)) :measure (nfix (- (vtg-ncap e) (nfix j)))))
  (let ((j (nfix j)))
    (if (< j (vtg-ncap e)) (let ((vtb (vtg-local (vtg-capo e j) vtb))) (vtg-caps e (+ 1 j) vtb)) vtb)))

; flg 0: node e; flg 1: a let*'s or a dependent loop's bindings from i, then
; its body; flg 2: a do's children from i; flg 3: a loop's inits or a
; recur's args from i, each pushed; flg 5: an independent loop's body after
; its inits from i are blanked; flg 6: a case's table walk from entry i
; (exec-vmtr's ex-trcs), the default at its end; flg 7: a letfn's lets from
; fn i (exec-vmtr's ex-trlf), each init in the letfn's scope, then its body;
; flg 8: a try's catch walk from catch i (exec-vmtr's ex-trh), the thrown
; value at the scope's next position, the rethrow at its end
(defun vtg-m (flg e i)
  (make-ord 1 (1+ (acl2-count e))
            (cond ((or (equal flg 1) (equal flg 5)) (nfix (- (vtg-i2 e) (nfix i))))
                  ((equal flg 2) (nfix (- (vtg-nk e) (nfix i))))
                  ((equal flg 3) (nfix (- (if (equal (vtg-kind e) 12) (vtg-i2 e) (vtg-nk e)) (nfix i))))
                  ((equal flg 6) (nfix (- (vtg-ncs e) (nfix i))))
                  ((equal flg 7) (nfix (- (vtg-i2 e) (nfix i))))
                  ((equal flg 8) (nfix (- (vtg-ncs e) (nfix i))))
                  (t *vtg40*))))

(defun vtg-tr (flg e i vtb)
  (declare (xargs :stobjs vtb :guard (and (natp flg) (natp i) (< i *vtg40*)) :verify-guards nil
                  :measure (vtg-m flg e i) :well-founded-relation o<))
  (cond
   ((equal flg 1)
    (if (or (equal (vtg-kind e) 11) (equal (vtg-kind e) 12))
        (let ((i (nfix i)))
          (if (< i (vtg-i2 e))
              (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                     (vtb (vtg-save vtb))
                     (vtb (vtg-blank (vtg-kid e i) vtb))
                     (vtb (vtg-bind (+ (vtg-s2 e) i) vtb))
                     (vtb (vtg-tr 1 e (+ 1 i) vtb))
                     (vtb (vtg-restore vtb)))
                (vtg-node 2 2 vtb))
            (if (equal (vtg-kind e) 12)
                ; (:loop ((:local p) ..) body), the slots then the loop's
                (let* ((vtb (vtg-locs (vtg-s2 e) 0 (vtg-i2 e) vtb))
                       (vtb (vtg-node 0 (vtg-i2 e) vtb))
                       (vtb (vtg-save vtb))
                       (vtb (vtg-binds (vtg-s2 e) (vtg-i2 e) vtb))
                       (vtb (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb))
                       (vtb (vtg-restore vtb)))
                  (vtg-node 4 2 vtb))
              (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb))))
      (vtg-other e vtb)))
   ((equal flg 2)
    (if (equal (vtg-kind e) 5)
        (let ((i (nfix i)) (nk (vtg-nk e)))
          (cond ((zp nk) (vtg-nil vtb))
                ((< i (- nk 1))
                 (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                        (vtb (vtg-save vtb))
                        (vtb (vtg-blank (vtg-kid e i) vtb))
                        (vtb (vtg-dead vtb))
                        (vtb (vtg-tr 2 e (+ 1 i) vtb))
                        (vtb (vtg-restore vtb)))
                   (vtg-node 2 2 vtb)))
                (t (vtg-tr 0 (vtg-kid e (- nk 1)) 0 vtb))))
      (vtg-other e vtb)))
   ((equal flg 3)
    (if (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16) (equal (vtg-kind e) 6) (vtg-coll (vtg-kind e)))
        (let ((i (nfix i)))
          (if (< i (if (equal (vtg-kind e) 12) (vtg-i2 e) (vtg-nk e)))
              (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                     (vtb (vtg-save vtb))
                     (vtb (vtg-blank (vtg-kid e i) vtb))
                     (vtb (vtg-tr 3 e (+ 1 i) vtb)))
                (vtg-restore vtb))
            vtb))
      (vtg-other e vtb)))
   ((equal flg 5)
    (if (equal (vtg-kind e) 12)
        (let ((i (nfix i)))
          (if (< i (vtg-i2 e))
              (let* ((vtb (vtg-save vtb))
                     (vtb (vtg-blank (vtg-kid e i) vtb))
                     (vtb (vtg-tr 5 e (+ 1 i) vtb)))
                (vtg-restore vtb))
            (let* ((vtb (vtg-save vtb))
                   (vtb (vtg-binds (vtg-s2 e) (vtg-i2 e) vtb))
                   (vtb (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb)))
              (vtg-restore vtb))))
      (vtg-other e vtb)))
   ((equal flg 6)
    ; (:if (:prim :case (:const t) (:local p)) then rest), p the test's
    ; position (the scope's last), else the default
    (if (equal (vtg-kind e) 19)
        (let ((i (nfix i)))
          (if (< i (vtg-ncs e))
              (let* ((vtb (vtg-cstest e i vtb))
                     (vtb (vtg-top vtb))
                     (vtb (vtg-node 6 3 vtb))
                     (vtb (vtg-tr 0 (vtg-cthen e i) 0 vtb))
                     (vtb (vtg-tr 6 e (+ 1 i) vtb)))
                (vtg-node 1 3 vtb))
            (vtg-tr 0 (vtg-kid e 1) 0 vtb)))
      (vtg-other e vtb)))
   ((equal flg 7)
    ; (:let init_i rest), every init in the letfn's scope; the body in it
    ; and the group's slots
    (if (equal (vtg-kind e) 13)
        (let ((i (nfix i)))
          (if (< i (vtg-i2 e))
              (let* ((vtb (vtg-lfinit e i vtb))
                     (vtb (vtg-tr 7 e (+ 1 i) vtb)))
                (vtg-node 2 2 vtb))
            (let* ((vtb (vtg-save vtb))
                   (vtb (vtg-lfbinds (vtg-s2 e) (vtg-i2 e) vtb))
                   (vtb (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb)))
              (vtg-restore vtb))))
      (vtg-other e vtb)))
   ((equal flg 8)
    ; (:if (:prim :isa (:const c) (:local p)) body rest), the body in the
    ; scope and the catch's slot at p; at the end the rethrow
    (if (equal (vtg-kind e) 18)
        (let ((i (nfix i)))
          (if (< i (vtg-ncs e))
              (let* ((vtb (vtg-catest e i vtb))
                     (vtb (vtg-save vtb))
                     (vtb (vtg-bind (vtg-cslot e i) vtb))
                     (vtb (vtg-tr 0 (vtg-cbody e i) 0 vtb))
                     (vtb (vtg-restore vtb))
                     (vtb (vtg-tr 8 e (+ 1 i) vtb)))
                (vtg-node 1 3 vtb))
            (vtg-rethrow e vtb)))
      (vtg-other e vtb)))
   (t
    (let ((k (vtg-kind e)))
      (cond ((equal k 1) (vtg-const (vtg-c e) vtb))
            ((equal k 3) (vtg-deref e vtb))
            ((equal k 2) (vtg-local (vtg-i2 e) vtb))
            ((equal k 4)
             (let* ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))
                    (vtb (vtg-save vtb))
                    (vtb (vtg-blank (vtg-kid e 0) vtb))
                    (vtb (vtg-tr 0 (vtg-kid e 1) 0 vtb))
                    (vtb (if (< 2 (vtg-nk e)) (vtg-tr 0 (vtg-kid e 2) 0 vtb) (vtg-nil vtb)))
                    (vtb (vtg-restore vtb)))
               (vtg-node 1 3 vtb)))
            ((equal k 17) (let ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))) (vtg-node 3 1 vtb)))
            ((equal k 11) (vtg-tr 1 e 0 vtb))
            ((equal k 5) (vtg-tr 2 e 0 vtb))
            ; a loop whose inits read none before them: (:loop (init ..) body)
            ((equal k 12)
             (if (vtg-lind e 1)
                 (let* ((vtb (vtg-tr 3 e 0 vtb))
                        (vtb (vtg-node 0 (vtg-i2 e) vtb))
                        (vtb (vtg-tr 5 e 0 vtb)))
                   (vtg-node 4 2 vtb))
               (vtg-tr 1 e 0 vtb)))
            ((equal k 16) (let ((vtb (vtg-tr 3 e 0 vtb))) (vtg-node 5 (vtg-nk e) vtb)))
            ; a builtin's call: (:prim f args..), the args in the call's scope
            ((and (equal k 6) (equal (vtg-pk e) 4)) (let* ((vtb (vtg-hd e vtb)) (vtb (vtg-tr 3 e 1 vtb))) (vtg-node 7 (vtg-nk e) vtb)))
            ((and (equal k 6) (equal (vtg-pk e) 3)) (let* ((vtb (vtg-hd e vtb)) (vtb (vtg-tr 3 e 1 vtb))) (vtg-node 6 (+ 1 (vtg-nk e)) vtb)))
            ((and (equal k 6) (not (equal (vtg-pk e) 0))) (let* ((vtb (vtg-hd e vtb)) (vtb (vtg-tr 3 e 1 vtb))) (vtg-node 6 (vtg-nk e) vtb)))
            ; every other call, ex-trcall: (:let head (:if (:prim :ifn (:local p))
            ; (:applyv (:local p) args..) (:throw (:const :not-fn)))), the args
            ; in the scope with the head's position p dead
            ((equal k 6)
             (let* ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))
                    (vtb (vtg-save vtb))
                    (vtb (vtg-blank (vtg-kid e 0) vtb))
                    (vtb (vtg-dead vtb))
                    (vtb (vtg-cast vtb))
                    (vtb (vtg-top vtb))
                    (vtb (vtg-tr 3 e 1 vtb))
                    (vtb (vtg-node 8 (vtg-nk e) vtb))
                    (vtb (vtg-notfn vtb))
                    (vtb (vtg-node 1 3 vtb))
                    (vtb (vtg-restore vtb)))
               (vtg-node 2 2 vtb)))
            ; a case: (:let test walk), the walk in the scope with the
            ; test's position p dead
            ((equal k 19)
             (let* ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))
                    (vtb (vtg-save vtb))
                    (vtb (vtg-blank (vtg-kid e 0) vtb))
                    (vtb (vtg-dead vtb))
                    (vtb (vtg-tr 6 e 0 vtb))
                    (vtb (vtg-restore vtb)))
               (vtg-node 2 2 vtb)))
            ((equal k 13) (vtg-tr 7 e 0 vtb))
            ; (:try body walk), the walk in the body's scope blanked; with a
            ; finally F: (:let (:try that (:if F r r)) (:if F p p)), F in the
            ; scope the body and catches leave blanked and a dead position p
            ((equal k 18)
             (let* ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))
                    (vtb (vtg-save vtb))
                    (vtb (vtg-blank (vtg-kid e 0) vtb))
                    (vtb (vtg-tr 8 e 0 vtb))
                    (vtb (vtg-restore vtb))
                    (vtb (vtg-node 9 2 vtb)))
               (if (< 1 (vtg-nk e))
                   (let* ((vtb (vtg-save vtb))
                          (vtb (vtg-blank (vtg-kid e 0) vtb))
                          (vtb (vtg-blankcs e vtb))
                          (vtb (vtg-save vtb))
                          (vtb (vtg-dead vtb))
                          (vtb (vtg-tr 0 (vtg-kid e 1) 0 vtb))
                          (vtb (vtg-restore vtb))
                          (vtb (vtg-rethrow e vtb))
                          (vtb (vtg-rethrow e vtb))
                          (vtb (vtg-node 1 3 vtb))
                          (vtb (vtg-node 9 2 vtb))
                          (vtb (vtg-save vtb))
                          (vtb (vtg-dead vtb))
                          (vtb (vtg-tr 0 (vtg-kid e 1) 0 vtb))
                          (vtb (vtg-top vtb))
                          (vtb (vtg-top vtb))
                          (vtb (vtg-node 1 3 vtb))
                          (vtb (vtg-restore vtb))
                          (vtb (vtg-restore vtb)))
                     (vtg-node 2 2 vtb))
                 vtb)))
            ; a collection: (:prim op args..), the args as a recur's
            ((vtg-coll k) (let* ((vtb (vtg-cop e vtb)) (vtb (vtg-tr 3 e 0 vtb))) (vtg-node 6 (+ 1 (vtg-nk e)) vtb)))
            ; a fn: (:mkclo tm caps..)
            ((equal k 14) (let* ((vtb (vtg-fnhd e vtb)) (vtb (vtg-caps e 0 vtb))) (vtg-node 0 (+ 2 (vtg-ncap e)) vtb)))
            ; a lazy seq: (:prim op (:mkclo tm caps..))
            ((equal k 15) (let* ((vtb (vtg-cop e vtb)) (vtb (vtg-fnhd e vtb)) (vtb (vtg-caps e 0 vtb)) (vtb (vtg-node 0 (+ 2 (vtg-ncap e)) vtb))) (vtg-node 6 2 vtb)))
            (t (vtg-other e vtb)))))))

(verify-guards vtg-tr :hints (("Goal" :in-theory (disable vtg-blank vtg-bind vtg-binds vtg-locs vtg-dead vtg-save vtg-restore vtg-node vtg-local vtg-const vtg-deref vtg-hd vtg-pk vtg-nil vtg-top vtg-cast vtg-notfn vtg-cstest vtg-lfinit vtg-lfbinds vtg-catest vtg-rethrow vtg-blankcs vtg-cop vtg-fnhd vtg-caps))))

; whether the clause's body recurs to the fn -- exec-vmtr's ex-tlr, a recur
; in a tail place no loop is round: vm_clause's loop round the body only
; then (ex-fbtc). A let's bindings and a do's all but last are no tail; a
; case's default and thens are. flg 1: a case's thens from entry i.
(defun vtg-tlrw (flg e i)
  (declare (xargs :guard (and (natp flg) (natp i) (< i *vtg40*))
                  :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-ncs e) (nfix i))) *vtg40*))
                  :well-founded-relation o<))
  (if (equal flg 1)
      (let ((i (nfix i))) (if (< i (vtg-ncs e)) (if (vtg-tlrw 0 (vtg-cthen e i) 0) t (vtg-tlrw 1 e (+ 1 i))) nil))
    (let ((k (vtg-kind e)) (nk (vtg-nk e)))
      (cond ((equal k 16) t)
            ((equal k 4) (if (vtg-tlrw 0 (vtg-kid e 1) 0) t (if (< 2 nk) (vtg-tlrw 0 (vtg-kid e 2) 0) nil)))
            ((equal k 5) (if (zp nk) nil (vtg-tlrw 0 (vtg-kid e (- nk 1)) 0)))
            ((or (equal k 11) (equal k 13)) (vtg-tlrw 0 (vtg-kid e (vtg-i2 e)) 0))
            ((equal k 19) (if (vtg-tlrw 0 (vtg-kid e 1) 0) t (vtg-tlrw 1 e 0)))
            (t nil)))))
(defun vtg-tlr (e) (declare (xargs :guard t)) (vtg-tlrw 0 e 0))

; ---- IT IS EX-TR ------------------------------------------------------------------------------

; a node the generated kinds make up, its numbers in the reads' range
(defun vtg-ok (e)
  (and (consp e) (natp (nth 0 e)) (< (nth 0 e) *vtg40*) (natp (nth 1 e)) (< (nth 1 e) *vtg40*)
       (natp (nth 4 e)) (< (nth 4 e) *vtg40*) (< (len (nth 2 e)) *vtg40*)))
; every node of x in the reads' range (flg t: a list of nodes): what vtg-rd reads
(defun vtg-okt (flg x)
  (declare (xargs :measure (acl2-count x)))
  (cond ((atom x) t)
        (flg (and (vtg-okt nil (car x)) (vtg-okt t (cdr x))))
        (t (and (vtg-ok x) (vtg-okt t (vtg-nth 2 x))))))
; a fn's outer slots in the reads' range
(defun vtg-fnos (os) (if (atom os) t (and (natp (car os)) (< (car os) *vtg40*) (vtg-fnos (cdr os)))))
(defun vtg-fnok (e) (and (vtg-fnos (ex-outers (nth 2 (ex-c e)))) (< (len (ex-outers (nth 2 (ex-c e)))) *vtg40*)))
(defun vtg-frag (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o<))
  (cond ((not (vtg-ok e)) nil)
        ((equal flg 1)
         (and (or (equal (vtg-kind e) 11) (and (equal (vtg-kind e) 12) (vtg-okt nil e) (not (vtg-lind e 1))))
              (if (< (nfix i) (vtg-i2 e))
                  (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 1 e (+ 1 (nfix i))))
                (vtg-frag 0 (vtg-kid e (vtg-i2 e)) 0))))
        ((equal flg 2)
         (and (equal (vtg-kind e) 5)
              (cond ((zp (vtg-nk e)) t)
                    ((< (nfix i) (- (vtg-nk e) 1)) (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 2 e (+ 1 (nfix i)))))
                    (t (vtg-frag 0 (vtg-kid e (- (vtg-nk e) 1)) 0)))))
        ((equal flg 3)
         (and (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16) (equal (vtg-kind e) 6) (vtg-coll (vtg-kind e)))
              (if (< (nfix i) (if (equal (vtg-kind e) 12) (vtg-i2 e) (vtg-nk e)))
                  (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 3 e (+ 1 (nfix i))))
                t)))
        ((equal flg 5)
         (and (equal (vtg-kind e) 12) (vtg-okt nil e) (vtg-lind e 1)
              (if (< (nfix i) (vtg-i2 e)) (vtg-frag 5 e (+ 1 (nfix i))) (vtg-frag 0 (vtg-kid e (vtg-i2 e)) 0))))
        ((equal flg 6)
         (and (equal (vtg-kind e) 19) (< (len (vtg-c e)) *vtg40*)
              (if (< (nfix i) (vtg-ncs e)) (and (vtg-frag 0 (vtg-cthen e (nfix i)) 0) (vtg-frag 6 e (+ 1 (nfix i))))
                (vtg-frag 0 (vtg-kid e 1) 0))))
        ((equal flg 7)
         (and (equal (vtg-kind e) 13)
              (if (< (nfix i) (vtg-i2 e)) (vtg-frag 7 e (+ 1 (nfix i))) (vtg-frag 0 (vtg-kid e (vtg-i2 e)) 0))))
        ((equal flg 8)
         (and (equal (vtg-kind e) 18) (< (len (vtg-c e)) *vtg40*)
              (if (< (nfix i) (vtg-ncs e))
                  (and (< (ex-cslot e (nfix i)) *vtg40*) (vtg-frag 0 (vtg-cbody e (nfix i)) 0) (vtg-frag 8 e (+ 1 (nfix i))))
                t)))
        (t (let ((k (vtg-kind e)))
             (cond ((member k '(1 2 3)) t)
                   ((equal k 4) (and (vtg-frag 0 (vtg-kid e 0) 0) (vtg-frag 0 (vtg-kid e 1) 0)
                                     (or (<= (vtg-nk e) 2) (vtg-frag 0 (vtg-kid e 2) 0))))
                   ((equal k 17) (vtg-frag 0 (vtg-kid e 0) 0))
                   ((equal k 11) (vtg-frag 1 e 0))
                   ((equal k 5) (vtg-frag 2 e 0))
                   ((equal k 12) (and (vtg-okt nil e) (if (vtg-lind e 1) (and (vtg-frag 3 e 0) (vtg-frag 5 e 0)) (vtg-frag 1 e 0))))
                   ((equal k 16) (vtg-frag 3 e 0))
                   ((vtg-coll k) (vtg-frag 3 e 0))
                   ((or (equal k 14) (equal k 15)) (vtg-fnok e))
                   ((equal k 6) (and (vtg-frag 0 (vtg-kid e 0) 0) (vtg-frag 3 e 1)))
                   ((equal k 19) (and (< (len (vtg-c e)) *vtg40*) (vtg-frag 0 (vtg-kid e 0) 0) (vtg-frag 6 e 0)))
                   ((equal k 13) (vtg-frag 7 e 0))
                   ((equal k 18) (and (< (len (vtg-c e)) *vtg40*) (vtg-frag 0 (vtg-kid e 0) 0) (vtg-frag 8 e 0)
                                      (or (<= (vtg-nk e) 1) (vtg-frag 0 (vtg-kid e 1) 0))))
                   (t nil))))))

(defthm vtg-reads-ex
  (implies (vtg-ok e)
           (and (equal (vtg-kind e) (ex-kind e)) (equal (vtg-i2 e) (ex-i2 e)) (equal (vtg-s2 e) (ex-s2 e))
                (equal (vtg-nk e) (ex-nk e)) (equal (vtg-c e) (ex-c e))))
  :hints (("Goal" :in-theory (enable vtg-int vtg-kind vtg-i2 vtg-s2 vtg-nk vtg-c ex-kind ex-i2 ex-s2 ex-nk ex-c ex-kids))))
(defthm vtg-kid-ex (equal (vtg-kid e j) (ex-kid-of e (nfix j))) :hints (("Goal" :in-theory (enable vtg-kid ex-kid-of ex-kids))))
(defthm vtg-c-ex (equal (vtg-c e) (ex-c e)) :hints (("Goal" :in-theory (enable vtg-c ex-c))))
(defthm vtg-pk-ex (equal (vtg-pk e) (ex-pk e)))
(defthm vtg-ncs-ex (implies (< (len (ex-c e)) *vtg40*) (equal (vtg-ncs e) (len (ex-c e))))
  :hints (("Goal" :in-theory (enable vtg-ncs vtg-int))))
(defthm vtg-cthen-ex (equal (vtg-cthen e j) (ex-cthen e j)) :hints (("Goal" :in-theory (enable vtg-cthen ex-cthen))))
(defthm vtg-cbody-ex (equal (vtg-cbody e j) (ex-cbody e j)) :hints (("Goal" :in-theory (enable vtg-cbody ex-cbody vtg-c))))
(defthm vtg-cslot-ex (implies (< (ex-cslot e j) *vtg40*) (equal (vtg-cslot e j) (ex-cslot e j)))
  :hints (("Goal" :in-theory (enable vtg-cslot ex-cslot vtg-c vtg-int))))

(defthm ex-pk-0 (iff (equal (ex-pk e) 0) (not (ex-pcall e))) :hints (("Goal" :in-theory (enable ex-pcall))))
; such a call has its head: one child at least
(defthm ex-pcall-nk (implies (ex-pcall e) (< 0 (ex-nk e))) :rule-classes :forward-chaining
  :hints (("Goal" :use ex-pcall-head :in-theory (e/d (ex-nk ex-kid-of ex-kids) (ex-pcall-head)))))
; its translation (:prim items.. args..): one item, or two (callw's)
(defthm ex-pop-is (and (implies (equal (ex-pk e) 4) (equal (ex-pop e) :callv)) (implies (not (equal (ex-pk e) 4)) (equal (ex-pop e) :prim)))
  :hints (("Goal" :in-theory (enable ex-pop))))
(defthm ex-phd-len
  (implies (ex-pcall e) (and (true-listp (ex-phd e)) (equal (len (ex-phd e)) (if (equal (ex-pk e) 3) 2 1))))
  :hints (("Goal" :in-theory (enable ex-pcall ex-pk ex-phd))))

; vtg-rd is ex-rd, vtg-lind ex-lind, on a tree in the reads' range
(defthm vtg-okt-nth (implies (vtg-okt t l) (vtg-okt nil (nth j l))))
(defthm vtg-okt-kid (implies (vtg-okt nil e) (vtg-okt nil (ex-kid-of e j)))
  :hints (("Goal" :in-theory (enable ex-kid-of ex-kids) :expand ((vtg-okt nil e)))))
(defthm vtg-okt-ok (implies (and (vtg-okt nil e) (consp e)) (vtg-ok e)) :hints (("Goal" :expand ((vtg-okt nil e)))))
(defthm vtg-atom-reads (implies (not (consp e)) (and (equal (vtg-kind e) 0) (equal (vtg-i2 e) 0) (equal (vtg-nk e) 0)))
  :hints (("Goal" :in-theory (enable vtg-int vtg-kind vtg-i2 vtg-nk))))
(defthm vtg-okt-reads
  (implies (vtg-okt nil e)
           (and (equal (vtg-kind e) (if (consp e) (ex-kind e) 0)) (equal (vtg-i2 e) (ex-i2 e)) (equal (vtg-nk e) (ex-nk e))
                (equal (vtg-s2 e) (ex-s2 e))))
  :hints (("Goal" :cases ((consp e)) :in-theory (enable ex-i2 ex-nk ex-kids ex-s2 vtg-s2 vtg-int))))
(defthm vtg-rd-ex
  (implies (and (vtg-okt nil e) (natp lo) (natp hi) (or (not (equal flg 1)) (consp e)))
           (equal (vtg-rd flg e i lo hi) (ex-rd (equal flg 1) e i lo hi)))
  :hints (("Goal" :induct (vtg-rd flg e i lo hi) :in-theory (e/d (vtg-rdcap) (vtg-okt ex-kid-of vtg-ok))
                  :expand ((vtg-rd flg e i lo hi) (ex-rd nil e i lo hi) (ex-rd t e i lo hi)))))
(defthm vtg-lind-ex (implies (vtg-okt nil e) (equal (vtg-lind e i) (ex-lind e i)))
  :hints (("Goal" :induct (vtg-lind e i) :in-theory (disable vtg-okt ex-kid-of vtg-ok vtg-rd) :expand ((ex-lind e i) (vtg-lind e i)))))

(defthm true-list-fix-id (implies (true-listp x) (equal (true-list-fix x) x)))
(defthm true-listp-ex-blank (implies (true-listp cm) (true-listp (ex-blank ls cm))))

; ex-tr, one lemma a kind
(defthm ex-tr-gen-kinds
  (implies (consp e)
           (and (implies (equal (ex-kind e) 1) (equal (ex-tr :m e 0 cm) (list :const (ex-c e))))
                (implies (equal (ex-kind e) 3) (equal (ex-tr :m e 0 cm) (list :prim :clotran.vm/deref (list :const (ex-c e)))))
                (implies (equal (ex-kind e) 2) (equal (ex-tr :m e 0 cm) (list :local (ex-pos (ex-i2 e) cm))))
                (implies (equal (ex-kind e) 4)
                         (equal (ex-tr :m e 0 cm)
                                (list :if (ex-tr :m (ex-kid-of e 0) 0 cm)
                                      (ex-tr :m (ex-kid-of e 1) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm))
                                      (if (< 2 (ex-nk e)) (ex-tr :m (ex-kid-of e 2) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm)) '(:const nil)))))
                (implies (and (equal (ex-kind e) 6) (ex-pcall e)) (equal (ex-tr :m e 0 cm) (cons (ex-pop e) (append (ex-phd e) (ex-tr :call e 1 cm)))))
                (implies (and (equal (ex-kind e) 6) (not (ex-pcall e)))
                         (equal (ex-tr :m e 0 cm)
                                (ex-trcall (ex-tr :m (ex-kid-of e 0) 0 cm)
                                           (ex-tr :call e 1 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil))) (len cm))))
                (implies (equal (ex-kind e) 17) (equal (ex-tr :m e 0 cm) (list :throw (ex-tr :m (ex-kid-of e 0) 0 cm))))
                (implies (equal (ex-kind e) 11) (equal (ex-tr :m e 0 cm) (ex-tr :let e 0 cm)))
                (implies (and (or (equal (ex-kind e) 11) (and (equal (ex-kind e) 12) (not (ex-lind e 1)))) (natp i) (< i (ex-i2 e)))
                         (equal (ex-tr :let e i cm)
                                (list :let (ex-tr :m (ex-kid-of e i) 0 cm)
                                      (ex-tr :let e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list (+ (ex-s2 e) i)))))))
                (implies (and (equal (ex-kind e) 11) (natp i) (<= (ex-i2 e) i))
                         (equal (ex-tr :let e i cm) (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 cm)))
                (implies (equal (ex-kind e) 5) (equal (ex-tr :m e 0 cm) (ex-tr :do e 0 cm)))
                (implies (zp (ex-nk e)) (equal (ex-tr :do e i cm) '(:const nil)))
                (implies (and (natp i) (< i (- (ex-nk e) 1)))
                         (equal (ex-tr :do e i cm)
                                (list :let (ex-tr :m (ex-kid-of e i) 0 cm)
                                      (ex-tr :do e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list nil))))))
                (implies (and (natp i) (not (zp (ex-nk e))) (<= (- (ex-nk e) 1) i))
                         (equal (ex-tr :do e i cm) (ex-tr :m (ex-kid-of e (- (ex-nk e) 1)) 0 cm)))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank) :expand ((ex-tr :m e 0 cm) (ex-tr :let e i cm)))))
(defthm ex-tr-loop-kinds
  (implies (consp e)
           (and (implies (and (equal (ex-kind e) 12) (ex-lind e 1))
                         (equal (ex-tr :m e 0 cm) (list :loop (ex-tr :lin e 0 cm) (ex-tr :let e 0 cm))))
                (implies (and (equal (ex-kind e) 12) (not (ex-lind e 1))) (equal (ex-tr :m e 0 cm) (ex-tr :let e 0 cm)))
                (implies (equal (ex-kind e) 16) (equal (ex-tr :m e 0 cm) (cons :recur (ex-tr :rec e 0 cm))))
                (implies (and (equal (ex-kind e) 12) (ex-lind e 1) (natp i) (< i (ex-i2 e)))
                         (equal (ex-tr :let e i cm) (ex-tr :let e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm))))
                (implies (and (equal (ex-kind e) 12) (ex-lind e 1) (natp i) (<= (ex-i2 e) i))
                         (equal (ex-tr :let e i cm)
                                (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 (append (ex-blank (ex-slots (ex-s2 e) (ex-i2 e)) cm) (ex-slots (ex-s2 e) (ex-i2 e))))))
                (implies (and (equal (ex-kind e) 12) (not (ex-lind e 1)) (natp i) (<= (ex-i2 e) i))
                         (equal (ex-tr :let e i cm)
                                (list :loop (ex-locals (ex-slots (ex-s2 e) (ex-i2 e)) cm)
                                      (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 (append (ex-blank (ex-slots (ex-s2 e) (ex-i2 e)) cm) (ex-slots (ex-s2 e) (ex-i2 e)))))))
                (implies (and (natp i) (< i (ex-i2 e)))
                         (equal (ex-tr :lin e i cm) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :lin e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))))
                (implies (and (natp i) (<= (ex-i2 e) i)) (equal (ex-tr :lin e i cm) nil))
                (implies (and (natp i) (< i (ex-nk e)))
                         (equal (ex-tr :rec e i cm) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :rec e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))))
                (implies (and (natp i) (< i (ex-nk e)))
                         (equal (ex-tr :call e i cm) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :call e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))))
                (implies (and (natp i) (<= (ex-nk e) i)) (equal (ex-tr :call e i cm) nil))
                (implies (and (natp i) (<= (ex-nk e) i)) (equal (ex-tr :rec e i cm) nil))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-lind ex-locals ex-slots)
                  :expand ((ex-tr :m e 0 cm) (ex-tr :let e i cm) (ex-tr :lin e i cm) (ex-tr :rec e i cm) (ex-tr :call e i cm)))))
; a collection's translation, its kids' walk
(defthm ex-tr-coll-kinds
  (implies (consp e)
           (and (implies (vtg-coll (ex-kind e)) (equal (ex-tr :m e 0 cm) (list* :prim (ex-cop e) (ex-tr :coll e 0 cm))))
                (implies (and (natp i) (< i (ex-nk e)))
                         (equal (ex-tr :coll e i cm) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :coll e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))))
                (implies (and (natp i) (<= (ex-nk e) i)) (equal (ex-tr :coll e i cm) nil))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-cop) :expand ((ex-tr :m e 0 cm) (ex-tr :coll e i cm)))))
; a fn's translation
(defthm ex-tr-fn-kind
  (implies (and (consp e) (equal (ex-kind e) 14)) (equal (ex-tr :m e 0 cm) (list* :mkclo (ex-c e) (ex-locals (ex-outers (nth 2 (ex-c e))) cm))))
  :hints (("Goal" :expand ((ex-tr :m e 0 cm)))))
; a lazy seq's
(defthm ex-tr-lazy-kind
  (implies (and (consp e) (equal (ex-kind e) 15)) (equal (ex-tr :m e 0 cm) (list :prim (ex-cop e) (list* :mkclo (ex-c e) (ex-locals (ex-outers (nth 2 (ex-c e))) cm)))))
  :hints (("Goal" :expand ((ex-tr :m e 0 cm)))))
; how many a loop's inits and a recur's args are, the loop's slots and their reads
(defun vtg-lin-ind (e i c)
  (declare (irrelevant c))
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i))) :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank)))))
  (if (< (nfix i) (ex-nk e)) (vtg-lin-ind e (1+ (nfix i)) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) c)) t))
(defun vtg-lin-ind2 (e i c)
  (declare (irrelevant c))
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix i))) :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank)))))
  (if (< (nfix i) (ex-i2 e)) (vtg-lin-ind2 e (1+ (nfix i)) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) c)) t))
(defthm vtg-len-rec
  (implies (consp e) (and (equal (len (ex-tr :rec e i c)) (nfix (- (ex-nk e) (nfix i)))) (true-listp (ex-tr :rec e i c))))
  :hints (("Goal" :induct (vtg-lin-ind e i c) :in-theory (disable ex-kid-of ex-clr ex-blank ex-tr) :expand ((ex-tr :rec e i c)))))
(defthm vtg-len-call
  (implies (consp e) (and (equal (len (ex-tr :call e i c)) (nfix (- (ex-nk e) (nfix i)))) (true-listp (ex-tr :call e i c))))
  :hints (("Goal" :induct (vtg-lin-ind e i c) :in-theory (disable ex-kid-of ex-clr ex-blank ex-tr) :expand ((ex-tr :call e i c)))))
(defthm vtg-len-coll
  (implies (consp e) (and (equal (len (ex-tr :coll e i c)) (nfix (- (ex-nk e) (nfix i)))) (true-listp (ex-tr :coll e i c))))
  :hints (("Goal" :induct (vtg-lin-ind e i c) :in-theory (disable ex-kid-of ex-clr ex-blank ex-tr) :expand ((ex-tr :coll e i c)))))
(defthm vtg-len-lin
  (implies (consp e) (and (equal (len (ex-tr :lin e i c)) (nfix (- (ex-i2 e) (nfix i)))) (true-listp (ex-tr :lin e i c))))
  :hints (("Goal" :induct (vtg-lin-ind2 e i c) :in-theory (disable ex-kid-of ex-clr ex-blank ex-tr) :expand ((ex-tr :lin e i c)))))
(defthm vtg-len-slots (and (equal (len (ex-slots s n)) (nfix n)) (true-listp (ex-slots s n))))
(defthm vtg-len-locals (and (equal (len (ex-locals ls c)) (len ls)) (true-listp (ex-locals ls c))))
(defthm vtg-len-cs (and (equal (len (ex-cs t x np m)) (len x)) (implies (true-listp x) (true-listp (ex-cs t x np m))))
  :hints (("Goal" :induct (len x) :expand ((ex-cs t x np m)))))

; THE STATE as its three fields, and each shim on it
(defun vtg-st (stk cm sv cs) (list stk cm sv cs))
(defun vtg-np (cs) (if (consp cs) (car cs) 0))
(defun vtg-nm (cs) (if (consp cs) (cdr cs) 0))
(defthm vtg-shims
  (and (equal (vtg-const v (vtg-st s c sv cs)) (vtg-st (cons (list :const v) s) c sv cs))
       (equal (vtg-nil (vtg-st s c sv cs)) (vtg-st (cons '(:const nil) s) c sv cs))
       (equal (vtg-deref e (vtg-st s c sv cs)) (vtg-st (cons (list :prim :clotran.vm/deref (list :const (vtg-c e))) s) c sv cs))
       (equal (vtg-hd e (vtg-st s c sv cs)) (vtg-st (revappend (ex-phd e) s) c sv cs))
       (equal (vtg-local n (vtg-st s c sv cs)) (vtg-st (cons (ex-cs nil (list :local (ex-pos n c)) (vtg-np cs) (vtg-nm cs)) s) c sv cs))
       (equal (vtg-save (vtg-st s c sv cs)) (vtg-st s c (cons c sv) cs))
       (equal (vtg-restore (vtg-st s c (cons c0 sv) cs)) (vtg-st s c0 sv cs))
       (equal (vtg-blank x (vtg-st s c sv cs)) (vtg-st s (ex-blank (ex-clr :m x 0) c) sv cs))
       (equal (vtg-bind n (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list n)) sv cs))
       (equal (vtg-binds n k (vtg-st s c sv cs)) (vtg-st s (append (ex-blank (ex-slots n k) (true-list-fix c)) (ex-slots n k)) sv cs))
       (equal (vtg-dead (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list nil)) sv cs))
       (equal (vtg-top (vtg-st s c sv cs)) (vtg-st (cons (ex-cloc (- (len c) 1) (vtg-np cs) (vtg-nm cs)) s) c sv cs))
       (equal (vtg-cast (vtg-st s c sv cs)) (vtg-st (cons (list :prim :ifn (ex-cloc (- (len c) 1) (vtg-np cs) (vtg-nm cs))) s) c sv cs))
       (equal (vtg-notfn (vtg-st s c sv cs)) (vtg-st (cons '(:throw (:const :not-fn)) s) c sv cs))
       (equal (vtg-node 1 3 (vtg-st (list* z y x s) c sv cs)) (vtg-st (cons (list :if x y z) s) c sv cs))
       (equal (vtg-node 2 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :let x y) s) c sv cs))
       (equal (vtg-node 4 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :loop x y) s) c sv cs))
       (equal (vtg-node 3 1 (vtg-st (list* x s) c sv cs)) (vtg-st (cons (list :throw x) s) c sv cs))
       (equal (vtg-node 6 3 (vtg-st (list* z y x s) c sv cs)) (vtg-st (cons (list :prim x y z) s) c sv cs))
       (equal (vtg-cstest e j (vtg-st s c sv cs)) (vtg-st (list* (list :const (nth 0 (nth j (ex-c e)))) :case s) c sv cs))
       (equal (vtg-lfinit e j (vtg-st s c sv cs))
              (vtg-st (cons (ex-cs nil (list* :mkgrp (cons j (ex-lfshape e 0)) (ex-lfargs e 0 c)) (vtg-np cs) (vtg-nm cs)) s) c sv cs))
       (equal (vtg-lfbinds n k (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (ex-slots n k)) sv cs))
       (equal (vtg-catest e j (vtg-st s c sv cs))
              (vtg-st (cons (list :prim :isa (list :const (nth 0 (nth j (ex-c e)))) (ex-cloc (len c) (vtg-np cs) (vtg-nm cs))) s) c sv cs))
       (equal (vtg-rethrow e (vtg-st s c sv cs)) (vtg-st (cons (list :throw (ex-cloc (len c) (vtg-np cs) (vtg-nm cs))) s) c sv cs))
       (equal (vtg-blankcs e (vtg-st s c sv cs)) (vtg-st s (ex-blank (ex-clr :cs e 0) c) sv cs))
       (equal (vtg-node 9 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :try x y) s) c sv cs))
       (equal (vtg-node 6 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :prim x y) s) c sv cs))
       (equal (vtg-cop e (vtg-st s c sv cs)) (vtg-st (cons (ex-cop e) s) c sv cs))
       (equal (vtg-fnhd e (vtg-st s c sv cs)) (vtg-st (revappend (list :mkclo (ex-c e)) s) c sv cs)))
  :hints (("Goal" :expand ((:free (n l acc) (vtg-popn n l acc))))))
; n items pushed in order, made one list (op 0) or node
(defun vtg-pind (l s k) (if (consp l) (vtg-pind (cdr l) (cons (car l) s) (+ 1 k)) (list s k)))
(defthm vtg-popn-rev
  (implies (natp k) (equal (vtg-popn (+ (len l) k) (revappend l s) acc) (vtg-popn k s (append l acc))))
  :hints (("Goal" :induct (vtg-pind l s k) :expand ((vtg-popn (+ 1 k) (cons (car l) s) (append (cdr l) acc)) (revappend l s)))))
(defthm vtg-node-rev
  (implies (and (equal n (len l)) (true-listp l))
           (equal (vtg-node op n (vtg-st (revappend l s) c sv cs))
                  (vtg-st (cons (if (equal op 0) l (cons (vtg-op op) l)) s) c sv cs)))
  :hints (("Goal" :use ((:instance vtg-popn-rev (k 0) (acc nil))) :in-theory (disable vtg-popn-rev vtg-op)
                  :expand ((:free (x acc) (vtg-popn 0 x acc))))))
; the same with one item pushed before them (a builtin call's head)
(defthm vtg-node-rev1
  (implies (and (equal n (+ 1 (len l))) (true-listp l))
           (equal (vtg-node op n (vtg-st (revappend l (cons h s)) c sv cs))
                  (vtg-st (cons (if (equal op 0) (cons h l) (list* (vtg-op op) h l)) s) c sv cs)))
  :hints (("Goal" :use ((:instance vtg-node-rev (l (cons h l)))) :in-theory (disable vtg-node-rev))))
; the same with items a pushed before them (a call's items)
(defthm vtg-revappend-append (equal (revappend (append a l) s) (revappend l (revappend a s))))
(defthm vtg-node-rev2
  (implies (and (equal n (+ (len a) (len l))) (true-listp a) (true-listp l))
           (equal (vtg-node op n (vtg-st (revappend l (revappend a s)) c sv cs))
                  (vtg-st (cons (if (equal op 0) (append a l) (cons (vtg-op op) (append a l))) s) c sv cs)))
  :hints (("Goal" :use ((:instance vtg-node-rev (l (append a l)))) :do-not-induct t :in-theory (disable vtg-node-rev))))
; the same with two items pushed before them (a fn's :mkclo and template)
(defthm vtg-node-rev3
  (implies (and (equal n (+ 2 (len l))) (true-listp l))
           (equal (vtg-node 0 n (vtg-st (revappend l (list* h2 h1 s)) c sv cs))
                  (vtg-st (cons (list* h1 h2 l) s) c sv cs)))
  :hints (("Goal" :use ((:instance vtg-node-rev2 (op 0) (a (list h1 h2)))) :in-theory (disable vtg-node-rev2))))
(defthm ex-blank-nil-true (implies (true-listp c) (true-listp (append c (list n)))))
(defthm vtg-len-blank (equal (len (ex-blank ls c)) (len c)))
(defthm vtg-len-app (equal (len (append a b)) (+ (len a) (len b))))
; a call's head a node: one child at least
(defthm vtg-kid0-nk (implies (consp (ex-kid-of e 0)) (< 0 (ex-nk e))) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ex-nk ex-kid-of ex-kids))))
; ex-trcall's translation with the captures read in place
(defthm vtg-cs-trcall
  (equal (ex-cs nil (ex-trcall h args p) np m)
         (list :let (ex-cs nil h np m)
               (list :if (list :prim :ifn (ex-cloc p np m)) (list* :applyv (ex-cloc p np m) (ex-cs t args np m)) '(:throw (:const :not-fn)))))
  :hints (("Goal" :in-theory (enable ex-trcall) :expand ((:free (x) (ex-cs nil x np m)) (:free (x y) (ex-cs t (cons x y) np m))))))
(defthm vtg-pk-not-pcall (implies (not (ex-pcall e)) (equal (ex-pk e) 0)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ex-pcall))))
(in-theory (disable ex-trcall ex-cloc))
(defthm vtg-ok-consp (implies (vtg-ok e) (consp e)) :rule-classes :forward-chaining)
; the rewrite of the captures, through the nodes the generated kinds make
(defthm vtg-cs-nodes
  (and (equal (ex-cs nil (list :const v) np m) (list :const v))
       (equal (ex-cs nil (list :prim op (list :const v)) np m) (list :prim op (list :const v)))
       (equal (ex-cs nil (list* :prim op x) np m) (list* :prim op (ex-cs t x np m)))
       (equal (ex-cs nil (list* :mkgrp op x) np m) (list* :mkgrp op (ex-cs t x np m)))
       (equal (ex-cs nil (list* :mkclo op x) np m) (list* :mkclo op (ex-cs t x np m)))
       (equal (ex-cs nil (list :if x y z) np m) (list :if (ex-cs nil x np m) (ex-cs nil y np m) (ex-cs nil z np m)))
       (equal (ex-cs nil (list :let x y) np m) (list :let (ex-cs nil x np m) (ex-cs nil y np m)))
       (equal (ex-cs nil (list :loop x y) np m) (list :loop (ex-cs t x np m) (ex-cs nil y np m)))
       (equal (ex-cs nil (cons :recur x) np m) (cons :recur (ex-cs t x np m)))
       (equal (ex-cs nil (list :throw x) np m) (list :throw (ex-cs nil x np m)))
       (equal (ex-cs nil (list :try x y) np m) (list :try (ex-cs nil x np m) (ex-cs nil y np m)))
       (equal (ex-cs nil (list :local p) np m) (ex-cloc p np m))))
; a call's items read no slot: its args' captures read in place
(defthm vtg-cs-pcall
  (and (implies (and (ex-pcall e) (not (equal (ex-pk e) 4)))
                (equal (ex-cs nil (cons :prim (append (ex-phd e) x)) np m) (cons :prim (append (ex-phd e) (ex-cs t x np m)))))
       (implies (equal (ex-pk e) 4)
                (equal (ex-cs nil (cons :callv (append (ex-phd e) x)) np m) (cons :callv (append (ex-phd e) (ex-cs t x np m))))))
  :hints (("Goal" :in-theory (enable ex-pcall ex-pk ex-phd) :expand ((:free (y z) (ex-cs t (cons y z) np m))))))
; a case's translation: its tree, its thens', and the walk's with the
; captures read in place
(defthm ex-tr-case-kinds
  (implies (consp e)
           (and (implies (equal (ex-kind e) 19)
                         (equal (ex-tr :m e 0 cm)
                                (list :let (ex-tr :m (ex-kid-of e 0) 0 cm)
                                      (ex-trcs (ex-c e) (ex-tr :ct e 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)))
                                               (ex-tr :m (ex-kid-of e 1) 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)))
                                               (len cm)))))
                (implies (< (nfix i) (len (ex-c e)))
                         (equal (ex-tr :ct e i cm) (cons (ex-tr :m (ex-cthen e (nfix i)) 0 cm) (ex-tr :ct e (1+ (nfix i)) cm))))
                (implies (<= (len (ex-c e)) (nfix i)) (equal (ex-tr :ct e i cm) nil))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-cthen) :expand ((ex-tr :m e 0 cm) (ex-tr :ct e i cm)))))
(defthm vtg-cs-trcs
  (and (implies (not (consp ct)) (equal (ex-cs nil (ex-trcs ct ts d p) np m) (ex-cs nil d np m)))
       (implies (consp ct)
                (equal (ex-cs nil (ex-trcs ct ts d p) np m)
                       (list :if (list :prim :case (list :const (nth 0 (car ct))) (ex-cloc p np m)) (ex-cs nil (car ts) np m)
                             (ex-cs nil (ex-trcs (cdr ct) (cdr ts) d p) np m)))))
  :hints (("Goal" :expand ((ex-trcs ct ts d p)
                           (ex-cs nil (list :if (list :prim :case (list :const (nth 0 (car ct))) (list :local p)) (car ts) (ex-trcs (cdr ct) (cdr ts) d p)) np m)
                           (:free (x y z) (ex-cs t (list* x y z) np m)) (:free (x) (ex-cs t (list x) np m))
                           (ex-cs nil (list :prim :case (list :const (nth 0 (car ct))) (list :local p)) np m)
                           (ex-cs nil (list :const (nth 0 (car ct))) np m) (ex-cs nil (list :local p) np m)))))
;; a letfn's translation: its lets, each init in the letfn's scope, then
; its body in that scope and the group's slots
(defthm ex-tr-lf-kinds
  (implies (consp e)
           (and (implies (equal (ex-kind e) 13)
                         (equal (ex-tr :m e 0 cm)
                                (ex-trlf e 0 cm (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 (append cm (ex-slots (ex-s2 e) (ex-i2 e)))))))
                (implies (and (natp j) (< j (ex-i2 e)))
                         (equal (ex-trlf e j cm x) (list :let (list* :mkgrp (cons j (ex-lfshape e 0)) (ex-lfargs e 0 cm)) (ex-trlf e (1+ j) cm x))))
                (implies (and (natp j) (<= (ex-i2 e) j)) (equal (ex-trlf e j cm x) x))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-slots ex-lfshape ex-lfargs) :expand ((ex-tr :m e 0 cm) (ex-trlf e j cm x)))))
;; a try's translation: its body's, its catch walk's over the catches'
; bodies (each in the walk's scope and its slot), its finally's (in the
; scope the body and catches leave blanked and a dead position)
(defthm vtg-blank-append-ls (equal (ex-blank (append a b) c) (ex-blank b (ex-blank a c))) :rule-classes nil)
(defthm ex-tr-try-kinds
  (implies (consp e)
           (and (implies (equal (ex-kind e) 18)
                         (equal (ex-tr :m e 0 cm)
                                (ex-trtry (ex-tr :m (ex-kid-of e 0) 0 cm)
                                          (ex-tr :cs e 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm))
                                          (ex-tr :m (ex-kid-of e 1) 0 (append (ex-blank (ex-clr :cs e 0) (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm)) (list nil)))
                                          (ex-c e) (< 1 (ex-nk e)) (len cm))))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-cbody ex-cslot ex-trtry)
                  :use ((:instance vtg-blank-append-ls (a (ex-clr :m (ex-kid-of e 0) 0)) (b (ex-clr :cs e 0)) (c cm)))
                  :expand ((ex-tr :m e 0 cm) (ex-tr :fin e 0 (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm))))))
(defthm ex-tr-try-cs
  (implies (consp e)
           (and (implies (< (nfix i) (len (ex-c e)))
                         (equal (ex-tr :cs e i cm)
                                (cons (ex-tr :m (ex-cbody e (nfix i)) 0 (append cm (list (ex-cslot e (nfix i))))) (ex-tr :cs e (1+ (nfix i)) cm))))
                (implies (<= (len (ex-c e)) (nfix i)) (equal (ex-tr :cs e i cm) nil))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-cbody ex-cslot) :expand ((ex-tr :cs e i cm)))))
(defthm vtg-cs-trh
  (and (implies (not (consp ct)) (equal (ex-cs nil (ex-trh ct hs p) np m) (list :throw (ex-cloc p np m))))
       (implies (consp ct)
                (equal (ex-cs nil (ex-trh ct hs p) np m)
                       (list :if (list :prim :isa (list :const (nth 0 (car ct))) (ex-cloc p np m)) (ex-cs nil (car hs) np m)
                             (ex-cs nil (ex-trh (cdr ct) (cdr hs) p) np m)))))
  :hints (("Goal" :expand ((ex-trh ct hs p)
                           (:free (x y z) (ex-cs nil (list :if x y z) np m)) (:free (x) (ex-cs nil (list :throw x) np m))
                           (:free (x y z) (ex-cs t (list* x y z) np m)) (:free (x) (ex-cs t (list x) np m))
                           (:free (x y) (ex-cs nil (list :prim :isa x y) np m))
                           (ex-cs nil (list :const (nth 0 (car ct))) np m) (ex-cs nil (list :local p) np m)))))
(defthm vtg-cs-trtry
  (equal (ex-cs nil (ex-trtry b hs f ct fin p) np m)
         (if fin
             (list :let (list :try (list :try (ex-cs nil b np m) (ex-cs nil (ex-trh ct hs p) np m))
                              (list :if (ex-cs nil f np m) (list :throw (ex-cloc p np m)) (list :throw (ex-cloc p np m))))
                   (list :if (ex-cs nil f np m) (ex-cloc p np m) (ex-cloc p np m)))
           (list :try (ex-cs nil b np m) (ex-cs nil (ex-trh ct hs p) np m))))
  :hints (("Goal" :in-theory (e/d (ex-trtry ex-trfin) (ex-trh))
                  :expand ((:free (x y) (ex-cs nil (list :try x y) np m)) (:free (x y z) (ex-cs nil (list :if x y z) np m))
                           (:free (x y) (ex-cs nil (list :let x y) np m)) (:free (x) (ex-cs nil (list :throw x) np m))
                           (:free (x y z) (ex-cs t (list* x y z) np m)) (:free (x) (ex-cs t (list x) np m))
                           (ex-cs nil (list :local p) np m)))))
(defthm vtg-nthcdr-parts
  (implies (and (natp i) (< i (len l)))
           (and (consp (nthcdr i l)) (equal (car (nthcdr i l)) (nth i l)) (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))))
(defthm vtg-nthcdr-end (implies (and (natp i) (<= (len l) i)) (not (consp (nthcdr i l)))))
(in-theory (disable ex-trcs ex-cthen ex-trlf ex-lfshape ex-lfargs ex-trtry ex-trh ex-cbody ex-cop))
(in-theory (disable ex-cs vtg-np vtg-nm ex-lind ex-rd vtg-rd))
(in-theory (disable ex-tr vtg-st vtg-const vtg-deref vtg-hd vtg-pk vtg-nil vtg-top vtg-cast vtg-notfn vtg-local vtg-save vtg-restore vtg-blank vtg-bind vtg-binds vtg-dead vtg-node vtg-frag vtg-ok
                    vtg-locs vtg-lind vtg-okt vtg-lfinit vtg-lfbinds vtg-catest vtg-rethrow vtg-blankcs vtg-cop vtg-fnhd vtg-caps vtg-fnok))

(defun vtg-locs-ind (s j n stk c cs)
  (declare (xargs :measure (nfix (- (nfix n) (nfix j)))))
  (if (< (nfix j) (nfix n))
      (vtg-locs-ind s (+ 1 (nfix j)) n (cons (ex-cs nil (list :local (ex-pos (+ s (nfix j)) c)) (vtg-np cs) (vtg-nm cs)) stk) c cs)
    (list s stk c cs)))
(defthm vtg-slots-zp (implies (zp n) (equal (ex-slots s n) nil)))
(defthm vtg-locs-st
  (implies (and (natp s) (natp j) (natp n))
           (equal (vtg-locs s j n (vtg-st stk c sv cs))
                  (vtg-st (revappend (ex-cs t (ex-locals (ex-slots (+ s j) (- n j)) c) (vtg-np cs) (vtg-nm cs)) stk) c sv cs)))
  :hints (("Goal" :induct (vtg-locs-ind s j n stk c cs) :in-theory (disable vtg-local vtg-np vtg-nm)
                  :expand ((ex-slots (+ s j) (- n j)) (vtg-locs s j n (vtg-st stk c sv cs))))))

; a fn's captures read: ex-locals of its outer slots, the captures in place
(defun vtg-caps-ind (j os stk c cs)
  (declare (xargs :measure (len os)))
  (if (consp os) (vtg-caps-ind (+ 1 j) (cdr os) (cons (ex-cs nil (list :local (ex-pos (car os) c)) (vtg-np cs) (vtg-nm cs)) stk) c cs) (list j stk c cs)))
(defthm vtg-nthcdr-cdr (implies (natp j) (equal (nthcdr (+ 1 j) l) (cdr (nthcdr j l)))) :hints (("Goal" :in-theory (enable nthcdr))))
(defthm vtg-caps-nthcdr
  (implies (and (natp j) (vtg-fnos os) (< (len (ex-outers (nth 2 (ex-c e)))) *vtg40*) (equal os (nthcdr j (ex-outers (nth 2 (ex-c e))))))
           (equal (vtg-caps e j (vtg-st stk c sv cs))
                  (vtg-st (revappend (ex-cs t (ex-locals os c) (vtg-np cs) (vtg-nm cs)) stk) c sv cs)))
  :hints (("Goal" :induct (vtg-caps-ind j os stk c cs) :in-theory (e/d (vtg-ncap vtg-capo vtg-int) (vtg-local vtg-np vtg-nm vtg-nthcdr-parts vtg-nthcdr-end))
                  :expand ((vtg-caps e j (vtg-st stk c sv cs)) (ex-locals os c) (:free (x y) (ex-cs t (cons x y) (vtg-np cs) (vtg-nm cs)))))
          (and stable-under-simplificationp '(:use ((:instance vtg-nthcdr-parts (i j) (l (ex-outers (nth 2 (ex-c e))))) (:instance vtg-nthcdr-end (i j) (l (ex-outers (nth 2 (ex-c e))))))))))
(in-theory (disable vtg-nthcdr-cdr))
(defthm vtg-caps-st
  (implies (vtg-fnok e)
           (equal (vtg-caps e 0 (vtg-st stk c sv cs))
                  (vtg-st (revappend (ex-cs t (ex-locals (ex-outers (nth 2 (ex-c e))) c) (vtg-np cs) (vtg-nm cs)) stk) c sv cs)))
  :hints (("Goal" :use ((:instance vtg-caps-nthcdr (j 0) (os (ex-outers (nth 2 (ex-c e)))))) :in-theory (enable vtg-fnok))))
(defthm vtg-ncap-is (implies (vtg-fnok e) (equal (vtg-ncap e) (len (ex-outers (nth 2 (ex-c e))))))
  :hints (("Goal" :in-theory (enable vtg-ncap vtg-int vtg-fnok))))

(defthm vtg-frag-facts
  (implies (vtg-frag flg e i)
           (and (vtg-ok e)
                (implies (equal flg 1) (or (equal (vtg-kind e) 11) (and (equal (vtg-kind e) 12) (vtg-okt nil e) (not (vtg-lind e 1)))))
                (implies (equal flg 2) (equal (vtg-kind e) 5))
                (implies (equal flg 3) (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16) (equal (vtg-kind e) 6) (vtg-coll (vtg-kind e))))
                (implies (equal flg 5) (and (equal (vtg-kind e) 12) (vtg-okt nil e) (vtg-lind e 1)))
                (implies (equal flg 6) (and (equal (vtg-kind e) 19) (< (len (ex-c e)) *vtg40*)))
                (implies (equal flg 7) (equal (vtg-kind e) 13))
                (implies (equal flg 8) (and (equal (vtg-kind e) 18) (< (len (ex-c e)) *vtg40*)))
                (implies (not (member flg '(1 2 3 5 6 7 8))) (member (vtg-kind e) (quote (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24))))
                (implies (and (not (member flg '(1 2 3 5 6 7 8))) (equal (vtg-kind e) 12)) (vtg-okt nil e))
                (implies (and (not (member flg '(1 2 3 5 6 7 8))) (member (vtg-kind e) '(18 19))) (< (len (ex-c e)) *vtg40*))
                (implies (and (not (member flg '(1 2 3 5 6 7 8))) (member (vtg-kind e) '(14 15))) (vtg-fnok e))))
  :rule-classes :forward-chaining :hints (("Goal" :expand ((vtg-frag flg e i)))))

; ex-tr's translation x with the captures read in place
(defun vtg-cw (x cs) (ex-cs nil x (vtg-np cs) (vtg-nm cs)))
(defun vtg-cwl (x cs) (ex-cs t x (vtg-np cs) (vtg-nm cs)))
; the induction: vtg-tr's, each call on the state it is handed
(defun vtg-ind (flg e i s c sv cs)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :verify-guards nil :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-cthen-ex vtg-cbody-ex)))))
  (declare (irrelevant s c sv cs))
  (let ((ls (ex-slots (vtg-s2 e) (vtg-i2 e))))
    (cond
     ((equal flg 1)
      (if (or (equal (vtg-kind e) 11) (equal (vtg-kind e) 12))
          (if (< (nfix i) (vtg-i2 e))
              (let ((k (vtg-kid e (nfix i))))
                (list (vtg-ind 0 k 0 s c sv cs)
                      (vtg-ind 1 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s)
                               (append (ex-blank (ex-clr :m k 0) c) (list (+ (vtg-s2 e) (nfix i)))) (cons c sv) cs)))
            (if (equal (vtg-kind e) 12)
                (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 (cons (vtg-cwl (ex-locals ls c) cs) s) (append (ex-blank ls c) ls) (cons c sv) cs)
              (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 s c sv cs)))
        nil))
     ((equal flg 2)
      (if (equal (vtg-kind e) 5)
          (cond ((zp (vtg-nk e)) nil)
                ((< (nfix i) (- (vtg-nk e) 1))
                 (let ((k (vtg-kid e (nfix i))))
                   (list (vtg-ind 0 k 0 s c sv cs)
                         (vtg-ind 2 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s)
                                  (append (ex-blank (ex-clr :m k 0) c) (list nil)) (cons c sv) cs))))
                (t (vtg-ind 0 (vtg-kid e (- (vtg-nk e) 1)) 0 s c sv cs)))
        nil))
     ((equal flg 3)
      (if (and (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16) (equal (vtg-kind e) 6) (vtg-coll (vtg-kind e))) (< (nfix i) (if (equal (vtg-kind e) 12) (vtg-i2 e) (vtg-nk e))))
          (let ((k (vtg-kid e (nfix i))))
            (list (vtg-ind 0 k 0 s c sv cs)
                  (vtg-ind 3 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s) (ex-blank (ex-clr :m k 0) c) (cons c sv) cs)))
        nil))
     ((equal flg 5)
      (if (equal (vtg-kind e) 12)
          (if (< (nfix i) (vtg-i2 e))
              (vtg-ind 5 e (+ 1 (nfix i)) s (ex-blank (ex-clr :m (vtg-kid e (nfix i)) 0) c) (cons c sv) cs)
            (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 s (append (ex-blank ls c) ls) (cons c sv) cs))
        nil))
     ((equal flg 6)
      (if (equal (vtg-kind e) 19)
          (if (< (nfix i) (vtg-ncs e))
              (let* ((th (vtg-cthen e (nfix i)))
                     (ts (list :prim :case (list :const (nth 0 (nth (nfix i) (ex-c e)))) (ex-cloc (- (len c) 1) (vtg-np cs) (vtg-nm cs)))))
                (list (vtg-ind 0 th 0 (cons ts s) c sv cs)
                      (vtg-ind 6 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m th 0 c) cs) (cons ts s)) c sv cs)))
            (vtg-ind 0 (vtg-kid e 1) 0 s c sv cs))
        nil))
     ((equal flg 7)
      (if (equal (vtg-kind e) 13)
          (if (< (nfix i) (vtg-i2 e))
              (vtg-ind 7 e (+ 1 (nfix i)) (cons (vtg-cw (list* :mkgrp (cons (nfix i) (ex-lfshape e 0)) (ex-lfargs e 0 c)) cs) s) c sv cs)
            (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 s (append c (ex-slots (vtg-s2 e) (vtg-i2 e))) (cons c sv) cs))
        nil))
     ((equal flg 8)
      (if (equal (vtg-kind e) 18)
          (if (< (nfix i) (vtg-ncs e))
              (let* ((b (vtg-cbody e (nfix i))) (c1 (append c (list (vtg-cslot e (nfix i)))))
                     (ts (list :prim :isa (list :const (nth 0 (nth (nfix i) (ex-c e)))) (ex-cloc (len c) (vtg-np cs) (vtg-nm cs)))))
                (list (vtg-ind 0 b 0 (cons ts s) c1 (cons c sv) cs)
                      (vtg-ind 8 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m b 0 c1) cs) (cons ts s)) c sv cs)))
            nil)
        nil))
     (t
      (let ((k (vtg-kind e)))
        (cond ((equal k 4)
               (let* ((k0 (vtg-kid e 0)) (c1 (ex-blank (ex-clr :m k0 0) c)) (t0 (vtg-cw (ex-tr :m k0 0 c) cs)))
                 (list (vtg-ind 0 k0 0 s c sv cs)
                       (vtg-ind 0 (vtg-kid e 1) 0 (cons t0 s) c1 (cons c sv) cs)
                       (vtg-ind 0 (vtg-kid e 2) 0 (cons (vtg-cw (ex-tr :m (vtg-kid e 1) 0 c1) cs) (cons t0 s)) c1 (cons c sv) cs))))
              ((equal k 17) (vtg-ind 0 (vtg-kid e 0) 0 s c sv cs))
              ((equal k 11) (vtg-ind 1 e 0 s c sv cs))
              ((equal k 5) (vtg-ind 2 e 0 s c sv cs))
              ((equal k 12)
               (if (vtg-lind e 1)
                   (list (vtg-ind 3 e 0 s c sv cs) (vtg-ind 5 e 0 (cons (vtg-cwl (ex-tr :lin e 0 c) cs) s) c sv cs))
                 (vtg-ind 1 e 0 s c sv cs)))
              ((equal k 16) (vtg-ind 3 e 0 s c sv cs))
              ((vtg-coll k) (vtg-ind 3 e 0 (cons (ex-cop e) s) c sv cs))
              ((or (equal k 14) (equal k 15)) nil)
              ((and (equal k 6) (not (equal (vtg-pk e) 0))) (vtg-ind 3 e 1 (revappend (ex-phd e) s) c sv cs))
              ((equal k 6)
               (let* ((k0 (vtg-kid e 0)) (c1 (append (ex-blank (ex-clr :m k0 0) c) (list nil)))
                      (p (ex-cloc (len c) (vtg-np cs) (vtg-nm cs))))
                 (list (vtg-ind 0 k0 0 s c sv cs)
                       (vtg-ind 3 e 1 (list* p (list :prim :ifn p) (vtg-cw (ex-tr :m k0 0 c) cs) s) c1 (cons c sv) cs))))
              ((equal k 19)
               (let* ((k0 (vtg-kid e 0)) (c1 (append (ex-blank (ex-clr :m k0 0) c) (list nil))))
                 (list (vtg-ind 0 k0 0 s c sv cs)
                       (vtg-ind 6 e 0 (cons (vtg-cw (ex-tr :m k0 0 c) cs) s) c1 (cons c sv) cs))))
              ((equal k 13) (vtg-ind 7 e 0 s c sv cs))
              ((equal k 18)
               (let* ((k0 (vtg-kid e 0)) (c1 (ex-blank (ex-clr :m k0 0) c)) (b (vtg-cw (ex-tr :m k0 0 c) cs))
                      (x (list :try b (vtg-cw (ex-trh (ex-c e) (ex-tr :cs e 0 c1) (len c)) cs)))
                      (c2 (ex-blank (ex-clr :cs e 0) c1)) (cf (append c2 (list nil)))
                      (r (list :throw (ex-cloc (len c) (vtg-np cs) (vtg-nm cs))))
                      (fx (vtg-cw (ex-tr :m (vtg-kid e 1) 0 cf) cs)))
                 (list (vtg-ind 0 k0 0 s c sv cs)
                       (vtg-ind 8 e 0 (cons b s) c1 (cons c sv) cs)
                       (vtg-ind 0 (vtg-kid e 1) 0 (cons x s) cf (cons c2 (cons c sv)) cs)
                       (vtg-ind 0 (vtg-kid e 1) 0 (cons (list :try x (list :if fx r r)) s) cf (cons c2 (cons c sv)) cs))))
              (t nil)))))))

; what vtg-tr pushes: ex-tr's at the place flg names, the captures read in
; place -- one expression, or (flg 3) the inits' or args' each in order
(defun vtg-want (flg e i c cs)
  (vtg-cw (cond ((or (equal flg 1) (equal flg 5)) (ex-tr :let e (nfix i) c)) ((equal flg 2) (ex-tr :do e (nfix i) c))
                ((equal flg 6) (ex-trcs (nthcdr (nfix i) (ex-c e)) (ex-tr :ct e (nfix i) c) (ex-tr :m (ex-kid-of e 1) 0 c) (- (len c) 1)))
                ((equal flg 7) (ex-trlf e (nfix i) c (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 (append c (ex-slots (ex-s2 e) (ex-i2 e))))))
                ((equal flg 8) (ex-trh (nthcdr (nfix i) (ex-c e)) (ex-tr :cs e (nfix i) c) (len c)))
                (t (ex-tr :m e 0 c)))
          cs))
(defun vtg-out (flg e i c cs s)
  (if (equal flg 3)
      (revappend (vtg-cwl (cond ((equal (vtg-kind e) 16) (ex-tr :rec e (nfix i) c)) ((equal (vtg-kind e) 6) (ex-tr :call e (nfix i) c)) ((equal (vtg-kind e) 12) (ex-tr :lin e (nfix i) c)) (t (ex-tr :coll e (nfix i) c))) cs) s)
    (cons (vtg-want flg e i c cs) s)))

(defthm vtg-tr-st
  (implies (and (vtg-frag flg e i) (true-listp c))
           (equal (vtg-tr flg e i (vtg-st s c sv cs))
                  (vtg-st (vtg-out flg e i c cs s) c sv cs)))
  :hints (("Goal" :induct (vtg-ind flg e i s c sv cs)
                  :in-theory (disable ex-kid-of ex-clr ex-blank ex-slots ex-locals)
                  :expand ((:free (flg) (vtg-frag flg e i)) (:free (flg) (vtg-tr flg e i (vtg-st s c sv cs)))))
          (and stable-under-simplificationp '(:in-theory (e/d (vtg-kid-ex vtg-ok) (ex-kid-of ex-clr ex-blank ex-slots ex-locals))))))

(defthm list4-id (implies (and (true-listp x) (equal (len x) 4)) (equal (list (car x) (cadr x) (caddr x) (cadddr x)) x))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x)) (true-listp x) (true-listp (cdr x))
                            (true-listp (cddr x)) (true-listp (cdddr x)) (true-listp (cddddr x))))))
(defthm vtb-as-st (implies (vtbp vtb) (equal (vtg-st (vtb-stk vtb) (vtb-cm vtb) (vtb-sv vtb) (vtb-cs vtb)) vtb))
  :hints (("Goal" :in-theory (e/d (vtg-st) (list4-id)) :use ((:instance list4-id (x vtb))))))
(defthm vtg-st-fields
  (and (equal (vtb-stk (vtg-st s c sv cs)) s) (equal (vtb-cm (vtg-st s c sv cs)) c) (equal (vtb-sv (vtg-st s c sv cs)) sv)
       (equal (vtb-cs (vtg-st s c sv cs)) cs))
  :hints (("Goal" :in-theory (enable vtg-st))))

; and so on the stobj: on a tree of the generated kinds the generated
; translation pushes exactly ex-tr's (vtg-out: at flg 0 one expression), the captures read in place (the
; fn's clause body's, exec-vmtr's ex-fbtc), the scope and the saves as
; they were
(defthm vtg-tr-ex-tr
  (implies (and (vtg-frag flg e i) (vtbp vtb) (true-listp (vtb-cm vtb)))
           (and (equal (vtb-stk (vtg-tr flg e i vtb)) (vtg-out flg e i (vtb-cm vtb) (vtb-cs vtb) (vtb-stk vtb)))
                (equal (vtb-cm (vtg-tr flg e i vtb)) (vtb-cm vtb))
                (equal (vtb-sv (vtg-tr flg e i vtb)) (vtb-sv vtb))
                (equal (vtb-cs (vtg-tr flg e i vtb)) (vtb-cs vtb))))
  :hints (("Goal" :use ((:instance vtg-tr-st (s (vtb-stk vtb)) (c (vtb-cm vtb)) (sv (vtb-sv vtb)) (cs (vtb-cs vtb))))
                  :in-theory (disable vtg-tr-st vtg-tr vtb-stk vtb-cm vtb-sv vtb-cs vtbp))))

; vtg-tlr is ex-tlr on a tree whose nodes it reaches are in the reads'
; range, a case's table among them
(defun vtg-tlrok (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-ncs e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-reads-ex vtg-cthen-ex)))))
  (if (equal flg 1)
      (and (< (len (ex-c e)) *vtg40*)
           (if (< (nfix i) (vtg-ncs e)) (and (vtg-tlrok 0 (vtg-cthen e (nfix i)) 0) (vtg-tlrok 1 e (+ 1 (nfix i)))) t))
    (and (vtg-ok e)
         (let ((k (vtg-kind e)) (nk (vtg-nk e)))
           (cond ((equal k 4) (and (vtg-tlrok 0 (vtg-kid e 1) 0) (or (<= nk 2) (vtg-tlrok 0 (vtg-kid e 2) 0))))
                 ((equal k 5) (or (zp nk) (vtg-tlrok 0 (vtg-kid e (- nk 1)) 0)))
                 ((or (equal k 11) (equal k 13)) (vtg-tlrok 0 (vtg-kid e (vtg-i2 e)) 0))
                 ((equal k 19) (and (< (len (ex-c e)) *vtg40*) (vtg-tlrok 0 (vtg-kid e 1) 0) (vtg-tlrok 1 e 0)))
                 (t t))))))
(defun vtg-tlr-ok (e) (vtg-tlrok 0 e 0))
(defun vtg-tli (i n) (declare (xargs :measure (nfix (- (nfix n) (nfix i))))) (if (< (nfix i) (nfix n)) (vtg-tli (1+ (nfix i)) n) t))
(defthm ex-tlr-let-at
  (implies (consp e) (equal (ex-tlr :let e i) (and (equal (ex-kind e) 11) (ex-tlr :m (ex-kid-of e (ex-i2 e)) 0))))
  :hints (("Goal" :induct (vtg-tli i (ex-i2 e)) :in-theory (disable ex-kid-of) :expand ((ex-tlr :let e i)))))
(defthm ex-tlr-do-at
  (implies (consp e) (equal (ex-tlr :do e i) (if (zp (ex-nk e)) nil (ex-tlr :m (ex-kid-of e (- (ex-nk e) 1)) 0))))
  :hints (("Goal" :induct (vtg-tli i (- (ex-nk e) 1)) :in-theory (disable ex-kid-of) :expand ((ex-tlr :do e i)))))
(defthm vtg-ex-c-atom (implies (not (consp e)) (equal (ex-c e) nil)) :hints (("Goal" :in-theory (enable ex-c))))
(defthm vtg-tlrw-ex-tlr
  (implies (vtg-tlrok flg e i) (equal (vtg-tlrw flg e i) (if (equal flg 1) (ex-tlr :ct e i) (ex-tlr :m e 0))))
  :hints (("Goal" :induct (vtg-tlrw flg e i) :in-theory (disable ex-kid-of ex-cthen)
                  :expand ((ex-tlr :m e 0) (ex-tlr :ct e i) (vtg-tlrok flg e i) (vtg-tlrw flg e i)))
          (and stable-under-simplificationp '(:in-theory (e/d (vtg-ncs vtg-int) (ex-kid-of ex-cthen))))))
(defthm vtg-tlr-ex-tlr
  (implies (vtg-tlr-ok e) (equal (vtg-tlr e) (ex-tlr :m e 0))))
(in-theory (disable vtg-tlr vtg-tlr-ok))

; ---- THE COST ---------------------------------------------------------------------------------
;
;; vtg-steps: vtg-tr's work as the generated code does it -- a step a call
; (a cycle among them) and a step a shim, vtg_binds n+1 (a bind a slot),
; vtg_lind one (its own walk vtg-lind-steps-bound), vtg_other's own work its
; host's; vtg-size: the nodes it reaches, a let's bindings and body among
; them, a loop's slots once more (read or bound again, their inits blanked).
; vtg-steps-bound: at most 16 steps a node -- each node's shims a constant.
(defun vtg-steps (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-cthen-ex vtg-cbody-ex)))))
  (let ((k (vtg-kind e)) (n2 (vtg-i2 e)) (body (vtg-kid e (vtg-i2 e))))
    (cond
     ((equal flg 1)
      (if (or (equal k 11) (equal k 12))
          (if (< (nfix i) n2)
              (+ 6 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 1 e (+ 1 (nfix i))))
            (if (equal k 12) (+ 7 (* 3 n2) (vtg-steps 0 body 0)) (+ 1 (vtg-steps 0 body 0))))
        2))
     ((equal flg 2)
      (if (equal k 5)
          (cond ((zp (vtg-nk e)) 2)
                ((< (nfix i) (- (vtg-nk e) 1)) (+ 7 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 2 e (+ 1 (nfix i)))))
                (t (+ 1 (vtg-steps 0 (vtg-kid e (- (vtg-nk e) 1)) 0))))
        2))
     ((equal flg 3)
      (if (and (or (equal k 12) (equal k 16) (equal k 6) (vtg-coll k)) (< (nfix i) (if (equal k 12) n2 (vtg-nk e))))
          (+ 4 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 3 e (+ 1 (nfix i))))
        2))
     ((equal flg 5)
      (if (equal k 12)
          (if (< (nfix i) n2) (+ 4 (vtg-steps 5 e (+ 1 (nfix i)))) (+ 5 n2 (vtg-steps 0 body 0)))
        2))
     ((equal flg 6)
      (if (equal k 19)
          (if (< (nfix i) (vtg-ncs e)) (+ 8 (vtg-steps 0 (vtg-cthen e (nfix i)) 0) (vtg-steps 6 e (+ 1 (nfix i))))
            (+ 2 (vtg-steps 0 (vtg-kid e 1) 0)))
        2))
     ((equal flg 7)
      (if (equal k 13)
          (if (< (nfix i) n2) (+ 3 (vtg-steps 7 e (+ 1 (nfix i)))) (+ 4 n2 (vtg-steps 0 body 0)))
        2))
     ((equal flg 8)
      (if (and (equal k 18) (< (nfix i) (vtg-ncs e))) (+ 7 (vtg-steps 0 (vtg-cbody e (nfix i)) 0) (vtg-steps 8 e (+ 1 (nfix i)))) 2))
     (t
      (cond ((equal k 4) (+ 5 (vtg-steps 0 (vtg-kid e 0) 0) (vtg-steps 0 (vtg-kid e 1) 0)
                            (if (< 2 (vtg-nk e)) (vtg-steps 0 (vtg-kid e 2) 0) 1)))
            ((equal k 17) (+ 2 (vtg-steps 0 (vtg-kid e 0) 0)))
            ((equal k 11) (+ 1 (vtg-steps 1 e 0)))
            ((equal k 5) (+ 1 (vtg-steps 2 e 0)))
            ((equal k 12) (if (vtg-lind e 1) (+ 4 (vtg-steps 3 e 0) (vtg-steps 5 e 0)) (+ 2 (vtg-steps 1 e 0))))
            ((equal k 16) (+ 2 (vtg-steps 3 e 0)))
            ((vtg-coll k) (+ 3 (vtg-steps 3 e 0)))
            ((equal k 14) (+ 3 (* 2 (vtg-ncap e))))
            ((equal k 15) (+ 5 (* 2 (vtg-ncap e))))
            ((equal k 6) (if (not (equal (vtg-pk e) 0)) (+ 4 (vtg-steps 3 e 1)) (+ 13 (vtg-steps 0 (vtg-kid e 0) 0) (vtg-steps 3 e 1))))
            ((equal k 19) (+ 7 (vtg-steps 0 (vtg-kid e 0) 0) (vtg-steps 6 e 0)))
            ((equal k 13) (+ 1 (vtg-steps 7 e 0)))
            ((equal k 18) (+ 6 (vtg-steps 0 (vtg-kid e 0) 0) (vtg-steps 8 e 0) (if (< 1 (vtg-nk e)) (+ 20 (* 2 (vtg-steps 0 (vtg-kid e 1) 0))) 0)))
            (t 2))))))
(defun vtg-size (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-cthen-ex vtg-cbody-ex)))))
  (let ((k (vtg-kind e)) (n2 (vtg-i2 e)) (body (vtg-kid e (vtg-i2 e))))
    (cond
     ((equal flg 1)
      (if (or (equal k 11) (equal k 12))
          (if (< (nfix i) n2)
              (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 1 e (+ 1 (nfix i))))
            (if (equal k 12) (+ n2 (vtg-size 0 body 0)) (vtg-size 0 body 0)))
        1))
     ((equal flg 2)
      (if (equal k 5)
          (cond ((zp (vtg-nk e)) 1)
                ((< (nfix i) (- (vtg-nk e) 1)) (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 2 e (+ 1 (nfix i)))))
                (t (vtg-size 0 (vtg-kid e (- (vtg-nk e) 1)) 0)))
        1))
     ((equal flg 3)
      (if (and (or (equal k 12) (equal k 16) (equal k 6) (vtg-coll k)) (< (nfix i) (if (equal k 12) n2 (vtg-nk e))))
          (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 3 e (+ 1 (nfix i))))
        1))
     ((equal flg 5)
      (if (equal k 12)
          (if (< (nfix i) n2) (+ 1 (vtg-size 5 e (+ 1 (nfix i)))) (+ n2 (vtg-size 0 body 0)))
        1))
     ((equal flg 6)
      (if (equal k 19)
          (if (< (nfix i) (vtg-ncs e)) (+ 1 (vtg-size 0 (vtg-cthen e (nfix i)) 0) (vtg-size 6 e (+ 1 (nfix i))))
            (vtg-size 0 (vtg-kid e 1) 0))
        1))
     ((equal flg 7)
      (if (equal k 13)
          (if (< (nfix i) n2) (+ 1 (vtg-size 7 e (+ 1 (nfix i)))) (+ n2 (vtg-size 0 body 0)))
        1))
     ((equal flg 8)
      (if (and (equal k 18) (< (nfix i) (vtg-ncs e))) (+ 1 (vtg-size 0 (vtg-cbody e (nfix i)) 0) (vtg-size 8 e (+ 1 (nfix i)))) 1))
     (t
      (cond ((equal k 4) (+ 1 (vtg-size 0 (vtg-kid e 0) 0) (vtg-size 0 (vtg-kid e 1) 0)
                            (if (< 2 (vtg-nk e)) (vtg-size 0 (vtg-kid e 2) 0) 0)))
            ((equal k 17) (+ 1 (vtg-size 0 (vtg-kid e 0) 0)))
            ((equal k 11) (+ 1 (vtg-size 1 e 0)))
            ((equal k 5) (+ 1 (vtg-size 2 e 0)))
            ((equal k 12) (if (vtg-lind e 1) (+ 1 (vtg-size 3 e 0) (vtg-size 5 e 0)) (+ 1 (vtg-size 1 e 0))))
            ((equal k 16) (+ 1 (vtg-size 3 e 0)))
            ((vtg-coll k) (+ 1 (vtg-size 3 e 0)))
            ((or (equal k 14) (equal k 15)) (+ 1 (vtg-ncap e)))
            ((equal k 6) (if (not (equal (vtg-pk e) 0)) (+ 1 (vtg-size 3 e 1)) (+ 1 (vtg-size 0 (vtg-kid e 0) 0) (vtg-size 3 e 1))))
            ((equal k 19) (+ 1 (vtg-size 0 (vtg-kid e 0) 0) (vtg-size 6 e 0)))
            ((equal k 13) (+ 1 (vtg-size 7 e 0)))
            ((equal k 18) (+ 1 (vtg-size 0 (vtg-kid e 0) 0) (vtg-size 8 e 0) (if (< 1 (vtg-nk e)) (* 2 (vtg-size 0 (vtg-kid e 1) 0)) 0)))
            (t 1))))))
(defthm vtg-steps-bound-flag
  (<= (vtg-steps flg e i) (if (member flg '(1 2 3 5 6 7 8)) (+ 1 (* 16 (vtg-size flg e i))) (- (* 16 (vtg-size flg e i)) 7)))
  :rule-classes nil
  :hints (("Goal" :induct (vtg-steps flg e i) :in-theory (disable vtg-kid-ex vtg-lind)
                  :expand ((:free (flg) (vtg-steps flg e i)) (:free (flg) (vtg-size flg e i))))))
(defthm vtg-steps-bound (<= (vtg-steps 0 e 0) (* 16 (vtg-size 0 e 0)))
  :rule-classes :linear :hints (("Goal" :use ((:instance vtg-steps-bound-flag (flg 0) (i 0))))))

; vtg-lind's work: vtg-rd's walk to its end (an answer found only stops it
; sooner), 2 steps a node and a child it walks (vtg-rd-size), vtg_rdcap
; one; the inits' walks and 3 steps an init (vtg-lind-size).
; vtg-lind-steps-bound: at most 6 steps a node it reaches.
(defun vtg-rd-walks (k)
  (member k '(4 5 17 7 8 9 22 21 6 11 12 16)))
(defun vtg-rd-steps (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-nk e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-cthen-ex vtg-cbody-ex)))))
  (if (equal flg 1)
      (if (< (nfix i) (vtg-nk e)) (+ 2 (vtg-rd-steps 0 (vtg-kid e (nfix i)) 0) (vtg-rd-steps 1 e (+ 1 (nfix i)))) 1)
    (if (vtg-rd-walks (vtg-kind e)) (+ 2 (vtg-rd-steps 1 e 0)) 2)))
(defun vtg-rd-size (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-nk e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-cthen-ex vtg-cbody-ex)))))
  (if (equal flg 1)
      (if (< (nfix i) (vtg-nk e)) (+ (vtg-rd-size 0 (vtg-kid e (nfix i)) 0) (vtg-rd-size 1 e (+ 1 (nfix i)))) 0)
    (if (vtg-rd-walks (vtg-kind e)) (+ 1 (vtg-rd-size 1 e 0)) 1)))
(defthm vtg-rd-steps-bound
  (<= (vtg-rd-steps flg e i) (if (equal flg 1) (+ 1 (* 5 (vtg-rd-size flg e i))) (- (* 5 (vtg-rd-size flg e i)) 2)))
  :rule-classes nil
  :hints (("Goal" :induct (vtg-rd-steps flg e i) :in-theory (disable vtg-kid-ex vtg-rd-walks)
                  :expand ((:free (flg) (vtg-rd-steps flg e i)) (:free (flg) (vtg-rd-size flg e i))))))
(defthm vtg-rd-steps-bound0 (<= (vtg-rd-steps 0 e i) (- (* 5 (vtg-rd-size 0 e i)) 2)) :rule-classes :linear
  :hints (("Goal" :use ((:instance vtg-rd-steps-bound (flg 0))))))
(defthm vtg-rd-size-pos (<= 1 (vtg-rd-size 0 e i)) :rule-classes :linear
  :hints (("Goal" :expand ((vtg-rd-size 0 e i)))))
(defun vtg-lind-steps (e i)
  (declare (xargs :measure (nfix (- (vtg-i2 e) (nfix i)))))
  (if (< (nfix i) (vtg-i2 e)) (+ 3 (vtg-rd-steps 0 (vtg-kid e (nfix i)) 0) (vtg-lind-steps e (+ 1 (nfix i)))) 1))
(defun vtg-lind-size (e i)
  (declare (xargs :measure (nfix (- (vtg-i2 e) (nfix i)))))
  (if (< (nfix i) (vtg-i2 e)) (+ (vtg-rd-size 0 (vtg-kid e (nfix i)) 0) (vtg-lind-size e (+ 1 (nfix i)))) 0))
(defthm vtg-lind-steps-bound (<= (vtg-lind-steps e i) (+ 1 (* 6 (vtg-lind-size e i))))
  :rule-classes :linear
  :hints (("Goal" :induct (vtg-lind-steps e i) :in-theory (disable vtg-kid-ex vtg-rd-steps vtg-rd-size)
                  :expand ((vtg-lind-steps e i) (vtg-lind-size e i)))))

; vtg-tlr's work: a node it reaches its reads (kind, count, a kid, i2) and
; the call, 5 steps; a case's entry its count, its then and the call; the
; nodes and entries it reaches vtg-tlr-size. vtg-tlr-steps-bound.
(defun vtg-tlrw-size (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-ncs e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-reads-ex vtg-cthen-ex)))))
  (if (equal flg 1)
      (if (< (nfix i) (vtg-ncs e)) (+ 1 (vtg-tlrw-size 0 (vtg-cthen e (nfix i)) 0) (vtg-tlrw-size 1 e (+ 1 (nfix i)))) 1)
    (let ((k (vtg-kind e)) (nk (vtg-nk e)))
      (cond ((equal k 4) (+ 1 (vtg-tlrw-size 0 (vtg-kid e 1) 0) (if (< 2 nk) (vtg-tlrw-size 0 (vtg-kid e 2) 0) 0)))
            ((equal k 5) (if (zp nk) 1 (+ 1 (vtg-tlrw-size 0 (vtg-kid e (- nk 1)) 0))))
            ((or (equal k 11) (equal k 13)) (+ 1 (vtg-tlrw-size 0 (vtg-kid e (vtg-i2 e)) 0)))
            ((equal k 19) (+ 1 (vtg-tlrw-size 0 (vtg-kid e 1) 0) (vtg-tlrw-size 1 e 0)))
            (t 1)))))
(defun vtg-tlrw-steps (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-ncs e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-reads-ex vtg-cthen-ex)))))
  (if (equal flg 1)
      (if (< (nfix i) (vtg-ncs e))
          (+ 4 (if (vtg-tlrw 0 (vtg-cthen e (nfix i)) 0) (vtg-tlrw-steps 0 (vtg-cthen e (nfix i)) 0)
                 (+ (vtg-tlrw-steps 0 (vtg-cthen e (nfix i)) 0) (vtg-tlrw-steps 1 e (+ 1 (nfix i))))))
        2)
    (let ((k (vtg-kind e)) (nk (vtg-nk e)))
      (cond ((equal k 16) 2)
            ((equal k 4) (+ 5 (if (vtg-tlrw 0 (vtg-kid e 1) 0) (vtg-tlrw-steps 0 (vtg-kid e 1) 0)
                                (+ (vtg-tlrw-steps 0 (vtg-kid e 1) 0) (if (< 2 nk) (vtg-tlrw-steps 0 (vtg-kid e 2) 0) 0)))))
            ((equal k 5) (if (zp nk) 3 (+ 4 (vtg-tlrw-steps 0 (vtg-kid e (- nk 1)) 0))))
            ((or (equal k 11) (equal k 13)) (+ 4 (vtg-tlrw-steps 0 (vtg-kid e (vtg-i2 e)) 0)))
            ((equal k 19) (+ 5 (if (vtg-tlrw 0 (vtg-kid e 1) 0) (vtg-tlrw-steps 0 (vtg-kid e 1) 0)
                                 (+ (vtg-tlrw-steps 0 (vtg-kid e 1) 0) (vtg-tlrw-steps 1 e 0)))))
            (t 3)))))
(defthm vtg-tlrw-steps-bound (<= (vtg-tlrw-steps flg e i) (* 5 (vtg-tlrw-size flg e i)))
  :rule-classes :linear :hints (("Goal" :induct (vtg-tlrw-steps flg e i) :in-theory (disable vtg-kid-ex vtg-cthen-ex vtg-cbody-ex vtg-tlrw))))
(defun vtg-tlr-size (e) (vtg-tlrw-size 0 e 0))
(defun vtg-tlr-steps (e) (vtg-tlrw-steps 0 e 0))
(defthm vtg-tlr-steps-bound (<= (vtg-tlr-steps e) (* 5 (vtg-tlr-size e))) :rule-classes :linear)
(in-theory (disable vtg-tlr-size vtg-tlr-steps))

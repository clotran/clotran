# The tree evaluator, proved and generated: the plan

`src/f/exec.inc` (2.6k) runs the analyzer's tree (anbuild's nodes, anpass's
clearing marks) on a stack of records: `run_loop` takes the top record --
node, pc, i, restart flag and node, the frame of slots a fn body's records
share -- and does one thing (`k_push` a child, `k_tail` into one,
`k_finish`, write a slot). The VM model's meanings (`vm-loop`'s `m`,
`vmx`'s `mx`) are the same core language big-step; `vmx-proof` proves the
VM runs `mx`.

## The statement

For a well-formed tree (anpass's tail check passed: a recur only in its
loop's tail, as many arguments as slots) and any records below,
**running the machine for the node's count of turns from a record of it
pops that record with the node's value, or, for a recur, leaves its loop's
record back at the body with the loop's slots rebound** (exec-proof,
`ex-machine-correct`); the value is what the meaning `ex-ev` says, and the
meaning is `mx2` (vmx2's, multi-arity and variadic fns) of the tree's
translation, slots mapped to `mx2`'s positions (exec-vm, `ex-vm-agree`),
and the VM run of the translation answers the tree's value (`ex-vm-runs`,
with vmx2-proof's `vcs2-correct`).
So the slot a local reads holds its binding's value, and the tree
evaluator and the VM agree. Marked reads clear their slots in
both (milestone 4's first part: ex-vwf blanks a cleared slot for what
runs after); that anpass's marks meet ex-vwf (tr-sound, no cleared slot
read again) is milestone 4's second part.

What is generated: the decisions of each turn, as integers (`ex-act`,
`ex-kid`, `ex-pc`, `ex-i`, `ex-fin`), as anprim's are; `exec_core` in
exec.inc does what they decide, action for action as the model's `ex-step`
does. Hand-written and named: the actions themselves (a push, a tail, a
slot's read and write), and every kind not yet in the model.

## Milestones (each lands with its gates green)

1. **The core**: constants, locals (and their clearing), if, do, let*,
   loop*, recur, k_finish's restart. exec, exec-proof, exec-vm,
   exec-cost; exec_gen.inc behind `exec_core`; recur's arguments run on
   the record stack (no nested `exec`). The row splits: core Generated,
   the rest Owed. *(done; exec-vm then covered the loop-free core)*
1b. **The VM for loop* and recur**: exec-vm's translation over loops --
   vmx's `:loop` binds its inits at once where the tree binds them one
   after another, so a loop becomes lets of its inits around an `mx`
   loop of their copies, and the scope relation holds only of the
   positions a name still reaches (the lets' positions are blanked).
   *(done: `ex-vm-agree` over loops and recurs, a recur's values
   only ever its loop's slots, never a value outside a loop's tail
   (`ex-recur-stays`); the translation is `xwf` (`ex-tr-xwf`), so with
   `vcsx-correct` the VM run answers the tree's value (`ex-vm-runs`))*
2. **Calls and fns**: N_FN's closure, N_CALL's record (argument mode,
   `bind_closure`'s slots, the fn body's KF_FNBODY|KF_RESTART record, a
   recur to the fn), N_VAR. Needs `vmx`'s `:callv`/`:mkclo` and the
   captures (anlocal's) in the meaning. Split in two:
2a. **The machine and the generation** *(done)*: exec.lisp's turn
   for N_VAR (the Var's value, the namespace the host's), N_FN (a closure,
   vmx's `(:clo template capvals)`, of the outer slots' values) and N_CALL
   (pc 0 its head pushed or direct-linked, 1 the callee kept, 2/3 each
   argument kept, 4 the entry -- a closure of the count's fixed arity: its
   arity's body pushed restarting in a frame of its own, arguments from the
   arity's start, captures in their inner slots, the closure in its self
   slot, the caller's frame kept in the record -- 5 the finish in the
   caller's frame); the meaning's `:call` place, a fn body the `:iter` a
   loop's body is (a recur to the fn restarts it), its entry taking fuel,
   asking the body `ex-wf` (now exec.lisp's) and no capture the marker.
   `ex-machine-correct` over them; exec-cost's `ex-call-turns` (2k + 4
   turns beyond the parts), Vars and fns leaves of the 3n - 2 bound.
   Generated: exec_core's actions 11 to 17 behind named shims
   (`call_head`, `call_dispatch`, `call_keep`, `call_enter`); the rest of a
   call is the host's (the argument modes, a builtin, a variadic arity,
   apply, the call stack).
2b. **The VM over calls and fns**: `ex-vm-agree`, `ex-tr-xwf`,
   `ex-vm-runs` for them. The design worked out: mx's defs keyed by the
   template itself (a closure's name), a def the arity and the body's
   translation -- lets of `(:capt j)` for the captures and of
   `(:mkclo template (:capt 0) ..)` for the self slot, so the body's scope
   is the parameters, the inner slots and the self slot by position, around
   the `:loop` of the parameters' copies the 1b loop translation gives (a
   recur to the fn is that loop's); a fn node `(:mkclo template locals of
   its outer slots)`; a Var `(:const value)`; a call `(:callv head args)`
   (mx runs the arguments first, the tree the head: the core is pure, so
   only the scope's agreement after each matters). What it needs that 1b
   did not: a value invariant -- every closure-shaped value's template in
   defs, its def the translation and its body ex-vwf (`ex-vwf` taking the
   defs: a fn node's template there, a constant's and a Var's value good),
   threaded through env, results and recur values -- one-arity, non-variadic
   templates with distinct parameter, inner and self slots, and
   vcsx-correct with those defs (xdefs-ok, alistp; check the compiler takes
   a non-symbol name).
   *(done, as designed: vcsx-correct asks only `alistp` and `xdefs-ok` of
   the defs, and both mx (`assoc-eq`, `assoc-equal` in the logic) and the
   VM's fntab (`assoc-equal`) look a name up by `equal`, so a template is
   its own def's name -- exec-vmrun runs one through the VM. `ex-xvs` the
   value invariant, `ex-defs-ok` the defs (every entry `ex-def` of its
   template, the template `ex-tmwf`), `ex-vwf` taking the defs; the flag
   induction gains the `:call` place, its end entering the callee's
   `:iter` with mx's caps the closure's (`ex-call-mx` and its siblings
   give the body's hypotheses). ex-vm-agree, ex-recur-stays, ex-tr-xwf and
   ex-vm-runs now cover Vars (a constant of the Var's value: the namespace
   is the host's, its value read from the node as the machine does), fns
   and calls. Left out: a template of several arities or a variadic one
   -- the machine leaves those to the host's apply, and the meaning
   answers :out for them, so ex-tmwf asks one fixed arity.)*
2c. **Arities and the call's dispatch** -- split in four:
2c-i. **Multi-arity, variadic, the arity error** *(done)*: exec-vm
   retargeted from vmx to vmx2 (`mx2`, `x2wf`, `x2defs-ok`,
   `vcs2-correct`): a template's def a clause per arity, `(nf body)` or
   `(nf body :rest)`, the parameters' loop over np = nf (+1 for the rest)
   copies; `ex-pick-arity`: the arity the tree's count picks is the
   clause `pick-arity` picks. The machine's entry picks by `ex-arity` (the
   generated `ex-arfit`: the fixed arity of the count, else the variadic
   one), a variadic one's rest bound as a list, nil for no extras
   (`ex-bargs`); a closure no arity fits THROWS (`ex-entry`'s 2): ex-ev's
   result gains `(:thrown . v)`, threaded through every place a part's
   value is taken (a part's throw its node's), the machine stopping with
   a throw record on top (`ex-throwr`; k_unwind's walk is milestone 3's).
   The value invariant asks no value be the symbol :clo, so a rest list
   is never closure-shaped; the recur marker became a dotted pair, so no
   rest list is it. ex-vm-agree, ex-recur-stays, ex-tr-xwf, ex-vm-runs
   over any arities; ex-machine-correct with the throw. Not claimed: the
   VM's agreement on a throw (mx2 runs a call's arguments before its head,
   so a throw in each could answer differently; milestone 3, with try,
   takes it: translate the head first). Generated: ex_arfit and ex_entry,
   behind exec.inc's `arity_in_pass`/`pick_arity` (the walk over the
   arities, used by bind_closure, fixed_arity and call_enter) and
   call_enter's entry. Wrapper elision (wrapper_of) and the direct link's
   epoch re-read stay the host's: the elided wrapper's body is its
   builtin's call on its parameters, so what the call answers is the
   builtin's -- the runtime's, vmx2's unconstrained `:prim` -- and the
   link is the namespace's (a Var's value read once more after an
   install), which the model reads from the node.
2c-ii. **apply** *(done; its VM agreement 2c-iii)*: the value
   `:apply` is clojure.core/apply (core.clj's fn, its list*, the applyTo
   it ends in: B_APPLY). A call of it with (f a1 .. an coll) is, at the
   call's entry, the call of f on a1 .. an and coll's elements
   (`ex-callee`, `ex-spread`), dispatched as any call (ex-entry); the
   generated `ex-apentry` decides the way first -- spread; apply's own
   arity error, fewer than two arguments; a last argument that is no seq,
   `:not-seq` thrown (clj's RT.seq IllegalArgumentException); or a fn the
   host applies (a builtin, a Var's fn, a non-fn and its ClassCastException).
   A seq is the model's list, nil the empty one (no closure is one); a
   vector's, a lazy seq's walk is the host's (to_seq, sq_first, sq_rest).
   Proved: `ex-machine-correct` with it (the machine's entry turn on apply
   is the spread call's, `ex-apply-turn`; the meaning's, `ex-apply-is-call`);
   B_APPLY's walk (`ex-apwalk`, over the generated `ex-apstep`: elements
   taken off the seq's front only while fewer than the variadic arity's
   req) hands a variadic closure its rest as it is exactly when the spread
   count picks the variadic arity, its locals the walk's fixed arguments
   and rest (`ex-apwalk-call`, for arities as clj's compiler allows them:
   no fixed one of more parameters than the variadic's), else spreads
   everything; counted: the walk at most min(len s, req - k) + 1 steps,
   the spread n + 2 (exec-cost). Generated: ex_apentry and ex_apstep, behind
   B_APPLY (its walk) and exec.inc's `variadic_req` (the variadic pass of
   the arity walk). Host, named: exec.inc reaches the spread call through
   core's apply's `.` (N_DOT, dot_dispatch, B_APPLY), the callee's body in
   a nested run (invoke_closure), not a turn of the loop -- the dot's turn
   is milestone 5's; a yield in apply (the scheduler's); a compiled
   variadic fn's rest (call_compiled). Found: a call of a non-fn answered
   RuntimeException "not a function: 1" where clj's cast raises
   ClassCastException (nil: NullPointerException) -- fixed in
   not_a_function, for apply and every call; `(apply 1 2)` still refuses
   the seq first (DEVIATIONS 84: `.` reads no target hint).
2c-iii. **The VM over apply** *(done)*: vmx2 gains `(:applyv f e1 .. en)`,
   a call whose head may be apply -- only the head's value tells, so every
   tree call translates to it. When f's value is `:apply`, its first
   argument a closure and its last a seq (the model's list, no closure),
   mx2 calls that closure on the arguments between and the seq's elements
   (`x2-spreads`, `x2-fn`, `x2-vals`); otherwise it is `:callv`'s call (a
   call of apply that does not spread -- of a builtin, of no fn, of no seq,
   too few arguments -- the runtime's `:prim :invoke`, as any non-closure's).
   The machine's `(:applyv m)`: the spread arguments written where the
   first argument was, the fn above them (`x2-stk`), then `:callv`'s
   dispatch at the count that makes (`vcs2-callv`, shared by both). Proved:
   vcs2-correct over it (vmx2-proof's call lemmas now over the spread
   callee, arguments and stack: callv2-eff, callv2-step), s2clk-linear and
   vm-time-bound (vmx2-cost, vmx2-time) unchanged in statement. exec-vm:
   the value invariant drops "no value is `:apply`" and asks a list's
   elements good (so a good seq spreads to good arguments,
   ex-callee-good); a call is mx2's `:applyv`, its spread the tree's
   ex-callee whenever the tree enters a closure (ex-mxcall-callee);
   ex-vm-agree, ex-recur-stays, ex-tr-xwf and ex-vm-runs with apply in
   them (exec-vmrun's example: (apply g 5 '(6 7)) and (apply g nil) --
   the rest (6 7) and the arity error -- the tree, mx2 and the VM alike).
   Not yet: the arrays (vmi, and so the Fortran VM) have no `:applyv`;
   vmic compiles it as a call and refuses it (ce-err), so vmic-correct and
   the generated compiler hold as before.
2c-iv. **Seqs past the list** *(done)*: model/seqk.lisp's seq kinds -- a
   list (nil the empty one), a vector `(:vec . elems)` read by index (its
   seq a view, B_APPLY's OBJ_SEQ), a lazy seq `(:lazy . c)` whose
   realisation `sk-real` is constrained by nothing (as vmx2's `:prim`: the
   theorems hold whatever it returns -- its answer read at its top, a lazy
   seq again none, LazySeq.seq's collapse the host's), and a cell `(:cons x
   . more)` (a realised lazy seq, its rest any seq). A step over a seq is
   the generated `sk-step` (0 the end, 1 a list's cell, 2 a vector's
   element i, 3 realise, 4 no seq, 5 a cell); `sk-els` its elements, at
   most `*sk-lim*` (B_APPLY's 1000000: more is the host's error, so a seq
   longer -- an infinite one -- is way 0 in ex-apway, the call the host's,
   only the variadic walk taking it). The tree's ex-spread and vmx2's
   x2-vals both spread `sk-elems` -- the translation does nothing to a
   vector or a lazy seq: `:applyv`'s spread reads them as the tree does.
   The walk ex-apwalk is over a cursor and reads position k only while
   the generated `ex-aplook` says k <= req + 1: clj's RestFn.applyTo
   realises through position req + 1 (boundedLength's last next()), so
   when it hands over at position req it realises the position past it
   too (the peek). Proved: ex-apwalk-call over every kind (for a seq of
   finitely many elements: the walk hands over exactly when the spread
   count picks the variadic arity, its fixed arguments and its rest's
   elements the arity's locals, else spreads every argument --
   ex-apwalk-els reduces it to the list walk ex-aplwalk); ex-apwalk-
   realise-bound (at most req + 2 - k realisations, one a position read);
   ex-apwalk-vector and ex-apwalk-list (a vector's walk, and a list's,
   realise nothing); ex-apply-is-call and ex-apply-turn unchanged in
   statement over the new ex-callee; ex-vm-agree, ex-recur-stays and
   ex-vm-runs with the new kinds, under ex-lzok (every realisation's
   answer good values -- the runtime hands the machine only closures it
   knows; ex-sk-els-good), exec-vmrun's (apply g 5 [6 7]) the rest (6 7)
   in the tree, mx2 and the VM alike; cost (exec-cost): the walk at most
   2t + 3 turns for t elements taken, t at most req - k
   (ex-apwalk-turns-taken, ex-apwalk-taken-req), the spread's read at most
   2n + 3 for n elements (sk-elems-turns). Generated: exec_gen.inc gains
   `ex_aplook` and `sk_step`; B_APPLY's walk and its spread (ap_spread,
   in place of coll_to_vector) read each position through exec.inc's
   shims ap_kind, ap_realise, ap_first, ap_next and ap_look. Host, named in
   docs/model-coverage.md: the thunk's computation (gce_force, the lazy
   seq row's); a chunked seq, a map's or set's cursor, a string's seq and a
   deftype's seq (ap_kind's kind 6, read by to_seq, sq_first and sq_rest,
   which every other caller still uses); the first `to_seq` of what is no
   lazy seq (a vector's view made, RT.seq's refusal). Bug found and fixed:
   B_APPLY realised a lazy seq one position short of clj ((apply (fn [a b
   & r]) s) realised 3 cells, clj 4).
2c-vi. **Apply's spread walks, in vmx2 and the tree** (split in two).
   The bug: vmx2's `:applyv` reads apply's WHOLE seq (x2-vals over
   sk-elems, up to *sk-lim* elements) before the dispatch, where clj's
   RestFn.applyTo reads a variadic callee's seq only through position
   req + 1 -- `(apply (fn [& xs] (first xs)) (range))` is 0 in clj; a
   counting seq through `(apply (fn [a & r] a) s)` realises 3 cells. Found
   too: the TREE has the same bug -- ex-ev and ex-turn spread through
   ex-callee/ex-spread (the whole seq); only B_APPLY and its generated
   decisions walk (ex-apwalk, proved to agree with the whole spread for a
   finite seq). So the fix is both models at once: ex-vm-agree compares
   them, and a rest bound to an unread seq is not a list of every element.
   The Fortran VM is unaffected (rt_applyp false: apply is B_APPLY's).
   - 2c-vi-a *(done)*: ONE WALK. ex-apstep, ex-aplook and ex-apwalk moved
     into model/seqk.lisp (exec.lisp, B_APPLY's generated decisions and
     vmx2 all read them there; exec_gen.inc unchanged). seqk's sk-spread
     is apply's spread as the walk takes it: `(:hand args)` -- a variadic
     fn handed the seq, its req fixed arguments and then the rest as ONE
     seq value (sk-consv of the arguments past req onto sk-cval, the seq
     at the walk's cursor, read at its top; nothing realised), `(:ok
     args)` every element read (the count's dispatch), `:none`, `:long`.
     Proved: sk-spread-long (a seq over *sk-lim* -- an infinite one --
     handed to a variadic fn with req <= *sk-lim* is spread, `:hand`, not
     the host's) and sk-spread-hand-realises (what it realises is
     ex-apwalk's, at most req + 2 - k: ex-apwalk-realise-bound, moved to
     seqk with it). Ported from wip/applyv-arrays: seqk's step reads
     guard-verified for any value (mbe), ex-apway's redundant :apply guard
     removed, scripts/fuzz-vmx2 drawing apply over every seq kind (fz-real
     attached; not on the arrays, which have no :applyv yet).
   - 2c-vi-b *(done)*: vmx2 and the tree over sk-spread. vmx2 -- x2-vals
     and friends take the function table (mx2's defs, the machine's
     `(cdr prog)`; x2-req, the variadic clause's count, is one in both),
     a `:hand` call dispatches through x2-cls/x2-prog: the clause list
     replaced by the variadic clause as the FIXED clause of req + 1
     parameters (x2-hcls -- same body, locals and frame, the rest in the
     last slot), so vcs2-callv and its proofs keep their shape; vmx2's
     checks are clj's examples (range attached as sk-real). The tree --
     ex-callee hands a variadic f over as ex-hclo (f's template with its
     variadic arity as that fixed one, f itself carried for the self
     slot, ex-self); exec-vm's ex-ehyp is over (ex-self f) and the arity
     ex-car picks. vmx2-proof, vmx2-cost, vmx2-time, exec-vm, exec-cost,
     exec-vmrun and the vmi chain certify, statements unchanged but for
     the spread. Note for the checks: a fn whose fixed arity exceeds its
     variadic count (vmx2's f2; clj refuses to compile it) is handed to
     the variadic clause by apply, as RestFn.applyTo does.
2c-v *(done)*. **`:applyv` in the arrays**: vmi and vmg (so the Fortran
   VM) get apply's spread -- `(:applyv m)` in vmic/vmicg instead of their
   refusal, the generated machine spreading through seqk's kinds, over
   vmx2's lazy sk-spread (a variadic fn handed the seq gets its req
   arguments and the rest as one value, its variadic clause entered as
   the fixed one of req + 1). vmi-proof: vmi-applyv-refines and -keeps (the
   scratch's walks are tawalk/twalk, tawalk is ex-apwalk, the spread is
   tspread = sk-spread), so vmi-correct and vmic-correct hold with it;
   vmg-applyv-bnd. Live in the runtime only when rt_applyp is: the VM
   step loop row of docs/model-coverage.md says what that needs. Next:
   milestone 3.
3. **Throw and try, case, collections**: N_THROW, N_TRY's pcs 0..5 and
   `k_unwind`'s catch walk (vmi's handler stack is the model), N_CASE's
   branch (`case_branch`), N_VECTOR/MAP/SET; their nested `exec`s made
   record steps as recur's were. Has (2c-i): ex-ev's `:thrown`, threaded
   through every place, the machine stopping at a throw record. Needs:
   k_unwind's walk from that record; the VM agreement on a throw (the
   call's head translated first, as the tree runs it -- vmx2's `:try` is
   the counterpart, vcs2-correct already covers throws); case's table
   read as data; and
   ex-xvs over collections, a closure inside a vector still a call's
   possible head.
3a. **Throw and try in the machine** *(done)*: N_THROW (kind 17: its
   value pushed, then thrown -- no nested `exec`) and N_TRY (18: children
   the body and, when there is one, the finally, nk 1 or 2; slot 2 its
   catches (class slot body)) are core kinds of ex-act (actions 18 throw
   the value, 19 finish, 20 keep it and push the finally, 21 finish with
   the kept value, 22 throw the kept throw again). A throw record now sits
   over the record it left, nothing in flight, and each turn k_unwind takes
   the record under it (ex-unwind over the generated `ex-unw`): a try at
   pc 1 runs the first catch (ex-catchw) whose class the runtime's
   instance? -- vmx2's `prim :isa`, whatever it answers -- takes, its slot
   bound, the try at pc 3; a try at pc 1 or 3 with a finally runs it (pc 4,
   the throw kept, then thrown again from pc 5); a call's record at pc 5
   gives the caller's frame back; any other record is popped; the last
   record stops the machine. ex-ev: a part's throw costs the pop turn too
   (ex-nv), `:fin` the try's end through its finally. Proved:
   ex-machine-correct with the throw clause exact -- a throw leaves
   `(cons (ex-throwr v) ks)`, nil in flight, the meaning's frame, v never the
   recur marker -- over throw and try (ex-good-m-throw, ex-good-try);
   counted (exec-cost): ex-throw-turns, ex-try-turns (at most 5 beyond the
   parts that run), ex-catchw-steps-bound. Generated: `ex_unw`, behind
   k_unwind (its catch walk over catch_matches); exec_core runs N_THROW and
   N_TRY; fuzz-exec-gen draws kinds 17 and 18 and ex-unw (-x reverses the
   catch's match). exec-vm is unchanged but for `:fin` refused by ex-vwf.
   **3b, first part** *(done)*: the tree's IFn test. A call's pc 1 asks
   ex-ifn -- vmx2's `prim :ifn` of the callee, whatever it answers -- (tv
   1 a fn; else ex-act's action 23 throws :not-fn over the call's record,
   no argument run); ex-ev the same, a linked head's or a run head's value
   (3 turns beyond the head's, ex-not-fn-turns); ex-machine-correct, exec-vm
   and exec-cost stand (exec-vm over values: mx2's :applyv answers a value
   only where the tree does). Fortran: exec_core's tv at a call's pc 1 is
   the host's is_ifn (Eval.f90: what apply invokes, nil and an unbound
   fn's value too, as clj's cast passes them), action 23 refuse_not_fn;
   flat's F_IFN after the head. Oracle: `(f (g))`, f a string; DEVIATIONS
   84 now only apply's `.` target hint.
   **3b, second part** *(done)*: the VM's agreement on a throw, apply's
   refusals with it. exec-vm's translation runs a call head first, as the
   tree does (ex-trcall): `(:let H (:if (:prim :ifn (:local p)) (:applyv
   (:local p) args..) (:throw (:const :not-fn))))`, p the head's new
   position, the arguments in scope cm ++ (nil) (ex-vwf's :call place takes
   that scope). ex-vpost's thrown clause at every place: mx2 answers the
   tree's throw, the scope agreeing at the frame the throw leaves and the
   thrown value good (a call's: an argument's throw, or its dispatch's --
   the body's, the arity error (ex-mxcall-arerr), apply's refusals).
   ex-vm-agree is over a value or a throw; ex-vm-runs too (vcs2-correct
   covers throws), under two hypotheses on the runtime, defun-sk as ex-lzok
   is: ex-ifnok (prim :ifn throws nothing) and ex-apok (a call of apply
   ex-apway refuses, 2 or 3, the runtime's prim :invoke refuses with the
   tree's :arity or :not-seq). No good value is the symbol :recur-marker
   (ex-xvs), so no good list holds the tree's recur marker (ex-xvs-no-mk)
   and apply's refusal 3 is never a spread vmx2 makes (ex-ap3-nospread).
   exec-vmrun's examples run mx2 and the VM under the checks' attachment
   (prim :ifn is constrained in the logic). Model only: the Fortran already
   runs the head first (3b's first part).
   exec-vm.lisp is three books now, each under 800 lines, no statement
   changed: exec-vmtr (the translation, the good values, ex-vwf, the scope,
   ex-tr-xwf), exec-vmcall (fns and calls) and exec-vm (the throw's
   hypotheses and the theorem).
   **3b, third part** *(done)*: throw and try in the VM. ex-tr: a throw
   `(:throw x)`; a try `(:try B H)` (ex-trtry), H the catch walk (ex-trh)
   `(:if (:prim :isa (:const c) (:local p)) Hj ..(:throw (:local p)))`, p the
   thrown value's position, clause j's body in scope cm ++ (slot j) (ex-tr's
   :cs place, the bodies a list as :rec's are); a finally F vmx2's
   desugaring (ex-trfin) `(:let (:try X (:if F (:throw p) (:throw p))) (:if F
   p p))`, F in scope cm ++ (nil) both times (ex-tr's :fin place). ex-vwf
   takes kinds 17 and 18: a catch's slot outside the scope, its body
   well formed in scope cm ++ (slot). Proved: ex-mx-trh (mx2 of the walk is
   ex-catchw's clause, or the throw again) and ex-mx-trtry (mx2 of the try is
   ex-mxtry), so the flag proof's try case is those lemmas', not its
   expansions; ex-vind/ex-vpost's :fin place is the try's end (the finally
   in the frame the body or catch left, its throw the try's); ex-vm-agree,
   ex-recur-stays and exec-vmrun's ex-vm-runs over throw and try, under a
   third hypothesis on the runtime, ex-isaok (prim :isa throws nothing);
   ex-tr-xwf (ex-trtry-xwf). exec-vmrun: (try (throw 7) (catch C x x)
   (finally 3)) caught, uncaught, with and without the finally -- the tree,
   mx2 and the VM alike. Model only (the machine's try is 3a's).
   **3b, fourth part** *(done)*: case*. N_CASE (19) is a core kind of
   ex-act: pc 0 its test pushed (action 3), pc 1 action 24 -- the record
   becomes the branch (k_tail, its restart kept), ex-csbr: the then of the
   table entry the walk takes, else the default (children test and
   default, nk 2; slot 2 the table read as data, each entry (test then)).
   Which entry takes the value is the runtime's, vmx2's prim :case of the
   entry's test and the value (ex-casew walks them in order) --
   case_branch's hash probe and Util.equiv, named as host; the macro's tests
   are distinct, so the walk's first is the probe's only one. ex-wf: the
   thens and default in the case's tail (a recur in a branch is its
   loop's). ex-ev as an if's: the test's turns, the branch's and 2.
   Proved: ex-machine-correct over it (ex-good-case, from ex-good-case-out
   and -br), ex-case-turns and ex-casew-steps-bound (exec-cost; ex-own's
   counts now 19 for ex-act, 15 for ex-pc); the translation `(:let X W)`,
   W the walk `(:if (:prim :case (:const t) (:local p)) Tj ..D)` at the
   test's position p, the thens and default in scope cm ++ (nil) and in
   the case's tail (ex-trcs, x2wf by ex-trcs-xwf); ex-mx-trcase (mx2 of the
   walk is the branch ex-csbr names); the case's two cases lemmas of their
   own (ex-vgood-case, from -val and -out) the flag proof meets closed;
   ex-vm-agree, ex-recur-stays and ex-vm-runs over it under a fourth
   runtime hypothesis, ex-caseok (prim :case throws nothing). exec-vmrun:
   (case x 1 10 2 20 30) taken and defaulted, the tree, mx2 and the VM
   alike. Fortran: N_CASE moved into exec_core (action 24 calls
   case_branch and k_tails into its answer); exec_gen.inc regenerated;
   fuzz-exec-gen draws kind 19 more often. Oracle: a case* in a loop's
   tail recurring from two of its branches.
   **3b, fifth part** *(done)*: the collections. N_VECTOR 7, N_MAP 8, N_SET
   9 are core kinds of ex-act: pc 0 action 25 opens the record (no values
   yet, pc 2), pc 2 pushes element i (action 3, pc 3) or, past the last,
   action 27 builds the collection and finishes with it, pc 3 action 26
   keeps the element's value (pc 2, i + 1) -- exec.inc's slot 4. A vector
   is seqk's (:vec . elems), as B_APPLY reads one; a map's and a set's
   build the runtime's, vmx2's prim :map / :set of the values, a value or a
   throw (ex-cbuild). ex-ev's place :coll (as :rec's: each element, then the
   build -- 1 turn, 2 for its throw, (:out) should the runtime's answer be
   the recur marker). Proved: ex-machine-correct over them (ex-good-m-coll,
   -coll-mid, -coll-end); exec-cost ex-coll-turns (2n + 2 beyond the
   elements'; ex-own's counts 21 for ex-act, 16 ex-pc, 12 ex-i); the
   translation (:prim op elements..), op :vector, :map or :set (ex-cop),
   x2wf as any :prim; the collection's cases lemmas of their own
   (ex-vgood-m-coll, -coll-mid, -coll-end), met by the flag proof closed;
   ex-vm-agree, ex-recur-stays and ex-vm-runs over them under a fifth
   runtime hypothesis, ex-collok: the runtime's vector of the values is
   seqk's (:vec . vals), its map or set of good values good (or a good
   throw). ex-xvs needs nothing new for a vector -- it reads a list's
   elements, so a closure inside a vector of good values is good, a call's
   possible head (ex-xvs-vec). exec-vmrun: (apply g 5 [6 7]) with the
   vector a literal, and #{1 2} -- the tree, mx2 and the VM alike.
   Fortran: N_VECTOR/MAP/SET moved into exec_core (actions 25 to 27, the
   builds vec_to_set/vec_to_map the host's); exec_gen.inc regenerated;
   fuzz-exec-gen draws kinds 7, 8, 9. Found: a set or map literal whose
   keys are equal at run time, `(let [a 1 b 1] #{a b})`, answers #{1} in
   clotran where clj throws IllegalArgumentException "Duplicate key: 1"
   (vec_to_set, vec_to_map) -- not fixed here, the model allows the
   runtime's throw. [Fixed since: both throw it, naming the later key
   (exec.inc dup_key); oracle cases added.] **Milestone 3b done.** Left from it: the old cases of
   the flag proof (ex-vm-agree-flag, ~950 s: if, do, let, loop, recur,
   calls) still go through its expansions after stable-under-
   simplificationp; reworking them into lemmas of their own, as try's,
   case's and the collections' are, would cut that time. [Done since:
   23 lemmas of their own (exec-vm's ex-old: the atom, :iter, :do,
   :let, :rec, :call, :fin, and kinds 4, 5, 6, 11/12, 16, 17 and the
   leaves at :m), each proved as the flag proof proved it, disabled until
   the flag proof, which now meets every case closed and never opens
   ex-vgood: 2.8 s, was ~950. The book as a whole is about the same,
   ~1050 s, most of it ex-vgood-let-mid (~435 s) and ex-vgood-m-if
   (~300 s); a case milestone 4 changes re-proves only its own lemma.]
   **Milestone 4, first part** *(done)*: the VM agreement over marked
   reads. ex-vwf no longer asks a local unmarked. ex-clr is the slots a
   node's marked reads may clear (every run's: both branches, every catch,
   none of a fn body's, which clears its own frame). The scope a place
   sees is cm blanked of what the parts before it may have cleared, in
   ex-tr and ex-vwf alike (a do's, let's, recur's, call's and
   collection's later parts, an if's branches, a case's branches, a try's
   catches and finally), so a read of a cleared slot is not well formed;
   ex-vpost's agreement after a node is cm blanked of its ex-clr (ex-agree
   is unchanged: a nil entry is a position no name reaches, as a loop's
   lets' are). A loop's body clears nothing of the scope outside it
   (ex-vwf's ex-nomem); a fn's body clears nothing of its captures or self
   slot, or has no recur to the fn (ex-arwf, as anpass leaves a body that
   recurs to its fn unmarked), so the :iter place's hypothesis is one or
   the other and ex-vind adds the body with no loop target. The marked
   read is a lemma of its own (ex-vgood-m-mark: ex-agree-clear, the slot
   written nil, blanked); the if's case is four (ex-vgood-if-out, -then,
   -else, -nil; the one lemma took 2100 s with the blanked scopes).
   ex-vm-agree, ex-recur-stays, ex-tr-xwf and exec-vmrun's ex-vm-runs
   stand, statements unchanged. Not admitted: a loop whose later init
   clears an earlier init's slot (the copy the loop translation makes
   would read it; anpass marks that only when the body never reads it).
   **Milestone 4, second part** *(in part)*: exec-clr.lisp states ex-vwf's
   clearing conditions on exec.lisp's tree as ex-cwf -- B the slots the
   parts before a place may have cleared, threaded as ex-vwf blanks its
   scope, no local nor fn's outer slot read of B, a loop body clearing
   nothing at all -- and proves them of marks that are anpass's liveness
   decision: ex-mkok, each marked read's slot not live after it, ex-lv the
   live set before a place as anpass's sp-out computes it (a branch's sets
   or-ed, a catch's from the finally's, a loop body's with every slot it
   reads live after it). ex-lv-mono, ex-lv-rds (a slot read is live before),
   ex-mkok-clr (a slot cleared is dead after), so ex-cwf-mkok: no later part
   reads what an earlier one cleared; ex-loop-noclr: a loop body clears
   nothing. The direct liveness argument, not ok-ann over tr's runs: no
   oracle to build. exec-clrmap.lisp is the map: ex-ast reads exec.lisp's
   node as anpass reads its own (kind, i2, children, a fn's outer slots its
   caps, a try's catch bodies or a case's thens its alternatives, a recur's
   rfn the node's slot 8, which exec.inc does not read), ex-shp the shapes
   both take, and ex-rds-ast: exec-clr's reads are anpass's rds of it.
   (anpass-proof's reg is anp-reg now: it clashed with vm-call's.)
   **Milestone 4, the rest** *(done)*: exec-clrlv.lisp, ex-lv-ast: ex-lv
   is sp-out of ex-ast's node on a tree of ex-shp's shapes (ex-lvp the
   piece: :m sp-out 0 of the node, :do :rec :call :coll sp-out 1 from i, a
   loop's :let sp-out 1 from i to n2 onto the body's sp-out from its sp-rd,
   :cs :ct sp-out 2 from i with A, :fin kid 1's), sp-out disabled, its node
   case opened once per kind (ex-spo-*), the sequences only by
   sp-out-seq-front, -seq-done, -2-open and -2-done, ex-lv and ex-shp opened
   by :expand on the induction's own node; the induction ex-lvind walks a
   call as its children from 0, as ex-shp does (under 1 s; the one
   induction with sp-out and ex-lv open ran past 600 s). ex-mk-local: sp-mk
   marks a local exactly when ex-mkok lets it be marked, so ex-mkok is
   anp-clears-spec's marks. exec-clrfn.lisp: ex-vwf-nolp, a body well formed
   with the fn's lp, its tail check at tt 1 passed and anp-hfr nil, is well
   formed with lp nil (ex-ntm-* the node's anp-tc and anp-hfr per kind; a
   recur at tt 1 is refused with rfn 0 and seen by has_fn_recur with rfn
   nonzero; ex-vwf-lpfree: a call's, collection's or try's parts and a
   loop's inits and body take no outer lp); ex-arwf-body, ex-arwf's last
   condition from the tail check and the marks being apply_clears' (none
   when anp-hfr holds). exec-clrvm.lisp: ex-vwf0, ex-vwf with no scope
   blanked and no clearing conditions but the one case not admitted asked
   (a loop's init clears no slot of the loop); ex-bl, a scope with some of
   B blanked; ex-vwf-cwf, ex-vwf0 and ex-cwf give ex-vwf; ex-anp-runs, end
   to end: a tree ex-vwf0 calls well formed whose marks are anpass's
   liveness decision (ex-mkok) runs on the VM as on the tree (ex-vm-runs'
   conclusion; the templates in defs taken well formed as ex-vm-runs takes
   them, ex-defs-ok). exec-clrmap's three copies of ex-ast-open made one.
   Left, named: the templates' bodies brought through ex-vwf0 the same way
   (an induction over ex-defs-ok, each body's ex-arwf from ex-vwf0,
   ex-mkok from (zeros n) and ex-arwf-body), and the loop-init case, which
   anpass marks when the body never reads the slot -- a hypothesis here,
   not a theorem.
   **Milestone 4 done.**
   **Next (milestone 5)**: the kinds exec.inc still runs through a nested
   `exec` (its `exec_aux`): N_DEF (exec_def: the init's value, then the
   Var's root bound -- a host action, the namespace's), N_LETFN
   (exec_letfn: the fns' closures into slots start .. start+n-1, then
   refresh_captures over them, then the body -- as a let's inits but for
   the captures' second pass, which wants the closure's capture slots
   rewritten in place: a new action), N_DEFTYPE (exec_deftype: the
   methods' closures, the type registered -- host), N_NEW/N_NEWTYPE (the
   arguments as a collection's, then new_cached -- a prim, as :vector's),
   N_SETBANG (exec_setbang: a Var's thread binding or a field set -- host),
   and N_DOT (run_loop's: target then arguments into slots 3 and 4, then
   dot_dispatch, re-executable, a yield inside it resumed by dispatching
   again -- the call's shape with the host's dispatch for the callee; the
   target's interface hint and its cast are DEVIATIONS 84's, which wants
   the cast before the arguments, as a call's action 23). Order: new
   (closest to the collections), then letfn (the frame action), then dot
   (with 84's cast, removing the deviation), then def, set!, deftype as
   host actions. Each: the kind into exec.lisp's ex-step and ex-ev, the
   generated ex-act's action, exec_gen.inc regenerated, fuzz-exec-gen
   drawing it, ex-vm-agree's case a lemma of its own (as exec-vm's ex-old).
   *(new done)*: N_NEW 22 and N_NEWTYPE 23 are collections of ex-act
   (actions 25, 3, 26, 27: the record opened, each argument pushed and
   kept, then built); the build is the runtime's, vmx2's prim of op
   (:new k C), C the node's class (ex-cop, ex-cbuild now of the node);
   the translation (:prim (:new k C) arguments..); ex-collok asks the
   construction of good values good, or a good throw (ex-collok-new).
   Proved: ex-machine-correct, ex-vm-agree (ex-vgood-m-new, its own case;
   the flag proof unchanged but ex-vind's kind list), the clearing books
   over it as a collection (ex-spo-seq: anpass reads its children in
   turn); exec-cost ex-new-turns (2n + 3 beyond its arguments'). Fortran:
   exec_core's action 27 calls new_cached (note_site first); exec_other
   no longer has it; exec_gen.inc regenerated; fuzz-exec-gen draws 22, 23.
   Oracle: a deftype constructed in a loop's body, and a throwing argument.
   *(def, set!, deftype done)*: N_DEF 10, N_DEFTYPE 20, N_SETBANG 24 are
   collections too: their children (a def's init when it has one, then its
   metadata when evaluated, as DefExpr runs them and anpass's liveness
   reads them; a deftype's methods' fns; a set!'s target when a field's,
   then its value) kept as elements, then the host's action, vmx2's prim
   of op (:host k C) -- ex-cop's op renamed from :new, which a new shares.
   What the action does to the namespace, the type registry or a field is
   the runtime's, ex-collok's named hypothesis (its kinds now 8 9 22 23 10
   20 24), not a theorem. Proved: ex-machine-correct and ex-vm-agree over
   them (ex-vgood-m-host, their own case), the clearing books (exec-clr,
   -clrvm over all three; exec-clrmap's ex-shp and exec-clrlv's ex-spo-seq
   over def and set! -- anpass reads a def's metadata from s3 after its
   kids, nil in ex-ast's node -- but not deftype, whose methods anpass
   reads as alternatives: ex-anp-runs does not yet cover a tree with a
   deftype, ex-ast wants its kids as alts); exec-cost ex-host-turns.
   Fortran: exec_core runs the three (core_kid gives a def's metadata
   node and a deftype's method fns as children; action 27 calls
   def_finish, deftype_finish, setbang_finish -- exec_def, exec_deftype,
   exec_setbang made to take their children's values); exec_other no
   longer has them; exec_gen.inc regenerated; fuzz-exec-gen draws 10, 20,
   24. Oracle: a def's init then metadata, in a loop's body, a throwing
   init binding nothing; set! of a binding and of a mutable field, a
   throwing value writing nothing; reify's methods over a loop's locals.
   **Next: letfn** -- designed, not built (the coordinator's decision: the
   group's captures an indirection, as an environment of recursive
   bindings, never left to the host). The smallest form found:
   - VALUE. A group closure is (:clo tm caps) as any; a capture whose outer
     slot is one of its own group's (start .. start+n-1) holds (:grp G j),
     G the group, a list of (tm_k caps_k) for k < n whose own group
     captures are (:grp nil j) -- nil standing for the G around it, so the
     value is finite. RESOLVED when read: (:grp G j) is (:clo tm_j caps_j)
     with each (:grp nil m) in caps_j made (:grp G m) -- the closure in
     slot start+j, the same value the frame holds. Any other capture reads
     as itself.
   - ex-act: letfn as a let's inits (actions 3, 6 into slots start+i, the
     fns' closures made as N_FN's, action 12) and then one new action
     before the body, 28 "the group sealed": each slot's closure's group
     captures rewritten to (:grp G j), G read from the n slots. ex-bind
     (a call's entry) resolves each capture as it binds it (ex-bind-caps).
   - vmx2: mx2's (:capt j) answers (x2-res (nth j caps)), x2-res the
     resolution above (the identity on any value not (:grp ..)-shaped, which
     ex-xvs then asks of a good value as it asks of :clo); and a form
     (:mkgrp n start (tm_0 e..) .. ) whose value is the n closures sealed,
     bound by the translation as a let's n inits. The machine x2 the same
     at its capture read and a group instruction. This touches the VM's
     base book: vmx2-proof, vmx2-cost, vmx2-time and vmi (which includes
     vmx2) re-proved, the jit books after them; budget it as its own lane.
   - Fortran: exec_core's action 28 is refresh_captures' pass over the
     group's slots, as now -- the in-place cycle is the indirection's
     unfolding: reading capture j of a group closure in place answers the
     object in slot start+j, as x2-res answers the value there. letfn's
     two exec calls (inits, body) become the record's children.
   No observable disagreement found between the two: clj refuses a
   non-fn init (LetFnExpr casts it to ObjExpr), so every slot of the group
   holds a closure, and every refreshed capture of a non-group slot reads
   the value it was made with (the inits make closures and nothing else);
   mutual recursion and (identical? g (f)) agree with clj (oracle).
   *(letfn built)*: vmx2.lisp: x2-res, the resolution above (x2-fill, the
   group's nil made G); mx2's (:capt j) answers (x2-res (nth j caps)), the
   machine's :capt the same (vcs2-step's own case, no longer vcsx-step's);
   (:mkgrp (j . shape) e1 .. eN), mkclo-shaped -- the N values every fn's
   captures in turn (a group capture the constant (:grp nil m)), its value
   x2-seal's j-th closure -- and the machine's (:mkgrp op N) instruction
   (vmi has no opcode for it: the array compiler, vmic and vmicg, refuses
   it -- vce-fail, as a closure of no function id -- so the array VM never
   runs a letfn group; VmRuntime's keyword table has :mkgrp). Re-
   proved: vmx2-proof (mkgrp2-*, s2good-mkgrp, each its own lemma beside
   mkclo's; s2good-capt opening vcs2-step), vmx2-cost, vmx2-time, vmi (its
   capt resolves), vmi-proof, vmg (rt-capt resolves), vmrt (vrt-decp-res:
   no decoded value is (:grp ..), the Fortran's group being its in-place
   cycle) and everything above them. exec.lisp: N_LETFN 13 a let whose
   inits are its fns (actions 3, 6), then action 28, the group sealed
   (ex-seal: each slot's closure's group captures (:grp G j), ex-gcaps,
   ex-grp) and its body become (as 4); ex-bind resolves each capture as it
   binds it and makes the self slot's closure of the resolved captures
   (ex-resl, ex-resclo), as the translation's :capt reads make it.
   Proved: ex-machine-correct over it (ex-good-let-seal, its own case);
   exec-cost ex-letfn-turns (2n + 1 beyond its fns' and its body's).
   Fortran: exec_core runs N_LETFN (action 28 is refresh_captures' pass
   over the group's slots, then k_tail to the body); exec_letfn and its
   nested execs gone; exec_gen.inc regenerated; fuzz-exec-gen draws 13.
   Oracle: an outer local beside the group, three fns in a cycle, a group
   fn escaping its letfn, a closure over a sibling, a variadic member,
   recur in a member, a letfn in a loop's body, nested groups, map and
   apply of a member, a throwing body -- all agree with clj; no observable
   disagreement between the in-place cycle and the indirection.
   *(letfn's VM agreement done)*: ex-tr's kind 13 is n of mx2's lets
   (ex-trlf), the j-th (:mkgrp (j . shape) caps..) -- shape each fn's
   template and count of captures, caps every fn's in turn read in the
   letfn's scope (ex-lfargs: a capture of the group's slot o the constant
   (:grp nil o-s), any other its slot's local) -- then the body in scope
   cm ++ (s .. s+n-1). ex-vwf admits 13: n > 0 inits, each a fn (kind 14)
   of a def's template with natural outer slots, each the group's or in
   scope (ex-lffns, ex-lfok); the group's slots new to the scope; the body
   clearing nothing of the scope outside it (as a loop's body: ex-clr of
   13 stays nil, so the clearing books are unchanged); the body well
   formed in the grown scope. ex-xvs: a closure's captures may hold (:grp
   G m) -- G's entries (tm caps) each a def's template with as many
   captures, each the group's own (:grp nil m') in range or a plain value
   (ex-gcok), every plain value among them good (ex-gvals); a group
   capture resolved is a good closure (ex-xvs-gres), so a good closure's
   resolved captures are good (ex-xvs-clo-resl, exec-vmcall's ex-efacts
   now asks it of ex-resl). exec-vmlf (new): the tree's n inits and seal
   are the sealed closures read from the letfn's starting frame (ex-ev-lf,
   ex-seal-lfr: ex-lfr, ex-lfg, ex-lfsv over ex-gcv), each let's x2-seal
   the same closure (ex-trlf-mx), the grown scope agreeing with the sealed
   frame and the closures good (ex-lf-facts); exec-vm's case
   ex-vgood-m-letfn, ex-vind's kind-13 tip the body in that scope, so
   ex-vm-agree, ex-recur-stays and ex-vm-runs cover letfn. Not covered:
   an empty letfn (n = 0), and a letfn whose body clears an outer local
   (ex-vwf refuses both); ex-anp-runs still takes no letfn (ex-vwf0 and
   the clearing books' ex-shp do not admit 13).
   *(deftype and letfn in ex-anp-runs done)*: exec-clrmap's ex-ast reads a
   deftype's children as its alternatives too, as anpass reads its methods
   (ex-ast-reads, ex-ast-alt over 20; rds 3 is rds 1 over it, ex-rds-
   deftype), ex-shp admits 20 as a collection; exec-clrlv's ex-spo-deftype
   (sp-out 3 is sp-out 1 over it). A letfn: exec-clr walks kind 13 as a let
   (ex-rds, ex-lv, ex-mkok, ex-cwf: its fns, then its body); ex-shp admits
   it with fns for inits (ex-lffns); anpass's second read of the fns'
   captures after the body (sp-fncaps) sets what their sp-out set already
   (ex-spo1-letfn, ex-fncaps-letfn: both ex-setl of ex-lfoall, the sets
   commuting and idempotent), so ex-spo-letfn: its sp-out is a let's, and
   ex-lv-ast covers it; exec-clrfn's ex-ntm-letfn (its body in its tail);
   exec-clrvm's ex-vwf0 admits 13 as ex-vwf does, ex-vwf-cwf over it
   (ex-cwf-lf-body, ex-cwf-lf-fns). A letfn body may clear an outer local:
   ex-clr of 13 is its let walk (its fns clear nothing, ex-clr-lf: the
   body's), the places after it see those slots blanked as after a let,
   and ex-vwf no longer asks its body to clear nothing outside it
   (exec-vmlf's ex-lf-parts and ex-lf-facts over it, exec-vm's
   ex-vgood-m-letfn the body's agreement cut to the outer scope). So
   ex-vm-agree and ex-anp-runs cover deftype and letfn; left: an empty
   letfn (n = 0), which ex-vwf refuses.
   *(the empty letfn done)*: ex-vwf and ex-vwf0 admit n = 0 -- it runs as
   its body, the seal a no-op, its translation the body's. exec-vmlf's
   ex-lf-facts-0 (the frame, scope cm ++ nil, and the body's run and
   translation the letfn's) and ex-lfenv, the body's env (env itself for
   n = 0: mx2 reads it as cm ++ nil agrees with it -- ex-agree-app-nil --
   so no lemma over mx2's env is needed); exec-vm's ex-vgood-m-letfn over
   it (ex-agree-lfenv cuts the scope back); exec-clrlv's ex-shp-let-body
   and exec-clrfn's ex-ntm-letfn stated at any n equal to the count, so
   they fire where the count is the literal 0. exec-vmtr split for size:
   the good values (ex-xvs, a group's captures, ex-outers/ex-inners) are
   exec-xvs.lisp.
   *(dot done)*: N_DOT 21 is a collection as the host's actions are: its
   children (its target when evaluated, then its arguments) kept, then
   the host's dispatch, vmx2's prim of op (:host 21 C) -- ex-collok's
   named hypothesis now over 21 too (the member's work, a deftype method
   entered in the loop, a yield re-dispatching: the runtime's). The cast
   is no new action: the analyzer wraps a hinted target in a call,
   (clotran-class-cast target C) (analyze.inc anb_dot_kind keeps the hint
   it finds in the scope for anb_dotnode; Eval.f90 B_CLASSCAST), so it
   runs before the arguments as an ordinary child -- clj's checkcast.
   Only an IFn hint casts (DEVIATIONS 85: is_instance does not know a lazy
   seq is an IObj); DEVIATIONS 84 closed. Proved: ex-machine-correct,
   ex-vm-agree (ex-vgood-m-host), ex-anp-runs (the clearing books read
   its children in turn, ex-shp and ex-spo-seq), exec-cost ex-host-turns,
   all over 21. Fortran: exec_core runs N_DOT (core kinds; action 27 calls
   dot_finish -- the native fast path takes the values vector as it is,
   else dot_dispatch with the target apart -- the vector handed over and
   given back for a yield's re-dispatch, a method's call request entered
   with enter_call); run_loop's own N_DOT case gone; exec_gen.inc
   regenerated; fuzz-exec-gen draws 21. Oracle: apply's cast before its
   seq ((apply 1 2) and its kin), a hint on the local and on the target
   as written with the argument never run, nil passing; a `.` in a loop's
   body, a static member, a throwing argument.
   *(N_LAZY, N_TOP, break_frames done)*: exec.lisp split for size (the
   tree's readers, the catch and case walks and the collections' builds
   are exec-tree.lisp; exec-vm's cases and theorem exec-vmok.lisp).
   N_LAZY 15 is a leaf, action 29: the closure of its template over the
   frame (12's) wrapped by the host, vmx2's prim (:host 15 C) of it, as
   27's build (ex-cbuild of the one closure: a value, or a throw over the
   record); ex-collok over 15 asks the wrap of a good closure good; ex-tr
   (:prim (:host 15 C) (:mkclo ..)); the clearing books read it as a fn
   (anpass's *n-lazy* is *n-fn*'s: ex-astf's captures, ex-rds, ex-lv,
   ex-cwf, ex-shp, ex-spo-fn, ex-vwf0 over (14 15)). N_TOP 26 is an entry:
   action 30 pushes its body (slot 2) with no restart in a frame of i2
   nils, the frame below kept in the record, and at pc 1 action 17 gives
   it back (k_unwind's 5 for a throw, ex-unw); its body in the VM is the
   body's translation in the scope blanked (ex-blank cm cm: no outer name
   reaches it, so no let-block is needed -- the body's lets bind its own
   slots), ex-vwf's case asking no loop target. exec.inc's record holds
   its own frame, so there action 30 is the old N_TOP case, k_tail to the
   body (or the flat form, flat's): the model's pc 1 return is that
   record's pop. Proved: ex-machine-correct (ex-good-m-top; the leaf case
   takes 15), ex-vm-agree (ex-vgood-m-lazy, ex-vgood-m-top, ex-vind's
   kind-26 tip), exec-clrvm's ex-top-runs (ex-anp-runs of the body in a
   frame of nils, anpass marking the body in its own frame), exec-cost's
   ex-lazy-turns (at most 2) and ex-top-turns (the body's and 2). The
   debugger: exec-proof's ex-frames, a read of the records (each
   record's node, pc, i and the frame it runs in -- the frame in flight
   down to the first record keeping the frame below, a call's at pc 5 or
   a top's at 1), ex-break-reads (a break changes nothing, a frame per
   record, each that record's node) and ex-frames-pop (a pop restores the
   frame it reported); break_frames among exec.inc's ratchet procs.
   Fortran: exec_core runs N_LAZY and N_TOP (actions 29, 30); run_loop's
   own cases gone; exec_gen.inc regenerated; fuzz-exec-gen draws 15, 26.
   *(the templates' bodies done)*: exec-clrvm's ex-anp-runs-defs is
     ex-anp-runs with ex-defs-ok0 for ex-defs-ok: each arity's body
     (ex-arwf0) ex-vwf0 in the fn's scope, of ex-shp's shapes, the tail
     check passed at the fn's tail, its marks ex-mkok's over a live set of
     its own and among apply_clears' over the fn's frame (ex-anmk: ex-mks,
     the tree's marked reads as anpass's nodes, a subset of anp-clears'
     mks with no error). ex-anmk-hfr derives "a body recurring to its fn
     clears nothing" from anp-clears-spec (its marks none when anp-hfr
     holds; ex-mks-clr: no marked read, nothing cleared); ex-arwf0-arwf
     from ex-vwf-cwf, ex-cwf-mkok and ex-arwf-body; a defun-sk over each
     arity's (L n anps) lifts it to ex-defs-ok0-ok. Left, named: ex-defs-ok0
     itself, the analyzer-side fact -- that every template in defs is
     what anbuild built and anpass marked -- stated on exec.lisp's tree,
     not derived from anbuild's run (no theorem yet takes anbuild's output
     to ex-vwf0 and ex-shp, nor anp-clears' marks in order to ex-mkok:
     ex-mks is a subset by node, which gives the hfr case only); and the
     loop-init case.
   **Was next** (as planned, for the record):
   - ex-anp-runs' (ex-defs-ok defs defs): an induction over ex-defs-ok's
     templates, each arity's body: ex-arwf from the body's ex-vwf0 (the
     same route ex-anp-runs takes for the top tree -- ex-vwf-cwf,
     ex-cwf-mkok over anpass's marks of the body, which anpass runs per
     fn body with the fn's scope) and ex-mkok from (zeros n) with
     exec-clrfn's ex-arwf-body for the fn-recur case. The analyzer side
     must say each template in defs was built by anbuild and passed
     through anpass (an anbuild-props fact over the templates the tree
     holds); the loop-init case stays the named hypothesis.
4. **Clearing joined**: the machine theorem over anpass's marks, from
   tr-sound -- a marked read's slot is never read again.
   *(done)*: exec-vm (first part), exec-clr, exec-clrmap, exec-clrlv,
   exec-clrfn, exec-clrvm; the templates' bodies (ex-anp-runs-defs, ex-defs-ok0 named) and the loop-init case
   left, named in its paragraph above.
5. **The rest**: def *(done)*, letfn *(done)*, deftype *(done)*, new *(done)*, set! *(done)*, dot *(done)*,
   N_LAZY *(done)*, N_TOP *(done)*, the debugger's frames (`break_frames`) *(done)*. The row is
   Generated but for the actions, named; the templates' bodies done but for ex-defs-ok0 (above).

N_FLAT (flat.inc, To be retired) and N_VMB (the VM itself) are not this
row's.

## Lane 3: vm.inc's translation generated from the model

The row "VM runtime: the translation from clotran's tree, the entry, the
hooks" (docs/model-coverage.md). exec-vmtr's ex-tr is proved
(ex-vm-agree, exec-vmok, exec-vmrun); vm.inc's `vm_tr` was hand-written.

**The map**, vm.inc piece by piece against the model:

| vm.inc | the model | encoding the same? |
|---|---|---|
| `vm_tr` N_CONST, N_LOCAL (a frame slot), N_IF, N_DO, N_THROW, N_LET | ex-tr kinds 1, 2, 4, 5, 17, 11 | yes -- **generated now** (vmtrg) |
| N_LOCAL of a capture | ex-fbtc reads it in place, `(:capt j)` (exec-vmcs's ex-cs) | yes -- vtg_local exact |
| N_LOOP, N_RECUR | lets, then `(:loop (locals..) body)`, `(:recur ..)` -- no dummy (item 3) | partly: the same when an init reads an earlier binding; vm.inc's independent-inits loop `(:loop (inits..) body)` (PLAN 34, no let keeps a walked seq's head) is not ex-tr's yet |
| N_CALL | a call whose head is read at translation (exec-vmtr's ex-pcall / ex-pk): a constant builtin's `(:prim f args..)`, a direct-linked Var's whose fn wraps builtin f `(:prim f args..)` (item 4); else ex-trcall: `:ifn` then `:applyv` | partly: both **generated now** (vtg_pk, vtg_hd, vtg_node 6) under named hypotheses -- exec-vm's ex-bipok (the runtime's prim of a builtin is its :invoke; a builtin is an IFn), ex-wrapok (a fn the runtime says wraps f at n is an IFn, and its call on n values answers prim f's, unless out of fuel); vtg_pk's tests (vm.inc's OBJ_BUILTIN not B_APPLY, and vm_linked_builtin / wrapper_of, where the model asks prim :clotran.vm/builtin, and i2 1 with prim :clotran.vm/wraps); apply's constant :callv. Also generated now (item 4(b)): a Var not direct-linked wrapping f, `(:prim :clotran.vm/callw (:const v) args..)` (vtg_pk 3, vtg_hd pushing callw and the Var's constant), under named ex-callwok (the runtime's callw of v on n values is prim f's) and vtg_pk's test (vm_wraps where the model asks prim :clotran.vm/wraps; vm_var_ref's constant where the model's is v). Also generated now (item 4(c)): an IFn constant's or Var's call, not apply, `(:callv h args..)` (vtg_pk 4, vtg_node 7), no new semantic hypothesis (the head answers v whenever the args do; v an IFn so the cast passes; not apply so no spread), named: vtg_pk's is_ifn (of the Var's value at translation) where the model asks prim :ifn. And generated now (item 4(c), the rest): every other call -- a local's or other expression's head, a non-IFn's, apply's -- is ex-trcall's `(:let h (:if (:prim :ifn p) (:applyv p args..) (:throw (:const :not-fn))))` (vtg_top, vtg_cast, vtg_notfn, vtg_node 8), no new semantic hypothesis (ex-ifnok, ex-apok as before); named: vm.inc's prim :ifn is VmRuntime's kind 9 (vrt-prim-kind's kifn) is_ifn, its not-fn throw `(:prim :clotran.vm/notfn p)` kind 10 refuse_not_fn, apply's spread the runtime's :invoke of B_APPLY (rt_applyp false). vm_tr's hand-written :callv is gone: N_CALL is wholly generated |
| N_VAR | `(:prim :clotran.vm/deref (:const v))` (item 3, done) | yes -- **generated now** (vtg_deref): the host's deref under a named hypothesis, exec-vm's ex-derefok (it answers the Var's value, the tree's v); named: vm.inc's constant is the Var, or the direct-linked node (vm_var_ref), where the model's is v; ex-vwf asks a Var's v not shaped as prim's throw, (:throw . x) |
| N_VECTOR/MAP/SET/NEW/DOT | `(:prim op ..)`, op ex-cop (`:vector`, `:map`, `:set`, `(:host k C)`) | **generated now** (item 7, vtg-tr k 7 8 9 21 22: vtg_cop, flg 3 from 0, vtg_node 6), no new semantic hypothesis (ex-collok); named: vtg_cop's op is the node itself, the runtime's kind 6 (vm_node_hook builds it), where the model's is ex-cop |
| N_FN | `(:mkclo tm caps..)` | **generated now** (item 7(b), vtg-tr k 14: vtg_fnhd, vtg-caps over vtg_ncap / vtg_capo, vtg_node 0), no new semantic hypothesis; named: vtg_fnhd's items are vm.inc's :prim and the node itself (vm_node_hook building the closure) where the model's are :mkclo and tm; vtg_ncap / vtg_capo read slot 2's pair vector where the model's is ex-outers |
| N_LAZY | `(:prim op (:mkclo tm caps..))` | **generated now** (item 7, vtg-tr k 15: vtg_cop, a fn's items, vtg_node 0, vtg_node 6 2), no new semantic hypothesis (ex-collok's (prim (:host 15 C))); vm.inc's encoding changed to nest the same way (approved): `(:prim LAZY (:prim FN caps..))`; named: vtg_cop's op the N_LAZY node, the runtime's kind 6 wrapping its one argument in a pending lazy seq (as eval_new's clotran.host.lazy_seq), vtg_fnhd's op an N_FN node of the same template made at translation (mk_node), where the model's are (:host 15 tm), :mkclo and tm |
| case* | ex-tr's `(:let test W)`, W ex-trcs's walk over prim :case | yes -- **generated now** (item 5, vtg-tr flg 6, vtg_cstest; vtg-tlrw walks its thens), no new semantic hypothesis (ex-caseok); named: vtg_ncs/vtg_cthen read gca_entries' order where the model's is ex-c's list, and vm.inc's test `(:prim NODE (:const then_j) p)` -- the runtime's kind 6, vm_node_hook: case_branch's probe takes entry j -- where the model's is `(:prim :case (:const t) p)` |
| letfn | ex-tr's ex-trlf: n lets of `(:mkgrp (j . shape) caps..)`, then the body | yes -- **generated now** (item 5, vtg-tr flg 7, vtg_lfinit, vtg_lfbinds), no new semantic hypothesis; named: vm.inc's init `(:prim NODE (:const j) caps.. (:local d)..(:local d+j-1))` -- the runtime's kind 6, vm_node_hook N_LETFN: fn j's closure, the group's captures patched among it and the earlier lets' closures (exec_letfn's refresh_captures, one group, its fns identical), a group capture `(:const nil)` -- where the model's is :mkgrp, x2-seal's j-th |
| try | ex-tr's kind 18 (ex-trtry) | **generated now** (item 5(b)): vtg-tr flg 8 and vtg_catest, vtg_rethrow; the implicit rethrows a distinct prim, named |
| def, the host's | ex-tr has them | vm.inc refuses (vm_scan): the fn runs on the tree |
| `vm_clause`, `vm_compile_fn` (the entry) | ex-fbtc, ex-clause, ex-def | partly: captures in place and the self slot a let after the parameters in both; the self let's value is `(:mkclo tm (:capt 0)..)` in the model, `(:capt ncap)` in vm.inc (named); the loop only on a recur to the fn in both (ex-tlr; vm_clause's test vtg_tlr, generated: item 3 (b)). **Generated now** (vmtrcl): the clause vtg_clause (vtg-clause-ex-clause: ex-clause, sl 1), the arity-error clause vtg_arcl (ex-arcl; ex-arcl-mxcl: appended to a callee's clauses it answers ex-mxcl's, its prim's throw for :arity), and the scope vtg_scope (vtg-scope-fbcm: ex-fbcm at sl 1, ex-fbcm0 at sl 0; named: vtg_nin/vtg_inr read capv, vtg_capin is c%capt). Named, still hand-written: vm_clause's arity read (nf, variadic, start, body), its vm_scan and the sl decision; vm_compile_fn's arities' loop (vm_clause of each arity in order, then vtg_arcl: ex-clauses's order then ex-arcl) and the program's reservation, compile, fuse and JIT -- host actions |
| `vm_run`, `vm_call_hook`, `vm_node_hook`, `vm_deref_hook` (the hooks) | vmx2's prim/invoke, exec-vm's ex-collok | host actions under named hypotheses; stay hand-written |

**Generated now**: model/vmtrg.lisp, `vtg-tr` (with loop/recur: item 3), `vtg-lind` and `vtg-tlr` (vm_clause's loop test),
guard-verified, generated to src/f/gen/vm_tr_gen.inc (`make gen-vm`;
check-vm-gen compares it). It builds on the value stack as anbuild does
and keeps the scope through shims (`vtg_bind`, `vtg_save`,
`vtg_restore`, `vtg_blank`, `vtg_local`, the reads, `vtg_other` for
every other kind -- vm_tr, which calls back). vtg-tr-ex-tr: on a tree of
the eight kinds it pushes exactly ex-tr's and leaves the scope as it
found it. vtg-steps-bound: its work at most 16 steps a node it reaches
(vtg-size), each node's shims a constant. `scripts/fuzz-vmtr-gen` (in
check-vm-gen) runs the generated vtg_tr, through shims that are
vmtrg.lisp's exactly (test/vmtrg/vmtr_check.f90), against ACL2's ex-tr
on random trees of these kinds and others; -x reverses a node's items.

**do** (done): ex-tr's do was `(:if e r r)`, r compiled twice a level,
exponential in a do's length. Now each value but the last is a dead
local, `(:let e r)`, r in scope cm ++ (nil) -- vm.inc's encoding -- in
ex-tr, ex-vwf, ex-vind (exec-vm), ex-vgood-do-mid (exec-vmok), and
exec-clrvm's ex-vwf0 and ex-cmpind, the k 19/:call pattern; ex-vm-agree,
ex-vm-runs and ex-anp-runs re-proved in statement unchanged (exec-cost's
ex-turns-bound-flag now inducts on its own walk, ex-ltind, a do's rest in
ex-lfwf's scope). vmtrg's
flg 2 walks a do's children with a new shim, `vtg_dead` (the depth one
more); vm_tr's own N_DO case is gone.

Named, not exact: `vtg_blank` blanks nothing and `vtg_restore`
undoes binds only (equal on ex-vwf trees, which never read a blanked
slot). `vtg_local` is exact: the scope carries `vtb-cs`, the clause's
parameter and capture counts, and a read is exec-vmcs's `ex-cloc` of its
position.

**Next**, each a model change before the code, so ex-vm-agree carries:
1. (do: done, above.)
2. the entry. **Captures in place: done.** A clause's body is ex-fbtc,
   ex-fbtr's body with no capture lets, rewritten by exec-vmcs's `ex-cs`:
   a position of the captures' is `(:capt j)`, one past them m lower.
   ex-cs-mx (mx2 answers the same of both: the environment a ++ c ++ b
   against a ++ b, c the captures resolved) and ex-cs-xwf (well formed in
   m fewer positions) carry ex-fbtc-mx and ex-fbtc-xwf, so ex-enter-mx1
   and ex-clauses-ok -- and everything above them, ex-vm-agree,
   ex-vm-runs -- stand unchanged in statement; ex-tr, ex-vwf, ex-agree and
   ex-vgood are untouched (the rewrite is of the translation, not of the
   scope). vmtrg's `vtg-local` reads through the same rewrite (`vtb-cs`),
   so `vtg_local` is exact; vtg-tr-ex-tr pushes ex-cs of ex-tr's;
   fuzz-vmtr-gen draws np and m.
   **The fn itself: option (a).** The self slot keeps ex-fbtc's let, the
   local after the parameters, and vm.inc's self read changed to match:
   vm_clause wraps the body in `(:let (:capt ncap) ..)` and maps the self
   slot to position nl (the loop's copies one higher). Its value is the
   named gap: the model remakes the closure, `(:mkclo tm (:capt 0)..)`;
   vm.inc reads the runtime's closure, which holds itself past its
   captures (VmRuntime rt_capt) -- the same fn, and the one Clojure's
   self name is (identical?, and a machine CLO list could not escape to
   the evaluator). vm.inc lets it only when the body reads the self slot
   (ex-fbtc always does: a position no name reaches otherwise, named with
   the rest of the entry) -- let always, fib (no self read) ran 115 ms for
   94 (fib 27, CLOTRAN_VM=1). Cost: a push a call of a fn that names
   itself, against (b)'s re-proof of vmx2,
   vmx2-proof, -cost, -time, vmi and vmg (~1940 s alone) to make mx2's call
   append the closure to caps.
   **Generated (vmtrcl.lisp):** `vtg-clause` builds the clause on the
   scope the host made (ex-fbcm; vtb-cs the counts) -- vtg-clause-ex-clause:
   at sl 1 it pushes exactly ex-clause, the scope as it was; three shims
   (vtg_num, vtg_key, vtg_self). Named: vtg_self pushes `(:capt m)` (above),
   and vm.inc passes sl 0 (no let, no self position) when the body reads no
   self slot. `vtg-arcl` pushes ex-arcl, `(0 (:prim :clotran.vm/arity
   (:const name) (:local 0)) :rest)`; ex-arcl-mxcl: a callee's clauses with
   it appended answer ex-mxcl's for a count some clause takes, and else the
   prim's throw where ex-mxcl throws :arity (hypothesis: the prim throws --
   vm_arity_hook, clj's ArityException). Cost: vtg-clause-steps-bound
   (linear in body and arity), vtg-arcl-steps-bound (11). fuzz-vmtr-gen
   runs both against ACL2 (clause/arcl modes, -x parts them). ex-def
   itself keeps no arity clause: ex-vm-agree is over ex-mxcl, which ex-arcl-mxcl
   relates.
   **The scope: generated (Lane 3 item 2).** vmtrcl's `vtg-scope` makes
   vm_clause's scope from none -- the parameters (vtg_binds), each
   capture's inner slot read in place (vtg-inrs over vtg_nin / vtg_inr,
   vtg_capin), the self slot when sl (vtg_bind); vtg-scope-fbcm: ex-fbcm at
   sl 1, ex-fbcm0 at sl 0. Cost vtg-scope-steps-bound (linear in parameters
   and captures). Named, not proved: vtg_nin / vtg_inr read the capture
   pair vector vm_compile_fn is handed where the model reads ex-inners of
   the template; vtg_capin is c%capt(s) = j (no local) where the model
   appends s (vtg_local's ex-cs reading, exact as before). vm_clause's
   hand loops are gone. fuzz-vmtr-gen's clause cases check vtg_scope's
   scope is the case's ex-fbcm / ex-fbcm0. **What stays the host's, named:**
   vm_clause's read of the arity vector (nf, variadic, start, body), its
   context and vm_scan (the refusal and the reads, hand Fortran over the
   source tree) and the sl decision (above); vm_compile_fn's arities' loop
   -- vm_clause of each arity in order, a refusal of any refusing the fn,
   then vtg_arcl last: ex-clauses's order, then ex-arcl -- and the
   program's reservation, vmicg_defs's compile (generated, vmicg), fuse,
   the JIT and the constants: host actions, not a translation.
3. loop/recur. **The dummy: dropped.** x2wf no longer asks a loop bind at
   least one: `(:loop () body)` is well formed, a recur to it `(:recur)`
   -- what vm.inc already emitted for a zero-binding loop. Weighed: the
   other way, a dummy only for a zero-binding loop, kept vmx2 but split
   every exec-vm loop lemma on n = 0 and made vm.inc emit it too; relaxing
   x2wf is one conjunct (vmx2, vmx2-proof's x2wf-loop-parts) and the vmx2
   chain (vmx2-proof .. vmg, vmic, vmf, vmj, vmrt) re-certified unchanged,
   and the exec books' change a deletion: ex-lsl is a loop's slots, ex-k
   its count, ex-tr's loop `(:loop (locals..) body)` and recur `(:recur
   args..)`, ex-fbin's loop the parameters' copies; ex-vm-agree and
   ex-vm-runs stand in statement unchanged.
   **Left:** (a) the independent-inits loop: vm.inc's `(:loop (inits..)
   body)` when no init reads an earlier binding (vm_loop_indep) -- every
   one-binding loop -- against ex-tr's lets and copies. **The predicate:
   done.** exec-vmtr's `ex-rd` is vm_reads_in on the tree (a local, a fn's
   or lazy's capture in lo..hi-1; the same kinds walked; any other kind
   reads), `ex-lind e 1` vm_loop_indep (init i from 1 reads none of s..s+i-1).
   **Left, the design** (checked against ex-ev, not yet built):
   ex-tr's k 12 when `(ex-lind e 1)`: `(:loop (ex-tr :lin e 0 cm) (ex-tr
   :let e 0 cm))`, :lin a new flag walking the inits as :rec does (each
   in the outer scope, blanked by the ones before), and :let's walk for
   it emitting no let (scope blanked, not appended) and at n2 the body in
   `(ex-blank ls cm) ++ ls` as now. ex-ev is untouched: its :let ignores
   tmp, so ex-vind's :let carries the inits' values in tmp (as :rec does)
   and at n2 enters :iter with them; ex-vhyp asks `(len tmp) = i`, their
   ex-xvs, and `(ex-agree (ex-slots s i) tmp fr)`; ex-vpost's m for it is
   mx2-loop of `(:loop nil (ex-tr :let e i cm))` on tmp ++ the rest's
   mx2-args (ex-mx-loop-body0 gives :m's from it). **The trap:** an init
   in the outer scope may reuse an earlier loop slot for a let of its own
   (ex-vwf only keeps a let's slot out of *its* scope), so the tree
   overwrites s+j before the body reads it while the VM keeps the init's
   value -- false without a condition. So ex-vwf's indep step asks each
   init well formed twice: in cm (the translation's scope) *and* in cm ++
   (ex-slots s i) (the slots reserved), plus `(ex-nomem (ex-clr init) ls)`;
   ex-vind lists both of the init's instances: the first gives mx2's
   answer, the second -- env ++ tmp, which agrees by the vhyp conjunct --
   gives the agreement on ex-slots s i after the init (its clears miss
   ls), so no frame lemma is needed. ex-vwf0 (exec-clrvm) and ex-cmpind
   take the same two instances; then ex-tr-xwf-flag (:lin as :rec's
   x2wf-args), exec-vmok's case lemmas (ex-vgood-let-imid/-iend beside
   ex-vgood-let-mid/-loop; ex-vgood-m-let split on ex-lind), exec-cost.
   ex-vm-agree / ex-vm-runs keep their statements.
   **Part 1 done (exec-vmtr, exec-vm certify):** ex-tr :lin (ex-vrank
   now :lin 1, :m 2; ex-vleft :lin as :let), :let's lind walk and k 12's
   `(:loop (ex-tr :lin e 0 cm) (ex-tr :let e 0 cm))`; ex-vwf :let lind step
   (slot new, init in cm and in cm ++ ex-slots s i, `ex-nomem (ex-clr init)
   (ex-slots s n2)`), its n2 (no subsetp ls cm), :lin, and k 12 asks
   `(or (not lind) (ex-vwf :lin e 0 cm lp defs))`; ex-xgood :lin as :rec,
   :let lind `x2wf .. (+ (len cm) n2) n2` (ex-tr-lin-len/-true-listp);
   exec-vm ex-vhyp conjunct (tmp len i, xvs, agree ex-slots s i), ex-vpost
   :let-lind case (not :recur; m = ma thrown or mx2-loop of (:loop nil
   (ex-tr :let e i cm)) on tmp ++ (val ma)), ex-vind lind step (3 kids)
   and n2 (:iter on tmp, cm blank ls). **Part 2 done (all books certify):**
   ex-vhyp's lind conjunct also bounds i <= n2; exec-vmok ex-vgood-let-mid/-loop
   and -m-let exclude lind, ex-vgood-let-imid/-iend and -m-ilet beside them
   (helpers ex-ev-let-tmp: a let's walk reads no tmp; ex-agree-slots-snoc;
   ex-nomem-slots-less; ex-slots-snoc moved in from exec-clrvm; ex-vgood-m-let
   one lemma over -m-let0/-m-ilet, the flag proof not splitting on ex-lind);
   exec-clrfn ex-vwf-lin-lp (ex-vwf-nolp); exec-clrvm
   ex-vwf0's lind step asks the init in cm and in cm ++ ex-slots s i, the rest
   in cm (no slot), the body without subsetp; ex-cmpind takes the two init
   instances; ex-vwf-let-lin gives ex-vwf's :lin from its :let walk;
   ex-vwf-cwf excludes flg :lin (ex-vwf0 has no :lin walk). The
   measures (ex-vrank :lin 1, else 2) needed no change. Still open: vtg-tr
   (vmtrg) takes no k 12/16 -- it would need ex-lind as a guarded vtg
   function, the :lin walk and :recur, and vm_tr's (b) case first.
   (b) the
   fn's loop only on a recur to the fn (vm.inc's c%fn_recur): ex-fbin
   without the loop is the body in ex-fbcm, the parameters not copied, a
   second entry path (:m, not :iter) through exec-vmcall's ex-enter-*.
   **(b) model done:** exec-vmtr's `ex-tlr` (a recur in a tail place lp
   reaches, no loop round it: the fn's) picks ex-fbtr/ex-fbin's shape --
   the loop when it holds, else `(ex-tr :m body 0 (ex-fbcm tm ar))`.
   exec-vmcall: ex-vwf-tlr-nil (no tail recur: well formed with lp nil),
   ex-vwf-sb (ex-vwf reads its scope only through the entries but nil, so
   ex-fcmb's well-formedness is ex-fbcm's: ex-fcmb-sb), ex-fbtr-mx-m,
   ex-enter-mx-m / -vwf-m, ex-call-mx-m / -vwf-m / -agree-fbcm (ex-enter-mx
   and ex-fbtr-mx now ask ex-tlr); exec-vmlf ex-arwf-vwf-m, ex-fbtr-xwf
   both shapes; exec-vm ex-vind's call entry takes both IHs (:iter in
   ex-fcm, :m in ex-fbcm with lp nil); exec-vmok ex-vgood-call-enter-m
   beside -enter, joined as -enter2. ex-vm-agree / ex-vm-runs unchanged
   in statement. **Generated:** vmtrg's `vtg-tlr` (guard t), ex-tlr on
   a tree in the reads' range with no case (vtg-tlr-ex-tlr; vm_scan
   refuses case), cost vtg-tlr-steps-bound (5 steps a node it reaches);
   vm_clause's loop test is vtg_tlr(body), c%fn_recur (rinfo's) gone.
   scripts/fuzz-vmtr-gen also runs vtg_tlr against ex-tlr on trees with
   recur, loop and letfn.
   **(a)+(b) generated (vtg-tr's kinds 12, 16):** vmtrg's `vtg-rd` / `vtg-lind`
   (ex-rd / ex-lind on a tree in the reads' range, vtg-okt: vtg-rd-ex,
   vtg-lind-ex; a fn's captures through the read `vtg_rdcap`), vtg-tr flg 3
   (a loop's inits / a recur's args, each pushed, ex-tr :lin / :rec), flg 5
   (an independent loop's body, its inits blanked, `vtg_binds`), flg 1 at n2
   for a dependent loop (`vtg-locs` then `(:loop ((:local p)..) body)`),
   `vtg-node 0` (a plain list), ops 4 :loop 5 :recur. vtg-tr-ex-tr now
   states the stack as vtg-out (flg 3 a revappend). Cost: vtg-steps-bound
   16 a node; vtg-lind-steps-bound 6 a node the test walks. vm_tr's
   N_LOOP / N_RECUR cases, vm_loop_indep, vm_reads_in, vm_wrap_lets and
   vm_head_list are gone; fuzz-vmtr-gen draws loops and recurs.
   **Left:** vm_clause itself (item 2's Left).
4. calls and Vars. **Var: done** (vtg_deref, ex-derefok). **A constant
   builtin's call: done** -- exec-vmtr's ex-bip/ex-bipe (prim
   :clotran.vm/builtin of an atom head constant, not :apply); ex-tr, ex-vwf
   (args in scope cm, no head let), ex-v2, ex-vind, ex-vwf0, ex-cmpind take
   the branch; exec-vm's named ex-bipok, ex-mx-callp; exec-vmok's
   ex-vgood-m-callp (ex-vgood-m-call now its complement); ex-vm-agree,
   ex-recur-stays, ex-vm-runs, ex-anp-runs, ex-top-runs, ex-anp-runs-defs gain
   (ex-bipok). vmtrg generates it (vtg_bip, vtg_hd, vtg_node 6), vm_tr's
   constant-builtin branch gone; fuzz-vmtr-gen draws it (fz-prim attaches the
   builtin test). **(a) a direct-linked Var whose fn wraps a builtin: done**
   -- the branch is now exec-vmtr's ex-pcall (ex-pk 1 a constant builtin, 2
   a Var of i2 1 whose v prim :clotran.vm/wraps at the call's count, ex-wrapf;
   ex-phd the items before the args, ex-pop the op), taken by ex-tr, ex-vwf,
   ex-v2, ex-vind, ex-vwf0, ex-cmpind; exec-vm's named ex-wrapok (such a v is
   an IFn; ex-mxcall of v on n values is (:out) or prim f's answer),
   ex-mx-pwrap, ex-mx-pcall, ex-pcall-ifn; ex-vgood-m-callp over ex-pcall;
   the top theorems gain (ex-wrapok defs); vmshift's ex-pcall-sh-rd. vmtrg
   generates it (vtg_pk, an int, replacing vtg_bip; vtg_hd pushes
   wrapper_of's f), vm_tr's vm_linked_builtin branch gone; fuzz-vmtr-gen
   draws it (fz-prim attaches :clotran.vm/wraps). Named, not proved: the
   model's link test is i2 1 where vm.inc's is i2 1 and the link epoch.
   **(b) a Var not direct-linked whose fn wraps a builtin: done** -- ex-pk 3,
   ex-phd (:clotran.vm/callw (:const v)); exec-vm's named ex-callwok (prim
   :clotran.vm/callw of v and n values is prim of the builtin v wraps at n),
   ex-mx-pcallw; the top theorems gain (ex-callwok); vmtrg's vtg_hd pushes
   ex-phd's items (vtg-node-rev2, vtg-cs-pcall), vtg_node 6 of nk + 1 at
   ex-pk 3; vm_tr's callw branch gone; fuzz-vmtr-gen draws Vars of i2 0 and 1.
   **(c) :callv of an IFn constant or Var, not apply: done** -- ex-pk 4
   (head kind 1 or 3, ex-ifn of v, v not :apply), ex-phd (h) the head's own
   translation, ex-pop :callv; exec-vm's ex-mx-pcallv (no new semantic
   hypothesis: ex-derefok gives the head's v after the args, ex-ifn the
   cast, not :apply no spread, so :callv is :applyv's), ex-pcall-nothrow;
   vmtrg's vtg_node 7; fuzz-vmtr-gen draws constants and Vars fz-prim
   calls IFns. Named: vtg_pk's is_ifn / vtg_hv (a non-linked Var's value
   read at translation) where the model asks prim :ifn of the tree's v.
   **(c), the rest: done** -- every other call (a local's or any other
   expression's head, a non-IFn constant's or Var's, apply's) is ex-tr's
   ex-trcall, now generated: vmtrg's vtg-tr k 6 at ex-pk 0 (shims vtg-top,
   vtg-cast, vtg-notfn; vtg-op 8 :applyv; vtg-frag takes every call;
   vtg-tr-ex-tr, vtg-steps-bound hold, 13 steps and the parts'). No new
   semantic hypothesis (exec-vm's agreement already took ex-trcall under
   ex-ifnok, ex-apok). The runtime gets prim :ifn and its refusal:
   vmrt's vrt-prim-kind kinds 9 (kifn) and 10 (knf), VmRuntime's dispatch
   to vm.inc's vm_cast_hook. Named, not proved: kind 9 is is_ifn (as
   exec_core's cast); the model's (:throw (:const :not-fn)) is vm.inc's
   (:throw (:prim :clotran.vm/notfn p)), refuse_not_fn of the head (the
   host's error, as exec_core's action 23, nothing run between); vtg_top's
   depth - 1 is ex-cloc of the scope's last position; :applyv's spread of
   apply is the runtime's :invoke of B_APPLY (rt_applyp false) where the
   model's is sk-spread. vm_tr's hand-written :callv is deleted; vm_tr
   keeps only collections, new, dot, fn, lazy-seq. fuzz-vmtr-gen draws
   local, subtree and non-IFn heads; fuzz-vmrt-gen the two new kinds.
   (Earlier note, kept: (c) `:callv` -- vm.inc translates and runs the args before the head and
   asks no :ifn, and does no apply spread (:applyv): needs the head pure
   (a local, a constant, a deref) or ex-tr reordered, and :invoke of a
   non-IFn throwing :not-fn.) Collections' op as the node: done, item 7.
5. try, letfn, case: vm_scan refused them; all three taken now.
   (a) case* -- done: ex-tr's kind 19 generated (vtg-tr flg 6, the table's
   walk; vtg-tlrw: a recur in a then or the default is a tail), vm_scan
   takes N_CASE, vm_tr hands it to vtg_tr. No new semantic hypothesis
   (ex-caseok as before). Named, not proved: vtg_ncs/vtg_cthen's entry order
   gca_entries' (the macro's tests distinct); vtg_cstest's items the N_CASE
   node and (:const then_j) where the model's are :case and (:const t): the
   runtime's kind 6, vm_node_hook, answers whether case_branch's probe of
   the value takes entry j -- one probe an entry walked (ponytail: O(n) a
   case). fuzz-vmtr-gen draws cases for vtg_tr, vtg_tlr and vtg_clause.
   (b) try -- done (option (i), James's decision): ex-tr's kind 18
   (ex-trtry) generated (vtg-tr flg 8 the catch walk, ex-trh; with a finally
   ex-trfin's two copies of F), vm_scan takes N_TRY (body, finally, each
   catch's body, its slot bound), vm_tr hands it to vtg_tr. No new semantic
   hypothesis (ex-isaok, mx2's :try as before). Named, not proved:
   vtg_catest's test is vm.inc's (:prim NODE (:const j) (:local p)) --
   vm_node_hook's N_TRY, catch_matches of catch j's class -- where the
   model's is (:prim :isa (:const c) (:local p)); the implicit rethrows
   (ex-trh's walk end, ex-trfin's handler's two) are a DISTINCT prim,
   vtg_rethrow's (:prim NODE (:local p)) -- vm_node_hook's N_TRY with one
   value, vm_rethrow: (:throw . p) as prim's throw unwinds, the host's
   error raised again with the message and trace vm_caught kept when p is
   the value the VM caught, else raised as N_THROW raises p -- where the
   model's is (:throw (:local p)); an explicit (throw e) in a catch stays
   kind 17's (:throw x), raising the printed value as the tree does. vtg_nk
   of an N_TRY is exec_core's nk (a nil finally slot: one). The host side
   (vm.inc, Eval.f90's vm_runref): a hook (call, node, cast, arity) entered
   with the host's error raised means the VM caught it -- vm_caught clears
   it as exec_try's catch does, trims the frame stack to the run's, and
   keeps value, message and trace on the run's vm_runref (the last four;
   ponytail: a finally catching four more host errors before its rethrow
   loses the first's message to the value's text); a status-0 end clears
   what is left; a status-1 end whose raised error is not the value thrown
   (a finally's own throw, no hook between) clears it and raises the value;
   vm_took sets the value it makes as the thrown one; runs past vm_runs' 64
   keep nothing (n_vm_deep). trace_order now skips a (:try ..)'s handler
   records (kind 2) where it read every record as a call's. And a run the
   machine stops out of room (status 2) inside a (:try ..) of its own raises
   the host's stack_overflow_error and throws it to the handler (vmg_unwind,
   as a prim's throw) -- outside vmfg-correct, whose status 2 is no answer;
   the tree's frame limit raises one a try catches (fuzz-regressions' deep
   recursion caught as :so, which crosscheck found). fuzz-vmtr-gen
   draws trys (catch j's class 60 + j, slot s2 + j, a finally or none);
   scripts/fuzz -m vm,jit's try/catch/finally forms run on the VM now.
   Divergences left, named: the tree's implicit rethrow reports no trace
   lines (gce_trace empty -- after a finally exec_core's action 22 restores
   kst%msg, not last_trace, which gce_clear_error emptied; with no clause
   taken the tree's report has none either) where the VM's keeps the
   original throw's (vm_caught's); and every VM frame in a trace lacks its
   file:line and the report names the run's entry, as before try.
   (c) letfn -- done: ex-tr's kind 13 (ex-trlf) generated (vtg-tr flg 7,
   vtg_lfinit, vtg_lfbinds), vm_scan takes N_LETFN (its kids fns), vm_tr hands
   it to vtg_tr. No new semantic hypothesis (ex-lfok, x2-seal as before).
   Named, not proved: vtg_lfinit's init is `(:prim NODE (:const j) caps..
   (:local d)..(:local d+j-1))` -- vm_node_hook's N_LETFN builds fn j's
   closure (the N_FN path) and patches the group's captures among it and the
   earlier lets' closures, so after the last let the one cyclic group
   exec_letfn makes (identical? of siblings as the tree's); a group capture
   `(:const nil)` where the model's is `(:const (:grp nil m))`. fuzz-vmtr-gen
   draws letfns (templates (0 0 (o 0 ..)), outer slots the group's or not).
6. (the cost theorem and fuzz-vmtr-gen: done, above.)
7. Collections -- (a) done: a vector, map or set literal, a new and a dot
   call (ex-kinds 7 8 9 22 21) are ex-tr's `(:prim op args..)`, op exec-tree's
   ex-cop, the args the kids in turn (ex-tr :coll), generated: vmtrg's vtg-tr
   k 7 8 9 21 22 (vtg-coll; vtg_cop then flg 3 from 0, as a recur's args,
   then vtg_node 6; vtg-tr-ex-tr, vtg-steps-bound hold, 3 steps and the
   kids'). vm_tr hands them to vtg_tr; its hand-written collection branch
   and vm_tr_kids are deleted. No new semantic hypothesis (exec-vm's
   agreement already takes them under ex-collok). Named, not proved:
   vtg_cop's op is vm.inc's NODE itself, the runtime's kind 6 --
   vm_node_hook builds the vector, set (vec_to_set), map (vec_to_map), new
   (new_cached) or dot call (dot_dispatch) from the parts' values -- where
   the model's is ex-cop's :vector, :map, :set or (:host k C).
   fuzz-vmtr-gen draws all five kinds. (b) a fn (14) -- done: ex-tr's
   `(:mkclo tm caps..)`, caps ex-locals of the template's outer slots
   (ex-outers), each read in place, generated: vmtrg's vtg-tr k 14
   (vtg_fnhd, vtg-caps walking vtg_ncap / vtg_capo, vtg_node 0;
   vtg-caps-st, vtg-tr-ex-tr and vtg-steps-bound hold, 3 steps and 2 a
   capture). vm_tr's N_FN branch is gone. No new semantic hypothesis
   (exec-vm's agreement already takes :mkclo). Named, not proved:
   vtg_fnhd's items are vm.inc's :prim and the N_FN node itself -- the
   runtime's kind 6, vm_node_hook building the closure from the captured
   values (make_closure_from's two shapes) -- where the model's are :mkclo
   and tm; vtg_ncap / vtg_capo read the template's pair vector (slot 2)
   where the model's is ex-outers of its list. A lazy seq (15) -- done:
   ex-tr's `(:prim (:host 15 tm) (:mkclo tm caps..))`, generated: vmtrg's
   vtg-tr k 15 (vtg_cop, vtg_fnhd, vtg-caps, vtg_node 0, vtg_node 6 2;
   ex-tr-lazy-kind, vtg-tr-ex-tr and vtg-steps-bound hold, 5 steps and 2 a
   capture). vm.inc's encoding changed to ex-tr's nesting (James approved;
   it was one flat `(:prim NODE caps..)`): `(:prim LAZY (:prim FN
   caps..))` -- the inner a fn's closure exactly (vm_node_hook's N_FN), FN
   an N_FN node of the lazy seq's template made at translation (vtg_fnhd,
   mk_node in analyze_fn's shape), the outer vm_node_hook's N_LAZY now
   only the wrap of its one value in a pending lazy seq (eval_new's
   clotran.host.lazy_seq's). Behaviour unchanged: the same closure, wrapped
   the same. No new semantic hypothesis (ex-collok's (prim (:host 15
   C))). vm_tr's N_LAZY branch and vm_node_prim are deleted.
   fuzz-vmtr-gen draws lazy seqs. (c) open: def, deftype, a new of a type, set! (10 20 23
   24): ex-tr has them, vm_scan refuses them.
The hooks stay host actions; the gap to the analyzer's tree is the
analyzer row's (anbuild builds the tree ex-tr reads only up to
ex-defs-ok0, exec-clrvm).

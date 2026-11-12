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
   Next: letfn.
4. **Clearing joined**: the machine theorem over anpass's marks, from
   tr-sound -- a marked read's slot is never read again.
   *(done)*: exec-vm (first part), exec-clr, exec-clrmap, exec-clrlv,
   exec-clrfn, exec-clrvm; the templates' bodies and the loop-init case
   left, named in its paragraph above.
5. **The rest**: def, letfn (`exec_letfn`), deftype, new *(done)*, set!, dot,
   N_LAZY, N_TOP, the debugger's frames (`break_frames`). Then the row is
   Generated but for the actions, named.

N_FLAT (flat.inc, To be retired) and N_VMB (the VM itself) are not this
row's.

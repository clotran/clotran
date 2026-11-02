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
evaluator and the VM agree. Locals clearing is anpass-sound's
(no cleared slot is read again); joining the two is milestone 4.

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
2c-v. **`:applyv` in the arrays** *(next)*: vmi and vmg (so the Fortran
   VM) get apply's spread -- `(:applyv m)` in vmic/vmicg instead of their
   refusal, the generated machine spreading through seqk's kinds; then
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
4. **Clearing joined**: the machine theorem over anpass's marks, from
   tr-sound -- a marked read's slot is never read again.
5. **The rest**: def, letfn (`exec_letfn`), deftype, new, set!, dot,
   N_LAZY, N_TOP, the debugger's frames (`break_frames`). Then the row is
   Generated but for the actions, named.

N_FLAT (flat.inc, To be retired) and N_VMB (the VM itself) are not this
row's.

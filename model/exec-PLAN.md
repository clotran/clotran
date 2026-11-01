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
meaning is `mx` of the tree's translation, slots mapped to `mx`'s
positions (exec-vm, `ex-vm-agree`), and the VM run of the translation
answers the tree's value (`ex-vm-runs`, with vmx-proof's `vcsx-correct`).
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
2a. **The machine and the generation** *(this commit)*: exec.lisp's turn
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
3. **Throw and try, case, collections**: N_THROW, N_TRY's pcs 0..5 and
   `k_unwind`'s catch walk (vmi's handler stack is the model), N_CASE's
   branch (`case_branch`), N_VECTOR/MAP/SET; their nested `exec`s made
   record steps as recur's were.
4. **Clearing joined**: the machine theorem over anpass's marks, from
   tr-sound -- a marked read's slot is never read again.
5. **The rest**: def, letfn (`exec_letfn`), deftype, new, set!, dot,
   N_LAZY, N_TOP, the debugger's frames (`break_frames`). Then the row is
   Generated but for the actions, named.

N_FLAT (flat.inc, To be retired) and N_VMB (the VM itself) are not this
row's.

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
   *(this commit: `ex-vm-agree` over loops and recurs, a recur's values
   only ever its loop's slots, never a value outside a loop's tail
   (`ex-recur-stays`); the translation is `xwf` (`ex-tr-xwf`), so with
   `vcsx-correct` the VM run answers the tree's value (`ex-vm-runs`))*
2. **Calls and fns**: N_FN's closure, N_CALL's record (argument mode,
   `bind_closure`'s slots, the fn body's KF_FNBODY|KF_RESTART record, a
   recur to the fn), N_VAR. Needs `vmx`'s `:callv`/`:mkclo` and the
   captures (anlocal's) in the meaning.
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

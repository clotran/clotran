# The ahead-of-time compiler: a model (lane 3n)

The row: docs/model-coverage.md, "Ahead-of-time compiler to Fortran",
`compiler.cljf` (2.1k) and `purefort.cljf` (1.4k), Owed. Both run inside
clotran (cljf) on `(clotran-ast form)`: the analyzer's tree exported as
maps, each carrying its OBJ_AST on `:node`.

## What the compiler decides

- compiler.cljf (tier B, library procedures on the runtime's ABI):
  1. ELIGIBILITY (`decline-reason`): no body; captures; a self name; and a
     recur, under a node of a kind it does not emit (`compiled-ops`: const
     local var if do call let loop recur fn lazy new dot), that is not
     inside a loop, fn or lazy-seq below that node. Such a node is pooled
     and run whole by the interpreter, which would hand the recur back as
     a value. Nothing declined is half-compiled.
  2. TYPES (`infer`, `call-type`, `bind-types`, `loop-env`): :long :double
     :bool :any :none per node, Clojure's primitive-local rules, a loop's
     slots joined with its recurs' to a fixpoint (at most 5 rounds, else
     boxed); the op of a call head is a host read (builtin name, or Var
     identity against clojure.core).
  3. ARITIES AND VERSIONS (`param-vectors`, `versions`, `guard-code`,
     `arity-code`): which procedure runs for an argument count, and which
     speculated typed version for argument tags.
  4. EMISSION (`gen` and its helpers): Fortran text per node kind, slots
     on the frame, typed temporaries, overflow checks, the escape hatch.
- purefort.cljf (tier A, runtime-free modules): param candidates and the
  cartesian versions (`version-limit` 8), `can-fail?`, emission.

It refuses by answering `{:declined why}`; purefort declines a version by
`decline` (an ex-info), and a function with no typed version.

## The statement, slice by slice

The meaning is the tree's: anpass-runs' `tr` (the runs exec.inc makes, a
recur an event) for the eligibility scan; exec's `ex-tr` / exec-vm for the
values. A compiled fn on a value of the typed subset answers what ex-tr
answers -- the vmic-correct shape -- is the end statement (slice 4).

## Generated vs named

Generated (scripts/acl2-fortran, Fortran called from cljf through a
builtin): decision procedures over the OBJ_AST -- the eligibility scan
(slice 1), the type inference (slice 2), the arity/version choice
(slice 3). Named host glue, hand-written: the reads (anpass's `ast_*`
shims, plus a fn's arity bodies `aot_nbods`/`aot_bod`), the builtin that
calls a generated procedure, the cljf's map plumbing, the Fortran text
itself (strings; slice 4 would model its meaning, not generate cljf).

## Slices (smallest first)

1. ELIGIBILITY SCAN -- model/aot.lisp: aot-fr (a recur under a node, not
   past a loop/fn/lazy), aot-sc (some non-emitted node over the fn's
   bodies, nested fn bodies included, has one). aot-proof.lisp:
   aot-sc-sound (the scan passes => every non-emitted node it reaches has
   no such recur) and aot-handed-norec (such a node, its tail check
   passed in its position, makes no recur in any run: `tr` has none).
   Generated src/f/gen/aot_gen.inc; builtin `clotran-aot-scan`;
   decline-reason's recur clause calls it. fuzz-aot-gen: generated vs
   ACL2 on random trees, -x the negative control. LANDED this lane.
2. TYPE INFERENCE -- model/aot.lisp's aot-ty (infer, call-type,
   bind-types, loop-env as compiler.cljf wrote them), on exec.lisp's tree
   (the one ex-ev runs) with three host reads more, over the stobj aots
   (a slot's type code; the current loop's recur types; a loop's settled
   types; the current call's operand types). Generated into
   src/f/gen/aot_gen.inc (aot_ty), answered by the builtin `clotran-aot-ty`
   (Eval.f90, aot_infer in analyze.inc) to compiler.cljf's infer and
   loop-env; the hand-written walk is deleted. GENERATED AND FUZZED THIS
   LANE; ITS PROOF IS OWED (below). Checked before the walk was deleted:
   old and new compared at every call on core.clj's 494 defns (428
   compiled), compiler-check's 249 calls and `scripts/fuzz -m compiled`
   -s 11: no difference. fuzz-aot-gen runs the generated aot_ty against
   ACL2's on random trees in random environments (types and ok); -x reads
   a double constant as a long and must part.
   - Codes: 0 none, 1 any, 2 long, 3 double, 4 bool, 5 doubles, 6 longs.
   - Model choices that differ from the cljf only on trees the analyzer
     does not build: a let's slot is written and the old word written
     back (the cljf rebuilt a map); a loop's recur types accumulate over
     its rounds instead of restarting each round (equal: the round's env
     already holds the earlier rounds' join, and join is a flat lattice's);
     a recur joins only into the innermost loop's slots (cljf: its atom).
   - Host reads, named: aot_hop (head-op: a folded builtin's name, or the
     Var's name when its namespace is clojure.core -- identity against
     ns-resolve, for an interned Var), aot_cty (const-type: an int? not
     Long/MIN_VALUE, a finite double? not a float, a boolean), aot_kw (a
     constant :doubles/:longs, the array cast's hint), aot_i2, aot_s2,
     aot_rs, aot_rn (exec.inc's reads of the same fields); the frame size
     is the template's nslots (*aot-nslots*), a slot past it typed any.
   - THE STATEMENT OWED (aot-ty-proof.lisp), designed:
     TYPED SUBSET (aot-sub): nodes of kinds const local var if do call
     let loop recur fn only, in exec-clrmap's shape bounds; no local
     marked for clearing (exec-clr proves a cleared slot is never read
     again; the statement does not use it); A-CONST: a constant whose
     read says long/double/bool has that host tag (aot-tag, an
     unconstrained function: the host's class of a value); A-HEAD: a call
     whose read names op k has a const or Var head whose value the host
     reads as k (aot-opof, unconstrained); ok = 1 (aot-ty's second answer:
     each let/loop slot untyped where bound, a loop's slots above the
     enclosing loop's, each recur to the current loop with its count).
     A-OP (a defun-sk, as exec-vm's ex-ifnok): a call whose callee the
     host reads as op k, its operands fitting the types aot-ty kept (the
     array cast's operand exempt: the cast checked it), answers in ex-ev
     a value of aot-optab's type, or not a value.
     THEOREM aot-ty-sound: with those, frame fr fitting the env (every
     slot's value of its type), r = (ex-ev :m e 0 nil fr fuel): if r is
     a value, it is of the type aot-ty gives e (long: aot-tag long, ...)
     and its frame still fits; if r is a recur, every slot fits its type
     or is one of the current loop's and fits what aot-ty joined there;
     throws and :out say nothing. Proof plan: ex-ind's induction with the
     stobj threaded as aot-ty threads it; lemmas: aot-ty leaves tv, cb,
     cn, a0..ad as it found them (every put paired with its restore), rc
     monotone below cb+cn (the ok's loop-above condition), a loop's final
     round is the env every iteration starts in (settled, or all any).
     COST (owed): ns, the nodes visited, at most wt(e): a node 1 + its
     parts, a loop's body 7 times (six rounds and the boxed one), an
     array cast's operand twice -- 7^depth of nested loops, as the cljf.
3. ARITY/VERSION CHOICE -- proved to pick ex-tr's arity (exec's arfit).
4. EMISSION -- a vmic-style compile to an IR with a meaning, proved to
   agree with ex-tr on the typed subset; the cljf prints the IR. Only
   then may the row be Modeled.
5. purefort's candidates/versions/can-fail, the same way.

The Owed row stays Owed until slice 4; slice 1 is its own Generated row.

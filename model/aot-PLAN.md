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
2. TYPE INFERENCE -- aot-ty over the tree with a named head-op read and a
   bounded fixpoint; proved: a node typed :long/:double/:bool evaluates
   under ex-tr (when it ends) to that kind of value.
3. ARITY/VERSION CHOICE -- proved to pick ex-tr's arity (exec's arfit).
4. EMISSION -- a vmic-style compile to an IR with a meaning, proved to
   agree with ex-tr on the typed subset; the cljf prints the IR. Only
   then may the row be Modeled.
5. purefort's candidates/versions/can-fail, the same way.

The Owed row stays Owed until slice 4; slice 1 is its own Generated row.

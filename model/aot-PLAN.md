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
   - Model change, lane 3r (no change to the answer): a loop round ok is joined with
     the next round ok (aot.lisp fl 5), so ok=1 says every round of every loop was ok -- a
     loop inside an intermediate round then cannot zero the recur types of the loop around
     it (aot-ty-rc-le needs it). It rejects (ok=0) only a let rebinding a loop slot typed in
     an early round, which the analyzer, giving each scope its own slots, does not build.
   - PROVED (model/aot-ty-proof.lisp, lane 3r): aot-ty-restore (tv cb cn exact, rc length;
     the operand registers but in a call argument walk); aot-ty-rc-grows (ok => rc only
     grows below cb+cn); the rounds: aot-star (the env the final round types the body in)
     with aot-star-ty (answer and ok are that walk), aot-star-settled (that walk leaves the
     loop slots rc below their types: settled, or all any when boxed), aot-star-env (the
     env only rises, and only on the loop slots); the frame-fit steps aot-ffr-* (bind,
     unbind with fresh, an ok walk, settle, widen, narrow); and the COST, aot-ty-cost: ns,
     the nodes visited, at most aot-wt -- every state-dependent choice at its dearest: a
     loop body 7 times (six rounds, the boxed one), an array cast operand twice, a recur
     its count or the loop (cb cn) -- so 7^d walks of a node under d nested loops.
   - PROVED (lane 3s), model/aot-ty-sound.lisp: aot-ty-sound, (aot-cl flg e i tmp fr fuel s) for
     every ex-ev flag, its aot-ty walk aot-tyof (:m/:iter 0, :do 1, :let 2 or 6, :rec 3,
     :call 4). HYPOTHESES, exactly: aot-sub (kinds const local var if do call let loop recur
     fn; fields in 40 bits; no local marked for clearing; ex-wf's shape of an if (2 or 3
     kids) and of a let or loop (i2 + 1 kids: the inits and the body); A-CONST: a constant fits its read
     type, aot-tag unconstrained; A-HEAD: a call whose op read is not 0 has a const or Var
     head whose value aot-opof reads as it; A-OP, aot-opok, a defun-sk: such a call, its
     operands 1..3 fitting types ta tb tc -- the first may instead be an array cast whose
     ta is its keyword type -- answers in ex-ev (:call at its last operand) a value of
     aot-optab type or none); cb cn natural, len tv <= len rc; ok = 1; the frame fits tv
     (aot-ffr); per flag: :do i < nk; :let i <= i2 and kind 11/12; :rec rstart = cb, nk = cn,
     rn = nk, tmp fits rc (aot-rfit); :call tmp the callee and i-1 operands fitting the
     registers (the cast exemption with ad = 1); :iter the walk at the final round env
     leaves rc settled. CONCLUSION: a value fits the type (for :call, optab of the
     registers) and the frame fits tv after (but a loop own slots, in the :let chain of a
     loop); a recur leaves the current loop slots fitting rc, the rest tv. The model
     differs from the old cljf only on trees the analyzer does not build: a let writes its
     slot and restores it; recur types accumulate over a loop rounds; a recur joins only
     the innermost loop. Headline: aot-ty-sound-m (a node walked ok in an env its frame
     fits answers in ex-ev a value of the type aot-ty gives it, the frame still fitting).
     The proof: induction aot-ind (ex-ev's recursion with the state aot-ty walks each part
     in); one lemma per ex-ev case (aot-cl-*), its IHs as aot-ind writes them; a call's
     operand step through aot-s3 (the registers after operand i) and aot-regok, so the
     cast's case split stays in two small lemmas. Certifies in ~80 s.
   - THE ASSUMPTIONS, how far the host reads justify them: the 40-bit fields, the kinds
     and the shapes are what anpass's reads and ex-wf already say of an analyzer tree;
     no clearing marks is assumed (whether the trees compiler.cljf sees carry them is not
     checked here). A-CONST: aot_cty computes the type FROM the constant
     (int? not Long/MIN_VALUE, finite double, boolean), so it holds of the host by
     construction; in the model aot-tag is a stub, so it stays a hypothesis. A-HEAD:
     aot_hop is nonzero only for a folded builtin const or a Var whose namespace is
     clojure.core, so the head is a const or Var by the read; that its VALUE is that op
     (aot-opof) assumes the core Var is not redefined -- a runtime assumption, kept. A-OP
     is the spec of the core ops (aot-optab against what +, aget, Math/... answer); it is
     not reducible to the reads and stays the one semantic assumption.
3. ARITY/VERSION CHOICE -- proved to pick ex-tr's arity (exec's arfit).
4. EMISSION -- a vmic-style compile to an IR with a meaning, proved to
   agree with ex-tr on the typed subset; the cljf prints the IR. Only
   then may the row be Modeled.
5. purefort's candidates/versions/can-fail, the same way.

The Owed row stays Owed until slice 4; slice 1 is its own Generated row.

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
(slice 1), the type inference (slice 2), the arity choice (slice 3; the
version choice is modelled and proved but stays cljf). Named host glue, hand-written: the reads (anpass's `ast_*`
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
3. ARITY/VERSION CHOICE -- model/aot.lisp's aot-arreg, aot-arnf, aot-arvr (fn-procedure's
   registration and pick), GENERATED into aot_gen.inc and answered by the builtin
   `clotran-aot-arity` (analyze.inc's aot_arity: the arities [nfixed variadic?] loaded into
   tv/rc, answered [reg var fixed...]); fn-procedure's hand-written single?/fixed/varg/:arity
   are deleted. PROVED (model/aot-ar-proof.lisp, lane 3t):
   - aot-arrun-is-ex-arity: aot-arrun (what a call of m arguments runs -- for reg >= 0 the
     caller's count check, Eval.f90's call_compiled; else the procedure's chain, the fixed
     arities by nargs == count in aot-arnf's walk, then the first variadic by nargs >= count,
     else the arity error) is exec's ex-arity (bind_closure's two ex-arfit passes): an arity
     exactly when exec has one, and the same one. HYPOTHESES: aot-arok (the stobj holds the
     template's arities: count and variadic flag in order; a count past 40 bits is read as 0
     and fails it) and aot-ar1v (at most one variadic -- clj's FnExpr refuses a second, so
     the analyzer never builds one); m natural.
   - THE VERSION CHOICE, modelled as arity-code's guards run it: aot-vsel (versions tried in
     order, the first whose guard passes -- aot-hguard, each hinted slot's value fitting its
     code: clotran_tag 2/3, an array view of kind 1/2 -- else the untyped body). aot-vsel-ffr:
     the frame then fits the env the chosen body was typed in (aot-henv: the version's codes,
     the rest any), which is aot-ty-sound-m's frame hypothesis, so aot-version-sound: the
     chosen body's ex-ev value has the type aot-ty gives it. NOT generated: versions,
     param-hints, array-params and guard-code stay hand-written cljf, the model stating what
     they decide; that they decide it is checked only by compiler-check's hinted and
     speculated-array cases (compiled against interpreted), not by the model. The guard's tag test IS aot-fits only through
     aot-tag (a stub: the same reading of a value's tag A-CONST makes).
   - COST: aot-arnf-cost, aot-arvr-cost (at most n - i + 1 calls each; the glue's walk calls
     aot-arnf once per fixed arity and once more).
   - fuzz-aot-gen: random arity sets (counts out of range, rc neither 0 nor 1) through the
     generated aot_arreg/aot_arnf/aot_arvr against ACL2's at every index; -x flips arity 0's
     variadic flag and the answers part ("arity" kind).
   - NOT PROVED here: that the arity's body then runs in exec's frame (ex-write of the
     arguments, the rest list) -- that is emission, slice 4 -- and that the template the
     cljf reads is the one exec runs (the same analyzer tree; assumed, as in slice 2).
4. EMISSION -- a vmic-style compile to an IR with a meaning, proved to
   agree with ex-tr on the typed subset; the cljf prints the IR. Only
   then may the row be Modeled. DESIGN (lane 3t, not started):
   - THE IR (model/aot-ir.lisp): what gen's statements do, not their spelling. A program is a
     list of instructions over a state (frame fr, boxed temporaries bt, typed temporaries tt,
     the recur flag, an error): (:get d s) (:put s d) (:const d c) (:box d t x) (:unbox x t d),
     (:prim op x a b) with its overflow test, (:if c then else), (:loop flag body),
     (:recur starts..) (writes the slots, sets the flag), (:call d head args) (the callee by
     ex-arity, slice 3), (:hatch d node) -- the escape: the node handed whole to the
     interpreter, its meaning ex-ev's by definition. aot-ir-run: the meaning, with fuel, cost
     theorem by counting as vm-cost does.
   - THE COMPILE (aot-cc e env -> IR), one case per kind gen emits, reading the types aot-ty
     gives (slice 2): a node typed long/double/bool goes to tt, any to bt; a typed op the
     inline prim with the overflow branch to :hatch; the rest boxed.
   - THE THEOREM, vmic-correct's shape: on aot-sub's subset, aot-ty ok, the frame fitting the
     env (aot-ffr) -- for the fn's entry, aot-version-sound's env -- aot-ir-run of aot-cc e
     answers ex-ev's value and frame (boxed: equal; typed: equal after :box), a recur as
     ex-ev's recur event. One lemma per kind, the aot-ind induction slice 2 built.
   - THE ENTRY: the arguments into the frame (ex-write, the rest list nil or the seq) after
     slice 3's pick, and the body as the flag loop; tying aot-arrun to ex-ev's :call case
     closes the gap slice 3 names.
   - CHECKED ARTIFACT: the generator returns integers, not lists, so the cljf keeps building
     the IR, as data now (gen answers IR, a printer writes the Fortran). fuzz-aot-gen grows a
     third part: random typed trees, the cljf's IR (through clotran) against ACL2's aot-cc,
     -x a dropped overflow branch. The printer is named glue: one Fortran template per
     instruction, read in review.
   - Order: 4a const local var if do let (boxed); 4b loop recur; 4c typed temps and prims with
     the hatch (A-OP enters here); 4d calls and closures; 4e the entry and versions.
5. purefort's candidates/versions/can-fail, the same way.

The Owed row stays Owed until slice 4; slice 1 is its own Generated row.

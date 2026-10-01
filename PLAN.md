# Plan

What we are about to build, what we decided not to, and why. NOTES.md
records how things came to be; this records where they are going.
Rewritten 2026-09-19 after a review of the whole tree; the previous
plan's decision records that still hold are kept at the bottom.

## The north star (James, 2026-09-27)

Four consulting scenarios, kept as a white paper and a pitch deck in
`docs/` (`make docs` regenerates the PDFs from the markdown), each with
where clotran stands today, measured:

- **A. Python/Fortran pipelines** -- Clojure orchestration over Fortran
  arrays, no copy, no glue. Packages, `bind-fortran` and ChemSol are
  this; several threads at once is what is missing.
- **B. Dynamic scripting for legacy solvers** -- a REPL driving a
  running solver. Package routines from the REPL are this, and
  `examples/embed` is a Fortran solver with the runtime linked in and
  its strategy in Clojure on its own grid (2026-09-28); a socket into
  it is what is missing.
- **C. Financial models** -- functional code compiled to lean,
  deterministic binaries. Per-namespace AOT compilation is this;
  standalone binaries and `repro` are missing.
- **D. DSLs for scientists** -- macros that compile math to clean,
  vectorizable Fortran. The macro system is Clojure's own; the
  pure-Fortran tier (step 13) is the missing half.

The order from here: the test suites (clojuredocs to 100% of portable
examples), then threads (step 14), then everything else works -- each
item weighed by which scenario it serves. "We want something this
powerful to use as consultants."

## The road from here (2026-09-29)

The white paper and deck (`docs/`, as of 2026-09-28) make promises this
plan did not list as steps; they are steps now, in this order. Each
names the scenario or goal it serves. docs/ is not being updated in
the meantime, and its numbers are those of 2026-09-28.

1. **The thread flake (step 20). First.** One oracle run in nine
   corrupts something shared after a thread case. A wrong answer that
   depends on timing undermines every scenario and goal 3, and a gate
   that has to be rerun is not a gate.
2. **Road item 1, finished: correctness, then speed.** Steps 18 and 19
   are its performance half, and they go on: step 18's stage 5 (the AOT
   compiler reading the flat form) and the last arities that stay trees;
   step 19's constant factors (making a record, a comparison called from
   Fortran). Then the clojuredocs suite re-scored -- 1233 of 1264
   portable examples (97.5%) before the flat work -- toward 100%.
3. **Sockets and a REPL into a running process (step 21).** Scenario B's
   headline, "REPL-driven control of a running solver", and goal 2's
   debugger over a live run. The target is `clojure.core.server`,
   vendored, loading unmodified.
4. **Standalone binaries (step 22).** Scenario C: `clotran build
   app.cljf -o app`, and a heap image that holds compiled core.
5. **`repro`, reproducible reductions (step 23).** Scenario C's
   "deterministic".
6. **Threads, the rest (step 24).** A thread pool for agents; parallel
   marking only if a measurement asks for it (step 14's did not).
7. **Network clients (step 25).** Scenario C's event streams, on
   step 21's sockets.
8. **The package manager.** `clotran-deps`, its own repository, reading a
   project's `deps.edn` (PACKAGES.md): the first slice resolves and
   fetches (2026-09-29); next, the launcher using it, a cached path, and
   native packages built from a recipe. Its first real package is
   `clotran-nrepl` (step 21 d).

Order from 2026-09-30 (James): first clj's names out of everything
clotran prints (DEVIATIONS 67), then step 22, then step 26 (one machine for bytecode and compiled
code: the speed James found missing), then step 24, then step 25; step 23
waits. Windows is deferred until about v1.0: macOS and Linux
until then.

Already there, though the deck says missing: `do concurrent` is emitted
by the pure-Fortran tier for loops of `amap`'s shape (2026-09-25).
Scenario D's remaining work is the rest of step 13.

## The goals, in order

1. **Complete Clojure/Fortran interoperability.** A clotran array is a
   Fortran array; a Fortran routine is an ordinary call. The finish
   line is ChemSol: `~/jborden/chemsol/src/main.f90` replaced by
   clotran code driving `chemsol.f90` and `push_array.f90`, run on
   `tests/test1.cs` .. `test3.cs` with `vdw.par`, producing the same
   outputs.
2. **A better way to debug Fortran.** Frame-based stack analysis in
   clotran, with dynamic inspection of Fortran primitives and, with
   wrappers, Fortran objects. gdb cannot do this (README explains why);
   a debugger written in the language over a representation the host
   defines can.
3. **A multi-threaded story.** Clojure's model: immutable values,
   atoms, refs, agents, STM.
4. **Eventually a JIT**, which is also what would let clotran be
   transpiled to Fortran.

Every item below is weighed against those four, not against a count
from Clojure's test suite. The suite is a measure, not the work queue;
using it as the work queue is how two days produced 2,810 lines of
clj-shaped `case` arms in one file.

## Where we are (measured 2026-09-22)

| | |
|---|---|
| core.clj | 724 of 724 forms load |
| our tests | 100% on both compilers; the gate. 914 oracle cases value-compared against `clj`, 23 expected differences |
| the derived language suite | 38 files, every file loads, 321 tests execute: 2880 pass / 0 fail / 0 error -- ALL of them, and the suite is a gate now rather than a score (2170 / 235 / 370 on 2026-09-19). The deriver was corrected on 2026-09-21: a class named in a type hint, a syntax-quoted helper macro, a quoted namespace name or code handed to `eval` now makes a test host, which took out 7 tests that were clj tests in disguise (static interface methods, `*unchecked-math*` boxing warnings, `import` of a record class, reflection warnings, an interface's error message) and let the three metadata tests execute (their helper enumerated clotran.browse's publics). Nothing is failing. The 26 spec-conformance messages went when clojure.spec.alpha was vendored and hooked into macroexpansion, `1N` when BigInt became a real type, the last compilation failure when a class became a value of its own kind, and `1.0M` when BigDecimal did -- all on 2026-09-21. What the suite does NOT cover is named in its own row: it is the clojure.core/cljs.core intersection, so nothing clj-shaped is in it |
| the portable libraries, on Clojure's OWN tests | `scripts/run-library-tests`, a gate since 2026-09-22 and part of `make test`: clojure.set, clojure.walk, clojure.string, clojure.math and clojure.pprint run VERBATIM, 109 tests and 859 assertions, 0 fail / 0 error. Not derived and mostly underivable -- the pprint tests are fragments loaded into one namespace through a macro of their own, and Clojure's clojure.zip file has no deftest at all. What the denominator EXCLUDES: clojure.data's one deftest imports HashSet, clojure.edn's tests need clojure.test.generative (not vendored), and clojure.zip and clojure.core.reducers have no deftest upstream. Those five libraries are covered by `test/clj/oracle.clj` instead |
| libraries loading | 35 of the 40 vendored namespaces `require` (set, string, walk, zip, data, edn, pprint, test, main, math, template, datafy, reflect, inspector, stacktrace, the four spec ones, ...). Loading, not running: reflect and inspector load because nothing touches the host until a call. The five that do not are each one named clj thing -- `clojure.repl` wants `proxy-super` (DEVIATIONS 28), `clojure.xml` wants `XMLHandler`, `clojure.core.server` wants `ReentrantLock`, and `clojure.repl.deps` and `clojure.tools.deps.interop` want `clojure/clj/basis.clj` and `process.clj`, which are not vendored |
| Clojure's suite, verbatim (for reference) | 2002 pass / 111 fail / 274 error over 346 tests, 84% of executed (2029 / 143 / 246 on 2026-09-19); 37 of 66 namespaces produce a passing assertion -- three more than before, and the errors rose with them: a namespace that crashes before reporting contributes NOTHING, so getting further shows up as errors. Most of the new ones are `with-precision`, which needs a MathContext (DEVIATIONS 30). The rest is clj: rt, array-symbols, clj-interop, serialization, reflect, streams, clearing, param-tags, method thunks and the generated adapters; and the suppliers (delays, atoms), BigInt and BigDecimal (vars, logic, pprint). The verbatim number predates spec being vendored; it is a reference, and it is re-measured when something moves it |
| startup | 0.75s (7.2s before step 4, 2.3s at the start of stage 2), core.clj re-read every launch |
| `(reduce + (range n))` | LINEAR since step 4: n=100000 in 0.16s, ~1.6 µs per element through the host's own IReduceInit reduce (17s and 170 µs at the end of step 4). Before: n=16000 took 161s and n=100000 did not finish in 15 minutes |
| `loop`/`recur` | ~1.7 µs per iteration, linear; a function call ~1.3 µs. `scripts/bench` has clj ratios: 23x to 514x depending on the form. Seqs are chunked, as in clj |
| memory | 168 MB after core.clj; recursion 100,000 deep works |
| Fortran library calls made through clotran | two PACKAGES, `packages/blas` and `packages/chemsol` (and `scripts/bind-fortran` binds a library from its own signatures) -- shared libraries opened at run time by the unchanged binary, `dgemm` and ChemSol's `readopt`, `dg_ld`, `solvout` and `entropy` through one shim signature; the base binary links no BLAS and no ChemSol; `examples/chemsol.cljf` reproduces the original program's output byte for byte on its three reference inputs (`scripts/chemsol-check`) |

The reduce row was the one that mattered and no scorecard saw it; step 4
below is how it was found and what it was.

## The diagnosis

One missing thing explains most of the ledger: **there is no analysis
pass.** `gce_analyze` is macroexpansion and nothing else. Consequences,
each of which has been treated as its own bug:

- names resolve at call time against `*ns*` (DEVIATIONS 3, 6, 16), so a
  closure carries a `__defining-ns__` binding in its environment to
  remember where it was written;
- every list form, on every evaluation, strips metadata, string-scans
  its head symbol three ways, runs a 24-way string cascade for special
  forms and looks up macro-ness, before doing anything;
- every local lookup is a hash-map probe up a chain of frames; every
  call allocates a frame and a map;
- intermediates live in Fortran locals, so rooting is manual, and it is
  done twice: 1,844 `vs_set`/`vs_get` calls plus `roots(:)` arrays
  threaded through 49 signatures in Eval alone. Design B promised
  rooting by construction. Values escaping into locals is why it did
  not deliver;
- there are no source positions (they existed only in the evaluator
  being deleted), so there are no frames, so there is no debugger;
- per-thread state is module globals: error state, depth, gensym and
  proxy counters, the type table, the binding stack, the value stack,
  the current namespace.

The second problem is the host boundary: five hand-synchronised Fortran
tables (`static_member`, `instance_member`, `eval_new`, `is_instance`,
`host_super`) holding 57 clj's runtime classes and 36 clj's host library names. Each
new clj member is a few hundred lines of Fortran and a rebuild.

## The work, in order

### 1. Delete the retired evaluator -- DONE

`clotran-bin`, its 17 modules (`Eval`, `LispReader`, `Values`, `RT`,
`Namespace`, `Env`, `Atom`, `Numbers`, `printer`, `readline`,
`NativeArray`, the four `Persistent*`, `rc`, `main`), the ten test
programs that drove them, `test/regression` (mal), the babashka oracle
script, the two `.clj` shims only `Eval.f90` loaded, and every mention
of them in the documents. Roughly 11,000 lines of Fortran and half of
every crosscheck. Moves no scorecard. Removes the "load-bearing
absence" trap recorded in `src/clj/clojure/PROVENANCE.md`.

Then the `GC` prefix went (DONE). With one evaluator there is nothing
to distinguish it from: `GCEval.f90` is `Eval.f90`, `GCReader` is
`LispReader`, `GCVector` is `PersistentVector`, and so on -- Clojure's
own names, as the deleted modules were called. Only the collector
itself keeps the name, because it IS the GC. The binary is
`clotran-bin` and `./clotran` at the root is the launcher: rlwrap and
core.clj, from any directory. Procedure prefixes (`gce_`,
`gcv_`, `gcl_`, ...) stay: they are short namespaces, and renaming a
few thousand call sites buys nothing until step 5 rewrites them anyway.

### 2. Decide what our test suite is, then derive it -- DONE

Three layers, each answering a different question:

- **Host tests** (`test/f/gc_*`): the heap, collections, reader,
  printer, evaluator under GC torture. Things Clojure's suite cannot
  see. Kept as the gate.
- **Runtime conformance, differential against `clj` -- DONE.**
  `scripts/oracle` runs `test/clj/oracle.clj` through `clj` and through
  clotran in one process each and compares values; `make test` runs it.
  It replaced the hand-typed expectations in `language_test.clj`, and
  14 of 477 of those turned out to be clotran's answer rather than
  Clojure's -- every one a known deviation, now marked `expect-diff`
  so the ledger goes red if a deviation quietly closes. `clj` is the
  oracle; bb never is.
- **Language tests derived from Clojure's suite -- DONE.**
  `upstream/derive-tests` computes the intersection of the public names
  of `clojure.core` (the vendored source and its siblings) and
  `cljs.core` (the pinned ClojureScript clone): 470 names, the
  language. It classifies every `deftest` in the vendored tree by the
  symbols it uses -- LANGUAGE if they all fall inside that set plus the
  special forms, the portable libs and a short exception allowlist;
  CONCURRENCY if the only outsiders are refs, agents, futures and STM
  (Clojure-only, but goal 3); HOST otherwise (a clj class, a member
  call, a constructor, a clojure.core name ClojureScript never had) --
  and writes the kept tests to `test/clj/derived/` with the source
  file and line of each. Of 578 deftests it can read, 306 are language,
  8 concurrency, 264 host; 7 files it cannot read at all (method
  values, param-tags, record literals) are all clj-shaped. A helper a
  kept test needs travels with it; a test whose helper is host goes
  with the helper; a top-level form with a head nobody defines
  (test.check's `defspec`) goes; a require of a non-portable library
  goes and so does everything it referred; a symbol nothing defines
  makes its test host, where "defines" is approximated by the
  binding positions of the form (its vector literals, `catch` names,
  `as->`), so `(vector-of :int)` and `(doc x)` are recognised as the
  clj's without a list of them. The two hand
  lists it does contain, the exception allowlist and the concurrency
  vocabulary, are printed by `--report` so they can be argued with.
  `scripts/run-clojure-tests-parallel test/clj/derived` runs it.

The scorecard is now the pass rate over the derived language suite,
with the denominator stated -- see "Where we are".

### 3. Freeze host-member work; one table, as data -- DONE

`src/f/hosttable.inc` is clj surface: 293 static rows (class,
member, builtin id or constant) and 139 instance rows, as Fortran
`parameter` data. `static_member`, `instance_member` and
`is_host_class` are three lookups over it, so the class list and the
member list can no longer disagree, and a bare class name is
canonicalised once (clj's implicit package added, the libs' short imports
mapped). The 900 lines of `case` arms are gone, along with
`math_index` and the one builtin the audit found unreachable.

The audit is `scripts/audit-host`: every `Class/member`, `(. x m)` and
`.member` the loaded Clojure mentions (src/clj, the derived suite,
the oracle, the examples). It found six members nothing mentions --
`createWithCheck` on three classes, `unchecked_divide`,
`getThreadBindingFrame`, `isUpperCase` -- and they are not rows. The
rest of the old table was reached, which is the honest finding: the
surface was already close to minimal, it was just not data.

The table is Fortran data rather than a Clojure map because the
natives it names would otherwise have to be interned by name for
host.clj to reference them -- 156 more Vars in clojure.core, or a
second namespace -- to buy nothing the parameter array does not.

Not done here: the class-versus-type-tag question (Open, below).

Amended 2026-09-21: a row is justified by the Clojure under `src/clj`
and the examples, never by a test. `scripts/audit-host` prints the rows
nothing justifies, with the blind spots its comments name; 53 rows were removed that day (NOTES, "The
table pruned to what the language asks for").
`is_instance` and `host_super` are still two hand-written hierarchies
and belong in this file as a third table once that question is
settled.

### 4. Profile the superlinear reduce -- DONE

Two causes, neither of them the ones guessed above (uncached protocol
dispatch, lazy-seq realisation). Instrumenting first was the right
call: `CLOTRAN_STATS=1` prints evaluations, allocations, collections
and marks at exit, `CLOTRAN_TRACE_MACRO=1` names every macro
expansion, and `sample` gave the call tree.

1. **The collector grew a pool only when a sweep freed NOTHING.**
   `reduce` holds the head of the range it is reducing (its own
   argument; Clojure's compiler clears that local, ours cannot yet),
   so the live set grows with n. A full-pool-only trigger then
   collected every few hundred allocations, each time marking the
   whole live set: 8000 elements, 2344 collections, 535 million
   marks. Now a pool grows when a collection leaves it more than half
   live, and the triggering pool grows until it can absorb the live
   set before filling again -- the amortised bound a tracing collector
   is supposed to have. Collections for n=8000 went 2960 -> 167.
2. **Analysis did not descend into map or set literals.** `extend`
   takes its method bodies as a MAP of fns, so every protocol method
   installed by `extend-type` or `extend-protocol` escaped
   `macroexpand_all` and re-expanded its macros on EVERY call: 3
   `let`s and an `if-let` per reduce step, 87% of the run inside
   `expand_macro`. Fixed in `mx_walk`. Evaluations per element went
   1832 -> 60, and startup 7.2s -> 4.1s, because core.clj's own
   protocol maps were paying the same tax on load.

`System/nanoTime` and `currentTimeMillis` exist now, so `time` works.

### 5. The analysis pass, executed over explicit frames -- STAGE 1 DONE

Stage 1 landed 2026-09-19: `src/f/analyze.inc` and `src/f/exec.inc`.
Every top-level form is analysed once into a node tree -- symbols
resolved to frame slots, Vars or constants; macros and syntax-quote
expanded in the writing namespace; special forms classified by an
integer kind -- and executed over frames, one raw vector of slots per
fn invocation, with flat closures that copy their captured values.
`__defining-ns__` is gone, DEVIATIONS 16 is resolved, 6 moved to
analysis time, and 32 records the one new deviation (a qualified
symbol that does not resolve is deferred to run time, for the skipped
clj libraries' sake). Measured against the step-4 numbers:

| | before | after |
|---|---|---|
| startup | 4.1s | 2.3s |
| `(reduce + (range 100000))` | 21s | 9.9s |
| `loop`/`recur`, 40000 | ~2s net | ~1s net |
| `(into [] (map inc (range 100000)))` | 35s (with the loop) | 17s |

Nothing of the old walker remains: `eval_dot` and `eval_new` take
values, and no form is re-analysed at run time. Stage 2 is what
follows.

The one big investment. `gce_analyze` resolves every symbol -- to a Var
handle, or to a (depth, slot) local -- classifies every node with an
integer kind, expands macros with the writing namespace known, strips
metadata once, and records source positions on nodes. The evaluator
walks that tree, keeping intermediates on an explicit operand stack
and locals in frame slots, never in Fortran locals across a call.

What it retires: call-time resolution and `__defining-ns__`
(DEVIATIONS 3, 6, 16), the string dispatch, env chains of maps, BOTH
rooting mechanisms (the root set becomes the operand stack, frames and
globals, by construction -- which is what Design B meant), most of the
220 `strip_meta` sites. What it provides: positions and frames for the
debugger (goal 2), a per-thread context holding the stacks and error
state (goal 3), a resolved tree that a JIT or a Fortran transpiler can
consume (goal 4; raw S-expressions cannot be transpiled), and a heap
that snapshots into an image (startup).

Staged so each step is checkable:

1. DONE -- analyser resolves and classifies; the executor consumes
   nodes over frames. The old walker is deleted: `gce_eval` is now
   "analyse if it is a form, then execute", and Eval.f90 lost 1,700
   lines. Load reads one form at a time (DEVIATIONS 1 resolved), and
   list forms carry a source position that the analyser puts on the
   node and an error reports as `file:line:col`, followed by the call
   stack: every closure invocation pushes a frame (the closure and its
   call site) that `fail` and `throw` render into the error before it
   unwinds. That is the frame array the debugger needs, before the
   protocol around it. `eval_dot` and `eval_new` take values, so
   nothing is re-analysed at run time.
2. DONE, first half -- the executor is a loop over an explicit
   continuation stack (exec.inc `run`, `kframe` in Eval.f90): a frame
   per pending node, its values in a region of the value stack, calls
   in tail position reusing the frame. `if`, `do`, `let*`/`loop*`,
   `case*`, calls, `recur`, `try`, `fn` and the vector, map and set
   literals run in the loop; the other kinds and every native that
   calls back into Clojure nest a run.
   Recursion is bounded by a frame count, not the Fortran stack
   (DEVIATIONS 7 resolved), and a suspended context is now data,
   which is what a green thread and a paused debugger frame need.
   Same speed or better: reduce over 100000 9.9s -> 6.6s, `into`
   17s -> 12.8s, loop/recur unchanged at 25 us -- and then -O2 (the
   build had none) took each by 2.7x again; `scripts/bench` has the
   clj ratios. Still to do in this
   stage: intermediates move to the operand stack; `roots(:)` leaves every
   signature; module globals move into a context type; source
   positions on nodes.
3. snapshot the heap after core.clj and start from the image. **Landed
   2026-09-28**: `build/core.image` (main.f90 image_save, `make image`)
   is the pools, the roots and every module's own state as they stand
   once core.clj and spec have loaded, written to a stream after a full
   collection and read back in place of loading them -- a handle is an
   index and a value carries no pointer, so the arrays go out as they
   are; native array buffers go typed, a regex is compiled again from
   its text, and compiled procedures and open packages are refused. A
   start is 0.2 s instead of 1.4 s and 125 MB instead of 196; the
   clojuredocs suite's 648 processes stopped paying 1.4 s each. The
   image is tied to the build (a stamp compiled into main.f90) and to
   the sizes of the files it holds; either differing, the sources load
   with a note. The baseline after loading core.clj was 152 MB; a 100000-element reduce
   no longer adds to it, because locals are cleared after their last
   read (a backwards liveness pass in analyze.inc, as Clojure's
   compiler does) and a call's argument vector is handed to the
   callee rather than kept rooted by the caller. Before those two,
   the same reduce peaked at 645 MB and an `into` at 1.16 GB.

This reverses the previous plan's "Not a bytecode VM" decision. Its
two reasons -- the env chain as a name->value map makes eval-in-frame
free, and the AST node IS the source form -- are both answered: a
per-function symbol table gives eval-in-frame, and nodes carry
positions. The goals stated above (frames, threads) both want an
explicit frame stack.

### 6. dgemm: the first real Fortran call -- DONE

`src/f/blas/` holds netlib's reference `dgemm.f`, `lsame.f` and
`xerbla.f`, verbatim (PROVENANCE.md there). `fortran/dgemm` takes two
`real8` rank-2 arrays and answers their product in a third; the three
buffers reach DGEMM as the `A(LDA,*)` it declares, by sequence
association over the contiguous registry buffer -- no copy, no
descriptor, no C. The language test builds A and B, multiplies, and
compares against the same product computed over `aget` in Clojure and
against the numbers.

What it fixed as the convention, for step 7:

- **Interop is STATIC.** Standard Fortran has no dynamic loading, so a
  routine is compiled into clotran and the product is a binary you
  link your Fortran into, like embedding Lua. The generator's output
  is `.f90` glue plus a rebuild, not a runtime loader.
- **The buffer crosses inside NativeArray.** `class(*), allocatable`
  buffers become typed by `select type` there and only there
  (`gcna_dgemm`); a binding never sees `class(*)`. One nested select
  per typed argument is the shape a generated binding will have.
- **Shapes are checked on this side.** `xerbla` STOPs the process, so
  no call may reach it with a bad argument; the builtin refuses
  mismatched ranks, kinds, inner dimensions and slices (a slice is
  strided and would be copied) before calling.
- **Whole arrays only.** The strided view `(aget m 1)` hands back is
  not what BLAS takes. A generated binding that wants a slice copies
  it explicitly and says so.

### 7. ChemSol -- the interop finish line -- DONE

`src/f/chemsol/` holds `chemsol.f90` and `push_array.f90` verbatim
(PROVENANCE.md there); `main.f90` is replaced by `examples/chemsol.cljf`.
`scripts/chemsol-check` runs it on `test1.cs`, `test2.cs` and `test3.cs`
with `vdw.par` and diffs against the original program's output: all
three match byte for byte.

The shape is the one NOTES.md asked for. `fortran/chemsol-readopt`,
`fortran/chemsol-dg-ld` and `fortran/chemsol-solvout` each take ONE
MAP whose keys are the routine's own argument names (`:iterld`,
`:n-reg1`, `:xw`, underscores as hyphens), unpack it into the twenty to
thirty positional arguments the unmodified routine declares, call it,
and answer the map with the scalars the routine wrote assoc'd back.
Arrays are clotran `real8`/`int4` arrays whose registry buffers the
routine reads and writes in place through a contiguous pointer
(`gcna_real8_ptr`), so `rpi`, `pcenter`, `vdwc6` and `iacw` come back
filled without repacking. The driver is

    (-> mol (f/chemsol-readopt vdw-par) (f/chemsol-dg-ld atoms) f/chemsol-solvout)

with everything main.f90 did around those calls -- parsing the input,
typing the atoms, the charge checks, the header -- written in Clojure.

Three things the library dictated, worth knowing for the generator:

- **A routine may do its own I/O.** `readopt` reads the tail of the
  input file (the `rp` block) from unit 45 and `vdw.par` from 44;
  `solvout` appends to `cs.arc`. The binding opens 44 and 45 around the
  call, positioned where main.f90's reads had left 45, from
  `:input-file` and `:input-skip` in the map. A generator has to be told
  which units a routine touches.
- **Fixed-size locals can be huge.** `dg_ld` declares 400 MB of them
  (`jp`, `jp2` at 10^8 `integer(2)`). The original build keeps them
  static; clotran's `-frecursive` would put them on an 8 MB stack and
  the first call died with SIGILL. `chemsol.f90` is compiled without
  that flag, and only it. A library's build flags are part of its
  binding.
- **Module state.** `ran2`'s seed lives in module variables, so one
  calculation per process is what matches the reference; a second in
  the same process continues the random sequence. Not hidden.

Also added on the way: `clotran-slurp`, a host reader for a whole file
(core.clj's `slurp` is written over `clj's io`).

### 8. Then, each now cheap because of step 5

Image for startup. Debugger over frames (the protocol below) -- DONE,
both halves: `(clotran-break)`, break-on-error and
`(clotran-last-break)` answer frames with locals by name, and the
state goes to `*clotran-break-handler*`, whose command resumes:
`:continue`, `{:continue v}`, `:step-in`, `:step-over`, `:step-out`,
`:abort`. The handler runs in a context of its own while the paused
one is parked -- the first use of stage 2's context type, and the
shape a green thread takes. The REPL is the default handler, nested.
Threads over VM contexts (the concurrency decision below) -- the
primitive and the `:green` impl are DONE: a future is a task in a
context of its own, parked when it blocks and resumed by whoever
waits; core.clj's future, promise, pmap and deref run verbatim over
it (tasks.inc, DEVIATIONS 38). `:process` is next. JIT only
when a profile still demands it, and then jank's way -- LLVM IR in
process -- rather than generated Fortran text through a compiler.

### 9. Packages -- a shared library any clotran can open

Superseded 2026-09-21. The earlier text said a package is LINKED into a
per-project `clotran-bin`, because "standard Fortran has no dynamic
loading". True of the standard, not of practice: `dlopen` and `dlsym`
are C functions, `iso_c_binding` names them, and `c_f_procpointer`
makes the symbol callable, with no C source of clotran's own. Proved on
this machine under gfortran and flang before this was written. James's
requirement: one clotran binary, pointed at compiled packages; no
`clotran-chemsol`, no `clotran-qdyn`.

**A package is one artifact.** A shared library (`.dylib`, `.so`,
`.dll`) that exports

- `clotran_manifest`: a C string of EDN naming the package and every
  routine -- its symbol, its arguments with type, intent and rank, what
  it returns. The reader that reads it is clotran's own.
- one shim per routine, `<name>_shim(argc, argv)`, `bind(C)`: argc
  C pointers, unpacked to the real routine's positional arguments. So
  clotran has exactly one procedure-pointer interface, ever, and a
  package built by any Fortran compiler is callable from any clotran.

**Calling it.** `(fortran/load-package "lib/libchemsol.dylib")` opens
the library, reads the manifest, and interns one fn per routine in the
package's namespace. A call marshals by the manifest: scalars by
pointer to a temporary, arrays by pointer into the registry buffer
(non-moving, contiguous -- the collector's design decision below is
what makes this safe), strings as character arrays with a length; the
result is the returned value, or a map of the `:out` scalars by name;
arrays are written in place. `src/f/DynLoad.f90` is the loader and the
calling convention; `B_PKGLOAD` and `B_PKGCALL` in Eval.f90 do the
marshalling; `src/clj/clotran/package.cljf` makes the fns.

**Building one.** `scripts/bind-fortran` (DONE) reads a free-form
module's signatures -- type, `intent`, rank -- and writes the shims and
the manifest; the Makefile builds the library with `-shared -fPIC`.
test/f/samplelib.f90 is a library written with no thought of clotran,
bound by the generator and called through the door in the language
test. A hand-written binding (ChemSol's, with its unit-44 and unit-45
handling) is a shim like any other. Fixed-form F77 is read too -- BLAS's
binding is generated from netlib's own dgemm.f, with an interface block
for procedures outside a module; an intent F77 cannot declare is taken as
:inout. Not read: derived types, optional and pointer dummies -- listed in
the output rather than guessed. A package manager is
then a directory of such libraries and a `deps.edn`-shaped manifest
naming them -- one with ChemSol and GAMESS, another with Qdyn -- and
`clotran-bin` never changes. BLAS and ChemSol become the first two
packages and leave the base binary; `scripts/chemsol-check` keeps
proving the seam through the door instead of the link.

**Known limits, recorded now.** A package carries its compiler's Fortran
runtime; one built with clotran's own compiler is the supported case,
and mixing runtimes in one process (two owners of unit 6) is a case to
test, not assume. A routine that calls back into clotran does not exist
yet; when one does, it enters through a context like a task. Many
Fortran libraries are not thread-safe; the manifest will say so and the
`:process` kind will serialise them.

**The JIT is the same door.** The resolved tree (step 5) compiled to
Fortran source, built into a shared library, and loaded here is the
transpiler of goal 4 and the cheapest compilation there is: seconds per
namespace, ahead of time, `clotran compile my.cljf` producing a package.
An in-process JIT (LLVM, jank's way) stays what the decision record
below says: when a profile demands it.

**What it depends on.** Nothing from threads. The image (step 5 stage 3)
is welcome but not required.

### 10. Compilation ahead of time, through the door

Recorded 2026-09-21, decided and started 2026-09-23 on
`feat/clotran-compiler`. James asked whether a JIT is even possible
here; it is, but what we are building is not one, and the section is
renamed to stop the word doing damage.

**It is ahead of time, per namespace, and you ask for it.** Clojure on
clj compiles every form to bytecode, `(+ 1 1)` at the REPL
included, because a class loads in microseconds. Invoking gfortran
costs 100 ms to 1 s, so compiling a typed form would take a thousand
times longer than interpreting it at about a microsecond a node. So:
`clotran compile my.cljf`. The REPL, `eval` and a `defn` you type stay
interpreted.

That still gets the speed, because the expensive thing is almost never
the form you typed. `(count (into [] (map inc (range 100000))))` is
705x clj on `scripts/bench`, and the five nodes of the form cost
five microseconds; all of it is inside `map`, `into` and the lazy seq
machinery, which is Clojure source in `clojure.core`. **So the first
namespace worth compiling is `clojure.core` itself**, which also takes
the 0.75 s startup down to process start.

**Two delivery shapes, and they want different answers.**

| shape | how generated code reaches the runtime |
|---|---|
| a package loaded at run time | the C ABI, any compiler, the existing door |
| a namespace linked into a binary | could `use GC`; goes through the C ABI anyway |

A statically linked binary is a build target, not a replacement for the
package system. The package system is the architecture.

**The runtime surface is `src/f/ClotranABI.f90`, and it is built.** A
Fortran module file is a private format tied to one compiler and one
version, and `make crosscheck` builds with two compilers, so generated
code cannot `use GC`. `bind(C)` and `iso_c_binding` are Fortran -- there
is no C source -- and the package door already speaks that convention.
The static case does not need it and uses it anyway, so that one
surface is exercised by every path and the generator emits one kind of
call.

**Rooting is JNI's model, for JNI's reason.** Values are not passed
across the boundary. They live in SLOTS on the shadow stack and every
entry point names a slot by index. The collector already scans the
shadow stack, so anything foreign code holds is rooted by construction
and nothing can sit in a register across an allocation -- the bug this
codebase has paid for twice. The cost is a slot write per intermediate,
which is the "root everything, stupidly" position; a value-passing fast
path needs a measurement behind it, not a preference.

**Errors report, they do not throw.** A Clojure error cannot unwind
through a foreign caller's frames. `clotran_call` answers a status and
the error is read with `clotran_error_copy`, the same discipline JNI
imposes. A binding that ignores the status keeps running with a broken
value, so a manifest has to say so.

**Milestone 1 is done.** `test/f/abi_test.f90` declares every entry
point by hand, uses no clotran module, and passes plain and under
torture: values held only in slots survive collection, a Var resolves
by namespace and name and calls, 2000 allocations collect without
losing what is kept, and a raising call reports rather than throws.
That was the one step that could have said the whole idea was wrong.

**Two decisions taken now rather than discovered later.**

*The debugger is a build flag.* The break protocol hands a handler
frames with the function, file, line, column and the locals by name,
and those come from the interpreter's continuation frames. A compiled
procedure has none, so compiled code is invisible to a break and absent
from a trace unless it is told to keep them -- and deviation 7's own
note applies, a trace that skips frames lies. James chose: compile
twice. A debug build emits frame bookkeeping, a release build does not.
It changes what every emitted procedure looks like, so it is settled
before the generator exists.

*Compiled recursion is machine-stack recursion, and that is a
regression to measure.* Deviation 7 is resolved because the executor
stopped using the Fortran stack: it is a loop over a heap continuation
stack, which is why a non-tail-recursive function reaches 100,000 deep
where clj stops near 11,000. Compile that to a Fortran procedure
calling itself and it is back on the machine stack, where the existing
native-nesting bound is 2,200 (`CLOTRAN_MAX_DEPTH`). `recur` is a loop
either way, because Clojure guarantees constant stack for it, not
because Fortran cannot recurse -- `-frecursive` is on and we already
depend on it. The number for compiled code is measured and published,
not assumed.

**Scope, set 2026-09-23.** Prebuilt third-party binaries are OUT for
now. A package manager fetches source plus a build recipe and builds on
the target, which is what Homebrew and Julia's ecosystem do, and which
is what makes other architectures work without us shipping anything.
Three things keep that door open at no cost: the C ABI on the dynamic
path, a version on every manifest from the first compiled package, and
the compiler and target recorded in it.

**The callback direction shares all of this.** A Fortran solver calling
a Clojure integrand needs the same surface plus a generated adapter
with the solver's exact declared interface -- `scripts/bind-fortran`
run backwards, since it already parses those declarations. It does not
need the compiler at all, only the speed the compiler would give the
callback.

**Loading and collisions, decided 2026-09-23.** Compiling is a
property of what a VAR HOLDS, not of a file. Compiling a namespace
installs a compiled function as each Var's value; redefining one at
the REPL puts an interpreted closure back in that one Var and leaves
its neighbours compiled. Callers go through the Var and cannot tell.
That is what the Var indirection is FOR, and it is why a caller does
not need recompiling when its callee does. Inlining a call target
would destroy it, so nothing inlines until something declares it may.

The package path is ORDERED and the first provider of a namespace
wins, like a classpath, so nobody learns a second model. Three
warnings, all of them James's call:

- two providers claim one namespace -- the warning Clojure's
  classpath lacks and everyone wishes it had; a package manager can
  probably keep it from ever firing
- source redefines a namespace that came from a compiled package,
  which is where you silently lose the compiled code you thought you
  were running
- the compiled artifact's recorded source hash no longer matches the
  file on disk, so a session and its artifact have diverged

A recompile LEAKS the old shared library, on purpose. It cannot be
closed while a compiled function object still points into it, and
closing it would crash; each compile gets a distinct name instead. A
session recompiling fifty times leaks a few megabytes, the same
bargain clj makes with class loaders.

Optimisation flags and a tree shaker for dependencies are wanted
eventually and are not now.

**Milestone 2 is done**: `(clotran-ast form)` hands back the resolved
tree as nested maps, walking the template vector a `fn` hides its
arity bodies in. **Milestone 3, the call path, is done too**: a
compiled procedure is `OBJ_COMPILED`, its pointer lives in
`CompiledFn`'s table (a `gc_value` has no pointer component, which is
what keeps a copy at 4 ns), `clotran_def_fn` installs one as a Var,
and `apply` reaches it. A hand-written Fortran procedure is called
from Clojure source, allocates, calls back through a Var, is refused
at the wrong arity, is reinstalled under the same name and the new
one is reached -- and with core.clj loaded, `fn?`, `ifn?` and `map`
all take it for what it is.

So the generator has nothing left to prove about HOW its output is
reached. Only about what it emits.

**Milestones 4 and 5 are done: the generator exists and it agrees.**
`src/clj/clotran/compiler.cljf` reads `(clotran-ast form)` and writes
Fortran: one procedure per function, calling the runtime through the C
convention, plus the one `clotran_install` the loader knows.
`scripts/compiler-check` generates, builds with gfortran, loads through
`clotran-load-compiled` and runs every case BOTH WAYS, comparing
values. On 16 cases it compiles 14, and 36 of 36 calls agree.

Three decisions the generator made that are worth keeping.

*Locals live in an interpreter frame, not in raw slots.* A frame is a
`gc_vec`: one allocation per call, indexed, already traced. It costs
more than raw slots and it buys two things that matter more right now
-- the escape hatch is one call rather than a bridge, and the debugger
sees a real frame. Raw slots for leaf procedures that never fall back
are a later optimisation with a measurement behind it.

*Anything Fortran cannot spell goes in the CONSTANT POOL.* Analysis
folds a resolved core function into the call head, so the head of
`(inc x)` is the function itself and not a lookup. A procedure cannot
write that down, nor a map, nor a Var. The pool holds the exact value
the interpreter would have used, so compiling cannot change what a form
means. Strings are pooled too, deliberately: a Fortran literal would
need its quotes doubled, its newlines turned into concatenations and
its byte length counted by hand, and each of those is a way to emit a
file that compiles into a different string.

*The pool handle is passed to `clotran_install`, not baked in.* The
file is written before the pool is registered. This also means compile
and install must happen in ONE process, because a pool holds Vars and
functions and cannot be written to a file and read back.
`compiler-check` compiles twice and throws the first Fortran away,
which works because compilation is deterministic.

**`loop` and `recur` compile, and compiled is now FASTER than
interpreted** -- but only after a measurement said it was not.

| 200,000 iterations of a summing loop | |
|---|---|
| interpreted | 385 ms |
| compiled, first working version | 625 ms |
| compiled, now | 318 ms |

The first version LOST, by a lot, and the reason is the design's own
bargain: every operation is an out-of-line C call where the
interpreter's equivalent is an inlined switch arm. Three things closed
the gap, and the third was almost all of it.

- a pooled value is already in a slot, so using it beat copying it
- a call's arguments are generated straight into the consecutive block
  rather than computed elsewhere and copied in
- **`gce_apply_slots` built its argument vector one `conj` at a time**,
  allocating a fresh vector per argument. `gcv_build` plus `gcv_put`
  makes one. A two-argument call in a loop was making twice the garbage
  the interpreter makes.

That is the shape of the remaining work, and it says plainly where the
real win is: not in emitting better statements, but in not calling the
runtime at all. `(+ i 1)` on two values the analyser can prove are
integers should be Fortran integer addition. That is the last
milestone and it is where the scientific loops live.

`recur` is a Fortran loop with a flag, which is what Clojure's
constant-stack guarantee requires in any implementation. The procedure
body is itself a loop, so a `recur` with no enclosing `loop` rebinds
the parameters. Each loop owns its flag and the outer one is restored
when an inner one ends -- `compiler-check` caught that as a difference
on a nested loop before it was, which is the entire point of having it.

**The 1.2x was a bug, not a ceiling -- and a profile found it.** A
sampled compiled loop spent 58% of its time in the collector. The
interpreter already calls numeric builtins without allocating, reusing
one scratch vector by the `scalar_builtin` rule; `gce_apply_slots` did
not, and built a fresh argument vector for every `+` and `<`. Giving it
the same rule took the collector out of the profile entirely.

| summing loop, 200,000 iterations | interpreted | compiled |
|---|---|---|
| before the fix | 385 ms | 317 ms |
| after the fix | 398 ms | 85 ms |
| after, with `-flto` (not adopted yet) | 345 ms | 67 ms |

What the profile says is left, with the collector gone: two thirds of
the time in ONE-LINE ACCESSORS -- `vs_get`, `vs_set`, `gc_slot`,
`gc_kind`, `gcv_nth` -- called out of line because they live in `GC.f90`
and their callers do not. Link-time optimisation inlines them, which is
the `-flto` row; it is not in the Makefile yet because flang has to
agree under the gate first.

The rest is the generic numeric path: `call_builtin`'s dispatch and the
tag checks in `numbers_ok`. Unboxed arithmetic removes all of it for a
value the analyser can prove is a number, and that is where the
remaining distance to clj's 2.77 ms is.

Two GC knobs were tried and did NOTHING: keeping the heap at 4x or 8x
the live set instead of 2x, and collecting at 8x live slots allocated
instead of 2x. Recorded so nobody tries them again as the answer.

**Arrays, through hints, as Clojure writes fast array code.** A
parameter hinted `^doubles`, `^longs`, `^double` or `^long` is checked
ONCE on the way in, and the procedure is VERSIONED: if every hinted
argument is what it promises, the typed body runs, with an array
indexed through a Fortran pointer to its buffer and a bounds check that
hands anything out of range to the generic call. If any argument is
not, the untyped body runs -- the code the function would get with no
hints. So a vector passed for `^doubles` answers exactly what the
interpreter answers, and compiling still cannot change what a call
means. `int`, `long` and `double` are typed casts with RT's range rules,
because `(aget a i)` inlines to `(aget a (int i))` and without them no
index was ever typed.

| 200,000-element double array, summed | |
|---|---|
| interpreted | 554 ms |
| compiled | 0.191 ms |
| warmed clj, same function | 0.192 ms |

Two things the check got wrong, both now fixed in it:

- It printed each case with `pr-str`, which DROPS metadata, so every
  `^doubles` reached the compiler stripped and the hinted cases ran
  the untyped version. The typed array path was untested and the array
  benchmark read 134 ms. Forms now keep `:tag`.
- It compared exceptions including the `at file:line` clotran appends,
  which is where an error was noticed, not what it says.

And one real bug underneath, in the array registry, not the compiler.
Growing it assigned the nodes to a bigger array, which DEEP-COPIES
every allocatable component, so every buffer moved to a new address.
A compiled loop holds a pointer into a buffer across allocations. Each
component is now handed over with `move_alloc`, which keeps the
address, and `test/f/native_array_test.f90` checks the invariant
directly -- the address before and after 200 allocations -- rather
than hoping to catch a read of freed memory, which depends on the
allocator and on the platform.

**Unboxed arithmetic landed, and it is the orders of magnitude.** The
same functions on a warmed clj, called 100 times after 200 warm-up
calls, against the compiled procedures:

| 200,000 iterations | interpreted | compiled | warmed clj |
|---|---|---|---|
| sum to a parameter `n` | 340 ms | 0.14 ms | 0.075 ms |
| sum to a literal bound, every local primitive | 318 ms | 0.075 ms | 0.075 ms |

The rules are Clojure's own. A loop or let local takes the primitive
type of its init, so `(loop [i 0] ...)` has a primitive long `i`, and
keeps it only if every `recur` feeds it the same type. An unhinted
parameter is boxed. `+`, `<`, `inc` and the rest are called directly
rather than through their Vars, which is what Clojure's `:inline` does
too. A primitive local lives in a Fortran variable, and `(+ i 1)` is an
add and an overflow test; an overflow takes the generic call, which
raises exactly what Clojure raises. A boxed operand of a comparison
gets a tag check, long and double compare unboxed, and anything else
is the generic call.

Four things the measurement taught, each fixed:

- A folded builtin in a call head is a FRESH OBJECT per analysis, so
  recognising `+` by identity found nothing and every addition stayed
  generic. The exporter now says `:builtin +`.
- gfortran folds BOTH halves of an overflow test at compile time, and
  with a literal operand the half that can never run overflowed and
  the file was refused. With a literal the sign is known, so only the
  reachable half is written.
- The unknown `n` in `(< i n)` was read from the frame and tag-checked
  on every iteration, three runtime calls a time round: 1.26 ms. A
  boxed local the loop cannot change -- a parameter, or anything bound
  outside the loop -- is now read and unboxed ONCE before it: 0.14 ms.
  That is what clj's JIT does by speculation; here it is known.
- `compiler-check` reported success when the generator threw part-way
  and silently left later cases unrun. It now fails unless every case
  is compiled or declined.

What this does NOT touch: sequence-heavy code. `(into [] (map inc
...))` spends its time in `clojure.core`'s lazy sequence machinery, and
compiling the caller changes almost nothing. That needs `clojure.core`
compiled.

**The escape hatch is wired in, and NOTHING declines for a node kind
any more.** A kind the generator does not emit has its NODE put in the
pool and run by `clotran_eval_node` in the same frame the compiled code
is using. `try`, set and map literals, destructuring and a hatched call
inside a compiled loop all answer what the interpreter answers: 64 of
64 calls agree.

That needed one change to the exporter: `(clotran-ast form)` now
carries `:node`, the node itself, beside its data. The exported map is
a copy, so without it the original was not reachable from Clojure and
the hatch had nothing to run.

It also caught its own bug. `gen-into` took the pool shortcut for every
pooled entry, so a hatched subtree was COPIED as an argument rather
than run, and `(get {:a 1} :a)` came back nil. A `:var` or a `:const`
entry is the value; a `:node` entry is a subtree. `compiler-check` said
so before it shipped.

What still DECLINES is a whole function, never a node: more than one
arity, variadic, a closure over an outer local, and a function that
names itself.

`decline-reason` is the list, so the answer is always visible. A
declined function stays interpreted and nothing else changes.

**Still to do before this is usable**: `loop`/`recur` as a Fortran loop,
which is where the interpreter-dispatch win is; a `clotran compile`
driver that does a whole namespace rather than one function; and the
escape hatch wired into the generator so a node kind it does not know
costs speed rather than a decline.

**In order, from here.**

2. ~~The exporter: a namespace's resolved tree as Clojure data.~~ Done.
3. An ABI entry that evaluates an already-analysed node in a given
   frame, which is the generator's escape hatch.
4. The generator for the straight-line subset -- constants, locals,
   `if`, `do`, `let*`, and calls through Var handles -- with every
   other node kind emitting a call back into the interpreter for that
   subtree. That escape hatch is what makes the generator correct from
   the first node kind it handles.
4. `loop` and `recur` as a real Fortran loop.
5. ~~`clotran compile`, producing a package~~ Done 2026-09-24; a linked
   binary is still to do. `clotran compile foo.cljf` writes `foo.dylib`
   (`.so`) beside the source; loading the source installs it, as RT.load
   prefers a class file beside a .clj. The constant pool cannot be
   written to a file -- Vars, folded functions, hatched subtrees -- so
   `clotran.loader` REBUILDS it by analysing each compiled form again,
   and two checks make that sound: a hash of the source (an edited file
   refuses its library) and a fingerprint of each analysed tree (a macro
   elsewhere that changed the expansion refuses it too). Installing costs
   about a second at startup, mostly loading the loader and analysing
   again; the heap image (step 5, stage 3) is what removes it.
6. `clojure.core` compiled -- the plumbing done 2026-09-24, the speed
   not yet. `make compiled-core` compiles 339 of core.clj's 529 defns
   into build/compiled/clojure/core.dylib, and every load of core.clj
   installs it: `make test` and the derived suite (2880 of 2880) pass
   with it in place. `scripts/bench` does not move, and should not be
   expected to: `map`, `reduce`, `into`, `range` and `sort` are among
   the 139 declined for more than one arity and the 49 declined as
   variadic.

   Multi-arity and variadic functions compile now (one procedure picks
   by argument count), and so do all 529 defns but one. It did NOT pay:
   `(reduce + (range 100000))` 111 -> 90 ms, `(into [] (map inc ...))`
   1852 -> 2029 ms, a non-tail recursion through inc/dec 13 -> 27 ms.
   map's work is inside a lazy-seq, which the interpreter still runs;
   reduce and into dispatch through protocols; and every compiled call
   allocates a frame and re-reads every pool entry, which costs more
   than the interpreter's own call of a small function like inc. What
   would pay, measured first: fn and lazy-seq bodies compiled (closures
   over captures), a call that allocates no frame for a leaf, pool
   entries read once per namespace rather than per call. Compiled core
   also pins tasks (DEVIATIONS 49).
   The pool and fingerprint are the HOST's (Eval.f90 compiled_pool),
   shared by compiler and loader: the first loader rebuilt them in
   Clojure and took 41 s to install core; this takes about half a
   second.
7. Unboxed arithmetic where the analyser can prove a number, which is
   where the scientific loops are.

Correctness comes free: `scripts/oracle` already runs every form
through `clj` and through clotran and compares values, so the compiled
path becomes a third leg and no expected value is ever typed by hand.
Measured against `scripts/bench` at each step, or not claimed.

**What this does not need.** LLVM, ORC, machine code, or any change to
the value representation. An in-process JIT stays what the decision
record below says: the day a profile shows node dispatch is what a real
program waits on. Nothing here forecloses it, because the input either
way is the resolved tree.

### 11. Parallelism: one shape, three stages (decided 2026-09-24)

**The shape.** clotran parallelizes one way at every scale: split the
data, compute each piece locally, combine the partial results with an
associative function. Clojure already names it -- `r/fold`, and `pmap`
followed by a `reduce` -- and it is the one shape that reaches every
level: a `do concurrent` loop (`reduce(+:s)`), threads in one process
(combine at the join), and, later, images across machines (`co_sum`,
`co_reduce`). A shared atom hammered by many workers is NOT the shape:
it is slow even in clj (contention, retries), and machines share no
memory to put it in. Atoms keep the job Clojure gave them, coordination.
Every parallel package keeps this shape: `repro/*` is fold with
order-independent combining; `coarrays` would be fold across images.

**The three stages.**

1. Baton threads -- DONE 2026-09-25. A future is a real OS thread with its
   own machine stack, so a task blocked below compiled code parks instead
   of pinning (DEVIATIONS 49 closed). 3000 futures, and 200 parked at
   once, run correctly in 2.7 s; language_test passes with compiled core. Only one thread runs clotran code at a time --
   one global lock, the baton -- so the heap stays single-threaded and
   every answer is today's. POSIX (`pthread_*`) covers macOS and Linux;
   Windows is a second file behind the same interface, or the same file
   through MinGW's winpthreads, as libgomp does -- to be proven. Proved
   2026-09-24: plain Fortran drives pthreads through iso_c_binding, one
   source, under gfortran and flang both.
2. Release the baton where no heap is touched -- PACKAGE CALLS DONE
   2026-09-25: a task calling a Fortran package parks as native, gives
   the baton to its stepper without waiting, and runs the routine on its
   own thread; eight 400x400 dgemm calls go from 186 ms one after
   another to 31 ms as eight futures (32 ms through pmap), the same
   answers. COMPILED NUMERIC CODE DONE 2026-09-25: a loop whose every
   runtime call is a statement inside a branch -- a slow path, the boxing
   of its result -- gives the baton up while it runs, each runtime call
   guarded by clotran_reacquire; the compiler also learned Math/ as
   Fortran intrinsics, without which such loops called back every time
   round. A compiled numeric loop over 2M elements in eight futures goes
   from 90 ms in turn to 12 ms. Runtime.availableProcessors answers
   the real count (2026-09-25: sysconf through Threads.f90, its constant
   the Makefile's per OS, 58 on macOS, 84 on Linux): pmap of a compiled
   numeric function over 40 items goes 20 ms to 11 ms (73 ms serial);
   pmap of dgemm stays at 75 ms, its ceiling elsewhere. Originally: around Fortran package
   calls (`dgemm`, ChemSol), in `do concurrent` loops, and in the typed
   region of compiled numeric code (unboxed locals, raw array pointers).
   A slow path -- overflow, a wrong-typed argument, a hatch -- takes the
   baton back. This is multi-core for scientific work: `(pmap simulate
   params)` over a compiled `simulate` uses every core. It is what NumPy
   does under Python's lock. It needs array buffers that never move
   (done, 5949ee1), arrays the caller keeps rooted, and each thread's
   roots visible to the collector. `Runtime.availableProcessors` must
   then answer the real count; today it answers 1, which sizes pmap.
3. A thread-safe collector: thread-local allocation, safepoints, write
   barriers, and a value compact enough for a hardware compare-and-swap
   (a `gc_value` is 32 bytes under both compilers; hardware CAS takes 16
   at most). Then any Clojure runs in parallel. A project of its own,
   named here so that it is not slipped in piece by piece.

The future semantics are the SAME at every stage: removing the baton
changes the runtime, never a program. `pmap`, `pcalls` and `pvalues` are
core.clj's own, built on `future`, so they come free at stage 1 and turn
multi-core at stage 2 with no change to anyone's code. `pmap`'s own
docstring gives the grain rule: "Only useful for computationally
intensive functions where the time of f dominates the coordination
overhead."

**`do concurrent` is emitted, never written.** The compiler emits it
only where the SHAPE of the code proves independence -- `amap` (a fresh
output array, one slot written per iteration) and `areduce` with an
exact operation -- and its body may contain no `clotran_*` runtime call,
only arithmetic on primitives and array pointers. `do concurrent` is a
promise the Fortran compiler trusts, not one it checks, so a wrong one is
a silent wrong answer. What is not proven runs serially. Compilers differ
in acting on it: flang with `-fopenmp -fdo-concurrent-to-openmp=host`
ran a test loop 3.2x faster on 10 threads; gfortran's
`-ftree-parallelize-loops` did not parallelize it at all. The same
source is the GPU door later (nvfortran `-stdpar=gpu`, flang `=device`).

**Built 2026-09-25**: `amap`, and a loop of its shape -- index from 0,
one `aset` per iteration at that index, an element expression that is
pure and does not read the result -- compiles to `do concurrent` in pure
Fortran, each iteration's temporaries in a `block`. The support module
and every generated version that does not print or write a parameter
are `pure`. Measured: a heavy element (four nested sin and cos) over 20
million doubles, 0.929 s serial to 0.190 s with flang
`-fopenmp -fdo-concurrent-to-openmp=host` on 8+2 cores, the same sum; a
light element gains only 2.0x, because the copies around the loop are
serial. `scripts/pure-check` builds every case threaded under flang and
gfortran too.

**Floating-point reductions stay explicit.** Addition of doubles is not
associative in any language: `(+ (+ 0.1 0.2) 0.3)` is
0.6000000000000001 and `(+ 0.1 (+ 0.2 0.3))` is 0.6, in clj and in both
Fortran compilers. A plain `reduce` stays serial and bit-identical to
Clojure; order-independent parallel sums are the `repro/*` package
(PACKAGES.md), asked for by name.

**Not now**: coarrays (PACKAGES.md: 348 MB and 2.3 s per clotran image;
the right tool only across machines), OpenMP directives in generated
code (they need `-fopenmp` to mean anything), native atomics for atoms
(stage 3).


### 12. Compile everything but eval; an image; standalone binaries (direction, 2026-09-24)

Where step 10 leads. Today 528 of core.clj's 529 defns compile, but the
generator emits only nine node kinds (const, local, if, do, call, var,
let, loop, recur) and hands every other subtree to the interpreter; and
only `defn` forms compile. In order:

1. The remaining node kinds -- closures (`fn` inside a function),
   `lazy-seq`, collection literals, `try`, `case`, `letfn`, `deftype`,
   `reify` and protocol dispatch -- and cheaper calls (no heap frame
   for a small function). This is what makes compiled core FASTER, not
   only compiled: map's work is in a lazy-seq, reduce's in a protocol.
   *Measured 2026-09-25, and designed.* Compiled calls are now FASTER
   than interpreted ones (a non-tail recursion 2.32 -> 0.97 ms, a loop
   calling a small fn 182 -> 19 ms); the "compiled core did not pay"
   above predates the call and collector work. With compiled core
   installed, sort 1746 -> 1372 ms and reduce 96 -> 85, but into/map
   does not move (1658 vs 1729): map's per-element loop is inside
   `(lazy-seq ...)`, which is `(new LazySeq (fn* [] ...))`
   -- a `:new` over a closure -- and the loop's `.nth` and `.add` are
   `:dot` interop nodes, all three handed to the interpreter. In order,
   each gated and measured on into/map with compiled core:
   a. `:fn` -- a compiled closure. Each inner fn is its own procedure in
      the file (fn-procedure, sharing the outer fn's pool), registered
      at install with no Var (`clotran_register_proc`); its creation
      site calls `clotran_make_closure` with the template's (outer ->
      inner) capture pairs, so the closure is an OBJ_COMPILED holding
      its captured values, inner slots and self slot. `call_compiled`
      records the fn it calls in the thread's context and the inner
      procedure's prologue copies its captures from it
      (`clotran_captures`) before anything else runs. The HOST's pool
      walk (Eval.f90 pool_walk) must treat N_FN as compiled and descend
      into its arity bodies in step, or the loader refuses the library.
      BUILT 2026-09-25: compiler-check 165 of 165 (nine closure cases),
      and with compiled core installed language_test passes and the
      derived suite is 2880 of 2880. It found one thing: a future's
      thread started its fn by bind_closure, interpreted closures only,
      and under compiled core binding-conveyor-fn's is compiled -- a
      task now applies anything else. into/map 1729 -> 1679 ms and
      reduce 85 -> 78 with compiled core: map's closure is still inside
      the `(new LazySeq ...)` that b is for.
   b. `(new LazySeq closure)` -- `clotran_make_lazy`, the
      OBJ_LAZY the interpreter builds; the forcer calls its thunk
      through `apply`, which already runs compiled fns.
      BUILT 2026-09-25, and for every class, not LazySeq alone: a
      compiled `new` puts its arguments in slots and calls
      `clotran_new`, the interpreter's own constructor path, so it makes
      what an interpreted one makes. compiler-check 183 of 183; with
      compiled core language_test passes and derived is 2880 of 2880.
      into/map 1679 -> 1493 ms, sort 1383 -> 1304. Interpreted steps per
      element of into/map 90 -> 61, allocations still 51: what is left
      is c -- the chunk loop's `.nth` and `.add`, `conj!`'s `.conj`.
   c. `:dot` -- interop calls from compiled code, through the host's
      own dispatch.
      BUILT 2026-09-25: the target and arguments into slots, then
      dot_dispatch with the node from the pool (the host's pool walk
      treats N_DOT as both an entry and a compiled subtree).
      compiler-check 193 of 193. into/map 1493 -> 1474 ms, 61 -> 53
      interpreted steps an element -- and the rest is found: `map` alone
      is 8 an element, `into` over a range 4, but REDUCING OVER A LAZY
      SEQ is 48 (`(reduce + (map inc ...))`; over a vector, 0). It is
      clojure/core/protocols.clj's internal-reduce for chunked seqs,
      which is inside `extend-protocol`: not a defn, so never compiled,
      and with no Var to install a compiled fn into. Next: compile the
      fn literals of top-level extend / extend-protocol / extend-type
      forms and put the compiled fns into the protocol's method maps at
      load -- the loader's second kind of install.
      BUILT 2026-09-26: each fn literal of a top-level extend-protocol,
      extend-type or extend is compiled as a defn is, defined under a
      hidden name in clotran.extends, and swapped into the protocol's
      method map by clotran.loader/install-extends (extend replaces a
      type's whole map, so the map standing is merged). protocols.clj
      now compiles 21 functions, core 534. Libraries of files that load
      while core.clj is still loading (core/protocols) install after
      core's own: the loader is written in the Clojure core defines.
      MEASURED, and it does not pay here: reducing over a lazy seq is 1
      interpreted step an element without it and 0 with it -- the 48 of
      the note above went with a-c -- and scripts/bench does not move.
      into/map's time is allocation and path copying (gc_vec,
      node_assoc, malloc/free, the sweep): transients ARE the persistent
      collections here (DEVIATIONS 11), so `into []` copies a path of
      the tree for every element. Real transients are what into/map, vec
      and mapv are waiting for.
   And fetching the stack once per generated procedure, passed to every
   runtime call: the thread-key lookups are ~20% of a compiled call.
   BUILT 2026-09-27: the 27 entries generated code calls take the
   stack first (`clotran_stack()` once per procedure), and a library
   records the runtime ABI it was built for (clotran.loader/abi, now
   2): one built for another is refused with a note instead of being
   called with its arguments shifted -- which is what a stale
   compiled core did to abi_test the first time.
2. The heap image (step 5, stage 3): landed 2026-09-28 for the
   interpreted core (0.2 s, 125 MB). Not yet: an image WITH compiled
   core in it -- a compiled procedure is a pointer into a library, so
   the image would have to name the libraries and reopen them in the
   same order.
3. `clotran build app.cljf -o app`: one executable -- runtime, compiled
   core, the program's compiled namespaces, the image -- with `-main`
   receiving `*command-line-args*`. Packages still load at run time.

**Compiling what is loaded, landed 2026-09-26.** Compiling had to be asked
for: `clotran compile`, or `make compiled-core` (4 min 12 s for core's 529
functions, removed by `make clean`), so in practice nobody ran compiled
code. Now `./clotran` (CLOTRAN_AUTOCOMPILE=1) builds every namespace it
loads in a separate background process, into a cache (~/.cache/clotran),
and installs from the cache when the same text loads again -- the source
hash is in the library's name, and a pointer file per hash names the
build, since a process cannot load a second library from one path. A
build that finishes during a session is installed at the next REPL
prompt (clotran.loader/poll), so a namespace being worked on -- edit,
reload, test -- runs interpreted right after the edit and compiled a
few seconds later, without a restart. Measured, a namespace with one
loop: 622 ms interpreted, 0.76 ms from the cache. And compiled core,
the benchmark forms: reduce 101 -> 48 ms, into/map 1027 -> 766, str of a
vector 312 -> 232, sort 1819 -> 1465; fib and a plain loop do not move --
they are the typed form, which stays interpreted. Files loaded while
core.clj itself loads wait for it (the loader is written in the Clojure
core defines). Tests and the gate leave CLOTRAN_AUTOCOMPILE unset;
test/clj/autocompile_test.clj builds and reinstalls one namespace
through a fresh cache.

**The calling convention allocated (found 2026-09-26).** Counting
allocations per element against clj's one or two: `(map inc (range
n))` 32, `into` over it 31, a `conj!` 10, one fn call 3 more -- every
call built its arguments as a heap vector (an object and a node), and an
interop call built one per argument and consed the target on. Laziness
and collections felt fundamentally slow because they are made of calls.
Step 1 of three (then interpreted frames reused, then 16-byte values):
a builtin that touches its arguments only by element -- 323 of 337, by
scripts/argsafe's reading of call_builtin, kept current by `make test`
-- is handed one of the thread's SPARE argument vectors, returned after
the call, on the interpreter's call path, compiled code's, and compiled
interop (`.nth`, `.conj` ...), where the target goes into the same
vector. coll_to_vector (vec and friends) builds through a transient.
Measured with compiled core, allocations per element before -> after:
map 32 -> 9, into/map 31 -> 4, conj! 10 -> 2, (inc i) in a loop 4 -> 2,
a fn call 7 -> 5, vec 13 -> 9; into/map 713 -> 202 ms, sort 1381 ->
1018. Step 2: an interpreted call's frame goes back to the thread's
spares when its body finishes (exec.inc, give_frame) and new_frame takes
one -- nothing keeps a frame after its call: closures copy what they
capture, letfn copies again, a break copies each local. A fn call 5 ->
4, map 9 -> 7 (compiled core); into/map is 47x clj on scripts/bench,
199x before step 1. Step 3: a value is 16 bytes, not 32 -- a tag, a pool
index and one 64-bit payload that holds a real's bits (GC.f90, gc_rval),
where a separate real sat beside the integer and was never used with it.
Thirty reads of the real changed; identity keeps comparing reals by value
(0.0 is -0.0, NaN is itself). Every slot, stack entry, vector element and
scan halves: peak memory on a vector of 300,000 and a map of 50,000 went
2.7 GB -> 1.3 GB, and with compiled core scripts/bench went reduce 50 ->
38 ms, loop 322 -> 220, into/map 225 -> 152 (39x clj), fib 31 -> 21.5,
sort 1050 -> 679, assoc 98 -> 67. `identical?` on equal numbers being true
was already so, and is now written down (DEVIATIONS.md 53).

**Profiled, 2026-09-27 (dtrace, `profile-997` on the pid).** What the
samples said, and what each fix bought, compiled core, scripts/bench:
- sort: `comparator_call` built its two arguments as a vector by
  `gcv_empty` + two `gcv_conj` per comparison; from two stack slots
  now. 679 -> 240 ms.
- reduce: ~20 thread-key lookups an element (29% of samples) -- each
  ABI entry, `push_frame`, `pop_frame` and `gce_apply_slots` fetched
  its own; now passed. A seqlock makes Var reads lock-free, and
  `vs_enter` no longer clears (above the top is nil already; the heap
  verifier checks it). 38 -> 10.2 ms.
- the plain loop: `recur` evaluated its arguments into a fresh vector
  every turn; into stack slots now. 220 -> 176 ms.
- startup: a third was `first` on a hash map's seq -- `seq_elem`
  built EVERY entry to return one, so walking a map, set or string was
  quadratic. `to_seq` now views a snapshot vector of them, made once.
  1.7 -> 1.27 s.
Measured as nothing, and in anyway: a compiled fn keeps its locals in
stack slots instead of a frame vector when nothing else reads the frame
(compiler.cljf, frameless) -- frame reuse had already made the frame
cheap. It can come out. What is left is structural: the interpreter reads its tree
through `gc_slot`/`gcv_nth` on heap vectors (half the loop's samples),
and a compiled call still crosses ~10 runtime entries.

**Direct slots, 2026-09-27.** Generated code reads and writes the value
stack itself: the stack is fixed and never moves (GC.f90 vstack_make;
DEVIATIONS 7), `clotran_slots` hands a procedure its address once, and
a copy, a tag or payload read, a set of a long, double, bool or nil is
Fortran on `sv(...)` instead of a runtime call. A boxed numeric op on
two longs or two doubles is done inline, overflow-guarded, falling to
`clotran_arith` otherwise; its fn is fetched from the pool only on that
slow path, and the prologue fetches only pool entries the body reads.
`vs_leave` clears through a local contiguous pointer (lldb showed a
stride reload and multiply per slot). compiler-check 249 of 249.
Measured: reduce 10.2 -> 8.5 ms, str of a vector 201 -> 158; into/map
and sort do not move -- their time is in the lazy-seq and interop
machinery, not in arithmetic.

What stays interpreted is `eval`: the REPL, `load-string`, source never
compiled. clj keeps its compiler at run time for the same
reason. `.cljc` compiles once it has `:cljf` or `:default` branches; a
library with only `:clj` and `:cljs` reads as nothing here.


### 13. As much as possible into pure Fortran: tiers, and warnings that say how to fix (decided 2026-09-24)

**Measured, 2026-09-24.** `clotran-bin` is 36.4 MB, of which the machine
code is 1.86 MB and 33.1 MB is ICU's complete data, linked whole. Linked
against ICU's empty stub data instead it is 3.07 MB and language_test
passes; Arabic letters, scripts and digits, case maps and `\w` all
behave the same. What needs data is emoji properties (ICU feature
`uemoji`, 13 KiB) and character names for `\N{...}` (`unames`, 269 KiB).
Locales, collation and legacy charsets are never reached by
clojure.core. So: ship the ~300 KB of Unicode data clojure.core needs
inside the binary, and the full ICU archive BESIDE it as an optional
package -- clj's own layout (`clj's base` holds Unicode data, standard
charsets and English; `jdk.localedata` and `jdk.charsets` are optional
modules `jlink` can drop). ICU supports it: `--with-data-packaging=archive`
and the Data Build Tool's feature filters.

A tier-A function written as the generator would emit it -- `stats/total`
-- is 1.1 KB of object code and a 35 KB program (`/usr/bin/grep` is
153 KB here).

**The tiers.** A program links only the runtime modules it reaches:

- A, pure Fortran: numbers, booleans, chars, primitive arrays, strings
  and small collections that do not outlive the function (escape
  analysis), keywords as constants, records of primitives (derived
  types), printing strings and numbers (`write`), `map`/`filter`/
  `reduce`/`range` chains FUSED into a loop (Clojure's own transducers
  say the same thing), and `def`/`defn` direct-linked -- Clojure 1.8's
  direct linking, under which clojure.core itself is compiled, excluding
  `^:dynamic` and `^:redef` (the pinned changes.md 1.1; Compiler
  `directLinkingKey`). A tier-A namespace is an ordinary Fortran module,
  usable from any Fortran program, and it is exactly the code that can
  release the baton, run in `do concurrent`, and go to a GPU.
- B, the collector and collections (and the printer, reader or regex
  module where reached): maps, vectors and seqs that are kept, shared or
  returned; protocols; atoms; exceptions.
- C, the interpreter and dynamic Vars: `eval`, `load-string`, runtime
  `require` of source, `binding`, `with-redefs`, `resolve` and call.

Most functions have no fixed tier: `map` over an array consumed by
`reduce` is A; the same `map` returned as a lazy seq is B.

**Warnings: every case, with the fix.** The compiler reports each call
site that pulls a function out of tier A, where, why, and what would
keep it in -- Rust's diagnostics are the model: a location, the span, a
note saying why, and a `help:` with the rewrite. So a programmer who
merely forgot to consume a seq is told so:

    warning[B001]: lazy seq kept, so `stats/squares` needs the collector
      --> stats.cljf:12:3
       |
    12 |   (map #(* % %) xs))
       |   ^^^^^^^^^^^^^^^^^ returned to the caller as a lazy seq
       = help: consume it here to stay pure Fortran:
               (reduce + (map #(* % %) xs))  or  (amap xs i r (* (aget xs i) (aget xs i)))

The existing `decline-reason` plumbing is where this starts.

Done 2026-09-24: `clotran compile --report` (src/clj/clotran/tiers.cljf).
Every code is defined in `clotran.tiers/codes`, beside the rules that
emit it -- a finding with an undefined code is refused -- and
`clotran explain B001` prints one, as `rustc --explain` does. A verdict
that rests on an assumption says so as a NOTE (N001: a sequence function
over a parameter is assumed to get a primitive array); a note does not
lower the tier.

**Types for tier A (decided 2026-09-24).** Pure Fortran needs a static
type for every argument, with no runtime underneath to fall back on. In
order: (1) infer from the calls in the program; (2) where there are
none -- a library function -- emit one version per plausible type
(double and long, arrays of each) under one Fortran GENERIC name, so
Fortran picks by argument type at compile time; (3) past a limit on
the versions, the report warns, with a `help:` suggesting the hint
(`^doubles a`) that settles it. No hints in the common case; a hint
exactly when the report says one would help.

Built 2026-09-25 (`clotran compile --pure`, src/clj/clotran/purefort.cljf,
checked by `scripts/pure-check` against clj under gfortran and flang, in
`make test`): numbers, booleans, strings, arrays as values and results;
loop/recur, let, if and cond; checked long arithmetic, casts, Math;
fused map/filter/remove chains into reduce, count and every?, fn
literals inlined with their captures; str and println, Fortran's way
(DEVIATIONS 50); a function answering nil is a subroutine. Types: a
hint, else what a same-file function takes where the parameter is
passed, else by use; a public function keeps every version, a PRIVATE
one only those reachable from a public one. Records of numbers are
Fortran derived types (name_t): a field read is rec%field, a
construction the structure constructor, its types checked -- a field is
its hint, else a double -- and a parameter read by a record's fields is
that record (2026-09-25). amap is a `do concurrent` loop. Several
fixed arities are one generic name, a version per arity and types,
longest first so `(f x)` can call `(f x 1)` (2026-09-25). Not yet:
variadic arities, and escape analysis for small collections -- planned:
a vector literal of numbers whose length is fixed where it is made and
which is only destructured, `nth`ed at a constant, `count`ed, or
returned, is a Fortran array of that length (`real(real64) :: v(2)`,
a function answering `[x y]` answers one); a map literal with keyword
keys and number values, read only by those keywords, is a derived type
as a record is, named from its keys. Anything that lets one escape --
`conj`, `assoc`, a call outside the file -- keeps it on the heap and
the function in tier B, with the warning saying which use did it.


### 14. Stage 3: plain Clojure on several threads at once (planned 2026-09-25)

Step 11's stage 3, laid out before any of it is built, because it is the
largest change since the evaluator and it pays nothing until its LAST
step: until the baton comes off interpreter code, every step below must
change no behaviour, and the gate proves each one.

**Measured, 2026-09-25.** A context (`eval_ctx`) holds its continuation
stack, trace frames, depth, error state, thrown value and binding stack,
and GC.f90 keeps a value stack per context -- swapped at every baton
hand-off. Everything else is shared: Eval.f90 alone has 64 saved
variables and 189 module-level allocatable arrays, the reader 32 more.
The collector's pools grow by REALLOCATION (`grow_str` and kin), which
moves every object slot, so a thread reading an object while another
grows a pool reads freed memory.

**The steps, each landing with the baton still on.**

a. *Classify the state.* Every module variable is per-thread (into
   `eval_ctx`), shared and fixed after startup (safe as it is), or shared
   and mutable (a lock, or a design change). The inventory is a file in
   the repository, checked by a script, so a new global cannot slip in
   unclassified.
b. *Per-thread state into the context.* Mechanical, large, no behaviour
   change: what is swapped at a hand-off today becomes what each thread
   simply owns.

   *How a thread finds its state* (decided 2026-09-25). Standard Fortran
   has no thread-local variables and neither compiler adds one, so a
   thread's slot is a POSIX key (`th_key` in Threads.f90;
   `TlsAlloc`/`TlsGetValue` behind the same interface on Windows).
   Measured: a `pthread_getspecific` plus an add costs 1.3 ns under
   both gfortran and flang at -O2, so a procedure fetches its context
   once on entry and reads components after that. Passing the context
   down every call was the alternative; it touches every signature
   in the evaluator for the same result.

   *The pieces, each gated on its own:*
   1. Keys in Threads.f90, and contexts that never move: `ctxs` holds a
      pointer per context, so the table grows without moving one
      (a thread keeps its context's address). Done 2026-09-25.
   2. Eval's per-thread variables (state.edn `:thread`, 21 of them;
      `has_error` alone is 184 uses in Eval.f90 and its .inc files,
      `kst`/`ksp` about 150 each) read
      through the thread's context. `gce_ctx_switch` stops copying; it
      re-points the key -- the debugger's handler is the one context
      that shares a thread with another. Measured with `scripts/bench`
      before and after: 1-2%. Done 2026-09-25.
   3. GC's value stack (`vstack`, `vs_top`) per thread, which retires
      `gc_stack_save`/`gc_stack_restore`. A lookup per `vs_get` cost 20%
      on plain loops, so `vs_*` also take the stack explicitly and the
      evaluator fetches it once per procedure: within 3%. Done 2026-09-25.
   4. The reader's error and scratch state under the reader's own key, so
      no module reaches up into Eval's; `regex_compile` answers its error
      instead of keeping it. `anon_seq`, which numbers `#(...)`
      parameters, stays one counter for every thread, as `RT.nextID` is.
      Done 2026-09-25: no per-thread module variable is left, and
      `scripts/state-inventory` now refuses one.

   Found on the way (the dgemm investigation, 2026-09-25): every hand-off
   broadcast one condition every parked thread waits on, so a hand-off
   cost grew with the number of tasks (0.17 ms a future at 10, 1.4-1.7 ms
   at 320). Each context now has its own condition and a hand-off wakes
   only the thread it names: 0.12-0.13 ms from 10 to 320. The scheduler's
   per-context arrays went into the context with it -- they grew by
   reallocation, unlocked, under threads reading them.
c. *Safepoints.* Collection and pool growth run with every mutator
   stopped at a safepoint -- an allocation, a loop back-edge in
   `run_loop`, a parked task (a parked task is at one already). The
   collector then sees every thread's stacks, as it sees every context's
   now.

   *As designed* (2026-09-25). An allocation is already a safepoint:
   any allocation can collect today, so the host already keeps every
   value live across one on its thread's value stack -- or passes it to
   the allocation itself as `roots` (gc_obj and kin take them for values
   held in Fortran locals). A thread parking at an allocation poll
   therefore pushes that call's `roots` and `slots` onto its own value
   stack first and pops them after, so the collecting thread sees them.
   A thread that
   must collect or grow a pool raises a stop request, waits until every
   other thread RUNNING HEAP CODE is parked at a poll, collects, and
   releases them. Waiting for the baton, or inside a native call (which
   touches no heap), is not running heap code. Polls: allocation entry,
   and `run_loop`'s dispatch, so a loop that allocates nothing cannot
   hold the world up. With the baton on, at most one thread runs heap
   code and the collector never waits -- inert until f, as every step
   must be. The proof comes with d: a host test (`gc_mt_test`) of
   several threads allocating at once, under torture, while collections
   stop them.
   *Built* (2026-09-25): GC.f90's heap_enter/world_stop. One heap lock
   around each allocation; an allocation that must collect or grow (a
   pool or the arena -- growth moves them) stops the world first; a
   thread counts as running between gc_mutator_enter and _leave, and
   only the main thread is registered, so while the baton is on no stop
   ever waits. The lock is re-entered freely by the thread holding it
   (a finalizer may allocate). `test/f/gc_mt_test` runs four threads
   building chains under torture, each allocation stopping the other
   three, with a new cell held ONLY in the next allocation's roots; it
   passes under both compilers, and fails when the world is not stopped
   (642-830 bad cells a thread) or when a parked thread does not publish
   its roots (38-683). The stack table and the global roots grow outside
   allocation and cannot take the heap lock (it needs the thread's own
   stack): both grow only under the baton now, and get their lock in f,
   with the `run_loop` poll and Eval's enter/leave at each hand-off.
   The lock costs within noise on `scripts/bench` (`into`: 1906 ms
   before; 1905-2132 after, three runs).
d. *Allocation.* Each thread takes a batch of free slots under a lock and
   allocates from it without one (a thread-local allocation buffer);
   pools grow only at a safepoint. *Deferred* (2026-09-25): the plain
   lock measured within noise with one thread, so batches wait for f,
   where contention can be measured. A batch must be emptied at every
   collection -- the sweep rebuilds the free lists and would hand a
   batched slot out twice.
e. *Shared Clojure state.* Namespace maps, Var roots, and the keyword and
   symbol intern tables under locks; an atom under a lock first (correct,
   slower), compare-and-swap once a value fits a machine word (a
   `gc_value` is 32 bytes; hardware takes 16 at most).
f. *The baton comes off interpreter code.* Tested by running the derived
   suite, the oracle and torture-mode GC with many threads at once, before
   anything else calls it done.

   **Landed 2026-09-26.** A future starts on a thread of its own and runs
   beside its maker; a wait is a condition-variable wait out of the
   running mutators; deadlock is found by counting; lazy seqs and delays
   run their bodies once across threads; `locking` is a per-object
   monitor. Three things the baton had been hiding had to go first:
   - **Dynamic bindings were global** (DEVIATIONS 10): `binding` wrote the
     Var, so eight futures' `with-out-str` wrote into each other's
     writers. Each thread now has its own stack of frames, as
     `Var.dvals` is a ThreadLocal, conveyed by `binding-conveyor-fn`.
   - **gfortran's static string lengths**: every call to a function
     returning `character(len=:), allocatable` keeps its result length
     in a static `slen.N`, whatever -frecursive says; `(str "k" 12)`
     came back "k 12". All 98 such functions are subroutines with an
     intent(out) argument now, and `scripts/no-static-slen` (in `make
     test`) keeps it so. flang never had them.
   - **A REPL waiting for a line** counted as a running mutator, so a
     collection another thread needed waited for the keyboard.
   **d landed 2026-09-26.** With more than one mutator, a thread takes
   free slots (256 per pool) and small arena runs (64 per size class up
   to 128 slots) under the heap lock a batch at a time and allocates from
   them without it; a batched slot stays flagged free, so the sweep skips
   it. Young lists and live counts are per thread and merged at each
   collection, the world stopped. One mutator: unchanged. Integers are
   formatted without Fortran I/O (gc_int_text): an internal write takes
   libgfortran's unit-table lock, the next wait behind the heap's.
   Measured, 8 futures of string-building work against the same work
   serially: 22 s -> 4.1-4.4 s, serially 8.7-9.3 s (about 2.1x). What
   is left is the stop-the-world collection itself -- about a third of
   thread time goes to waiting at safepoints and pauses -- which is what
   parallel marking is for. `test/clj/threads_heap.clj` runs eight
   allocating futures under CLOTRAN_GC_VERIFY=1 in `make test`; it caught
   a reused context dropping its young list.

   **Then the sweep left the pause (2026-09-26).** Measured first: of a
   young collection's pause, marking was 13 ms serial / 70 ms with eight
   threads, waiting for the safepoint 11 ms, and the SWEEP 383 / 678 ms.
   Parallel marking would have bought nearly nothing, so it was not done.
   Instead each thread sweeps its own young, lazily: a young collection
   marks, then hands every thread its young list as a PENDING list; the
   thread frees the dead in it into its own batches as it needs slots
   (pend_refill_*), before touching the shared free lists; whatever is
   left is freed at the next collection's start (finish_pending), so no
   slot is ever freed twice or handed out while pending. Finalizers of
   pending dead run there too, on the collector. One mutator: unchanged.
   Measured, the same 8 futures: 4.1 s -> 2.5 s (serially 8.8 s), young
   pauses 748 ms -> 95 ms in total. A first version refilled vectors from
   the shared lists while the thread's own dead waited, which doubled the
   collections; drawing on pending first fixed it.

**Agents and STM landed 2026-09-28** (feat/threads): an agent's
actions run in order on a thread of the agent's own, started when it
has work and gone when it has none (DEVIATIONS 29 resolved); `dosync`
is a transaction with a per-thread log and a commit, transactions
serialized under one lock -- a valid STM schedule, no retries, no
history (DEVIATIONS 10 resolved for refs). `*agent*` is bound during
an action; a send made inside an action or a transaction is held until
it ends, as Agent.nested and LockingTransaction.enqueue hold it, and
restart-agent resumes a failed agent's kept queue. Not done: a thread
pool for agents (a drain is a thread per busy agent).

**Open: a thread-timing flake in the oracle (2026-09-28).** RESOLVED 2026-09-29, step 20: a missed root in read_regex, not threads. The oracle's
script, run nine times on one binary, gave identical output eight
times and once a burst of !error from case 918 on -- reduce, into and
seq over ordinary collections, all failing from one point onward, a
shared thing corrupted once. Without the 37 cases that start threads
the script is byte-for-byte deterministic; with them, one run in nine.
The suspects are the futures that outlive their case (a future with a
1 ms deref timeout keeps summing 300000 numbers beside the next
cases; pmap over an infinite range) and a race between that thread's
allocation and a collection: the multi-threaded collector's domain
(14c/14d), not a rooting gap the verifier or CLOTRAN_GC_EVERY finds
(neither did, nor did 25 repetitions of those cases under both). It
predates the image; the image only made the oracle fast enough to run
nine times. A red gate whose one difference is a burst of !error after
a thread case is this, and is rerun. Next: a stress run of the thread
cases alone with the verifier, and the collector's stop-the-world
handshake read against a thread that is mid-allocation.

**Not in this step**: a concurrent collector (the world stops for each
collection), and a compacting one (objects never move, as now).

**Open: rare huge slowdowns, not reproduced** (2026-09-25). Twice a run
took hundreds of times its usual time and never did again: one
`scripts/bench` run of `(count (sort (map #(mod (* % 7919) 10007) (range
50000))))` took 931 s (usually about 2.2 s; re-run at once, 2182 ms, and
smaller sizes scale linearly), and one run of the dgemm investigation
took about 17 minutes instead of 28 s with some 360 tasks piled up in
dgemm or `native_end`. Both under heavy machine load (average 10-16).
No cause is known and none is claimed. Next time: `sample` the process
while it is slow, and CLOTRAN_STATS at exit.

**Open decision: how long the world stops** (raised 2026-09-25). A stop
is the correctness baseline; what hurts is its LENGTH -- a full mark of
the whole heap, about 14 ms at 180k live objects, growing with it. The
options, cheapest first: (1) generational -- most collections scan only
the young, so short pauses, and probably faster single-threaded code
too; (2) parallel marking -- the stopped threads mark instead of idling;
(3) per-thread young heaps, as OCaml 5 has -- each thread collects its
own young without stopping anyone, and only shared objects go to a
common heap (it suits Clojure, whose shared data is immutable, at the
cost of a write barrier on every store of a young object into shared
data); (4) concurrent marking -- near-zero pauses, write barriers
everywhere, the hardest. Leaning (1) then (2), with (3) considered once
pauses can be MEASURED with the baton off (f). Claims about other
runtimes here are from memory: read their sources before choosing.

Measured 2026-09-26 (CLOTRAN_STATS "pauses"): two or three FULL
collections a run, 10-26 ms each; the collector's real cost is the
young collections, about 2 ms each and 7-15% of runtime, which marking
in parallel would not shorten. So (2) waits until the baton is off
(14f), when one pause stops every thread -- James's order: threads,
then parallel marking.

Decided 2026-09-25: (1), then (2), maybe (3) -- without letting it pull
the compilation plan off course. (1) was chosen first on a profile: the
collector was 20% of `into`/`map` and 40% of a compiled loop calling a
small function (a dead frame per call, and every collection re-marked
the ~150k objects core.clj leaves live).

(1) BUILT 2026-09-25, non-moving, by sticky mark bits (GC.f90,
"generations"): survivors stay marked and marked is old; a young
collection marks from the roots and the remembered set, stops at the
old, and sweeps only the young lists; the barrier is in the only two
setters that store into an existing object. Growth now reads live
counts (a young sweep frees little and must not grow a pool for it),
and growth copies the mark bits, which it used to reset. Explicit
`gc_collect` stays full. CLOTRAN_GC_FULL=1 turns it off;
CLOTRAN_GC_VERIFY=1 checks the heap after every young collection --
five workloads ran clean under it. gc_test 19 fails without the
barrier. `scripts/bench`: reduce 114 -> 96 ms, loop 319 -> 286,
into/map 1884 -> 1658, sort 2182 -> 1746, assoc 138 -> 96, str 301 ->
~272; fib unchanged; a compiled loop calling a small fn 30.7 -> 20.1.

### 15. Binary data (noted 2026-09-26, James: "binary analysis is key to scientific software")

Binary manipulation works as it does in Clojure, each item checked against
clj in `test/clj/oracle.clj`. The arrays and types LANDED 2026-09-27
(DEVIATIONS 45 resolved); the bit operations were already there.

**Arrays and types.**
- `byte-array`, `short-array` and `char-array` with their own classes
  `[B`, `[S` and `[C` -- closing what is left of DEVIATIONS 45, whose
  visible symptom is `(bytes? (byte-array [1 0]))`: `true` in clj,
  `false` here.
- `bytes?`, `aget`/`aset`, `alength` and `aclone` on them.
- Clojure's signed semantics: a byte is -128..127 and `(byte 200)`
  throws; `unchecked-byte`, `unchecked-short` and `unchecked-char` wrap.

**Bit operations on longs (64-bit).**
- `bit-and`, `bit-or`, `bit-xor`, `bit-not`, `bit-and-not`;
- `bit-shift-left`, `bit-shift-right`, `unsigned-bit-shift-right`;
- (the rest of the list as James extends it: bit-set, bit-clear,
  bit-flip, bit-test, and reading/writing raw bytes from files belong
  here too, each against clj).

Order: after threads (14e/f) and parallel marking, unless moved up.

### 16. Lazy walks in constant space (found 2026-09-27)

Running the clojuredocs suite made the machine unusable: not CPU --
one clotran is 1.2 s and 190 MB at startup -- but memory. Walking a
lazy seq of 10^6 elements took 780 MB (`last`, `dorun`), 2.4 GB
(`nth` over `iterate`) and 3.1 GB (`bounded-count` over a range) where
clj stays at its baseline; the suite's 10^8-element examples then
swapped. Measured with `CLOTRAN_STATS=1`, `CLOTRAN_GC_FULL=1` and the
census `CLOTRAN_STATS=2` (GC.f90 `census`, what is live by kind at a
full collection). Three separate causes, in the order they were found:

1. **Generational nepotism.** A young collection promotes the cell
   being walked; that cell dies at once but, being old, is not swept
   until a full collection, and its `next` keeps every later cell
   alive. A full collection happens only when the promoted count
   exceeds the old generation (~4×10^5 objects after core.clj), so up
   to that many dead cells accumulate. With every collection full,
   `(dorun (range 10^6))` is 194 MB -- the baseline -- at no time
   cost. The fix is a survival-rate trigger: a young collection that
   kept most of what was allocated since the last one asks for a full
   collection next. Aging (survive two young collections before
   promotion) is the upgrade path if that trigger costs too much on a
   program that legitimately builds a large live heap.
2. **A builtin holds its arguments for the walk.** `nth` and `count`
   walk with the args vector rooted on the value stack, so the head is
   reachable for the whole walk; HotSpot's frames have precise
   liveness and drop it. Retention only, measured under full GC: `nth`
   2.8 GB, `count` of a mapped seq 780 MB; `last`, `dorun` and
   `reduce` do not retain. The fix: the walk roots its cursor, not the
   arguments.
3. **`count` of a range realises it.** `(count (range 10^6))` is 2.7 s
   here and 0.02 ms in clj (LongRange.count is arithmetic). The
   pending range cell holds `[lo hi step]`; count is computable.

**Landed 2026-09-27**, each checked under `CLOTRAN_GC_VERIFY=1`:

| walk of 10^6 elements | before | after |
|---|---|---|
| `(last (range n))`, `(dorun (range n))` | 780 MB | 196 MB (the baseline) |
| `(nth (iterate inc 0) n)` | 2.4 GB | 199 MB |
| `(count (range n))`, `(bounded-count 10 (range n))` | 3.1 GB, 2.7 s | 194 MB, 1.2 s |
| `(count (map inc (range n)))` | 780 MB | 197 MB |

1. *Aging* (GC.f90): a young survivor stays young -- unmarked, on the
   aged list, skipped by the pending sweeps -- and is old only after a
   second survival; a promoted object that points at an aged one is
   remembered, and `forget_young` keeps the remembered old objects that
   still point at an aged one. The survival-rate trigger tried first
   did not fire: the retained chain was only 3 of the 12 allocations an
   element makes.
2. The head let go on every path a builtin's argument takes: `apply`
   hands the vector over as it does for a closure; `drop_arg0` takes
   the first argument out of the vector in place (N_CALL's spare vector
   and N_DOT keep the vector itself); and the executor clears its
   last-value slot `vbase + 1` when it invokes a builtin -- the last
   argument evaluated was the seq, and that slot rooted it for the
   whole call, which is why `nth` (last argument: the index) was fine
   and `count` was not.
3. `sq_count` is one loop; it recursed once per chunk cell, and the
   Fortran frames were the chain.
4. A pending range cell counts arithmetically (`range_count`).
5. An `iterate` cell keeps `f` and `x` in its slots, not a `[f x]`
   vector, and a realised cell lets its thunk go, as `LazySeq.sval`
   nulls its fn.

Still to do: a vector of one or two elements is given a 32-slot root
run (512 bytes, `gcv_build` and `gcv_conj`), and a walk makes ~12
allocations an element; both are size and speed, not retention, and
touch PersistentVector.f90.

### 17. What a node costs (found 2026-09-28)

`(apply + (take 1000000 (range)))`: 15.2 s here, 82 ms on a warmed
clj. Measured to the piece, one million times each:

| form | clotran | evaluator steps | allocations | clj, warm |
|---|---|---|---|---|
| an empty `dotimes` iteration | 0.66 us | 11 | 0 | 0.001 us |
| `(f i)`, f the identity | 1.0 us | 15 | 0 | 0.005 us |
| `(seq (lazy-seq (list i)))` | 2.6 us | 22 | 7 | 0.05 us |
| one element of `(take n (range))` | 8.9 us | 71 | 11 | 0.08 us |

The yardstick that says this is design and not "an interpreter's
number": CPython's empty loop iteration is about 20 ns. Ours is 660
ns -- 30x an interpreter, before clj is in the picture. A step is
60 ns, and the profile of the empty loop says what it buys: the
dispatch and node decoding (29%); reading the node's fields and
children through out-of-line accessors, the children being a
persistent VECTOR so each read is a trie walk (22%); pushing and
popping a seven-slot continuation frame for every node, leaves
included (18%); a thread-local lookup of the context on each push and
pop (10%). Nothing is silly on its own; the design pays all of them
per node.

What moved, and by how much:

- `inc'`, `+'`, `-'`, `*'` went through big-integer TEXT on every
  call (a decimal string added to and parsed back); `(range)` is
  `(iterate inc' 0)`, so every element paid 0.8 us. Fixed: the big
  path only on overflow. 15.2 s -> 12.4 s.
- `-O3` (the accessors inlined): the empty loop 1959 -> 1617 ms, a lazy
  take 2330 -> 1909, a call 1052 -> 813, about 20%.
- the run loop passing its context to k_push/k_tail/k_finish instead
  of a thread-local lookup each time: 3%.

- core's one-line wrappers -- `first`, `rest`, `next`, `seq`, `cons`
  are `(fn [coll] (. RT (first coll)))` -- ran a whole
  interpreted call (470 ns) around an 80 ns builtin. Analysis now
  marks an arity whose body is exactly a builtin applied to its own
  parameters, and a call with that arity calls the builtin, the
  wrapper's call-stack entry pushed around it as clj's trace has
  it. clojure.core fns only, and not while a step is pending, so a
  user's fn keeps its whole frame and stepping stops in core's.
  Compiled `(first c)` 570 -> 120 ns.
- `lazy-seq` expands to `(new LazySeq (fn* [] ...))`,
  which took the generic `new` path (680 ns); it is the lazy node now.
- `apply` HELD THE SEQ. core's `apply` is `(. f (applyTo s))`, and the
  dot call's frame kept its argument vector -- the head of s -- for
  the whole call, so every cell walked stayed live: 452 MB at 10^6
  elements, 129 MB now, the same as `reduce`. Found by watching which
  stack slot received a vector holding a lazy cell; per-root reach
  counts were no help, every root reaching core's shared structure.

`(apply + (take 1000000 (range)))`: 15.2 s -> 6.6 s, 452 -> 129 MB.
Still about 80x clj, and the per-element anatomy says where:
forcing a lazy cell nests a whole `run` (1.2-1.9 us), `iterate` builds
an argument vector per step, and `reduce`'s protocol dispatch is 2.7
us. Those are the executor's shape, below.

What is left is the shape of the executor: an AST walked with a frame
per node. The two roads, not exclusive:

1. **A flat instruction form per function body.** Analysis emits a
   linear code vector with an operand stack and register locals; a
   node is one dispatch, no frame, its operands by direct index; the
   continuation stack stays for calls and suspension (a paused context
   is still data, the debugger and green threads keep what they have).
   This is stage 2 of step 5 made concrete ("intermediates move to the
   operand stack"). Expected: a step from 60 ns toward 10-15, so 3-5x
   on everything interpreted -- the REPL, macro expansion, spec, every
   library that the compiler cannot take. Weeks: it replaces exec.inc's
   node loop and analyze.inc's output.
2. **The compiler emitting closures and `lazy-seq`** (step 12). The
   seq library is nothing but those, so today `take`, `iterate`, `map`
   never compile; with them, compiled core runs the seq library as
   Fortran procedures. The small-fn loop that compiles today is 10x
   its interpreted self. Days to weeks.

Neither reaches 82 ms: that is compiled code with escape analysis.
Both together are the road the white paper names.

### 18. A flat instruction form for fn bodies (started 2026-09-28)

Step 17's first road, taken. What it means:

Today a fn body is a TREE of nodes, and running it is a walk: every
node -- a constant, a local, an `if` -- gets a seven-slot continuation
frame pushed, its children fetched out of a persistent vector, and the
frame popped when it answers. `(< i n)` is four frames. That is where
the 60 ns a step goes, and a loop turn is eleven steps.

The flat form is the same fn as a LIST of instructions over numbered
registers, made once when the fn is analysed:

    (loop [i 0] (if (< i n) (recur (inc i)) i))

    1  CONST  r0 <- 0
    2  CALL   r2 <- < r0 r1      ; builtin, operands by register
    3  JMPF   r2 -> 6
    4  CALL   r3 <- inc r0
    5  RECUR  r0 <- r3, goto 2
    6  RET    r0

One dispatch per instruction, operands read by index, no frame per
node. The registers are the fn's frame vector itself -- its locals,
plus temporaries above them -- so closures, captures, locals clearing,
the debugger's view of locals and the collector's rooting all see what
they see today. A CALL to another interpreted fn still pushes one
continuation frame, for the callee, and the caller waits in it with
its instruction counter: so a suspended context is still data, a
future still yields, a break still shows every fn on the stack.

Measured before building (a standalone gfortran -O3 program, the loop
above over clotran's gc_value, 10^8 turns): 6.8 ns a turn with `<` and
`inc` inline, 9.3 ns with both as general builtin calls. Today's
`dotimes` turn is 530 ns. The real thing adds rooting, error checks and
safepoints; 15-25 ns is the expectation, 20x and more on interpreted
loops.

Stages, each gated and each leaving the tree walker able to run
everything (`CLOTRAN_FLAT=0` runs trees only, and the gate compares):

1. Compile an arity when every node in it is one of: const, local,
   var, if, do, let, loop, recur, call, fn, lazy-seq, vector/map/set
   literals, throw -- or a node the tree itself runs nested (def,
   set!, letfn, new ...), run through the tree as one instruction. An
   arity with anything else -- try, case, host `.` calls -- stays a
   tree. The arity keeps its tree (the AOT compiler and the analysis
   passes read it); the code sits beside it.
2. try/catch/finally, case, `.` calls, so nearly every arity compiles.
3. Top-level forms too (a `dotimes` typed at the REPL is a top form).
4. Forcing a lazy seq inside the loop, not in a nested run.
5. The AOT compiler reads the flat form instead of the tree.

**Stage 1 landed (2026-09-28).** `flat.inc`: the compiler (`fc`, per
arity, run from analyze_fn after locals clearing) and the executor
(`flat_run`, the run loop's N_FLAT case). 2727 of the 3434 arities
analysed while core loads compile (79%); the rest are held back by a
host `.` call (641), `try` (47), `case` (11), and a nested node holding
a `recur` (8) -- so stage 2 is mostly `.`. The gate runs
language_test a second time with `CLOTRAN_FLAT=0` (check-tree), and
the derived suite gives 2880 of 2880 both ways, identical per
namespace (26.0 s flat, 29.3 s trees, 4 jobs).

| | trees | flat |
|---|---|---|
| a counting `loop`, 10^6 turns, in a fn | 503 ms | 195 ms |
| `(fib 25)` | 209 ms | 120 ms |

195 ns a turn is not the 15-25 the standalone program promised: a
loop turn is six instructions, and each `<` or `inc` is a CALL that
resolves its head, looks for a wrapper and fills a scratch vector.
Measuring that is the next thing, before stage 2.

**Then the per-instruction cost (2026-09-28).** A sample of the loop
put the time in resolving each call's head and filling a vector for
`<` and `inc`, and in checked frame accessors with the write barrier.
Now a call whose head is a builtin constant compiles to `F_CALLB`,
two machine integers go through `+ - * < > <= >= = inc dec zero? pos?
neg?` inline (anything else, and every overflow, to the builtin, which
throws as before), a one- or two-argument builtin reads a local in
place when nothing after it in the call could clear it, and registers
go through unchecked accessors (`gc_reg`, `gc_reg_set`: the barrier
only for a reference).

| | trees | flat, stage 1 | now |
|---|---|---|---|
| counting `loop` in a fn, 10^6 turns | 514 ms | 195 ms | 36 ms |
| `(fib 25)` | 209 ms | 120 ms | 59 ms |
| `reduce + take`, 10^5 | 717 ms | | 468 ms |
| `(apply + (take 10^6 (range)))` | 6.6 s | | 5.5 s |

36 ns a turn against the standalone program's 7-9. The seq library
moves least: its arities mostly hold a `.` call (stage 2) and a top
form typed at the REPL is still a tree (stage 3).

**Stage 2, host calls (2026-09-28).** `.` calls compile (`F_DOT`,
dispatched as the tree's N_DOT: a value, a closure to enter in a frame
of its own, or a park that dispatches again with the same target and
arguments). 3329 of 3434 arities now (97%); `try` (69), a nested node
holding a `recur` (22) and `case` (14) are what is left. The original
expression, `(apply + (take 10^6 (range)))`: 15.2 s at the start of
the day, 4.55 s now. What a lazy element still costs is the forcing:
`gce_force` runs the thunk in a nested run from Fortran (stage 4).

**Stage 3, top-level forms (2026-09-28).** analyze_top compiles the
form's body too (`flat_compile_body`), kept in the N_TOP node's p2, so
a loop typed at the REPL runs as one in a fn does; `unchecked-inc` and
`unchecked-dec` joined the inline integers (dotimes counts with them).
Per 10^6, at the top level: an empty `dotimes` 549 -> 44 ms, `(+ i 1)`
in one 798 -> 60 ms, `(f s)` with f bound to `first` 855 -> 253 ms.

**Stage 4 begun: what a call and a lazy element cost (2026-09-29).**
Measured first: a plain call was 215 ns, a core wrapper call (`first`)
209, an allocation about 100, and one element of `(dorun (take n
(range)))` 2.3 us with 9 allocations and two thunks forced through a
nested run. Taken so far:
- a CALL TABLE per fn template (flat.inc `call_table`, the template's
  eighth element): frame size, self slot, captures and, per fixed
  arity, first slot, bodies and wrapper builtin, as one raw vector --
  the flat call and `bind_closure` read it instead of walking the
  persistent template (18% of a loop of calls);
- flat_run is a TRAMPOLINE over flat frames: a call into a flat body
  and a return to a flat caller go on in place, not through run_loop;
- `first`, `rest`, `next`, `seq` answered inline where the answer is a
  slot already there (nil, a list, a realised cell) -- no argument
  vector, no dispatch, and no call-stack entry, since nothing can fail;
- `[roots, x]` root lists where x is already on the stack were heap
  temporaries grown element by element (malloc, realloc, free on every
  call): gone from the call path and iterate;
- iterate calls f through the value stack (no argument vector) and a
  thunk gets a shared empty argument vector: 9 -> 6 allocations an
  element.

| | before | now |
|---|---|---|
| a fn call in a loop | 215 ns | 159 ns |
| `(fib 25)` | 59 ms | 46 ms |
| `dorun take`, 10^5 | 242 ms | 155 ms |
| `(apply + (take 10^6 (range)))` | 4.55 s | 3.4 s |

Tried and reverted: allocating from per-thread batches with one thread
(the heap lock is not where an allocation's 100 ns goes).

**Forcing in the loop (2026-09-29).** When a flat body's `first`,
`rest`, `next` or `seq` meets a pending cell whose thunk is an
interpreted fn, the cell is claimed as gce_force claims it and the
thunk runs as a callee in the loop (`flat_force`), the body waiting
AT that instruction; on the answer the cell is settled (`force_settle`,
force_run's second half, now shared) and the instruction runs again,
finding it realised. A thunk that throws is released by k_unwind
(pending again, waiters woken). `dorun take` 155 -> 135 ms per 10^5,
a hand-written lazy loop 213 -> 174.

**Host calls (2026-09-29).** `(apply + s)` walks s in core's reduce1,
whose `chunked-seq?` is `instance?`, whose body is `(. c (isInstance
x))`: 1.3 us a call, half of each element. Three things, largest
first: dot_dispatch prepended the target with `cons_vec`, built by
conj -- every element a copied 32-slot node (now sized once and filled);
a flat `.` call on an evaluated target with a native member goes to
the builtin straight from its registers, as dispatch would (nil, a
deftype instance and a Var still dispatch); and is_instance answers
IChunkedSeq, ISeq and Reduced from the value's kind before building
any string. `instance?` 1296 -> 281 ns, reduce1 2.97 -> 1.89 us an
element, `(apply + (take 10^6 (range)))` 3.1 -> 1.9 s (15.2 s at the
start of 2026-09-28).

**Stage 2 done: try and case (2026-09-29).** `case*` compiles to the
test, `case_branch` (the tree's own table walk) and a jump to the
branch's label (`F_CASE`). `try` runs in the frame: `F_TRY` saves the
frame's handler (its kst%mode, otherwise unused by a flat frame) and
the call-stack depth and installs the handler's label; k_unwind, on
reaching a flat frame with a handler, lands it there (`flat_catch`:
exception and message in the try's registers, outer handler and depth
restored, anything waited on let go, error cleared) rather than popping
it; catches are tried in order (`F_CATCH`, catch_matches as the tree);
with a finally the catches run under a second handler, so a catch that
throws still runs it; an exception nothing takes runs the finally and
goes on with its message and trace (`F_RETHROW`). A recur that would
jump out of a try leaves that arity a tree (Clojure refuses it anyway).
5181 of 5203 arities (99.6%); the rest hold a node the tree runs
nested with a recur inside. `dorun (map inc (range 10^5))` 279 -> 121
ms, now that map's chunked branch compiles.


**Steps 18 and 19, continued (2026-09-29).** Every arity core loads now
compiles flat: a nested tree node beside a recur no longer refuses an
arity, only a recur inside one (node_has_recur). Measured against the
start of the day, per call or element:

| | before | after |
|---|---|---|
| `(:k m)`, a small map | 379 ns | 192 ns |
| a native reduce calling a fn | 736 ns | 143 ns |
| `(assoc m k v)` into 5 x 10^4 entries | 2.3 us | 1.35 us |
| `(assoc! t k v)`, transient map | 2.7 us | 1.3 us |
| `sort`, per element | 2.3 us | 1.2 us |
| `(R. a b)`, a record | 1.7 us | 640 ns |
| `(assoc r :a v)`, a record | 4.7 us | 800 ns |
| `frequencies`, per element | 3.3 us | 2.4 us |

How: a keyword call from the register; gce_apply_slots entering a fn
through its call table with no argument vector (native reduce, sort,
swap! all call back that way); the hash map and vector rooting on the
value stack instead of growing heap root arrays per level; a `new`
compiled flat that keeps the type it resolved; record field assoc
and lookup built directly, as emit-defrecord's methods would.

Found on the way and fixed (c14b20d): records were hashed and compared
by identity inside maps and sets -- a set of twenty equal records had
twenty members. DEVIATIONS 60 keeps the case not fixed: a deftype's own
equals and hasheq.

**Stage 5 (the AOT compiler reading the flat form): measured, not
started.** Compiled code against flat, 2026-09-29:

| | flat | compiled |
|---|---|---|
| a loop calling a small fn, 10^6 | 221 ms | 34 ms |
| non-tail recursion, 2000 deep x 50 | 47 ms | 8 ms |
| `(fib 25)` | 48 ms | 14 ms |
| `(reduce + (map inc (range 10^5)))` | 101 ms | 106 ms |

Compiling still pays 3-6x on scalar code and nothing on seq code, whose
time is the runtime's (allocation, forcing). Stage 5 would widen WHAT
compiles -- closures, lazy-seq, try, case, protocol calls -- and those
are the constructs whose cost is in the runtime, so it buys little
speed for a rewrite of the compiler's front end (1762 lines, plus the
pure-Fortran tier's 1148). Deferred until a measurement says the
interpreted remainder of compiled code is what is slow. Compiled
recursion stops near 2,200 deep (DEVIATIONS 7), the interpreter's at
100,000.

### 19. Slow spots, surveyed against clj (2026-09-29)

Thirty everyday forms timed on a warmed clj (best of 5) and on
clotran (best of 2), ranked by the ratio. The worst, before and after
the fixes of this day:

| form | before | after | what it was |
|---|---|---|---|
| records: `(:a (->R i 1))` | 506x | 176x | keyword lookup went through the record's valAt as a nested call; the hidden fields were conj'd |
| protocol call | 377x | 110x | `fnFor` always nil: every call re-found the method (DEVIATIONS 13, resolved) |
| `clojure.string/join` | 350x | 81x | StringBuilder append copied the whole text: O(n^2) |
| `re-seq` over a long subject | 323x | 35x | offsets counted, and the subject scanned, from its start at every match |
| `pr-str` of a vector | 235x | 63x | the same StringBuilder |
| `filterv even?` | 215x | 154x | `integer?`'s instance? checks built strings |

Also found on the way: `instance?` with a class literal is now the
builtin (clj's InstanceOfExpr), and regex `replace` and `split`
were quadratic too. Every row is now linear in its input; what is left
is the constant factor, spread thin: records still cost 1.6 us to make
(eval_new looks the type up by name), a sort comparison is a Clojure
call from Fortran (a nested run, about 0.5 us), and the flat executor
itself. The median ratio of the thirty is about 50x; `fib` is 8x.

### 20. The thread flake (opened 2026-09-28, a step 2026-09-29)

Step 14's open note: the oracle's script, run nine times on one binary,
once gave a burst of !error from case 918 on -- reduce, into and seq
over ordinary collections failing from one point onward. Deterministic
without the 37 thread cases. The suspects: futures that outlive their
case (a 1 ms timed deref leaves a sum of 300000 numbers running beside
the next cases; pmap over an infinite range), allocating while the
next cases run and collections happen.

What 2026-09-29 changed that bears on it: the agent error race (an
error written onto the agent before its handler ran) is fixed, the
allocator now takes per-call temporaries off the stack
(`-fstack-arrays`), and lazy cells are forced in the flat loop under
gce_force's claim protocol. None of that is known to be the cause.

The order: (1) make it reproduce on demand -- the thread cases alone,
in a loop, under CLOTRAN_GC_VERIFY=1 and CLOTRAN_GC_EVERY, and the
full oracle N times with the failing run's output kept; (2) find the
shared thing corrupted, with a watchpoint or the verifier, not a
theory; (3) fix it at the root; (4) a check in the gate that runs the
thread cases enough times to catch it, bounded in time. Done when the
oracle is byte-identical across a run of repetitions large enough to
have caught the one-in-nine.

**Resolved 2026-09-29: not threads -- a missed root.** Reproduced on
the 2026-09-28 binary: its own oracle script, run under eight CPU
burners, failed 1 run in 87, one case answering !error:
`(with-out-str (clojure.pprint/pprint ...))`. No thread was running
then (no future, pmap or send comes earlier), so the variable was not
scheduling but WHERE COLLECTIONS FELL: identity hashes differ run to
run (the heap's layout moves with shuffles, random uuids and times in
earlier cases), and with it which allocation a collection lands on.
CLOTRAN_GC_EVERY=1 made it deterministic -- clojure.pprint would not
load ("Unable to resolve symbol: param-pattern") -- and the smallest
case was `(def p #"a")`: a form holding a regex literal read as
nothing. `read_regex` made the regex object with only its own text as
a root, not the caller's, so a collection there freed the form being
read around the literal and later allocations reused it. One argument
fixed it (4690cc3).

The same shape was elsewhere: 71 allocations in 20 procedures that are
given `roots` and did not pass them on (sq_rest, deep_equal,
coll_to_vector, mf_lookup, namespace creation, the #tag resolver ...),
all fixed (a832d69). `scripts/root-check` finds the shape and runs in
check-static.

Kept caught by `check-oracle-gc` (ORACLE_GC=97 scripts/oracle): the
whole oracle script through clotran as it is and collecting every 97
allocations, the answers compared -- 55 s, in the gfortran half only.
The old binary differs on 50 lines under it, among them a silent wrong
answer (a regex case answering `()` for "aXc"); with read_regex's bug
put back, today's differs on one. Today's binary is identical across
collection intervals 13 to 509.

### 21. Sockets, and a REPL into a running process

Scenario B: a Fortran solver with clotran linked in (`examples/embed`),
driven from a REPL while it runs -- inspect the grid, change the
strategy, go on. Goal 2 wants the same thing for its debugger: a break
in a running program answered from outside it.

The language already has this as source: `clojure.core.server`
(vendored) is Clojure's socket REPL. It reaches for `clj's networking library`'s
ServerSocket, Socket, InetAddress and SocketException, `clj's io`
readers and writers over a socket's streams, `Thread.` with a name, and
a ReentrantLock.

**Decided 2026-09-29: clotran's own server, not `server.clj`.** clotran
is its own host -- Fortran and C -- and does not emulate clj; a clj
name appears only where vendored Clojure literally writes it, as a thin
mapping onto a clotran type. `server.clj` would need a pile of
`clj's networking library`/clj's collection library classes emulated, so it stays vendored
and unloaded, and the step is instead, in order:

a. *Character streams* (done 2026-09-29): `clotran.io`'s readers, with
   `read` over a stream taking one form's characters. core.clj's
   `with-in-str`, `read-line`, `read`, `read+string` and `line-seq` work
   on them; DEVIATIONS 65.
b. *Sockets* (done 2026-09-29): a C shim (POSIX and Winsock behind one small interface --
   macOS's `sin_len`, Windows' `WSAStartup` and `SOCKET` are the shim's
   business) reached through iso_c_binding. A blocked accept or read waits
   outside the running mutators, as `block_on` does.
c. *`clotran.server`*: a socket REPL (done 2026-09-29: `start-server`,
   `stop-server`, a thread a connection, clj's prompt and error shape,
   driven by `nc`) and a prepl (done 2026-09-29: `io-prepl`'s messages
   match clj's own for the same input, :ms and clj stack frames aside),
   then `start-server` from `examples/embed` (done 2026-09-29: with
   HEAT_REPL=<port> the Fortran solver serves a REPL, its time loop runs
   outside the running mutators, and scripts/embed-repl-check reads the
   live grid, writes into it and stops the run, in the gate).
   Bytes for binary protocols (done 2026-09-29): `clotran.net/read-bytes`
   and `write-bytes` into and out of a byte array, nothing allocated, and
   `clotran.io/utf8-bytes` / `utf8-string`, what bencode needs.
d. *nREPL, as a package* (serving 2026-09-29, `~/jborden/clotran-nrepl`:
   the eleven ops below, tested against its own client and the reference
   client nrepl/nrepl 1.3.0; CIDER itself not yet tried): what CIDER speaks (bencode, eval, load-file,
   describe, completions), on the model of babashka's compact server.
e. *CIDER's debugger, queued (2026-09-29)*: CIDER's debugger UI is its
   Emacs side (`cider-debug.el`); the instrumenting is clj middleware
   cider-nrepl. clotran-nrepl answering that protocol from clotran's own
   break protocol (`clotran-break`, frames with locals) puts CIDER's
   debugger over clotran with no fork. Emacs support is its own tool,
   `~/jborden/clotran-mode` (`.cljf` in clojure-mode, `clotran-jack-in`).

Windows is built with a mingw-w64 cross toolchain and run under Wine for
quick checks; a real Windows runner is the authority, as flang is for
the gate. SEAMS.md gets the entry: ClojureScript has no socket server in
cljs.core either, so this is the host's.

### 22. Standalone binaries

Scenario C: one executable, no runtime to install. Step 12 laid out
`clotran build app.cljf -o app` -- the runtime, compiled core, the
program's compiled namespaces and the heap image in one file, `-main`
getting `*command-line-args*`, packages still opened at run time.
Missing first: an image that holds compiled core (a compiled procedure
is a pointer into a library, so the image has to name the libraries
and reopen them in the same order).

LANDED 2026-09-30: programs. `clotran app.cljf a b` runs a file with
*command-line-args* and `clotran -m NS a b` a namespace's -main, as clj -M
does, with no REPL after and status 1 on an uncaught error (DEVIATIONS 68
for the report's layout); `clotran test` runs a project's -test namespaces
(clotran.test-runner, which needed file-seq: clotran.io.File's directory
methods over src/c/fs_shim.c). make test's check-program. Next: build.

LANDED 2026-09-30: `clotran build -m NS -o app` (or a file that is a
namespace with -main). The executable is clotran-bin with the image of
the heap once NS has loaded -- and the clotran namespaces otherwise
loaded on first use from the sources -- and its entry appended, with a
trailer main.f90 finds by reading its own file (fs_shim.c
clotran_exe_path). Every argument is *command-line-args*. 131 MB, 0.18 s
warm. `(:gen-class)` works (clotran/genclass.cljf).

LANDED 2026-09-30: compiled code in an image. DynLoad logs every
install -- the library by its real path, and the constant pool it was
given -- and the image holds the log and the procedure count; reading it
opens the same libraries in the same order and calls their
clotran_install again with the Vars left alone (dl_replaying), so every
handle the heap holds names its procedure again, and a different count
stops the start. A library's manifest is read without opening it as a
package (clotran-library-manifest). `clotran build` builds what the
program loads into the cache (a first pass that waits for the builds),
takes the image from a second load that installs from the cache and
builds nothing, and appends the libraries; the program writes them once
under TMPDIR/clotran-app-<image hash> and opens them from there. The
program's loop 165 -> 8.5 ms. Core is compiled into it too: the build
loads core from its source so core's library installs (a first build
compiles it, about a minute; the cache keeps it). That needed a form to
analyse the same in every process: a name in a clotran namespace not yet
loaded -- clotran.rt/array-list, clotran.rt.TransformerIterator/create --
now loads it at analysis once core has loaded (Eval prepare_clotran_name),
where before it was a late lookup in one process and a Var in the other,
and core's library was refused (sequence, partition-by, partition-all,
shuffle). MEASURED, and compiled core does not pay everywhere: reduce
over a range 161 -> 82 ms, but (reduce + (map inc ...)) 341 -> 446 and
into/map 345 -> 416 -- the interpreter's flat form has overtaken the
compiled lazy-seq path, which is the next thing to look at there.
Packages opened at run time are untried in a built program.

### 23. `repro`: reproducible reductions

Scenario C's "deterministic". PACKAGES.md has the design: binned
summation (Demmel and Nguyen), `(repro/sum xs)` bit-identical across
orders, threads and machines. Blocked on ReproBLAS's licence, which
was not found; the alternative is to write the binned accumulator
ourselves from the paper, which is small.

### 24. Threads, the rest

A thread pool for agents (today a busy agent's drain is a thread of its
own). Parallel marking in the collector only when a measurement shows
marking in the pause -- step 14's showed the sweep, which was fixed by
lazy per-thread sweeping instead.

### 25. Network clients

Scenario C's event streams, on step 21's sockets: a TCP client first,
protocol clients (HTTP, Kafka) as packages after, weighed against the
scenario when step 21 is done.

**Deferred (2026-09-29): Fortran values in the debugger and the REPL.**
Looked at, not started. What was found, so it is not re-derived:
- A running program's MODULE variables can be read and written by name
  with no debug information: gfortran exports each as the data symbol
  `__<module>_MOD_<name>`, found with dlsym from Fortran (bind(C), as
  DynLoad does), an allocatable one as gfortran's array descriptor
  (data address, rank, bounds). Tried on a small solver: a scalar, a
  fixed array and an allocatable with bounds -2:4 read, `dt` written
  between steps and used by the next one. Main-program variables are
  not exported; flang's descriptor has another layout.
- With `-g`, gfortran 16's DWARF describes everything at -O0: each
  local's frame offset, derived types' member offsets, and an
  allocatable's data location, allocation status, bounds and stride as
  expressions over the descriptor. So goal 2's "DWARF describes only
  indirectly and late" is too pessimistic for gfortran. At -O2 the
  locations are lists, a value readable only where it is live. flang 23
  describes types and its descriptor but gives locals NO location.
- lldb, the only native debugger on macOS arm64, shows no Fortran
  locals at all (`frame variable` is empty); gdb does not run there.
- What building it would take: find the DWARF (in the ELF on Linux, a
  .dSYM on macOS), parse it (Clojure over byte arrays -- step 15), walk
  the frames when the solver calls clotran's hook, evaluate location
  expressions (a small stack machine), present scalars as numbers,
  arrays as clotran arrays over the solver's memory, derived types as
  maps -- so "every obj%val" is `(map :val cells)`. Fortran frames would
  sit in the break protocol's :frames beside Clojure's. Weeks, mostly
  the parser. A CIDER front end needs step 21's sockets and an nREPL
  server, and cider-nrepl's middleware read first.
- An atom holding a program's control state is the opt-in variant:
  consistent snapshots, watches, validators, but the program must be
  written for it. Arrays already work this way (examples/embed).

### 26. One machine: a stack of frames shared by bytecode and compiled code (planned 2026-09-30)

James, 2026-09-30, on `(time (apply + (take 1000000 (range))))` taking
seconds: "I feel like we are doing something fundamentally wrong." We
are. This step is the fix, and it comes before steps 24 and 25.

**What was measured.** The same job -- sum the first 10^6 elements of
an infinite lazy sequence -- in six runtimes on this machine, each the
idiomatic way and as a hand-built memoized stream (a thunk cell per
element, which is what a Clojure `lazy-seq` is). ms:

| runtime | the step runs as | idiomatic | hand-built stream |
|---|---|---|---|
| GHC -O2 | compiled, fused | 2.3 | 12.9 |
| CPython 3.14 | C library (itertools) | 9.5 | -- |
| GHC -O0 | compiled, no fusion | 17.8 | 37.5 |
| clj | JIT | 61 | 73 |
| SBCL 2.4.9 | compiled | -- | 65 |
| CPython 3.14 | generators | 78 | -- |
| CHICKEN 6 csc -O3 | compiled | -- | 302 |
| GHCi 9.4 | bytecode | 12 | 576 |
| CPython 3.14 | interpreted | -- | 675 |
| **clotran** | flat interpreter | **1752** | **2604** |
| CHICKEN 6 csi | interpreter | -- | 2800 |
| SBCL sb-eval | tree walker | -- | 10126 |

Per element, clotran against clj: an empty loop 61 ns against 4.8, a
function call +140 ns against +0.7, a cons +200 against +0.6. The
fast rows share one property: the per-element step is compiled
(GHC, SBCL, CHICKEN), JIT-compiled (clj) or native library code
(CPython's C itertools). The interpreters -- clotran among them -- all
pay a thunk per element, and clotran pays four times what GHCi and
CPython pay.

**What was found** (macOS `sample`, the collector's own statistics, and
reading the call path):

1. A call costs ~110 ns interpreted. `F_CALL` (flat.inc) copies each
   argument into a new frame and nils the caller's register -- two
   write-barrier stores per argument, because a frame is a GC heap
   vector (`gc_reg_set`, 14% of a call loop); reads the callee's
   layout from heap vectors (`call_table_of`, `ct_int`, `ct_body`);
   and keeps three stacks: the shadow value stack, a trace stack
   (`push_frame`) and a continuation stack (`k_push`, `flat_top`,
   `k_finish`). The dispatch loop alone is 46% of a call loop.
2. Thread-local lookups (`pthread_getspecific`) are 7-9% of samples:
   `ctx_self()` and `gc_my_stack()` in every procedure.
3. Allocation doubles Clojure's: a closure is two objects (the closure
   and a vector of its captures), a `lazy-seq` three, `take` six an
   element where clj allocates three. An unrealised range allocates
   nine per `next` (`range_cell` builds a 3-element persistent vector
   per element), so `(seq (range n))` is not chunked in practice
   although `chunked-seq?` says it is.
4. Compiled code borrowed the interpreter's heap frames and so its
   costs: compiled `map`/`into` were SLOWER than interpreted (446
   against 341 ms). A compiled call to a compiled fn is 30 ns and a
   compiled empty loop 2.7 ns, so the compiler itself is not the
   problem -- the frames and calling convention under it are.
5. Compiled code held the heads of seqs: temporaries were never
   cleared, a local's last read was not a clearing read, arguments
   stayed in the caller's slots, and `apply` held its argument vector
   through a compiled call. Fixed 2026-09-30 (the analyser's clearing
   reads honoured, arguments taken by the callee, ABI 3) -- a
   compiled `(reduce + (take n (range)))` went from 5.5 million
   objects marked per run to 23 thousand. One retention remains on
   compiled core's `reduce` path (protocols' `internal-reduce`):
   the heap still grows with n there.
6. Not the problem, measured: the collector (68 of 1750 ms), the
   allocation lock (removing it bought nothing), the lazy cell's lock
   and broadcast (2%), `malloc` on this form.

**The model, and why.** clj's host's bytecode and Hack's (HHBC) are stack
machines built to be JIT-compiled: interpreted, every operand is a
push and a pop, and we have no JIT. SBCL compiles everything and its
interpreter is an afterthought. GHC compiles everything too -- and
GHCi's bytecode interpreter runs on the SAME stack and heap as the
compiled code, calling it and being called with no conversion, so one
module can be bytecode while the rest is native. That is clotran's
situation exactly (compiled namespaces from the cache; the REPL, eval
and a namespace being edited interpreted), so it is the model:

- ONE machine per thread: a stack of frames over the heap we have, and
  one calling convention. Compiled Fortran and bytecode are two ways
  of running a frame on it.
- Compiled code is the main path (SBCL, GHC): core and every loaded
  namespace, ahead of time, through the cache that exists.
- REGISTER bytecode (Lua, Dalvik, our flat form) for everything not
  compiled yet: with no JIT, register bytecode is the one that is
  fast to interpret.
- Laziness as GHC does it: a thunk is one object, its captures inline,
  updated in place when forced, no lock while one thread runs.
- No JIT (PLAN, "Should we JIT?"), no C beyond small shims, no
  change to what a value is.

**The machine.**

1. THE STACK. Per thread, the value stack that exists (fixed, never
   moves, scanned as roots) holds every frame's registers: a frame is
   slots `base+1 .. base+nregs`. Pushing one bumps a pointer; there is
   no heap frame and no write barrier on a register, because the
   collector scans the live stack instead. A parallel array of FRAME
   RECORDS -- fn, code handle, pc, base, caller, kind (bytecode,
   compiled, builtin, native Fortran) -- replaces the trace stack and
   the continuation stack: a stack trace, a break's view of the
   locals and the debugger all read this one chain.
2. CODE OBJECTS. An arity's code is a native integer array of
   instructions plus a rooted array of constants and its layout
   (nregs, nparams, capture slots), in a registry by handle, as
   CompiledFn's table is. Nothing at run time reads a persistent
   vector to find out how to call a function.
3. CALLS. Arguments are in consecutive registers at the top of the
   caller's frame, and the callee's frame BEGINS there (Lua): no copy.
   A CALL instruction caches its callee (identity, or the Var's
   epoch) and the callee's entry, so a call is a check, a push and a
   jump. A compiled procedure is entered with the same frame --
   `subroutine f(ctx, base)` -- and calls bytecode, and is called by
   it, the same way; an unknown callable (keyword, map, multimethod)
   takes the general road.
4. CLEARING. The analyser's clearing reads become CLEAR/MOVE in the
   bytecode and in compiled code; a callee owns its arguments. A frame
   that returns is simply popped. Holding a seq's head becomes
   something code has to do on purpose.
5. CLOSURES AND THUNKS. A closure is one object: code handle and up to
   OBJ_SLOTS captures inline (a vector only beyond that). A lazy-seq
   is one object the same way; forcing it runs its code on the stack
   and overwrites it with the result, blackholed by owner id; the
   state lock only when more than one thread runs.
6. THE CONTEXT. The thread's context is passed down every call (as
   compiled code already passes its stack), not looked up.
7. SUSPENSION. A thread (an evaluator context, NOTES: threads are
   contexts) may yield only at a bytecode frame, as today's flat form
   does; compiled frames run to completion or call back. Checked
   against step 14's contexts before step 24 builds on it.
8. INTEROP. Values keep their tags; native arrays stay in the registry
   BLAS and a solver see. A call into a Fortran package pushes a
   frame of kind native, so the debugger's chain shows it with the
   package's names; a Fortran derived type may become a value kind of
   its own later -- a tagged handle, as an array is.
9. THE DEBUGGER. Every frame has a pc and its registers on the stack:
   a breakpoint is a pc, stepping is running to the next pc, and
   inspecting a frame is reading its slots -- the same for bytecode,
   compiled code (whose call sites record their pc) and native frames.

**The migration, each step gated, measured, and committed on its own.**

- 26.0 The yardstick: `scripts/bench-langs` runs the table above
  (GHC, SBCL, CHICKEN, CPython, clj, clotran), and `scripts/bench`
  gains the per-element rows (loop, call, cons, lazy step, range
  walk). Every later step cites both.
- 26.1 Code objects in native arrays: the flat form's code and
  constants move out of persistent vectors. No behaviour changes.
- 26.2 Frames on the stack: a flat body's registers become value-stack
  slots; the heap frame and its barrier go. Closures already copy
  what they capture, so no frame outlives its call.
- 26.3 One frame record: flat-to-flat calls push a record instead of a
  trace entry plus a continuation; traces, `break` and the step
  debugger read the chain.
- 26.4 The calling convention: overlapping frames and per-instruction
  call caches.
- 26.5 Compiled code on the same frames: the generator emits against
  stack registers and the record chain; the `clotran_frame_*` heap
  frame entries go (ABI 4). Compiled and bytecode frames call each
  other directly.
- 26.6 One-object closures and thunks; forcing without a lock while
  one thread runs.
- 26.7 Seqs: a range walks in real chunks; then allocation (a
  per-thread bump nursery, SBCL's shape) only if a profile then says
  so.
- 26.8 The tree evaluator (exec.inc) retires once the flat form covers
  every node kind -- or stays as the fallback for what it does not,
  with that list written down.

**The order changed, 2026-09-30.** After 26.2, compiled core ran the
yardstick 2.5x SLOWER than the interpreter (3.7 s against 1.5) -- at
HEAD too, so not 26.2's doing. Compiled code is meant to be the main
path, so its retention and 26.5 went ahead of 26.3 and 26.4. What
compiled core had been paying, each found by bisecting forms and
reading the generated Fortran:

- the head of the seq, held: a loop's or let's binding temporary, an
  `if`'s test slot (`if-let` in `seq-reduce`: the whole reduce), a
  variadic rest's temporary, never cleared; arguments left in the
  caller's slots by an interop call (compiled `apply`'s
  `(. f (applyTo (seq args)))`) and by the generic call path; and
  `apply` realising the whole rest for a compiled variadic fn, where
  `RestFn.applyTo` hands it over unrealised. Peak heap for
  `(apply + (take 1e6 (range)))`: 4*10^6 objects, now 2.6*10^5.
- a generational chain: a full collection promoted the cell a lazy
  walk was on, its realisation remembered the young tail, and every
  young collection then kept the walk's whole window alive -- 5*10^4
  objects marked each, against 7. A full collection now ages the young
  it finds alive.
- `lazy-seq` bodies handed to the interpreter one element at a time
  (the generator did not compile N_LAZY).

**No formal VM; a cost model instead (2026-09-30).** Asked whether to
define the VM formally and know its structures' costs in O-notation:
the structures are Clojure's and their orders are known; what clotran
pays is constant factors and allocation, which O-notation hides. So
`scripts/cost-model` counts the objects each operation allocates per
element -- exactly, where a time is noisy -- and `make test` fails
when a row of `test/costs.edn` goes up (check-costs). An executable
model of the instruction set (ACL2) can come once the machine settles.

**Measured** (ms for 10^6 elements; allocations per element from the
cost model; 26.2 is aaafe46):

| | 26.2 | now |
|---|---|---|
| `(apply + (take n (range)))`, interpreted | 1580 | 1497 |
| the same, compiled core | 3741 | 2024 |
| `(dorun (range n))`, interpreted | 1300 | 432 |
| `(dorun (range n))`, allocations | 9 | 2 |
| `(reduce + (map inc (range n)))`, allocations | 3.25 | 2.91 |

(5b92194's message says range went 8 -> 1 allocations: an integer
division; the cost model says 9 -> 2.)

What is left, by the table: a closure is 2 objects (clj: 1), a
`lazy-seq` 3 (clj: 2), and a `take` step 6 -- 26.6's work; compiled
calls still go through the general `gce_apply_slots` -- 26.4's.

**Targets**, against the table: an interpreted call from ~110 ns to
under 30; your form from 1752 ms to under 300 as bytecode and under
100 compiled; the hand-built stream from 2604 ms to GHCi's and
CPython's 600. The oracle, the language suite, the library tests and
the torture pass stay green at every step.

**Risks.** GC rooting while registers move from heap vectors to the
stack (the torture pass and oracle-gc exist for exactly this); the
suspension rule meeting step 24's thread pool; the break protocol and
nREPL's debugger reading the new chain; ABI churn for cached
libraries (the loader already refuses a stale ABI).

**Sources.** The runtimes as installed (GHC 9.4.8, SBCL 2.4.9, CHICKEN
6.0.0 by brew, CPython 3.14, clj 1.12) and their sources, cloned
shallow under `~/github`: GHC's `rts/Updates.h` (thunks, blackholes and
indirections) and `libraries/ghc-internal/src/GHC/Internal/List.hs`
(take's fusion RULES); CPython's `Python/bytecodes.c`
(`_INIT_CALL_PY_EXACT_ARGS`, `_PUSH_FRAME`) and `Python/pystate.c`
(`_PyThreadState_PushFrame`); SBCL's
`src/runtime/gencgc-alloc-region.h`; CHICKEN's `chicken.h` (`C_alloc`).
Also Baker's Cheney-on-the-MTA as CHICKEN describes it
(more-magic.net, "CHICKEN internals: the garbage collector") and
Coutts et al., "Stream Fusion".

## Decisions that still hold

**The value type has no `FINAL`.** Copying a `cons_value` (nine
allocatable components plus `FINAL`) cost 497 ns; `gc_value` (four
scalars) costs 4 ns. Nothing else moved that number.

**A tracing, non-moving mark-sweep GC.** Non-moving because interop
needs stable addresses: a buffer handed to dgemm must not move. The
collector itself -- typed pools, finalizers for out-of-heap storage
(ICU handles, native arrays), torture mode -- is sound and stays.
What changes in step 5 is only where roots come from.

**Concurrency is Clojure's model, after the frame stack.** STM sits on
the value representation; a collector written with a context type
takes a second thread nearly for free; one retrofitted does not.
Substrate (OpenMP vs pthreads via `iso_c_binding`) is settled by a
spike -- can two threads each run an independent evaluation without
corrupting the Fortran runtime? -- not from the armchair. `native_array`
is shared mutable memory that STM does not cover; that needs a
decision before agents exist. Many Fortran libraries are not
thread-safe (module `save` variables, COMMON), so a binding declares
it and unsafe calls are serialised.

**The debugger is a protocol, not a UI.** A breakpoint calls a handler
Var with the paused state as data and gets a command back:

```clojure
{:reason  :breakpoint          ; or :error
 :message "'this-does-not-exist' not found"
 :frames  [{:fn "t1/broken" :file "/tmp/pos.clj"
            :line 6 :col 3 :end-line 6 :end-col 25
            :env {x 3, coll [1 2]}}
           ...]}
;; handler returns :continue | {:continue v} | :step-in | :step-over
;;                 | :step-out | :abort
```

Nothing in the evaluator may assume a terminal. Pausing into a nested
REPL is the model (Common Lisp `break`, SLDB); sockets are additive
later. Frames must record tail calls elided by `recur`, or a deep loop
shows one frame and the trace lies.

As built (step 8): the Var is `*clotran-break-handler*`, `binding` it
scopes a handler, and the REPL binds itself as the root handler when
it starts. `{:eval form :frame n}` was not built: locals are
immutable and `:env` already holds their values, so evaluating in a
frame is the handler's own `(eval (list 'let bindings form))` over
the data, not a command the evaluator has to know. Steps count calls,
the events the executor has, not lines. One level: a break inside the
handler is a snapshot, and an error there is not a break. At an error
the throw is already in progress, so every command lets it continue.

**Not generated Fortran through a compiler.** gfortran costs 100 ms to
1 s per invocation and loses to interpreting for everything but a hot
loop; generated code must still cooperate with the collector; `dlopen`
is POSIX, not Fortran. When a JIT is justified it is LLVM IR and ORC
in process, with the Fortran as the runtime library. Note that this
changes the premise (Fortran as host becomes Fortran as runtime) and
should be chosen deliberately. Step 5's resolved tree is the input
either way.

**Interop syntax is Clojure's, written with ClojureScript's discipline.**
`(.method obj args)`, `(.-field obj)`, `(Type/static args)`,
`Type/CONSTANT`, `(Type. args)` and `(set! (.-field obj) v)` -- all of
which clj reader also accepts (`.-` since Clojure 1.4), so code
written this way stays `.cljc`-portable. Fortran's object model maps
onto it directly: a derived type is the class; a type-bound
`procedure` is an instance method and one declared `nopass` is a
static; a public component is a field, read with `.-`; `extends` is
the supertype chain `host_super` answers, and `deferred` bindings on
an `abstract` type are what a protocol is implemented against;
`generic` bindings are arities; `final` is a finalizer. `%` is not
used: it is Fortran's spelling of the accessor, not a semantic, and
adopting it would break every portable file to say the same thing.
What the `fortran` namespace does today -- `fortran/make-array`,
`fortran/dgemm`, the ChemSol map-in map-out routines -- is the static
half; the instance half arrives with the first wrapped derived type,
which is step 7's generator.

**Files: `.cljf`, `.cljc`, `.clj`.** A clotran source file is `.cljf`
(the feature `:cljf` in reader conditionals is the same word);
`.cljc` is portable Clojure, which clotran reads with `:cljf` and
`:default` branches taken; `.clj` is clj, loaded as written
because that is the premise. `require` looks in that order.
DEVIATIONS 33.

**A thread is an evaluator context; the kinds of thread are impls of
one protocol.** Three things not to conflate: `fork` is a process,
a green thread is a context the runtime multiplexes on one OS
thread at points it chooses (Erlang, Go, clj virtual threads,
core.async), an OS thread is real parallelism over a shared heap.
Stage 2 moves the evaluator's state into a context type; a green
thread is then a context the evaluator loop switches between, on one
OS thread, with no change to the collector -- and the debugger's
paused frame is one context while the REPL runs in another. That is
the primitive. Over it, one protocol (`spawn`, `join`, `status`,
`cancel`, a mailbox) with a current implementation the way
core.matrix has one; core.clj's `future`, `pmap`, agents and
`promise` already go through executor objects and become thin
wrappers over it. Impls, in the order they get cheap: `:green` (the
default); `:process` (local subprocesses, ssh, Slurm, a Kubernetes
Job -- via `execute_command_line`, which is standard Fortran and
works on Windows; NOT `fork`, which is Unix-only); `:os` (OpenMP or
C11 threads through iso_c_binding, after the collector is
thread-safe -- the spike); `:coarray` (Fortran's own images);
a tuple space. A shared-heap impl takes a closure; a process or
remote impl takes a form and data, since a closure over local state
cannot be shipped, and `spawn` must say which it was given. A GPU is
not an impl of this: it runs kernels over arrays and arrives as
array operations under the `fortran` namespace.

clj's virtual threads (Loom) are this model and show where the work
has to go: executors and pools were always a library, but a thread
that parks and resumes needed the runtime, because only the runtime
can capture its stack. Here the context type is the host's part and
the protocol and impls are a library in clotran. Copy Loom's rule
about blocking: `deref` of an unfinished future, a mailbox `receive`
and a subprocess wait yield to the scheduler, so pipeline code is
straight-line Clojure. The limit: on one OS thread a blocking
Fortran call (dgemm, ChemSol's dg_ld) holds every green thread until
it returns; carrier threads are the `:os` impl. Clojure itself has
not moved: at our commit Agent builds soloExecutor with
newCachedThreadPool. Prior art: Erlang, Loom, Julia's Distributed
with ClusterManagers, core.async, bordeaux-threads, core.matrix's
implementation protocol, and Fortran's own coarrays, which are the
impl a Fortran user will look for first.

As built (2026-09-20): the task type (`OBJ_TASK`, tasks.inc) is the
primitive; `:green` is its scheduling -- run at submit until the first
block, park, resume on demand. Yielding needs a re-executable dispatch
under the block, so `.` became a loop-driven node and a reify method
reached through it runs in the loop rather than a nested run; a block
under a native frame is pinned, as Loom pins a carrier. The protocol
(`spawn`, `join`, `status`, `cancel`, a mailbox) is `clotran.thread`
(src/clj/clotran/thread.cljf): two protocols, `Kind` -- what an
implementation supplies: `-name`, `-takes`, `-spawn`, `-self`,
`-receive` -- and `Handle` -- what a spawned thread answers: `-join`,
`-status`, `-cancel`, `-send` -- with one current kind in `*kind*`
the way core.matrix keeps a current implementation, and `green` the
default. The API over them is `spawn`, `join`, `status`, `cancel!`,
`send!`, `receive`, `self`, `set-kind!`. `green` is a deftype whose
handle wraps a task; its host half is four builtins the namespace is
born with (`task-spawn`, `task-status`, `task-mailbox`,
`current-task`). `:process` is the second kind to write, behind the
same names, with `-takes` `:form`.

**Arrays are never ragged.** A Fortran rank-2 array is one contiguous
column-major block; `[[I` is nested and cannot be handed to BLAS at
any price. `(aget m 1)` is a strided view over the parent's buffer.
DEVIATIONS 24 and 25.

## Open

**RESOLVED: `class` and a class literal answer the same value.**
`(class "a")` and `String` are both the class `String`
(`class_name_of`, `class_key`; a KEYWORD until 2026-09-21, when a
class became a kind of its own -- DEVIATIONS 34); the tag stays behind `clotran-type`; `host_super` is
keyed by class name; `import*` records short names. The derived suite
did not move (2164/241/370 over 324 executed), the oracle gained
seven value-compared cases, and `pprint` got past `(condp = (class x)
String ...)` -- to a column-accounting bug of its own. DEVIATIONS 34.

**Where does the binding generator read type information from?**
Parsing `interface` blocks, or a declaration written in clotran.
Step 6 answers it with one example.

**Frames for every call, or only non-tail ones?** Pushing per call
measures as free, so this is about trace readability.

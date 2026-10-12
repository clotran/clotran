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

**THE NEXT SPEED WORK (decided 2026-10-10, step 34's closure).** The
yardstick's road ended at the interpreter's floor; this tier is where a
Fortran host wins outright, because clj's host cannot vectorize what
gfortran can. The target is stated before the work, as the yardstick
was, so the gain is attributed: three loops a scientist writes, over a
`double-array` of 10^6, interpreted today against clj (both answer the
same value):

| form | clotran ms | clj ms |
|---|---|---|
| dot product: `loop` over `(aget a i)` `(aget b i)` | 2400 | 15 |
| stencil: `dotimes` with `aset` of a 3-point average | 3174 | 127 |
| an LCG Monte Carlo sum (no array; `mod`, `/`, `double`) | 525 | 26 |

scripts/bench carries them. The goal is each row BELOW clj's, by the tier
compiling the qualifying `defn` to a Fortran loop (`do concurrent` where
`amap`'s shape allows), behind `clotran compile`, everything else staying
interpreted and the warning saying why a body did not qualify. In James's
rules' order: the tier modelled first (which bodies qualify, the
translation to a loop, correctness against the flat form's meaning, and
a cost theorem -- honest here, since the generated code is the loop the
machine runs); the emitter generated from it, as vmc_gen was; then wired
in and measured against the table. Found on the way and not yet fixed:
`aget` costs ~2.4 us a call interpreted, the generic host call.

**LANDED 2026-10-10: tier A inside the compiled library.** Found first:
the tier already existed as clotran.purefort (hand-written Clojure
emitting Fortran, 92 cases agreeing across gfortran, flang and clj since
09-25), and `clotran compile --pure` lowered all three target loops --
but `clotran compile`, the road the loader installs, never called it:
every `aset`, `mod`, `/` and `double` became a boxed value and a generic
runtime call, so the dot product happened to hit the unboxed array fast
path (1.8 ms installed) and the stencil and the LCG installed at
interpreted speed, 2400 and 500 ms, under "compiled: 3 functions". The
join (src/clj/clotran/compiler.cljf, purefort.cljf):

- purefort has a LIBRARY MODE (`generate src {:library true}`): nothing
  `pure`, every procedure that can fail takes a trailing `err`, a
  failure calls the runtime (ClotranABI's new `clotran_fail`, Eval's
  gce_raise_coded: the class by code -- arithmetic, array index, illegal
  argument, negative array size, arity, string index -- raised in this
  thread's context) and sets the flag, and the generated code checks it
  after every such statement and returns (with-err, a paren-matching
  pass over the emitted lines; a checked operation inside an `if` or
  `do while` condition declines the version rather than branch on a
  garbage value). `do concurrent` is a plain `do` there, since neither
  an impure call nor a return is allowed inside one. The support module
  is named after the namespace's, so two libraries in one process do not
  clash. The standalone module is unchanged but for its failure sites
  now being `if ... then` blocks.
- compile-file asks purefort for the versions and, for a function with
  one over numbers and arrays alone (`:long :double :doubles :longs`)
  answering a number, a boolean or nil, and not printing, installs a
  DISPATCHER under the function's symbol: the arguments' tags tested
  per version, a scalar read from its slot, an array viewed through
  clotran_array_view (its buffer, no copy; a slice or a boxed array
  fails the test), the version called, its answer boxed into dst; on
  the flag set, a return with no answer, as a tier-B procedure after an
  error. Anything no version takes falls to the tier-B procedure,
  renamed with _b. Versions that print are not dispatched to -- the
  pure code writes Fortran's standard output, which *out* never sees;
  pure-check caught exactly that (show, describe-num, countdown).
- `clotran compile` prints each function's road: `pure Fortran: dot (4
  versions)`, then `compiled: 4 functions; 4 pure Fortran`.
- scripts/pure-check has the library road: the file compiled by
  `clotran compile`, installed, every case through the installed
  functions against clj -- and the CONTROL that every function library
  mode emits a dispatchable version for came out pure, else the road
  would be testing tier B under the pure road's name. scripts/fuzz-pure
  rides on it (30 functions, 275 runs, 0 differ). make test's check-pure
  and check-fuzz-pure cover both.
- The `^doubles` hint refused lowering ("the constant :doubles is not a
  number"): the analyser's (clotran-array-cast x :doubles) had its
  keyword emitted as an expression. Fixed; the hint the report tells
  users to add now works.

MEASURED, the step-13 rows installed from the REPL (ms, 10^6):

| form | interpreted | clj | compiled |
|---|---|---|---|
| dot product | 2400 | 6-15 | 1.0-1.4 |
| stencil | 3174 | 13-127 | 1.3-1.7 |
| LCG sum | 525 | 15-26 | 1.3 |

Every row is below clj's, by 5x to 100x. Errors inside the pure loop
answer the interpreter's exception, class and message: `(dot (double-array
3) (double-array 2))` is array_index_out_of_bounds_exception "Index 2 out
of bounds for length 2" both ways, and `(fact 25)` arithmetic_exception
"long overflow" both ways. scripts/bench's compiled column shows the
three rows this way (test/clj/bench_loops.cljf, the loops as defns).

NOT DONE, said plainly: strings and records stay tier B; the tier is
still the hand-written emitter, not a model -- it has an oracle the VM
never had, and modelling the translation is the candidate for the
model's next book, not a precondition for this.

**Array results (2026-10-10, same day).** A version answering a
`doubles` or `longs` is dispatched to as well: the dispatcher takes the
allocatable the Fortran made and `clotran_array_new` (ClotranABI.f90)
makes a clotran array of it -- one copy, since the registry's buffer
cannot be handed over through a C interface, and a memory pass beside
the loop that made the values. A library's array-valued function
allocates its result empty before anything can fail (the emitter), as a
failed call returns on err and the caller's copy of an unallocated
result was a segfault -- pure-check's `(zeros -1)` found it the first
run. pure-check: 460 of 460 agree, 32 functions pure in the library (27
before); fuzz-pure 275 of 275. Measured: `scaled-copy` of 10^6 doubles,
a new array out, 1456 ms interpreted and 2.4 ms through the library,
copy included. The gate's fuzz-fn (seed 3339268384) then found the one
message a pure version writes a number into -- "Value out of range for
long: 1.0E300" -- in Fortran's ES form through the library, where the
interpreter writes clj's; the double now rides back in the error record
and the runtime writes it (clotran_fail_double), pure-check's library
road compares messages exactly (its by-value comparison of DEVIATIONS 50
is the standalone road's, and had hidden this), and DEVIATIONS 50 says
which road it is about.

**The pure loop and the other threads (2026-10-10, same day).** A pure
loop polled no safepoint, so another thread's collection waited for it
to finish: with `lcg-sum` of 10^9 (1.25 s) in a future, the main
thread's `(apply + (take 10^6 (range)))` took 2180 ms against 918
alone. Polling is not the fix; the dispatcher now gives the mutators up
around the pure call, as `call-package*` does around a foreign routine
(tasks.inc, step 14), and takes them back before it boxes the answer.
That is safe for the same reason it is for dgemm: the pure code
touches no clotran object, and an array's buffer stays where it is
while the registry grows (NativeArray.f90's move_alloc, written for
exactly this). A failure can no longer be raised from inside the pure
code -- the raise allocates -- so library mode's `err` is a record
(`cl_err`, code and message) that cl_fail fills and the dispatcher
raises through clotran_fail once it holds the mutators again; the pure
module calls nothing of the runtime, and cl_fail is pure again. The
same run: 942 ms beside the loop. scripts/compiler-check runs a pure
loop in a future and requires it still running after the main thread
has allocated; pure-check's library road covers the failures (460 of
460 agree, 27 pure). No new design decision: the baton is step 14's,
the handle rules step 27's.

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
restart-agent resumes a failed agent's kept queue. The thread pool
came with step 24 (2026-10-10), designed in ACL2.

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
   client nrepl/nrepl 1.3.0, and the real CIDER headless in Emacs by its
   test/cider-test.el): what CIDER speaks (bencode, eval, load-file,
   describe, completions), on the model of babashka's compact server.
e. *The debugger in the editor -- superseded by step 31a (2026-10-06):
   a DAP server, which CIDER's Emacs reaches through dape as VS Code and
   Neovim reach it natively; the cider-nrepl protocol is not the target.
   The original note:* CIDER's debugger UI is its
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

**Decided 2026-10-10: the agent scheduler, designed in ACL2 from what
the strong runtimes do, not from clj's host Agent class.** James: "threads and
concurrency are extremely important to get right. both clojure and rust
are rock solid in concurrency and I want to match that" -- and "you
don't have to match [the host's Agent class]. let's get this correct." The language
semantics stay Clojure's (the oracle): an agent's actions run one at a
time in the order sent; a send inside an action is held until the
action ends and released in order after the state is set, dropped if it
threw; `:fail` stops the queue until restart-agent, `:continue` goes on;
`send` for CPU work, `send-off` for blocking work. Clojure's executor
underneath -- one shared queue, a fixed pool, the agent resubmitted for
every action -- is the part that is replaceable (`set-agent-send-executor!`
exists for that), and it is the part the stronger runtimes do
differently. What Erlang's BEAM, Pony, Go and Tokio agree on, and the
design takes:

- *Per-worker run queues of runnable agents, not one shared queue.*
  Tokio's 2019 rewrite named the single shared queue every worker
  contends on -- Clojure's design -- as the bottleneck; BEAM has a run
  queue per scheduler, Pony per thread, Go per P.
- *Work stealing into an empty queue*: a worker whose queue is empty
  steals half of a victim's, starting from a random victim (Go, Tokio).
  Stealing only into an empty queue means a stolen agent runs no later
  than it would have.
- *A batch cap*: an agent runs at most B actions per scheduling, then
  goes to the back of the queue if it has more (Pony's batch, Akka's
  `throughput`, BEAM's reductions). This is what keeps a flooded agent
  from starving the rest; clj's host executor has nothing like it.
- *An injection queue* for agents made runnable from outside the
  workers (the REPL, a future, a transaction's commit), checked every N
  local picks so it cannot starve (Go's 61st tick, Tokio's ~60).
- *Blocking work on a separate, unbounded pool*: BEAM's dirty
  schedulers are this; `send-off` keeps today's thread per busy agent,
  draining without a cap, since nothing waits behind it.
- *Locked run queues, not lock-free deques.* BEAM locks each run queue;
  the lock-free Chase-Lev deque took Iris and Coq to verify (arXiv
  2309.03642) and Fortran has no atomics beyond the CAS shim. Each run
  queue has a lock and a steal takes the victim's; the model's steps
  are the atomic steps the locks give. A lock-free queue could replace
  one later behind the same model.
- Not taken: preemption (Go's signals, BEAM's reductions inside a
  process). A long action holds its worker, as in Pony, Akka and clj's
  host; a pure loop gives the mutators up (step 13) so it at least holds
  up no collection.
- Not green threads (James, 2026-10-10: "just don't get me in the place
  of green threads"). A worker is an OS thread from Threads.f90's shim,
  as every thread here is; an agent is never a thread, only a queue a
  worker drains. Nothing switches stacks in user space.

The model is `model/agents.lisp`: the state (agents, run queues keyed
by worker and :global and :solo, running with the batch left, holds,
log, the sent ghost), the events (new, send, take, steal, finish,
restart, tx/commit/abort), and the theorems for every interleaving:
no two workers run one agent (agents-serial); what was sent to an
agent is what it ran, in order, then its queue (agents-order); an
agent is on exactly one run queue or one worker exactly when unfailed
with work (agents-head); unfailed work queued means some take, steal or
finish is enabled, so the machinery cannot deadlock (agents-live); a
steal never delays the agents it moves or leaves behind
(steal-no-delay); and the cost: a scheduler that finishes what runs and
takes what waits empties every unfailed queue in at most 2n events for
n actions (drive-cost). The Fortran follows the book, then
scripts/fuzz-threads grows the pool cases (more agents than workers,
sends from inside actions, a blocking send-off beside sends) against
clj.

**LANDED 2026-10-10: the scheduler, as the books state it.** Both
books certify (`model/agents.lisp`: serial, order, head, live,
live-take, steal-no-delay; `model/agents-drive.lisp`: drive-finishes,
drive-cost at 2n). The Fortran follows them (Eval.f90, "the agent
scheduler"): run queue 0 is :global and 1..K the workers' own, each an
atom holding a vector replaced by compare-and-swap, so no lock is held
across an allocation; `sched_take` is the model's take (own, :global
every 32 picks or when own is empty, a steal of half from the next
worker round, else parked on the state condition -- the park re-checks
every queue under the lock, so a push, which notifies under it, is
never lost); the worker loop and the solo drain are clotran.rt's
`agent-worker` and `agent-drain`, with the batch of 16 and the hand-off
by the next action's executor. K is the processors and two, as Clojure
sizes its send pool, or `CLOTRAN_AGENT_POOL`. The action carries its
executor as a third element; `pooledExecutor` and `soloExecutor` are
self-keyed host constants -- a builtin row there answered the builtin
itself as the value, so every `send` had been a `send-off`.

Found on the way, and fixed: an agent's queue popped by copying the
rest, so a queue of n drained in O(n^2) -- 10^5 sends to one agent did
not finish in ten minutes. The queue is now a vector and a head index
("queue", "head"), copied once more than half is behind the index: O(1)
a pop amortised, 10^5 sends and the drain in 1.6 s each. A sub-vector
VIEW with a compaction step was tried first and produced a duplicate
run of one action in about one run of three, not explained after a
day's reading; the head index uses nothing but the operations the old
code used, and showed no duplicate in sixteen runs. The park path
once read the queues through the sequence-counted cell read while
holding the state lock, which spins until the lock is free: a plain
read under the lock. Measured, one agent, 10^5 sends, the sends
alone: 1.7 s with the queue building, 3.4 s with a worker draining
beside them -- the compare-and-swap on the agent's map is contended,
and every retry allocates; that is the cost to take out next, not the
scheduler's. Checks: the language test's scheduler block (100 agents
on the pool, nested sends, send-off beside send); scripts/fuzz-threads
grew send-off, nested sends and 40 agents and runs on a 2-worker pool
in the gate's nightly set, 20 of 20 agreeing with clj on both pool
sizes.

**Closed 2026-10-10.** `shutdown-agents` is Agent.shutdown as clj
behaves (measured through `clj`): the workers wake and end, a send
after it is accepted and queued and never runs, `await-for` times
out. The language test checks it, last, after every agent above is
done with. An idle pool keeps its K threads parked, as clj's pool
keeps its threads; they are counted among the waiters with no
deadline, which is what the deadlock verdict needs -- and that verdict
had a gap the pool exposed: a waiter with no deadline slept forever
once it had decided "not a deadlock", and a worker that re-parked after
that (woken by a notify, finding nothing) woke nobody, so the language
test's unsatisfiable wait hung under the gate's load; such a wait
re-checks every 200 ms now (tasks.inc, block_on). Parallel marking
in the collector: not taken up -- step 14's measurement put the pause
in the sweep, which lazy per-thread sweeping fixed, and nothing since
has shown marking there. The cost of a send, measured: 10^5 `swap!`
on an atom take 0.14 s and 10^5 `send` 1.6 s with nothing draining,
so a send is eleven swaps; that is `send-via`'s binding conveyor (a
`binding` and a closure per send, in core.clj) and the dispatch's map
update, not the scheduler, and it goes with step 19's slow spots.
What clotran does that clj does not: a `future` after
`shutdown-agents` still runs (DEVIATIONS 78); clj's futures share the
solo executor and are rejected with it.

A race in that shutdown, fixed 2026-10-10 after the language test caught
it under the gate's load: `await`'s count-down runs as an action, so the
sender reached `shutdown-agents` and the next `send` while the worker
was still inside that action's batch, peeked the new action and ran it.
An action dispatched after shutdown is now filed with kind `:dead`
(Eval.f90, agent_enqueue); a pop ends the drain at a dead head and leaves
it queued (B_AGENTPOP), so it never runs, while actions queued before
shutdown still run, as clj's executor runs what it already holds. In the
model since 2026-10-11 (`model/agents.lisp`): a record's fourth field
holds the dead actions, `agents-order` is sent = done ++ queue ++ dead,
`shut-persists` says no event clears shutdown, `enqueue-after-shutdown`
that a send after it touches no run queue and no live queue -- so no
worker can take a dead action -- and `total-work-enqueue-after-shutdown`
(`model/agents-drive.lisp`) that it adds no work to drive-cost's 2n.

Sources read 2026-10-10: the BEAM scheduler
(blog.appsignal.com/2024/04/23/deep-diving-into-the-erlang-scheduler),
Pony's scheduler (tutorial.ponylang.io/runtime-basics/scheduler,
ponylang.io/faq/runtime), "Making the Tokio scheduler 10x faster"
(tokio.rs/blog/2019-10-scheduler), Go's work-stealing scheduler
(about.sourcegraph.com/go/gos-work-stealing-scheduler), Akka's
Dispatcher `throughput` (doc.akka.io), the Chase-Lev verification
(arxiv.org/abs/2309.03642) and the verified OCaml 5 work-stealing
scheduler (iris-project.org/pdfs/2026-pldi-parabs.pdf).

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
  fast to interpret. SUPERSEDED 2026-10-06 by step 31: stack bytecode
  and a JIT.
- Laziness as GHC does it: a thunk is one object, its captures inline,
  updated in place when forced, no lock while one thread runs.
- No JIT (PLAN, "Should we JIT?"), no C beyond small shims, no
  change to what a value is. The "no JIT" is SUPERSEDED 2026-10-06
  by step 31.

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
- 26.9 The differential fuzzer (James, 2026-10-01: "add it now, it
  might help you understand things better and not run into so many
  bugs"). `scripts/fuzz` builds random closed programs from a typed
  grammar whose let, fn, if-let and when-let follow -- and are checked
  against -- Clojure's own specs (the vendored
  clojure/core/specs/alpha.clj), through test.check; runs them through
  clj and through clotran flat, tree and compiled; any difference is a
  bug, and --shrink cuts a failure down. What it finds goes into
  test/clj/fuzz-regressions.edn, which make test runs with 300
  generated cases (check-fuzz). Its first find: two long literals
  whose product overflows compiled to a constant gfortran folds and
  rejects, failing a whole namespace's library.

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

**Compiled core is still slower, and ./clotran no longer turns it on
(2026-10-07).** James saw `(time (apply + (take 1e6 (range))))` take
1461 ms at a `./clotran` prompt, against the 920 ms in this plan.

What it was not:
- not a regression in the code: from source, from a fresh image, and
  through scripts/bench it was 914-932 ms;
- not the stale image in the working tree: that was refused ("from
  another build"), and the sources loaded.

What it was: the launcher's CLOTRAN_AUTOCOMPILE=1, on since 09-26,
which installs compiled core from ~/.cache/clotran once a build has
filled it. Before the cache is warm a run is interpreted; after, it is
compiled.

scripts/bench, ms, interpreted core against compiled core (the same
run, the third column now in scripts/bench):

| form | interpreted | compiled |
|---|---|---|
| (apply + (take 1e6 (range))) | 915 | 1440 |
| (reduce + (range 1e5)) | 3.3 | 8.4 |
| (count (into [] (map inc ...))) | 56 | 89 |
| (count (str (vec (range 2e4)))) | 74 | 79 |
| (count (sort (map ...))) | 74 | 181 |
| (reduce (fn [m i] (assoc ...)) {} ...) | 39 | 21 |
| loop, fib, deep recursion | the same | the same |

The cause is 26.5's, still not done. Compiled code calls through
heap frames (the `clotran_frame_*` entries of ClotranABI.f90), so
every crossing between compiled and interpreted code -- which seq
code makes at every lazy step -- pays for a frame on the heap. The
fix is the one frame stack steps 30-31 design for bytecode, JIT'd and
compiled code alike.

Until then ./clotran has CLOTRAN_AUTOCOMPILE=0 by default;
CLOTRAN_AUTOCOMPILE=1 turns it on, and numeric namespaces still gain
from it (the README's sumsq: 716 ms to 1). A better default for
later: compile user namespaces but leave core interpreted, which the
loader cannot yet tell apart.

Also found on the way: an image older than the binary is refused
correctly. But `make clotran-bin` alone leaves build/core.image stale,
so every start loads the sources until `make` or `make image` runs.

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

**Where step 26 stopped (2026-10-01).** Tuning the existing flat
executor bought 8% on calls (b64aaab: lean flat-to-flat frames) and 3%
on seq walks (76950bb: `class` interned); the compact code store and
computed GO TO measured no better and were reverted. A profile puts a
call's ~93 ns in many 3-5 ns pieces and a `take` step's 1.4 us in
interpretation (the flat loop 31%, builtin dispatch 13%), not
allocation: a closure is 1 object and a `lazy-seq` 2, as clj's are.
26.6's allocation target was already met. Closing the rest is a new
calling convention and frame layout -- a VM design -- which James
decided is designed formally first, in ACL2 on SBCL (2026-10-01:
"we would need to design that in ACL2"). The boundary comes first
(step 27), then the instruction set (step 28).

### 27. The boundary, formally (begun 2026-10-01)

Interoperability is the first priority (James, 2026-10-01), and both
halves of the system stand on one boundary: the VM that runs dynamic
Clojure, and tier A (step 13), which compiles a typed subset to plain
Fortran with no runtime at all. A value crosses in one of FOUR shapes
and nothing else does:

| shape | Clojure side | Fortran side |
|---|---|---|
| number | integral, real | `integer(int8..int64)`, `real(real32/64)` |
| array | `fortran/make-array`, `^doubles` | contiguous, column-major, any rank (DEVIATIONS 24) |
| text | a string, UTF-8 by code point (DEVIATIONS 41) | `character` |
| record | `defrecord` with typed fields (planned) | a derived type |

Closures, lazy seqs, open maps, persistent collections, Vars and
exceptions never cross: they are fused away into loops (tier A, B001)
or stay in the VM.

**The model.** `model/boundary.lisp`, certified by ACL2 8.7
(`~/jborden/acl2`, built on SBCL 2.4.9), proves what is not a choice:

- the column-major layout is a bijection -- every in-bounds subscript
  of any rank lands inside the buffer (`cm-offset-in-buffer`) and no
  two share an element (`cm-offset-injective`);
- the aliasing check the door must make (F2018 15.5.2.13: an argument
  a routine may modify is associated with no other argument) implies
  every written buffer is bound exactly once
  (`alias-ok-means-written-buffers-unshared`);
- marshalling costs one unit per argument plus one per dimension,
  whatever the extents: crossing copies no array
  (`marshal-cost-ignores-extents`).

**Found by examining it** (verified on packages/blas, 2026-10-01): the
door today gives three silent wrong answers --

- a double where the manifest says `int4` crosses as its IEEE BITS:
  `(blas.raw/dgemm "N" "N" 2.0 ...)` answers `[0 0 0 0]`, no error;
- an integer past 32 bits wraps: m = 2^32+2 crosses as 2;
- the same array as an input and the output (`c` for `a`) is
  accepted, which the standard forbids: `[3 8 3 8]` for `[3 3 3 3]`.

Fixed (2026-10-01): 7ec6198 the numbers, 36419a4 the aliasing. (An
earlier line here said extents cross as `c_int` unchecked; they cannot
overflow -- NativeArray holds extents as default 32-bit integers, which
is its own limit, 2^31-1 per dimension.) Still: only `real8` and
`int4` arrays cross, though NativeArray holds every kind.

Building a routine with one argument of each scalar kind
(test/f/samplelib.f90 `echo_kinds`) found two more: the generated shim
passed a one-byte `logical(c_bool)` to a routine's four-byte default
`logical` -- a compile error, so no package with a plain logical
argument could build -- and int8 crossed as `c_long`, four bytes on
Windows; and the door refused `5N`, though a BigInt is an integer and
`(int 5N)` is 5. A BigInt inside the window now crosses.

`scripts/fuzz-door` (`make fuzz-door`) runs the model as the oracle:
ACL2 executes `cross` on every generated value -- both sides of every
window's edge, BigInts, IEEE's specials, exact doubles, and things that
are not numbers -- the door judges the same values through
`echo_kinds`, and the two must agree, a crossing value arriving
unchanged. 0 disagreements in 2392 pairs; a model mutated to widen
int4 by one is caught at once (2^31, as a long and as a BigInt).

**Decisions for James** (recommendations first; clj's own interop is
host behaviour and inconsistent -- `(Integer/toString 2.0)` truncates,
3000000000 throws, a float parameter takes 1e40 as Infinity while
`(float 1e40)` throws -- and ClojureScript has no typed parameters,
so the language gives no rule here):

**Decided (James, 2026-10-01).**

1. NUMBERS NEVER MIX. An integer crosses only into an integer kind,
   and only if it lies in the kind's window (int8 -128..127, int16
   -2^15..2^15-1, int32 -2^31..2^31-1, int64 -2^63..2^63-1, as both
   compilers report); otherwise it throws. A real crosses only into a
   real kind; a double into `real64` is the same bits. `1` where a
   routine wants a real throws, saying to write `1.0` or `(double n)`
   -- a double is exact only up to 2^53, and rounding silently is the
   mixing rule 1 forbids. `real32` rounds; a finite value past
   3.40282347e38 throws.
2. No unsigned kinds: the standard has none (both compilers have one
   behind `-funsigned`, an extension), and neither has Clojure.
3. Logical: `true` or `false` only.
4. TEXT is UTF-8 everywhere in clotran; converting is the boundary's
   job, by the kind the manifest declares: plain `character` gets the
   UTF-8 bytes (`len` counts bytes), `character(kind=ucs4)` one code
   point per position. Lossless both ways for any clotran string; both
   compilers print an emoji either way (verified).
5. A record's field types come from BOTH the Fortran type definition
   (bind-fortran reads it) and, where given, the Clojure hints --
   checked against each other.
6. DEBUGGING IS A REQUIREMENT OF THE BOUNDARY, not an add-on: every
   frame, whatever its kind (bytecode, compiled, tier A, native), reads
   as names to values, and that is an invariant of the VM model (step
   28). A call through the door pushes a native frame named after the
   routine with its arguments by name -- `pkg_call` pushes none today,
   so a package call is missing from every trace. A tier-A debug build
   records its locals in the same records. Fortran libraries compiled
   with debug information are acceptable where their internals must be
   seen. Every element of every array is inspectable on its own, under
   the array's own subscripts.
7. Callbacks: a tier-A function crosses as a plain procedure; any
   other function through a trampoline, which makes its caller tier B.
   The trampoline catches every throw (Fortran frames cannot be
   unwound), answers the library until it returns -- through the
   routine's abort flag where it has one -- and rethrows in Clojure.
   Measured (2026-10-01, an embedder calling f(t,y) 10^6 times): 2.6 ns
   per call as Fortran, 362 ns through clotran; negligible when f does
   microseconds of work, decisive when it does a few flops, so the
   compiler says which.

**Open: records are objects.** Fortran's derived types are not
Clojure's records: since F2003 they have type-bound procedures,
inheritance (`extends`), polymorphism (`class(...)`) and finalizers,
and are assigned in place -- objects. Large codes nest them, mostly
through pointer and allocatable components (MOM6's `ocean_grid_type`,
CP2K's `qs_environment_type`), which `bind(C)` forbids. So a copy into
an immutable `defrecord` cannot carry real codes. The direction James
leans (clotran is a convenience on top of Fortran): a Fortran object
stays in Fortran memory, as an array does; clotran holds a handle and
sees it as a live map -- nested objects and array components
navigable in place, every array element inspectable; changes written
in place by an explicit setter, as `aset` is; methods called with dot
syntax. **Decided** (James, 2026-10-01: "that's right").

8. OWNERSHIP comes from the Fortran declarations, which bind-fortran
   reads into the manifest: a plain dummy is BORROWED for the call
   (a pointer to a non-TARGET dummy becomes undefined on return,
   F2018 15.5.2.4); an `allocatable, intent(out)` dummy or an
   allocatable result is TRANSFERRED to clotran, whose collector frees
   it; a TARGET or POINTER dummy is RETAINED -- kept alive by a
   keep-alive link to the object that holds it (pybind11's keep_alive);
   a pointer result is LIBRARY-OWNED: clotran holds the pointer, never
   copies, and calls the library's destroy routine when the manifest
   names one. Against the "Fortran lake": a registry of every object
   that has crossed (owner, creation site, size), which the debugger
   lists; a conservative source analysis that marks a routine that may
   deallocate what it was given; and an AddressSanitizer debug build,
   in which using a freed object names the routine that freed it.
   Copying is the escape hatch for a may-free routine a library
   documents nothing better about.
9. EQUALITY follows Fortran's meaning in Clojure's spelling, so that
   neither a mathematician nor a Fortran programmer meets a different
   idea of it:

   | question | Fortran | MATLAB | clotran |
   |---|---|---|---|
   | element by element, an array of answers | `a == b` | `a == b` | `fortran/==` |
   | the same values, one answer | `all(a == b)`, equal shapes | `isequal` | `=` |
   | the same object | `associated(p, q)` | `==` on handles | `identical?` |

   `=` on Fortran arrays and objects compares VALUES -- a deliberate
   departure from Clojure, whose `=` on an array is identity in clj
   and in cljs (`extend-type default IEquiv`); a DEVIATIONS entry when
   it lands. A derived type, which Fortran gives no `==`, is equal
   component by component. NaN equals nothing, itself included, as
   IEEE and Fortran say (`x == x` is false for one NaN variable; clj's
   `(= x x)` is true only because it checks identity first). Cycles
   through pointer components are detected. Past 10^6 elements `=`
   warns once per call site per run ("use identical? to compare by
   identity") and can be aborted; compiled code calls the same
   routine. A Fortran array or object HASHES BY TYPE AND SHAPE, which
   do not change when Fortran writes in place: as a Clojure map key it
   is never lost (a content hash answered nil after a write), and the
   hash costs O(rank), not O(n).

Each decision becomes a definition and theorems in the model before
the door changes, and the door's checks are then tested against the
model's -- the fuzzer generates calls, the model says accept or
refuse, the door must agree.

**Mutation across the door (James, 2026-10-07: "let's put that in
plan").** Clojure's promise covers Clojure's values, and none of them
crosses by reference. A number crosses as the native value the routine
declares; an `out` or `inout` scalar's new value comes back as a key in
the call's answer map, and the number passed in is untouched. Text
crosses converted. A vector, map, list or string cannot cross at all.
What crosses by reference is mutable on purpose: a Fortran array, the
same buffer with no copy, and a Fortran object, a handle. clj's host
arrays are the same: `aset` writes in place, and a `let` binding names
the same array afterwards with different contents. What the door
already does: the aliasing rule (a buffer a routine may write is not
bound twice in one call, proved in boundary.lisp), and declared intent
read by bind-fortran, `:inout` where F77 declares none. Two more:

1. **`intent(in)` honoured, checked.** gfortran refuses a routine that
   assigns to an `intent(in)` dummy, but a library can still write one
   through C, EQUIVALENCE or COMMON. In the debug build (PLAN 31a's
   build flag), the door hashes every `intent(in)` array before the
   call and compares after, and names the routine that wrote it.
2. **Copy-in, by choice.** An option on an array argument, or on a
   call, that copies the array on the way into an `out` or `inout`
   dummy and leaves the caller's array as it was. Writing into your
   array becomes something the call site asks for or declines, not a
   surprise.

Both are boundary decisions, so each goes into model/boundary.lisp
first, with the door's fuzzer: the hash check catches a write to an
`intent(in)` buffer, and the copy-in leaves the caller's buffer equal
to what it was.

### 28. The VM, formally (begun 2026-10-01)

**First, the data structures** (James, 2026-10-01: "I don't expect
ANY deviation between the clojure and theoretical Big O"). Measured
against clj's own bounds (test/bigo.edn, scripts/bigo: 56 operations
in clj, clotran interpreted and clotran compiled), clotran deviated on
12: vector pop, subvec and rseq; the first of a seq over a hash map,
hash set, sorted map, sorted set or string; a string's count, nth and
subs; and, found while modelling, a sorted map's height after
deletion. One flaw, repeated: an operation rebuilt or copied the
structure instead of using it. Fixed one structure a commit, each with
its book: model/vector.lisp (our trie: nth after every operation,
depth the least that holds it), model/string.lisp (the index finds
what the walk did), model/hashseq.lisp (the cursor walks exactly the
trie's entries, in order), model/btree.lisp (16..32 per node, height
at most log16(n/2), a walk's leaves at most n/16). All 56 now meet
the theory in all three (2026-10-02). The speed-ups at n = 10^5 run
from 26x (string count) to 10^5x (rseq).

**What it did not move:** `(apply + (take 1000000 (range)))` is
1200 ms against clj's 50-75 (it was 1497): a `take` step is five
interpreted calls and ten builtins, which is the interpreter, not a
data structure. James, 2026-10-02: past the data structures, design
the bytecode VM in ACL2.

**The design.** `model/vm.lisp` is the machine before any Fortran.
Its parts, each a definition with theorems, built up a stage at a
time:

1. THE LANGUAGE the analyser hands it (analyze.inc's nodes): const,
   local, if, let, loop/recur, call, fn (closure), var, do, try,
   throw -- and a REFERENCE MEANING, a direct evaluator, the tree
   executor's semantics in miniature.
2. THE MACHINE: a register VM. A code object holds its instructions,
   its constants, its register count, and a NAME TABLE (register ->
   the local it holds, pc -> source position). A frame is a small
   fixed header -- code, return pc, the caller's result register --
   then its registers, contiguous on the thread's frame stack; no
   per-frame heap object, no generic continuation record. Operands are
   registers; a builtin reads its arguments from registers, never
   from an argument vector built for it.
3. THE COMPILER from the language to the machine.
4. THE THEOREMS: running the compiled code answers what the meaning
   does (correctness); every value the rest of the computation reads
   is in a register of a frame on the stack (what the collector
   roots: no hidden temporary); every frame reads as names to values
   (the debugging requirement of step 27, decision 6); a tail call or
   recur does not grow the stack; each instruction is O(1) but a call
   (O(arguments)) and what a builtin does.

Stage 1 is the core without functions: const, local, if, let, a
builtin. Then loop/recur, then calls and frames, then closures, then
try/throw, then vars with per-call-site caches -- each stage keeping
every theorem of the ones before.

**Paused behind step 29** (James, 2026-10-02), **resumed 2026-10-04**
once the gate was fast enough to run per commit. Stages 1 and 2
(model/vm.lisp, model/vm-loop.lisp) are certified.

**Stage 3, calls and frames (2026-10-04).** model/vm-call.lisp is the
design: one flat value stack, a frame being a base index into it, a
call copying its arguments to the callee's base above the caller's live
registers and pushing a return record (pc, base, destination). Its
checks run the machine against the meaning. model/vm-call-proof.lisp
proves it: vm-call-correct (a compiled program, recursion included,
answers its meaning) and vm-call-rooted (wiping every register from the
caller's frame top up at each return changes no answer, for any top
the compiler's call sites fit under, which `top-ok` states). Both are
one proof: the wiping machine with top nil IS the plain one. The
rooting theorem is the collector's contract; F_RETHROW's freed
message (2026-10-04) was a value outside it.

**Registers or a stack: both, then compare** (James, 2026-10-04). James
prefers a stack machine, the Hack VM's shape, as easier to reason
about and debug. The register form was step 26's choice, for fewer
dispatches per expression. Next is a stack-machine model of the same
language in its own book, with the same theorems. The choice is then
made on evidence: the proof effort, code size, and a scripts/bench
prototype. Neither shape is settled until then.

**The stack machine, proved (2026-10-04).** model/vm-stack.lisp is the
design: each frame has a locals vector and an operand stack, a call
saves the caller's (pc, locals, operands) on the control stack, and a
let stores into the next local slot. It shares vm-call's meaning and
examples. model/vm-stack-proof.lisp proves vm-stack-correct and
vm-stack-rooted, the same two theorems, with wiping applied to local
slots above the caller's scope.

**The comparison (2026-10-04, overnight).** Every book below is in
`make model`:

| | register machine | register, operands in place | stack machine |
|---|---|---|---|
| design | vm-call.lisp | vm-call-opt.lisp (the same machine) | vm-stack.lisp |
| correct, recursion included | vm-call-correct | vm-opt-correct | vm-stack-correct |
| rooted: the collector's contract | vm-call-rooted (registers above the frame's top wiped at each return) | vm-opt-rooted | vm-stack-rooted (local slots above the caller's scope wiped) |
| running is linear (vm-cost.lisp) | clk <= 2 evals | clk-o <= clk (vm-opt-faster) | s-clk <= 2 evals |
| compiling is linear (vm-cost.lisp) | code <= 3 size, a program <= 3 (size + bodies) + 1 | no longer than the plain compiler's | the same |
| proof certifies in | 174 s | 586 s | 112 s |

`evals` counts the expressions the meaning itself evaluates, every call
included. So on both machines a compiled program takes at most a
constant factor more steps than the language says it must. Each step
is O(1) except a call, which copies its n arguments.

**Measured on the same programs** (vm-call-opt.lisp, `compare-three`):
instructions in the program, then steps to the answer.

| program | register | register, operands in place | stack |
|---|---|---|---|
| fib(15) | 47 / 20715 | 36 / **16770** | 48 / 20715 |
| fib(10) | 47 / 1857 | 36 / **1504** | 48 / 1857 |
| tri(50) | 47 / 559 | 36 / **408** | 48 / 559 |
| the eight vm-call/vm-stack examples | 47-53 / 6-119 | 36-42 / 4-88 | 48-54 / 6-119 |

- **Compiled plainly, the two machines are the same.** Every leaf gets
  its own instruction (a register move, a stack load), so they take the
  same steps within one.
- **The register machine wins only through its compiler.** vm-call-opt
  is a second compiler for the SAME machine: an operator or a test reads
  a local in its own register instead of moving it first. It cuts
  19-27% of the steps and about 23% of the instructions. That is the
  published register-machine advantage, and a stack machine cannot have
  it without new instructions (a superinstruction such as
  load-load-add). vm-call-opt-proof.lisp proves it correct and rooted on
  the same machine, and never slower than the plain compiler
  (vm-opt-faster).
- **Instructions are counted, not bytes.** A register instruction
  carries three operands where a stack one carries none, so the
  register machine's programs are wider than these counts show. For an
  interpreter in Fortran the dispatch count is what costs, since each
  instruction is a `select case` iteration.
- **The proofs.** The stack proof was easier to write, because a return
  restores the caller's locals exactly. The register machine's caller
  only agrees below a bound, a relation every case carries. The stack
  proof also reused the register book's general lemmas. The in-place
  compiler was the hardest of the three by far. Each operand is in
  place or computed, so an operator has four shapes. A proof stating
  them directly split into tens of thousands of cases, until one
  operand lemma (good-op, with closed pre- and postconditions) covered
  both shapes. That cost is the price of the 20%: a production
  register compiler would carry more such cases (constants in place,
  superinstructions), and each needs this treatment.
- **Debugging.** A register frame names every value by slot ("r2 =
  …"), which the debugger needs (step 27, decision 6). A stack frame
  names locals the same way, but its operands have only a depth.

**With closures (2026-10-06).** The closure call (model/vm-closure*.lisp,
step 30) was built for both machines. Each was proved correct, and each
has the same bound of 2 `cevals` steps (`cclk-linear`, `sclk-linear`).
Neither moves a value on a call. What separated them was rooting:
- On the stack machine it is a theorem about every step:
  `vcs-rooted`, with every slot at or above the stack top wiped after
  each instruction. A collector may run anywhere and scan below the
  top. That top is in the machine state, so the proof needs no bound
  from the compiler. It took one conjunct carried through `sgood` plus
  a 7 s book.
- On the register machine there is no top. Its rooting would need
  vm-call's bound on the registers a frame holds live across a call,
  threaded through the whole proof as vm-call-proof does. That is
  still owed.
- Certification: register 521 + 59 s, stack 401 + 290 s. The stack
  figure includes the reads conjunct, which cost about 20% over the
  proof without it.

**The models' fuzzer** (`scripts/fuzz-vm-model`, `make fuzz-model`).
It generates random well-formed programs over the examples' functions
from a seed, compiles each for all three machines, and runs them in
ACL2 against the meaning. 600 programs at two seeds: 0 disagree. As a
negative control, a planted bug (a test read in place jumping on the
stale temporary instead) still CERTIFIED, because vm-call-opt's own
examples never exercise it. The fuzzer found it in 2 of 300 programs,
on the in-place machine only, and exited 1.

**The models' fuzzer** (`scripts/fuzz-vm-model`, `make fuzz-model`).
It generates random well-formed programs over the examples' functions
from a seed, compiles each for all three machines, and runs them in
ACL2 against the meaning. 600 programs at two seeds: 0 disagree. As a
negative control, a planted bug (a test read in place jumping on the
stale temporary instead) still CERTIFIED, because vm-call-opt's own
examples never exercise it. The fuzzer found it in 1 of 300 programs,
on the in-place machine only, and exited 1.

The decision is James's. The evidence so far: about 20% fewer steps for
registers, at the cost of a harder proof and a compiler that must use
operands in place; a simpler proof and simpler bytecode for the stack.

### 30. The stack VM: the interpreter's next executor (begun 2026-10-05)

James, 2026-10-05: many commits tuning the flat executor have not made
it fast, so build the stack machine step 28 modelled. This is the
INTERPRETER: the bytecode clotran runs when it is not compiled. The
compiled mode (Clojure ahead of time to Fortran) is a separate path and
stays as it is. No JIT is in scope; when one is, step 28's comparison
says either bytecode suits it.

**What the time is, measured** (2026-10-05; flat mode against a warmed
clj, ms for 10^6 iterations):

| benchmark | clj | flat | ratio | flat per iteration |
|---|---|---|---|---|
| tight loop/recur | 0.5 | 36 | 72x | 36 ns: about 6 ns an instruction |
| one fn call an iteration | 7.1 | 131 | 18x | +95 ns a call |
| one cons an iteration | 13.6 | 191 | 14x | +155 ns |
| (count (take 1e6 (range))) | 86 | 946 | 11x | |
| (apply + (take 1e6 (range))) | 47 | 1174 | 25x | |

The cons case is ONE allocation per iteration (CLOTRAN_STATS). Its 155
ns is mostly not the allocator. Most of it is the generic builtin call
-- the arguments packed into a heap vector and unpacked again
(flat_builtin, call_builtin, gcv_nth, gc_vec_set, args_give) -- and the
Fortran temporaries that call malloc and free. gc_obj and gcl_cons are
about a fifth of it. Letting a single-threaded program allocate from
the per-thread batches (batching() with one thread running) changed
nothing measurable. The allocator's lock is not the cost.

**The design** (vm-stack.lisp, proved):
- one value stack; a frame is a base, its locals and its operands on
  it, and a return record (pc, base, the closure). No continuation
  object per call, and no heap frame.
- a builtin is called with its operands where they lie on the stack,
  with no argument vector. This is the measured cost above, and the
  stack shape makes it natural.
- variable-length instructions in an int32 vector: one opcode word and
  its operands, with no fixed eight-word record copied per instruction.
- the collector scans the stack below the top and nothing else (the
  rooting theorem, vm-stack-rooted).
- the depth limit is a byte budget on the stack, calibrated near clj's
  overflow depth (about 61,600 frames of a one-argument fn), with a
  DEVIATIONS entry for the difference. Flat's fixed 200,000 frames lets
  a non-tail recursion pass that overflows in clj.

**Milestones**, each measured by scripts/bench against clj and flat,
and each fuzzed against clj through scripts/fuzz's new mode:
1. constants, locals, if, let, loop/recur, the integer and seq
   builtins as instructions. Gate: the tight loop at least 3x faster
   than flat.
2. calls to interpreted fns and builtins with operands on the stack.
   Gate: the call benchmark at least 3x faster than flat. **Kill
   criterion: if it is not, stop and rethink before going further.**
3. closures and captures (the model's next stage first).
4. try/throw and finally (modelled first).
5. vars with per-call-site caches, then everything flat does, and flat
   goes.
Until 5, the stack VM runs behind CLOTRAN_VM=stack and falls back to
flat or the tree for any body it does not compile. Flat stays the
oracle the VM is fuzzed against.

**Milestone 1, done and measured (2026-10-05): no gain.** The stack
machine ran inside flat_run's frames and protocol: S_* instructions,
variable-length, a runtime sp, flat instructions for the rest. It
loaded core.clj and agreed with flat. Then it was measured, flat
against stack, back to back on a quiet machine (run to run noise is
about 20%):

| tight loop/recur, ms | flat | stack in flat_run | stack, hot loop its own small function |
|---|---|---|---|
| < inc recur | 28-34 | 32-42 | 32 |

A counter showed the loop running wholly on the stack machine: about 9
stack instructions an iteration, at about 3.3 ns each -- already what
a select-case interpreter in Fortran costs, which has no threaded
dispatch to make one cheaper. The stack form takes 9 dispatches where
flat takes 5 or 6, so a cheaper dispatch only broke even. In this
host what costs is the NUMBER of dispatches, which is step 28's
register-or-stack comparison from the other side. The answer is
fewer, larger instructions: a register form with operands in place,
or a stack form with superinstructions. James, 2026-10-05: keep the
stack machine on a branch (feat/svm-stack), the base for the
superinstruction experiment.

**What costs instead, the same in any VM, and next:**
1. A builtin call: its arguments written into a heap vector and read
   back (cons, about 155 ns, mostly this; the allocation a fifth of it).
   The hottest builtins -- cons, first, next, seq, conj, get, nth --
   called with their operands directly, no vector.
2. A call to a Clojure fn, about 95 ns: the continuation frame, the
   call stack and the call table, against the model's frame (a base
   and a return record). The kill criterion moves here: the call
   benchmark at least 3x faster, or rethink.

**The allocator**, a separate item: the Fortran temporaries in the hot
paths that reach malloc (memmove and free in the profile), and the
collection cost per million young objects. Measured and fixed apart
from the VM, so each change's effect is its own.

**The allocator, modelled (model/alloc.lisp, 2026-10-06; James: "we
definitely want to also model our allocator").** It is designed before
the Fortran, as the VM was:
- A nursery filled by bumping, and an old space.
- A MOVING young collector. It copies a set L of nursery objects to
  the end of the old space, rewrites every reference through the
  forwarding map, and empties the nursery.
- A write barrier with a remembered set. Its invariant is that every
  old object holding a young reference is remembered.

What is proved:
- `gc-invisible`: a young collection changes nothing the program can
  observe. Every path of fields from every root reads the same after
  as before. It holds for ANY L that holds the young objects the roots
  and the remembered objects reference and is closed under young
  fields.
- `fwd-unremembered`: the barrier is what limits a young collection
  to the remembered objects. An old object the barrier never recorded
  has no young reference, and forwarding leaves it alone.
- The operations keep the invariant: a write
  (`write-keeps-barrier`, through `barrier2-write`), an allocation
  (`alloc-keeps-barrier`), and the collection itself
  (`young-gc-barrier`).

scripts/fuzz-alloc (make fuzz-model) runs random mutator programs on
the collecting model and on a heap that never collects: allocations,
writes, forgotten roots, collections with L from a worklist over the
roots and the remembered set. After every operation the observations
from every root agree. After every collection the barrier and L's
closure are checked executably. Its negative control, a barrier that
records nothing, is caught.

What it means for the Fortran: the moving collector needs every
reference the program holds to be in a root it scans. That is the
rooting property model/vm-call-proof.lisp states, and the one the two
rooting bugs of 2026-10-05 broke. A non-moving collector forgave such
a slip until the slot was reused. A moving one does not forgive it at
all, so the implementation goes with CLOTRAN_GC_EVERY counting every
allocation kind, as it now does.

Proved since (2026-10-06):
- `live-set-ok`: L computed. A worklist from the roots' and the
  remembered objects' young references, with fuel; when the fuel runs
  out the whole nursery is L. Either is a good L, so
  `collection-invisible` holds for the collector's own L. That L holds
  ONLY what is reachable is not proved; it is what makes the cost
  theorem below about live data, and it is how `reach` is written.
- `alg-is-spec`: the collector that fixes up only the remembered
  objects (`young-gc-alg`) builds the same heap as the specification
  that forwards the whole old space, given the barrier's invariant and
  a remembered set inside the old space (`rem-ok`, kept by every
  operation). gc-invisible is therefore about the algorithm.
- `alg-cost`: when the worklist finishes, a young collection takes at
  most 2 (roots + remembered objects' fields + L's objects' fields)
  steps, each O(1). The worklist's own steps are exactly its starts
  plus the young references L's objects hold (`reach-steps-exact`).
  The old space's size and the nursery's garbage do not appear. The
  "already in L?" test counts one step: in the Fortran it is the
  object's forwarding word, not a list search. A remembered entry is
  paid for by the write that made it, and the set empties at every
  collection.

scripts/fuzz-alloc runs `young-gc-alg` now, so the fuzzer checks the
algorithm and `alg-is-spec` connects it to the proof.

**The old space's own collection, modelled (model/alloc-old.lisp,
2026-10-06).** A mark and a sweep, NOT moving: an old object keeps its
place, so a reference to it stays valid as long as the object lives,
and collecting the old space rewrites no reference. It runs right
after a young collection, when the nursery is empty. What is proved:
- `young-gc-heap-ok`: a young collection over a good L leaves a
  well-formed heap. Every reference is in bounds in the new old space,
  and no young reference is left anywhere. Until now only the barrier
  was proved kept; the shapes and bounds were assumed.
- `old-gc-invisible`: the mark and sweep changes nothing observable,
  for any marked set that holds the roots' objects and is closed under
  fields. Underneath it is `obs-agree`: two heaps that agree on such a
  set read the same along every path.
- `free-reuse-invisible`: storing anything into a freed slot changes
  nothing observable. That is what reusing the slot for a new object
  does, so the free list is safe to allocate from.
- `mark-set-ok`: the mark the collector computes, a worklist from the
  roots with fuel and all objects as the fallback, is such a set.
- `full-gc-invisible`: a young collection followed by the mark and
  sweep changes nothing observable.
- `old-gc-cost`: the roots, plus the marked objects' fields, plus one
  step per old object for the sweep. The sweep is linear in the old
  space, live or not. That is why the young collection exists: it runs
  often and never pays that cost.

scripts/fuzz-alloc now runs full collections too. Its second negative
control (`-m`) is a mark that takes the roots' objects but not what
they reference, and it is caught.

**Placed (James, 2026-10-07):** the allocator in Fortran comes after
the Fortran stack VM and everything else the VM needs. That is when
allocation becomes a larger share of what is left; the profiles so far
put allocation and the collector near 11%, and 26.7 already said a
nursery waits for a profile to ask for it.

Several threads' young collection, DECIDED (James, 2026-10-07: "we
can use stop all threads"):
- stop every thread at a safepoint and collect all nurseries at once,
  in parallel. This is HotSpot's, .NET's, SBCL's, GHC's and OCaml 5's
  choice, and GHC and OCaml tried thread-local young heaps first and
  turned them down.
- A thread inside a Fortran call counts as stopped.
- Arrays that cross the boundary never live in the moving nursery.

The alternative is promote-on-publish (Erlang's per-process heaps, in
the extreme). It needs no global pause, and Clojure's few publish
points make it unusually cheap here. But it is a barrier at every
publish point, and missing one corrupts memory. It stays open in case
measured pauses with many threads call for it.

The model owes this next, before any Fortran: per-thread nurseries;
a collection that starts only once every thread is stopped or in a
native call; and the theorem that a thread in a native call, holding
only boundary arrays (never in the nursery), observes nothing of the
collection. That is `gc-invisible` with threads.

Owed in the model:
- Several threads' nurseries, stop-the-world as decided above: the
  safepoint, the in-native rule, and boundary arrays outside the
  nursery.
- Promotion into freed slots. The copy now goes to the end of the old
  space. `free-reuse-invisible` says a freed slot may take it, but the
  forwarding map would then be a slot list rather than an offset.

**Lazy cells claimed lock-free, done (2026-10-05).** Every forced
element of a lazy seq took the global state lock twice, to claim and
to give back. `model/lazy-cell.lisp` is the protocol: the state word
goes from pending to `LAZY_RUNNING + thread id` in one compare-and-swap.
Under every schedule it proves one runner (`one-runner`), that a thread
that finished forcing read the cell's value (`done-reads-realised`),
and that a realised cell stays realised (`realised-stays`). The owner
settles with a plain store. Only a thread that found the cell running
takes the lock, and it counts itself a waiter, so the owner wakes
waiters only when there are some. Measured: `(apply + (take 1e6
(range)))` 1060 -> 956 ms, `count` of the same 806 -> 747, `reduce`
over `map` 721 -> 691; `filter` unchanged. That is about 10%, which is
what removing two uncontended lock round trips per element was worth.
The rest of a forced element's cost is the thunk call and the cell's
allocation, the next items.

**The runtime, measured (2026-10-05).** scripts/bench, clotran ms, the
session's start and its end:

| form | before | after | clj |
|---|---|---|---|
| (apply + (take 1e6 (range))) | 1060 | 918 | 60 |
| (count (take 1e6 (range))) | 806 | 721 | 42 |
| cons loop, 1e6 | 290 | 199 | 16 |
| (reduce + (map inc (range 1e6))) | 721 | 367 | 16 |
| (reduce + (filter even? (range 1e6))) | 1089 | 629 | 7 |
| (reduce + (seq (vec (range 1e6)))) | 985 | 147 | 19 |
| (count (vec (range 1e6))) | 340 | 89 | 11 |

What moved them: the lazy cell's lock-free claim; a vector's seq
claiming IChunkedSeq (its reduce had walked element by element); vec
of a chunked seq a chunk at a time with no Fortran array temporaries;
and the flat interpreter answering a chunk loop's members (.nth, .add,
instance?, the bit operations, first/next/seq of a vector's seq) with
no argument vector. The profiles also found two GC rooting bugs and a
printer bug, each fixed apart (swap!'s new value, inst_invoke's
arguments, 2^122's digits), and CLOTRAN_GC_EVERY now collects at every
allocation kind, which is why it had missed the first two.

What is left is the CALL: a closure call is 80-100 ns, and even? is
two of them and five builtins (355 ns), so filter is still 93x. A
profile of a loop of calls is 78% flat_run itself -- the call and
return instructions, not a helper -- so the next measurement is per
line of F_CALL's closure road.

That measurement (gcov, a coverage build, 2e6 calls of (fn [x] x)
less a loop without them): 213 lines a call. The callee's own work is
4 of them. The rest is the protocol: the outer loop's re-entry twice
(44), copying each instruction's words (36), F_CALL's closure road
(40), the frame and record pushes (30), the call table read through
ct_int five times. Lines are not time, though. Skipping the outer
loop on a lean call and return removed 44 lines and moved nothing
(98 ns to 100). Doing it through a contained subroutine made the call
10% SLOWER (108 ns): a procedure contained in flat_run that touches
its locals keeps them in memory, and the dispatch loop's pc, rb, cb
and kb were among them. flat_builtin, flat_force and the rest already
reach w, rb and pc that way. Measured too: passing pc, rb, ks and w's
words to them as arguments instead moved nothing (98 ns to 100). So
no one part of the call is the cost; it is spread over the whole
protocol, and trimming lines does not find it. What would is the call
the model already describes (model/vm-call-opt.lisp: operands in
place, a frame that is a base and a return record), built as one
road rather than patched into this one.

**The call, modelled for both machines (2026-10-05, James: build the
modelled call, and nothing that bars the stack VM).**
model/vm-closure.lisp:
- A function is a value: a closure, its code and the values it
  captured. The callee is read from a register at run time, and a
  call of what is not a closure, or of the wrong arity, is an error.
- A body reads its captures THROUGH its closure, which the call
  leaves in the callee's frame: nothing is copied in per call.
  Clotran's ct_stack_frame copied every capture, every call.
- The arguments are evaluated into the slots the callee's frame
  begins at, and the closure into the next. So the call moves NO
  value, whatever the number of arguments: it is a return record, a
  base and a jump. `callv-moves-no-value` proves it of the register
  machine and `vcs-callv-moves-no-value` of the stack machine.
- The stack machine here is the one clotran would run, ONE value
  stack with the operands above the locals, not vm-stack.lisp's
  frames of separate lists. Its call is the same protocol: the frame
  begins at the first pushed argument, the answer returns to where
  the frame began. The call protocol bars neither machine.

scripts/fuzz-vm-closure (make fuzz-model) runs random closure
programs (captures, closures passed and kept, recursion through a
capture, wrong arities, non-closures called) through both machines
against the meaning, with a negative control that must catch a
broken machine.

PROVED, for the register machine (model/vm-closure-proof.lisp and
vm-closure-correct.lisp): `vc-correct`, every compiled program answers
what its meaning does. The callee's locals are the caller's argument
registers, read in place, and its captures are read through the
closure in its frame (`cself-ok`). The proof is vm-call-proof.lisp's
shape, with the call taken in four stages: the arguments, the callee,
the call and return, and the combination. In one lemma it outgrew
the prover.

PROVED, for the one-stack machine (model/vm-closure-stack-proof.lisp
and vm-closure-stack-correct.lisp, 2026-10-06): `vcs-correct`, the
same theorem. The arguments are pushed where the callee's frame
begins, so the call moves no value here either.

PROVED, the cost (model/vm-closure-cost.lisp): on both machines the
clock is at most 2 `cevals`, the number of expressions the meaning
itself evaluates, recursion included (`cclk-linear`, `sclk-linear`).
Every step is O(1): a `:callv` is one step whatever its arity
(`callv-moves-no-value`, `vcs-callv-moves-no-value`). The one step
that is not is `:mkclo`, which copies k captures that k counted
expressions just computed.

PROVED, rooting for the one-stack machine (model/vm-closure-rooted.lisp,
2026-10-06): `vcs-rooted`, a compiled program answers what its meaning
does with every slot at or above the stack top wiped after EVERY
step, so a collector may run at any instruction and scan only the
stack below its top. The return records hold a pc and a frame base,
no value, so that stack is all the roots there are; the closure being
called sits in its frame below the top. Two halves:
- `wiped-run-agrees`, for any program: a run that never reads at or
  above its top ends where its wiped run does. The machine checks its
  operands' count itself; what it does not check is the slot a
  `:load` or `:capt` names and that a `:ret`'s base is below its top
  (`reads-ok`).
- `vcs-program-reads`: a compiled program never does. `sgood` carries
  it as a fifth conjunct, so the correctness proof proves it.
scripts/fuzz-vm-closure runs every program wiped as well. Its new
negative control (`-w`) wipes the top slot too, and only the wiped
runs disagree.

Still owed before the implementation:
- rooting for the register machine, if it is kept: it has no stack
  top, so its wipe needs vm-call.lisp's bound on the registers a frame
  holds live across a call.

Measured in passing, for the implementation: 25-30% of flat_run is
instruction fetch and dispatch. Each instruction word is a 16-byte
gc_value, eight strided loads into a buffer in memory, dispatched
through a chain of compares. Compact integer code is a representation
the implementation needs whichever machine it runs. A cache keyed by
code-vector slot was tried and is wrong: slots are reused after a
collection.

**The VM model extended: loop and recur (2026-10-07).** The first of
the extensions the Fortran stack VM needs before it is written; the
model comes first.

Books: model/vmx.lisp, vmx-proof.lisp, vmx-cost.lisp.

The language gains:
- `(:loop (i1 .. ik) body)`: k new locals;
- `(:recur e1 .. ek)`: only in a loop body's tail, with the loop's arity.

The machine gains one instruction, `(:recur k b L)`. It copies the top
k values into slots b .. b+k-1, puts the stack top at fb+b+k, and jumps
to the loop's head L. So a loop runs in constant stack, and its head is
reached at one fixed depth, as stage 2a's depth check requires.

Every old instruction is handed to vm-closure.lisp's vcs-step
unchanged, so the books on vcs-step (the stack proof, rooting, cost,
every JIT stage) stand as they are. The JIT will need the instruction
when it is extended.

Proved:
- `vcsx-good`: an expression's code pushes its value, or, in a loop
  body's tail, arrives at the loop's head with the recur's values in
  place and nothing below the loop's first slot changed. That covers
  loops, nested loops, calls of functions that loop, and closures made
  in a loop.
- `vcsx-correct`: a whole compiled program answers its meaning.
- `sxclk-linear`: at most 2 machine steps per expression the meaning
  evaluates, every iteration counted. A loop's k slides are paid for by
  its k inits, through the stronger statement clock + 1 <= 2 evals.

The method that made it tractable:
- the property's two outcomes (a value, a recur) named apart;
- each case proved one path at a time from a handful of facts, in
  ACL2's minimal theory;
- joins split by outcome.

The first try, one lemma per case with everything enabled, timed out
at 15 minutes on a binary operator; the paths take seconds.

scripts/fuzz-vmx is its fuzzer (make fuzz-model):
- programs with counting loops, recur in either branch or under a let,
  nested loops, and calls into looping functions, each checked
  well-formed by xwf;
- the extended machine against the extended meaning, 300 programs;
- `-x`, a recur that copies one slot too high, must be caught: 46 of
  100.

Still to model before the Fortran:
- multi-arity and variadic functions;
- calls into the runtime (builtins and interop);
- try/catch/finally and throw.

**The rest of the VM's language, defined (model/vmx2.lisp,
2026-10-07).** On top of loop and recur, the design James agreed to:
- Multi-arity and variadic functions. A function is a list of clauses,
  `(n body)` or `(n body :rest)`. A call takes the clause of its arity,
  or else the variadic one, its extra values packed into one list in
  place.
- Calls into the runtime, `(:prim op ...)`. The runtime `prim` is
  constrained by nothing, so the theorems hold whatever the builtins
  compute. Its answer `(:throw . v)` throws.
- `throw` and `try`. A handler record on the control stack, beside the
  call records. A throw unwinds to the nearest handler, and its value
  becomes the handler's local. A bad call (`:not-fn`, `:arity`)
  throws, so a try catches it, as clj's ClassCastException and
  ArityException are caught.
- No recur across a try, as clj's compiler refuses one.
- `finally` desugared:
  `(try B (finally F))` = `(let [r (try B (catch t (do F (throw t))))] (do F r))`.

New instructions: `:prim`, `:throw`, `:try`, `:endtry`, and `:callv` by
clause.

19 checks run the machine against the meaning and against the expected
answers: variadic sums, arity picked and thrown, throws out of calls,
loops and builtins, the finally desugaring.

scripts/fuzz-vmx2 (make fuzz-model) runs 300 programs, 61 of them
ending in a throw, and agrees on all. Its control puts a throw's value
one slot high. At first it was caught in 4 of 100, because in
`(try (throw x) h)` the slot the broken machine skips already holds x:
the body pushed it there. The generator now pushes something else
first, and throws a division by zero under an add. The control is now
caught in 7 of 100.

**The whole language, proved (model/vmx2-proof.lisp, vmx2-cost.lisp,
2026-10-07).**
- `vcs2-good`: every expression in every frame does what its meaning
  answers. The property gains a third outcome beside a value pushed and
  a recur at its loop's head: a throw arrives where unwinding the
  starting control stack lands. That is the nearest handler's pc and
  frame, with the thrown value in the handler's local and nothing
  below it changed; with no handler, the machine stops at `:thrown`.
  The invariant that makes "nothing below it changed" true: every
  handler record's slot is at or below the stack top where the
  expression starts.
  - A throw out of a call passes over the call records: `thrown-at`
    reads only the nearest handler.
  - A loop's later iteration throws from a head whose slots were
    rewritten, so the transfer is stated against a bound, the loop's
    base, rather than the head's stack top.
- `vcs2-correct`: a whole compiled program answers its meaning, its
  value or the value of a throw nothing caught.
- `s2clk-linear`: at most 2 steps per expression the meaning
  evaluates. A try counts twice: its record pushed, and popped with
  the jump. A throw is one step however deep, and **the Fortran owes
  that**: it keeps the nearest handler's index, so a throw truncates
  the control stack instead of walking it.

The method is vmx-proof's, path by path, and its one new lesson is a
call's frame. Fixed and variadic frames differ, and opened in the
hints the `if` between them was copied into every instance. The
prover then spent ten minutes before starting a proof. Named and kept
closed (`call-frame`, `call-nl`, `call-benv`), each path takes
seconds, and the return is one abstract lemma over plain states.

The VM model is now the whole language the Fortran stack VM (step 30)
must run: closures, loops and recur, arities and variadic packing,
runtime calls, try and throw.

**The Fortran is GENERATED from the model (decided, James,
2026-10-07: "let's write the generator for everything").** A Fortran
written by hand against the model can only be tested against it, and
the proof would be about a description, not the code that ships. So
the proved ACL2 definitions are translated mechanically into Fortran,
as CompCert extracts the compiler it proves. What is trusted is the
translator and gfortran/flang, which already check each other. Nobody
edits generated Fortran. A change goes into the model, is proved, and
is generated again. A speed trick such as a superinstruction is
modelled first.

What it needs:
- **An implementation-level model per component.** Today's books prove
  things about lists and unbounded integers. Generated code needs
  64-bit integers, arrays (ACL2 stobjs, updated in place) and the real
  data layout. Each component gets that model, proved equal to the
  abstract one it refines.
- **A translator** from that ACL2 subset to Fortran, in bb. It is
  checked by running the generated Fortran and the ACL2 definitions on
  the same inputs, for identical bytecode and step-by-step identical
  machine states, with a negative control.

What it covers, in order:
1. the VM's step loop and the bytecode compiler (vmx2);
2. the analyzer from Clojure's special forms to the core language,
   modelled first (macros stay Clojure, run by core.clj);
3. the allocator and both collectors (alloc, alloc-old);
4. the persistent data structures (vector, hashseq, string);
5. the JIT's emitter (jit, jit2, jit3, extended to vmx2's
   instructions).

What stays hand-written: the builtins' results (checked against clj,
as now), I/O, the OS calls, ICU, and the glue between routines.

**The VM's implementation level, proved (model/vmi.lisp,
vmi-proof.lisp, 2026-10-07).** The first component's implementation
model, the one the Fortran will be generated from:
- One ACL2 stobj: 64-bit registers (pc, frame base, sp, status, the
  control stack's top, the nearest handler's index) and fixed-size
  arrays (code, a constant pool, the stack, the control records, the
  function table).
- Instructions are 4 words: opcode and three operands.
- A throw truncates the control stack to the nearest handler's index
  in one step; each handler record links to the one below it.
- An operation that may allocate writes its answer into a stack slot,
  so generated code holds no value across an allocation.

What is proved:
- `vmi-step-refines`: one step of the arrays, read back as vmx2's
  state, is `vcs2-step` on the program read back from them, unless an
  array overflowed. vmx2's walk to the nearest handler is the chain's
  head.
- `vmi-step-keeps`: a step keeps the invariant (registers natural,
  the control stack inside its arrays, the handler chain) and the
  program.
- `vmi-run-refines`: runs, step for step.
- The encoder's round trip: a program encoded into the arrays reads
  back as itself.
- `vmi-correct`: a compiled program, encoded and run on the arrays,
  answers what its meaning does, unless an array overflowed. With
  `vcs2-correct` under it, that is the meaning down to the machine the
  Fortran comes from.

Not proved yet: that no register or intermediate value leaves 64 bits.
The refinement holds for ACL2's unbounded integers. Fortran's integer
overflow is undefined, so before the translator emits this code the
guards must be verified: every arithmetic on bounded values, array
lengths below 2^60, code operands below 2^31.

scripts/fuzz-vmx2 `-i` runs every program on the arrays in lockstep
with vcs2-step and compares every state: 300 programs agree. `-xi`,
an array unwind that puts the caught value one slot high, is caught in
24 of 100. Comparing every step sees what comparing only answers
misses.

The proof method was vmx2's, per instruction with a few named facts,
and the lessons were about representation:
- the control stack's read-backs as functions of the field lists, so
  a write above the top is a list fact;
- `update-nth` and `nth` kept closed, or ACL2 rewrites a field write
  into conses;
- a disabled function loses its induction scheme too;
- many implications handed to `:use` together clausify exponentially
  (a 1189 s preprocess), where the same lemmas as rewrite rules took
  0.00 s.

**64 bits, proved, and the first generated Fortran (model/vmg.lisp,
vmg-correct.lisp, scripts/acl2-fortran, 2026-10-08).**
- `vmg.lisp` is vmi's machine word for word, with guards, every
  integer result declared `(signed-byte 64)`. Guard verification
  proves every array index in bounds, every stored value 64-bit, and
  every intermediate result inside 64 bits.
- The bounds invariant (`vmg-bnd`): array lengths at most 2^40;
  registers and code words at most 2^40; live control records bounded
  and linked below themselves; the nearest-handler index pointing at a
  handler, each handler linking to a handler; a function's clauses
  inside the clause arrays. `vmg-step-good`: a step that leaves the
  machine running leaves it in bounds, so `vmg-run`'s guard holds for
  a whole run.
- Each function is its vmi twin (`vmg-step-is`, `vmg-run-is`), and
  `vmg-correct` is vmi-correct for the guarded run.
- `scripts/acl2-fortran` (bb) asks ACL2 for each function's
  translated body -- no macros, only lambda, if, constants and calls --
  refuses any whose guards are not verified, and writes
  `src/f/gen/vm_gen.f90`: 29 functions, the machine a `type(vm_state)`
  updated in place, tail recursion as loops, an `if` in an expression
  as an if statement into a temporary so only the branch taken runs,
  the value operations (`rt_*`) left to the runtime. Nobody edits it;
  `make gen-vm` writes it again.
- `scripts/fuzz-vm-gen` runs fuzz-vmx2's programs on the generated
  Fortran and on ACL2's vmi and compares the machine after every step:
  300 programs and 44,650 steps agree under gfortran, 100 and 11,146
  under flang. Its control, an uncaught throw leaving two slots where
  ACL2 leaves one, is caught in 22 of 100. `make check-vm-gen` (in
  fuzz-model) also fails if the checked-in file is not what the model
  generates.

**Measured (2026-10-08), the generated VM against flat and clj.** The
loop `(loop [i 0 s 0] (if (< i 1e6) (recur (+ i 1) (+ s i)) s))`,
10^6 iterations, compiled by vmx2's compiler and run by
`test/vm/vm_bench` on the test runtime:

| | ms | instructions an iteration |
|---|---|---|
| clj | 0.54 | |
| clotran flat | 36 | 5-6 |
| generated VM, gfortran -O3 | 49 | 11 |
| generated VM, flang -O3 | 120 | 11 |

The generated code costs about 4.5 ns an instruction, flat's order,
and runs twice as many: 11 instructions an iteration where flat runs
5 or 6. That is milestone 1's finding again -- in this host what costs
is the number of dispatches. The speed does not come from
hand-tuning the generated Fortran (nobody edits it). It comes from
the model: superinstructions defined and proved in vmx2/vmi/vmg, so
an iteration is fewer instructions, and then the JIT (step 31). Being
correct by construction comes first; the generated VM replaces flat
only when it is also faster.

What the check rests on: the translator, the compilers, and the test
runtime (`test/vm/vm_runtime.f90`), which mirrors vmx2's value
functions and primitives. The generated VM is not wired into clotran
yet. That needs clotran's own values behind `rt_*` (gc_value, the
builtins, rooting for a moving collector), and the analyzer from
Clojure to the core language -- the next components, modelled first.

**The compiler at the implementation level (model/vmic.lisp,
2026-10-08).** vcs2-compile builds lists of instruction lists;
vmic writes the code words straight into vmi's arrays at a cursor,
in one pass. A jump's target is written once it is known (the
condition's jump after its branches, the try's handler after its
body). The locals' slots are an array (stobj `vce`) grown and cut
back with each scope, the loop three integers, and the expression is
read through `rt-` operations (car, cdr, a keyword test, a small
natural), so the generated Fortran will walk clotran's own lists.
`vmic-program` sizes the arrays by a first pass and fills the
function table. Checked: vmi's 15 programs in the book, and
`fuzz-vmx2 -i` compiles every program both ways and compares the
arrays (300 agree; the `-xc` control, a condition's jump one past
its else, caught 100 of 100).

Proved (`vmic-proof.lisp`, `vmic-correct.lisp`): wherever vmic
finishes without an error or an overflow, vcs2-compile's code sits at
the cursor, each instruction's four words and pool slot the encoder's
(`vmic-code`). A write elsewhere leaves a placed instruction placed, so
the backpatched jumps cost nothing in the proof. The environment is a
prefix of the slot array, and an error or an overflow is sticky. The
table's fields are folds of `update-nth`, the same ones the encoder
writes. So the machine vmic-program leaves is, in everything vmi-correct
reads, the one vmi-load-prog leaves for vcs2-program's lists, and
`vmic-correct` is vmi-correct for it: a program it compiles, run on
the arrays, answers its meaning unless an array overflowed. Soundness
only: that it accepts every encodable program is the fuzzer's claim,
not a theorem.

**The compiler, generated (model/vmicg.lisp, 2026-10-08).** vmicg is
vmic word for word, with guards and every integer result declared
64-bit, as vmg is vmi. Each function is proved equal to its vmic twin
(`vmicg-compile-is` by vmic's flag induction), so `vmicg-correct` is
vmic-correct. Guard verification proves every index in bounds and
every intermediate inside 64 bits. The bound: the cursor, the stack
depth and the environment's length each grow by at most the size of
what is left to compile, so a program under 2^39 instructions keeps
all three under 2^40. `vmicg-program` counts the sizes first,
saturating at 2^40 so the count cannot overflow, and calls a program
larger than that an overflow before writing anything.

scripts/acl2-fortran now also translates functions with several
results (an `mv` is a subroutine with intent(out) dummies after the
arguments), real recursion (`recursive`, found from the call graph;
tail self-calls are still loops), and a second stobj (`vce`,
type(vc_state) :: ce). vm_gen.f90 regenerates byte for byte.
src/f/gen/vmc_gen.f90 is the compiler. `scripts/fuzz-vmc-gen` runs it
against ACL2's vmicg-program on fuzz-vmx2's programs, a fifth of them
broken so the refusals run too: the error flag, the status and every
array agree, 300 under gfortran and 100 under flang. Its control (the
generated conditional jump one past its target) was caught 100 of 100.
It runs in `make check-vm-gen`.

The bounds a run starts from: vmg-run's guard asks for `vmg-good`
(every code word and table entry in 0..2^40, the tables inside their
arrays), and nothing proves that a loaded or compiled program meets
it. So it is checked instead: vmg-good is guard-verified ACL2 too,
and vm_gen.f90 now carries it as `vmg_good`, generated, for the glue
to run before every `vmg_run` -- translation validation, the bounds
checked where they are not proved. Both fuzzers report it: no
program fuzz-vm-gen loads or fuzz-vmc-gen compiles without an error
lies outside them, and the Fortran and ACL2 agree on it for every
one. Proving it of vmicg-program's output would drop the check. Next: wire the
generated pair into clotran -- clotran's values behind the `rt_`
operations, an analyzer from Clojure to the core language, and the
runtime's real arithmetic and primitives.

**Superinstructions (model/vmf.lisp, vmf-proof.lisp, vmfg.lisp,
2026-10-08).** First an experiment: running a loop's instructions
under one dispatch, each still doing its own reads and writes, was no
faster (54 ms against 49) -- the profile puts the time in each
instruction's code-word reads, bounds-checked stack accesses and value
building, not the dispatch. So a superinstruction is a direct
definition of a run of instructions:

| tag | run | what it does at once |
|---|---|---|
| 17 | load a; push k; lt; jmpf t | a loop's test of a local against a constant |
| 18 | load a; push k; add | a local plus a constant |
| 19 | load a; load b; add | a local plus a local |

The encoding costs no proof elsewhere: a load uses only its first
operand, so the fusion pass writes the tag into the load's fourth word.
The opcode stays 2, the program reads back as the same program
(vmi-ins ignores that word), and it runs the same under vmi-step. The
tag is only a hint. `vmi-xstep` checks that the run's instructions
follow, that the run lies inside the code and that the stack has room,
and otherwise takes one ordinary step.

Proved:
- `vmi-f17-steps` (18, 19): each superinstruction is the three or four
  steps it replaces.
- `vmi-xrun-is`: a fused run is a run at least as long.
- `vmi-fuse-prog-facts`: the pass leaves the shape, the invariant, the
  program read back and the start state unchanged.
- `vmf-correct`: a compiled program, fused and run by vmi-xrun, answers
  what it means unless an array overflowed.
- `vmfg.lisp`: the guarded twins, every index in bounds and every
  integer in 64 bits, each fused step keeping the bounds
  (`vmg-xstep-good`). `vmfg-correct` covers the whole generated
  pipeline: vmicg-program, then vmg-fuse-prog, then vmg-xrun.

Generated into vm_gen.f90 (`vmg_xstep`, `vmg_xrun`, `vmg_fuse_prog`).
`fuzz-vm-gen -f` tags each program with both passes, prints the tags,
and steps ACL2's vmi-xstep against the generated vmg_xstep: 300 under
gfortran, 100 under flang. Seed 1's 100 programs take 12,683 fused
steps where unfused they take 16,254. Its control, a loop's test that
holds jumping one instruction too far, was caught in 25 of 100.

Measured on the 10^6-iteration loop (test runtime, gfortran -O3, the
same machine and session; flat re-measured):

| | ms | dispatches an iteration |
|---|---|---|
| clotran flat | 36 | 5-6 |
| generated VM | 47 | 11 |
| generated VM, fused | 31 | 4 |

**The runtime's operations, fused (2026-10-08).** Clojure's `+` and `<`
are not vmx2's :add and :lt -- they throw on overflow, compare doubles
and ratios -- so clotran will compile them to :prim, which the model
leaves unconstrained: every theorem holds whatever the runtime's
operation does, throws included. Four more superinstructions fuse the
prims a loop runs: 20 (load a; push k; prim op 2; jmpf t), 21 (load a;
prim op 1), 22 (load a; load b; prim op 2), 23 (load a; push k; prim op
2). A prim that throws stops the run where its own step would and
unwinds. Proved as before (`vmi-f20-steps` .., three steps for 20 when
it throws, four otherwise), their guarded twins generated; a prim on
one or two values written out is `rt_prim1`/`rt_prim2`, which the
runtime answers without building the argument list. `fuzz-vm-gen -f`
agrees, and its `-xp` control (the fused prims' stack top one too high)
is caught in 7 of 100 -- fuzz-vmx2's programs call few prims.

The fused VM is the first generated machine faster than flat on this
loop. The comparison flatters it slightly: the test runtime's values
are simpler than clotran's, and the number that will count is the one
measured on clotran's values once the VM is wired in.

**The generated VM in clotran, opt-in (CLOTRAN_VM=1, 2026-10-08).**
`src/f/VmRuntime.f90` is the runtime the generated code runs on over
clotran's values (nil, true and false for the model's nil, t and
:false; a throw and a closure lists headed by private objects no
program can reach); `src/f/vm.inc` translates an arity whose nodes it
knows (constants, locals, Vars, if, do, let, loop, recur, throw, calls)
into vmx2's core language -- each call a prim, so clotran's own `+` and
`<` with their throws -- and compiles, fuses, bounds-checks and runs it
with the generated code. The arity is one function whose parameters are
its entry slots, called from a main that fetches each by a prim, so the
whole run is a compiled program from pc 0 and vmfg-correct covers it;
the translation and the runtime are glue the theorem does not, checked
instead: `scripts/fuzz -m vm` agrees with clj on 600 cases and the 140
regressions, and language_test passes 193 of 196 -- the three are a
break reading a VM body's locals and call positions, which the VM does
not keep. core.clj: 1,355 arities run on the VM, 957 stay flat. Off by
default; the gate does not run it.

Measured, and the point of the next steps:

| | flat (default) | VM |
|---|---|---|
| a 10^6-iteration loop in a fn | 32 ms | 97 ms |
| `(apply + (take 10^6 (range)))` | 947 ms | 3,900 ms |

clj does the second in 72 ms -- James's yardstick. The VM loses because
a call costs it a setup (the entry values copied, the control stack
allocated, main's prims, mkclo and callv) and every call it makes goes
back up through the evaluator (`gce_apply_slots`); the superinstructions
never run on that form. Next, in the model: a VM-compiled fn called by
the VM directly, its frame on the VM's stack, nothing allocated per
call; then the lazy-seq, range and take objects (step 26's findings 1
and 3) as modelled data structures.

**The boundary, cheaper (2026-10-09).** A profile of the yardstick
under the VM (2.58 s then) split it: the VM's own instructions 26%, the
collector 21%, the glue between the VM and the runtime 18%, the
evaluator and the builtins 36%. Per element, 77 VM instructions (~660
ns) and about 12 calls into the runtime at ~160 ns each. So the
boundary came first, as the JIT's native code will call it too:
- a call through a Var whose fn only wraps a builtin (core's first,
  next, seq, rest, cons) is ONE prim, `(:prim :clotran.vm/callw var
  args)`, not a deref prim, a VM call frame and the builtin's prim;
- the runtime's call hook answers a builtin, or a wrapper of one, on
  what is there (flat_seq_op, flat_int_op, flat_cons_op) before the
  evaluator's general apply;
- a VM closure's function id is read from its call table, one raw
  vector, not the template's persistent vectors;
- a fn or lazy-seq node's closure is made straight from the captured
  values, with no frame vector to copy them out of;
- the evaluator enters a VM body with the arguments from its slots, no
  frame made;
- a prim on three values builds no list (model/vmg.lisp vmg-prim-call,
  rt_prim3), as one and two did.
The translation also now honours DIRECT LINKING (DEVIATIONS 55): a
core call site reads the fn its Var held when the site was analysed,
as flat does. Before, redefining `first` sent core's own `str` into it,
and a redefinition calling `str` overflowed the stack; the regressions
file has the case and now runs under the VM too.

| | flat | VM before | VM now |
|---|---|---|---|
| `(apply + (take 10^6 (range)))` | 0.91 s | 2.58 s | 1.5-1.7 s |
| a 10^7-iteration loop | 255 ms | | 605 ms |

The VM is still slower than flat on both. What is left per prim is
the runtime's calling convention: arguments copied onto the value stack
and dispatched through keyword compares and a procedure pointer, about
25 ns, which flat's executor does in place.

**Forcing a lazy cell inside the machine, tried and reverted
(2026-10-09).** Under the VM each element's cell is forced by a nested
run (the runtime's next, the evaluator's apply, a fresh vm_run), ~300
ns. The protocol tried needed no change to vmx2 or its proofs: the
translator wrapped first/next/rest/seq as `(:let x (:try (:prim
callwf f x) (:callv H H t f x)))`, the runtime answered a pending cell
whose thunk the VM compiled by claiming it and THROWING a request, and
H, a fixed function of the program, called the thunk on the machine's
own stack under a try that gave the cell back on a throw, settled it
and did the op again. It agreed with clj, and it was slower: forcing an
empty thunk 300 -> 600 ns, the yardstick 1.6 -> 2.0-2.5 s. A force is
~20 VM steps and 6 prims at ~8 and ~25 ns each, more than the nested
run, and every seq op paid a let and a try besides. Any protocol that
moves runtime work into VM code loses until a VM step and a prim cost
what a native instruction and a direct call do -- the JIT's stage 2.
In flat mode forcing already runs in the loop (flat_force), so this
was never the default mode's cost.

Also measured that day, for the allocator (alloc.lisp's moving nursery
or a non-moving one): the yardstick's collections are ~2% of it and
allocation ~5-7%, so neither design moves it more than ~7%; it is
retained data that gains -- walking a kept 10^6-cell lazy seq is 87 ns
a step today, 57 laid out by bumping, 27 compacted -- so the moving
design stands for that.


**Threads, later** (after the allocator). Their logic -- the
stop-all-threads safepoint handshake, agent queues, the STM's retries
-- can be modelled and generated too. The proof must hold for every
interleaving of the threads' steps, and for the hardware's memory
ordering: arm64 reorders memory operations more than x86-64 does. The
model's primitives will be the atomics and locks of Fortran 2018
(atomic_define, atomic_cas) or OpenMP, whose memory orderings the
compilers implement for each architecture. So the generator writes no
per-architecture code. Today's threads call pthreads through bind(C)
(src/f/Threads.f90), and data shared under a mutex is already ordered
correctly on both. OpenMP would also give Windows, which pthreads does
not. nvfortran (CUDA Fortran, OpenACC) and OpenMP's parallel loops are
data parallelism -- an array kernel across cores or a GPU -- a
separate feature for clotran's numeric users, not the runtime's
threads.

### 31. A stack bytecode VM and a JIT (decided 2026-10-06)

James, 2026-10-06: "let's build a byte code stack machine then a JIT
compiler for clotran. model it, then let's see if we can get the
(time (apply + (take 1000000 (range)))) down in time." Targets:
"I can't foresee us ever needing to support other archs other than
arm64 and x86-64."

**What it reverses.** Step 26 chose register bytecode, and its
"no JIT" line rested on interpreting being the fast path for code
not compiled ahead of time. A register machine's advantage is fewer
dispatches when interpreting: Lua 5.0 and Dalvik switched to registers
for it, and the VM showdown (Shi, Casey, Ertl, Gregg 2008) measured
47% fewer instructions executed and 32% less time. A JIT removes
dispatch for both shapes, since it compiles each instruction to
machine code once. So with a JIT, stack bytecode is the simpler
format: it is easiest to compile to, compact, and its rooting is
proved for every step (`vcs-rooted`). clj's host, .NET and WebAssembly
are stack machines for this reason.

**The emitter is ours.** arm64 first, then x86-64. A small C shim
provides executable memory (`MAP_JIT` with write protection toggled
per thread on macOS, `mmap`/`mprotect` on Linux, `VirtualAlloc` on
Windows) and flushes the instruction cache. Fortran remains the host;
LLVM ORC is not adopted. The CPU model in ACL2 is the instructions we
emit and no more.

**Modelled first, in stages** (model/jit*.lisp):
1. A baseline JIT. Each bytecode becomes a fixed block of machine
   instructions. Stack slots stay in memory, and the frame base and
   stack top live in two machine registers. Theorem: for ANY program,
   a run that reads only below its top is simulated block for block.
   Compiled programs then answer what their meaning does
   (`vcs-correct`, `vcs-program-reads`). It removes dispatch, the
   fetch/decode/jump of every instruction, and nothing else.
2. Static stack depth. The depth is known at every bytecode pc, so the
   stack top's arithmetic disappears and the top slots become machine
   registers, spilled at calls and safepoints with a stack map. This
   is the stage at which stack and register bytecode should compile to
   the same machine code; the model will show whether they do. It
   extends `vcs-rooted` to compiled code.
3. Calls and inlining for core's own functions. The benchmark's time
   (sampled 2026-10-06, clotran ~920 ms, clj ~60 ms) is the
   interpreter loop 37% (dispatch about 10% of the total), calls,
   frames and closures 24%, allocation and GC 11%, and lazy forcing 8%.
   Removing dispatch alone is worth about 10%. Getting near clj needs
   the modelled one-road call, cheaper allocation, and compiled
   `range`/`take`/`+`.

**Measured at every step** with the same form and a profile, so that
each gain is attributed to its stage.

**Stage 1, proved (2026-10-06).** model/jit.lisp is the design: the
CPU model, the translation (`jblock` per bytecode, `npc` for where each
block begins, and branch targets and the function table moved to their
blocks), and ten executable checks. model/jit-proof.lisp proves
`jit-sim`: for ANY bytecode program, a run whose every step has its
operands is simulated block for block. The machine's frame base, top,
stack and return records equal the bytecode's after each block, and
its pc is at the block of the bytecode's pc. One lemma per opcode
(`block-add`, `block-callv`, ...) does the work.
`jit-clock-bound`: at most 5 machine instructions per bytecode, none of
them a dispatch. model/jit-correct.lisp: `jit-correct`, a compiled
closure program answers its meaning on the machine code, and
`jit-linear`, in at most 10 instructions per expression the meaning
evaluates. To make compiled runs qualify, `reads-ok` now also requires
a step's operands to exist (`sp` >= 2 for :add, :lt and :slide, >= 1
for :jmpf). The stack proof certified unchanged with it.

scripts/fuzz-vm-closure runs every program through the JIT as a fourth
machine. Its `-j` control breaks :add's block (the second operand read
from the first's slot) and is caught by the JIT's runs alone.

**Register or stack bytecode under the baseline JIT** (model/jit.lisp,
`compare-jit`). Each entry is bytecodes executed / machine instructions
/ memory operations:

| program | stack | register |
|---|---|---|
| fib(15) | 22,688 / 64,114 / 30,576 | 22,688 / 48,332 / 30,576 |
| tri(50) | 610 / 1,824 / 909 | 610 / 1,368 / 909 |
| down(30) | 370 / 1,104 / 519 | 370 / 828 / 519 |

Both shapes execute the same bytecodes and make the same memory
traffic. The stack form costs 33% more machine instructions, and the
whole difference is the run-time stack-top adjustments (`:addsp`).
Stage 2's static depth removes those. Under a template JIT, the shapes
differ only in that bookkeeping.

**Stage 2a, static depth, proved (2026-10-06).** model/jit2.lisp is
the design:
- `dinfer` infers the stack depth at every pc with a worklist (each pc
  set once, so linear).
- `dcheck` checks the inferred depths, as a bytecode verifier does.
  Each instruction's successors get the depth it leaves. What it reads
  (operands, a `:load`'s or `:capt`'s slot) is below the top. Each
  function's entry is at arity + 1, and main starts at 0.
- Code that passes is translated with every slot addressed as
  `FB + depth`: no stack-top register, no `:addsp`. Calls, returns and
  closure-making carry the depth as an operand (`:calld`, `:retd`,
  `:mkclod`).
- Code that fails is translated by stage 1.

model/jit2-proof.lisp:
- `dinv-step`, THE CHECK IS SOUND. When `dcheck` passes, every step
  keeps the stack top at `FB + depth[pc]`, and keeps each return
  record where its caller's depth says. This holds for ANY bytecode
  that passes, with one more case: a program halted by its last
  `:ret`.
- `jit2-sim`: from any state the invariant holds in, the machine code
  is the bytecode block for block. Nothing about the run is assumed,
  where stage 1 needed every step to have its operands.
- `jit2-clock-bound`: at most 4 machine instructions per bytecode.

model/jit2-correct.lisp: `jit2-correct`, a compiled closure program
answers its meaning through the stage-2 JIT, by its own code when the
check passes and by stage 1's when it does not. `jit2-linear` bounds
it by 10 instructions per expression the meaning evaluates.

| program | stage 1 | stage 2a | register shape (template) |
|---|---|---|---|
| fib(15) | 64,114 | **48,332** | 48,332 |
| tri(50) | 1,824 | **1,368** | 1,368 |
| down(30) | 1,104 | **828** | 828 |

Once the depth is known, stack bytecode compiles to EXACTLY the
register machine's instruction count; memory traffic is unchanged
(30,576 for fib(15)). What is left is memory traffic: every slot is
still loaded and stored. Stage 2b keeps the top slots in machine
registers, spilled at calls and at the collector's safepoints by a
stack map.

scripts/fuzz-vm-closure runs every program through stage 2 as a fifth
machine and reports how many pass the depth check. Its `-d` control
breaks stage 2's `:add` and is caught by the stage-2 runs alone.

**Stage 2b, slots in registers (model/jit3.lisp, 2026-10-06).** The
frame's first K slots (K = 8 in the model) live in machine registers;
the rest stay in memory. The allocator is LAZY, and each cached slot's
state is tracked while translating: in memory only, in its register
only (dirty), or both.
- A slot is loaded only when first read.
- It is stored only when dirty, and only where something needs it in
  memory: the runtime (calls, closure-making, returns) and boundaries.
- Popped slots are dropped and never stored.

Boundaries are branch targets, function entries, main's start and
every `:ret`. At a boundary every slot is in memory, the state that
code joining from anywhere can agree on. Spilling everything before a
runtime call is also the collector's contract at its safepoints: all
that is live is below the stack top in memory.

| program | stage 2a (instr / mem ops) | stage 2b, lazy | change |
|---|---|---|---|
| fib(15) | 48,332 / 30,576 | 33,538 / 10,850 | -31% / -65% |
| tri(50) | 1,368 / 909 | 963 / 353 | -30% / -61% |
| down(30) | 828 / 519 | 583 / 213 | -30% / -59% |
| straight-line lets | 32 / 27 | 13 / 0 | |

An EAGER cache, which spills every slot at every call and refills
after, was slower than stage 2a on fib (53,262 instructions), because
calls come every few instructions. Laziness is what makes caching pay.

Making `:ret` a boundary (so a return finds its frame in memory) cost
nothing on these programs. Its purpose is the proof: a halted return
then re-executes in place.

**Stage 2b proved (2026-10-06).** model/jit3-proof.lisp's `jit3-sim`:
from any state the invariant holds in, the register-allocated code is
the bytecode, block for block. Memory below the frame's base is the
bytecode's stack, and each slot of the frame is where the allocator's
state says: its register, memory, or both. This holds for any bytecode
the depth check passes. model/jit3-correct.lisp's `jit3-correct`: a
compiled closure program answers its meaning through the stage-2b JIT
(through stage 1 when the check fails). `jit3-linear`: in at most 18
machine instructions per bytecode -- the spills before a runtime op, its
block, and the spills into a boundary -- so 36 per expression the
meaning evaluates. A bound, not the measured cost: the table above has
what the programs actually take.

The method that made the runtime steps go through, after a call step
had failed at 892 s with 14,817 subgoals:
- state each block's run as an equation over plain variables (what the
  call reads, where it lands), proved once;
- prove the concrete step in ACL2's `ground-zero` theory, with every
  fact passed in by `:use` and no rewriting of the translation's
  terms.

After this, the call steps take about a second each, mkclo and ret a
few seconds. The other cost of the proof was a stricter check:
`dcheck-entries` now requires each entry's arity to be a natural and
its depth to be the arity plus one, which `jit2` shares.

The proof found a real bug. `:capt` took the capture in the closure's own register, and
that register may be a live cached slot, so a function reading its
capture twice answered 11 instead of 21. The translation now copies
the closure into the result register first. *jit3-defs* carries the
case as a permanent check, and the fuzzer's generator now calls a
function that reads its capture twice. Rerun with the old translation
swapped in, the fuzzer catches it in 17 of 300 programs.

scripts/fuzz-vm-closure runs every program through stage 2b as a
sixth machine. Its `-r` control is an allocator that never loads (it
takes a slot to be in its register already), and it is caught by the
stage-2b runs alone.

**Stage 1 on the machine clotran runs (2026-10-09).** jit*.lisp
designed the JIT on vm-closure.lisp's small machine; model/vmj.lisp
does it on vmi, the machine vm_gen.f90 is generated from. Each bytecode
is a block: push, load, slide, jmpf and jmp as native moves and
branches, each slot they touch checked against the stack's length
first; every other instruction, and a failed check, is a call of the
step the interpreter runs. `vmj-block-is`: a block run from its pc is
one vmi-step. `vmj-run-is`: blocks translated once from the program,
then run, are vmi-run step for step, since a step changes no code and
no pool.

src/f/vmjit.inc emits it for arm64, opt-in (CLOTRAN_VM=1
CLOTRAN_JIT=1), each function as the VM compiles it: an entry stub, the
blocks, and a slow stub that calls vmg_xstep through a bind(c) helper
and goes on through a pc -> native table (a pc with no native code
interprets). src/c/jit_shim.c maps the memory (MAP_JIT and per-thread
write protection on macOS) and flushes the instruction cache. The
emitter is written by hand from vmj-block, op for op; generating it
from the model, with an arm64 decoder theorem, is still to do.
`scripts/fuzz -m jit` agrees with clj (`make check-fuzz-jit`, nightly);
its control, a jmpf that branches on the opposite test, is caught.

It gains nothing measurable:

| | VM | VM + JIT stage 1 |
|---|---|---|
| `(apply + (take 10^6 (range)))` | 1.5-1.7 s | 1.4-1.7 s |
| a 10^7-iteration loop | 605 ms | 614 ms |

The instructions it compiles are the cheap ones. A loop iteration is
two prims (`<`, `unchecked-inc`), a recur and five moves; the prims and
the recur are ~85% of it and still go through the runtime. So the next
stage is the one that compiles the prims: a builtin's fast case
(integer compare and arithmetic with the overflow check, first and
next of a realised cell) inline, the runtime otherwise, with the
builtin's meaning on those cases a stated property of the runtime
that the fuzzer checks (prim is unconstrained in the model).

**Stage 2 on the machine clotran runs: the prims compiled (2026-10-09).**
model/vmj2.lisp: a prim whose operator -- a pool constant, so known when
the block is translated -- is a builtin with an integer fast case
(flat_int_op's: + - = < > <= >= inc dec zero? pos? neg?) is a native
`(:fast id n)`: when its arguments are integers and the answer fits 64
bits, slot sp-n := the answer and sp := sp-n+1; otherwise the step. prim
is unconstrained in the model, so what a builtin answers there is a
STATED PROPERTY OF THE RUNTIME, `prim-fast-ok`; under it, `vmj2-block-is`
(a block is one vmi-step) and `vmj2-run-is` (the native machine, blocks
translated once, is vmi-run step for step); `vmj2-ops`, a block is at
most 5 native ops. src/f/vmjit.inc emits it (vmj_fast): tags checked,
adds/subs with b.vs to the slow tail on overflow, cmp and cset for the
tests. scripts/fuzz -m jit checks prim-fast-ok against clj; its new
control, CLOTRAN_JIT_BREAK=2 (a sum one off), is caught (make
check-fuzz-jit, 20 cases).

**Recur natively, and a correction (2026-10-09).** vmj2-block's recur:
`(:poll)`, `(:chk-spfb b+k)`, `(:copydown b k)` -- the k new values down
to the frame's slots, in order -- `(:setsp-fb b+k)` and the jump; no
runtime, so `vmj2-recur-is` needs no hypothesis. A loop all native would
never reach the step that stops for a collection, so `(:poll)` goes to
the step every 4096th back edge (x28 counts them down) and the slow
step now polls whenever a stop is pending; the model's poll is the
runtime's choice, unconstrained (`jit-poll-due`), and either way the
block is the step. Its control, CLOTRAN_JIT_BREAK=3 (of two values or more,
the last not copied), runs on test/clj/jit-loops.edn, loops that end
whatever their last value holds: the generated programs seldom loop (none
in 20 cases of one seed), and a broken recur in one of core's loops can
hang. scripts/fuzz's vm and jit modes now load core from source
(CLOTRAN_IMAGE=0), so core's own fns run compiled by the VM and the JIT
-- with the heap image they were flat code, and those modes tested only
the cases' own fns.

THE CORRECTION: the table first written here measured flat three times.
Its runs were launched as `env $env ...` with `$env` holding
"CLOTRAN_VM=1 CLOTRAN_JIT=1", which zsh does not split, so CLOTRAN_VM
was that whole string and the VM was off. The commit that landed stage
2 carries those numbers ("1420 -> ~908 ms"); they are wrong. Measured
with the variables set one by one:

| | flat | VM | VM + JIT, prims | VM + JIT, prims and recur |
|---|---|---|---|---|
| `(apply + (take 10^6 (range)))` | ~915 ms | ~1430 ms | ~1310 ms | 1300-1600 ms |
| a 10^7-iteration loop | 273 ms | 550 ms | 148 ms | 59 ms |
| the same, summing | 360 ms | 800 ms | 172 ms | 71 ms |

The yardstick rows are with core compiled by the VM: loaded from source
(CLOTRAN_IMAGE=0, or an image from another build, as these runs had). With
the heap image core's fns come in as flat code and the VM compiles only
what is defined after, so under CLOTRAN_VM=1 the yardstick is flat's,
~945 ms in every mode. A loop is now 4.6x faster than flat (~6 ns a turn).
The yardstick hardly moves: its time is in the runtime's calls -- the seq operations, forcing,
allocation and the collector -- not in the steps the JIT compiles.
scripts/fuzz's JIT runs set the variables as a map, so its findings and
controls were real throughout.

**Calls under the JIT: the step by opcode (2026-10-10).** fib(35):
flat 3632 ms, VM ~4190, VM+JIT 2958, clj 78. Sampled under the JIT, a
call's time was the slow step itself (its stub, vm_jit_step and
vmg_xstep's tests for the fused patterns, ~35%), the Var's deref through
the runtime's dispatch (~23%), callv (~16%: rt_clop, the clause's pick,
the frame's record), ret. Now the slow step runs a call, a return or a
prim as that instruction's own generated step (vmg_callv, vmg_ret,
vmg_prim -- vmj-step-op: the step at an opcode is that instruction),
and rt_prim1 answers a Var's deref through the hook with nothing put on
the stack: fib(35) under the JIT 2958 -> ~2300 ms, the yardstick with
core compiled (CLOTRAN_IMAGE=0) ~1320 against the VM's ~1420. Native
callv and ret -- the closure's call table and the control stack read in
arm64 -- are what remains of stage 3; not done: what they would save is
the runtime's own work per call (the Var's value, the closure check, the
pick), which an inline cache keyed by the closure cannot hold safely
while the collector reuses a freed object's index.

### 31a. The unified debugger (decided 2026-10-06)

James, 2026-10-06: no Python. Make one debugger, with our own UX,
where the native backend is transparent to the user.

**The shape.** clotran's debugger is a Debug Adapter Protocol (DAP)
server written in clotran. Every editor talks to it the same way:
VS Code natively, Emacs through `dap-mode` or `dape`, Neovim through
`nvim-dap`, and the REPL and the terminal through its own front end.
It in turn drives a native debugger over DAP:
- macOS: `lldb-dap` (ships with Xcode and LLVM; present here under
  Xcode).
- Linux: `gdb -i dap` (gdb 14 and later), or `lldb-dap`.
- Windows, natively with no Cygwin or WSL: `lldb-dap`, `codelldb`
  (CodeLLDB's own DAP adapter over liblldb), or MinGW's `gdb -i dap`,
  found on `PATH` and launched with `CreateProcessW` and pipes.

It reports the backend once (`using lldb` / `using gdb`) as a field an
IDE can read. The repo ships a `.vscode/launch.json`; Emacs and Neovim
get a documented two-line configuration.

**What clotran does itself, so the view is identical on every backend:**
- One stack. clotran's frame records (Clojure, JIT'd and native
  frames) are read through DAP `readMemory` and merged with the native
  frames the backend reports.
- Values. A `gc_value` prints as Clojure text, either decoded from the
  heap or by calling clotran's printer through DAP `evaluate`.
- Fortran values too. lldb has no Fortran support, so descriptors and
  derived types are decoded by clotran from the type knowledge
  `scripts/bind-fortran` already has, rather than left to the backend.

**What the JIT's emitter must provide:**
- frame pointers, so native unwinding works through JIT'd code;
- registration of each compiled function through the GDB JIT interface
  (a C-level struct and hook, which lldb also reads), so backends name
  JIT'd frames;
- the pc map (machine pc to bytecode pc) and the slot map (where each
  local lives at each pc), both of which the model already computes
  and proves.

The first version debugs a JIT'd function by running it interpreted.

**Open:**
- Check the license of cpptools' `cppvsdbg`. It is believed to be
  usable only from Microsoft's products, so it is not a backend we
  depend on.
- Find which Windows LLVM builds ship `lldb-dap.exe`.
- Debug-info formats: flang targeting MSVC emits CodeView/PDB, which
  needs lldb; MinGW gfortran emits DWARF.
- The real prerequisite is a native Windows build of clotran: make, a
  POSIX shell and `dlopen` stand in the way today. The debugger can
  only be as native as the build.
- First step, a spike: drive `lldb-dap` from a bb script, stop inside a
  Fortran package call, and read the stack and the locals.

**Fuzzing, decided with it:**
- The gate shrinks the first failure of each kind (about 60 s bound),
  printing the original seed with the shrunk form.
- `make repro CASE=...` writes the case to a fixture, builds the debug
  binary, and opens it in the unified debugger with a breakpoint on
  the error path. Hangs and crashes become an immediate attach target.

LANDED 2026-10-07, both:
- **Shrinking.** `scripts/fuzz --shrink-budget N` shrinks every failure
  greedily within N seconds of wall time, all failures together, and
  marks a case the budget cut short. Each failure prints its seed and
  the command that reproduces it. The gate's check-fuzz runs with 60.
  Its negative control, `--control-shrink`, plants a bug (flat mode
  reads every 7 as 8). The run must find it and shrink every case to
  one no larger that still fails, at least one strictly smaller:
  12 planted failures, 6 smaller, all still failing, on seed 2. One
  300-character case came down to `(pr-str (vec (range 8)))`. That
  control is check-fuzz-shrink, in test-nightly. The other fuzzers
  keep their own reports for now; scripts/fuzz is the one with rose
  trees to shrink.
- **`make fuzz-repro CASE='(form)' [MODE=tree] [DEBUG=1]`**
  (scripts/fuzz-repro). This is `fuzz-repro`, not `repro`, which is
  step 23's. It prints clj's answer and clotran's for the form, writes
  it to build/repro/case.cljf, and with DEBUG=1 runs clotran under
  lldb (gdb where there is none), stopped at set_thrown, which every
  throw goes through. `--batch` prints that throw's backtrace instead,
  for a log. It is lldb and gdb directly until the unified debugger
  exists, and the binary is the ordinary -g -O2 build. Hangs are not
  handled yet: interrupting a running case is the next piece.

### 32. Execution contexts: one pool over local, SSH, Slurm and Kubernetes (decided 2026-10-06)

**Moved out of clotran (James, 2026-10-07): "threads over ssh or
whatever machinery should be a separate library we write."** The pool
-- contexts over SSH, Slurm and Kubernetes, mixed pools, retry, file
transport -- is its own library, local-only like clotran-deps and
named jborden/<repo>, not part of clotran's core and not on clotran's
critical path.

What clotran itself owes that library is only what any program would
need from the core: threads as contexts (step 24), spawning a process
with pipes, and the embedding C entry points (libclotran).
model/pool.lisp stays here as the library's design until its repository
exists, then moves with it. The rest of this step is that library's
design, kept as it was written.

James, 2026-10-06: the practical worry is that a scientist must learn
Clojure, and that clotran must make their workflow better in fact.
The driving case is a 2-D free-energy surface: an N x M grid of
umbrella-sampling windows, each run by an MD engine (GROMACS, OpenMM,
LAMMPS) with a restraint at (d1, d2), then WHAM/MBAR over the outputs.

**Order.** As written 2026-10-06: step 31 pauses once stage 2b's proof
lands (`model/jit3-proof.lisp`), then the fuzzing items from 31a, then
this step, then the rest of 31. The proof and the fuzzing items landed
2026-10-07, and this step then moved out of clotran (above). So clotran's
next work is the VM's again:
- the VM model extended to what real Clojure needs (loop/recur on the
  stack machine, try/catch/finally and unwinding, variadic and
  multi-arity fns, calls into the runtime);
- then the Fortran stack VM and its bytecode compiler (step 30);
- then the JIT's emitter (step 31).

**What a task is.** Data: a program to run (an MD engine, or clotran
code), its inputs, the files it needs, and the outputs it gives back.
The heavy compute happens in the engine, not in our VM, so what
clotran adds is distribution, transport, retry and the gather, not
JIT speed.

**One protocol, several kinds** (as in "threads are contexts", step 24):
- an execution context dispatches a task and reports its outcome;
- kinds: local threads, SSH hosts, Slurm (array jobs), Kubernetes pods;
- a mixed pool is a context over several of them.

**Failure is task-level retry.** A window is idempotent: a killed job is
re-queued on another context. Resuming mid-run means carrying the
engine's own checkpoint (.cpt, .chk) with the retried task; our VM's
state is not the state that matters. Over a network nothing is
zero-copy; only the final gather into one Fortran or NumPy array is.

**The surface scientists see.** Data in, data out. `libclotran` exports
`bind(C)` entry points (the embed example is the start), and a thin
Python client over ctypes calls them: `pool.map(window, grid)` returns
a NumPy array. This is a client for users; our own tooling stays bb,
with no Python. No Python-like syntax over Clojure: it would look like
Python and behave like Clojure (no `a[i] = x`, no NumPy semantics), and
the FES case needs no language at all.

**What we offer that Parsl, Dask and Ray do not:**
- legacy Fortran solvers called in-process, with no wrapper layer;
- one self-contained binary with pinned packages on every node, so
  there is no conda environment to rebuild per cluster;
- the scheduler's behaviour stated in the model.

**Model and fuzzer.**
- Model: the pool in ACL2 -- tasks, contexts that may drop a task, and
  retry -- with the theorem that a run over any mixed pool, under any
  pattern of failures that eventually lets each task finish, gives the
  local run's results.
- Fuzzer: random grids, pools and failure schedules from a seed, with
  the local run as the oracle.

**The model, 2026-10-07: model/pool.lisp.** Tasks are data, their work
a pure function. A context is a named slot that runs one task at a
time. Events come in any order and any mix of contexts:
- dispatch: a free context takes the next pending task;
- done: its value is recorded;
- lost: the task is queued again (a node died, a job was killed, a
  heartbeat timed out);
- late: a task thought lost answers anyway, so a value can arrive
  twice.

Proved for every schedule:
- `pool-sound`: every recorded value is the task's work.
- `pool-keeps`: no task is dropped. Each is pending, running or done,
  whatever is lost. This needed the invariant that a context holds at
  most one task, which the model found: `free` removes a context's
  every entry, so two at once would lose one.
- `pool-correct`: a run that empties the queue and the contexts answers
  the local map.

The round-robin scheduler, against any sequence of outcomes the world
chooses:
- `drive-finishes`: with as many successes as tasks, it finishes;
- `drive-cost`: in two events an outcome, so 2(n + f) for n tasks and
  f losses;
- `drive-correct`: what it finishes is the local map.

An `assert-event` runs four windows over a laptop thread and a Slurm
job, with a loss and a late duplicate, and gets the squares.

What it does not model yet:
- the files a task carries (inputs, checkpoints, outputs), and
  their transport;
- several tasks to one context at once, for a multi-slot node, which
  is several contexts today;
- time: heartbeats and timeouts are just the world choosing `lost`.

**First, the baseline.** Write down, step by step, what a scientist does
today for the 2-D surface: scripts, `.sbatch` files, rsync, by-hand
gathering. That count is what this step must shrink, and the README
example is the same workflow done through clotran.

Build order: local plus SSH first, then Slurm, then Kubernetes; then
`libclotran` and the Python client.

### 33. The runtime under the model (decided 2026-10-09)

James, 2026-10-09: "should we write everything first, then profile and
then optimize the model and then have our Fortran emitter update that
part of our language?" -- and, told that only the VM loop and its
compiler are generated: "continue in that order".

**Why.** The models designed the VM, the allocator, lazy cells and the
persistent structures, but only the VM's step loop (vm_gen.f90) and its
compiler (vmc_gen.f90) are generated from them. Everything the
yardstick spends its time in -- the heap, the collector, cons and lazy
cells, the seq operations, apply, the flat interpreter -- is
hand-written Fortran that predates the models, and in the VM model it
all sits behind `prim`, unconstrained. Optimising a model cannot touch
code that is not generated from one. The day's measurements say the
same from the other side: the moving nursery alloc.lisp designs cannot
be bolted onto the hand-written runtime, whose `roots(:)` convention
(241 procedures, ~970 call sites) keeps references as copies a moving
collector cannot update -- with every collection relocating objects
(a test mode, scratch only), core's load stops at its first vector
append. Code generated from the model is move-safe by construction
(vmi: an operation that may allocate writes its answer into a stack
slot, so generated code holds no value across an allocation).

**The order**, each stage modelled, proved, generated, fuzzed against
the model, wired in behind the API it replaces, and measured:
1. THE HEAP (GC.f90's core, ~2,300 lines).
   a. The collector's algorithm: marking from the roots over the three
      pools (objects, vector runs, texts) and sweeping. The policy
      around it (young or full, aging, batching, finalizers, the world
      stopped) stays hand-written at first and calls it.
   b. Allocation: free lists, the arena's size-class slabs, the
      threads' batches.
   c. The generations: aging, the remembered set and its barrier.
   d. THE OBJECT LAYOUT: objects sized to their kind (a cons and a lazy
      cell in 32-48 bytes, not 96) -- the change that buys locality --
      behind the same gc_slot/gc_kind API.
   e. The moving nursery (alloc.lisp), once what holds references is
      generated. Before it: identity hashes stored rather than taken
      from `ref` (gc_hash, gc_equal's fallback), the image's indices,
      and the references kept outside traced values (a closure's
      call-table ref in i2, flat's cached arena offsets).
2. The seq and lazy-cell operations as functions over the modelled
   heap, not prims.
3. The calling convention.

The yardstick is measured after each, in the mode that runs the
generated code.

**Stage 1a, the marking, generated (2026-10-09).** model/heapg.lisp is
the collector's marking at the level the Fortran is generated from,
guard-verified: GC.f90's pools seen through accessors (an object's five
slots, a run's words in the arena, each pool's marks), the marker's own
stack and counts. A reference is MARKED WHEN IT IS PUSHED, so each object
and run is pushed at most once and the stack, sized at each collection's
start to the objects and runs there are, cannot overflow (an overflow
sets a flag, and GC.f90 stops on it). Texts are leaves, counted at every
push as GC.f90's marker counted them. model/heapg-proof.lisp proves
`hpg-drain-closed`: from a state the invariant holds in -- each marked
object or run on the stack or BLACK, every reference it holds marked --
which no marks and the roots just pushed are, a drain that empties its
stack with no overflow leaves the mark set closed under references, the
property alloc-old.lisp's old-gc-invisible asks of a sweep. Underneath:
marking writes no word of the pools, never unmarks, and a push leaves
the stack below its top alone.

scripts/acl2-fortran generates it (`-b heapg`) as src/f/gen/heap_gen.inc,
included in GC.f90's contains part: the translator now takes a book's
stobj tables from its configuration, and maps an array the runtime owns
to its accessors (`:externs`: reader, writer, length), so the generated
code works on GC's own pools with nothing copied. GC.f90's push_mark and
drain_mark_stack are the generated hpg_push and hpg_drain. The yardstick
does not move (~857 ms); nothing was meant to, this stage puts the
collector's algorithm under the model. scripts/fuzz-heap-gen marks random
heaps -- references in range and out of it, objects already marked as a
young collection finds them, stacks too small to finish -- with ACL2's
hpg-drain and with the generated code, under gfortran and flang (make
check-vm-gen); its control, an object's last slot left unread, is caught.

**Stage 1b, the sweep, generated (2026-10-09).** model/heapsw.lisp: the
frees a sweep and a young collection make, and the sweep over each pool.
An object freed has its finalizer asked for (a native array's buffer, a
regex handle: the runtime's, a write to h-ofin), its kind cleared, and
goes on the free list; a run's words go back on their size class's free
list through the first word's third field, as slab_push did, its place
and length cleared, and the run on the run free list; a text's storage is
released (h-srel) and the text goes on its free list. Guard-verified,
with two total helpers where a word read from one array is stored in
another or used as a place (hpg-s64, hpg-n40): the identity on what the
runtime holds, and what lets the guard proofs see the bounds.
model/heapsw-proof.lisp proves the sweep frees EXACTLY the slots neither
marked nor free (objects, runs, texts), never writes an object's slot,
keeps a marked object's kind and a marked run's place and length, and
writes no arena word but the first of a run it frees (`no-start`): with
hpg-drain-closed, what the roots reach is marked and the sweep changes
none of it.

GC.f90's sweep, free_obj, free_vec and free_str are the generated
hpg_sweep_* and hpg_free_*; GC's counts (live, swept, frees, live arena
words) are taken from the model's where they are read. The translator
learned extern scalar fields (the free lists' heads are GC's variables),
folds a comparison with a literal past 64 bits, and writes the least
64-bit integer as an expression (it has no literal). The young
collection's sweep costs ~6% more than the hand-written one (77 against
71 ms over a run of three yardsticks); the yardstick does not move
(849-866 ms against the previous build's 875-878, the same machine).
scripts/fuzz-heap-gen now sweeps after marking, from free flags, free
lists, class heads and arena words of its own, and compares everything
the sweep wrote.

**Stage 1b, allocation, objects (2026-10-09).** Before it, a probe of
which slots each object kind uses (CLOTRAN_STATS, scratch): the
yardstick's lazy cells (9.1 M allocated over three runs) and closures
(3.0 M) use all five slots -- a lazy cell changes shape in place, pending
to realised, and iterate keeps its x in slot 5 -- so sizing objects to
their kind (stage 1d) would save about a third on them, not the 2-3x
this plan supposed; 1d is worth less, and the allocator as it is was
modelled.

model/heapal.lisp: a slot from the free list's head or past the used end
(obj_take without a batch); with batching, the thread's batch filled
from the list and the used end, each slot from the end flagged free while
it waits, and its last taken; and USE, what gc_obj does to a slot handed
out. model/heapal-proof.lisp proves NO SLOT IS HANDED OUT TWICE, over a
ghost list L, the free list's slots, and B, the batch's: L runs from the
head through the links to 0, every slot of L and B is free and at most
used, and L and B together hold no slot twice. A take hands out L's head
(the list its rest) or the slot past used (on neither); a pop the
batch's last; a fill moves slots from L's front or past used into B (a
witness, fill-rest, says which); use of a slot on neither keeps the
invariant; and the sweep's free of a slot not free puts it on L's
front. GC.f90's obj_take is the generated take, fill and pop (the
thread's own young dead still go into its batch by the hand-written
pend_refill_obj); gc_obj's in-line pop on its fast path stays as it was
-- the generated pop reads the thread's batch through an accessor that
finds the thread each time. The accessors' pool lengths are now the
pool's size, which allocation needs and the marking and sweep accept.
scripts/fuzz-heap-gen runs three takes, a fill and four pops after the
sweep, on both sides. Runs, texts and the arena's slab allocator take
the same shape next.

**Stage 1b, allocation, vectors and texts (2026-10-09).** vec_take and
str_take were obj_take's text with the names changed, so the model says
so: heapal.lisp and heapal-proof.lisp are each ONE text over a pool, @
its letter and % its name (h-@head, hpg-%-take), instantiated for
objects, vectors and texts by a macro that renames the symbols. Every
definition and theorem above now holds of all three pools; only the
sweep's free differs per pool (a finalizer, a run back to the arena, a
text released), so hpg-free-obj-safe, -vec-safe and -str-safe are
written out. GC.f90's vec_take and str_take are the generated take,
fill and pop, as obj_take is, and the vector and text accessors' lengths
are the pools' sizes. scripts/fuzz-heap-gen allocates in all three pools
after the sweep; skipping the vector fill or the text fill in its driver
is caught. The yardstick does not move (~857 ms). Next, the arena: the
size-class runs (run_take, runs_fill, slab_alloc).

**Stage 1b, allocation, the arena's runs (2026-10-09).** model/heaprn.lisp:
a vector's run of 2^(c-1) words for its size class c, from the class's
free list (linked through the first word's ival, as hpg-slab-free left
it) or fresh past the arena's used end if it fits; with batching and
classes 1 to 8, through the thread's batch of 64 per class, filled when
empty. A run that does not fit is 0, and GC.f90 grows the arena with the
world stopped and asks again. heaprn-proof.lisp proves, per class over a
ghost free list and a ghost list R of every other class's free and
batched runs, that RUNS ARE APART: what run_take hands out lies inside the
used arena and overlaps no run still free or batched in its class or in
R (hpg-run-take-safe); taking keeps every other class's invariant
(hpg-run-take-other); and the sweep's free of a run apart from all free
runs puts it on its class's list and keeps every class's invariant
(hpg-slab-free-safe, -other). Intervals, not slots: the invariant is
pairwise apartness of (off . len) pairs, and the proof is layered --
run-new, push, pop, fill, from-batch, take-c, take -- because one theorem
over run_take's composition split past 150 cases. Two small changes to
the model for the proof: run-pop does not pop an entry that is not a run
(a batch never holds one), and run_take is three functions. GC.f90's
run_take is the generated one; runs_fill and slab_alloc are gone, the
arena's growth kept as arena_grow; gc_vec's in-line batch pop on its fast
path stays hand-written, as gc_obj's does. One latent bug the model
caught: a vector longer than 2^29 has a size class past class_head's 30,
which the hand-written slab_alloc indexed out of bounds; the model takes
no list for it, only fresh arena. scripts/fuzz-heap-gen makes up to eight
run takes after the pools' allocations; forcing batching off in its
driver is caught. The yardstick does not move (~866 ms).

**Stage 1b, the cost theorems (2026-10-09).** The heap books landed with
correctness theorems and no cost theorem, which the rule (every model
algorithm gets a step-count bound; James, 2026-10-04, and again today:
"have cost theorems for everything moving forward") does not allow.
model/heap-cost.lisp counts steps as vm-cost.lisp does -- each count
follows its function's own recursion over the function's own state, a
turn a constant number of array reads and writes -- and proves: a take,
pop or use in any pool is one step; a pool's batch fill at most fuel
turns and at most the batch's room; a sweep of slots i .. n exactly
n+1-i turns, a vector's free at most 41 steps more (its size class); a
size class at most 41 doublings, a run length at most 63; the arena's
batch fill at most 64 turns; run_take at most 170 steps; an object's scan
at most its five slots, a run's at most its length; and THE DRAIN'S WORK
AT MOST ITS STARTING POTENTIAL -- each stack entry and each unmarked
object (6) or vector (1 + its length) carries its scan cost, a push only
moves a cost from the unmarked reserve onto the stack, and a turn does
at most its popped entry's cost (hpg-drain-is-dstep ties the counted turn
to hpg-drain). Marking is linear in the heap, each object and vector
scanned once; allocation is O(1) a slot and O(1) a run, a batch's refill
amortised over the batch; sweeping is linear in the pool. From here on a
model book is committed with its cost theorem, or not at all.

**Stage 1c, the young collection's soundness and the barrier (2026-10-10).**
A young collection marks from the roots and the REMEMBERED SET and stops
at the old: what the last collection left marked is neither cleared nor
scanned. model/heapgn-proof.lisp states when that is sound. YOUNG-START,
at a young collection's start: every marked object and run is black (all
it references marked) or remembered. From such a state, `young-inv`: the
roots pushed and the remembered objects and runs scanned (scan-objs,
scan-vecs) give the drain's invariant, so with heapg-proof's
hpg-drain-closed, `young-closed`: a drain that empties its stack with no
overflow leaves every marked object and run black -- what the roots
reach, through the old or not, is marked, and the sweep of the young frees
none of it. `barrier-keeps`: a write into an object's slot with its
barrier -- the object remembered when it is marked and what is written is
not -- keeps young-start. `young-cost`: the remembered set's scan is 5
pushes an object, proportional to what is remembered, not to the old.
model/heapgn.lisp's hpg-young-ref is the barrier's test, generated, and
proved equal to the proof's (`hpg-young-ref-is`); GC.f90's is_young -- the
test gc_set_slot and the vectors' writes ask -- is it, and collect_young
scans the remembered set with the generated hpg_scan_obj and
hpg_scan_vec. scripts/fuzz-heap-gen scans random remembered sets between
the roots and the drain and asks the barrier's test of random references,
ACL2 against the generated code; its control (a text's mark read inverted)
parts the barrier's answers. The yardstick does not move (A/B from source,
~900-930 ms both).

AGING, too (`aging-keeps`): a young survivor is aged rather than
promoted, its mark cleared, and that keeps young-start when every marked
object and run that references it is remembered. GC.f90 meets the
condition in two places, read against the theorem: collect_young
remembers each newly promoted object that points at an aged one
(any_aged_slot, any_aged_run), and forget_young keeps in the set every
remembered entry that still does -- the old ones were remembered by the
barrier while their target was young, which barrier-keeps covers. Their tests --
does this object's slots, this run's words, reference anything aged --
are generated now (model/heapgn.lisp's hpg-obj-refs-aged and
hpg-vec-refs-aged over two new stobj arrays, the aged flags), and
heapgn-proof's obj-refs-aged-finds and vec-refs-aged-finds show each
finds every reference aging-keeps needs remembered; GC.f90's
any_aged_slot, any_aged_run and forget_young call them, and
scripts/fuzz-heap-gen asks them of random heaps with random aged flags.

### 34. Dispatch and the calling convention, timed (decided 2026-10-09)

**Why now, ahead of stage 33's 1c-1e.** The yardstick's account
(`sample` over twelve runs, bucketed): of its 862 ns an element, 65% is
the interpreter's dispatch (flat_run's own loop 38%, frames, calls,
call tables, argument passing), 14% lazy cells and seq operations, 13%
allocation, 3% the collector, 1% arithmetic. A free allocator would buy
~130 ns; the dispatch holds ~560. James: make dispatch and the calling
convention the next stage, and "include timing in your proofs".

**What an element is** (CLOTRAN_STATS, less an empty program): 45 flat
instructions -- 15 moves, 6 branches, 18 calls (9 direct-linked builtins
`callw`, 3 builtins `callb`, 6 general, 3 of which open a frame and run a
Clojure body), 1 recur, 1 lazy -- 8 host seq operations (seq 3, first 2,
next, rest, cons), 1 lazy cell forced, and 4 objects (3 lazy cells, a
closure).

**Timing in the proofs.** ACL2 counts steps; time is steps by weights.
Each operation class carries a weight in ns; a cost theorem bounds WEIGHTED
work and holds for any weights; `scripts/calibrate` measures the weights on
the machine (non-negative least squares over designed loops, each adding
one kind of work, fit by relative error, the collector's pauses taken off)
and checks them against programs the fit never saw. A weight goes into a
claim only when it predicts those. CLOTRAN_STATS now counts flat
instructions by opcode, builtins by id (generic and in line), lazy forces,
and allocations by kind -- about 1.5% on the yardstick, the price of the
account.

First fit (2026-10-09): a frame's call and return ~25 + 45 ns, a host seq
operation ~64, an allocation ~32, a branch ~6, a builtin through callb ~8.
The fit set within 24%; held out, the yardstick within 18-30%, iterate 27%,
a hand-written lazy recursion 6%, a cons loop 1% -- but chunked map and
filter 500-1400% off: their per-chunk interop and `new` are one class here
and are not one cost. Not yet good enough to state a time; good enough to
aim. And a finding on the way: `integer?` costs ~196 ns and `even?` ~357
(pos? ~33), because core.clj's integer? is a chain of instance? checks
that clotran resolves at run time and clj's compiler inlines.

**Second fit (2026-10-09).** Interop (`dot`) and `new` their own classes,
loops for a chunk's .nth and a chunk buffer made, a fn called from the
host, the hand-written lazy recursion moved into the fit; a class the fit
set does not exercise is now pinned to 0 and named rather than left free
-- the first unpinned fit had put 161 us on a lazy force to soak up error.
Held out: the yardstick +7%, filter -8%, iterate +11%, map -15%, a
reduce with a Clojure fn -33% (the host's call into the fn is not yet a
class). Weights: a Clojure frame's return ~88 ns, a host seq operation ~64,
a var read ~36, an allocation ~34, interop ~21, a recur ~12, a builtin
through callb ~7, moves and branches ~0 beside them. Lazy forces are not
measured: the fit's forcing goes through flat_force in line, which
force_n does not see.

**In the VM, not flat (James, 2026-10-09).** Asked whether the cheaper
convention goes into the hand-written flat executor or the modelled VM:
"Put the convention into the VM model, obviously." Flat is what the VM
must beat; the VM is where the model leads and the JIT follows.

**The VM's account (2026-10-09).** CLOTRAN_STATS now counts the VM's steps
by opcode and its prims by kind. An element under CLOTRAN_VM=1, 1660 ns:
56 steps (15 load, 10 push, 12 prim, 4 jmpf, 4 ret, 3 callv, 3 capt, 2
slide, 2 jmp, 1 recur), 14 prims (7 callw, 4 values called through the
evaluator's apply, 2 deref, 1 evaluator node), 2 lazy cells forced by a
nested run. Sampled and bucketed: THE BOUNDARY 40% (~658 ns: vm_run's
entries, gce_apply_slots, dispatch's keyword compares, the call hooks),
the steps 22% (~356, ~6.4 ns a step), seq operations and forcing 15%,
allocation 10%, retention and the collector 10% (grow_obj and marking:
the VM keeps the seq's head alive where flat does not, 2.9 M objects
marked against 0.6 M). The generated step chooses its instruction by
SIXTEEN NESTED IFs -- ACL2's case translated literally.

**Order.** (1) the translator emits a case on an integer as `select case`,
a jump table: no model change, the proofs as they are; (2) the prim
convention in the model -- prims numbered when compiled and dispatched by
table, the seq operations on a realised cell answered without leaving the
machine -- with WEIGHTED cost theorems, generated; (3) entering the
machine (a nested run, a call from the runtime) without setup; (4) what
the VM keeps alive, found, and a dead slot proved cleared; (5) instance?
with a constant class answered at link time.

**Done so far (2026-10-09).** (1) The translator writes an integer case
as SELECT CASE; the plain step now is one, and the yardstick did not
move (the fused step tests its patterns first, and the chain of compares
was not where the time went). A call through a DIRECT-LINKED Var whose fn
only wraps a builtin is now that builtin's prim, resolved when the VM
translates the site -- the fn was fixed when the site was analysed
(DEVIATIONS 55), so its builtin is -- not a callw that derefs the Var and
looks the wrapper up every call: 7 callw prims an element went to 0, the
yardstick under the VM 1690 -> ~1420 ms.

**THE TIME THEOREM (model/vmx2-time.lisp).** The clock split by kind: the
machine's PRIM steps are at most x2prims, the prims the meaning evaluates
(s2pclk-prims -- the compiled code crosses the boundary no more often than
the language says), and for ANY weights ws and wp, ws x s2clk + wp x
s2pclk <= 2 ws x2evals + wp x2prims (vm-time-bound). Which steps are prim
instructions is read off the clock's structure, the :prim case's step,
the one the compiler emits as the prim (s2code-len's). `scripts/calibrate
-m vm` fits those classes -- each form run as a fn's body, since the VM
compiles bodies -- with the runtime's own work besides: a step ~13 ns, a
prim's extra ~4, a seq operation through a prim ~107, another builtin
~139, a force ~73, an allocation ~37; held out, the yardstick +16%,
iterate -4%, filter +15%, map -18%, a reduce with a Clojure fn -67% (the
runtime's call into a VM body, not yet a class). By that account the
yardstick's eight seq operations an element are ~850 of its ~1230 ns
under the VM: THE SEQ OPERATIONS ON A REALISED CELL, ANSWERED IN THE
MACHINE, are next.

**The seq operations, generated (stage 33's 2, 2026-10-09).** James:
model the seq and lazy-cell operations, then the JIT, then the heap's
1c-1e. model/heapsq.lisp: first, next, rest and seq of nil, a list and a
lazy cell already realised, as reads of the heap stobj (an object's kind,
its first integer field -- h-oi1, new -- and its slots), guard-verified
and generated into heap_gen.inc. The answer is a PLACE -- nil, the
argument, or the word 5o+k whose slot holds the value -- since a slot is
more than the tag and ref the model sees; the runtime copies that slot,
and nothing allocates. The operation is named by the runtime's builtin id,
so neither caller translates. Proved: a place answered is inside the pool
(hpg-seq-op-place); a lazy cell is read only realised, the argument's and
next's tail's (hpg-seq-op-realised: with lazy-cell.lisp's
done-reads-realised and realised-stays, why no lock is needed); seq
answers a cell itself only non-empty, and next its tail only non-empty
(hpg-seq-op-nonempty, hpg-next-tail-nonempty); at most 7 heap reads
(hpg-seq-op-reads), and that time at any weight a read
(hpg-seq-op-time). flat_seq_op's nil, list and lazy-cell cases are the
generated op (GC.f90's gc_seq_fast); the VM's one-argument prim of a
builtin asks it before the boundary (rt_prim1), 4.1 M of the yardstick's
seq operations answered there (CLOTRAN_STATS: the prims' new `seq`
column). scripts/fuzz-heap-gen asks random seq operations of every heap,
ACL2's hpg-seq-op against the generated one; its control (a delegating
cell read as pending) is caught.

WHAT IT DID NOT DO: the yardstick did not get faster -- flat ~2-4% slower
(the hot path is ~30 instructions with no calls; the rest is a call more
and the binary's layout: a loop with no seq operations moved by 1 ns too),
the VM unchanged at ~1420 ms though 4.1 M operations now skip dispatch,
vmrt_call and the call hook. So calibrate's ~107 ns "seq operation
through a prim" was not the layering: the regression put there the
forcing and allocation that go with them. Sampled under the VM, the
yardstick is about a third the collector and allocation (grow_obj and
marking: the retention above), a quarter the steps, a quarter the
boundary (gce_apply_slots, call_builtin -- instance? alone is 1.09 M
generic calls -- the hooks), and the generated seq op ~2%. Next, in
James's order: the JIT (stages 2-3), then the heap (1c-1e).

**What the VM keeps alive, found (2026-10-10).** With core compiled by
the VM (CLOTRAN_IMAGE=0), walking 3x10^6 elements marks ~5.8 M objects a
collection where flat marks ~0.6 M, the object pool grows to 8.4 M slots
against 0.26 M, and the run is 3-4x flat's (grow_obj alone is the largest
item sampled). Bisected: a hand-written lazy recursion walked by a loop
INSIDE a VM fn retains the whole seq; the same loop at top level (flat)
does not; dorun, reduce1 (the yardstick's `+`) and any `loop` do. THE
CAUSE is the translation of loops (vm.inc's vm_tr and vm_clause): a
`loop`'s bindings are bound by lets and the (:loop ...) starts from copies
of them, and a fn whose body recurs becomes (:loop ((:local 0) ..) body)
over copies of its parameters -- the originals, the lets' slots and the
parameters, hold the seq's head for the loop's whole life. Flat clears a
local at its last read (the analyser's liveness pass); the VM has no
instruction that can.

Tried and reverted the same day: scanning a VM run's window of the value
stack only up to its sp (the slots above are dead). It changed nothing --
the holders are below sp -- and rests on a property proved for the stage-1
JIT's machine, not for vmi.

THE FIX IS A MODEL CHANGE, and the design: a loop over locals that
already exist, (:loopl n body) -- the body run with the env's last n
locals as the loop's, recur copying down to them -- so a let-bound loop
and a recurring fn need no copies at all, rather than copies and a clear.
Its meaning is :loop's with those values; its code is :loop's without the
inits. What it breaks is vmx2-proof's central invariant, "nothing below
the expression's start is changed": recur now writes slots below the
loop's own start. The invariant becomes "nothing below the start less the
locals the expression owns" (a let owns its slot, so the let around a
:loopl still preserves everything below itself), threaded through
vcs2-good's every case, then vmi, vmic, the generated step and compiler,
the fused patterns and the JIT's blocks. Several days of proof, not a
night's: the next item for step 34.

A complication found reading the compiler (vcs2-body): a clause's frame
is its arguments and then ITS CLOSURE (slot n, which :capt reads), so a
recurring fn's loop over its parameters has a live slot above its
locals, and recur sets sp to just past the locals it writes -- it would
drop the closure. So the recur of a :loopl needs its own stack top,
(:recur k b l d) with sp := fb+d, or the clause's loop takes the closure
as one more local. The let-bound loop (a loop's bindings) has no such
slot above and needs only :loopl.

**The let-bound loop, fixed without a model change (2026-10-10).** When no
binding of a loop reads one before it -- the common case, and every loop
the fuzzer generates -- the translator now writes (:loop (init ..) body)
with the inits themselves, as vmx2 has always allowed, and no lets: there
is no slot beside the loop's to keep a head (vm.inc's vm_loop_indep and
vm_reads_in, a scan of the inits that counts any node kind it does not
know as a read). A loop walking 3x10^6 elements inside a VM fn: 4.45 M
objects marked -> 0.87 M, the pool 8.4 M -> 0.26 M slots, 2.8 -> 2.25 s.
Loops whose bindings read earlier ones keep the let translation, and a
fn that recurs (dorun, reduce1) still holds its parameters: those need
the model change above.

**instance? in place (2026-10-10).** Under the VM the yardstick asked
instance? 1.09 M times through the generic builtin call (chunked-seq? in
reduce1). It is now an in-place case beside cons (flat_cons_op: a class
and any value, is_instance as call_builtin answers it; anything else the
builtin's, which throws): the generic calls 1.09 M -> 10, the yardstick
with core compiled by the VM ~1387 -> ~1327 ms. Flat with the heap image
never asked it per element, and does not move. Not yet the item as
planned -- the class constant answered when the site is linked.

**What the recurring-fn fix would buy, measured (2026-10-10).** The
yardstick three times, core from source (CLOTRAN_IMAGE=0), CLOTRAN_STATS,
less a run with no yardstick: collector pauses per run ~17 ms flat, ~165
ms VM (marked 5.8 M against 0.62 M, pool 8.4 M slots against 0.26 M). So
the :loopl change's direct ceiling on the yardstick is ~150 ms of the VM's
~1400 (~10%), plus the unmeasured pool growth -- VM+JIT ~1200 -> ~1050,
still behind flat's ~900. The larger share is the boundary: per run 21 M
calls of a value that is not a builtin, 12 M seq ops, 3.1 M evaluator
nodes (vm_prim_n). So for the yardstick the calling convention (step 33
stage 3, JIT stage 3) comes first; :loopl is a space fix first (a long
dorun/reduce in a VM fn holds the whole seq). Next session: choose
between them.

**CLOSED (2026-10-10): the yardstick is not where the design went wrong,
and it is not the next work.** James asked whether we had done something
wrong. Measured, so the next session does not re-derive it:

THREE EXECUTORS, ONE NUMBER. Flat 915 ms (image; 940 from source), the
generated VM 1410-1650, VM+JIT 1250-1350, and core compiled ahead of time
to Fortran 1440 (10-07). Removing dispatch entirely did not move it, so
dispatch is not the cost.

THE PARTS, ms per 10^6 elements, flat with the image against clj:

| form | clotran | clj |
|---|---|---|
| empty `loop` | 28 | 1-2 |
| `(nth (iterate inc' 0) n)` | 97 | 23-30 |
| `loop` calling `next` on `(range)` | 258 | 30-33 |
| `(dorun (take n (range)))` | 790 | 50-59 |
| `(apply + (take n (range)))` | 915 | 56-87 |

The empty loop is the dispatch floor, ~6 ns an instruction: the 45
instructions an element are ~270 of the 915 ns. The other ~650 is the
runtime -- a force from interpreted code is ~230 ns against 97 for the
native walk, and the take layer alone is ~690 an element: one closure
body plus the force chain around it (flat_force, push_frame, k_push, the
trampoline's re-entry, k_finish, force_settle, flat_release). The
line-level profile (xctrace, dSYM) agrees: flat_run's own 22-40% is spread
over its handlers, the hottest 256 bytes of it 10%, and the other 60% is
forty helpers at 1-4% each. The collector's pauses are 2% (26 young
collections, 18.8 ms). Per element: 45 instructions, 4 objects (3 lazy
cells, a closure), 3 continuation pushes.

A FAIR INTERPRETER. `take` and `reduce1` written in plain Clojure and run
under babashka, so sci interprets exactly what clotran interprets: 300-385
ms. clj with the same definitions: 58-84. A mature interpreter is ~5x
behind the JIT on this form, and clotran is ~2.8x behind that
interpreter. (bb's stock 60-137 ms is its compiled core, not sci.) The
floor for a polished interpreter on this design is therefore ~300-400 ms;
clj's 60-70 needs an inlining JIT with escape analysis and bump
allocation, a different class of system.

THE MODEL, REVIEWED. `prim` is unconstrained, so the step and time
theorems bound the ~25% that is the machine; the VM is a second executor
beside flat and its 40% boundary exists only because of that, and with
the image on, VM mode runs core as flat anyway; the heap books verify the
layout GC.f90 has (five slots, 96 bytes a cons) and found a real
out-of-bounds, but each generated stage landed 0-6% slower, never faster;
and the stages that would move the number (the nursery, the convention,
a lean force) are the ones the hand-written runtime's `roots(:)`
convention blocks. 28.6k lines of ACL2 produced a VM 1.5x slower than the
executor it was to replace. The model stays the correctness oracle for
what it generates; it is not a road to this number.

DECIDED (James, 2026-10-10: "that is a fair point about the speed ... let's
do your plan"): the single yardstick is retired as the north star --
scripts/bench now times the five parts and step 13's forms, with a bb
column; `:loopl` stays a space fix, noted, not next; the VM's calling
convention, the moving nursery and JIT stages 2-3 are not next. The speed
work is step 13, the pure-Fortran tier, where a Fortran host wins
outright; then step 24's thread pool and step 21's remaining pieces.

### 35. v1.0: the language as the smallest package (decided 2026-10-10)

James, 2026-10-10: "I want the most minimal of package for the root
language. Something where simply deps can be pulled in to build
everything else." Other projects use their own `deps.edn` plus
clotran's, and are themselves a basis for further packages. "We're
language designers right now": the editor work (step 21's CIDER
debugger, LSP, DAP, tree-sitter, an MCP server) is not on the v1.0
menu; nor are the JIT and VM speed work or step 32. "Work towards
everything keeping the windows port last."

**Where the language stands, measured 2026-10-10:** the derived suite
(Clojure's own tests over the clojure.core/cljs.core intersection plus
concurrency) is 39 namespaces, 312 tests, 2719 assertions, 0 fail, 0
error, every namespace executing; the five portable libraries run
verbatim at 859 of 859; the oracle agrees on 1184 forms with 24
expected differences, each a DEVIATIONS entry. VERSION is 0.1.0.

**What v1.0 is, in order of work:**
1. *The ledger.* Every DEVIATIONS entry says RESOLVED, by design, or a
   host limit. Audited 2026-10-10, entry by entry: 25 resolved, 29 by
   design, 6 host limits (4, 5, 12, 14, 28, 52), and 20 that still read
   as temporary or open -- 2 (host.clj before core.clj), 3 (symbols
   fall back to clojure.core: a refers map), 6 (syntax-quote at
   analysis time), 10 (`set!` of an unbound Var sets its root), 17
   (deftype's short name global: a per-namespace import table), 19
   (recur in a deftype method passes this), 20 (mutable deftype
   fields), 23 (fns are not IObj), 32 (an unresolved qualified symbol
   is a run-time error), 36 (`binding` accepts a non-dynamic Var), 42
   (`s/check-asserts`), 47 (all-ns lists host classes), 48 (the
   compile-time half of type hints), 51 ("Divide by zero" wording), 54
   (a slash inside a namespace), 60 (a deftype's hash asked once), 62
   (an array of references has no element class), 68 (an uncaught
   error reported as a load failure), 74 (the nil key walked by hash).
   Probed against clj and the binary on 2026-10-10 (every entry, one
   probe each): 47 no longer deviates and is resolved; the rest still
   do, and 19, 32, 36, 42 and 62 described their own behaviour wrongly
   (42 had turned from a throw into a silent no-op) and are corrected.
   The order to resolve the rest, cheapest by each entry's own removal
   sentence: 36 (DONE 2026-10-10), 42 (DONE), 23 (DONE), 10 (DONE), 19
   (DONE), 32 (DONE, for a user's code), 62 (DONE), 68 (DONE), 17 (DONE), 3 (DONE), 60 (DONE), then 48, 6, 2 -- each in its own gated
   commit, or reclassified by design with the reason. Three are
   reclassified on 2026-10-10 as staying through 1.0, each entry saying
   so: 54 (a namespace with a slash in it needs a boundary stored beside
   every symbol's and keyword's interned text, for names clojuredocs
   calls non-conformant), 51 (an error string clj picks by its static
   types -- "/ by zero" for primitive operands, "Divide by zero" for
   boxed -- which needs the compiler's type inference in the analyser to
   choose a message), and 74 (the nil key's place in a hash map's walk,
   a change to the trie and to model/hashseq.lisp's theorem for the
   order of one key). Also found and fixed by the gate's fuzzers while
   working this list, each in its own commit: the compiled long cast at
   exactly 2^63, the ## reader's message inside #(...), rationalize of
   ##-Inf, and a shutdown-agents race (step 24). The table at the
   top said "host" for 7, 13 and 15 where their prose says resolved;
   18, 23, 25, 26 and 15/22 cited entries since resolved; 56/61 and
   57/63 are duplicates -- fixed. A v1.0 ledger has no scaffolds and
   no stale sentences.
2. *Mutable deftype fields* (DEVIATIONS 20) -- DONE 2026-10-10: the
   analyser keeps the method's field table and routes a mutable field's
   reads and writes through `this`; clj's rules measured and matched
   (a loop and a let may set it, a fn made in the method may read but
   not set it, an immutable field is refused, a mutable one is private);
   the oracle's Tally and Shadow, the language test's refusal, and
   scripts/fuzz-deftype in the gate, 30 of 30 with clj. The residual:
   the refusal comes at the method's first run, where clj's comes
   when the type is defined, since a body is analysed when first run.
3. *Step 15's tail*: raw bytes to and from files, each item against
   clj; bit-set, bit-clear, bit-flip and bit-test checked rather than
   assumed.
4. *The install.* `make install PREFIX=`: the binary, the image, the
   core sources and the launcher. The launcher resolves a project's
   `deps.edn` by calling `clotran-deps`, shipped beside it as the
   `clj` script ships tools.deps, so nobody sets `CLOTRAN_PATH` by
   hand; `clotran new` writes a `deps.edn`. The optional tools
   (clotran-nrepl, clotran-mode, later the generator's output) are git
   coordinates in a project's `deps.edn`, pinned by sha, never in the
   binary. The sibling repositories stay local until James says.
5. *The version.* VERSION 1.0.0, the pinned Clojure release named, a
   stated policy for what a minor and a patch may change (DEVIATIONS
   entries, the ABI, the package format).
6. *Windows*, last: the mingw build under Wine as the quick check, a
   real runner as the authority -- or 1.1, named as such.

**Said plainly in the release notes:** the speed as the README states
it; the debugger as it is (calls, one level); interop as
`call-package*` and hand-written bindings. The Fortran binding
generator (step 7) is the first thing in 1.x, so 1.0 waits on nothing
but the language.

**1.x, noted now (James):** tree shaking, Fortran and Clojure both,
so an experiment links to a tree-shaken source and its binary and is
reproducible by construction -- the AOT road of step 12 and the image
already know what a program reaches.

### 29. Fuzz everything (begun 2026-10-02)

James: "fuzz everything at this point and going forward". The rule
is in CLAUDE.md ("Every feature gets a fuzzer"). This step covers the
features that came before the rule. Each row of the table gets a
generator, an oracle that decides, and a `make` target. Each row is
done when its fuzzer is green and its seeded run is in `make test`.

| feature | fuzzer | oracle | state |
|---|---|---|---|
| evaluation: let, loop, closures, try, seqs | scripts/fuzz | clj, 3 modes | green, in make test |
| core functions, by spec | scripts/fuzz --fns | clj, :ret | green, in make test |
| frames: breaks and traces | scripts/fuzz-frames | clj, the generator, 3 modes | green in flat and tree, and compiled traces, in make test (check-frames); compiled BREAKS show no frames until the debug build (step 10's decision) exists |
| frames: file and line | scripts/fuzz-frames | clj's trace elements, the generator | green, same scope (James, 2026-10-02). Found: a trace element gave the line its frame was called FROM; compiled frames had no lines, and install read each fn from a string, at line 1 |
| the package door | scripts/fuzz-door | model/boundary.lisp | green |
| data-structure costs | scripts/bigo | clj's bounds, model/ | green (measures, does not generate) |
| the reader on MALFORMED text | scripts/fuzz-read (generated source, mutated: characters deleted, inserted, swapped, cut) | clj's read-string: the value, or the error by class and message | green, in make test (check-fuzz-read). Found: \\ did not end a token, nor # ' % a number; \\NNN was not an escape; ^meta took a string, number or nil; a key twice was kept; #() nested; a #_ form's error was overwritten by the next; every message was clotran's own, and every class RuntimeException. DEVIATIONS 6, 14, 46 and 75 not compared |
| the reader and the printer | scripts/fuzz-print (test.check any-printable-equatable) | clj: the literal read, pr-str, print-str, str, read back | green, in make test (check-fuzz-print). Found: a collection's str did not print through print-method or *print-namespace-maps*; the #tag scan lost its seq under GC |
| numbers: the tower, overflow, ratios | scripts/fuzz-num | clj: value and class of one op on any two kinds | green, in make test (check-fuzz-num); documented deviations (26, 27, 43, 69, 70, 71) not generated. Found: a float printed as its double; (int hugeN) answered 0 and unchecked-int lost the low bits; bit-not took a BigInt; quot and rem of doubles were not clj's formulas, and gfortran fused n - q*d (now -ffp-contract=off everywhere); a ratio with a double took the ratio path; a decimal quotient lost its scale; compiled (int x) boxed as a long |
| strings and regex | scripts/fuzz-str | clj | green, in make test (check-fuzz-str); DEVIATIONS 14 and 41 not generated. Found: ICU loops forever on a lazy *? or +? over what can match empty (regex_shim.c compiles {0,}? and {1,}?) |
| collections under random op sequences | scripts/fuzz-coll | clj: value, count, seq order, hash | green, in make test (check-fuzz-coll). Found: a hash map or set replaced the key it held with an equal new one; a nil key walks out of clj's order (DEVIATIONS 74); a lazy seq of lazy seqs was unwrapped recursively, a frame per element; a library's manifest was built by 10^4 concatenations, half an hour in gfortran |
| GC and the heap image | scripts/fuzz-gc (every generator collecting every 3, 17, 1009 allocations, and noimage) | clj | green, in make test (check-fuzz-gc). Found: data-structure code calling back into the evaluator (key equality, hash, a comparator) held its map unrooted -- under GC the reader lost keys, destructure, ns and spec failed, and spec loaded 42 definitions short, which was then marked loaded |
| spec itself: generated spec forms | scripts/fuzz-spec (its forms checked by a spec of spec forms) | clj: valid?, conform, unform, explain-data, form; 4 modes with torture | green, in make test (check-fuzz-spec). Found: a fn's class name carried no name (spec's fn-sym); (empty m) of a HAMT was nil; a deftype could not name itself in its methods, and its equals, hashCode and compareTo were not consulted; UUID was a record, so a map; scripts/fuzz showed a failing case's answer from a solo rerun. Spec's own nested quantifiers are exponential, in clj too |
| the specs of fuzz_specs.clj | scripts/fuzz --fns | each :args generator conforms to its :args; every fdef has a :ret | green, in make test (check-fuzz) |
| typed functions, compiled | scripts/fuzz-fn (generated defns: ^long and ^double parameters, return hints, primitive locals, loops, calls between them, as scripts/fuzz --fixture) | clj, 3 modes; called directly, through apply, and with a double for a long | green, in make test (check-fuzz-fn) |
| macros: destructuring, threading, conditionals, ns forms | scripts/fuzz-macro | clj, core.specs | green, in make test (check-fuzz-macro). Found: nth took a keyword, so (let [[a b] :k] ...) answered nil nil. ns forms: :require with :as, :refer and :rename, :refer-clojure :exclude; not :import, whose host names the oracle cannot translate inside (package Class) |
| threads, agents, STM | scripts/fuzz-threads, and in fuzz-gc every 17 and 1009 allocations | clj: final values; invariants (the refs' total kept) | green, in make test (check-fuzz-threads, check-fuzz-gc); a deadlock is a TIMEOUT, and a batch that hangs only whole is a BATCH-TIMEOUT. Found: dosync took its lock still counted as running, so a collection waited for it forever; apply's rest seq was unrooted, and with another thread allocating an agent's action saw nil args -- sends lost |
| the compiler (tier A, purefort) | scripts/fuzz-pure through scripts/pure-check | clj and the interpreter, gfortran and flang | green, in make test (check-fuzz-pure). The full compiler (clotran compile) is fuzzed by every generator's compiled mode |
| the heap image | scripts/fuzz-gc's noimage mode | clj | green, with GC above |
| sockets and the REPL over one | scripts/fuzz-net (through nc, as embed-repl-check) | byte equality; clj for each form through io-prepl | green, in make test (check-fuzz-net) |
| the package door | scripts/fuzz-door | model/boundary.lisp | green |
| packages from generated Fortran | scripts/fuzz-bind (bind-fortran, gfortran and flang) | what the generator computed | green, in make test (check-fuzz-bind). Found: the door carried no integer(8) array, though bind-fortran binds them |
| the package manager | scripts/fuzz-deps (clotran-deps on generated graphs, local and git; and malformed deps.edn, fixed shapes and mutated text) | a model of PACKAGES.md's rules; each library loaded from where it was chosen; for a malformed file, clj -Spath's verdict and path | green, in make test (check-fuzz-deps). Found: clotran-deps took a deps.edn of the wrong shape -- :deps a vector, :paths a string, a root that is not there, text after the map -- and answered a path built from nothing |
| all of the above | scripts/fuzz-all (make fuzz-all: full size, hours) | each fuzzer's own | a scorecard: pass, FAIL, TIMEOUT, SKIP |

Every check draws a fresh SEED each make (`make test SEED=n` repeats
one), and errors compare by class and message, less what only clj's
host says. The first gates on random seeds found, besides the rows
above: a lazy seq hashed by identity (DEVIATIONS 35, resolved), which
also lost the compiler a pooled constant; a ##NaN constant compiled to
Fortran that does not build; arity errors named every nested fn "fn";
createAsIfByAssoc refused a trailing element clj conjs; (+ x) refused
nil.

Spec under GC torture is the first lead: `s/cat` answers wrong under
torture when core is loaded from source (found 2026-10-01). Finding it
is a target for the "spec itself" and GC rows.

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

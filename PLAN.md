# Plan

What we are about to build, what we decided not to, and why. NOTES.md
records how things came to be; this records where they are going.
Rewritten 2026-09-19 after a review of the whole tree; the previous
plan's decision records that still hold are kept at the bottom.

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
JVM-shaped `case` arms in one file.

## Where we are (measured 2026-09-21)

| | |
|---|---|
| core.clj | 724 of 724 forms load |
| our tests | 100% on both compilers; the gate. 797 oracle cases value-compared against `clj`, 15 expected differences |
| the derived language suite | 39 files, every file loads, 324 tests execute: 2825 pass / 35 fail / 5 error, so 98.6% of assertions that EXECUTED (2170 / 235 / 370 on 2026-09-19). Three metadata tests no longer execute: they enumerate the publics of fifteen namespaces including clojure.java.browse and clojure.java.shell, which do not exist here, and ran vacuously while `find-ns` invented namespaces. What remains is named, not chased: 26 spec-conformance messages (special, fn), 4 JVM-only (compilation), 3 non-ASCII whitespace in byte strings (string), 2 class printing (protocols, DEVIATIONS 34), 2 boxed-math warnings (numbers), 2 `apply` realising a million elements (vars, DEVIATIONS 37), 1 `1.0M`/`1N` (transducers, DEVIATIONS 26) |
| libraries loading | 25 of 25 vendored libraries `require` (clojure.set, string, walk, zip, data, edn, pprint, test, repl, main, math, xml, ...). Loading, not running: reflect, inspector and core.server load because nothing touches the host until a call |
| Clojure's suite, verbatim (for reference) | 2029 pass / 143 fail / 246 error over 351 tests, 84% of executed (1810 / 219 / 1396 on 2026-09-19); 34 of 66 namespaces produce a passing assertion. The rest is the JVM: rt, array-symbols, java-interop, serialization, reflect, streams, clearing, param-tags, method thunks and the generated adapters; and the suppliers (delays, atoms), BigInt and BigDecimal (vars, logic, pprint), and spec |
| startup | 0.75s (7.2s before step 4, 2.3s at the start of stage 2), core.clj re-read every launch |
| `(reduce + (range n))` | LINEAR since step 4: n=100000 in 0.16s, ~1.6 µs per element through the host's own IReduceInit reduce (17s and 170 µs at the end of step 4). Before: n=16000 took 161s and n=100000 did not finish in 15 minutes |
| `loop`/`recur` | ~1.7 µs per iteration, linear; a function call ~1.3 µs. `scripts/bench` has the JVM ratios: 23x to 514x depending on the form. Seqs are chunked, as on the JVM |
| memory | 168 MB after core.clj; recursion 100,000 deep works |
| Fortran library calls made through clotran | `fortran/dgemm` (reference BLAS) and ChemSol's `readopt`, `dg_ld`, `solvout`, `entropy`; `examples/chemsol.cljf` reproduces the original program's output byte for byte on its three reference inputs (`scripts/chemsol-check`) |

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
`host_super`) holding 57 `clojure.lang.*` and 36 `java.*` names. Each
new JVM member is a few hundred lines of Fortran and a rebuild.

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
  `scripts/derive-tests` computes the intersection of the public names
  of `clojure.core` (the vendored source and its siblings) and
  `cljs.core` (the pinned ClojureScript clone): 470 names, the
  language. It classifies every `deftest` in the vendored tree by the
  symbols it uses -- LANGUAGE if they all fall inside that set plus the
  special forms, the portable libs and a short exception allowlist;
  CONCURRENCY if the only outsiders are refs, agents, futures and STM
  (Clojure-only, but goal 3); HOST otherwise (a Java class, a member
  call, a constructor, a clojure.core name ClojureScript never had) --
  and writes the kept tests to `test/clj/derived/` with the source
  file and line of each. Of 578 deftests it can read, 306 are language,
  8 concurrency, 264 host; 7 files it cannot read at all (method
  values, param-tags, record literals) are all JVM-shaped. A helper a
  kept test needs travels with it; a test whose helper is host goes
  with the helper; a top-level form with a head nobody defines
  (test.check's `defspec`) goes; a require of a non-portable library
  goes and so does everything it referred; a symbol nothing defines
  makes its test host, where "defines" is approximated by the
  binding positions of the form (its vector literals, `catch` names,
  `as->`), so `(vector-of :int)` and `(doc x)` are recognised as the
  JVM's without a list of them. The two hand
  lists it does contain, the exception allowlist and the concurrency
  vocabulary, are printed by `--report` so they can be argued with.
  `scripts/run-clojure-tests-parallel test/clj/derived` runs it.

The scorecard is now the pass rate over the derived language suite,
with the denominator stated -- see "Where we are".

### 3. Freeze host-member work; one table, as data -- DONE

`src/f/hosttable.inc` is the JVM surface: 293 static rows (class,
member, builtin id or constant) and 139 instance rows, as Fortran
`parameter` data. `static_member`, `instance_member` and
`is_host_class` are three lookups over it, so the class list and the
member list can no longer disagree, and a bare class name is
canonicalised once (`java.lang.` added, the libs' short imports
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
JVM libraries' sake). Measured against the step-4 numbers:

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
   JVM ratios. Still to do in this
   stage: intermediates move to the operand stack; `roots(:)` leaves every
   signature; module globals move into a context type; source
   positions on nodes.
3. snapshot the heap after core.clj and start from the image. The
   baseline after loading core.clj is 152 MB; a 100000-element reduce
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
(core.clj's `slurp` is written over `java.io`).

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

**Building one.** `scripts/bind-fortran` reads the Fortran sources'
signatures (explicit interfaces, `intent`, rank) and writes the shims,
the manifest and a Makefile fragment that builds the library with
`-shared -fPIC`; a hand-written binding (ChemSol's, with its unit-44
and unit-43 handling) is a shim like any other. A package manager is
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
which the JVM reader also accepts (`.-` since Clojure 1.4), so code
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
`:default` branches taken; `.clj` is JVM Clojure, loaded as written
because that is the premise. `require` looks in that order.
DEVIATIONS 33.

**A thread is an evaluator context; the kinds of thread are impls of
one protocol.** Three things not to conflate: `fork` is a process,
a green thread is a context the runtime multiplexes on one OS
thread at points it chooses (Erlang, Go, Java virtual threads,
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

Java's virtual threads (Loom) are this model and show where the work
has to go: executors and pools were always a library, but a thread
that parks and resumes needed the runtime, because only the runtime
can capture its stack. Here the context type is the host's part and
the protocol and impls are a library in clotran. Copy Loom's rule
about blocking: `deref` of an unfinished future, a mailbox `receive`
and a subprocess wait yield to the scheduler, so pipeline code is
straight-line Clojure. The limit: on one OS thread a blocking
Fortran call (dgemm, ChemSol's dg_ld) holds every green thread until
it returns; carrier threads are the `:os` impl. Clojure itself has
not moved: at our commit Agent.java builds soloExecutor with
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

**RESOLVED: `class` and a class literal answer the same keyword.**
`(class "a")` and `String` are both `:String` (`class_name_of`,
`class_key`); the tag stays behind `clotran-type`; `host_super` is
keyed by class name; `import*` records short names. The derived suite
did not move (2164/241/370 over 324 executed), the oracle gained
seven value-compared cases, and `pprint` got past `(condp = (class x)
String ...)` -- to a column-accounting bug of its own. DEVIATIONS 34.

**Where does the binding generator read type information from?**
Parsing `interface` blocks, or a declaration written in clotran.
Step 6 answers it with one example.

**Frames for every call, or only non-tail ones?** Pushing per call
measures as free, so this is about trace readability.

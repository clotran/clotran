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

## Where we are (measured 2026-09-19)

| | |
|---|---|
| core.clj | 724 of 724 forms load |
| our tests | 100% on both compilers; the gate |
| the derived language suite | 314 tests kept (306 language + 8 concurrency) in 39 files, every file loads, 324 tests execute: 2164 pass / 241 fail / 370 error, so 78% of assertions that EXECUTED. Fewer tests are kept than before the analysis pass because the deriver now treats a symbol nothing defines as host; the pass rate over what is kept is unchanged |
| Clojure's suite, verbatim (for reference) | 1810 pass / 219 fail / 1396 error over 357 tests, 53% of executed; 32 of 67 namespaces produce a passing assertion |
| startup | 4.1s (was 7.2s before step 4), core.clj re-read every launch |
| `(reduce + (range n))` | LINEAR since step 4: n=100000 in 17s net, ~170 µs and 60 evaluations per element. Before: n=16000 took 161s and n=100000 did not finish in 15 minutes |
| `loop`/`recur` | ~100 µs per iteration, linear |
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

### 1. Delete the retired evaluator -- IN PROGRESS

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
itself keeps the name, because it IS the GC. The binary is `clotran`
and `scripts/clotran` wraps it in rlwrap. Procedure prefixes (`gce_`,
`gcv_`, `gcl_`, ...) stay: they are short namespaces, and renaming a
few thousand call sites buys nothing until step 5 rewrites them anyway.

### 2. Decide what our test suite is, then derive it

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
2. intermediates move to the operand stack; `roots(:)` leaves every
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

Image for startup. Debugger over frames (the protocol below).
Threads over VM contexts (the concurrency decision below). JIT only
when a profile still demands it, and then jank's way -- LLVM IR in
process -- rather than generated Fortran text through a compiler.

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
;; handler returns :continue | :step-in | :step-over | :step-out | :abort
;;                 | {:eval form :frame 0}
```

Nothing in the evaluator may assume a terminal. Pausing into a nested
REPL is the model (Common Lisp `break`, SLDB); sockets are additive
later. Frames must record tail calls elided by `recur`, or a deep loop
shows one frame and the trace lies.

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

**Arrays are never ragged.** A Fortran rank-2 array is one contiguous
column-major block; `[[I` is nested and cannot be handed to BLAS at
any price. `(aget m 1)` is a strided view over the parent's buffer.
DEVIATIONS 24 and 25.

## Open

**`class` answers a type tag, class literals evaluate to a class
name, and they do not agree.** `(class "a")` is `:string`; `String`
evaluates to `:String`. `clojure.pprint`'s writers do `(condp = (class
x) String ...)` and miss every branch, which is the largest single
thing between clotran and a working `pprint`. Recommended: option 1,
class literals and `(class x)` both evaluate to the same class object,
the tag stays internal, and `host_super` is re-keyed in the step-3
table. Hazard: `(class x)` is a protocol's `:impls` key, so change the
table first and what `class` answers last, behind the language suite.

**Where does the binding generator read type information from?**
Parsing `interface` blocks, or a declaration written in clotran.
Step 6 answers it with one example.

**Frames for every call, or only non-tail ones?** Pushing per call
measures as free, so this is about trace readability.

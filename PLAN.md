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
| Clojure's suite | 1810 pass / 219 fail / 1396 error over 357 tests, so 53% of assertions that EXECUTED; 32 of 67 namespaces produce a passing assertion; none crash before reporting |
| startup | 7.2s, core.clj re-read every launch |
| `loop`/`recur` | ~100 µs per iteration, linear |
| `(reduce + (range n))` | n=4000: 22s. n=16000: 161s. SUPERLINEAR. n=100000 did not finish in 15 minutes |
| Fortran library calls made through clotran | 0 |

The reduce row is the one that matters and no scorecard sees it.

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
- **Runtime conformance, differential against `clj`.** One file of
  forms, run through `clj` and through clotran in one process each,
  values compared. This replaces hand-copied expected values in
  `test/clj/language_test.clj` and is the only kind of check that
  catches a silent wrong answer. `clj` is the oracle; bb never is.
- **Language tests derived from Clojure's suite.** Not 67 verbatim
  files with a hand-written exclusion list. The intersection of the
  public names of `clojure.core` (pinned clone) and `cljs.core` (pinned
  clone) IS the language. A `deftest` whose free symbols fall inside
  that set, plus `clojure.test`, is a language test; one that reaches
  outside it is a host test and is excluded. A bb script computes the
  set, classifies every `deftest` in the vendored tree, and emits a
  derived tree with provenance. The vendored files stay untouched, and
  the derivation re-runs on the next Clojure release. This removes
  `genclass`, `proxy`, `compilation`, `annotations`, `serialization`,
  `reflect`, `method_thunks`, `param_tags`, the `generated_*_adapters`
  files, `api` and `generators` mechanically. The intersection decides
  what to test; `clj` still decides the answer (ClojureScript has only
  doubles and different hashes).

The scorecard becomes: pass rate over the derived language suite, with
the denominator stated.

### 3. Freeze host-member work; one table, as data

No new `case` arms. The JVM surface clotran must READ (because core.clj
writes it) is finite: audit it against what core.clj and the vendored
libs we keep actually reference, and put it in ONE table -- preferably
declared in Clojure as data, the way `Integer/MIN_VALUE` already is --
with Fortran supplying only primitives. Anything in the Fortran not
reached by that audit goes. Settle the open class-versus-type-tag
question (below) in the same table.

### 4. Profile the superlinear reduce -- BEFORE step 5

`sample <pid>` on macOS names the path without a rebuild. Add
evaluation and collection counters per top-level form behind an
environment variable, and `System/nanoTime` so `time` works (it is in
the intersection: cljs has `system-time`). Instrument before
theorising. It is probably one pathology -- uncached protocol dispatch
(DEVIATIONS 13) or lazy-seq realisation -- and step 5 will not fix it
on its own.

### 5. The analysis pass, executed over explicit frames

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

1. analyser resolves and classifies; the recursive walker consumes
   nodes; read-one-form-at-a-time load rides along (DEVIATIONS 1);
2. intermediates move to the operand stack; `roots(:)` leaves every
   signature; module globals move into a context type;
3. snapshot the heap after core.clj and start from the image.

This reverses the previous plan's "Not a bytecode VM" decision. Its
two reasons -- the env chain as a name->value map makes eval-in-frame
free, and the AST node IS the source form -- are both answered: a
per-function symbol table gives eval-in-frame, and nodes carry
positions. The goals stated above (frames, threads) both want an
explicit frame stack.

### 6. dgemm: the first real Fortran call

Vendor netlib's reference `dgemm.f`, `lsame.f` and `xerbla.f` (F77,
single files, no framework, builds the same on Linux). Build two
matrices in clotran, multiply with dgemm, read back, compare against
the same product computed in Clojure with `reduce`. This validates the
premise -- that hosting on Fortran beats bridging to it -- which after
154 commits is still unvalidated, and it fixes the marshaling
convention. Decide explicitly that interop is STATIC: standard Fortran
has no dynamic loading, so a binding is compiled into clotran and the
product is a library you link your Fortran against, like embedding
Lua. That shapes the generator: emit `.f90` glue, rebuild.

### 7. ChemSol -- the interop finish line

After dgemm proves the convention. Replace `main.f90` with clotran,
import `chemsol.f90` and `push_array.f90`, run the three test inputs
with `vdw.par`, compare outputs. Its routines take twenty to thirty
positional arguments (`dg_ld`, `readopt`), which is the
argument-marshaling problem NOTES describes: unpack a map into
positional args, call the unmodified routine, repack. Independent of
step 5; can run in a worktree once step 6 lands.

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

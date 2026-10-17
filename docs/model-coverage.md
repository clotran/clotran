# What the ACL2 model covers

clotran is meant to be a formalized language: every part whose
behaviour is not already defined by someone else is designed and proved
in ACL2 (`model/`), and its Fortran generated from the proof. The
reason is shared memory. Several threads mutate one heap, and the race
conditions that brings are found by proof, not by testing, which only
sees the interleavings that happened to run.

This table is where that stands. Each row is one of:

- **Generated** -- the Fortran is written from proved ACL2 by
  `scripts/acl2-fortran`, and nobody edits it: change the model, prove
  it, `make gen-vm`.
- **Modeled** -- the design is proved, but the Fortran is hand-written
  to it, so nothing mechanical ties the two; it can drift.
- **Owed** -- not modeled yet, and should be.
- **By design** -- not modeled, because something else is the
  authority: Clojure defines the answer (`clj` is the oracle and the
  fuzzers compare against it), or the operating system does, or the
  code is vendored.

Lines are counted from the sources as of 2026-10-17. Update a row in
the commit that moves it.

## The machine and the heap

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| VM step loop | `src/f/gen/vm_gen.f90` (1.8k) | vm, vmx, vmx2, vmi, vmg | **Generated** | Designed in ACL2 first; compared step for step against ACL2 (`check-vm-gen`) |
| VM bytecode compiler | `src/f/gen/vmc_gen.f90` (1k) | vmic, vmicg | **Generated** | `vmicg-correct`; compared array for array |
| Superinstructions | in `vm_gen.f90` | vmf, vmfg | **Generated** | Each proved equal to the steps it fuses |
| Collector: marking, sweep, allocation, arena runs, write barrier, the seq op | `src/f/gen/heap_gen.inc` (2k) | heapg, heapsw, heapal, heaprn, heapgn, heapsq, heap-cost | **Generated** | Stage 1 of the heap plan (PLAN step 33) |
| VM runtime layer | `VmRuntime.f90` (630), `vm.inc` (1.3k) | none -- `prim` is unconstrained in the model | **Owed** | Joins the proved machine to clotran's values |
| JIT, arm64 | `vmjit.inc` (640) | vmj, vmj2, jit, jit2, jit3 | **Modeled**; the emitter is hand-written | Generating the emitter is in the plan |
| The rest of the heap: pools, roots and the shadow stack, texts, the image | `GC.f90` (~3k of 5k) | partly alloc | **Owed** | The `roots(:)` convention, ~970 call sites, is what keeps out a moving collector |
| Moving nursery | not built | alloc | **Modeled**, not implemented | Waits on the row above |

## Concurrency

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| A lazy seq realised once, the other threads waiting | `GC.f90` | lazy-cell, proved under every interleaving | **Modeled**, hand-written | |
| Agents and their scheduler | `tasks.inc`, core | agents, agents-drive | **Modeled**, hand-written | |
| Execution pool | a separate library | pool | **Modeled** | Kept out of clotran's core (PLAN step 32) |
| Threads: pthreads, a context per thread | `Threads.f90` (380) | none | **Owed** | |
| Several threads on one heap: per-thread batches, the state lock, stopping every thread for a collection | `GC.f90` | none; the heap books are one thread's view | **Owed** | The largest risk |
| Lock-free Var reads, atoms' compare-and-swap | `seqlock.c` (80), `Eval.f90` | none | **Owed** | |
| Futures, promises, latches, a wait's deadlock detection | `tasks.inc` (440) | none | **Owed** | |
| Transactions (STM) | `Eval.f90` | none | **Owed** | Serialised under one lock today (DEVIATIONS 10), so small to model |

## Data structures

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| Persistent vector, subvec | `PersistentVector.f90` (490) | vector | **Modeled**, hand-written | Generating it was planned |
| Sorted map | `Assoc.f90` (930) | btree | **Modeled**, hand-written | |
| Hash map trie | `PersistentHashMap.f90` (515) | hashseq covers only its seq | **Owed** | The source cites `model/hashmap.lisp`, which does not exist |
| Array map, list, environments, namespaces | ~1k together | none | **Owed** | Small |
| A string's index | `GC.f90` | string | **Modeled**, hand-written | |

## The package boundary

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| The door: integers cross exactly, UTF-8, handles, array aliasing | `DynLoad.f90`, `ClotranABI.f90`, `NativeArray.f90` (~2.3k) | boundary | **Modeled**, hand-written | The book proves the decisions (PLAN step 27), not this code |

## The language and its compilers

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| Analyzer and tree evaluator | `analyze.inc`, `exec.inc` (7.4k) | the VM model covers the core language's machine | **Owed** | Stage 2 of the generation plan |
| Flat interpreter | `flat.inc` (2k) | none | **Owed**, or retired | The VM is meant to replace it |
| Ahead-of-time compiler to Fortran | `compiler.cljf`, `purefort.cljf` (3.4k) | none | **Owed** | Checked today by comparing compiled, interpreted and `clj`; a model would look like vmic's |

## Not modeled, on purpose

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| What each builtin answers | most of `Eval.f90` (~20k) | none | **By design** | Clojure defines the answer: `clj` is the oracle, the fuzzers compare. Their *algorithms* -- hashing, the numeric tower -- could still be proved |
| Reader, printer | `LispReader.f90`, `Printer.f90` (4k) | none | **By design** | `clj`, through fuzz-read and fuzz-print |
| Numbers: BigInt, BigDecimal, ratios, IEEE | ~1.6k | none | **By design** for values | The answer must be clj's; the algorithms are optional to prove |
| `core.clj` and Clojure's libraries | `upstream/`, vendored | none | **By design** | Clojure's own source, run as written |
| Regex and Unicode | ICU, vendored | none | **By design** | Never edited |
| The OS: processes, sockets, files, dlopen, Windows shims, the launcher | `src/c/*`, `main.f90`, `launcher.cljf` | none | **By design** | The OS defines it; `scripts/fuzz-run` checks argument passing |

## Keeping it honest

- `make check-vm-gen` compares `vm_gen.f90` and `vmc_gen.f90` with what
  the model generates and runs them against ACL2. It does not yet
  compare `heap_gen.inc`.
- Neither `make model` nor `make check-vm-gen` is in a gate yet: they
  run when run by hand. Only the macOS machine has ACL2.
- On 2026-10-17 all three generated files were regenerated and were
  byte-for-byte what is checked in.

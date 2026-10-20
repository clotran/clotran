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
| The main thread's mailbox: a package's function (a window system's event loop) run on the process's first thread | `Threads.f90` `th_main_*` | mainbox: each accepted function runs once, in order; the main thread stops within 4 of its steps after the end | **Modeled**, hand-written | |
| Several threads on one heap: per-thread batches, the state lock, stopping every thread for a collection | `GC.f90` | none; the heap books are one thread's view | **Owed** | The largest risk |
| Lock-free Var reads, atoms' compare-and-swap | `seqlock.c` (80), `GC.f90` `gc_cell_*`, `Eval.f90` | seqlock, and casloop for swap! | **Modeled**, hand-written | A read that ends returns both words of one committed value, the one current at its first load, while every write is under the state lock; a read's retries at most the counter's moves, two a write; swap! and swap-vals! linearizable, exactly once, lock-free (2026-10-19). Found: an agent's new state and restart-agent were stored without the lock (now gc_cell_set), and the writer's fence Boehm's seqlock needs was missing |
| Futures, promises, latches, a wait's deadlock detection | `tasks.inc` (440) | none | **Owed** | |
| Transactions (STM) | `Eval.f90` `tx_*`, B_RUNTX | stm: serializable in lock order, a read seeing the serial run's value, all-or-none commits, each thread's transactions once in order, the holder never waits and only an idle thread waits for another's lock, the release within its length + 2 holder steps | **Modeled**, hand-written | Serialised under one lock (DEVIATIONS 10); modelling it found three bugs, fixed 2026-10-19: swap!/compare-and-set! wrote a ref outside any transaction, a throwing watch left half a commit, a watch's own dosync deadlocked on the held lock |

## Data structures

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| Persistent vector, subvec | `PersistentVector.f90` (490) | vector | **Modeled**, hand-written | Generating it was planned |
| Sorted map | `Assoc.f90` (930) | btree | **Modeled**, hand-written | |
| Hash map trie | `PersistentHashMap.f90` (515) | hashmap, and hashseq its seq | **Modeled**, hand-written | get, assoc and dissoc, the count they keep, the depth and their step counts (2026-10-19); a bucket is taken as the alist it behaves as |
| Array map, list, environments, namespaces | `PersistentArrayMap.f90`, `PersistentList.f90`, `Env.f90`, `Namespace.f90` (~1k) | arraymap, envns, and casloop for the registry's and mappings' compare-and-swap | **Modeled**, hand-written | Array map get/assoc/dissoc (both ways) and the positional edits as their loops run, the list's cached count, an env's walk and what a set shows through shared frames, intern keeping a Var, one namespace a name; every registry and mappings write linearizable, exactly once, lock-free (2026-10-19) -- the read-assoc-store before it lost ~40% of concurrent create-ns |
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
| The REPL's line editor: the input and its cursor, the history, completion | `lineedit.cljf` (520), `tty_shim.c` (190) | lineedit: the cursor stays within the text, an edit changes only its span, the history gives the draft back, completion leaves the candidate in the word's place; each key linear in the input | **Modeled**, hand-written | The terminal itself -- raw mode, the bytes, the width -- is the OS's |

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

- `make check-vm-gen` compares all three generated files with what the
  model generates and runs them against ACL2, with negative controls.
- Both are in the gate: the gfortran half of `make crosscheck`
  certifies every book (`make model`) and runs `check-vm-gen`
  (`check-model`). Only macOS has ACL2; there a missing ACL2 fails the
  gate, and the Linux and Windows gates say they skipped it.
- `make check-model-ratchet` runs in every gate and needs no ACL2.
  `model/ratchet.edn` names each generated file and each hand-written
  part a **Modeled** row describes, with its books and a hash of each
  side; code that moves while its books do not fails, and so does a
  change to this table's count of **Owed** rows, which
  `scripts/model-ratchet --stamp` lowers and never raises. Its
  negative controls (`--control`) make each drift in memory and must
  see it caught. A row that moves updates the table, `ratchet.edn` and
  the books in one commit.
- On 2026-10-17 all three generated files were regenerated and were
  byte-for-byte what is checked in.

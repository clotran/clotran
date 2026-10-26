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
| The rest of the heap: pools, roots and the shadow stack, texts, the image | `GC.f90` (~3k of 5k): the value stack (`vs_*`, `gc_stack_new`), the spare frames, `gc_obj`/`gc_vec`/`new_text`'s roots, `collect_*`, the global roots and their handles, the pools' growth, the texts, `gc_image_write`/`_read` | heaprt: every slot above a stack's top is nil, so a new frame is nil uncleared; a frame leaves the stack exactly as it found it and never changes its callers' slots while it runs, so what they hold is a root at every allocation; anything reachable from a root -- a global, a stack slot, the allocation's own roots and the slots `gc_obj` is about to store -- survives any collection whose marking holds the roots and is closed; a value held in a local and in no root is freed and its cell handed to the next allocation (unrooted-is-reused); a global slot's index never moves, `gc_global_keep` leaves its handle live with its value and every other as it was, `gc_init` makes every handle stale; every spare frame is a used cell, so one taken was handed to no one else; a pool's growth keeps its slots and adds unused ones; an image read gives back the pools, arena, texts, global roots and generation as written, so the graph the roots reach is the one saved; counted: `vs_enter` 1 step, `vs_leave` top - base + 1, `push_roots` one push a root, `gc_global_new` at most count + 2, `gc_frame_give` n + 1, growth 2n, the image linear in the pools and the texts' bytes | **Modeled**, hand-written | Under the rooting discipline the ~970 call sites keep by hand: a frame writes only its own slots and leaves to its own base, a value held across an allocation is in its roots, a frame's slot or reachable from a global, a spare is given only by the call that allocated it, an image is read before any root is claimed and taken with one thread. A bug it found, fixed: a new heap (`gc_init`, an image read) kept stack 1's spare frames, vectors of the old heap the new one hands to someone else (spare-survives-reset-is-stale; `clear_batches` empties them, `test/f/gc_test.f90` 20b fails without it). Not covered: the generational aging (`age_*`, `collect_young`'s promotion -- the alloc books' design), the string builder, `vm_run`'s shortcut leave (the VM runtime row) |
| Moving nursery | not built | alloc | **Modeled**, not implemented | Waits on the row above |

## Concurrency

| Part | Code (lines) | Model | Status | Why |
|---|---|---|---|---|
| A lazy seq realised once, the other threads waiting | `GC.f90` | lazy-cell, proved under every interleaving | **Modeled**, hand-written | |
| Agents and their scheduler | `tasks.inc`, core | agents, agents-drive | **Modeled**, hand-written | |
| Execution pool | a separate library | pool | **Modeled** | Kept out of clotran's core (PLAN step 32) |
| Threads: pthreads, a context per thread | `Threads.f90` (380), `Eval.f90` `gce_ctx_new`, `ctx_release` | threads: a th_key_get answers the asking thread its own slots, cache or not, under the discipline the code keeps; no two live threads hold one context id; a th_join returns only on a thread that has exited; counted: a lookup 2 steps, a take 3, a give-back 2 | **Modeled**, hand-written | Found: th_main_serve ran a posted function on the first thread with the single-thread key cache still on, so one calling back into the C ABI got the program thread's value stack (old-serve-reads-the-owners); now it turns the cache off first (2026-10-24; test/f/threads_test.f90 fails without it). The lock and condition wrappers are pthread's own |
| The main thread's mailbox: a package's function (a window system's event loop) run on the process's first thread | `Threads.f90` `th_main_*` | mainbox: each accepted function runs once, in order; the main thread stops within 4 of its steps after the end | **Modeled**, hand-written | |
| Several threads on one heap: per-thread batches, the state lock, stopping every thread for a collection | `GC.f90` `heap_enter`, `world_stop`, `gc_mutator_*`, `gc_poll`, the batches and pending lists, `push_roots`, `gc_grow_*` | heapmt, heapmt-proof, proved under every interleaving: every cell a thread roots is in use -- on no free list, batch or pending list -- so no collection frees one; a cell in a thread's batch is no other thread's to take or move, and an allocation's cell is in no thread's roots; a collection runs only with every other thread parked or out, and while it runs no other thread changes a cell, a root, a phase or a counter; some thread can always step; counted: the stop waits for at most n - 1 parks and none is undone while it waits, the collector's passes are 4 a thread plus its roots, a pending refill at most its list's length in turns and its batch's room, whatever the threads | **Modeled**, hand-written | Under the discipline the code keeps: nothing enters the heap (`heap_enter`, `gc_poll`, `world_stop`, `gc_mutator_enter`) holding the state lock, nothing waits for `tx_lk` or a monitor holding it or while counted running, and only threads clotran starts run clotran code. Without it, a thread parked holding the state lock while a running one waits for the lock is a deadlock (parked-under-state-lock-is-stuck). No bug found: an instrumented build saw no `heap_enter` under the state lock in a six-thread atom/ref/agent/intern/pmap run (2026-10-25). The marking from the roots is heapg/heapgn's, a list's slots heapal's |
| Lock-free Var reads, atoms' compare-and-swap | `seqlock.c` (80), `GC.f90` `gc_cell_*`, `Eval.f90` | seqlock, and casloop for swap! | **Modeled**, hand-written | A read that ends returns both words of one committed value, the one current at its first load, while every write is under the state lock; a read's retries at most the counter's moves, two a write; swap! and swap-vals! linearizable, exactly once, lock-free (2026-10-19). Found: an agent's new state and restart-agent were stored without the lock (now gc_cell_set), and the writer's fence Boehm's seqlock needs was missing |
| Futures, promises, latches, a wait's deadlock detection | `tasks.inc` (440) | waits: the wait counters are the sleepers and the live threads; a deadlock verdict means every other live thread sleeps with no deadline on a target not ready, nothing is left to ready one, and from such a state the next check gives it (1 step) | **Modeled**, hand-written | The verdict took 100 ms with nothing announced to mean no waiter was about to wake -- a timing assumption a loaded machine breaks (old-verdict-is-wrong); now each waiter registers its target and the verdict asks them (any_waiter_ready), 2026-10-19 |
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
| A call's sizes, checked before the call: an explicit-shape dummy reaches no further than the array passed | `package.cljf` `check-call` (~200), the bounds from `bind.cljf` | boundary, section 8: an accepted call reaches only inside its arrays, a refused one would have reached past one; the check linear in the declaration | **Modeled**, hand-written | PLAN step 40 (2026-10-24); assumed-size and unevaluable bounds are said, not checked |

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

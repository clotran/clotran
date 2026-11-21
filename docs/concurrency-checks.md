# Concurrency checks on the real code (2026-11-20)

Two checks that sit beside the ACL2 model (model/seqlock.lisp, heapmt.lisp), which is
sequentially consistent and sees interleavings only at its own action granularity.
Both are nightly (`make test-nightly`), not the per-commit gate. Neither changes
behaviour when not asked for: no DEVIATIONS entry.

## make check-seqlock: the fences (src/c/seqlock.c)

`test/c/seqlock_litmus.c` #includes seqlock.c (the code under test is not a copy) and
runs two writers (under a mutex, as the state lock does) and two readers; a reader
must never see a torn pair. `scripts/check-seqlock` runs

- ThreadSanitizer on it, 10 runs: clean;
- GenMC 0.20.0 (RC11, LLVM 22) exhaustively: no violation, 18 complete executions
  (494 blocked: the reader's spin);
- NEGATIVE CONTROLS, each must be found by GenMC: -DMUTANT_NO_RELEASE_FENCE (the writer's
  release fence in clotran_seq_begin) and -DMUTANT_NO_ACQUIRE_FENCE (the reader's acquire
  fence in clotran_seq_read16). Both give "Safety violation" (the assert).

TSan does NOT see the mutant (200 runs of the no-release-fence build: no failure; it is not
a weak-memory checker). GenMC is built from source (https://github.com/MPI-SWS/genmc) with
brew's llvm@22 and hwloc (LLVM 23 does not build); expected at ~/clotran/genmc, or $GENMC.
Without it the script runs TSan only and says SKIP.

arm64 (clang -O2): clotran_seq_begin is `ldaddal` then `dmb ish`; the fence compiles to a full
barrier, and the mutant is the `ldaddal` alone. clotran_seq_end is `ldaddl` (release RMW).
clotran_seq_read16: `ldapr` (acquire), two plain `ldr`, `dmb ishld` (the acquire fence), a plain
`ldr` of the counter. So on arm64 the writer fence is redundant in practice (the acquire half of
`ldaddal` already keeps the writer's later stores after it); it is needed on the C11 abstract
machine and any target whose RMW lowers without acquire. The litmus is about the C11 argument,
not this chip.

## make check-sched: the scheduler seam (src/f/Threads.f90, sched_*)

CLOTRAN_SCHED_SEED=k (unset: off). Every th_lock_acquire / th_lock_release / th_cond_wait /
th_cond_timedwait / th_cond_broadcast first draws from one seeded LCG (under its own mutex):
1 in 8 yields, 1 in 64 sleeps 1-100 us, and a wait returns at once as a SPURIOUS WAKEUP 1 in 4
(lock released and retaken, then returns). Callers must loop on their condition (th_cond_wait's
contract). Off, each routine pays one integer compare. What it is not: the same seed gives the
same sequence of perturbations, but which thread takes each draw is still up to the OS, so it
is a seeded perturbation, not a replayable schedule (that needs a baton; owed).
`scripts/check-sched [N]` first checks the seam is live (a lock-heavy loop is >2x slower seeded),
then runs fuzz-threads and fuzz-gc under seeds 1..N (SCHED_SEEDS, default 4; about 7 minutes a seed on a loaded machine; a 2nd argument is the first seed) against clj.

## make check-lazy: the lazy-cell waiters pairing (src/c/seqlock.c)

`test/c/lazy_litmus.c` #includes seqlock.c: an owner settles the cell (relaxed store, as the
Fortran store is plain) then reads clotran_lazy_waiters_fenced(); a waiter does
clotran_lazy_waiters_add(1) then reads the cell. Store buffering: the lost wakeup is "owner saw
no waiter AND waiter saw the cell still running". GenMC (RC11): 3 complete executions, none
violating. NEGATIVE CONTROLS (the script finds the fence's line in seqlock.c and drops it with a
-DMUTANT_LINE macro): the waiter's seq_cst fence (in _add) and the owner's (in _fenced): each
"Safety violation". Same GenMC as check-seqlock; absent: SKIP.

## make check-replay: the model's conformance on the real code (scripts/check-replay-run)

CLOTRAN_SCHED_LOG=prefix writes prefix.<pid> (off: one integer compare per op; CLOTRAN_SCHED_LOG_MAX
lines, default 3M, a prefix of a run is a run). Logging starts when a second thread becomes a
mutator (gc_mutator_enter, n_running >= 2): before that the process is one thread and every
allocation is noise. Lines: thread, event, lock/cond address, name. From the th_* wrappers: acq,
rel, wait, woke (a wait is a release, the wakeup an acquire, spurious or not), bcast; from GC.f90:
enter, leave, henter, park, wake, hleave, stop, stopalone, stopwake, start; "mark" lines
(see below). Each line is written under one log mutex, inside the lock-held span it describes,
so file order is one real order of the events.

scripts/check-replay maps each log to heapmt actions (state_lk acq/rel/wait -> :slock/:sunlock, tx_lk ->
:xlock/:xunlock, the GC events -> :enter :leave :henter :wake :hleave :stop :stopwake :start) and
runs hm-step in ACL2 (needs model/heapmt.cert), failing when a step leaves the state unchanged (not
enabled), lands in a different phase than the code reports (e.g. the code parked and the model
did not: stop_world disagrees), or breaks the invariant (hm-inv-g and th-ok at every step). It also
checks per lock: one holder, released by its holder. Who held what when logging began is read off
each thread's first event. The model runs with no cells: this checks the lock, safepoint and
stop protocol (and the discipline: state_lk only from :out/:run/:inheap/:collect, tx_lk only when
out), not batches, roots or the sweep.
CONTROLS: deleting the park events, or the stop events, from a real log must fail the replay
(it does: not enabled at the next stopwake / henter).
Workloads: fuzz-threads (-n 2) and fuzz-gc (-n 1) under CLOTRAN_SCHED_SEED=1..4, every clotran
process logged.

## Marks: shared accesses the th_* wrappers do not see (th_mark)

Listed in the study: gc_cell_get's seqlock read (GC.f90), clotran_gc_hold (gc_hold_begin/end),
the lazy-cell CAS (gc_cas_i1), the waiters counter (gc_lazy_wait_add), the wake test
(gc_lazy_wake), and gc_obj's lock-free batch pop. th_mark(name) is a yield point under a seed and
a "mark" line in the log; added at all but the last (gc_obj's pop is the allocation hot path
and is thread-private by the batch invariant, so it is left: a yield there needs a measured
cost). scripts/check-replay-run first runs futures over a lazy seq, an atom and a sorted-map
comparator and fails unless every mark name appears in the log.

## What this tells about the open questions

- Fortran writes to cells (gc_set_slot: `obj_pool(i)%slot(i) = x`) are PLAIN stores of a 16-byte
  struct, under the state lock; only the readers' loads are atomic. Formally a C11 data race; it
  is safe because the reader retries on the counter and the compiler cannot move the store across
  the opaque clotran_seq_begin/end calls. The litmus models the stores as relaxed atomics, so it
  proves the protocol, not the codegen of that store.
- Every pthread call is in Threads.f90 (grep: no other use besides pthread_jit_write_protect_np
  in jit_shim.c); so the seam sees every lock and wait. It does not see: gc_cell_get's seqlock
  read, clotran_gc_hold, the lazy-cell CAS and waiters counter, nor gc_obj's lock-free batch pop.

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

## What this tells about the open questions

- Fortran writes to cells (gc_set_slot: `obj_pool(i)%slot(i) = x`) are PLAIN stores of a 16-byte
  struct, under the state lock; only the readers' loads are atomic. Formally a C11 data race; it
  is safe because the reader retries on the counter and the compiler cannot move the store across
  the opaque clotran_seq_begin/end calls. The litmus models the stores as relaxed atomics, so it
  proves the protocol, not the codegen of that store.
- Every pthread call is in Threads.f90 (grep: no other use besides pthread_jit_write_protect_np
  in jit_shim.c); so the seam sees every lock and wait. It does not see: gc_cell_get's seqlock
  read, clotran_gc_hold, the lazy-cell CAS and waiters counter, nor gc_obj's lock-free batch pop.

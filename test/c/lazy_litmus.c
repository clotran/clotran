/* Store-buffering litmus for the lazy-cell waiters pairing (src/c/seqlock.c,
 * clotran_lazy_waiters_add / _fenced; protocol in model/lazy-cell.lisp, code in
 * Eval.f90 gce_force and GC.f90 gc_lazy_wake). Waiter: count itself (add 1),
 * then look at the cell; if still running it goes to sleep. Owner: settle the
 * cell (the Fortran store is plain: a relaxed store here), then read the count
 * with the fence; if 0 it does not wake anyone. Lost wakeup = owner saw 0
 * waiters AND waiter saw the cell running. The same functions are used (#include).
 * MUTANT_LINE=n drops the seq_cst fence on line n of seqlock.c (the script finds
 * the line in _add or _fenced). */
#include <pthread.h>
#include <assert.h>
#include <stdatomic.h>
#ifdef MUTANT_LINE
#define atomic_thread_fence(o) (__LINE__ == MUTANT_LINE ? (void)0 : __c11_atomic_thread_fence(o))
#endif
#include "seqlock.c"

static _Atomic int cell = 1;          /* 1 = running, 0 = settled */
static int owner_saw_none, waiter_saw_running;

static void *owner(void *a) {
  (void)a;
  atomic_store_explicit(&cell, 0, memory_order_relaxed);
  if (clotran_lazy_waiters_fenced() == 0) owner_saw_none = 1;
  return 0;
}

static void *waiter(void *a) {
  (void)a;
  clotran_lazy_waiters_add(1);
  if (atomic_load_explicit(&cell, memory_order_relaxed) == 1) waiter_saw_running = 1;
  return 0;
}

int main(void) {
  pthread_t t[2];
  pthread_create(&t[0], 0, owner, 0);
  pthread_create(&t[1], 0, waiter, 0);
  for (int i = 0; i < 2; i++) pthread_join(t[i], 0);
  assert(!(owner_saw_none && waiter_saw_running));   /* no lost wakeup */
  return 0;
}

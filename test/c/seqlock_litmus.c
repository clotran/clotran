/* Standalone litmus harness for src/c/seqlock.c: two writers (serialised by a
 * mutex, as the state lock does in GC.f90) and two readers, using the SAME
 * functions (the file is #included, so the code under test is not a copy).
 * A writer bumps the counter, stores a pair (n, n) with plain relaxed stores,
 * and ends; a reader must never see a torn pair (a != b).
 * Build: -DMUTANT_NO_RELEASE_FENCE / -DMUTANT_NO_ACQUIRE_FENCE drop a fence. */
#include <pthread.h>
#include <assert.h>
#include <stdatomic.h>
/* mutants: drop one fence kind (a negative control for the checker) */
#ifdef MUTANT_NO_RELEASE_FENCE   /* the writer's release fence in clotran_seq_begin */
#undef atomic_thread_fence
#define atomic_thread_fence(o) ((o) == memory_order_release ? (void)0 : __c11_atomic_thread_fence(o))
#endif
#ifdef MUTANT_NO_ACQUIRE_FENCE   /* the reader's acquire fence in clotran_seq_read16 */
#undef atomic_thread_fence
#define atomic_thread_fence(o) ((o) == memory_order_acquire ? (void)0 : __c11_atomic_thread_fence(o))
#endif
#include "seqlock.c"

static int64_t cell[2];  /* the shared 16-byte value */
static pthread_mutex_t lk = PTHREAD_MUTEX_INITIALIZER;

static void *writer(void *arg) {
  int64_t n = (int64_t)(intptr_t)arg;
  pthread_mutex_lock(&lk);
  clotran_seq_begin();
  __atomic_store_n(&cell[0], n, __ATOMIC_RELAXED);
  __atomic_store_n(&cell[1], n, __ATOMIC_RELAXED);
  clotran_seq_end();
  pthread_mutex_unlock(&lk);
  return 0;
}

static void *reader(void *arg) {
  (void)arg;
  int64_t d[2];
  clotran_seq_read16(cell, d);
  assert(d[0] == d[1]);
  return 0;
}

int main(void) {
  pthread_t t[4];
  pthread_create(&t[0], 0, writer, (void *)1);
  pthread_create(&t[1], 0, writer, (void *)2);
  pthread_create(&t[2], 0, reader, 0);
  pthread_create(&t[3], 0, reader, 0);
  for (int i = 0; i < 4; i++) pthread_join(t[i], 0);
  return 0;
}

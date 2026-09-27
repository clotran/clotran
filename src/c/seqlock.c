/* The state lock's SEQUENCE COUNTER (GC.f90): a reader of a shared cell
 * takes no lock -- it copies the cell and checks that no writer ran in the
 * meantime -- and a writer, which holds the state lock anyway, makes the
 * counter odd for as long as it holds it. Fortran has no atomics or fences
 * outside coarrays, so these few lines are C11.
 *
 * Every Var read is a cell read, and taking a mutex for each one was the
 * largest single cost in a profile of reduce (PLAN.md, the calling
 * convention). Writers are rare: a def, an alter-var-root, a swap!. */
#include <stdatomic.h>
#include <stdint.h>

static _Atomic int64_t clotran_seq = 0;

/* the outermost acquire of the state lock: the counter goes odd */
void clotran_seq_begin(void) {
  atomic_fetch_add_explicit(&clotran_seq, 1, memory_order_acq_rel);
}

/* the outermost release: even again, after the writer's stores */
void clotran_seq_end(void) {
  atomic_fetch_add_explicit(&clotran_seq, 1, memory_order_release);
}

/* A consistent copy of the 16-byte value at src: retried while a writer
 * holds the lock or ran during the copy. */
void clotran_seq_read16(const int64_t *src, int64_t *dst) {
  for (;;) {
    int64_t s1 = atomic_load_explicit(&clotran_seq, memory_order_acquire);
    if (s1 & 1) continue;
    int64_t a = __atomic_load_n(&src[0], __ATOMIC_RELAXED);
    int64_t b = __atomic_load_n(&src[1], __ATOMIC_RELAXED);
    atomic_thread_fence(memory_order_acquire);
    if (atomic_load_explicit(&clotran_seq, memory_order_relaxed) == s1) {
      dst[0] = a;
      dst[1] = b;
      return;
    }
  }
}

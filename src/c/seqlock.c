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

/* The collector's HOLD: how many threads are in data-structure code that
 * has called back into the evaluator -- a key's equality or hash, a
 * sorted map's comparator -- while holding values in Fortran locals no
 * root list names. A collection then would free them (GC.f90,
 * gc_hold_begin). Changed atomically, read with the world stopped. */
static _Atomic int64_t clotran_gc_holds = 0;

void clotran_gc_hold(int64_t delta) {
  atomic_fetch_add_explicit(&clotran_gc_holds, delta, memory_order_acq_rel);
}

int64_t clotran_gc_holding(void) {
  return atomic_load_explicit(&clotran_gc_holds, memory_order_acquire);
}

/* A LAZY CELL's claim (model/lazy-cell.lisp): its state word goes from
 * pending to running-by-this-thread in one compare-and-swap, so forcing a
 * cell nobody else is forcing takes no lock. A thread that finds the cell
 * running counts itself a waiter BEFORE it looks again, under the state
 * lock; the owner settles, fences, and wakes the waiters only when the
 * count says there are some. The fence on one side and the
 * read-modify-write on the other are both sequentially consistent, so
 * either the owner sees the waiter and wakes it, or the waiter sees the
 * settled cell: no wakeup is lost. */
static _Atomic int64_t clotran_lazy_waiters = 0;

int clotran_cas_i32(int32_t *p, int32_t expected, int32_t desired) {
  return __atomic_compare_exchange_n(p, &expected, desired, 0,
                                     __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}

void clotran_lazy_waiters_add(int64_t d) {
  atomic_fetch_add_explicit(&clotran_lazy_waiters, d, memory_order_seq_cst);
  atomic_thread_fence(memory_order_seq_cst);
}

int64_t clotran_lazy_waiters_fenced(void) {
  atomic_thread_fence(memory_order_seq_cst);
  return atomic_load_explicit(&clotran_lazy_waiters, memory_order_seq_cst);
}

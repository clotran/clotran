/* Executable memory for clotran's JIT (PLAN step 31; src/f/vmjit.inc).
 * One region, mapped once; code is written into it with the platform's
 * write protection lifted for the calling thread only (macOS arm64's
 * MAP_JIT), and the instruction cache flushed over what was written. */
#include <stdint.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#endif
#ifdef __APPLE__
#include <pthread.h>
#include <libkern/OSCacheControl.h>
#endif

void *clotran_jit_alloc(int64_t n) {
#ifdef _WIN32
  return VirtualAlloc(0, (size_t)n, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
#elif defined(__APPLE__)
  void *p = mmap(0, (size_t)n, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
#else
  void *p = mmap(0, (size_t)n, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON, -1, 0);
  return p == MAP_FAILED ? 0 : p;
#endif
}

/* n 32-bit instruction words to dst */
void clotran_jit_write(void *dst, const uint32_t *w, int64_t n) {
#ifdef __APPLE__
  pthread_jit_write_protect_np(0);
  memcpy(dst, w, (size_t)n * 4);
  pthread_jit_write_protect_np(1);
  sys_icache_invalidate(dst, (size_t)n * 4);
#else
  memcpy(dst, w, (size_t)n * 4);
  __builtin___clear_cache((char *)dst, (char *)dst + n * 4);
#endif
}

/* the code at entry, run on the context ctx */
typedef void (*clotran_jit_fn)(void *);
void clotran_jit_enter(void *entry, void *ctx) { ((clotran_jit_fn)entry)(ctx); }

/* 1 where the JIT has an emitter: arm64 */
int clotran_jit_arch(void) {
#if defined(__aarch64__) || defined(__arm64__)
  return 1;
#else
  return 0;
#endif
}

/* test/c/mainthread.c: a package with one function for the main thread
   (fortran/main-thread*, Threads.f90's mailbox) and one routine telling
   whether it ran there -- the language test's check of the handoff. */
#include <pthread.h>
#include <unistd.h>
#if defined(__linux__)
#include <sys/syscall.h>
#endif

static volatile int ran, on_main = -1;

void clotran_test_on_main(void)
{
#if defined(__APPLE__)
	on_main = pthread_main_np();
#elif defined(__linux__)
	on_main = getpid() == (pid_t) syscall(SYS_gettid);
#else
	on_main = -1;   /* not known here; ran says it ran */
#endif
	ran++;
}

/* was_main(out ran, out main): how many times it ran, and whether on
   the process's first thread (1), not (0), or not known (-1) */
void was_main_shim(int argc, void **argv)
{
	*(int *) argv[0] = ran;
	*(int *) argv[1] = on_main;
}

const char *clotran_manifest(void)
{
	return "{:package \"mainthread\" :routines [{:name \"was-main\" :symbol \"was_main_shim\" "
	       ":args [{:name \"ran\" :type :int4 :intent :out :rank 0} {:name \"main\" :type :int4 :intent :out :rank 0}]}]}";
}

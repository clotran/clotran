/* win_shim.c -- the POSIX calls the host makes that mingw-w64 does not
 * have, under their POSIX names, so the Fortran binds one set of names on
 * every system. Built only for Windows (Makefile). winpthreads supplies
 * pthread_*, clock_gettime and nanosleep; msvcrt supplies isatty, mkdir
 * (the mode argument is ignored) and the rest. */
#ifdef _WIN32
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0601   /* SetThreadErrorMode, GetActiveProcessorCount */
#endif
#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* dlopen and friends over LoadLibrary: flags ignored (Windows binds every
 * import at load, which is RTLD_NOW); the error is FormatMessage's text */
static __thread char dl_err[512];
static __thread int dl_err_set;

static void dl_fail(const char *what) {
  DWORD e = GetLastError();
  int n = snprintf(dl_err, sizeof dl_err, "%s: ", what);
  if (n < 0 || n >= (int)sizeof dl_err) n = 0;
  if (!FormatMessageA(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS, 0, e, 0,
                      dl_err + n, (DWORD)(sizeof dl_err - n), 0))
    snprintf(dl_err + n, sizeof dl_err - n, "error %lu", (unsigned long)e);
  for (char *p = dl_err; *p; p++) if (*p == '\r' || *p == '\n') *p = ' ';
  dl_err_set = 1;
}

void *dlopen(const char *path, int flags) {
  char full[MAX_PATH * 4];
  HMODULE h;
  DWORD n, mode;
  (void)flags;
  if (!path) return (void *)GetModuleHandleA(0);
  /* a library's own dependencies are looked for beside it, which
   * LOAD_WITH_ALTERED_SEARCH_PATH does for a full path with backslashes
   * only; a relative one is undefined */
  n = GetFullPathNameA(path, sizeof full, full, 0);
  if (n == 0 || n >= sizeof full) { dl_fail(path); return 0; }
  for (char *p = full; *p; p++) if (*p == '/') *p = '\\';
  /* no dialog box for a missing import: a headless run would wait on it */
  SetThreadErrorMode(SEM_FAILCRITICALERRORS | SEM_NOOPENFILEERRORBOX, &mode);
  h = LoadLibraryExA(full, 0, LOAD_WITH_ALTERED_SEARCH_PATH);
  if (!h) dl_fail(path);
  SetThreadErrorMode(mode, 0);
  return (void *)h;
}

void *dlsym(void *h, const char *name) {
  FARPROC p = GetProcAddress((HMODULE)h, name);
  if (!p) dl_fail(name);
  return (void *)p;
}

char *dlerror(void) {
  if (!dl_err_set) return 0;
  dl_err_set = 0;
  return dl_err;
}

/* realpath: the absolute name of a path that exists, with / between its
 * parts, as clotran writes every path */
char *realpath(const char *path, char *out) {
  char buf[MAX_PATH * 4];
  DWORD n = GetFullPathNameA(path, sizeof buf, buf, 0);
  if (n == 0 || n >= sizeof buf) return 0;
  if (GetFileAttributesA(buf) == INVALID_FILE_ATTRIBUTES) return 0;
  for (char *p = buf; *p; p++) if (*p == '\\') *p = '/';
  if (!out) return _strdup(buf);
  strcpy(out, buf);
  return out;
}

/* sysconf: the one name asked, the online processor count -- in every
 * processor group; GetSystemInfo counts the first 64 only */
long sysconf(int name) {
  (void)name;
  return (long)GetActiveProcessorCount(ALL_PROCESSOR_GROUPS);
}

/* rename over an existing file, as POSIX rename does (linked with
 * --wrap=rename): msvcrt's refuses when the target exists */
int __wrap_rename(const char *from, const char *to) {
  return MoveFileExA(from, to, MOVEFILE_REPLACE_EXISTING | MOVEFILE_COPY_ALLOWED) ? 0 : -1;
}
#endif

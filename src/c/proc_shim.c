/* proc_shim.c -- running a program, and the file operations a shell was
 * used for: clotran's own launcher, its background compiles and
 * clotran.files call these instead of /bin/sh, so nothing clotran ships
 * needs a shell (on Windows, none is there).
 *
 * A program is an argv, NOT a command line: no shell parses it, so no
 * argument is ever split, globbed or expanded. On Windows the argv is
 * joined into the one command line CreateProcess takes, quoted by the
 * rules CommandLineToArgvW and the C runtime read back, so the child's
 * argv is the parent's. Strings are UTF-8 everywhere (on Windows the
 * binary's manifest makes the narrow -A calls UTF-8). */
/* rand_s, for a temporary directory's name on Windows */
#define _CRT_RAND_S
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdio.h>
#include <sys/stat.h>

/* the n strings packed into buf, each ended by a NUL */
static char **unpack(const char *buf, long n) {
  char **v = calloc((size_t)n + 1, sizeof *v);
  if (!v) return NULL;
  for (long i = 0; i < n; i++) { v[i] = (char *)buf; buf += strlen(buf) + 1; }
  return v;
}

#ifdef _WIN32
#include <windows.h>
#include <direct.h>
#include <io.h>

static const char *os_name = "Windows";

int clotran_setenv(const char *name, const char *value) {
  return _putenv_s(name, value) == 0 ? 0 : -1;
}

/* one argument as the C runtime's parser reads it back: quoted when it is
 * empty or holds a space, tab or quote; a run of backslashes is doubled
 * before a quote and before the closing quote, and a quote is \" */
static void quote_arg(const char *a, char **out) {
  char *o = *out;
  int needs = (*a == 0) || strpbrk(a, " \t\"") != NULL;
  if (!needs) { size_t k = strlen(a); memcpy(o, a, k); *out = o + k; return; }
  *o++ = '"';
  for (const char *p = a;; p++) {
    long bs = 0;
    while (*p == '\\') { bs++; p++; }
    if (*p == 0) { while (bs-- > 0) { *o++ = '\\'; *o++ = '\\'; } break; }
    if (*p == '"') { while (bs-- > 0) { *o++ = '\\'; *o++ = '\\'; } *o++ = '\\'; *o++ = '"'; }
    else { while (bs-- > 0) *o++ = '\\'; *o++ = *p; }
  }
  *o++ = '"';
  *out = o;
}

/* the environment block: this process's, with each NAME=VALUE of env in
 * place of what it had (Windows names are case-insensitive) */
static char *env_block(char **env, long nenv) {
  char *cur = GetEnvironmentStringsA(), *p;
  size_t cap = 2, len = 0;
  for (p = cur; *p; p += strlen(p) + 1) cap += strlen(p) + 1;
  for (long i = 0; i < nenv; i++) cap += strlen(env[i]) + 1;
  char *blk = malloc(cap);
  if (!blk) { FreeEnvironmentStringsA(cur); return NULL; }
  for (p = cur; *p; p += strlen(p) + 1) {
    const char *eq = strchr(p + 1, '=');
    size_t kl = eq ? (size_t)(eq - p) : strlen(p);
    int replaced = 0;
    for (long i = 0; i < nenv; i++)
      if (strlen(env[i]) > kl && env[i][kl] == '=' && _strnicmp(env[i], p, kl) == 0) replaced = 1;
    if (!replaced) { size_t k = strlen(p) + 1; memcpy(blk + len, p, k); len += k; }
  }
  for (long i = 0; i < nenv; i++) { size_t k = strlen(env[i]) + 1; memcpy(blk + len, env[i], k); len += k; }
  blk[len++] = 0;
  if (len == 1) blk[len++] = 0;
  FreeEnvironmentStringsA(cur);
  return blk;
}

/* Runs argv (nargv strings packed in args) in dir (or here), with env's
 * NAME=VALUE overrides, stdin from NUL and stdout and stderr to the file
 * out (or this process's own when out is ""). Waiting, the exit status;
 * not, 0 once it has started. -1 when it could not be started. */
long clotran_run(const char *args, long nargv, const char *dir, const char *out,
                 const char *envs, long nenv, int wait) {
  char **argv = unpack(args, nargv), **env = unpack(envs, nenv);
  size_t cap = 1;
  for (long i = 0; i < nargv; i++) cap += 2 * strlen(argv[i]) + 3;
  char *line = malloc(cap), *o = line;
  for (long i = 0; i < nargv; i++) { if (i) *o++ = ' '; quote_arg(argv[i], &o); }
  *o = 0;
  char *blk = nenv > 0 ? env_block(env, nenv) : NULL;
  SECURITY_ATTRIBUTES sa = { sizeof sa, NULL, TRUE };
  HANDLE in = CreateFileA("NUL", GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, &sa, OPEN_EXISTING, 0, NULL);
  HANDLE fo = INVALID_HANDLE_VALUE;
  STARTUPINFOA si; PROCESS_INFORMATION pi;
  memset(&si, 0, sizeof si); si.cb = sizeof si;
  si.dwFlags = STARTF_USESTDHANDLES;
  si.hStdInput = in;
  if (*out) {
    fo = CreateFileA(out, GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, &sa, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    si.hStdOutput = si.hStdError = fo;
  } else {
    si.hStdOutput = GetStdHandle(STD_OUTPUT_HANDLE);
    si.hStdError = GetStdHandle(STD_ERROR_HANDLE);
  }
  long r = -1;
  if (CreateProcessA(NULL, line, NULL, NULL, TRUE, 0, blk, *dir ? dir : NULL, &si, &pi)) {
    r = 0;
    if (wait) {
      DWORD code = 0;
      WaitForSingleObject(pi.hProcess, INFINITE);
      GetExitCodeProcess(pi.hProcess, &code);
      r = (long)code;
    }
    CloseHandle(pi.hProcess); CloseHandle(pi.hThread);
  }
  if (fo != INVALID_HANDLE_VALUE) CloseHandle(fo);
  if (in != INVALID_HANDLE_VALUE) CloseHandle(in);
  free(blk); free(line); free(argv); free(env);
  return r;
}

static int make_dir(const char *p) { return _mkdir(p); }
static int remove_dir(const char *p) { return _rmdir(p); }
static int replace_file(const char *from, const char *to) {
  return MoveFileExA(from, to, MOVEFILE_REPLACE_EXISTING) ? 0 : -1;
}

#else
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
extern char **environ;

#ifdef __APPLE__
static const char *os_name = "Mac OS X";
#else
static const char *os_name = "Linux";
#endif

int clotran_setenv(const char *name, const char *value) { return setenv(name, value, 1); }

/* name found on PATH, as execvp would find it, into buf; done here, in
 * the parent, since the child may only exec after a fork */
static int find_on_path(const char *name, char *buf, size_t cap) {
  if (strchr(name, '/')) { snprintf(buf, cap, "%s", name); return 0; }
  const char *path = getenv("PATH");
  if (!path) path = "/usr/bin:/bin";
  while (*path) {
    const char *end = strchr(path, ':');
    size_t k = end ? (size_t)(end - path) : strlen(path);
    snprintf(buf, cap, "%.*s/%s", (int)k, k ? path : ".", name);
    if (access(buf, X_OK) == 0) return 0;
    path += k + (end ? 1 : 0);
  }
  return -1;
}

/* the environment: this process's, each NAME=VALUE of env in place */
static char **env_vector(char **env, long nenv) {
  long n = 0;
  while (environ[n]) n++;
  char **v = calloc((size_t)(n + nenv + 1), sizeof *v);
  long k = 0;
  if (!v) return NULL;
  for (long i = 0; i < n; i++) {
    const char *eq = strchr(environ[i], '=');
    size_t kl = eq ? (size_t)(eq - environ[i]) : strlen(environ[i]);
    int replaced = 0;
    for (long j = 0; j < nenv; j++)
      if (strncmp(env[j], environ[i], kl) == 0 && env[j][kl] == '=') replaced = 1;
    if (!replaced) v[k++] = environ[i];
  }
  for (long j = 0; j < nenv; j++) v[k++] = env[j];
  return v;
}

/* As on Windows above. A child not waited for is reaped by a later call,
 * so none is left a zombie for long. */
long clotran_run(const char *args, long nargv, const char *dir, const char *out,
                 const char *envs, long nenv, int wait) {
  char **argv = unpack(args, nargv), **env = unpack(envs, nenv);
  char **envp = env_vector(env, nenv);
  char exe[4096];
  long r = -1;
  while (waitpid(-1, NULL, WNOHANG) > 0) ;
  if (argv && envp && nargv > 0 && find_on_path(argv[0], exe, sizeof exe) == 0) {
    pid_t pid = fork();
    if (pid == 0) {
      /* the child: only what is safe between fork and exec */
      int in = open("/dev/null", O_RDONLY);
      if (in >= 0) { dup2(in, 0); close(in); }
      if (*out) {
        int fd = open(out, O_WRONLY | O_CREAT | O_TRUNC, 0644);
        if (fd < 0) _exit(127);
        dup2(fd, 1); dup2(fd, 2); close(fd);
      }
      if (*dir && chdir(dir) != 0) _exit(127);
      execve(exe, argv, envp);
      _exit(127);
    }
    if (pid > 0) {
      r = 0;
      if (wait) {
        int st = 0;
        while (waitpid(pid, &st, 0) < 0 && errno == EINTR) ;
        r = WIFEXITED(st) ? WEXITSTATUS(st) : 128 + (WIFSIGNALED(st) ? WTERMSIG(st) : 0);
      }
    }
  }
  free(envp); free(argv); free(env);
  return r;
}

static int make_dir(const char *p) { return mkdir(p, 0777); }
static int remove_dir(const char *p) { return rmdir(p); }
static int replace_file(const char *from, const char *to) { return rename(from, to); }
#endif

/* os.name, as clj's host names the three: into buf, NUL-ended; its length */
long clotran_os_name(char *buf, long cap) {
  snprintf(buf, (size_t)cap, "%s", os_name);
  return (long)strlen(buf);
}

/* user.dir: this process's working directory, into buf, NUL-ended,
 * with / between its parts on every system; its length, or -1 */
#ifdef _WIN32
long clotran_cwd(char *buf, long cap) {
  if (!_getcwd(buf, (int)cap)) return -1;
  for (char *p = buf; *p; p++) if (*p == '\\') *p = '/';
  return (long)strlen(buf);
}
/* nothing to do: Windows runs a file by its name */
int clotran_make_executable(const char *p) { (void)p; return 0; }
#else
long clotran_cwd(char *buf, long cap) {
  if (!getcwd(buf, (size_t)cap)) return -1;
  return (long)strlen(buf);
}
/* p runnable by everyone who can read it, as chmod +x */
int clotran_make_executable(const char *p) {
  struct stat st;
  if (stat(p, &st) != 0) return -1;
  return chmod(p, st.st_mode | ((st.st_mode & 0444) >> 2)) == 0 ? 0 : -1;
}
#endif

/* A new directory under base, made with a name no other process has or
 * will be given (mkdtemp; on Windows, a name tried until one is made):
 * its path into buf, or -1. */
#ifdef _WIN32
long clotran_temp_dir(const char *base, char *buf, long cap) {
  for (int tries = 0; tries < 100; tries++) {
    unsigned int r1 = 0, r2 = 0;
    rand_s(&r1); rand_s(&r2);
    snprintf(buf, (size_t)cap, "%s/clotran-%08x%08x", base, r1, r2);
    if (_mkdir(buf) == 0) return (long)strlen(buf);
    if (errno != EEXIST) return -1;
  }
  return -1;
}
#else
long clotran_temp_dir(const char *base, char *buf, long cap) {
  snprintf(buf, (size_t)cap, "%s/clotran-XXXXXX", base);
  return mkdtemp(buf) ? (long)strlen(buf) : -1;
}
#endif

/* The directory p and every parent it needs, as mkdir -p: 0 when p is a
 * directory afterwards, -1 when it is not. */
int clotran_mkdirs(const char *p) {
  size_t n = strlen(p);
  char *buf = malloc(n + 1);
  if (!buf) return -1;
  memcpy(buf, p, n + 1);
  for (size_t i = 1; i <= n; i++) {
    if (i == n || buf[i] == '/' || buf[i] == '\\') {
      char c = buf[i];
      buf[i] = 0;
      /* C: on Windows is a drive, not a directory to make */
      if (!(i == 2 && buf[1] == ':')) make_dir(buf);
      buf[i] = c;
    }
  }
  struct stat st;
  int ok = stat(p, &st) == 0 && (st.st_mode & S_IFMT) == S_IFDIR;
  free(buf);
  return ok ? 0 : -1;
}

/* p removed: a file, or a directory that is empty. 0, or -1. */
int clotran_delete(const char *p) {
  struct stat st;
  if (stat(p, &st) != 0) return -1;
  if ((st.st_mode & S_IFMT) == S_IFDIR) return remove_dir(p) == 0 ? 0 : -1;
  return remove(p) == 0 ? 0 : -1;
}

/* from moved to to, replacing a file there, in one step where the system
 * has one: a reader never sees half of to. 0, or -1. */
int clotran_rename(const char *from, const char *to) { return replace_file(from, to); }

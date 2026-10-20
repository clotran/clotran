/* ptydrive: a program run under a pseudo-terminal, typed at, its output
 * kept -- what scripts/lineedit-check drives the REPL's line editor with.
 *
 *   ptydrive COLS ROWS STEPS OUT CMD ARG...
 *
 * STEPS is one step a line, bytes in hex (no escaping to get wrong):
 *   S <hex>          type these bytes
 *   U <hex> <ms>     wait until the output after the last match holds them
 *                    (exit 3 when it does not within ms)
 *   W <ms>           wait, reading the output
 *   R <cols> <rows>  the window resized
 *   M                how much output there is now, a line of OUT.marks
 *   K <signal>       a signal to the program's process group (POSIX)
 * OUT gets every byte the program wrote. When the steps are done the
 * driver waits up to 20 s for the program to end, and answers its exit
 * status (124 when it had to be killed).
 *
 * POSIX: forkpty. Windows: a ConPTY (CreatePseudoConsole), whose output
 * is the console re-rendered as VT sequences. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *got;
static size_t ngot, cap, mark;
static FILE *outf, *marks;

static void keep(const unsigned char *b, size_t n) {
  if (ngot + n > cap) { cap = (ngot + n) * 2 + 4096; got = realloc(got, cap); }
  memcpy(got + ngot, b, n);
  ngot += n;
  fwrite(b, 1, n, outf);
  fflush(outf);
}

static size_t unhex(const char *h, unsigned char *b) {
  size_t n = 0;
  while (h[0] && h[1] && h[0] != ' ' && h[0] != '\n' && h[0] != '\r') {
    unsigned v;
    sscanf(h, "%2x", &v);
    b[n++] = (unsigned char)v;
    h += 2;
  }
  return n;
}

/* where the output after the mark holds needle, CSI sequences skipped
   (ConPTY puts \033[K and the like between what the program wrote): the
   offset after it, or -1 */
static long found(const unsigned char *needle, size_t n) {
  for (size_t i = mark; i < ngot; i++) {
    size_t j = i, k = 0;
    while (k < n && j < ngot) {
      if (got[j] == 27 && j + 1 < ngot && got[j + 1] == 91 && needle[k] != 27) {
        j += 2;
        while (j < ngot && !(got[j] >= 0x40 && got[j] <= 0x7E)) j++;
        j++;
        continue;
      }
      if (got[j] != needle[k]) break;
      j++, k++;
    }
    if (k == n) return (long)j;
  }
  return -1;
}

/* the platform's half: read what is there for up to ms, type, resize, end */
static int pump(int ms);
static void type_bytes(const unsigned char *b, size_t n);
static void resize(int cols, int rows);
static void signal_child(int sig);
static int finish(void);
static int start(int cols, int rows, char **argv);

static long now_ms(void);

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: ptydrive COLS ROWS STEPS OUT CMD ARG...\n"); return 2; }
  FILE *steps = fopen(argv[3], "r");
  outf = fopen(argv[4], "wb");
  static char mname[4096];
  snprintf(mname, sizeof mname, "%s.marks", argv[4]);
  marks = fopen(mname, "w");
  if (!steps || !outf || !marks) { perror("ptydrive"); return 2; }
  if (start(atoi(argv[1]), atoi(argv[2]), argv + 5) != 0) { fprintf(stderr, "ptydrive: no pty\n"); return 2; }
  static char line[1 << 16];
  static unsigned char b[1 << 15];
  while (fgets(line, sizeof line, steps)) {
    if (line[0] == 'S') {
      type_bytes(b, unhex(line + 2, b));
      pump(30);
    } else if (line[0] == 'W') {
      long until = now_ms() + atoi(line + 2);
      while (now_ms() < until) pump((int)(until - now_ms()));
    } else if (line[0] == 'R') {
      int c, r;
      sscanf(line + 2, "%d %d", &c, &r);
      resize(c, r);
      pump(50);
    } else if (line[0] == 'M') {
      /* how much output there is now, a line of OUT.marks: the screen at
         this moment is the output up to there */
      fprintf(marks, "%lu\n", (unsigned long)ngot);
      fflush(marks);
    } else if (line[0] == 'K') {
      signal_child(atoi(line + 2));
      pump(50);
    } else if (line[0] == 'U') {
      size_t n = unhex(line + 2, b);
      const char *t = strrchr(line, ' ');
      long until = now_ms() + (t ? atoi(t + 1) : 10000);
      long at;
      while ((at = found(b, n)) < 0) {
        if (now_ms() >= until) { fprintf(stderr, "ptydrive: timed out at: %s", line); finish(); return 3; }
        pump(100);
      }
      mark = (size_t)at;
    }
  }
  return finish();
}

#ifdef _WIN32
#include <windows.h>

static HPCON pc;
static HANDLE in_w, out_r;
static PROCESS_INFORMATION pi;
static CRITICAL_SECTION lock;
static unsigned char *pend;
static size_t npend, cpend;

static long now_ms(void) { return (long)GetTickCount64(); }

/* ConPTY must be drained or the child blocks: a thread reads all along */
static DWORD WINAPI reader(LPVOID unused) {
  (void)unused;
  unsigned char b[4096];
  DWORD n;
  while (ReadFile(out_r, b, sizeof b, &n, NULL) && n > 0) {
    EnterCriticalSection(&lock);
    if (npend + n > cpend) { cpend = (npend + n) * 2; pend = realloc(pend, cpend); }
    memcpy(pend + npend, b, n);
    npend += n;
    LeaveCriticalSection(&lock);
  }
  return 0;
}

static int pump(int ms) {
  long until = now_ms() + ms;
  do {
    EnterCriticalSection(&lock);
    if (npend) { keep(pend, npend); npend = 0; }
    LeaveCriticalSection(&lock);
    Sleep(10);
  } while (now_ms() < until);
  return 0;
}

static void type_bytes(const unsigned char *b, size_t n) {
  DWORD w;
  WriteFile(in_w, b, (DWORD)n, &w, NULL);
}

static void signal_child(int sig) { (void)sig; }

static void resize(int cols, int rows) { ResizePseudoConsole(pc, (COORD){(SHORT)cols, (SHORT)rows}); }

static int start(int cols, int rows, char **argv) {
  HANDLE in_r, out_w;
  InitializeCriticalSection(&lock);
  if (!CreatePipe(&in_r, &in_w, NULL, 0) || !CreatePipe(&out_r, &out_w, NULL, 0)) return -1;
  if (CreatePseudoConsole((COORD){(SHORT)cols, (SHORT)rows}, in_r, out_w, 0, &pc) != S_OK) return -1;
  CloseHandle(in_r);
  CloseHandle(out_w);
  STARTUPINFOEXA si;
  SIZE_T sz = 0;
  memset(&si, 0, sizeof si);
  si.StartupInfo.cb = sizeof si;
  /* the driver's own stdio may be pipes (ssh, make): without this the
     child inherits them and writes past the pseudo-console */
  si.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
  InitializeProcThreadAttributeList(NULL, 1, 0, &sz);
  si.lpAttributeList = malloc(sz);
  InitializeProcThreadAttributeList(si.lpAttributeList, 1, 0, &sz);
  UpdateProcThreadAttribute(si.lpAttributeList, 0, PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE, pc, sizeof pc, NULL, NULL);
  static char cmd[32768];
  cmd[0] = 0;
  for (char **a = argv; *a; a++) {
    if (a != argv) strcat(cmd, " ");
    strcat(cmd, "\"");
    strcat(cmd, *a);
    strcat(cmd, "\"");
  }
  if (!CreateProcessA(NULL, cmd, NULL, NULL, FALSE, EXTENDED_STARTUPINFO_PRESENT, NULL, NULL, &si.StartupInfo, &pi)) return -1;
  CreateThread(NULL, 0, reader, NULL, 0, NULL);
  return 0;
}

static int finish(void) {
  DWORD code = 124;
  if (WaitForSingleObject(pi.hProcess, 20000) != WAIT_OBJECT_0) TerminateProcess(pi.hProcess, 124);
  GetExitCodeProcess(pi.hProcess, &code);
  pump(200);
  ClosePseudoConsole(pc);
  fclose(outf);
  return (int)code;
}

#else
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#if defined(__APPLE__)
#include <util.h>
#else
#include <pty.h>
#endif

static int master = -1;
static pid_t child;

static long now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1000L + t.tv_nsec / 1000000L;
}

static int pump(int ms) {
  struct pollfd p = {master, POLLIN, 0};
  unsigned char b[4096];
  long until = now_ms() + ms;
  for (;;) {
    long left = until - now_ms();
    int r = poll(&p, 1, left > 0 ? (int)left : 0);
    if (r > 0) {
      ssize_t n = read(master, b, sizeof b);
      if (n <= 0) return -1;
      keep(b, (size_t)n);
      continue;
    }
    if (left <= 0) return 0;
  }
}

static void type_bytes(const unsigned char *b, size_t n) {
  while (n > 0) {
    ssize_t w = write(master, b, n);
    if (w < 0) { if (errno == EINTR) continue; return; }
    b += w;
    n -= (size_t)w;
  }
}

static void resize(int cols, int rows) {
  struct winsize w = {(unsigned short)rows, (unsigned short)cols, 0, 0};
  ioctl(master, TIOCSWINSZ, &w);
}

/* to the child's process group: forkpty made it a session's leader */
static void signal_child(int sig) { kill(-child, sig); }

static int start(int cols, int rows, char **argv) {
  struct winsize w = {(unsigned short)rows, (unsigned short)cols, 0, 0};
  child = forkpty(&master, NULL, NULL, &w);
  if (child < 0) return -1;
  if (child == 0) {
    execvp(argv[0], argv);
    perror("ptydrive: exec");
    _exit(127);
  }
  return 0;
}

static int finish(void) {
  int st = 0;
  long until = now_ms() + 20000;
  for (;;) {
    pump(50);
    pid_t r = waitpid(child, &st, WNOHANG);
    if (r == child) break;
    if (now_ms() > until) { kill(child, SIGKILL); waitpid(child, &st, 0); fclose(outf); return 124; }
  }
  pump(100);
  fclose(outf);
  return WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st);
}
#endif

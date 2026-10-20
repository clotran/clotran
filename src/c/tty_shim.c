/* The terminal under the REPL's line editor (src/clj/clotran/lineedit.cljf,
 * model/lineedit.lisp): raw mode on and off, keystrokes as UTF-8 bytes, the
 * width. Everything else -- keys, the buffer, the screen -- is Clojure.
 *
 *   clotran_tty_is()         1 when standard input and output are terminals
 *   clotran_tty_raw(on)      raw (1) or as it was (0): 0, or -1
 *   clotran_tty_cols()       the window's width in columns (80 if unknown)
 *   clotran_tty_read(b, n)   up to n bytes typed: how many, 0 at end of
 *                            input, -2 when the window changed size
 *   clotran_tty_wait(ms)     1 when a key comes within ms, else 0
 *   clotran_tty_suspend()    Ctrl-Z: the terminal put back, the process
 *                            stopped, raw again once it is continued
 *
 * POSIX: termios, as cfmakeraw but keeping output processing (\n is still
 * \r\n for whatever the editor does not draw); the state as it was is put
 * back by clotran_tty_raw(0), at exit, and on a fatal signal before it is
 * raised again -- never a terminal left raw. A read waiting for a key
 * looks five times a second whether SIGWINCH came.
 * Windows: the console's modes, VT input and output, line input, echo
 * and Ctrl-C processing off; ReadConsoleInputW's key events made UTF-8. */
#include <string.h>
#include <stdlib.h>
#ifdef _WIN32
#include <windows.h>

static DWORD in_mode, out_mode;
static UINT in_cp, out_cp;
static int raw_on;

/* the console's code pages as they were, at exit: UTF-8 while clotran
   runs, as bin\clotran.cmd sets them, so the editor's and the program's
   UTF-8 show as what they are */
static void restore_cp(void) {
  if (out_cp) SetConsoleOutputCP(out_cp);
  if (in_cp) SetConsoleCP(in_cp);
}

int clotran_tty_is(void) {
  DWORD m;
  return GetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), &m) &&
         GetConsoleMode(GetStdHandle(STD_OUTPUT_HANDLE), &m);
}

static void restore(void) {
  if (!raw_on) return;
  SetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), in_mode);
  SetConsoleMode(GetStdHandle(STD_OUTPUT_HANDLE), out_mode);
  raw_on = 0;
}

int clotran_tty_raw(int on) {
  static int registered;
  HANDLE in = GetStdHandle(STD_INPUT_HANDLE), out = GetStdHandle(STD_OUTPUT_HANDLE);
  if (!on) { restore(); return 0; }
  if (raw_on) return 0;
  if (!GetConsoleMode(in, &in_mode) || !GetConsoleMode(out, &out_mode)) return -1;
  if (!registered) {
    atexit(restore);
    out_cp = GetConsoleOutputCP();
    in_cp = GetConsoleCP();
    atexit(restore_cp);
    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCP(CP_UTF8);
    registered = 1;
  }
  /* quick edit (selecting with the mouse) kept as the user has it */
  DWORD i = (in_mode & ~(ENABLE_LINE_INPUT | ENABLE_ECHO_INPUT | ENABLE_PROCESSED_INPUT))
            | ENABLE_VIRTUAL_TERMINAL_INPUT | ENABLE_WINDOW_INPUT;
  if (!SetConsoleMode(in, i)) return -1;
  SetConsoleMode(out, out_mode | ENABLE_PROCESSED_OUTPUT | ENABLE_VIRTUAL_TERMINAL_PROCESSING);
  raw_on = 1;
  return 0;
}

int clotran_tty_cols(void) {
  CONSOLE_SCREEN_BUFFER_INFO b;
  if (GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &b))
    return b.srWindow.Right - b.srWindow.Left + 1;
  return 80;
}

/* key events as UTF-8; a surrogate pair may be split over two events */
long clotran_tty_read(char *buf, long cap) {
  static WCHAR high;
  HANDLE in = GetStdHandle(STD_INPUT_HANDLE);
  long n = 0;
  if (cap < 8) return -1;
  for (;;) {
    INPUT_RECORD r[64];
    DWORD got = 0, avail = 0;
    /* more than one event read only while they are already there */
    if (n > 0 && (!GetNumberOfConsoleInputEvents(in, &avail) || avail == 0)) return n;
    if (!ReadConsoleInputW(in, r, n > 0 ? (avail < 64 ? avail : 64) : 1, &got)) return n > 0 ? n : 0;
    for (DWORD k = 0; k < got; k++) {
      if (r[k].EventType == WINDOW_BUFFER_SIZE_EVENT && n == 0) return -2;
      if (r[k].EventType != KEY_EVENT) continue;
      /* a key's character comes with its press -- but one outside the keyboard
         (an emoji, through ConPTY or an IME) comes as Alt and a numpad code,
         the character on Alt's release */
      if (!r[k].Event.KeyEvent.bKeyDown && r[k].Event.KeyEvent.wVirtualKeyCode != VK_MENU) continue;
      WCHAR c = r[k].Event.KeyEvent.uChar.UnicodeChar;
      if (c == 0) continue;
      WCHAR w[2]; int nw = 0;
      if (c >= 0xD800 && c < 0xDC00) { high = c; continue; }
      if (c >= 0xDC00 && c < 0xE000) { if (!high) continue; w[nw++] = high; high = 0; }
      w[nw++] = c;
      for (int rep = r[k].Event.KeyEvent.wRepeatCount; rep > 0; rep--) {
        if (n + 8 > cap) return n;
        n += WideCharToMultiByte(CP_UTF8, 0, w, nw, buf + n, (int)(cap - n), NULL, NULL);
      }
    }
  }
}

int clotran_tty_wait(int ms) {
  return WaitForSingleObject(GetStdHandle(STD_INPUT_HANDLE), (DWORD)ms) == WAIT_OBJECT_0;
}

void clotran_tty_suspend(void) {}

#else
#include <errno.h>
#include <signal.h>
#include <poll.h>
#include <termios.h>
#include <unistd.h>
#include <sys/ioctl.h>

static struct termios saved;
static volatile sig_atomic_t raw_on, resized;

int clotran_tty_is(void) { return isatty(0) && isatty(1); }

static void restore(void) {
  if (raw_on) { tcsetattr(0, TCSAFLUSH, &saved); raw_on = 0; }
}

static void on_fatal(int sig) {
  restore();
  signal(sig, SIG_DFL);
  raise(sig);
}

static void on_winch(int sig) { (void)sig; resized = 1; }

int clotran_tty_raw(int on) {
  static int registered;
  if (!on) { restore(); return 0; }
  if (raw_on) return 0;
  if (tcgetattr(0, &saved) != 0) return -1;
  if (!registered) {
    struct sigaction sa;
    int fatal[] = {SIGHUP, SIGTERM, SIGQUIT, SIGABRT, SIGSEGV, SIGBUS};
    atexit(restore);
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_fatal;
    sigemptyset(&sa.sa_mask);
    for (unsigned k = 0; k < sizeof fatal / sizeof *fatal; k++) {
      struct sigaction old;
      /* a handler someone else installed is theirs to keep */
      if (sigaction(fatal[k], NULL, &old) == 0 && old.sa_handler == SIG_DFL) sigaction(fatal[k], &sa, NULL);
    }
    sa.sa_handler = on_winch; /* no SA_RESTART: the read returns */
    sigaction(SIGWINCH, &sa, NULL);
    registered = 1;
  }
  struct termios t = saved;
  t.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL | IXON);
  t.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
  t.c_cflag |= CS8;
  t.c_cc[VMIN] = 1;
  t.c_cc[VTIME] = 0;
  if (tcsetattr(0, TCSAFLUSH, &t) != 0) return -1;
  raw_on = 1;
  return 0;
}

int clotran_tty_cols(void) {
  struct winsize w;
  if (ioctl(1, TIOCGWINSZ, &w) == 0 && w.ws_col > 0) return w.ws_col;
  return 80;
}

long clotran_tty_read(char *buf, long cap) {
  for (;;) {
    struct pollfd p = {0, POLLIN, 0};
    if (resized) { resized = 0; return -2; }
    /* SIGWINCH may land on another thread: a read that waits is woken
       to look at the flag five times a second */
    int r = poll(&p, 1, 200);
    if (r == 0 || (r < 0 && errno == EINTR)) continue;
    long n = read(0, buf, (size_t)cap);
    if (n < 0 && errno == EINTR) continue;
    return n < 0 ? 0 : n;
  }
}

int clotran_tty_wait(int ms) {
  struct pollfd p = {0, POLLIN, 0};
  return poll(&p, 1, ms) > 0;
}

void clotran_tty_suspend(void) {
  int was = raw_on;
  restore();
  kill(0, SIGTSTP);
  if (was) clotran_tty_raw(1);
}
#endif

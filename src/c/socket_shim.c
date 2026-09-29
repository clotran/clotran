/* socket_shim.c -- see socket_shim.h. POSIX and Winsock differ in four
 * places, each behind one #ifdef below: startup, the handle type, how a
 * socket is closed, and where the last error is read. */
#include "socket_shim.h"

#include <stdio.h>
#include <string.h>

#ifdef _WIN32
#  ifndef _WIN32_WINNT
#    define _WIN32_WINNT 0x0600   /* WSAPoll */
#  endif
#  include <winsock2.h>
#  include <ws2tcpip.h>
typedef SOCKET sock_t;
#  define BAD_SOCK INVALID_SOCKET
#  define poll WSAPoll
#  define CLOSE_SOCK closesocket
#  define SHUT_BOTH SD_BOTH
static int last_err(void) { return WSAGetLastError(); }
static int interrupted(int e) { return e == WSAEINTR; }
#else
#  include <errno.h>
#  include <netdb.h>
#  include <poll.h>
#  include <signal.h>
#  include <sys/socket.h>
#  include <netinet/in.h>
#  include <unistd.h>
typedef int sock_t;
#  define BAD_SOCK (-1)
#  define CLOSE_SOCK close
#  define SHUT_BOTH SHUT_RDWR
static int last_err(void) { return errno; }
static int interrupted(int e) { return e == EINTR; }
#endif

#ifdef MSG_NOSIGNAL
#  define SEND_FLAGS MSG_NOSIGNAL
#else
#  define SEND_FLAGS 0
#endif

static void say(char *err, int32_t errcap, const char *what, int code) {
    if (!err || errcap <= 0) return;
#ifdef _WIN32
    snprintf(err, (size_t)errcap, "%s (error %d)", what, code);
#else
    snprintf(err, (size_t)errcap, "%s: %s", what, strerror(code));
#endif
}

static int32_t cs_init(char *err, int32_t errcap) {
#ifdef _WIN32
    WSADATA d;
    int r = WSAStartup(MAKEWORD(2, 2), &d);
    if (r != 0) { say(err, errcap, "WSAStartup", r); return -1; }
#else
    (void)err; (void)errcap;
    signal(SIGPIPE, SIG_IGN);
#endif
    return 0;
}

/* Waits until h is readable, up to ms: 1 ready, 0 timeout, -1 error. */
static int wait_readable(sock_t h, int32_t ms) {
    struct pollfd p;
    for (;;) {
        p.fd = h; p.events = POLLIN; p.revents = 0;
        int r = poll(&p, 1, ms < 0 ? -1 : ms);
        if (r < 0 && interrupted(last_err())) continue;
        return r < 0 ? -1 : (r == 0 ? 0 : 1);
    }
}

static struct addrinfo *resolve(const char *host, int32_t port, int passive, char *err, int32_t errcap) {
    struct addrinfo hints, *res = NULL;
    char service[16];
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (passive) hints.ai_flags = AI_PASSIVE;
    snprintf(service, sizeof service, "%d", (int)port);
    int r = getaddrinfo((host && *host) ? host : NULL, service, &hints, &res);
    if (r != 0) {
        if (err && errcap > 0) snprintf(err, (size_t)errcap, "cannot resolve %s: %s", host ? host : "", gai_strerror(r));
        return NULL;
    }
    return res;
}

static void no_sigpipe(sock_t s) {
#ifdef SO_NOSIGPIPE
    int one = 1;
    setsockopt(s, SOL_SOCKET, SO_NOSIGPIPE, (const char *)&one, sizeof one);
#else
    (void)s;
#endif
}

/* once per process, from the calls that make a socket; repeating it is
 * harmless (signal is idempotent, WSAStartup counts) */
static int ready = 0;
static int32_t ensure_init(char *err, int32_t errcap) {
    if (ready) return 0;
    if (cs_init(err, errcap) != 0) return -1;
    ready = 1;
    return 0;
}

int64_t cs_listen(const char *host, int32_t port, int32_t backlog, char *err, int32_t errcap) {
    if (ensure_init(err, errcap) != 0) return -1;
    struct addrinfo *res = resolve(host, port, 1, err, errcap), *a;
    int code = 0;
    if (!res) return -1;
    for (a = res; a; a = a->ai_next) {
        sock_t s = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
        if (s == BAD_SOCK) { code = last_err(); continue; }
        int one = 1;
        setsockopt(s, SOL_SOCKET, SO_REUSEADDR, (const char *)&one, sizeof one);
        if (bind(s, a->ai_addr, (int)a->ai_addrlen) == 0 && listen(s, backlog > 0 ? backlog : 50) == 0) {
            freeaddrinfo(res);
            return (int64_t)s;
        }
        code = last_err();
        CLOSE_SOCK(s);
    }
    freeaddrinfo(res);
    say(err, errcap, "cannot listen", code);
    return -1;
}

int32_t cs_local_port(int64_t h) {
    struct sockaddr_storage ss;
    socklen_t n = sizeof ss;
    if (getsockname((sock_t)h, (struct sockaddr *)&ss, &n) != 0) return -1;
    if (ss.ss_family == AF_INET) return ntohs(((struct sockaddr_in *)&ss)->sin_port);
    if (ss.ss_family == AF_INET6) return ntohs(((struct sockaddr_in6 *)&ss)->sin6_port);
    return -1;
}

int64_t cs_accept(int64_t h, int32_t ms, char *err, int32_t errcap) {
    int w = wait_readable((sock_t)h, ms);
    if (w == 0) return -2;
    if (w < 0) { say(err, errcap, "accept", last_err()); return -1; }
    for (;;) {
        sock_t c = accept((sock_t)h, NULL, NULL);
        if (c != BAD_SOCK) { no_sigpipe(c); return (int64_t)c; }
        if (interrupted(last_err())) continue;
        say(err, errcap, "accept", last_err());
        return -1;
    }
}

int64_t cs_connect(const char *host, int32_t port, char *err, int32_t errcap) {
    if (ensure_init(err, errcap) != 0) return -1;
    struct addrinfo *res = resolve(host, port, 0, err, errcap), *a;
    int code = 0;
    if (!res) return -1;
    for (a = res; a; a = a->ai_next) {
        sock_t s = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
        if (s == BAD_SOCK) { code = last_err(); continue; }
        if (connect(s, a->ai_addr, (int)a->ai_addrlen) == 0) {
            freeaddrinfo(res);
            no_sigpipe(s);
            return (int64_t)s;
        }
        code = last_err();
        CLOSE_SOCK(s);
    }
    freeaddrinfo(res);
    say(err, errcap, "cannot connect", code);
    return -1;
}

/* How many bytes the UTF-8 sequence led by b has in all; 1 for a byte
 * that leads nothing. */
static int utf8_len(unsigned char b) {
    if (b >= 0xF0) return 4;
    if (b >= 0xE0) return 3;
    if (b >= 0xC0) return 2;
    return 1;
}

static int recv_some(sock_t h, char *buf, int32_t n) {
    for (;;) {
        int r = recv(h, buf, n, 0);
        if (r < 0 && interrupted(last_err())) continue;
        return r;
    }
}

int32_t cs_read(int64_t h, char *buf, int32_t cap, int32_t ms, char *err, int32_t errcap) {
    if (cap < 4) { say(err, errcap, "read", 0); return -1; }
    int w = wait_readable((sock_t)h, ms);
    if (w == 0) return -2;
    if (w < 0) { say(err, errcap, "read", last_err()); return -1; }
    int n = recv_some((sock_t)h, buf, cap - 3);
    if (n < 0) { say(err, errcap, "read", last_err()); return -1; }
    if (n == 0) return 0;
    /* the last character complete: find where it starts, then read the
     * bytes it still lacks (there is room: cap - 3 above) */
    int i = n - 1;
    while (i > 0 && n - i < 4 && ((unsigned char)buf[i] & 0xC0) == 0x80) i--;
    int need = utf8_len((unsigned char)buf[i]) - (n - i);
    while (need > 0) {
        int r = recv_some((sock_t)h, buf + n, need);
        if (r <= 0) break;   /* the peer went mid-character: hand over what came */
        n += r;
        need -= r;
    }
    return n;
}

int32_t cs_read_raw(int64_t h, char *buf, int32_t cap, int32_t ms, char *err, int32_t errcap) {
    int w = wait_readable((sock_t)h, ms);
    if (w == 0) return -2;
    if (w < 0) { say(err, errcap, "read", last_err()); return -1; }
    int n = recv_some((sock_t)h, buf, cap);
    if (n < 0) { say(err, errcap, "read", last_err()); return -1; }
    return n;
}

int32_t cs_write(int64_t h, const char *buf, int32_t len, char *err, int32_t errcap) {
    int32_t done = 0;
    while (done < len) {
        int r = send((sock_t)h, buf + done, len - done, SEND_FLAGS);
        if (r < 0) {
            if (interrupted(last_err())) continue;
            say(err, errcap, "write", last_err());
            return -1;
        }
        done += r;
    }
    return done;
}

int32_t cs_close(int64_t h) {
    shutdown((sock_t)h, SHUT_BOTH);
    return CLOSE_SOCK((sock_t)h) == 0 ? 0 : -1;
}

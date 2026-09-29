/* socket_shim.h -- the whole of what clotran needs from the OS's sockets,
 * the same on POSIX (macOS, Linux) and Windows (Winsock). Fortran reaches
 * it through iso_c_binding (Socket.f90) and never sees a sockaddr: an
 * address is a host name and a port, resolved here with getaddrinfo, so
 * macOS's sin_len, Linux's lack of it and IPv4 against IPv6 stay in C.
 *
 * A socket is an int64 handle (a POSIX fd, or a Windows SOCKET, which is
 * pointer-sized). Every call that can fail returns a negative number and
 * writes a short message into err (truncated to errcap - 1, always
 * NUL-terminated); a timeout is -2, distinct from an error (-1). A wait
 * in ms: negative is no limit.
 */
#ifndef CLOTRAN_SOCKET_SHIM_H
#define CLOTRAN_SOCKET_SHIM_H

#include <stdint.h>

/* The first listen or connect starts the library: WSAStartup on Windows,
 * SIGPIPE ignored on POSIX (a write to a closed peer is an error return,
 * not a signal). */

/* A listening socket bound to host (NULL or "" is every interface; a
 * name or a numeric address) and port (0 picks a free one). */
int64_t cs_listen(const char *host, int32_t port, int32_t backlog, char *err, int32_t errcap);

/* The port a socket is bound to: the one port 0 picked. */
int32_t cs_local_port(int64_t h);

/* The next connection, waiting up to ms; -2 at the timeout. */
int64_t cs_accept(int64_t h, int32_t ms, char *err, int32_t errcap);

/* A connection to host:port. */
int64_t cs_connect(const char *host, int32_t port, char *err, int32_t errcap);

/* Up to cap bytes into buf, waiting up to ms: the count, 0 at the end of
 * the stream, -2 at the timeout. Ends on a whole UTF-8 character: a
 * character split across two arrivals is completed before returning, so
 * the caller can decode each read on its own (cap must be at least 4). */
int32_t cs_read(int64_t h, char *buf, int32_t cap, int32_t ms, char *err, int32_t errcap);

/* Up to cap bytes, as they came -- no character completed: for a binary
 * protocol (bencode counts bytes). Otherwise as cs_read. */
int32_t cs_read_raw(int64_t h, char *buf, int32_t cap, int32_t ms, char *err, int32_t errcap);

/* All len bytes, or an error. */
int32_t cs_write(int64_t h, const char *buf, int32_t len, char *err, int32_t errcap);

/* Ends both directions, waking a thread blocked reading it, then closes. */
int32_t cs_close(int64_t h);

#endif

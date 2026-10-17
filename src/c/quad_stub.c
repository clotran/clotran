/* quad_stub.c -- the five libquadmath entry points libgfortran's formatted
 * I/O refers to, defined here so the static link takes nothing from
 * libquadmath (LGPL, which the GCC Runtime Library Exception does not
 * cover). A name an object already defines is never pulled from an
 * archive, so with these five present no libquadmath code reaches
 * clotran-bin, nor a program `clotran build` copies it into
 * (check-no-libquadmath).
 *
 * clotran has no 128-bit real: libgfortran calls these only to format or
 * read a real(16), which clotran never does. Reaching one is therefore a
 * bug, and stops the program rather than answering wrongly. The arguments
 * are never read, so no prototype here needs __float128, which clang on
 * arm64 macOS lacks. A Fortran package loads its own libgfortran, and
 * with it its own libquadmath: these are hidden from it (macOS) or bound
 * by DLL name (Windows), and never linked on Linux, where glibc's
 * _Float128 serves libgfortran instead and an exported definition
 * would interpose on a package's libquadmath.so. */
#include <stdio.h>
#include <stdlib.h>

#if defined(__GNUC__) && !defined(_WIN32)
#define QUAD_STUB __attribute__((visibility("hidden"), noreturn))
#else
#define QUAD_STUB __attribute__((noreturn))
#endif

QUAD_STUB static void no_quad(const char *name) {
  fprintf(stderr, "clotran: %s: 128-bit real I/O is not supported\n", name);
  abort();
}

QUAD_STUB void quadmath_snprintf(void) { no_quad("quadmath_snprintf"); }
QUAD_STUB void strtoflt128(void) { no_quad("strtoflt128"); }
QUAD_STUB void isinfq(void) { no_quad("isinfq"); }
QUAD_STUB void isnanq(void) { no_quad("isnanq"); }
QUAD_STUB void signbitq(void) { no_quad("signbitq"); }

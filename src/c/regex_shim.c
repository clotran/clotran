/* regex_shim.c -- see regex_shim.h. Everything here is a thin call into
 * ICU's uregex_* C API (unicode/uregex.h); the header does the ICU
 * version-suffix renaming (uregex_open becomes uregex_open_78, etc.),
 * which is why every ICU call goes through the real header rather than
 * a hand-written prototype -- the renamed symbols are all the linker
 * ever sees.
 *
 * ICU matches over UChar (UTF-16 code units); clotran's strings are
 * UTF-8 bytes, so the subject and the pattern are DECODED on the way
 * in (widen), and the offsets ICU reports are character indices that
 * Fortran turns back into byte positions with u8_off/u8_slice (GC.f90).
 * Text that is not valid UTF-8 is widened byte for byte instead. What
 * follows in this comment is the history of the one-byte version:
 * decoding here; nothing in this codebase currently does one.
 */
#include "regex_shim.h"
#include <unicode/uregex.h>
#include <unicode/utypes.h>
#include <unicode/ustring.h>
#include <stdlib.h>
#include <string.h>

/* UTF-8 to UTF-16, so a multibyte string matches as its characters
 * and every offset ICU reports is a character index (a UTF-16 unit; the
 * same thing off the astral plane), which is what Fortran's u8_slice
 * takes. Bytes that are not UTF-8 -- Latin-1 read from a file -- are
 * widened one byte to one unit instead, as everything once was. */
static UChar *widen(const char *bytes, int32_t len, int32_t *ulen) {
  UErrorCode status = U_ZERO_ERROR;
  UChar *out = (UChar *)malloc((size_t)(len > 0 ? len : 1) * sizeof(UChar));
  int32_t i, n = 0;
  if (!out) return NULL;
  u_strFromUTF8(out, len, &n, bytes, len, &status);
  if (U_FAILURE(status)) {
    for (i = 0; i < len; i++) out[i] = (UChar)(unsigned char)bytes[i];
    n = len;
  }
  *ulen = n;
  return out;
}

void *cre_compile(const char *pattern, int32_t pattern_len,
                   char *err_buf, int32_t err_cap) {
  UErrorCode status = U_ZERO_ERROR;
  UParseError pe;
  URegularExpression *re;
  UChar *upattern;
  int32_t ulen;

  if (err_cap > 0) err_buf[0] = '\0';
  memset(&pe, 0, sizeof(pe));

  upattern = widen(pattern, pattern_len, &ulen);
  if (!upattern) {
    if (err_cap > 0) strncpy(err_buf, "out of memory", (size_t)err_cap - 1);
    return NULL;
  }
  re = uregex_open(upattern, ulen, 0, &pe, &status);
  free(upattern);
  if (U_FAILURE(status)) {
    if (err_cap > 0) {
      strncpy(err_buf, u_errorName(status), (size_t)err_cap - 1);
      err_buf[err_cap - 1] = '\0';
    }
    return NULL;
  }
  return re;
}

void *cre_clone(void *handle) {
  UErrorCode status = U_ZERO_ERROR;
  URegularExpression *re;
  if (!handle) return NULL;
  re = uregex_clone((const URegularExpression *)handle, &status);
  if (U_FAILURE(status)) return NULL;
  return re;
}

/* Frees the subject text this handle is holding, if any.
 *
 * ICU keeps only a shallow reference to the buffer we passed to
 * uregex_setText, so uregex_getText hands back OUR pointer and nothing
 * else can free it. Casting away const is the point: this memory is
 * ours, not ICU's.
 *
 * A clone does not share it -- uregex_clone's contract says the input
 * string is not cloned -- so no handle can free another's text. */
/* Frees one subject-text buffer that cre_set_text handed out.
 *
 * The CALLER owns it, not this file and not ICU. An earlier attempt
 * asked uregex_getText for the pointer instead -- which aborts, because
 * a handle that never had setText called on it answers with something
 * ICU owns, and a compiled pattern is exactly that. Guessing whether a
 * pointer is ours is not something malloc forgives. */
void cre_free_text(void *buf) {
  if (buf) free(buf);
}

void cre_close(void *handle) {
  if (handle) uregex_close((URegularExpression *)handle);
}

int32_t cre_set_text(void *handle, const char *text, int32_t text_len,
                     void **out_buf) {
  UErrorCode status = U_ZERO_ERROR;
  UChar *utext;
  int32_t ulen;
  if (!handle) return -1;
  utext = widen(text, text_len, &ulen);
  if (!utext) return -1;
  /* ICU keeps only a shallow reference to this buffer -- uregex_setText's
   * own doc says so -- never copying or freeing it, so it must outlive
   * every call that follows on this handle. It is never freed here
   * either: a bounded per-Matcher leak, the same trade-off gc_value
   * itself makes by having no FINAL and no destructor. A Matcher's text
   * is set once, used through a short find/matches loop, and the
   * process is short-lived (a REPL or a bootstrap run), so the leak is
   * bytes, not an unbounded one. */
  uregex_setText((URegularExpression *)handle, utext, ulen, &status);
  if (U_FAILURE(status)) {
    free(utext);
    return -1;
  }
  /* Handed to the caller, which keeps it alongside the handle and frees
   * it through cre_free_text when the Matcher is collected. */
  if (out_buf) *out_buf = utext;
  return 0;
}

int32_t cre_matches(void *handle) {
  UErrorCode status = U_ZERO_ERROR;
  UBool r;
  if (!handle) return -1;
  r = uregex_matches((URegularExpression *)handle, -1, &status);
  if (U_FAILURE(status)) return -1;
  return r ? 1 : 0;
}

int32_t cre_find_next(void *handle) {
  UErrorCode status = U_ZERO_ERROR;
  UBool r;
  if (!handle) return -1;
  r = uregex_findNext((URegularExpression *)handle, &status);
  if (U_FAILURE(status)) return -1;
  return r ? 1 : 0;
}

int32_t cre_group_count(void *handle) {
  UErrorCode status = U_ZERO_ERROR;
  int32_t n;
  if (!handle) return -1;
  n = uregex_groupCount((URegularExpression *)handle, &status);
  if (U_FAILURE(status)) return -1;
  return n;
}

int32_t cre_group_span(void *handle, int32_t idx, int32_t *start, int32_t *end) {
  UErrorCode status = U_ZERO_ERROR;
  int32_t s, e;
  if (!handle) return -1;
  s = uregex_start((URegularExpression *)handle, idx, &status);
  if (U_FAILURE(status)) return -1;
  e = uregex_end((URegularExpression *)handle, idx, &status);
  if (U_FAILURE(status)) return -1;
  if (s < 0) return 0;
  *start = s;
  *end = e;
  return 1;
}

/* --- Character ----------------------------------------------------
 * java.lang.Character's predicates and case maps over a code point,
 * answered by ICU (unicode/uchar.h). u_isWhitespace is documented as
 * Java's Character.isWhitespace: the separators less the no-break
 * spaces, plus the C0 controls Java counts. The case maps are the
 * SIMPLE ones, one code point to one. */
#include <unicode/uchar.h>

int32_t cu_isws(int32_t cp)    { return u_isWhitespace((UChar32)cp) ? 1 : 0; }
int32_t cu_isalpha(int32_t cp) { return u_isalpha((UChar32)cp) ? 1 : 0; }
int32_t cu_isdigit(int32_t cp) { return u_isdigit((UChar32)cp) ? 1 : 0; }
int32_t cu_isupper(int32_t cp) { return u_isupper((UChar32)cp) ? 1 : 0; }
int32_t cu_islower(int32_t cp) { return u_islower((UChar32)cp) ? 1 : 0; }
int32_t cu_isalnum(int32_t cp) { return u_isalnum((UChar32)cp) ? 1 : 0; }
int32_t cu_toupper(int32_t cp) { return (int32_t)u_toupper((UChar32)cp); }
int32_t cu_tolower(int32_t cp) { return (int32_t)u_tolower((UChar32)cp); }

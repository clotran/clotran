/* regex_shim.c -- see regex_shim.h. Everything here is a thin call into
 * ICU's uregex_* C API (unicode/uregex.h); the header does the ICU
 * version-suffix renaming (uregex_open becomes uregex_open_78, etc.),
 * which is why every ICU call goes through the real header rather than
 * a hand-written prototype -- the renamed symbols are all the linker
 * ever sees.
 *
 * ICU matches over UChar (UTF-16 code units); clotran's strings are
 * plain byte buffers, one byte per character, matching the Latin-1/
 * ASCII assumption already made throughout GC.f90. So every byte is
 * WIDENED to a UChar with the high byte zero, never decoded as UTF-8 --
 * which keeps a UTF-16 offset numerically identical to a byte offset,
 * so Fortran can slice its own buffer directly off uregex_start/_end
 * with no conversion at all. A real multibyte string would need real
 * decoding here; nothing in this codebase currently does one.
 */
#include "regex_shim.h"
#include <unicode/uregex.h>
#include <unicode/utypes.h>
#include <stdlib.h>
#include <string.h>

static UChar *widen(const char *bytes, int32_t len) {
  UChar *out = (UChar *)malloc((size_t)(len > 0 ? len : 1) * sizeof(UChar));
  int32_t i;
  if (!out) return NULL;
  for (i = 0; i < len; i++) out[i] = (UChar)(unsigned char)bytes[i];
  return out;
}

void *cre_compile(const char *pattern, int32_t pattern_len,
                   char *err_buf, int32_t err_cap) {
  UErrorCode status = U_ZERO_ERROR;
  UParseError pe;
  URegularExpression *re;
  UChar *upattern;

  if (err_cap > 0) err_buf[0] = '\0';
  memset(&pe, 0, sizeof(pe));

  upattern = widen(pattern, pattern_len);
  if (!upattern) {
    if (err_cap > 0) strncpy(err_buf, "out of memory", (size_t)err_cap - 1);
    return NULL;
  }
  re = uregex_open(upattern, pattern_len, 0, &pe, &status);
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

void cre_close(void *handle) {
  if (handle) uregex_close((URegularExpression *)handle);
}

int32_t cre_set_text(void *handle, const char *text, int32_t text_len) {
  UErrorCode status = U_ZERO_ERROR;
  UChar *utext;
  if (!handle) return -1;
  utext = widen(text, text_len);
  if (!utext) return -1;
  /* ICU keeps only a shallow reference to this buffer -- uregex_setText's
   * own doc says so -- never copying or freeing it, so it must outlive
   * every call that follows on this handle. It is never freed here
   * either: a bounded per-Matcher leak, the same trade-off gc_value
   * itself makes by having no FINAL and no destructor. A Matcher's text
   * is set once, used through a short find/matches loop, and the
   * process is short-lived (a REPL or a bootstrap run), so the leak is
   * bytes, not an unbounded one. */
  uregex_setText((URegularExpression *)handle, utext, text_len, &status);
  if (U_FAILURE(status)) {
    free(utext);
    return -1;
  }
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

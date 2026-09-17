/* regex_shim.h -- the entire surface Fortran needs from ICU's regex
 * engine, chosen to match exactly what core.clj's re-pattern/re-matcher/
 * re-find/re-matches/re-groups/re-seq compile down to: Pattern/compile,
 * .matcher, .find, .matches, .groupCount, .group. Nothing else.
 *
 * Deliberately NOT exposed: text extraction. A matched group's span
 * (start/end) is returned as a UTF-16-code-unit offset, which this
 * project treats as a byte offset -- see NOTES.md on the Latin-1/ASCII
 * assumption already made throughout GC.f90's string handling. Fortran
 * already holds the subject text, so it slices its own buffer rather
 * than round-tripping the substring through this ABI.
 */
#ifndef CLOTRAN_REGEX_SHIM_H
#define CLOTRAN_REGEX_SHIM_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Compiles a pattern. Returns an opaque handle, or NULL on failure with
 * a short message copied into err_buf (truncated to err_cap - 1, always
 * NUL-terminated). Inline flags -- (?i), (?s), (?m) -- are parsed by
 * ICU from the pattern text itself, the same as java.util.regex, so
 * there is no separate flags argument. */
void *cre_compile(const char *pattern, int32_t pattern_len,
                   char *err_buf, int32_t err_cap);

/* An INDEPENDENT copy of a compiled pattern, for one Matcher. Cloning
 * rather than sharing the Pattern's own handle is what lets two
 * Matchers over the same Pattern search two different strings at once
 * without one's position clobbering the other's -- Pattern.matcher(s)
 * in Java has exactly this independence. */
void *cre_clone(void *handle);

void cre_close(void *handle);

/* Sets the subject text on a (cloned) handle, resetting its search
 * position to the start. Returns 0 on success, -1 on error. */
int32_t cre_set_text(void *handle, const char *text, int32_t text_len,
                     void **out_buf);

/* Frees a buffer cre_set_text handed back. The caller owns it: ICU
 * keeps only a shallow reference, so nothing else can free it, and
 * asking ICU for the pointer back is not safe on a handle that never
 * had text set. */
void cre_free_text(void *buf);

/* Matcher.matches(): the WHOLE subject must match, anchored both ends.
 * Returns 1, 0, or -1 on error. */
int32_t cre_matches(void *handle);

/* Matcher.find(): the next match anywhere in the subject, resuming
 * after the previous match's end (or from the start, on the first
 * call) -- ICU's uregex_findNext does exactly this bookkeeping, so none
 * of it needs to live on the Fortran side. Returns 1, 0, or -1. */
int32_t cre_find_next(void *handle);

/* The pattern's total capturing-group count (0 for none), independent
 * of whether a match has happened yet. */
int32_t cre_group_count(void *handle);

/* The span of one group (0 = the whole match) from the most recent
 * successful matches()/find(). Returns 1 and sets the start and end
 * offsets if the group participated, 0 if it exists but did not (an
 * optional group that did not match -- Java's .group(n) is null there),
 * -1 on error or if idx is out of range. */
int32_t cre_group_span(void *handle, int32_t idx, int32_t *start, int32_t *end);

#ifdef __cplusplus
}
#endif

#endif

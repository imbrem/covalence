/*
 * Tiny no-libc compatibility shim used in lieu of `<string.h>` and
 * `<assert.h>` when compiling the BLAKE3 official C reference for
 * wasm32-unknown-unknown with `-nostdlib`.
 *
 * Provides:
 *
 *   - `memcpy(dst, src, n)`   — bytewise copy.
 *   - `memset(dst, c, n)`     — bytewise fill.
 *   - `strlen(s)`             — NUL-terminated string length.
 *   - `assert(cond)`          — compiled out (no-op): the upstream
 *                               asserts live under `#if defined(BLAKE3_TESTING)`,
 *                               so this is the same condition the
 *                               release upstream build hits.
 *
 * Definitions live in `main.c` so each upstream `.c` file stays as
 * close to pristine as the freestanding target allows. The signatures
 * match the C standard library exactly (so toolchains that *do*
 * provide `<string.h>` can drop this shim with no source changes).
 */

#ifndef COV_COMPAT_H
#define COV_COMPAT_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

void *memcpy(void *dst, const void *src, size_t n);
void *memset(void *dst, int c, size_t n);
size_t strlen(const char *s);

#ifdef __cplusplus
}
#endif

#define assert(x) ((void)0)

#endif /* COV_COMPAT_H */

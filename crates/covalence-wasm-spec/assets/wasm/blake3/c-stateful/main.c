/*
 * Canonical-ABI wrapper for the BLAKE3 official C reference (tag 1.8.5).
 *
 * Single-instance "stateful" world (`blake3-stateful.wit`): the module
 * instance IS the hasher object. The plain-mode `blake3_hasher` lives
 * in a static global; `init` resets it via `blake3_hasher_init`.
 *
 * Export-name strategy
 * --------------------
 * Each canonical-ABI export is declared with
 * `__attribute__((export_name("covalence:hash/api@0.1.0#NAME")))`,
 * matching the SHA-256 C variant. wit-component recognises the Legacy
 * mangling and binds these to the `covalence:hash/api` interface
 * without any out-of-band `exports.json` map.
 *
 * Why `hash` lives in C rather than coming from `compose_one_shot`:
 *   the WAT-level wrapper synthesises `hash` by injecting a function
 *   that calls `$init_impl` / `$update_impl` / `$finalize_impl` —
 *   private WAT aliases that don't exist for C sources. For C variants
 *   we emit `hash` directly, and `rebuild.rs` skips compose when the
 *   `hash` export is already present.
 *
 * cabi_realloc
 * ------------
 * Implemented in C as a bump allocator over `__heap_base` (provided by
 * lld at link time) with `__builtin_wasm_memory_{size,grow}` for
 * growth. No free / no resize; matches the SHA-256 C variant.
 *
 * libc shims (`memcpy` / `memset` / `strlen`)
 * -------------------------------------------
 * The BLAKE3 upstream sources call these from `<string.h>`; the
 * freestanding wasm32-unknown-unknown target has no libc. The shim
 * declarations live in `cov_compat.h` (included from blake3_impl.h);
 * the definitions live here in `main.c` so each upstream source file
 * stays as close to pristine as possible.
 */

#include <stddef.h>
#include <stdint.h>

#include "blake3.h"
#include "blake3_impl.h"

typedef unsigned char  u8;
typedef unsigned int   u32;

#define BLAKE3_DIGEST_BYTES BLAKE3_OUT_LEN

/* ─── module-global hasher context ─────────────────────────────────── */

static blake3_hasher CTX;

/* ─── libc shims (definitions; declarations in cov_compat.h) ───────── */

void *memcpy(void *dst, const void *src, size_t n)
{
    u8 *d = (u8 *)dst;
    const u8 *s = (const u8 *)src;
    for (size_t i = 0; i < n; i++) {
        d[i] = s[i];
    }
    return dst;
}

void *memset(void *dst, int c, size_t n)
{
    u8 *d = (u8 *)dst;
    u8 v = (u8)c;
    for (size_t i = 0; i < n; i++) {
        d[i] = v;
    }
    return dst;
}

size_t strlen(const char *s)
{
    size_t i = 0;
    while (s[i] != '\0') {
        i++;
    }
    return i;
}

/* ─── bump allocator (cabi_realloc) ────────────────────────────────── */

/*
 * `__heap_base` is a linker-defined symbol pointing at the first byte
 * past the static data + stack area. Past that point linear memory is
 * unmanaged, free for our bump allocator to carve up.
 */
extern unsigned char __heap_base;

static unsigned int  BUMP        = 0; /* lazily initialised to __heap_base */
static unsigned int  BUMP_INITED = 0;

static unsigned int align_up(unsigned int x, unsigned int a)
{
    unsigned int mask = a - 1u;
    return (x + mask) & ~mask;
}

/*
 * `cabi_realloc(orig_ptr, orig_size, align, new_size)`:
 *   - `orig_ptr == 0`  → fresh allocation of `new_size` bytes.
 *   - `orig_ptr != 0`  → resize (we panic — unused by our exports).
 */
__attribute__((export_name("cabi_realloc")))
void *cabi_realloc(void *orig_ptr, unsigned int orig_size,
                   unsigned int align, unsigned int new_size)
{
    (void)orig_size;
    if (orig_ptr != (void *)0) {
        __builtin_trap();
    }
    if (!BUMP_INITED) {
        BUMP        = (unsigned int)&__heap_base;
        BUMP_INITED = 1;
    }
    if (align == 0) align = 1;
    unsigned int aligned = align_up(BUMP, align);
    unsigned int end     = aligned + new_size;

    unsigned int cur_bytes = (unsigned int)__builtin_wasm_memory_size(0) << 16;
    if (end > cur_bytes) {
        unsigned int need_bytes = end - cur_bytes;
        unsigned int need_pages = (need_bytes + 0xFFFFu) >> 16;
        if (__builtin_wasm_memory_grow(0, need_pages) == (unsigned long)-1L) {
            __builtin_trap();
        }
    }
    BUMP = end;
    return (void *)(unsigned long)aligned;
}

static void bump_reset(void)
{
    BUMP        = (unsigned int)&__heap_base;
    BUMP_INITED = 1;
}

/* ─── canonical-ABI exports ────────────────────────────────────────── */

__attribute__((export_name("covalence:hash/api@0.1.0#init")))
void cov_init(void)
{
    blake3_hasher_init(&CTX);
    /* Reset bump so streaming-then-finalize doesn't accumulate garbage
     * across hash sessions. Matches the WAT variants. */
    bump_reset();
}

__attribute__((export_name("covalence:hash/api@0.1.0#update")))
void cov_update(const u8 *data, u32 len)
{
    blake3_hasher_update(&CTX, data, (size_t)len);
}

/*
 * Canonical-ABI Legacy return for `func() -> list<u8>`: the callee
 * allocates a return area of size 8 (ptr + len), populates it, and
 * returns its pointer. Both the digest buffer (32 bytes) and the
 * return-area pointer come from `cabi_realloc`.
 */
__attribute__((export_name("covalence:hash/api@0.1.0#finalize")))
unsigned int cov_finalize(void)
{
    u8 *digest = (u8 *)cabi_realloc((void *)0, 0, 1, BLAKE3_DIGEST_BYTES);
    blake3_hasher_finalize(&CTX, digest, BLAKE3_DIGEST_BYTES);
    unsigned int *ret = (unsigned int *)cabi_realloc((void *)0, 0, 4, 8);
    ret[0] = (unsigned int)(unsigned long)digest;
    ret[1] = BLAKE3_DIGEST_BYTES;
    return (unsigned int)(unsigned long)ret;
}

/*
 * `compress(state, block) -> list<u8>`:
 *   truncate8(compress(state, block, t=0, b=64, d=0)).
 *
 * `blake3_compress_in_place(cv, block, block_len, counter, flags)`
 * writes the post-XOR top half (8 words) back into `cv`, which is
 * exactly the truncate-to-8 step the WIT spec calls for. We copy the
 * caller's state into a local CV first so the input is not mutated.
 */
__attribute__((export_name("covalence:hash/api@0.1.0#compress")))
unsigned int cov_compress(const u8 *state_ptr, u32 state_len,
                          const u8 *block_ptr, u32 block_len)
{
    if (state_len != 32u || block_len != 64u) __builtin_trap();
    uint32_t cv[8];
    /* LE-decode the 32-byte state into 8 u32 chaining-value words. */
    for (int i = 0; i < 8; i++) {
        cv[i] = ((uint32_t)state_ptr[4*i    ])
              | ((uint32_t)state_ptr[4*i + 1] <<  8)
              | ((uint32_t)state_ptr[4*i + 2] << 16)
              | ((uint32_t)state_ptr[4*i + 3] << 24);
    }
    blake3_compress_in_place_portable(cv, block_ptr, 64, 0, 0);
    u8 *out = (u8 *)cabi_realloc((void *)0, 0, 1, 32);
    for (int i = 0; i < 8; i++) {
        out[4*i    ] = (u8)(cv[i]      );
        out[4*i + 1] = (u8)(cv[i] >>  8);
        out[4*i + 2] = (u8)(cv[i] >> 16);
        out[4*i + 3] = (u8)(cv[i] >> 24);
    }
    unsigned int *ret = (unsigned int *)cabi_realloc((void *)0, 0, 4, 8);
    ret[0] = (unsigned int)(unsigned long)out;
    ret[1] = 32u;
    return (unsigned int)(unsigned long)ret;
}

/*
 * `hash(data) -> list<u8>` — equivalent to `init; update; finalize`.
 * Emitted in C so the rebuild pipeline for C variants stays a single
 * clang invocation (no WAT-level `compose_one_shot`).
 */
__attribute__((export_name("covalence:hash/api@0.1.0#hash")))
unsigned int cov_hash(const u8 *data_ptr, u32 data_len)
{
    cov_init();
    cov_update(data_ptr, data_len);
    return cov_finalize();
}

/*
 * `keyed-hash(key, data) -> list<u8>`. `key` is 32 bytes; we reuse the
 * stateful CTX (matching the WAT variant's "one-shot resets the
 * instance" semantics). Returns a 32-byte digest in a Legacy
 * (ptr, len) return area.
 *
 * We deliberately do *not* `bump_reset` here: the host has already
 * lowered `key_ptr` and `data_ptr` into the bump region, and rewinding
 * the bump cursor before reading them risks the digest allocation
 * landing on top of the still-needed key bytes. The bump region grows
 * monotonically across one-shots; `cov_init` (= the WIT `init`
 * export) is the single owner of bump-reset.
 */
__attribute__((export_name("covalence:hash/api@0.1.0#keyed-hash")))
unsigned int cov_keyed_hash(const u8 *key_ptr, u32 key_len,
                            const u8 *data_ptr, u32 data_len)
{
    if (key_len != BLAKE3_KEY_LEN) __builtin_trap();
    blake3_hasher_init_keyed(&CTX, key_ptr);
    blake3_hasher_update(&CTX, data_ptr, (size_t)data_len);
    u8 *digest = (u8 *)cabi_realloc((void *)0, 0, 1, BLAKE3_DIGEST_BYTES);
    blake3_hasher_finalize(&CTX, digest, BLAKE3_DIGEST_BYTES);
    unsigned int *ret = (unsigned int *)cabi_realloc((void *)0, 0, 4, 8);
    ret[0] = (unsigned int)(unsigned long)digest;
    ret[1] = BLAKE3_DIGEST_BYTES;
    return (unsigned int)(unsigned long)ret;
}

/*
 * `derive-key(context, key-material) -> list<u8>`. `context` is a
 * UTF-8 string (canonical-ABI string-lift gives us ptr + length).
 * Returns a 32-byte derived key in a Legacy (ptr, len) return area.
 *
 * Same bump-cursor invariant as `cov_keyed_hash`: do not reset.
 */
__attribute__((export_name("covalence:hash/api@0.1.0#derive-key")))
unsigned int cov_derive_key(const u8 *ctx_ptr, u32 ctx_len,
                            const u8 *km_ptr, u32 km_len)
{
    blake3_hasher_init_derive_key_raw(&CTX, ctx_ptr, (size_t)ctx_len);
    blake3_hasher_update(&CTX, km_ptr, (size_t)km_len);
    u8 *digest = (u8 *)cabi_realloc((void *)0, 0, 1, BLAKE3_DIGEST_BYTES);
    blake3_hasher_finalize(&CTX, digest, BLAKE3_DIGEST_BYTES);
    unsigned int *ret = (unsigned int *)cabi_realloc((void *)0, 0, 4, 8);
    ret[0] = (unsigned int)(unsigned long)digest;
    ret[1] = BLAKE3_DIGEST_BYTES;
    return (unsigned int)(unsigned long)ret;
}

/*
 * lld emits the linear memory under the symbol name "memory" when
 * `-Wl,--export-dynamic` is in effect — exactly what the component-
 * model glue expects, so no force-export shim is needed.
 */

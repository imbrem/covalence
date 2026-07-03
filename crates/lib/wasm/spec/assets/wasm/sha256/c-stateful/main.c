/*
 * Canonical-ABI wrapper for the RFC 6234 §8.2 SHA-256 reference.
 *
 * Single-instance "stateful" world (`sha256-stateful.wit`): the module
 * instance IS the hasher object. Hasher context lives in a static
 * global; `init` resets it.
 *
 * Export-name strategy
 * --------------------
 * Each canonical-ABI export is declared with
 * `__attribute__((export_name("covalence:hash/api@0.1.0#NAME")))`,
 * so we avoid the need for any out-of-band C-name → ABI-name map
 * (the alternative would have been a `<variant>.exports.json` post-
 * processing step in `rebuild.rs`). The exported symbols match the
 * Legacy mangling that `wit-component` recognises when wrapping a core
 * module against the `covalence:hash/api` interface.
 *
 * Why `hash` lives in C rather than coming from `compose_one_shot`:
 *   the WAT-level wrapper synthesises `hash` by injecting a function
 *   that calls `$init_impl`, `$update_impl`, `$finalize_impl` — those
 *   private aliases are a WAT convention only. For C sources we emit
 *   `hash` directly, and `rebuild.rs` skips the compose step when the
 *   `hash` export is already present in the core module.
 *
 * cabi_realloc
 * ------------
 * Implemented in C as a bump allocator over `__heap_base` (provided by
 * lld at link time) with `__builtin_wasm_memory_{size,grow}` for
 * growth. No free / no resize; matches the SHA-1 handwritten WAT.
 */

#include "sha256.h"

/* ─── module-global hasher context ─────────────────────────────────── */

static sha256_ctx CTX;

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
    sha256_init(&CTX);
    /* Reset bump so streaming-then-finalize doesn't accumulate garbage
     * across hash sessions. Matches the WAT variants. */
    bump_reset();
}

__attribute__((export_name("covalence:hash/api@0.1.0#update")))
void cov_update(const u8 *data, u32 len)
{
    sha256_update(&CTX, data, len);
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
    u8 *digest = (u8 *)cabi_realloc((void *)0, 0, 1, SHA256_DIGEST_BYTES);
    sha256_finalize(&CTX, digest);
    unsigned int *ret = (unsigned int *)cabi_realloc((void *)0, 0, 4, 8);
    ret[0] = (unsigned int)(unsigned long)digest;
    ret[1] = SHA256_DIGEST_BYTES;
    return (unsigned int)(unsigned long)ret;
}

/*
 * `compress(state, block) -> list<u8>`: state_ptr/state_len,
 * block_ptr/block_len lowered straight to linear memory by the host.
 */
__attribute__((export_name("covalence:hash/api@0.1.0#compress")))
unsigned int cov_compress(const u8 *state_ptr, u32 state_len,
                          const u8 *block_ptr, u32 block_len)
{
    if (state_len != 32u || block_len != 64u) __builtin_trap();
    u8 *out = (u8 *)cabi_realloc((void *)0, 0, 1, 32);
    sha256_compress(state_ptr, block_ptr, out);
    unsigned int *ret = (unsigned int *)cabi_realloc((void *)0, 0, 4, 8);
    ret[0] = (unsigned int)(unsigned long)out;
    ret[1] = 32u;
    return (unsigned int)(unsigned long)ret;
}

/*
 * `hash(data) -> list<u8>` — emitted in C rather than via
 * `compose_one_shot` so the rebuild pipeline for C variants stays a
 * straight clang invocation. Equivalent to `init; update; finalize`.
 */
__attribute__((export_name("covalence:hash/api@0.1.0#hash")))
unsigned int cov_hash(const u8 *data_ptr, u32 data_len)
{
    cov_init();
    cov_update(data_ptr, data_len);
    return cov_finalize();
}

/*
 * lld emits the linear memory under the symbol name "memory" when
 * `-Wl,--export-dynamic` is in effect — exactly what the component-
 * model glue expects, so no force-export shim is needed.
 */

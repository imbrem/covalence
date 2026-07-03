/*
 * Canonical-ABI wrapper for the TweetNaCl Ed25519-verify reference.
 *
 * Targets `ed25519.wit` (`covalence:sign/api@0.1.0`). Exports a single
 * `verify(public-key, message, signature) -> bool` function that
 * returns `true` iff the supplied signature is a valid Ed25519
 * signature for the given message under the given public key, per
 * RFC 8032 §5.1.7.
 *
 * Strategy
 * --------
 *
 * TweetNaCl exposes `crypto_sign_open(m, mlen, sm, n, pk)` where:
 *   - `sm` is the concatenation `signature || message`
 *     (signature is 64 bytes, so `n = 64 + |message|`)
 *   - `m` is an output buffer for the recovered message; `mlen` for
 *     its length. We don't care about either — only the int return,
 *     which is `0` on success and `-1` on rejection.
 *
 * So `verify(pk, msg, sig)` performs:
 *   1. Reject `|pk| != 32` or `|sig| != 64` immediately.
 *   2. Allocate `signature || message` (64 + |msg| bytes) from the
 *      canonical-ABI bump allocator.
 *   3. Allocate a `64 + |msg|`-byte scratch buffer for the recovered
 *      message (we discard it but TweetNaCl requires it).
 *   4. Call `crypto_sign_open` and lift `(rc == 0)` to a `bool` i32.
 *
 * The bump allocator is reset on every `verify` call so the linear
 * memory cost stays bounded by the largest single message we verify.
 *
 * Export naming follows the established pattern: each canonical-ABI
 * export is decorated with `__attribute__((export_name("...")))` so
 * `wit-component` can wrap the core module against
 * `covalence:sign/api@0.1.0` without an out-of-band export map.
 */

#include "tweetnacl.h"

typedef unsigned char u8;
typedef unsigned int   u32;
typedef unsigned long long u64;

/* ─── bump allocator (cabi_realloc) ────────────────────────────────── */

/*
 * `__heap_base` is a linker-defined symbol pointing at the first byte
 * past the static data + stack area. Past that point linear memory is
 * unmanaged, free for our bump allocator to carve up. Copied verbatim
 * from `sha256/c-stateful/main.c` — same shape suits the verify path.
 */
extern unsigned char __heap_base;

static u32  BUMP        = 0; /* lazily initialised to __heap_base */
static u32  BUMP_INITED = 0;

static u32 align_up(u32 x, u32 a)
{
    u32 mask = a - 1u;
    return (x + mask) & ~mask;
}

__attribute__((export_name("cabi_realloc")))
void *cabi_realloc(void *orig_ptr, u32 orig_size,
                   u32 align, u32 new_size)
{
    (void)orig_size;
    if (orig_ptr != (void *)0) {
        __builtin_trap();
    }
    if (!BUMP_INITED) {
        BUMP        = (u32)&__heap_base;
        BUMP_INITED = 1;
    }
    if (align == 0) align = 1;
    u32 aligned = align_up(BUMP, align);
    u32 end     = aligned + new_size;

    u32 cur_bytes = (u32)__builtin_wasm_memory_size(0) << 16;
    if (end > cur_bytes) {
        u32 need_bytes = end - cur_bytes;
        u32 need_pages = (need_bytes + 0xFFFFu) >> 16;
        if (__builtin_wasm_memory_grow(0, need_pages) == (unsigned long)-1L) {
            __builtin_trap();
        }
    }
    BUMP = end;
    return (void *)(unsigned long)aligned;
}

static void bump_reset(void)
{
    BUMP        = (u32)&__heap_base;
    BUMP_INITED = 1;
}

/* ─── canonical-ABI exports ────────────────────────────────────────── */

/*
 * `verify(pk, msg, sig) -> bool` — WASM has no native bool, so the
 * canonical ABI lowers a `bool` return to an i32 (0 = false, 1 = true).
 * We hand-write that as the natural C `int` return.
 */
__attribute__((export_name("covalence:sign/api@0.1.0#verify")))
int cov_verify(const u8 *pk_ptr, u32 pk_len,
               const u8 *msg_ptr, u32 msg_len,
               const u8 *sig_ptr, u32 sig_len)
{
    if (pk_len != 32u || sig_len != 64u) {
        return 0;
    }

    /* RFC 8032 §5.1.7 says invalid encodings MUST be rejected. The
     * TweetNaCl `unpackneg` + `crypto_verify_32` path inside
     * `crypto_sign_open` is the canonical check; we just bridge the
     * call. */

    u32 sm_len = 64u + msg_len;
    u8 *sm = (u8 *)cabi_realloc((void *)0, 0, 1, sm_len);
    /* Layout: signature || message. */
    u32 i;
    for (i = 0; i < 64u; i++) sm[i] = sig_ptr[i];
    for (i = 0; i < msg_len; i++) sm[64u + i] = msg_ptr[i];

    /* Recovered-message scratch buffer. `crypto_sign_open` writes the
     * unpacked message here even though we discard it; the buffer
     * needs to be `sm_len` bytes for the worst-case write pattern. */
    u8 *recovered = (u8 *)cabi_realloc((void *)0, 0, 1, sm_len);
    u64 mlen = 0;

    int rc = crypto_sign_open(recovered, &mlen, sm, (u64)sm_len, pk_ptr);

    /* Reset the bump pointer so successive `verify` calls only ever
     * pay for the largest single verification's working set. */
    bump_reset();
    return rc == 0 ? 1 : 0;
}

/*
 * lld emits the linear memory under the symbol name "memory" when
 * `-Wl,--export-dynamic` is in effect — exactly what the component-
 * model glue expects, so no force-export shim is needed.
 */

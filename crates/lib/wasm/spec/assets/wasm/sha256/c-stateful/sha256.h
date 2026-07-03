/*
 * Minimal SHA-256 interface — single instance, no libc.
 *
 * Source: RFC 6234 §8.2 reference SHA-256 (public domain, RFC 5378).
 *         https://datatracker.ietf.org/doc/html/rfc6234#section-8.2
 *
 * Stripped to four primitives used by the `sha256-stateful` world:
 *
 *   sha256_init     — reset the context to FIPS §5.3.3 IV.
 *   sha256_update   — feed `len` bytes from `data`.
 *   sha256_finalize — finish padding (FIPS §5.1.1) and emit 32 bytes
 *                     into the caller-supplied buffer.
 *   sha256_compress — block primitive: 8 × 32-bit BE state + 64-byte
 *                     block → 8 × 32-bit BE next state (FIPS §6.2.2).
 *
 * All four match the canonical-ABI shapes wrapped by `main.c`.
 */

#ifndef COV_SHA256_H
#define COV_SHA256_H

typedef unsigned char  u8;
typedef unsigned int   u32;
typedef unsigned long long u64;

#define SHA256_BLOCK_BYTES  64
#define SHA256_DIGEST_BYTES 32
#define SHA256_STATE_WORDS  8

typedef struct {
    u32 h[SHA256_STATE_WORDS];   /* H[0..7], native-endian */
    u8  buf[SHA256_BLOCK_BYTES]; /* pending bytes */
    u32 pending;                  /* 0..63 */
    u64 total_bits;               /* total message length in bits */
} sha256_ctx;

void sha256_init(sha256_ctx *ctx);
void sha256_update(sha256_ctx *ctx, const u8 *data, u32 len);
void sha256_finalize(sha256_ctx *ctx, u8 out[SHA256_DIGEST_BYTES]);

/*
 * Single-block compression. `state` is 32 BE bytes (8 × u32 BE);
 * `block` is 64 bytes of the message block; `out_state` receives 32 BE
 * bytes. This wraps the round function so it can be exported by itself.
 */
void sha256_compress(const u8 state[32], const u8 block[64], u8 out_state[32]);

#endif

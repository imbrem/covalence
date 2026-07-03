/*
 * SHA-256 reference implementation.
 *
 * Adapted from RFC 6234 §8.2 (public domain per RFC 5378, see RFC 6234
 * "Copying conditions"):
 *
 *     https://datatracker.ietf.org/doc/html/rfc6234#section-8.2
 *
 * The structure of §8.2 (round-table K, SHA-256 IV, processing function
 * shape) is preserved for auditability. The only deltas vs the RFC text
 * are:
 *
 *   - No <string.h>: `memcpy`/`memset` replaced by hand-rolled inline
 *     loops (the WASM target is built with `-nostdlib`).
 *   - Integer typedefs come from `sha256.h` rather than `stdint.h` /
 *     `inttypes.h`.
 *   - Errors and option flags from the RFC's `USE_MODIFIED_MACROS` /
 *     `Length_High` / `Length_Low` machinery are dropped — we only need
 *     the streaming hash function and a single-block compression hook.
 *
 * Algorithmically this is bit-identical to the RFC text: same
 * initialization vector (FIPS §5.3.3), same K[0..63] (FIPS §4.2.2),
 * same Ch/Maj/Σ0/Σ1/σ0/σ1 (FIPS §4.1.2), same 64-round mixing
 * function (FIPS §6.2.2), same big-endian padding (FIPS §5.1.1).
 */

#include "sha256.h"

/* ─── §4.2.2 round constants ───────────────────────────────────────── */

static const u32 K[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u,
};

/* ─── §4.1.2 mixing functions ──────────────────────────────────────── */

static inline u32 rotr(u32 x, u32 n) { return (x >> n) | (x << (32u - n)); }
static inline u32 shr (u32 x, u32 n) { return x >> n; }

static inline u32 Ch (u32 x, u32 y, u32 z) { return (x & y) ^ (~x & z); }
static inline u32 Maj(u32 x, u32 y, u32 z) { return (x & y) ^ (x & z) ^ (y & z); }

static inline u32 BSIG0(u32 x) { return rotr(x, 2)  ^ rotr(x, 13) ^ rotr(x, 22); }
static inline u32 BSIG1(u32 x) { return rotr(x, 6)  ^ rotr(x, 11) ^ rotr(x, 25); }
static inline u32 SSIG0(u32 x) { return rotr(x, 7)  ^ rotr(x, 18) ^ shr (x, 3);  }
static inline u32 SSIG1(u32 x) { return rotr(x, 17) ^ rotr(x, 19) ^ shr (x, 10); }

/* ─── core compression (FIPS §6.2.2) ───────────────────────────────── */

static void sha256_process_block(u32 H[8], const u8 block[64])
{
    u32 W[64];
    u32 a, b, c, d, e, f, g, h;
    u32 T1, T2;
    int t;

    for (t = 0; t < 16; t++) {
        W[t] = ((u32)block[4*t]     << 24)
             | ((u32)block[4*t + 1] << 16)
             | ((u32)block[4*t + 2] <<  8)
             | ((u32)block[4*t + 3]      );
    }
    for (t = 16; t < 64; t++) {
        W[t] = SSIG1(W[t-2]) + W[t-7] + SSIG0(W[t-15]) + W[t-16];
    }

    a = H[0]; b = H[1]; c = H[2]; d = H[3];
    e = H[4]; f = H[5]; g = H[6]; h = H[7];

    for (t = 0; t < 64; t++) {
        T1 = h + BSIG1(e) + Ch(e, f, g) + K[t] + W[t];
        T2 = BSIG0(a) + Maj(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + T1;
        d = c;
        c = b;
        b = a;
        a = T1 + T2;
    }

    H[0] += a; H[1] += b; H[2] += c; H[3] += d;
    H[4] += e; H[5] += f; H[6] += g; H[7] += h;
}

/* ─── streaming API ────────────────────────────────────────────────── */

void sha256_init(sha256_ctx *ctx)
{
    /* FIPS §5.3.3 IV. */
    ctx->h[0] = 0x6a09e667u;
    ctx->h[1] = 0xbb67ae85u;
    ctx->h[2] = 0x3c6ef372u;
    ctx->h[3] = 0xa54ff53au;
    ctx->h[4] = 0x510e527fu;
    ctx->h[5] = 0x9b05688cu;
    ctx->h[6] = 0x1f83d9abu;
    ctx->h[7] = 0x5be0cd19u;
    ctx->pending    = 0;
    ctx->total_bits = 0;
}

void sha256_update(sha256_ctx *ctx, const u8 *data, u32 len)
{
    u32 i;

    ctx->total_bits += (u64)len * 8u;

    if (ctx->pending > 0) {
        u32 need = SHA256_BLOCK_BYTES - ctx->pending;
        if (len < need) {
            for (i = 0; i < len; i++) {
                ctx->buf[ctx->pending + i] = data[i];
            }
            ctx->pending += len;
            return;
        }
        for (i = 0; i < need; i++) {
            ctx->buf[ctx->pending + i] = data[i];
        }
        sha256_process_block(ctx->h, ctx->buf);
        data += need;
        len  -= need;
        ctx->pending = 0;
    }

    while (len >= SHA256_BLOCK_BYTES) {
        sha256_process_block(ctx->h, data);
        data += SHA256_BLOCK_BYTES;
        len  -= SHA256_BLOCK_BYTES;
    }

    if (len > 0) {
        for (i = 0; i < len; i++) ctx->buf[i] = data[i];
        ctx->pending = len;
    }
}

void sha256_finalize(sha256_ctx *ctx, u8 out[SHA256_DIGEST_BYTES])
{
    /* FIPS §5.1.1 padding. */
    u32 i;
    u64 bits = ctx->total_bits;

    ctx->buf[ctx->pending++] = 0x80u;

    if (ctx->pending > 56) {
        while (ctx->pending < SHA256_BLOCK_BYTES) ctx->buf[ctx->pending++] = 0;
        sha256_process_block(ctx->h, ctx->buf);
        ctx->pending = 0;
    }
    while (ctx->pending < 56) ctx->buf[ctx->pending++] = 0;

    /* 8-byte BE length tail */
    ctx->buf[56] = (u8)(bits >> 56);
    ctx->buf[57] = (u8)(bits >> 48);
    ctx->buf[58] = (u8)(bits >> 40);
    ctx->buf[59] = (u8)(bits >> 32);
    ctx->buf[60] = (u8)(bits >> 24);
    ctx->buf[61] = (u8)(bits >> 16);
    ctx->buf[62] = (u8)(bits >>  8);
    ctx->buf[63] = (u8)(bits      );

    sha256_process_block(ctx->h, ctx->buf);

    for (i = 0; i < SHA256_STATE_WORDS; i++) {
        out[4*i    ] = (u8)(ctx->h[i] >> 24);
        out[4*i + 1] = (u8)(ctx->h[i] >> 16);
        out[4*i + 2] = (u8)(ctx->h[i] >>  8);
        out[4*i + 3] = (u8)(ctx->h[i]      );
    }
}

void sha256_compress(const u8 state[32], const u8 block[64], u8 out_state[32])
{
    u32 H[8];
    u32 i;
    for (i = 0; i < 8; i++) {
        H[i] = ((u32)state[4*i    ] << 24)
             | ((u32)state[4*i + 1] << 16)
             | ((u32)state[4*i + 2] <<  8)
             | ((u32)state[4*i + 3]      );
    }
    sha256_process_block(H, block);
    for (i = 0; i < 8; i++) {
        out_state[4*i    ] = (u8)(H[i] >> 24);
        out_state[4*i + 1] = (u8)(H[i] >> 16);
        out_state[4*i + 2] = (u8)(H[i] >>  8);
        out_state[4*i + 3] = (u8)(H[i]      );
    }
}

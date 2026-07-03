/*
 * TweetNaCl — verify-only Ed25519 (RFC 8032) interface.
 *
 * Source: https://tweetnacl.cr.yp.to/20140427/tweetnacl.h (public domain).
 *
 * Stripped to the single primitive used by the `ed25519` world:
 *
 *   crypto_sign_open(m, mlen, sm, n, pk)
 *     — verify a 64-byte Ed25519 signature appended to a message
 *       (sm = signature || message, n = total length) under the given
 *       32-byte public key. Returns 0 on success, -1 on failure.
 *
 * TweetNaCl bundles its own SHA-512 (`crypto_hash`) internally; the
 * verify path needs no external hash dependency. Signing / keypair
 * primitives, `crypto_box`, `crypto_secretbox`, `crypto_stream`,
 * `crypto_onetimeauth` are intentionally NOT exposed — they would
 * pull in `randombytes`, which the wasm32-unknown-unknown freestanding
 * target cannot provide without a host import.
 */

#ifndef COV_TWEETNACL_VERIFY_H
#define COV_TWEETNACL_VERIFY_H

#define crypto_sign_ed25519_tweet_BYTES 64
#define crypto_sign_ed25519_tweet_PUBLICKEYBYTES 32

extern int crypto_sign_ed25519_tweet_open(unsigned char *,unsigned long long *,const unsigned char *,unsigned long long,const unsigned char *);

#define crypto_sign_open crypto_sign_ed25519_tweet_open
#define crypto_sign_BYTES crypto_sign_ed25519_tweet_BYTES
#define crypto_sign_PUBLICKEYBYTES crypto_sign_ed25519_tweet_PUBLICKEYBYTES

#endif

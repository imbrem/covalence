Ed25519 signature verification — TweetNaCl reference (RFC 8032 §5.1.7).

Built from the public-domain TweetNaCl 20140427 release at
<https://tweetnacl.cr.yp.to/20140427/tweetnacl.c>, slimmed to the
transitive closure of `crypto_sign_open` (the verify entry point) plus
a small canonical-ABI wrapper in `main.c`. Every primitive needed for
verification — Curve25519 field arithmetic, Edwards group ops,
L-modular reduction, the constant-time `crypto_verify_32` — is
preserved byte-for-byte from upstream. Salsa20, Poly1305, secretbox,
box, `crypto_sign` (signing), and `crypto_sign_keypair` (keygen) are
intentionally NOT exposed: signing requires `randombytes`, which is
not available on the freestanding `wasm32-unknown-unknown` target.

TweetNaCl bundles its own SHA-512 (`crypto_hash` over
`crypto_hashblocks`) inside this translation unit. For v0 we do not
yet link Ed25519 verify against our `sha512` spec via WIT
composition; that is a planned follow-up.

Spec references:

- RFC 8032 (Edwards-Curve Digital Signature Algorithm):
  <https://datatracker.ietf.org/doc/html/rfc8032>
- TweetNaCl 20140427: <https://tweetnacl.cr.yp.to/>

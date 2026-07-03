SHA-256 — C reference, single-instance ("object model") shape.

Targets `sha256-stateful.wit`. Built by `rebuild --features
rebuild-c` from `sha256.c` / `sha256.h` (RFC 6234 §8.2 reference
implementation, public domain) plus `main.c` (a small canonical-ABI
wrapper that exposes `init` / `update` / `finalize` / `compress` /
`hash` and ships a bump `cabi_realloc`).

The reference C is bit-for-bit identical to RFC 6234 §8.2
algorithmically — the only edits drop `<string.h>` dependencies (the
target is `-nostdlib`) and use C99 integer types via `sha256.h`
typedefs rather than `<stdint.h>`. The 64-round mixing function and
the K[0..63] round constants match the WAT variants of SHA-256;
streaming/finalize padding follows FIPS §5.1.1.

Canonical-ABI export names are attached at the C source level via
`__attribute__((export_name("covalence:hash/api@0.1.0#...")))` so no
out-of-band export map is needed.

Spec references:

- FIPS PUB 180-4: <https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>
- RFC 6234 §8.2: <https://datatracker.ietf.org/doc/html/rfc6234#section-8.2>

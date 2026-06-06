SHA-512 — hand-written WAT, resource shape.

Targets `sha512.wit`. Exposes a `resource hasher` with constructor,
update, and finalize. One module instance can run up to 8 concurrent
hashers from a fixed-size handle pool (slot index = rep, 256-byte
slots in linear memory; SHA-512 state is 64 B + 128 B pending buffer
+ 16 B 128-bit byte counter, all per slot). `finalize` consumes the
resource and frees its slot; resources dropped without being
finalized leak the slot until the module instance is torn down.

The 80-round mixing function over u64, FIPS §5.3.5 IVs, FIPS §4.2.3
K constants, and FIPS §5.1.2 128-bit-length padding match the spec
verbatim. See FIPS PUB 180-4:
<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>

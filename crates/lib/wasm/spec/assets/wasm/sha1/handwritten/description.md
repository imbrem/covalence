SHA-1 — hand-written WAT, resource shape.

Targets `sha1.wit`. Exposes a `resource hasher` with constructor,
update, and finalize. One module instance can run up to 8 concurrent
hashers from a fixed-size handle pool (slot index = rep, 128-byte
slots in linear memory). `finalize` consumes the resource and frees
its slot; resources dropped without being finalized leak the slot
until the module instance is torn down.

The 80-round mixing function and FIPS §5.3.1 IVs match the spec
verbatim. See FIPS PUB 180-4:
<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>

SHA-1 — hand-written WAT, single-instance ("object model") shape.

Targets `sha1-stateful.wit`. The module instance IS the hasher: state
lives in fixed memory globals (no handle table, no slot allocator).
An embedder gets N concurrent hashers by instantiating N copies of
the component. `init` resets the state to the FIPS §5.3.1 IV plus a
zero pending buffer; `update` accumulates bytes and dispatches
block-aligned chunks; `finalize` pads per FIPS §5.1.1 and emits the
20-byte digest.

The 80-round mixing function is bit-for-bit identical to the resource
variant — only the streaming wrapper differs. See FIPS PUB 180-4:
<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>

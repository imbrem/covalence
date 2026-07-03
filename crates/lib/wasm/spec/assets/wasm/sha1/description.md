# SHA-1 reference components

Two hand-written WAT implementations of SHA-1 (FIPS PUB 180-4 §6.1):

- **`handwritten`** — resource-based streaming hasher. One module
  instance can host many concurrent hashers through a small in-module
  handle pool (8 slots). The composed one-shot `hash` wrapper uses
  `[constructor]hasher → [method]hasher.update → [method]hasher.finalize`.
- **`handwritten-stateful`** — single-instance "object model". The
  module IS the hasher: state lives in fixed memory globals, no handle
  table, no slot allocator. The embedder spins up N concurrent hashers
  by instantiating N copies. The composed one-shot wrapper uses
  `init → update → finalize`.

Both pass the same KAT vectors (they compute the same mathematical
function). Block size 512 bits, output 160 bits. The 80-round mixing
function and FIPS §5.3.1 IVs are shared verbatim across variants.

See FIPS PUB 180-4 (NIST):
<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>

# SHA-256 reference components

Two hand-written WAT implementations of SHA-256 (FIPS PUB 180-4 §6.2):

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
function). Block size 512 bits, output 256 bits. The 64-round
compression with `Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁`, the 64-entry
round-constant table `K[0..64]` (from §4.2.2), and the FIPS §5.3.3
IVs are shared verbatim across variants.

See FIPS PUB 180-4 (NIST):
<https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>

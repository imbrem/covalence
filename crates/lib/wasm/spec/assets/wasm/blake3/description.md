# BLAKE3 reference components

Two hand-written WAT implementations of BLAKE3
("BLAKE3: one function, fast everywhere", 2020):

- **`handwritten`** — resource-based plain-mode streaming hasher with
  one-shot `keyed-hash` and `derive-key` exports. One module instance
  can host up to 4 concurrent plain-mode hashers through a small handle
  pool; the keyed and derive-key one-shots use a separate transient
  state slot so they don't perturb the pool.
- **`handwritten-stateful`** — single-instance "object model". The
  module IS the hasher: state lives in fixed memory globals (key,
  chunk buffer, chunk counter, CV stack, etc.). The embedder spins up
  N concurrent hashers by instantiating N copies. Plain-mode streaming
  via `init / update / finalize`; `keyed-hash` and `derive-key` are
  exposed as one-shots and reset the instance as a side effect.

Both implement the full BLAKE3 tree-mode hashing for arbitrary input
sizes: 64-byte blocks combine into 1024-byte chunks (via 16 sequential
block compressions with CHUNK_START / CHUNK_END flags); chunks combine
via PARENT compressions of equal-height subtrees off a CV stack. The
ROOT flag is added only at the final compression so that the chunk and
parent compressions producing intermediate CVs use the *same* function
but a different domain.

The G mixing function, 7 rounds, message permutation, and flag bits
are taken verbatim from spec §2.3-§2.5. Output is 32 bytes (XOF /
arbitrary-length output is not exposed in v0).

See:
<https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf>

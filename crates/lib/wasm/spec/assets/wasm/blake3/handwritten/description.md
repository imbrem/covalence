BLAKE3 — hand-written WAT, resource shape.

Targets `blake3.wit`. Exposes a plain-mode `resource hasher` with
constructor/update/finalize plus world-level `keyed-hash`, `derive-key`
and `compress` one-shots. One module instance can run up to 4
concurrent plain-mode hashers from a fixed-size handle pool; the
keyed and derive-key one-shots run on a separate transient slot and do
not consume a handle. `finalize` consumes the resource and frees its
slot; resources dropped without being finalized leak the slot until the
module instance is torn down.

The G mixing function, 7 rounds, message permutation, and tree-mode
chunk/parent flags follow spec §2.3-§2.5 verbatim. Tree-mode streaming
maintains a chunk-CV stack of up to 54 entries (enough for any input
up to 2^54 chunks ≈ 2^64 bytes); equal-height subtrees fold on each
chunk-CV push.

See "BLAKE3: one function, fast everywhere":
<https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf>

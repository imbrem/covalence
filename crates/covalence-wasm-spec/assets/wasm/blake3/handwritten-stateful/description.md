BLAKE3 — hand-written WAT, single-instance ("object model") shape.

Targets `blake3-stateful.wit`. The module instance IS the plain-mode
hasher: state lives in fixed memory globals (no handle table, no slot
allocator). An embedder gets N concurrent hashers by instantiating N
copies of the component. Plain mode runs through `init / update /
finalize`; `init` resets to the IV and zero-pending state. `keyed-hash`
and `derive-key` are exposed as one-shots and reset the instance as a
side effect.

The G mixing function, 7 rounds, message permutation, and tree-mode
streaming logic are bit-for-bit identical to the resource variant —
only the slot/handle plumbing differs. The CV stack supports up to 54
levels (any input ≤ 2^64 bytes).

See "BLAKE3: one function, fast everywhere":
<https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf>

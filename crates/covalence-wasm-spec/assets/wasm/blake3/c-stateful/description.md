BLAKE3 — official C reference, single-instance ("object model") shape.

Targets `blake3-stateful.wit`. Built by `rebuild --features rebuild-c`
from the BLAKE3 official C reference at tag 1.8.5
(<https://github.com/BLAKE3-team/BLAKE3/tree/1.8.5/c>, CC0 1.0 / Apache
2.0 dual-licensed) plus `main.c` (a small canonical-ABI wrapper that
exposes `init` / `update` / `finalize` / `compress` / `hash` /
`keyed-hash` / `derive-key` and ships a bump `cabi_realloc`).

Vendored upstream sources (portable backend only):

- `blake3.h`
- `blake3_impl.h`
- `blake3.c`
- `blake3_portable.c`
- `blake3_dispatch.c`

The four `.c` files compile pristine apart from dropping `<string.h>`
and `<assert.h>` — the freestanding wasm32-unknown-unknown target has
no libc. `cov_compat.h` declares the missing `memcpy` / `memset` /
`strlen` and an inert `assert` macro; the definitions live in
`main.c`. On wasm32 neither `IS_X86` nor `IS_AARCH64` is defined and
`BLAKE3_USE_NEON` expands to 0, so every dispatch function falls
straight through to `blake3_compress_in_place_portable` /
`blake3_compress_xof_portable` / `blake3_hash_many_portable` — the
SIMD detection and inline-asm code paths are not reachable.

The committed `c-stateful.wasm` produces bit-identical digests to the
WAT-level `handwritten-stateful` variant for every test vector
(`tests/against_rust.rs` + `tests/kat.rs`).

Canonical-ABI export names are attached at the C source level via
`__attribute__((export_name("covalence:hash/api@0.1.0#...")))` so no
out-of-band export map is needed.

`compress` is implemented as
`truncate8(compress(state, block, t=0, b=64, d=0))` via
`blake3_compress_in_place_portable(cv, block, 64, 0, 0)` — the
upstream function writes the top-8-word post-XOR result back into
`cv`, which IS the WIT-specified truncate-to-8 step. The caller's
`state` is LE-decoded into a local CV first so the input is not
mutated.

Spec references:

- BLAKE3 paper:
  <https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf>
- BLAKE3 reference C (vendored from 1.8.5):
  <https://github.com/BLAKE3-team/BLAKE3/tree/1.8.5/c>

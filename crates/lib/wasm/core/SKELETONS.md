# Skeletons — covalence-wasm

- **`cov:pure` host binding removed pending rewrite** — `src/pure.rs` (wasmtime
  Host* impls for `wit/pure.wit`) and its integration tests were deleted when
  the Pure-meta rules were collapsed into the HOL-Light rule set; must be
  re-derived against the current `covalence-core` rules. `wit/pure.wit` and the
  guest fixture `covalence-core-test-guest` (`crates/kernel/hol/test-guest`)
  remain, but nothing builds or loads the guest — no CI target covers it.

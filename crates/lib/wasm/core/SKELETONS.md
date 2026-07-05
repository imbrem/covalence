# Skeletons — covalence-wasm

- **`cov:pure` host binding removed pending rewrite** — `src/pure.rs` (wasmtime
  Host* impls for `wit/pure.wit`) and its integration tests were deleted when
  the Pure-meta rules were collapsed into the HOL-Light rule set; must be
  re-derived against the current `covalence-core` rules. `wit/pure.wit` and the
  guest fixture `covalence-core-test-guest` (`crates/kernel/hol/test-guest`)
  remain, but nothing builds or loads the guest — no CI target covers it.
  The WIT still declares `has-no-obs` funcs from the deleted observer system
  (toHOL purge S2); drop them when the host binding is re-derived.

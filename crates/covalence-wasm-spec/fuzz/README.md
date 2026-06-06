# covalence-wasm-spec fuzz targets

Differential fuzz harnesses for the reference WASM hash components,
driven by `cargo-fuzz` / libFuzzer. Each target wraps a single
algorithm × world combination and compares its output against the
reference Rust implementation in `covalence_hash`.

## Available targets

- **`sha1_resource_differential`** — hashes random inputs through the
  SHA-1 resource component (`sha1/handwritten`) and compares with
  `covalence_hash::sha1`.
- **`sha1_stateful_differential`** — same, against the stateful
  component (`sha1/handwritten-stateful`).

Inputs are biased to SHA-1 padding edges (`{0, 1, 55, 56, 63, 64, 65,
119, 120, 127, 128, 129, 192, 256}`) plus random lengths up to 4 KiB.

## Running

From the crate root (`crates/covalence-wasm-spec/`):

```sh
cargo +nightly fuzz run sha1_resource_differential -- -max_total_time=60
cargo +nightly fuzz run sha1_stateful_differential -- -max_total_time=60
```

Drop `-max_total_time=60` to fuzz indefinitely. Corpora and crash
artifacts land in `fuzz/corpus/` and `fuzz/artifacts/` (both git-ignored).

# Skeletons — `covalence-init/src` (crate-root modules)

Placeholders in crate-root `src/*.rs` (modules without their own
`SKELETONS.md`). See [`CLAUDE.md`](../../../../../CLAUDE.md) § Skeletons, the
[crate index](../SKELETONS.md), and the [root index](../../../../../SKELETONS.md).

## `sexp.rs` — term S-expression round-trip asymmetry

`term_to_sexp` serializes `nat-lit` / `int-lit` / `bool-lit` forms that
`term_from_sexp` has **no parse arms for** (one-way; `blob`/`small-int` do
round-trip). Dies with the literal `TermKind` variants (toHOL purge S10/S11) —
the serialize arms go with them; do not add parse arms meanwhile without the
maintainer's serialization sign-off (persisted-format wall).

## `project.rs` — multi-file `.cov` project loader

`Project` / `compile_project` does the `.cov`→`.cov` import graph + topological
compile (and `.cov`→Rust seam-env / FFI-tactic leaves). Design:
[`notes/vibes/web/cov-project.md`](../../../../../notes/vibes/web/cov-project.md). Open:

- **Rust↔`.cov` mutual recursion.** Cycles through the Rust↔`.cov` boundary are
  **rejected** (`ProjectError::Cycle`), not resolved; the two-phase / SCC+fixpoint
  approach (§5) is unimplemented.
- **Concurrent unit compilation.** Units compile strictly sequentially
  (`resolve_blocking` per unit) because `script::block_on` is not nestable —
  blocked on the nestable-executor work in `src/script/SKELETONS.md`.
- **Single `init/mod.rs` `Project`.** `library_env` / `library_tactic` /
  `prime_library_imports` + per-theory `cov_theory!` blocks are hand-wired;
  folding into one cached `Project` (§6) is not done.
- **WASM project units + Cargo-features distribution.** Compiling a Rust unit to
  WASM against the abstract `cov:*` API (interchangeable with `.cov` nodes) and
  the Cargo-feature → content-hash distribution mapping (§7) are design-only.

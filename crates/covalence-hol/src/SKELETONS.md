# Skeletons — `covalence-hol/src` (crate-root modules)

Intentional placeholders in the crate-root `src/*.rs` modules (those not under
a module subdirectory with its own `SKELETONS.md`). See `CLAUDE.md` § Skeletons
and the [crate index](../SKELETONS.md).

## `project.rs` — the multi-file `.cov` project loader

The dependency-resolving loader (`Project` / `compile_project`) implements the
`.cov`→`.cov` import graph + topological compile (and `.cov`→Rust seam-env /
FFI-tactic leaves). Design: [`docs/cov-project.md`](../../../docs/cov-project.md).
Deferred:

- **Rust→`.cov` *feeding* edge + full mutual recursion.** A Rust unit that is
  itself a project input feeding a later `.cov` unit (a cycle through the
  Rust↔`.cov` boundary) is not handled. Mutual reference among units is
  currently **rejected** (`ProjectError::Cycle`) rather than resolved; the
  two-phase (declare-signatures-then-check-bodies) or SCC+fixpoint approach
  (`docs/cov-project.md` §5) is unimplemented.
- **The single `init/mod.rs` `Project`.** `init::library_env` /
  `library_tactic` / `prime_library_imports` + the per-theory `cov_theory!`
  blocks are still hand-wired; folding them into one cached `Project` definition
  (`docs/cov-project.md` §6) is not done.
- **WASM-against-abstract-API project units + Cargo-features distribution.**
  Compiling a Rust unit to WASM against the abstract `cov:*` kernel/store API
  (so a Rust unit and a `.cov` unit are interchangeable graph nodes), and the
  Cargo-feature → content-hash distribution mapping (`docs/cov-project.md` §7),
  are design-only.
- **Concurrent unit compilation.** Units compile strictly sequentially (each
  `resolve_blocking`-forced before the next) because `script::block_on` is not
  nestable; concurrent compilation waits on the nestable-executor work tracked
  in `src/script/SKELETONS.md`.

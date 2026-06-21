# Skeletons — covalence-kernel

## Empty / stub modules

- **`crates/covalence-kernel/src/facts.rs`** — empty module. The *observer*
  layer that records and content-addresses proven `covalence-hol` theorems
  will land here as the HOL-on-store stack comes online. See the
  `covalence-kernel` crate-root docs and `docs/roadmap.md`.

## Partial implementations

- **`crates/covalence-kernel/src/service.rs`** — the target-agnostic check
  surface (`KernelService`). **In place:** synchronous `check` of a
  self-contained `.cov` article against the standard-library prelude →
  `CheckReport` (theorems + diagnostics), portable to `wasm32-unknown-unknown`.
  **Deferred:**
  - **Async dependency loading.** The `ArticleSource` trait + `TrustPolicy` are
    defined as seams but not yet wired through
    `covalence_hol::script::run_async`; network `#import`s (the `category.wiki`
    story) need that so a `fetch` can be `await`ed instead of dead-locking a
    blocking executor on the browser main thread.
  - **`TrustLevel::DeepCheck` is not enforced** — both trust levels currently
    behave identically (the standard library is always re-checked; there is no
    dependency-trust bypass yet).
  - **No diagnostic spans.** `Diagnostic::span` is always `None` until the
    `.cov` script layer carries source extents (see
    `crates/covalence-hol/src/script/SKELETONS.md`).
  - **Statement rendering is canonical S-expression**, not math notation; the
    notation / MathML printer is future work (see `docs/web-kernel.md`).

## Removed-pending-rewrite subsystems

- **`covalence-kernel` legacy prover** — the arena + e-graph + union-find
  prover kernel that used to live in `covalence-kernel` was removed in the
  kernel rewrite. What remains is the content-addressed store wiring
  (`backend.rs`, `store.rs`) plus the empty `facts` module above. Recover the
  old prover from the `backup/pre-hol-cleanup` branch if needed.

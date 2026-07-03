# Skeletons — covalence-kernel

See [`CLAUDE.md`](../../../CLAUDE.md) § Skeletons and the [root index](../../../SKELETONS.md).

## Empty / stub modules

- **`src/facts.rs`** — empty module. The observer layer recording and
  content-addressing proven `covalence-hol` theorems lands here as the
  HOL-on-store stack comes online (see crate-root docs, `notes/vibes/roadmap.md`).

## Removed-pending-rewrite subsystems

- **Legacy prover** — the arena + e-graph + union-find prover kernel was removed
  in the rewrite; only the content-addressed store wiring (`backend.rs`,
  `store.rs`) + the empty `facts` module remain. Recover from
  `backup/pre-hol-cleanup`.

## Partial — `src/service.rs` (`KernelService`)

Synchronous `check` of a self-contained `.cov` article is in place. Deferred:

- **Async dependency loading.** `ArticleSource` + `TrustPolicy` are defined as
  seams but not wired through `covalence_hol::script::run_async`; network
  `#import`s need it so a `fetch` can be `await`ed rather than dead-locking a
  blocking executor on the browser main thread.
- **`TrustLevel::DeepCheck` not enforced** — both levels behave identically (stdlib
  always re-checked; no dependency-trust bypass).
- **No diagnostic spans** — `Diagnostic::span` always `None` until the `.cov` script
  layer carries source extents (see `covalence-hol/src/script/SKELETONS.md`).
- **Statement rendering is canonical S-expression**, not math notation; MathML
  printer is future work (`notes/vibes/web-kernel.md`).

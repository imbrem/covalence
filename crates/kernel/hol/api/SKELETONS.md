# covalence-hol-api — skeletons

- **Consumer migration not done.** The `Hol`/`Nat` traits + the end-to-end
  demo (`tests/through_the_api.rs`) landed, but no *real* external consumer is
  migrated onto them yet: `lang/haskell`, `proof/alethe`, `proof/egglog`,
  `server/core` still build terms via `covalence_core::Term`/`TermKind`
  directly. Migration order + the swap-the-backend argument:
  `notes/vibes/backend-decoupling.md`. Inventory: `bun scripts/backend-coupling.mjs`.
- **Trait family incomplete.** Only `Hol` + `Nat` exist. Planned peers:
  `Inductives` (declare type + recursor + induction, fronting
  `covalence_inductive::InductiveBackend`), a `HolOmega`/kinds surface tying to
  `kindcheck.rs`/`tyrep.rs`, and further theory traits (`Int`/`List`/`Bool`)
  mirroring `Nat`.
- **`Hol` error type not associated.** Fixed to `covalence_core::Result`
  (inherited from the trait's origin in the inductive engine); a fully
  backend-agnostic surface makes `Error` an associated type. Deferred until a
  second backend needs a different error.

# covalence-kernel-sat — skeletons

Generic SAT-proof replay. Built so far: the [`ClauseBackend`](src/lib.rs) trait
(the resolution seam) and the [`replay_lrat`](src/lib.rs) entry point. Design:
`notes/vibes/logics/smt-import-architecture.md`. Open work, severe first:

## Severe

- **`replay_lrat` is a stub** (returns `NotImplemented`). Needs the pure,
  backend-independent RUP → resolution-chain extraction: per LRAT step, assume
  `¬C`, unit-propagate through the antecedent clauses in order recording each
  propagated literal, then read the reverse order off as a resolution chain
  deriving `C`. This mirrors `covalence-kernel-smt`'s `farkas` (cert-check as
  data, replay separate) and is the valuable pure piece to build next.
- **No `ClauseBackend` impl.** A native HOL impl (clause = right-associated `∨`,
  `resolve` via `covalence_init::init::logic::resolve` / `clause_intro`) is
  unbuilt; the crate currently has the trait but no backend, so nothing exercises
  the seam end-to-end. Adding it pulls in `covalence-core`/`-init`/`-hol-eval`.

## Minor

- **DRAT (no hints) not handled.** Only LRAT (which carries per-step antecedents)
  is a replay entry point; a bare DRAT proof must first be elaborated to LRAT
  (e.g. `drat-trim -L`) or have its propagation recomputed. No elaborator here.
- **RAT (not just RUP).** The resolution extraction covers RUP steps; RAT steps
  (resolution-asymmetric-tautology, needing the pivot's every resolvent) are not
  yet modelled.

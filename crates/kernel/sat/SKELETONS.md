# covalence-kernel-sat — skeletons

Generic SAT-proof replay. Built: the [`ClauseBackend`](src/lib.rs) trait (the
resolution seam), a native HOL backend ([`HolClauseBackend`](src/hol.rs)), and
[`replay_lrat`](src/lib.rs) driving an LRAT proof end-to-end into a kernel
`⊢ ⊥` (CaDiCaL → LRAT tested in `tests/cadical_e2e.rs`). Design:
`notes/vibes/logics/smt-import-architecture.md`. Open work, severe first:

## Minor

- **Left-fold resolution only.** `replay_lrat` folds `resolve` over each step's
  antecedents in order, relying on `logic::resolve`'s own pivot-finding (first
  complementary pair). This works for the reverse-unit-propagation chains
  CaDiCaL emits, but a chain where the naive fold picks the wrong pivot (two
  complementary pairs between successive clauses) has no fallback: the
  pivot-simulation path (unit-propagate under the falsifying assignment,
  `resolve_on` with the computed pivot) is unbuilt.
- **DRAT (no hints) not handled.** Only LRAT (which carries per-step
  antecedents) is a replay entry point; a bare DRAT proof must first be
  elaborated to LRAT (e.g. `drat-trim -L`) or have its propagation recomputed.
  No elaborator here.
- **RAT (not just RUP).** The resolution replay covers RUP steps; RAT steps
  (resolution-asymmetric-tautology, needing the pivot's every resolvent) are not
  yet modelled — `replay_lrat` treats every antecedent list as a plain
  resolution chain.

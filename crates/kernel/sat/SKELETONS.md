# covalence-kernel-sat — skeletons

Generic SAT-proof replay. Built: the [`ClauseBackend`](src/lib.rs) trait (the
resolution seam), a native HOL backend ([`HolClauseBackend`](src/hol.rs)), and
[`replay_lrat`](src/lib.rs) driving an LRAT proof end-to-end into a kernel
`⊢ ⊥` (CaDiCaL → LRAT, `tests/cadical_e2e.rs`; `examples/unsat_certify.rs`).
Design: `notes/vibes/logics/smt-import-architecture.md`. Open work, severe first:

## Severe — blocks real solver proofs at scale

- **RAT steps unhandled** (parser + replay). Real CaDiCaL proofs (pigeonhole,
  and the k-bit exhaustive family for k≥6) use **RAT** — even `--plain` does.
  `parse_lrat_text` rejects the negative antecedent hints (`ExpectedInteger
  "-46"`), and `replay_lrat` is RUP-only. RAT clause additions are only
  *satisfiability-preserving*, not entailed, so producing a genuine `{F} ⊢ ⊥`
  from a RAT step is not just a resolution chain — approach under research.
- **Replay perf blowup.** Replaying a k=6 exhaustive proof (64 clauses) took
  ~12.5 s vs 26 ms at k=5 — superlinear. `HolClauseBackend::resolve` keeps
  duplicate literals in resolvents (`logic::resolve_on` only drops the pivot), so
  clause terms grow and per-step kernel work explodes. Fix: dedup literals + a
  threaded term interner (keep the running clause as a literal-set, materialise
  the HOL term once). Must scale like the set.mm import path.

## Minor

- **Left-fold pivot-finding.** `replay_lrat` folds `resolve` over antecedents in
  order, relying on `logic::resolve`'s first-complementary-pair search. Works for
  CaDiCaL RUP chains; a chain needing an explicit pivot (unit-propagation
  simulation) has no fallback.
- **DRAT (no hints) not handled.** Only LRAT (with per-step antecedents) is a
  replay entry point; a bare DRAT proof must be elaborated to LRAT first.

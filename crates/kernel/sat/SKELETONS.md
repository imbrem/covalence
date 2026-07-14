# covalence-kernel-sat — skeletons

Generic SAT-proof replay. Built: the three-plug-point API ([`SatProblem`] →
`Term`, [`ClauseBackend`] → `Thm`, [`ReplayStrategy`]), two native HOL backends —
the disjunction [`HolClauseBackend`](src/hol.rs) and the **scale-default**
sequent-form [`SequentClauseBackend`](src/sequent.rs) (`C` as `{C, ~l₁,…,~lₙ}⊢F`;
resolution is a hyp-set cut, ~3 kernel rules/step regardless of clause size) —
and [`RupReplay`](src/lib.rs) — proper trace-based RUP reconstruction (falsify
`C`, unit-propagate the antecedents to compute each pivot, resolve backward from
the conflict; refutation detected via the LRAT clause being empty, so it is
backend-agnostic). Real CaDiCaL `--plain` proofs replay to a genuine `⊢ ⊥`
(`tests/cadical_e2e.rs` disjunction, `tests/sequent_e2e.rs` sequent + the
`bench_pigeonhole_scaling` benchmark; `examples/unsat_certify.rs`). Design:
`notes/vibes/logics/smt-import-architecture.md`. Open work, severe first:

## Severe

- **RAT steps unhandled** (parser + replay). Non-`--plain` CaDiCaL proofs, and
  other solvers, use **RAT** (extended resolution / preprocessing). `parse_lrat_text`
  rejects the negative antecedent hints; a RAT clause is only
  satisfiability-preserving, not entailed, so `⊢ ⊥` reconstruction needs the
  **extension-variable ("RAT-as-definition")** method (research-vetted: fresh
  `z:bool` + `⟺` defining hypothesis per RAT step → RUP additions → discharge the
  conservative definitions; polynomial, uses existing zero-TCB primitives). This
  is a new `ReplayStrategy`. Stopgap in place: run CaDiCaL with `--plain` for
  RUP-only proofs.

## Minor

- **Interning/hash-consing** on the sequent backend is a further constant-factor
  win (the hyp-set unions in `resolve_on` still hash terms).
- **`SequentClauseBackend::is_empty_clause` is best-effort.** A *unit* input
  clause's `C` disjunction is a bare atom `x`, structurally identical to a
  surviving `~`-literal, so the shape check can't certify an all-unit-input empty
  clause. Harmless: `RupReplay` uses the LRAT clause being empty as authoritative
  (`⊢ F` + hyps ⊆ inputs is still the checked contract). A proper fix would tag
  input-clause hyps.
- **DRAT (no hints) not handled.** Only LRAT (with per-step antecedents) is a
  replay entry point; a bare DRAT proof must be elaborated to LRAT first.

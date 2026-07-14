# covalence-kernel-sat — skeletons

Generic SAT-proof replay. Built: the three-plug-point API ([`SatProblem`] →
`Term`, [`ClauseBackend`] → `Thm`, [`ReplayStrategy`]), a native HOL backend
([`HolClauseBackend`](src/hol.rs)), and [`RupReplay`](src/lib.rs) — proper
trace-based RUP reconstruction (falsify `C`, unit-propagate the antecedents to
compute each pivot, resolve backward from the conflict). Real CaDiCaL `--plain`
proofs replay to a genuine `⊢ ⊥` (pigeonhole in `tests/cadical_e2e.rs`;
`examples/unsat_certify.rs`). Design: `notes/vibes/logics/smt-import-architecture.md`.
Open work, severe first:

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
- **Resolution is O(clause-size) per step.** `HolClauseBackend` represents a
  clause as a `∨`-term, so each `resolve_on` (`logic::resolve_on`) does
  `elim_disj` — a kernel inference per literal — and rebuilds the disjunction.
  With the dedup fix the term stays bounded, but per-step cost is still linear in
  clause size, so huge proofs (pigeonhole h≥7) are slow (~44 s at 6.6k steps).
  The scale fix is a **sequent-form clause backend**: represent `C` as
  `{¬l₁,…,¬lₙ} ⊢ ⊥`; then resolution is a hypothesis-set cut (near-O(1), sets not
  rebuilt terms) — the LCF-standard efficient SAT-replay representation, and a
  drop-in second `ClauseBackend` under the same API. (Interning/hash-consing is a
  further constant-factor win on top.)

## Minor

- **DRAT (no hints) not handled.** Only LRAT (with per-step antecedents) is a
  replay entry point; a bare DRAT proof must be elaborated to LRAT first.

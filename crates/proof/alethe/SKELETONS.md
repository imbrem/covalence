# Skeletons — covalence-alethe

See [`CLAUDE.md`](../../../CLAUDE.md) § Skeletons and the [root index](../../../SKELETONS.md).

The negate-goal → refute → conclude `⊢ G` flow is wired (`goal.rs`,
`discharge.rs`, `tactic.rs`, replayed through `hol::HolAletheBridge`; exposed as a
script `Tactic` via `(#by (smt))`). Deferred:

## Goal discharge

- **Content-addressed proof cache.** `discharge::ProofCache` is an in-memory /
  on-disk lookup keyed by the goal's printed form (no store backing, no problem
  canonicalisation). The design is a `covalence-store` cache: key = hash of the
  canonical `SmtProblem`, value = Alethe blob, written back on miss.
- **`goal_to_problem` fragment.** Renders only the QF_UF + linear-`int` shapes the
  bridge reads (bool/int literals, free vars as `declare-fun`, `tfree` sorts,
  connectives, `= + - * < <=`, unary `-`). Goals with binders, non-`int` numerics
  (`nat`, floats, `bytes`), or derived-type ops are rejected `NotImplemented`. A
  wider renderer (+ matching bridge rules) is needed.
- **`.cov` int-literal goals.** The script `infer` has no `int`-literal syntax and
  `int.*` lives outside `core`, so the script-seam test discharges a propositional
  tautology; arithmetic goals go through the direct discharge API. An `int`-literal
  surface + `int` catalogue import would let `(#by (smt))` close LIA goals in `.cov`.

## Rule coverage — `HolAletheBridge` (`src/hol.rs`)

The QF_UF core, propositional family, int term layer, and `hole`/rewrite
re-derivation are checked. The following return `NotImplemented` / `UnknownRule`:

- **`hole` beyond closed arithmetic / propositional.** A hole needing
  variable-level ring normalisation (`x+1 = 1+x`, `*` distribution) has no shared
  `reduce`+`simp` normal form. Needs proved `int` ring identities
  (`add_comm`/`assoc`/`mul_distrib`) + a linear normaliser. Likewise disequality-
  reflexivity holes over uninterpreted terms.
- **Linear-arithmetic core** — `la_generic` (Farkas), `src/la.rs`. Handles the
  unit-coefficient all-strict transitivity-cycle case for any `n ≥ 2`. Still to wire:
  - Non-unit / rational coefficients (scale each literal: `int::lt_mul_pos` to
    scale, `int::lt_add_mono`+`add_comm` to add; rational→int clearing).
  - Mixed strict (`<`) / non-strict (`≤`) literals (`int::le_def`,
    `lt_trichotomy`, `lt_of_le_of_lt`).
  - The general scale-and-sum combination for non-transitivity-cycle refutations.
  - `la_mult_pos`/`la_mult_neg`; `la_rw_eq`; `la_disequality`; `la_totality`;
    `la_tautology`.
- **Subproofs** — `anchor` and any `step` with `:discharge` (`subproof`/`bind`/
  `let`) are rejected.
- **Rest of propositional family** — `equiv_pos1`, `equiv_neg1/2`, `and_pos`/
  `and_neg`, `or`/`or_pos`/`or_neg`, `implies_pos`/`implies_neg`, `contraction`,
  `tautology`, `ite*`, and the equality lemmas (`eq_reflexive`/`eq_transitive`/
  `eq_symmetric`/`eq_congruent`). Need cases in `hol.rs::step`.
- **Parametric sorts** (`declare-sort` arity > 0) — rejected `ParametricSort`.

## North star — Alethe in PA / SOA (not built)

Discharge target is HOL today. Long-term: replay an arithmetic Alethe certificate
(LIA ⊂ PA) as a `Derivable_PA` / SOA derivation, transported via the metatheory
ladder. The bridge would dispatch its `int`/LIA core into a PA model; `goal_to_problem`
and the reductio wrapper keep their shape, only the backend logic changes.

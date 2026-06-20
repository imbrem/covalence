# Skeletons — covalence-alethe

## Goal discharge (`discharge.rs` / `goal.rs` / `tactic.rs`)

The **negate-the-goal → refute → conclude `⊢ G`** flow is wired:
[`goal::goal_to_problem`] renders `¬G` to an `SmtProblem`,
[`discharge::SmtDischarger`] obtains an Alethe refutation (cached proof, else
an injected `SmtSolver`), replays it through [`hol::HolAletheBridge`]
(surfacing the empty-clause refutation via `HolAletheBridge::refutation`), and
`discharge::reductio` concludes `⊢ G` classically (`lem` + `false_elim`).
[`tactic::smt_tactic`] exposes it as a `covalence_hol::script::Tactic` over the
public `(#register-ffi-tactic smt)` / `(#by (smt))` seam. Deferred:

- **Content-addressed proof cache.** [`discharge::ProofCache`] is the *first
  cut*: an in-memory / on-disk lookup keyed by the goal's printed form
  (`CachedProof::Text` or `::Path`). The real design is a `covalence-store`
  content-addressed cache — key = hash of the canonical `SmtProblem`, value =
  the Alethe blob — persisted and shared across a session, with the solver
  result written back on a cache miss. Not yet built; `ProofCache` has no store
  backing and no canonicalisation of the problem.
- **`goal_to_problem` fragment.** Renders only the shapes
  `HolAletheBridge` reads back (QF_UF + the linear-`int` term layer:
  `bool`/`int` literals, free vars as uninterpreted `declare-fun`s, `tfree`
  sorts, the connectives, `= + - * < <=`, unary `-`). A goal with binders
  (`∀`/`∃`/`λ`), non-`int` numeric literals (`nat`, floats, `bytes`), or
  derived-type operations is rejected `NotImplemented` — never mistranslated.
  Quantified / `nat` / mixed-theory goals need a wider renderer (and matching
  bridge rules).
- **`.cov` int-literal goals.** The script `infer` has no `int`-literal syntax
  and `int.*` lives outside `core`, so the script-seam test discharges a
  propositional tautology (`¬(a ∧ ¬a)`); the arithmetic goal is exercised
  through the direct discharge API. An `int`-literal surface + an `int` catalogue
  import would let `(#by (smt))` close LIA goals stated in `.cov` too.

## North star — Alethe in PA / SOA (not built)

Today the discharge target logic is **HOL** (`reductio` lands `⊢ G` in HOL).
Long-term an *arithmetic* Alethe certificate (LIA ⊂ PA) should be replayable as
a `Derivable_PA` / SOA derivation and transported via the metatheory ladder —
the eventual generalisation of the bridge's target (cf. another agent's
`crates/covalence-hol/src/peano/`). The bridge would dispatch its `int`/LIA
core into a PA model rather than the HOL `int` ring; `goal_to_problem` and the
reductio wrapper stay the same shape, only the backend logic changes.

## Partial subsystems

- **`covalence-alethe` rule coverage.** `HolAletheBridge` (in
  `crates/covalence-alethe/src/hol.rs`) checks the QF_UF core (`assume`,
  `resolution` / `th_resolution`, `refl`, `trans`, `symm`, `cong`,
  `equiv_pos2`, `false`), the propositional family (`equiv1`, `equiv2`,
  `implies`, `and`, `and_intro`, `not_not`, `evaluate`,
  `equiv_simplify`), the integer term layer (`Int`, literals,
  `+ - * < <= > >=`), and `hole` / rewrite re-derivation by
  `reduce`+`simp`. The following return `BridgeError::NotImplemented` (or
  `UnknownRule`) and still need wiring:
  - **`hole` beyond closed arithmetic / propositional.** The recompute
    hook (`hol.rs::hole` → `normalize`) discharges a hole whose two sides
    share a `reduce`+`simp` normal form — closed `int` arithmetic
    (`1+2=3`), literal `=`, connective identities (`¬true=false`). A hole
    needing *variable-level ring normalisation* (`x+1 = 1+x`, distributes
    `*`) has no shared normal form yet → reported. Needs proved `int`
    ring identities (`add_comm`/`assoc`/`mul_distrib`) from the Peano/int
    theory + a linear normaliser. Likewise disequality-reflexivity holes
    over uninterpreted terms.
  - **Linear-arithmetic core** — `la_generic` (the Farkas rule), in
    `crates/covalence-alethe/src/la.rs`, re-derives (never trusts) the
    refutation through the **proved** `int` ordered ring (`int::lt_trans`,
    `int::lt_irrefl`, with `int::lt_add_mono` / `int::lt_mul_pos` /
    `int::le_def` available for the generalisation). It now handles the
    **unit-coefficient, all-strict transitivity-cycle** case for **any
    `n ≥ 2`**: literals `t₁ < t₂, …, tₙ < t₁` (any rotation/order) are
    walked into a single cycle, chained via `int::lt_trans` into `x < x`,
    and contradicted by `int::lt_irrefl`. Non-unit `:args` coefficients,
    open (non-closing) chains, and non-`lt` literals are all rejected
    `NotImplemented` rather than fabricated. Still to wire:
    - **Non-unit / rational coefficients**: scale each literal by its
      coefficient before summing — `int::lt_mul_pos` to scale a strict
      inequality by a positive constant, `int::lt_add_mono` (+ `add_comm`)
      to add inequalities; plus a rational→int clearing step for
      fractional coefficients.
    - **Mixed strict (`<`) / non-strict (`≤`)** literals and `le`/`lt`
      mixing (needs `int::le_def` + `lt_trichotomy`, and `lt_of_le_of_lt`).
    - The genuine general *scale-each-literal-by-its-coefficient-and-sum*
      combination for refutations that do **not** reduce to a transitivity
      cycle.
    - `la_mult_pos`/`la_mult_neg` — multiply a (dis)equality/inequality by
      a sign-definite constant (`int::lt_mul_pos` covers the positive
      strict case directly).
    - `la_rw_eq` (`(a = b) ↔ (a ≤ b ∧ b ≤ a)`; have `int::le_def`),
      `la_disequality` (`a ≠ b → a < b ∨ b < a`; from `int::lt_trichotomy`),
      `la_totality` (`a ≤ b ∨ b ≤ a`; from `lt_trichotomy` + `le_def`),
      `la_tautology` (closed LIA tautology clauses).
  - **Subproofs** — `anchor` and any `step` carrying `:discharge`
    (`subproof`, `bind`, `let`, …). The bridge rejects `:discharge`.
  - **The rest of the propositional rule family** — `equiv_pos1`,
    `equiv_neg1`/`equiv_neg2`, `and_pos`/`and_neg`, `or`/`or_pos`/`or_neg`,
    `implies_pos`/`implies_neg`, `contraction`, `tautology`, `ite*`, plus
    the equality lemmas `eq_reflexive`/`eq_transitive`/`eq_symmetric`/
    `eq_congruent`. Each is a `clause_intro` of an intuitionistic sequent,
    a `simp`/`tauto`, or a direct equality derivation — the
    `init/logic.rs` machinery is in place; they just need cases in
    `hol.rs::step` (cf. the `equiv1`/`implies`/`and` cases already there).
  - **Parametric sorts** (`declare-sort` arity > 0) — rejected with
    `ParametricSort`.

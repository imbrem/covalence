# Skeletons — covalence-alethe

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
  - **Linear-arithmetic core** — `la_generic` (the Farkas rule) is
    **prototyped** in `crates/covalence-alethe/src/la.rs`: it re-derives
    (never trusts) the refutation through the **proved** `int` ordered ring
    (`int::lt_trans`, `int::lt_irrefl`, with `int::lt_add_mono` /
    `int::lt_mul_pos` available for the generalisation). The prototype
    handles only the **two-literal, coefficient-`(1,1)`, strict** case —
    `P < Q ∧ Q < P ⟹ ⊥` (the canonical `x<0 ∧ 0<x` shape) — and reports
    `NotImplemented` for everything else. Still to wire:
    - **General `la_generic`**: `n > 2` literals; non-unit / rational
      coefficients; mixed strict (`<`) and non-strict (`≤`) literals; the
      genuine *scale-each-literal-by-its-coefficient-and-sum* combination
      (needs `int::lt_add_mono`/`le_add_mono` to add inequalities and
      `int::lt_mul_pos` to scale a strict inequality by a positive
      constant — both proved in `init::int`; plus a rational→int clearing
      step for fractional coefficients, and `le`/`lt` mixing lemmas like
      `lt_of_le_of_lt`).
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

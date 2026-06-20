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
  - **Linear-arithmetic core** — `la_generic`, `la_mult_pos`/`la_mult_neg`,
    `la_rw_eq`, `la_disequality`, `la_tautology`, `la_totality`. The LIA
    proper: Farkas certificates over rational coefficients. Blocked on the
    **ordered-ring theory of `int`** (`le`/`lt` transitivity, add-
    monotonicity, sign rules) that the `high-hol` Peano build-up is
    producing. This is the major remaining undertaking.
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

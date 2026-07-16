# covalence-kernel-smt — skeletons

Generic SMT-proof replay. Built so far: the pure Farkas certificate checker
(`rational`/`lincomb`/`farkas`) and the [`RulePolicy`](src/policy.rs) subset
knob. Design: `notes/vibes/logics/smt-import-architecture.md`. Open work,
severe first:

## Severe — the replay is only partly wired

- **General scale-and-sum Farkas replay.** `replay::refute_cycle` handles the
  **unit-coefficient cycle** case with `<`/`≤` mixing (via the `Int` derived
  order lemmas). The general certificate (non-unit rational coefficients,
  non-cyclic combinations) — which `farkas::check` already *validates* — still
  needs the `0 ⋈ p` scale/sum construction and, critically, a **linear ring
  normaliser** (`⊢ Σ cᵢ·pᵢ = D`) to prove the summed polynomial equals its
  constant. `init/int.rs` has the multiplicative `prove_imul_eq` but no additive
  analogue; `lt_add_lt` (two-sided strict mono) + `add_pos` are proved and cover
  the summation, so only the normaliser is missing. See
  `notes/vibes/logics/smt-import-architecture.md`.
- **`Int`-generic term → `NormLit` parser.** No module yet reads a backend
  `H::Term` (via the `covalence_hol_api::Int` destructors) into a
  `farkas::NormLit` — i.e. steps 1–3 of the Alethe `la_generic` procedure
  (negate / strip `not` / orient to `>`/`≥`/`≈` / collect the linear
  combination). Atoms must intern to a `usize` (Term is `PartialEq` but not
  `Ord`, so `LinComb<Term>` is out). The cycle replay currently takes
  pre-built `Edge`s; the parser + a cycle detector over `farkas::check` output
  close the loop from raw Alethe.
- **Alethe step dispatcher.** No generic driver mapping `AletheCommand`s to
  backend calls filtered by `RulePolicy`. The working HOL bridge still lives in
  `crates/proof/alethe`; migrating it here (over `Int`/clause traits) is the
  point of this crate.

## Minor — Farkas checker gaps

- **GCD strengthening.** `farkas::strengthen` does the simple per-spec tightening
  (`> d` integer → `≥ d+1`); Carcara's stronger `d ↦ ⌊d⌋ + gcd(coeffs)` variant
  (sometimes needed for cvc5 `la_generic`) is not applied. `LinComb::integer_coeff_gcd`
  is in place for it.
- **`la_*` family beyond `la_generic`.** `la_mult_pos`/`la_mult_neg`,
  `la_disequality` (all emitted by cvc5 1.3.x), and the veriT-only
  `la_totality`/`la_tautology`/`la_rw_eq` have no checker.
- **i128 coefficient ceiling.** `Rational` is `i128`-based; astronomically large
  coefficients surface as `FarkasError::Overflow` rather than promoting to bignum.

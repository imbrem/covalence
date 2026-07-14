# covalence-kernel-smt — skeletons

Generic SMT-proof replay. Built so far: the pure Farkas certificate checker
(`rational`/`lincomb`/`farkas`) and the [`RulePolicy`](src/policy.rs) subset
knob. Design: `notes/vibes/logics/smt-import-architecture.md`. Open work,
severe first:

## Severe — the replay is not wired yet

- **`Int`-generic term → `NormLit` parser.** No module yet reads a backend
  `H::Term` (via the `covalence_hol_api::Int` destructors) into a
  `farkas::NormLit` — i.e. no steps 1–3 of the Alethe `la_generic` procedure
  (negate / strip `not` / orient to `>`/`≥`/`≈` / collect the linear
  combination). Atoms must intern to a `usize` (Term is `PartialEq` but not
  `Ord`, so `LinComb<Term>` is out).
- **Kernel replay (valid cert → `⊢ ⊥`).** The `farkas::check` result is verified
  data only; nothing drives the ordered-ring proof primitives to *build* the
  refutation. Needs a `LinArith`-style backend exposing: normalise a literal to
  `0 ⋈ p`, scale by a nonneg constant, add two inequalities, integer-strengthen
  (`lt_succ`), and refute a closed `0 ⋈ D`. Several rely on **int lemmas that
  don't exist yet** — no `le_add_mono`, no two-sided additive mono, no nonneg
  scaling, no additive ring normaliser (see `init/int.rs` gaps in
  `notes/vibes/logics/smt-import-architecture.md`). Prove those in `init/int.rs`
  first (cargo-test-gated).
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

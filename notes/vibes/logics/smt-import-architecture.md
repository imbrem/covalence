# SMT / SAT proof import — architecture

*Status 2026-07-14: keystone built (Int trait + pure Farkas checker + subset
policy + crate scaffolding). Replay + proof/alethe migration are the next
stages. Branch `smt-uflia-api`.*

Goal: arbitrary **Alethe** (cvc5 / veriT) proof import for **QF-UFLIA**, growing
toward general cvc5 problems seen in program verification — and retargetable so
the *same* import can land in native HOL today and in an internal Peano
arithmetic or second-order arithmetic backend later. Everything is untrusted
replay: only the kernel's own rules mint theorems, so the whole stack adds zero
TCB.

## The layering

```
crates/lib/sat      covalence-sat        DIMACS/DRAT/LRAT formats + verdict checkers   (portable, wasm)
crates/lib/smt      covalence-smt        Alethe format: parse, SmtProblem, Cvc5Solver  (portable)
                      │
crates/kernel/hol/api  covalence-hol-api  Int + (future) LinArith traits = the ABSTRACTED INTEGER API
crates/kernel/sat   covalence-kernel-sat ClauseBackend seam + LRAT→resolution replay   (untrusted)
crates/kernel/smt   covalence-kernel-smt Farkas cert checker + RulePolicy + replay     (untrusted)
                      │
crates/proof/alethe covalence-alethe     wires the Alethe format to the generic driver + goal discharge/tactic
```

`crates/kernel/{sat,smt}` sit under `kernel/` but are **not** TCB — same as
`covalence-init`. They only drive the trusted kernel API.

## Two axes of genericity (the user's requirements)

1. **Target logic / integer representation.** The arithmetic replay is written
   against the `covalence_hol_api::Int` trait, never a concrete kernel. Native
   HOL `int`, a `succ`/double-and-add numeral encoding, and an *object-level*
   `int` reflected inside internal PA / SOA are all just different `Int` impls.
   Reading and writing integer terms goes through the trait's builders +
   destructors + named ordered-ring lemma accessors, so the Farkas engine
   carries across every representation unchanged.
2. **Rule subset.** `RulePolicy` (kernel/smt) classifies Alethe rules into
   families (Resolution / Propositional / Equality / LinearArith / Rewrite /
   Subproof) and admits only a chosen subset — `qf_uf()`, `qf_uflia()`, `all()`,
   plus per-name allow/deny. A backend that can't model subproofs, or a caller
   who wants to bound what it replays, gets a clean structured refusal instead of
   a deep failure. This is the ratchet for growing coverage one family at a time.

## The key insight: check ≠ re-derive

`la_generic` is a full **scale-and-sum Farkas certificate**. *Checking* that the
certificate is arithmetically valid is pure rational linear algebra — completely
backend-independent. Only *re-deriving* `⊢ ⊥` from it needs the arithmetic
backend. So the two are separate modules:

- **`farkas` (built, pure, tested).** Implements the Alethe spec's checking
  procedure over `LinComb<Atom>` + `Rational`: step 4 integer strengthening
  (`> d` int → `≥ d+1`), step 5 scaling by `|aⱼ|` (or `aⱼ` for equalities), then
  the sum-to-contradiction test (residual LHS = 0, and `0 ⋈ D` manifestly
  false). The two worked spec examples (`0 > 0` cycle; `0 ≥ 1/4` strengthening)
  are unit tests. Steps 1–3 (negate / strip / orient each literal into `s ⋈ d`)
  are the frontend's job — they read concrete term syntax.
- **`replay` (next).** Turns a valid `FarkasCert` into `⊢ ⊥` by driving
  ordered-ring proof primitives.

cvc5 1.3.x emits `la_generic` + `la_mult_pos`/`la_mult_neg` + `la_disequality`
for QF-UFLIA (integer bound tightening `INT_TIGHT_UB/LB` is itself expressed as a
`la_generic` with args `(1,1)`). It does *not* emit `la_totality`/`la_tautology`/
`la_rw_eq` (those are veriT). `lia_generic` is a hole even in Carcara.

## What the replay needs from `init/int.rs` — and what's missing

The refutation construction (in `0 ⋈ p` normal form): scale each asserted literal
by its nonneg coefficient, integer-strengthen strict rows, sum them, and refute
the resulting `0 ⋈ D` (D a positive literal, decided by the eval TCB). Present in
`init/int.rs`: full ring, `lt_irrefl/trans/trichotomy`, `le_def`, `lt_add_mono`,
`lt_mul_pos`, and `lt_succ` (= the integer-strengthening fact `a<b ⟺ a+1≤b`).
**Missing (must prove first, cargo-test-gated):**

- `le_add_mono` (`a ≤ b ⟹ a+c ≤ b+c`) — only the strict version + cancel-iffs exist.
- two-sided additive mono (`a ⋈₁ b ∧ c ⋈₂ d ⟹ a+c ⋈₃ b+d`) — only `add_pos`
  (the `0`-based strict instance) exists; the general row-sum must chain it.
- nonneg scaling (`0 ≤ c ⟹ a ≤ b ⟹ a·c ≤ b·c`) — only strict `lt_mul_pos`;
  case-split on `le_def` for the non-strict/zero-coefficient case.
- an additive ring normaliser (`⊢ Σ cᵢ·pᵢ = D`) — `int` has the multiplicative
  `prove_imul_eq` but no additive analogue (`nat::prove_add_eq` is the pattern).
- public negation/order lemmas (`lt_neg_swap`, `a < b ⟺ -b < -a`) — currently private.

These derive from what's there; they're just unbuilt. `lt_imp_le` also needs
lifting from `le_def` (rat has it, int doesn't).

## Status ledger

- **Built + tested:** `covalence_hol_api::Int` (native impl over `init::int`);
  `kernel-smt` `rational` + `lincomb` + `farkas` (the pure checker) + `RulePolicy`;
  `kernel-sat` `ClauseBackend` trait + `replay_lrat` entry point.
- **Next:** the missing `int` lemmas → the `LinArith` proof primitives → the
  `Int`-generic parser (steps 1–3) → the kernel replay → the Alethe dispatcher →
  migrate `crates/proof/alethe` onto it (preserving its current coverage and the
  `(#by (smt))` tactic) → LRAT RUP→resolution in `kernel-sat`.
- **Deferred:** GCD strengthening; `la_mult_*`/`la_disequality`; subproofs
  (`anchor`/`bind`/`let`); the internal-PA / SOA backends (each a new `Int` impl);
  rational-coefficient Farkas run in `rat` vs. denominator-cleared in `int`.

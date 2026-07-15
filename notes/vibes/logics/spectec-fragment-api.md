# The high-level SpecTec-fragment API (layered, reusable, trait-based)

Status: first slice landed on branch `wasm-semantics`. Companion to
[cfg-stratum-design.md](./cfg-stratum-design.md) (grammars) and
[wasm-spec.md](./wasm-spec.md) (the SpecTec front end). Fulfils the maintainer
directive: *reusable high-level APIs over the core of covalence, for universally
useful SpecTec fragments like grammars* — layered so low-level rewrites leave
high-level callers alone.

## The layering

```
SpecTec-shaped top   Fragment trait + RelationEnv / GrammarEnv     (crates/kernel/hol/init/src/spectec, grammar/cfg)
      │  delegates strictly downward, ZERO Thm-minting of its own
mid   wasm::relation {rule_set, spec_rule_set, derive, derivable}   (unary  Derivable_R)
      grammar::cfg   GrammarEnv → binary::{derivable2, derive_mixed} (binary Derives_E)
      │
generic  metalogic::{RuleSet, binary::RuleSet2, apply::apply_rule, derive_via_closed}
      │
bottom   covalence-core / covalence-hol-eval  (HOL-ω kernel — re-checks everything)
```

A **fragment** is *a lowered SpecTec definition you build kernel-checked
derivations in*. The unifying trait:

```rust
pub trait Fragment {
    fn judgement_kind(&self) -> &'static str;     // "Derivable_R" | "Derives_E"
    fn n_clauses(&self) -> usize;                 // rules / productions
    fn derive(&self, clause_idx: usize, args: &[Term], premises: Vec<FragPremise>) -> Result<Thm>;
}
pub enum FragPremise { Derivation(Thm), Side(Thm) }  // unifies relation Vec<Thm> + grammar Premise
```

- `RelationEnv` (relations → `Derivable_R ⌜J⌝`, unary engine) is the peer of the
  existing `GrammarEnv` (grammars → `Derives_E n w`, binary engine). Both `impl
  Fragment`, so grammars and operational-semantics relations drive through one
  surface. Re-exported from `covalence-hol-api` (one crate for consumers).
- `RelationEnv` bundles what `wasm::relation`'s free functions leave to the
  caller: the clause count, each rule's metavar order (`RuleMeta`, via
  `encode::collect_metavars`), and the tag+encode of a judgement — so callers
  pass **SpecTec expressions** (`derive_exprs`) and rule **names**
  (`rule_index`), not pre-encoded `Φ=nat` terms.

**Delegation invariant:** every method body is a one-liner to an existing free
function. The trait layer adds no kernel rules. Re-pointing `wasm::relation::derive`
at `metalogic::apply::apply_rule`, or swapping the `Φ=nat` encoding, is invisible
to `Fragment` callers — the layering goal.

## Basic WASM semantics (the acceptance demo)

Derived kernel-checked, hypothesis-free, through `RelationEnv`
(`spectec/relation.rs` tests):

- **Value typing** — `Num_ok`: `⊢ S ⊢ CONST(I32, 0) : I32` (cross-checked vs
  `env.derivable("Num_ok", ⌜J⌝)`).
- **Reduction** — `Steps/refl`: `⊢ Z; [NOP] ↪* Z; [NOP]` (the reflexive closure
  of single-step reduction — a genuine, if trivial, operational-semantics step).
- Whole-spec `RelationEnv::spec(wasm_spec())` lowers 200+ rules with a report.

## Why this shape / K reuse

Mirrors how the K frontend wraps the *same* relation engine (`covalence-init::k`
→ `Derivable_KStep`). `RelationEnv` is the SpecTec-side, GrammarEnv-altitude
version; K's `prove_step`/`KStepThm` is the free-function+result-struct altitude.
Both sit on `wasm::relation`/`metalogic` — so the mid-level is genuinely shared,
and a K or WASM low-level rewrite doesn't disturb the other's high-level API.

## Next (roadmap)

1. **Richer premises** — the single-step `Step` relation and most reduction rules
   carry `if`/`let` side conditions (221 rules) and iterated `…*` premises (63).
   Side conditions need the denotational `wasm::denote` leg (decidable predicate
   → `bool`); iteration needs list recursion. This is the gate to real reduction
   *traces* (multi-step `↪*` via `Steps/trans` composing single steps).
2. **LEB128 value-decode** (`leb128_decode : list u8 → nat` + round-trip) — still
   the orthogonal atoms.md deliverable, on `nat_binary`/`nat_bits_iso`.
3. **`Typ`/`Dec` fragments** — wrap `wasm::syntax` (datatypes) and functions as
   `Fragment` impls; then a `SpecTecSpec` that indexes all fragments of a spec.
4. **Value-coupled parsing** (grammar side) — `ListN` vectors / `Bmodule` need a
   value-producing parser above the recognizer (see cfg-stratum-design §M6 residuals).

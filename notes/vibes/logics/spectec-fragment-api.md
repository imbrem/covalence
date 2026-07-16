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

## Basic WASM semantics (the acceptance demos)

Derived kernel-checked, hypothesis-free, through `RelationEnv`
(`spectec/relation.rs` tests):

- **Actual instruction reduction** — `Step_pure` (the pure single-step relation
  `instr* ↪ instr*`): `⊢ [NOP] ↪ []`, `⊢ [UNREACHABLE] ↪ [TRAP]`,
  `⊢ [v, DROP] ↪ []`. The premise-free rules of `Step_pure` are genuine one-step
  *executions*, reached through the combined spec env (which keeps the
  premise-free rules and skips the side-condition ones). This is real WASM
  operational semantics, not just reflexivity.
- **Compositional validity typing** — `Valtype_ok/num` premised on `Numtype_ok`,
  over the combined spec env: `⊢ C ⊢ (num I32) : ok` built by discharging the
  `⊢ C ⊢ I32 : ok` inductive premise (cross-checked against the independently
  built `Derivable_Valtype_ok` judgement). Real cross-relation premise
  composition.
- **Value typing / reduction closure** — `Num_ok`: `⊢ S ⊢ CONST(I32, 0) : I32`;
  `Steps/refl`: `⊢ Z; [NOP] ↪* Z; [NOP]`.
- Whole-spec `RelationEnv::spec(wasm_spec())` lowers 200+ rules with a report.

Every `RelationEnv::derive_exprs(clause_idx, args, premises)` call takes
**SpecTec expressions** (encoded internally) and rules addressed **by name**
(`rule_index`) — the ergonomic win over calling `wasm::relation::derive` raw.

## Why this shape / K reuse

Mirrors how the K frontend wraps the *same* relation engine (`covalence-init::k`
→ `Derivable_KStep`). `RelationEnv` is the SpecTec-side, GrammarEnv-altitude
version; K's `prove_step`/`KStepThm` is the free-function+result-struct altitude.
Both sit on `wasm::relation`/`metalogic` — so the mid-level is genuinely shared,
and a K or WASM low-level rewrite doesn't disturb the other's high-level API.

## Side conditions (the mirror-principle unlock — analysis + first piece)

Real *parameterized* reduction (`select`, `br_if`, `i32.add` const-fold) is gated
by `if`/`let` side-condition premises. The hard part is the **representation
bridge**: the judgement encoding ([`wasm::encode`]) is *uninterpreted* (`Φ=nat`
free algebra, metavars `st$v$c`, substitution = `all_elim`, and a numeric literal
`Num n` is the **opaque** constant `st$c$num.nat.N`, NOT a real nat), while a
condition (`c ≠ 0`, `c = c₁+c₂`) needs *real* arithmetic from the denotational leg
([`wasm::denote`], computable via `reduce()`).

**Faithful vs. gate.** Simply *dropping* the condition from the clause and gating
at derive-time makes `Derivable_R` **over-approximate** (a skeptic could derive
the rule when the condition is false) — unfaithful. The sound design keeps the
condition as a real *denoted* antecedent in the clause (mangled `st$v$` metavar
names, so it shares the `∀` with the judgement), instantiates condition-metavars
with **real nats** (valid in both the opaque judgement spine and the computable
condition), and discharges via `prove_true`.

**Landed (`spectec::side_cond`):** the sound reusable core —
`prove_side_condition(cond, binds) → ⊢ cond` for value-fragment conditions
(`Bool`/`Num`/`Var`/`Cmp`/`Bin`/`Un`): substitute concrete bindings, denote the
closed condition, discharge by kernel computation. It *gates* (proves `n=0` for
`n:=0`, **refuses** `n:=5` — cannot fabricate), matching the front end's
faithfulness contract. Tested on `=`/`<`/`≤` + arithmetic; non-value-fragment
(`Uncase`/`Proj`/`Call`) rejected up front.

**What's still needed to unlock a *whole* real rule** (findings from the probe):
- No value-fragment-condition rule lowers on `if`-support *alone* — **every** one
  (`Step_read/*-zero`'s `n=0`, `Limits_ok`'s `n≤k`, …) *also* carries an `Iter`
  (`…*`) or `Let` premise. So the full unlock needs `if` + `let` + iterated
  premises together (Let = a value-fragment binding `e₁=e₂`; iteration needs list
  recursion), plus wiring the discharge into `lower_rule`/`clause_of`/`derive`
  (condition as denoted antecedent + `derive` discharging it with the
  `side_cond` Thm).
- The flagship branch rules (`select`/`if`/`br_if`, condition
  `Proj(Uncase c) ≠ 0`) additionally need the **datatype leg** (`Uncase`/`Proj`
  denote support) — gated on `wasm::syntax` variants + a `Dec`/metafunction leg.
- A `bool.not F → T` fold unblocks the `Ne` (`≠`) family for `side_cond`.

## Next (roadmap)

1. **Richer premises** — wire `side_cond` into the engine: `if` as a denoted
   clause antecedent discharged in `derive`, `let` bindings, and iterated `…*`
   premises (list recursion). That unlocks the first whole conditional rule
   (`Step_read/*-zero` or `Limits_ok`) and, with `Steps/trans`, real multi-step
   reduction *traces*.
2. **LEB128 value-decode** — LANDED (`crate::init::leb128`): `leb128_decode :
   list nat → nat` = `foldr (λb acc. (b mod 128) + 128·acc) 0`, with
   `prove_decode(bytes) → ⊢ leb128_decode ⌜bytes⌝ = value` computed via the
   `list_recursion` fold clauses + nat arithmetic (0/127/128/624485/0xFFFFFFFF
   tested, hypothesis-free). Residuals: a `u8 → nat` computable cast (bytes are
   `nat` for now), a round-trip vs a `leb128_encode`, and rehoming into the
   planned `covalence-numerals` crate. Orthogonal to the recognition-side LEB128.
3. **`Typ`/`Dec` fragments** — wrap `wasm::syntax` (datatypes) and functions as
   `Fragment` impls; then a `SpecTecSpec` that indexes all fragments of a spec.
4. **Value-coupled parsing** (grammar side) — `ListN` vectors / `Bmodule` need a
   value-producing parser above the recognizer (see cfg-stratum-design §M6 residuals).

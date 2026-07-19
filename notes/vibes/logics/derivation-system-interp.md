+++
id = "N002A"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T22:10:01+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# The derivation-system interpretation API — a layered trait tower bottoming at HOL-ω

*AI-authored design corpus.* This note records the **layered-API + reification
slice** landed on branch `mm-metatheory`: the `MmAlgebra`/`MmRecursor` reification
traits (`crates/kernel/hol/init/src/metalogic/mm_algebra.rs`) and the
`DerivationSystem`/`DerivationInterp` mid-level API (`.../metalogic/interp.rs`),
plus the K matching-logic → Metamath cross-system instance they are designed to
carry (deferred).

## Why a trait tower

Goal (B): layer the APIs so **intense low-level rewrites leave high-level APIs
untouched**. The precedent is the existing three-rung inductive stack —
`covalence-hol-eval::derived::DerivedRules` → `init::inductive::hol::Hol` →
`init::inductive::data::Inductive<H: Hol>` — where the engine (`graph`/`existence`/
`recursor`) is generic over `I: Inductive` and swapping the backend leaves it
unchanged. This tower replicates that dependency-inversion one level up, for
*derivation systems* (Metamath, K, wasm, cfg, lisp) rather than *inductive types*.

Each layer's PROVIDED methods delegate only to the REQUIRED methods of the layer
directly below, bottoming at HOL-ω kernel rules.

```
L0  HOL-ω KERNEL (TCB, unchanged)   covalence_core::{Term,Type,Thm}
                                     + covalence_hol_eval::{EvalThm, DerivedRules}
                                     + init::ext::{TermExt,ThmExt}
L1  INDUCTIVE REALIZATION           covalence_inductive::InductiveBackend
                                     (ImpredicativeBackend::realize) + InductiveFacts
                                     {rec_app, comp, induct, mem_ctor, distinct, …}
L2  RULE-INDUCTION ENGINE           metalogic::{RuleSet, derivable, rule_induction,
                                     conj, nth_conjunct, …}  (free fns)
L3  REIFIED TERM ALGEBRA  ★NEW★     metalogic::mm_algebra::{MmAlgebra, MmRecursor}
                                     — the insulation boundary; two impls
                                     (FreeAlgebra, MmExprAlgebra)
L4  TRANSPORT / INTERP              metalogic::transport_db::transport
                                     (+ relations::transport on Φ⟨bool⟩)
L5  DERIVATION-SYSTEM FRONTEND ★NEW★ metalogic::interp::{DerivationSystem,
                                     DerivationInterp} — the reusable K-target API
L6  CROSS-SYSTEM RESULTS            a DerivationInterp whose Src/Tgt are two
                                     different L5 systems (K→Metamath) — no new trait
```

## L3 — `MmAlgebra` / `MmRecursor` (the insulation boundary)

The single genuinely-new trait carrying the low-level swap. `MmAlgebra` abstracts
"a reified Metamath-expression algebra over an opaque HOL carrier Φ":
`phi`/`sym`/`app`/`encode` build the encoding; `structural_sigma(leaf_map)` builds
a structural translation; `sigma_app_hom(σ)` witnesses its per-node homomorphism;
`caps().structural` flags whether the impl is genuine. **Object-safe** (returns bare
core `Term`/`Thm`; Φ is a runtime value not an associated type — so `&dyn
MmAlgebra` works, needed by `DerivationSystem::algebra`). The recursor surface
(`rec_app`/`comp`/`induct`/`mem`/`mem_ctor`) is on the separate `MmRecursor:
MmAlgebra` companion because only the inductive backend can honestly implement it.

Two impls of the core trait — the acid-test's whole point:
- `FreeAlgebra(&Database)` — recursor-free `Φ=nat`; `structural_sigma` opaque,
  `sigma_app_hom = Err`, `caps().structural = false`.
- `MmExprAlgebra` — inductive `MmExpr := sym(nat) | app(Rec,Rec)` (church-realized);
  `structural_sigma` a catamorphism, `sigma_app_hom` proved from `comp`,
  `caps().structural = true`.

See `structural-sigma-transport.md` §"TIER 2a" for the reification detail (and the
rank-1 fold-to-observation-instance subtlety).

## L5 — `DerivationSystem` / `DerivationInterp` (the reusable K-target API)

`transport_db`'s free-function interface lifted to two traits, so each system
presents a uniform frontend and an interpretation between two systems is "just
another impl".

```rust
pub trait DerivationSystem {
    fn rule_set(&self) -> RuleSet<'static>;   // its Derivable_L RuleSet (L2)
    fn algebra(&self) -> &dyn MmAlgebra;       // its reified-term encoding (L3)
    fn derivable(&self, a: &Term) -> Result<Term> {   // PROVIDED — delegates to L2
        derivable(&self.rule_set(), a)
    }
}

pub trait DerivationInterp {
    type Src: DerivationSystem;  type Tgt: DerivationSystem;
    fn src(&self) -> &Self::Src;  fn tgt(&self) -> &Self::Tgt;
    fn sigma(&self) -> Result<Term>;             // σ : Φ_src → Φ_tgt (via L3)
    fn clause_sims(&self) -> Result<Vec<Thm>>;   // one simulation per source rule
    fn interpret(&self) -> Result<Thm> {          // PROVIDED — never overridden
        transport_db::transport(&self.src().rule_set(), &self.tgt().rule_set(),
                                &self.sigma()?, self.clause_sims()?)
    }   // ⊢ ∀A. Derivable_Src A ⟹ Derivable_Tgt (σ A)
}
```

**Non-vacuity, landed:** the σ=id conservative-extension result already proved in
`transport_db::tests` re-instantiates through `interpret()` verbatim — routed
through the now-public `transport_db::id_clause_sims(src_db, tgt_db)` (promoted from
a test helper to a reusable module-level function this session). No new proof; a
real working impl proving the L5 layering delegates correctly to L4. The Metamath
`DerivationSystem` shim's `derivable(a)` is shown to equal `derivable(&rule_set,
a)`.

## L6 — the K matching-logic → Metamath instance (designed, deferred)

The user's K target: converting MATCHING-LOGIC proofs (`covalence_k::fragment`
matching-logic IR from `definition.kore`) → METAMATH is a cross-system
interpretation = the `transport_db` interface generalized:

- `Src` = the K system: `k::reduce`'s `Derivable_KStep` over KORE rewrite rules
  (`covalence_k::fragment::rewrite_rules` lowered to a `RuleSet` of LHS⇒RHS
  clauses) — a genuinely non-Metamath rewrite system, already a `RuleSet` on `Φ=nat`.
- `Tgt` = a Metamath `MmSession`'s db `RuleSet`.
- `sigma()` = the syntax morphism (matching-logic pattern → Metamath wff encoding:
  `k$app`→Metamath `concat`, each `k$c$sym`→its Metamath encoding — a former
  renaming, built as an `MmAlgebra::structural_sigma` catamorphism once the `MmExpr`
  carrier migration lands).
- `clause_sims()` = per-K-rewrite-rule "σ simulates this rewrite as a Metamath `|-`
  derivation" (each via `MmSession::apply` / `derive_axiom_instance`).
- `interpret()` transports EVERY K reduction into a Metamath derivation in one
  `rule_induction` move.

**What blocks the concrete instance** (all deferred, none on the additive path):
1. an **honest structural σ** — needs the `MmExpr` recursor AND an endomorphism
   `Φ → Φ` (TIER 2a's σ is `Φ_dom → Φ_obs`, not yet an endomorphism);
2. the **carrier migration** — K's `Φ=nat` free algebra vs the Church `MmExpr`
   carrier (`transport_db`'s `check_same_carrier`);
3. the per-KORE-rule `clause_sims` — real Metamath simulation proofs.

The traits are designed so that instance is "just another impl", no engine change.
`structural-sigma-transport.md` TIER 3 identifies K→Metamath as the first concrete
cross-system target (both already `RuleSet`s on `Φ=nat`), with Dedukti/LF the
universal σ-target for Lean/Coq reached by the identical move.

## Soundness

No TCB edit, no axiom/postulate/`unsafe`. Every `Thm` is built from existing kernel
/ eval helpers (`comp`, `beta_conv`, `beta_nf`, `trans`, `sym`, `all_intro`,
`imp_intro`, `imp_elim`, `rewrite`, `mem_ctor`, `distinct`) and every new theorem is
asserted hypothesis-free in tests. The `MmAlgebra` opacity contract mirrors
`InductiveTheory`'s (`ty` opaque; everything flows through `mem`/`ctors`/`facts`):
L4+ never touch `concat`/`app_ctor` directly, so swapping the carrier changes only
which impl runs.

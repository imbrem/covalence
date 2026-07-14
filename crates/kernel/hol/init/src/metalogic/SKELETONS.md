# Skeletons — `covalence-init/src/metalogic`

Open work in the **metalogic** layer: the generic `Derivable_L` engine, databases
as HOL values, and Metamath import/replay + composition. See `CLAUDE.md` §
Skeletons, the [crate index](../../SKELETONS.md), and the
[root index](../../../../../../SKELETONS.md).
Design: `notes/vibes/theories-models-and-logics.md` §5.5/§5.6.

## Severe

- **Structural `σ` for transport — MM-import `Φ=nat` carrier still open (TIER 2).**
  `transport` is demonstrated at **non-identity structural `σ`** on the
  reified-prop `Φ⟨bool⟩` carrier: `relations_sigma` builds (TIER 0) the
  variable-index renaming `σ_f` and (TIER 1, done) the propositional-SUBSTITUTION
  catamorphism `σ_g := λA. λ v ¬ ∧ ∨ ⟹. A (λn. (g n) v ¬ ∧ ∨ ⟹) ¬ ∧ ∨ ⟹` —
  atom↦arbitrary-formula, the FOL/HOL signature-morphism shape in miniature.
  `var_subst_sigma` / `sigma_hom_of_var_subst` prove its `⟹`-homomorphism and
  `transport_at_var_subst` discharges `transport()`'s `σ_hom` at it, for both
  `g := λn. var(succ n) ∧ var n` (structure-DEEPENING) and `g := λn. ¬(var n)`.
  Non-vacuity is structural, not a leaf index: `σ_g⌜var 0⌝ = ⌜var(succ 0) ∧ var 0⌝`
  has an `and` ROOT former, so `σ_g` lives strictly outside the whole
  depth-preserving renaming family (`sigma_subst_moves_and_deepens` asserts
  `≠ ⌜var 0⌝` AND `≠ σ_succ⌜var 0⌝`). What remains: (a) TIER 2 — a **cross-rule-set
  non-identity `σ`** on `transport_db` over the **MM-import** `Φ=nat` carrier
  (`mm_database`/K/wasm), needing the encoding reified as an inductive `MmExpr`
  (`sym(nat) | app(Rec,Rec)`) with a catamorphic recursor (church.rs backend); an
  OPAQUE whole-judgement `σ` (prefix-tag/retag/inject) could land on `Φ=nat` now
  without `MmExpr` and is the right next slice; (b) TIER 3 — a genuine CROSS-SYSTEM
  `σ` (K→Metamath first; Dedukti/LF as universal target for Lean/Coq). Design:
  `notes/vibes/logics/structural-sigma-transport.md`.
- **HOL→ZFC-scale transport** (`Derivable_HOL ⟹ Derivable_ZFC ∘ σ`) — the
  north-star instance; needs structural-`σ` above + concrete HOL/ZFC rule sets.
  Not built.
- **`∃P. ValidProof(P,S,db) ⟺ Derivable_DB db S` grounding bridge.** `Derivable_DB`
  rests on the impredicative engine, not on a HOL reification of the
  [`metamath`](../../../../../proof/metamath/) verifier. Reifying that decidable checker as a HOL
  function and proving the equivalence is unbuilt. Upgrades the *grounding* only.

## Minor

- **Lift scoped `L' ⊆ L` to full `L`.** `derive_theorem` yields `Derivable_L'`;
  `transport_db` monotonicity can lift it to `Derivable_L` but is not auto-applied.
  (`MmSession::apply`/`theorem` already share the *full-db* `L`, so composites
  built with the session need no lifting; this is only for the scoped fast path.)
- **Typecodes & `$d` over-approximated** (sound for construct direction): clauses
  quantify each metavar over all of `Φ`, not the typecode sub-language; `$d`
  disjointness unenforced. `MmSession::apply` inherits this — it does NOT check
  `$d` or the float-witness typecode; a `$d`-violating composite is a genuine HOL
  theorem but not a valid Metamath proof. Per-step replay re-checks each instance,
  so replayed witnesses stay genuine. Sound-by-design for the existence direction.
- **Per-logic denotation** for `project`ing a finished `Derivable_L` to a concrete
  fact — not built.
- **Declarations-only load + prove-on-demand.** Parse keeping only declarations
  (`$a`/`$p`/frames/`$d`), skip proof bodies, decode one proof lazily on
  `derive_theorem`. Needs a proof-skipping parse mode in `covalence-metamath`.
- **Structured-former encoding** (shorter HOL repr): give each syntactic former a
  transparent `define`d HOL constant of its arity, so `⌜S⌝` is a tree of named
  constants (`wi(ph,ps)`) and the theorem's only free vars are real metavars.
  Replay keeps formers folded → still `all_elim`. Design: `metalogic` SKELETONS
  history / §5.6.
- **set.mm/ZFC stdlib program** (design): use set.mm as ZFC stdlib from the
  frontend (namespacing, tactics) with set.mm FFI kept as the mirror-principle
  check; two-phase definitions-first import; import instrumentation
  (inference/memory counters); definition/dependency-graph explorer.

## North stars (design only — do NOT build)

- **`S`-transport** `Derivable_L1(A) ⟹ Derivable_L2(S(A))` (§5.6) — `⟹_σ`
  transport generalized across logics.
- **Conservative extension / equivalence `A ≅ B`** — mutual interpretation; the
  **category of databases** (objects = databases, morphisms = `⟹_σ`, `⊑` the
  sub-order; monotonicity/transport as functoriality) as a `crate::algebra::category`
  instance.
- **`Metamath-L ≅ native-L`** (§5.6). The **composition** side is now built:
  `MmSession` (`apply_rule`) applies an imported database's rules directly over the
  `Φ=nat` `RuleSet` — no HOL `Database` *value* needed for that. What remains is a
  *representation-equivalence metatheorem* (relate the `RuleSet`-derivability of an
  imported db to the `Derivable_DB` of a first-class HOL `Database` value à la
  `database.rs`), which needs the `∃ValidProof ⟺ impredicative` bridge. This is a
  theorem-stating goal only — the composition API does not depend on it.
- **Full `#logic` directive wiring** into the `.cov`/surface compiler (§5.6).

## Notes

- No `unsafe` (project rule). Every relation/composition theorem is kernel-proved
  and genuine; tests assert hypothesis-freeness. No postulates. `apply_rule`,
  `MmSession`, and the `Derivable_DB`/replay paths all build only from existing
  kernel rules + engine helpers (`derive_via_closed`, `nth_conjunct`, `all_elim`,
  `imp_elim`, `and_intro`).
- The env-gated `#[ignore]`s in `mm_import.rs`/`mm_database.rs` (`scan_failures`,
  `import_set_mm_sample`, `replay_set_mm_bj1`, `bench_derive_theorem`,
  `measure_dedup`) are intentional set.mm (~48 MB, not vendored) / benchmark
  harnesses, not deferred work.

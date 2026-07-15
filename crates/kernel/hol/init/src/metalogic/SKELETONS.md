# Skeletons — `covalence-init/src/metalogic`

Open work in the **metalogic** layer: the generic `Derivable_L` engine, databases
as HOL values, and Metamath import/replay + composition. See `CLAUDE.md` §
Skeletons, the [crate index](../../SKELETONS.md), and the
[root index](../../../../../../SKELETONS.md).
Design: `notes/vibes/logics/theories-models-and-logics.md` §5.5/§5.6.

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
  depth-preserving renaming family.

  **TIER 2a landed (`mm_algebra.rs`):** the MM-import encoding is now REIFIED as a
  genuine inductive `MmExpr := sym(nat) | app(Rec,Rec)` via `ImpredicativeBackend`
  (the `MmAlgebra`/`MmRecursor` trait tower rung + two impls `FreeAlgebra` /
  `MmExprAlgebra`). A structural leaf-renaming `σ` is built by catamorphism
  (`structural_sigma` = `rec_app([λc. sym(succ c), app])`) and its app-homomorphism
  `⊢ ∀X Y. σ(app X Y) = app(σX)(σY)` is proved DIRECTLY from the `comp` law
  (unconditional, hypothesis-free). The insulation acid-test runs one high-level op
  UNCHANGED on both backends.

  **What TIER 2a does NOT close (still open):**
  1. **σ is `Φ_dom → Φ_obs`, not an endomorphism `Φ → Φ`.** The catamorphism folds
     the carrier at `'r := Φ_obs` down to `Φ_obs = MmExpr⟨nat⟩` (a fixed
     observation instance); an endomorphism `C → C` is not rank-1 expressible.
     `transport_db::transport` wants `σ : Φ → Φ` on ONE carrier, so the structural
     `MmExpr` σ does not yet plug in.
  2. **Carrier migration.** The live `mm_database`/K encoders produce `Φ=nat`
     free-algebra terms; `MmExpr` is the Church carrier. Firing `transport_db`
     across two REAL rule sets with an `MmExpr` σ needs `replay_db` re-encoded onto
     `MmExpr` (`MmExprAlgebra::encode` exists as a host-side re-lift, but the import
     hot path is untouched) — `check_same_carrier` rejects `nat` vs `MmExpr`.
  3. **`Wf`-preservation-by-induction** (`⊢ ∀t. Wf t ⟹ Wf(σ t)`) is NOT proved:
     `induct`/`mem_ctor` are over the polymorphic carrier while σ is `Φ_dom →
     Φ_obs`, so `λt. Wf(σ t)` does not typecheck against the induction carrier
     without an observation-instance `induct` the church backend does not expose.
     Deferred (the app-hom, needing only `comp`, lands).
- **L5 `DerivationInterp` — K matching-logic → Metamath instance not built
  (`interp.rs`).** The `DerivationSystem`/`DerivationInterp` traits + a Metamath
  `DerivationSystem` shim landed; `interpret()` delegates to
  `transport_db::transport` (the σ=id monotonicity result re-instantiates through
  it, via the now-public `transport_db::id_clause_sims`). A concrete K→Metamath
  `DerivationInterp` needs an honest structural σ (the endomorphism blocker above),
  per-KORE-rule `clause_sims` (real Metamath simulation proofs), and the carrier
  migration. Deferred. Design: `notes/vibes/logics/derivation-system-interp.md`.

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
  `MmSession`, the `Derivable_DB`/replay paths, AND the `mm_algebra`
  (`MmExprAlgebra`) reification (`sym`/`app`/σ/app-hom) all build only from existing
  kernel rules + engine helpers (`derive_via_closed`, `nth_conjunct`, `all_elim`,
  `imp_elim`, `and_intro`, `comp`, `rec_app`, `beta_nf`, `trans`, `all_intro`). The
  `mm_algebra`/`interp` trait tower is additive — no edit to `mm_database`/K/wasm or
  the import hot path.
- The env-gated `#[ignore]`s in `mm_import.rs`/`mm_database.rs` (`scan_failures`,
  `import_set_mm_sample`, `replay_set_mm_bj1`, `bench_derive_theorem`,
  `measure_dedup`) are intentional set.mm (~48 MB, not vendored) / benchmark
  harnesses, not deferred work.

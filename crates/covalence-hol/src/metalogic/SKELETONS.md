# Skeletons — `covalence-hol/src/metalogic`

Intentional placeholders in the **metalogic** layer: the generic `Derivable_L`
engine ([`mod.rs`](./mod.rs), [`toy.rs`](./toy.rs)) **and** databases as
first-class HOL data ([`database.rs`](./database.rs)) with the relations between
them ([`relations.rs`](./relations.rs)). See `CLAUDE.md` § Skeletons and the
[crate index](../../SKELETONS.md). Design: `docs/theories-models-and-logics.md`
§5.5/§5.6.

## Status (what is done, proven)

**The generic engine (`mod.rs`/`toy.rs`):**

- `mod.rs` — `RuleSet` (carrier `phi` + a clause builder), `Derivable_L A :=
  ∀d. Closed_L d ⟹ d A` (`derivable`/`closed_conj`), `nth_conjunct`, the shared
  derivation-constructor spine (`derive_via_closed`), the generic **rule
  induction** (`rule_induction`), and **one-step projection** (`project` /
  `project_normalized`). **Done, proven.**
- `toy.rs` — a from-scratch second instance (`tt` + a `box` necessitation rule)
  exercising every entry point end-to-end. **Done, proven.**
- [`peano::pa`](../peano/pa.rs) wired in as an instance (`pa_rule_set`), pinned
  byte-identical by `derivable_via_engine_matches`. [`init::prop`](../init/prop.rs)
  left additive/alongside (foundational, 1344 lines) — `toy` covers the
  second-instance requirement without touching it.

**Databases as HOL values + relations (`database.rs`/`relations.rs`):**

- **`Database := Φ⟨bool⟩ → bool`** — a database is the HOL predicate selecting
  its axioms over the reified-formula carrier `Φ` (from `init::prop`). Genuine
  syntactic data; **HOL quantifies over databases**.
- **`Derivable_DB db A := ∀d. Closed_DB db d ⟹ d A`** — the same impredicative
  derivability, with the axiom clause `∀ax. db ax ⟹ d ax` reading axioms off the
  **HOL database value** `db` (MP is the fixed structural frame). Derivability is
  a function of the database value. **Done.**
- **Extension `A ⊑ B := ∀ax. A ax ⟹ B ax`** + **monotonicity**
  `⊢ A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S` (`database::monotone`) — honest,
  hyp-free, oracle-free; demonstrated transporting `Derivable_DB {p0} p0` across
  `{p0} ⊑ {p0,p1}`. **Done, proven.**
- **Interpretation `A ⟹_σ B` + transport** (`relations.rs`):
  `Interp A B σ := ∀ax. A ax ⟹ Derivable_DB B (σ ax)` and
  `⊢ σ_hom σ ⟹ Interp A B σ ⟹ Derivable_DB A S ⟹ Derivable_DB B (σ S)`
  (`relations::transport`), by rule induction over `relations::derivable_db_mp`,
  with `σ_hom σ := ∀X Y. σ⌜X⟹Y⌝ = ⌜σX⟹σY⌝`. Demonstrated at the identity
  translation (monotonicity as interpretation under `id`). **Done, proven.**

## Reconciliation — the two `Derivable` notions (do unify)

There are now **two** impredicative derivability constructs here: the engine's
`Derivable_L`, parameterized by a Rust `RuleSet` *closure* (prop/PA/toy), and
`database::Derivable_DB`, parameterized by a HOL `Database` *value* (the relation
lattice — built directly on the `init::prop` pattern because `database.rs`
branched before the engine existed). Same idea, different parameterization level.
**The unification: drive the engine off a HOL `Database` value** (a `RuleSet`
whose axiom clause reads a HOL predicate), collapsing the two — at which point
`monotone`/`transport` become theorems about the *engine's* `Derivable_L`.
Tracked here; not yet done.

## Deferred

### The `∃P. ValidProof(P, S, db) ⟺ Derivable_DB db S` grounding bridge

`Derivable_DB` is grounded on the impredicative engine, **not** on a HOL
reification of the [`metamath`](../metamath/) verifier. The §5.6 *primitive* is
`Derivable_A(S) := ∃P. ValidProof(P, S, A)` over the decidable checker; reifying
that checker as a HOL function and proving it equivalent to `Derivable_DB` is the
bridge — **not built**. The database is already the HOL value the relations range
over (the essential requirement), so this upgrades the *grounding*, not the
relation theorems.

### The Metamath-`Database` → `Derivable_L` connection (the engine stretch)

Deriving a `Derivable_L` from a [`metamath::Database`](../metamath/)'s axioms +
rule schemas (the `#logic`-semantics seed). Pieces: (1) an encoding of Metamath
`SExpr` into a HOL carrier `Φ`; (2) a `RuleSet` builder turning each assertion
into a `Closed_L` clause (metavariable substitution = the kernel's `inst`, `$d` →
freshness); (3) a per-logic denotation (only to *project*). Demonstrate on the
prop-calc example database. **Not built.**

### A non-trivial structural `σ` for transport

Transport is proven for any `⟹`-homomorphic `σ` (`σ_hom` hypothesis), demonstrated
at the identity. A genuinely *structural* `σ` (e.g. a variable-renaming `Φ`-fold
with `σ_hom` discharged from the fold's `⟹`-case) is the next step. **Not built.**

## North stars (design only — do NOT build)

- **`S`-transport** `Derivable_L1(A) ⟹ Derivable_L2(S(A))` (§5.6 (2)) — the
  `⟹_σ` transport generalized across logics.
- **Conservative extension** — `A ⊑ B` + reflection `Derivable_DB B S ⟹
  Derivable_DB A S` for `S` in `A`'s language (a language predicate on `Φ` + a
  proof/model argument).
- **Equivalence `A ≅ B`** — mutual interpretation; **the category of databases**
  (objects = databases, morphisms = `⟹_σ`, `⊑` the inclusion sub-order;
  monotonicity/transport as functoriality) — a `crate::category` instance.
- **`Metamath-L ≅ native-L`** (e.g. `Metamath-PA ≅ our-PA`, §5.6 (3)) — lift the
  concrete `metamath::Database` / `peano::mm_pa` into a `Database` HOL value; needs
  the `∃ValidProof ⟺ impredicative` bridge + a representation-equivalence
  metatheorem (`metamath`'s `SKELETONS.md` north star).
- **Full `#logic` directive wiring** into the `.cov`/surface compiler (§5.6 (4)).

## Notes

- No `unsafe` (project rule).
- Every relation theorem is **genuine** — kernel-proved, with the inline tests
  asserting hypothesis-freeness and oracle-freeness (`has_no_obs`). No postulates.

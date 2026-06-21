# Skeletons — `covalence-hol/src/metalogic`

Intentional placeholders in the **metalogic** layer: databases as first-class
HOL data ([`database.rs`](./database.rs)) and the relations between them. See
`CLAUDE.md` § Skeletons and the [crate index](../SKELETONS.md). The design and
the spec live in [`mod.rs`](./mod.rs) and
`docs/theories-models-and-logics.md` §5.6.

## Status (what is done, proven)

- **`Database := Φ⟨bool⟩ → bool`** — a database is the HOL predicate selecting
  its axioms over the reified-formula carrier `Φ` from [`crate::init::prop`].
  Genuine syntactic data; HOL quantifies over databases.
- **`Derivable_DB db A := ∀d. Closed_DB db d ⟹ d A`** — the impredicative
  Church derivability of [`crate::init::prop`] / [`crate::peano::pa`], with the
  axiom clause `∀ax. db ax ⟹ d ax` reading the axioms off the **HOL database
  value** `db` (modus ponens is the fixed structural frame). So derivability is
  a function of the database value. **Done.**
- **Extension `A ⊑ B := ∀ax. A ax ⟹ B ax`** + **monotonicity**
  `⊢ A ⊑ B ⟹ Derivable_DB A S ⟹ Derivable_DB B S` — an honest, hypothesis-free,
  oracle-free HOL theorem (`database::monotone`), demonstrated transporting a
  concrete fact (`Derivable_DB {p0} p0`) across a concrete one-axiom extension
  `{p0} ⊑ {p0, p1}` to `Derivable_DB {p0, p1} p0`. **Done, proven.**

- **Interpretation `A ⟹_σ B` + transport** (`relations.rs`). The translation
  `σ : Φ → Φ`, the relation `Interp A B σ := ∀ax. A ax ⟹ Derivable_DB B (σ ax)`,
  and the **transport** theorem
  `⊢ σ_hom σ ⟹ Interp A B σ ⟹ Derivable_DB A S ⟹ Derivable_DB B (σ S)` — a
  genuine HOL theorem proved by rule induction over the reusable
  `relations::derivable_db_mp` MP-closure of `Derivable_DB`, with the
  `⟹`-homomorphism `σ_hom σ := ∀X Y. σ⌜X⟹Y⌝ = ⌜σX⟹σY⌝` carried as an explicit
  hypothesis. Demonstrated on the **identity translation** (σ_hom proved by β;
  the identity-renaming instance of transport — monotonicity as interpretation
  under `id`). **Done, proven.**

## Deferred work

- **The `∃P. ValidProof(P, S, db) ⟺ Derivable_DB db S` bridge.** `Derivable_DB`
  is grounded on the impredicative engine (the same one
  [`crate::init::prop`] / [`crate::peano::pa`] already prove sound), **not** on
  a HOL reification of the [`crate::metamath`] verifier. The §5.6 ideal is
  `Derivable_L S := ∃P. ValidProof(P, S, db)` over the decidable Metamath
  checker; reifying that checker as a HOL function and proving it equivalent to
  the impredicative `Derivable_DB` is the bridge, **not built**. The database is
  already a HOL value the relations range over (the essential requirement), so
  this is an upgrade of the *grounding*, not of the relation theorems.

- **A non-trivial structural `σ` for transport.** Transport is proven for any
  `⟹`-homomorphic `σ` (`σ_hom` as a hypothesis) and demonstrated at the
  identity. A genuinely *structural* translation — e.g. a variable-renaming
  homomorphism `σ` induced by `ρ : nat → nat` folded over the encoding, with
  `σ_hom` discharged from the fold's `⟹`-case rather than by β — is the next
  step. Needs `σ` built as a `Φ`-fold and a structural `σ_hom` proof. **Not
  built.**

## North stars (design only — do NOT build)

- **Conservative extension** — `A ⊑ B` together with the *reflection*
  `Derivable_DB B S ⟹ Derivable_DB A S` for `S` in `A`'s language (the converse
  of monotonicity, restricted to the sub-language). Needs a language predicate
  on `Φ` and a proof-theoretic / model-theoretic argument; out of scope here.
- **Equivalence `A ≅ B`** — mutual interpretation (`A ⟹_σ B` and `B ⟹_τ A` with
  `σ`/`τ` mutually inverse up to derivability). Builds on the `⟹_σ` stretch.
- **The category of databases** — objects = databases, morphisms =
  interpretations `⟹_σ`, with `⊑` the inclusion sub-(pre)order; identity and
  composition of `σ`'s, and monotonicity/transport as functoriality. A
  `crate::category` instance once `⟹_σ` lands.
- **Connecting to `crate::metamath::Database` / `crate::peano::mm_pa`** — lift
  the concrete Metamath PA database (and the native `peano::pa` engine) into a
  `Database` HOL value and prove `Metamath-PA ≅ our-PA`. Requires the
  `∃ValidProof ⟺ impredicative` bridge above plus a representation-equivalence
  metatheorem (`crate::metamath`'s `SKELETONS.md` north star).

## Notes

- No `unsafe` (project rule).
- The relation theorems are **genuine** kernel-proved HOL theorems: every step
  goes through `covalence-core`'s rules and the inline tests assert
  hypothesis-freeness and oracle-freeness (`has_no_obs`). No postulates.

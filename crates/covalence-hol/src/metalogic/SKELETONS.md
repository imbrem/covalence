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

## mm_replay — Metamath proof → `⊢ Derivable_Prop ⌜S⌝` (construct, don't trust)

[`mm_replay.rs`](./mm_replay.rs) replays a **verified, untrusted** Metamath proof
into a kernel-constructed `⊢ Derivable_Prop ⌜S⌝` — the "construct, don't trust"
bridge that lands in *pure derivability over the encoded syntax* (NO denotation
`⟦S⟧`, NO observer, NO oracle). The Metamath verifier's say-so is not trusted; the
kernel re-checks each step (syntax former → `init::prop::p_imp`; `ax-1`/`ax-2` →
`init::prop::derive_axiom`; `ax-mp` → `derive_mp` + `imp_elim`; `$e` →
`Thm::assume(Derivable_Prop ⌜hyp⌝)`).

- **The propositional-calculus fragment is DONE.** `replay_prop` handles the
  set.mm `ax-1`/`ax-2`/`ax-mp` database: `wi` former, both axiom schemas (matching
  set.mm exactly), modus ponens, and essential hypotheses (which surface as the
  theorem's `Derivable_Prop ⌜hyp⌝` hypotheses). Tested end-to-end on `ax2i` (a
  single `ax-2` instance, hypothesis-free) and `a1i` (a derived rule carrying one
  essential), each genuine and oracle-free.

- **The HOL-backed `DatabaseSink` is DONE (prop fragment).** [`mm_sink.rs`](./mm_sink.rs)'s
  `HolPropSink` implements `covalence_metamath::DatabaseSink`: it forwards
  structural building to an inner `Database` and, for each `$p`, replays via
  `replay_prop` — **constructing `⊢ Derivable_Prop ⌜S⌝` as the `.mm` is read**
  (`read_prop(source)`). The reader drives the builder trait; this is the HOL
  backend (vs the in-memory checker). Generalising it to an arbitrary database
  needs the schema-database replay below.

### Deferred — the general schema-database replay (north star)

Generalise from the fixed prop-calc rule set to an **arbitrary `metamath::Database`**:
one *substitution-instance* `Closed_L` clause per assertion (each Metamath assertion
= a schematic rule; metavariable substitution = the kernel's `inst`, `$d` →
freshness), i.e. a **`RuleSet`-from-`Database`** builder, landing the
*database-relative* `Derivable_DB ⌜db⌝ ⌜S⌝`. This unifies `mm_replay` with the
existing [`database.rs`](./database.rs) `Derivable_DB` over HOL database *values*
and is the same work flagged in this file's "The Metamath-`Database` → `Derivable_L`
connection" deferral. **Not built.**

## Reconciliation — the two `Derivable` notions (DONE, Phase A)

There were **two** impredicative derivability constructs: the engine's
`Derivable_L`, parameterized by a Rust `RuleSet` *closure* (prop/PA/toy), and
`database::Derivable_DB`, parameterized by a HOL `Database` *value*. **Unified**:
`database::db_rule_set(db)` packages the database value as a `RuleSet` (the fixed
modus-ponens frame + the axiom clause reading `db`), and `database::derivable_db`
is now literally `metalogic::derivable(&db_rule_set(db), ·)` — one derivability
notion. Pinned byte-identical to the former inline form by
`derivable_db_matches_inline_definition`; `monotone`/`transport` are therefore
theorems about the *engine's* `derivable`. (The `Closed_DB` frame is still the
fixed *MP-only* rule frame; generalising the engine's clauses to one
*substitution-instance clause per Metamath assertion* — so a general database's
non-MP rules are modelled — is the `RuleSet`-from-`Database` work below.)

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

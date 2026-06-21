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

### mm_database — the general schema-database replay (DONE: normal AND compressed proofs)

[`mm_database.rs`](./mm_database.rs) generalises `mm_replay` from the fixed
prop-calc rule set to an **arbitrary `metamath::Database`**: a data-driven
`metalogic::RuleSet` is built from the database's `|-` assertions (one
substitution-instance `Closed_L` clause each — premises and conclusion encoded,
metavariables ∀-bound outermost-first), and `replay_db(db, assertion)` walks a
*verified, untrusted* proof — **normal OR compressed** — re-deriving
`⊢ Derivable_L ⌜S⌝` =
`metalogic::derivable(&rule_set(db), enc(S))` step by step through the kernel
(syntactic formers → `Slot::Wff`; `|-` axioms/rules → the `nth_conjunct` +
`all_elim` + `imp_elim` derivation constructor `mirror`-of-`init::prop::derive_mp`;
`$e` → `Thm::assume`). **One function replays many logics** — tested genuine
(`has_no_obs`) and hyp-correct on three unrelated databases: PROP (`ax2i`, `a1i`),
demo0 (`th1 |- t = t`), GROUP (`th |- ( ( a o b ) = ( a o b ) )`). "A Metamath
database IS a logic." **Done.**

- **Compressed proofs — DONE.** `replay_db` drives off the uniform
  `crate::metamath::proof_steps(db, assertion)` step sequence (decoding *both*
  encodings) and runs a `heap: Vec<Slot>` alongside the `stack`: a `Save` (`Z`)
  step clones the top stack `Slot` onto the heap; a `Heap(i)` step re-pushes
  `heap[i]`. Because `Slot` (and its `Term`/`Thm`) are cheap `Arc`-clones, a
  re-used sub-proof is a **re-push, not a recomputation** — the compressed
  proof's *sharing* is preserved (no exponential re-expansion). This is what lets
  real `hol.mm` (all 151 proofs compressed) and `set.mm` flow into the kernel.
  Per-label logic is factored into `apply_label`, shared by the step loop.

- **The encoding** is an *uninterpreted free term algebra* over `Φ = nat`: a
  binary `mm$concat`, one `mm$c$<tok>` constant per Metamath constant symbol, and
  each metavariable a plain free var. Substitution = `all_elim` because these are
  all uninterpreted free vars/variables: `enc(schema)[v := enc(arg)]` is
  *syntactically* `enc(schema[v := arg])` (no β/δ/normalisation). The fold is
  **former-structured** (a `Parser` built from the database's syntactic formers
  parses both literal and substituted expressions into the *same* compact tree)
  so `concat`-associativity never desyncs a literal axiom conclusion from the same
  expression reached by substituting a former-built argument into a schema.

- **Remaining / over-approximated** (sound for the existence/construct direction):
  - **Typecodes & `$d`** — clauses quantify each metavar over *all* of `Φ` rather
    than the typecode's sub-language, and `$d` disjointness is not enforced. A
    larger rule set only proves *more*; the per-step replay re-checks each
    instance, so the constructed witness is genuine.
  - **Rule-set-size scaling — the per-theorem fast path is DONE
    (`derive_theorem`).** `replay_db` builds one `Closed` clause per `|-`
    assertion in the *whole* database (~47k for `set.mm`), and each
    lemma-application's `nth_conjunct` is O(position) — so whole-database replay
    is impractical (minutes/theorem at `set.mm` scale). The fix shipped:
    [`derive_theorem(db, label)`](./mm_database.rs) builds the rule set from just
    the **proof's referenced `|-` assertions** (`scoped_clauses`, the label
    closure — small per theorem), sharing the entire replay loop (`replay_with`)
    with `replay_db`. Measured: `hol.mm` all 151 in ~44 s (vs minutes), and
    **`set.mm` ~8.6 ms/theorem** (50 theorems in ~0.43 s) — practical. The
    resulting logic is a sub-rule-set `L' ⊆ L`; `transport_db` monotonicity
    lifts `Derivable_L' ⟹ Derivable_L` when the full-database statement is wanted
    (not yet auto-applied — recorded as the remaining "lift to full L" step).
  - **Tying the Rust `RuleSet` to a first-class HOL `Database` *value*** (à la
    [`database.rs`](./database.rs)'s `Derivable_DB`) is a further unification —
    the `mm_database` rule set is a Rust closure, not yet a HOL `db` value.

### mm_import — real `.mm` databases INTO covalence-hol (DONE, hol.mm + set.mm)

[`mm_import.rs`](./mm_import.rs) is the high-level API over the fast per-theorem
[`derive_theorem`](./mm_database.rs): the honest culmination of the
construct-don't-trust pipeline — **real Metamath databases flow into the kernel
as `⊢ Derivable_L' ⌜S⌝` theorems**, re-derived from their (possibly compressed)
proofs, each scoped to its own referenced lemmas so import is practical.

- `import_theorems(db)` — import every `$p` theorem (proof present) via
  `derive_theorem`, into `(label, Result<Thm>)`, database order, capturing
  per-theorem errors.
- `import_theorems_with_progress(db, progress)` — same, invoking
  `progress(done, total, label)` after each theorem (for a UI progress bar).
- `read_and_import(source)` — `metamath::parse` + import, surfacing the first
  parse/replay failure as `ImportError`.

**Real `hol.mm` (vendored, CC0, all 151 `$p` proofs compressed) DONE.**
`import_hol_mm` (default, fast) imports the first 25 theorems + the `idi`
(`H ⊢ H`, empty-scoped-rule-set) edge case; `import_hol_mm_full` (`#[ignore]`d,
~44 s) sweeps all 151, each genuine (`has_no_obs`). **Real `set.mm` DONE
(samples):** `import_set_mm_sample` (`#[ignore]`d, `COV_SET_MM` env path) imports
50 theorems in ~0.43 s (~8.6 ms/theorem) via the scoped path — set.mm theorems
flow into covalence-hol at practical speed. (Importing *all* 47k is bounded only
by total proof size now, not the database-size blowup.)

**Deferred — declarations-only load + prove-on-demand.** A future workflow: parse
a database keeping only the **declarations** (the `$a`/`$p` statements + frames +
`$d`), *without* storing/parsing the proof bodies — so one can cheaply load and
browse all of set.mm's statements (and use them as the rule set), then call
`derive_theorem` to **prove a specific declaration** on demand. Needs a
proof-skipping parse mode in `covalence-metamath` (e.g. `Proof` stored as the raw
unparsed token span, decoded lazily only when a theorem is actually derived) and a
`derive_theorem` that decodes that one proof on the fly. The `/metamath` demo would
then offer "load declarations only" + click-to-prove. **Not built.**

### Future directions — the set.mm/ZFC stdlib program (design, not yet built)

Priorities (user, this session): **clean + auditable API first** (the import is
run once; don't over-optimize), then performance. The construct-don't-trust core
(replay re-checks every step; `has_no_obs`) is the auditable bit. North stars:

- **set.mm as the ZFC stdlib, used from the *frontend*.** Import set.mm as the
  ZFC standard library foundation and *use it from the nice frontend* — with
  **namespacing, tactics**, etc. — rather than hand-editing raw `.mm`. We may
  replace parts with our own proofs, but **keep set.mm FFI as the mirror-principle
  check** ("we are proving what we think we are"), and *don't* roll our own for
  the basic derivations or the axioms (use set.mm's).
- **Shorter / readable HOL repr — the structured-former encoding (MODERATE).**
  Today `parse`/`encode` emit a flat `mm$concat`-tree of per-symbol `mm$c$<tok>`
  *free variables* (readable token names, but verbose, and the theorem carries
  them all as free-var parameters). The win: give each **syntactic former** (`$a`
  with a `wff`/`class`/`term`/… conclusion) a **transparent HOL definition** —
  via the kernel's `define`, exactly like `nat.add`/`nat.mul` — of its arity:
  `mm.former.<label> := λ(args:nat…). <concat-encoding of the former body>`, and
  have `parse` emit `mm.former.<label>(enc arg₁,…,enc argₖ)`. Then `⌜S⌝` is a
  readable **tree of named definitions** (`wi(ph,ps)`, `wcel(A,B)`) — short,
  structured, and (unlike free vars) genuine *constants*, so the theorem's only
  free vars are the real metavars (`mm$v$…`). Transparent: each former's defining
  theorem `⊢ mm.former.<label> = λ…. <body>` unfolds it to the raw syntax on
  demand (a conservative definitional extension — no new axioms).
  **Soundness/replay is unchanged**: replay keeps the formers *folded* (never
  unfolds them), and they're constants while metavars are free vars, so a
  substitution-instance is still exactly `all_elim`
  (`enc(schema)[v:=enc(arg)] = enc(subst)` syntactically — folded constants don't
  reduce). The Parser already does the former-structured *parse*
  (`Former`/`parse`/`encode_greedy`); the change is (a) a per-database pass that
  `define`s one constant per former, and (b) `parse` emitting the former-constant
  application instead of `concat`. Symbols + `concat` could likewise become
  transparent definitions (toward the nat-Gödel-numbering view) as a follow-on.
  Re-test prop/demo/group + hol.mm + the formerly-failing set.mm theorems.
  NB: distinct from Metamath's `df-*` *definitional axioms* (`|-` axioms, already
  imported as rule-set clauses) — turning *those* into unfolding HOL definitions
  (`M := S` + conservativity) is a separate, deeper feature.
- **Two-phase / definitions-first import (EASY–MODERATE).** A mode that loads
  just the **signature** — the formers (the `mm$f$…` constants above) + the
  `df-*` definitional axioms — and shows it, *without* proving theorems (cheap;
  browse/use the ZFC signature). Then prove theorems (the parallel part). With
  uninterpreted former-constants there's no hard ordering dependency, so
  "definitions first" is mainly organizational; it becomes load-bearing only if
  `df-*` become unfolding definitions. Pairs with declarations-only load above.
- **Instrumentation:** basic operation counters (kernel inference steps per
  theorem) + memory-use counters surfaced in the import UI.
- **Definition / dependency graph** info, then a **graph explorer**; and, for a
  large verification job, a **hierarchical task-graph visualization** with the
  ability to zoom into threads of work as they happen.

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

## transport_db — generic transport between Metamath-database logics (DONE: generic + σ=id monotonicity)

[`transport_db.rs`](./transport_db.rs) generalises [`relations.rs`](./relations.rs)'s
fixed-frame `Derivable_DB` transport to an **arbitrary [`RuleSet`]** — the
"relate formal systems" / "induction on derivations" engine. Over any source/target
rule set sharing a carrier `Φ` and a translation `σ : Φ → Φ`:

- `interp_stmt(src, tgt, σ, a)` — the statement `Derivable(src, a) ⟹ Derivable(tgt, σ a)`;
- `sigma_pred(tgt, σ)` — the rule-induction predicate `λx. Derivable(tgt, σ x)`;
- `transport(src, tgt, σ, clause_sims)` — `⊢ ∀A. Derivable(src, A) ⟹ Derivable(tgt, σ A)`,
  proved in ONE move as `metalogic::rule_induction(sigma_pred(tgt,σ), clause_sims,
  derivable(src, A), "A", Φ)` (the trailing `pred A` redex β-reduced to the clean
  `Derivable(tgt, σ A)`). The caller's **`clause_sims` ARE the per-rule
  "σ simulates this rule in the target" obligations** — `clause_sims[k]` proves
  `src`'s k-th clause at `d := sigma_pred(tgt,σ)`; `rule_induction` re-checks each,
  so a bogus simulation fails the build. **Done, proven.**

- **Worked instance — conservative extension / monotonicity for arbitrary
  Metamath databases (σ = id, T ⊇ S).** `mm_database::clause_infos` exposes each
  `|-` clause (`float_vars`/`ess_encs`/`concl_enc` + `build_body`); the test builds
  source `S` (prop calc `ax-1`/`ax-2`/`ax-mp`) and target `T = S + ax-3` (same
  signature), and for each source clause proves the σ=id simulation by routing the
  `σ`-image premises through the *byte-identical* target clause (`nth_conjunct` +
  `all_elim` + the impredicative derivation constructor), then β-folding back.
  `transport` lands the genuine `⊢ ∀A. Derivable_S A ⟹ Derivable_T (id A)`
  (hyp-free, `has_no_obs`), and the second test specialises it to move a concrete
  `ax-1` axiom instance from `S` into `T`. **Done, proven.** (Contrast
  `database::monotone`, which proves the same for the fixed MP+axiom frame; this is
  it for any database's full rule set, through the generic engine.)

- **Remaining — a richer structural `σ`.** A genuinely structural translation
  (constant-symbol renaming `mm$c$foo ↦ mm$c$bar`, connective mapping) with the
  per-rule simulations honestly proved is **not built**. *Blocker:* the
  `mm_database` carrier `Φ = nat` is a free term algebra of **uninterpreted free
  vars** (`mm$concat`, `mm$c$<tok>`) — substitution = `all_elim` precisely because
  there is *no* constructor/recursor. A structural `σ` that descends `concat`-trees
  cannot be written as a closed HOL `Φ → Φ` function without first reifying the
  encoding as a genuine inductive datatype (a recursor over `concat`/leaves). That
  datatype-ification is the prerequisite, shared with the "non-trivial structural
  `σ`" note below.
- **Remaining — the HOL→ZFC-scale instance** (`Derivable_HOL ⟹ Derivable_ZFC ∘ σ`):
  the north-star target; needs the structural-σ infrastructure above plus the
  concrete HOL/ZFC databases as rule sets. **Not built.**

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
rule schemas (the `#logic`-semantics seed). Pieces (1) an encoding of Metamath
expressions into a HOL carrier `Φ` and (2) a `RuleSet` builder turning each `|-`
assertion into a `Closed_L` clause are now **DONE** in
[`mm_database.rs`](./mm_database.rs) (demonstrated on the prop-calc, demo0, and
GROUP databases). Remaining: (3) a per-logic **denotation** (only needed to
*project* a finished `Derivable_L` to a concrete fact) is **not built**, and the
`$d`/typecode restrictions are over-approximated (see the `mm_database` section
above).

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

# Covalence — Roadmap (time-to-product for the Metamath vision)

The "what's next" doc, oriented at **minimizing time to a thin-but-honest
product**. For the vision (the three-layer stack, internal Metamath as the thin
waist) see [`VISION.md`](./VISION.md) §1; for the substrate detail see
[`theories-models-and-logics.md`](./theories-models-and-logics.md) §5.6/§5.7; for
the kernel TCB [`kernel-design.md`](./kernel-design.md).

## What "product" means

A **thin but honest demo of the full experience**:

> *write theories and specs → lower them to various logics → prove things in
> different logics and models, and transport between them.*

Two headline instances we are aiming the thin demo at:

- **Verify *all of* `set.mm` in Grothendieck-Tarski** — ingest `set.mm`, check
  *the whole database*, and read off its axiom base (`ax-groth` + ZFC) as `⊑` a GT
  database (conservative extension). **All of set.mm is the right target, not a
  fragment** — Metamath verification is whole-database and auto-scaling (a single
  interesting theorem already pulls in most of the library), so "one theorem" is
  the *same engineering* as "all", differing only in wall-clock — which is short
  (the verifier is tiny, verification ~linear in proof size). It is a good
  **benchmark**. And it stays cheap on the HOL side by **proof-irrelevance**: we run
  the Rust `metamath::verify` and record `∃D. ValidProof(D,P,Ax)` — we *never*
  replay proofs through the kernel ("we never need to look at the proofs").
- **Analysis in SOA** — reify second-order arithmetic, state the reals via
  Spivak's axioms, and prove *one* extension with a real-numbers type *conservative*
  over SOA (later: builtins for limits / exponentials / calculus).

**The leanness asymmetry (the actual time-minimizer):** *verifying* auto-scales
(set.mm = whole-database, "all" ≈ "one" effort — do all), but *proving* does not
(each SOA/analysis result is real kernel work — *there* "one honest result" is the
lean MVP). So: **verify all of set.mm (a short benchmark); prove one real thing in
SOA (the lean part).** The minimality that helps the set.mm product is the *trust
path*, not the theorem count: use **mode-1 symbolic ingestion** via the existing
small/auditable Rust `metamath::verify` (defer the verified-WASM-checker), and "in
GT" is reading off the axiom base. The real set.mm TTP levers are the
**compressed-proof parser + full `.mm` grammar** and confirming verifier throughput.

## The honesty principle (what "construct, don't trust" means)

The keystone of the Metamath thin-waist is **proof-irrelevance done honestly**:

> `metamath::verify` (the small, untrusted Rust checker) lets us **construct**,
> in the HOL kernel, the theorem `⊢ Derivable_… ⌜S⌝` ("**∃ a derivation** of `S`")
> — we never *trust* the checker, never inject an oracle, and never replay the
> object logic's steps as denotations. The Rust replay is untrusted; every kernel
> step it drives is re-checked; the only thing you trust is that the function
> **constructs the theorem it claims to** (its type signature), not its internals.

Two consequences we lean on hard:

- **No trust seam / no observer.** Derivability is *constructed* via the
  impredicative engine's derivation constructors, not admitted via an oracle. (The
  kernel's early `Observer` primitive is being reworked into a lower layer — avoid
  coupling to it.)
- **Never unfold the object terms.** We land `Derivable_… ⌜S⌝` over the *encoded
  syntax* `⌜S⌝`, not its denotation `⟦S⟧`. Nat literals encode as `S(S(S(Z)))`,
  proofs can be double-exponentially long with zero sharing — and that is fine,
  because we only ever assert *existence* of a derivation; we never build or
  unfold it. The result theorem is small.

## What is already built

- **Authoring forms** — `#sig`/`#thy`/`#model`/`#models` + `#spec`; `nat.sig`/
  `nat.thy` with `nat.cov ⊨ nat.thy` certified.
- **The Metamath engine + reader in the lower, HOL-free `covalence-metamath`
  crate** (expr/subst/frame/DV/verify + the `.mm` reader) — the `ValidProof`
  primitive. *(Done this session: the engine was inverted down out of
  `covalence-hol`, which now depends on `covalence-metamath`. Next: a `Database`
  trait with pluggable backends — the in-memory RPN checker as a HOL-free
  "sanity-check" impl behind a flag, and a HOL-backed consumer that reads axiom
  sets from real `.mm` files.)*
- **PA, deeply** — `Derivable_PA` (pure, soundness proved once, one-step
  projection) *and* `peano::mm_pa` + `mm_replay` (a Metamath PA database + an
  untrusted-proof→kernel replay). *(NB: `mm_replay` currently lands `⟦S⟧` — the
  denotation; the honesty principle above says the general replay should land
  `Derivable_… ⌜S⌝` instead, leaving `project`-to-`⟦S⟧` an optional last step.)*
- **The generic engine** `metalogic::{RuleSet, derivable, rule_induction}` and the
  **HOL `Database` type + relation lattice** `metalogic::{database, relations}`:
  `⊑`/monotonicity and `⟹_σ`/transport as kernel-proved theorems. *(Done this
  session — Phase A: `database::Derivable_DB` is now literally
  `derivable(&db_rule_set(db), ·)`, one derivability notion.)*
- **Accelerators** — Alethe/SMT goal discharge (`(#by (smt))`) + n-ary Farkas.

## The critical path (the keystone first)

### Phase A — the keystone: unify `Derivable` + `#logic`-as-database ✅ DONE

**Drive the generic engine off a HOL `Database` value**, collapsing the two
`Derivable` notions (engine `Derivable_L` over a Rust `RuleSet` closure;
`Derivable_DB` over a HOL `Database` value) into one. `database::db_rule_set(db)`
packages the database value as a `metalogic::RuleSet`, and `derivable_db` is now
literally `metalogic::derivable(&db_rule_set(db), ·)`. This makes "**a `#logic`
*is* a Metamath database**" real: a `#logic` produces a HOL `Database`, its
derivability comes from the unified engine, and the **relation lattice (`⊑`/`⟹_σ`)
applies to every logic**.

### Phase B — construct, don't trust: replay `metamath::verify` → `⊢ Derivable_… ⌜S⌝`

Given a Metamath database + a proof the (untrusted) Rust `metamath::verify`
accepts, **construct** the kernel theorem `⊢ Derivable_… ⌜S⌝` by replaying the
proof through the impredicative engine's derivation constructors — *no oracle, no
observer, no denotation* (see the honesty principle above). This is exactly
`peano::mm_replay` generalized and re-aimed: land in `Derivable_… ⌜S⌝` rather
than `⟦S⟧`. The first slice is the **propositional fragment**, where Metamath
wffs map directly into `init::prop`'s `Φ` carrier and ax-1/ax-2/ax-mp are exactly
`init::prop::derive_axiom`/`derive_mp` — so a verified prop-calc `.mm` proof
becomes `⊢ Derivable_Prop ⌜S⌝`. The general, schema-database version (one
substitution-instance `Closed` clause per assertion — the `RuleSet`-from-`Database`
work) is the follow-on; with it the replay lands `⊢ Derivable_DB ⌜db⌝ ⌜S⌝` over
the encoded database value, the literal "`#logic` is a Metamath database."

### Phase C — the full-experience demo (the MVP)

Assemble the thin demo on A+B: write a theory + spec, **lower it to ≥2
logics-as-databases via `#logic`**, prove a theorem in one, and **transport** it
across (`⊑`/`⟹_σ`). The `add_comm` cross-model demo is the seed; the Metamath
version is "the same theory as two databases with a proven transport." This *is*
the honest demo of write→lower→prove-across.

### Phase D — the headline instances (parallel, on A–C)

- **The `Database` trait + readers** ✅ *mostly done.* `covalence-metamath` now
  has primitive `Expr` (typecode + flat `Vec<Symbol>`, SExpr only at the
  `to_sexpr`/`from_sexpr` boundary), the **`DatabaseSink`** builder trait +
  `SymbolKind` enum the readers drive, the **compressed-proof decoder**
  (base-20/5 + `Z` saves + heap) and **`$[ ]$` file inclusion** (`SourceResolver`),
  and the in-memory RPN checker as a HOL-free **sanity-check** verifier behind the
  default-on `checker` feature. The **HOL-backed `DatabaseSink`**
  (`metalogic::mm_sink::HolPropSink`, `read_prop`) constructs `⊢ Derivable_Prop ⌜S⌝`
  *as it reads* a prop `.mm` — the reader drives the builder trait, this is the HOL
  backend. *Remaining:* generalising that sink to an **arbitrary** database (the
  schema-database replay landing `⊢ Derivable_DB ⌜db⌝ ⌜S⌝`), and symbol interning
  for set.mm scale.
- **`set.mm` in GT** — read *all of* `set.mm` ([metamath/set.mm]; needs the
  compressed-proof parser + full `.mm` grammar) and verify the whole database via
  the Rust `metamath::verify` (mode-1 symbolic ingestion; the HOL side stays
  proof-irrelevant — `∃` derivation, never unfolded). An independent elaborator
  checks the resulting database against a GT database (fetched + diffed, §5.7), and
  the axiom relation (`ax-groth`+ZFC `⊑` GT) is a `⊑`/conservative-extension theorem.
- **`hol.mm` to define our internal HOL** — [set.mm's `hol.mm`][hol.mm] is HOL
  *as a Metamath database*. Ingesting it makes the three-layer vision literal: the
  middle layer's logic is **specified** by a Metamath database, and our kernel is
  the implementation we relate to it (a representation-equivalence: our HOL ≅
  Metamath-HOL). A natural confidence-builder and a canonical spec for the waist.
- **theory→Metamath as a compile target** — lower a standard `#thy` to a Metamath
  database, as a *first-order* or *higher-order* theory. A particularly
  interesting target to relate to/from (the mirror principle): the same theory,
  two independent lowerings, proven equivalent. (And the reason we keep terms
  *encoded*, never unfolded: a nat literal is `S(S(S(Z)))`, exponential to expand.)
- **Analysis in SOA** — reify SOA (the ladder's rung 3: a second sort +
  comprehension over the FOL framework), Spivak's reals as a `#thy`, and the
  reals-extension-conservative-over-SOA result. Calculus builtins are a follow-on.

[metamath/set.mm]: https://github.com/metamath/set.mm
[hol.mm]: https://raw.githubusercontent.com/metamath/set.mm/refs/heads/develop/hol.mm

## After the product

### Phase E — factor out `covalence-pure`, sophisticate the backend

Reintroduce `covalence-pure` (the first-order base; HOL as a type inside it,
[`covalence-pure.md`](./covalence-pure.md)), then the **WASM executor models** —
the computational-metatheory / bottom layer: programs join by proving their
bytecode meets a spec under the executor's semantics; proven-WASM compilation makes
the middle layer "generalized Haskell." (Also folds in the legacy
`covalence-kernel` → re-export-façade migration of the app stack.)

### Phase F — more frontends, with commutative-diagram confidence

Add frontends beyond `.cov`/`#sig` — **SpecTec** (the WebAssembly spec DSL) as a
first-class frontend, **egg/egglog** theories, etc. Gain confidence in a complex
frontend the **mirror-principle** way: prove a *commutative diagram* —
`SpecTec ⟶ our-prover` vs `SpecTec ⟶ HOL ⟶ HOL-in-our-prover` — equivalent, so two
independent lowerings agreeing is the evidence. Same shape for egg/egglog.

---

## Reference: the backup branch

The repo was pared to the *current design only*; everything removed lives on
**`backup/pre-hol-cleanup`** (`git checkout backup/pre-hol-cleanup -- <path>`):
the old `covalence-hol` postulate catalogues (`nat_axioms.rs`/`int_axioms.rs`/old
`init/`), the gated Pure-era modules (`bridge.rs`/`peano.rs`/`pure_hol.rs`), the
HOL Python bindings (`covalence-python/src/pure.rs`), and the retired docs
(`ARCHITECTURE.md`/`AGENTS.md`/`MVP_DESIGN.md`/`plan.md`/`docs/design/proposals/*`/
the arena-egraph prover docs).

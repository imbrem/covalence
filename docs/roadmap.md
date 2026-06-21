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

- **Verify a `set.mm` fragment in Grothendieck-Tarski** — ingest a real `set.mm`
  development, check its proofs, and relate its axiom base to a GT database
  (`set.mm`'s axioms `⊑` GT, conservative extension).
- **Analysis in SOA** — reify second-order arithmetic, state the reals via
  Spivak's axioms, and prove an extension with a real-numbers type *conservative*
  over SOA (later: builtins for limits / exponentials / calculus).

"Thin but honest" = the **leanest version that is genuinely real** (a real `set.mm`
theorem actually verified; a real conservativity result actually proved) — not a
mock. That framing is the time-minimizer.

## What is already built (this session)

The pieces exist; they are not yet *unified* into "a logic = a Metamath database
you lower theories into and prove across":

- **Authoring forms** — `#sig`/`#thy`/`#model`/`#models` + `#spec`; `nat.sig`/
  `nat.thy` with `nat.cov ⊨ nat.thy` certified.
- **The Metamath engine** in `covalence-hol/src/metamath/` (expr/subst/frame/DV/
  verify) — the `ValidProof` primitive — plus the `.mm` reader in
  `covalence-metamath`.
- **PA, deeply** — `Derivable_PA` (pure, soundness proved once, one-step
  projection) *and* `peano::mm_pa` + `mm_replay` (a Metamath PA database + an
  untrusted-proof→kernel replay that lands `∀x.x+0=x` by induction).
- **The generic engine** `metalogic::{RuleSet, derivable, rule_induction}` and the
  **HOL `Database` type + relation lattice** `metalogic::{database, relations}`:
  `⊑`/monotonicity and `⟹_σ`/transport as kernel-proved theorems.
- **Accelerators** — Alethe/SMT goal discharge (`(#by (smt))`) + n-ary Farkas.

## The critical path (the keystone first)

### Phase A — the keystone: unify `Derivable` + `#logic`-as-database

The single highest-leverage move (already SKELETON'd in `metalogic/SKELETONS.md`):
**drive the generic engine off a HOL `Database` value**, collapsing the two
`Derivable` notions (engine `Derivable_L` over a Rust `RuleSet` closure;
`Derivable_DB` over a HOL `Database` value) into one. This makes "**a `#logic` *is*
a Metamath database**" real in code: a `#logic` produces a HOL `Database`, its
derivability comes from the unified engine, and the **relation lattice (`⊑`/`⟹_σ`)
applies to every logic**. Everything below rides on this — do it first.

### Phase B — ground it honestly: `∃P. ValidProof ⟺ Derivable`

Connect the existence-of-derivation to the *actual* `metamath::verify` primitive
(reify `ValidProof` in HOL, or bridge a concrete verified proof to `Derivable`).
For the thin demo this can be partial — but it is what makes "we prove what we
think we prove" literally true rather than an impredicative-encoding artifact.

### Phase C — the full-experience demo (the MVP)

Assemble the thin demo on A+B: write a theory + spec, **lower it to ≥2
logics-as-databases via `#logic`**, prove a theorem in one, and **transport** it
across (`⊑`/`⟹_σ`). The `add_comm` cross-model demo is the seed; the Metamath
version is "the same theory as two databases with a proven transport." This *is*
the honest demo of write→lower→prove-across.

### Phase D — the headline instances (parallel, on A–C)

- **`set.mm` in GT** — `covalence-metamath` ingests a `set.mm` fragment (needs the
  compressed-proof parser), verifies it, and `covalence-metamath`'s independent
  elaborator checks the resulting database against a GT database (fetched + diffed,
  §5.7); the axiom relation is a `⊑`/conservative-extension theorem.
- **Analysis in SOA** — reify SOA (the ladder's rung 3: a second sort +
  comprehension over the FOL framework), Spivak's reals as a `#thy`, and the
  reals-extension-conservative-over-SOA result. Calculus builtins are a follow-on.

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

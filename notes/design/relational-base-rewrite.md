# Relational base rewrite — persist proven facts as signed SQLite

- **Status:** Draft — **maintainer to flesh out**. This is a scaffold: the
  cross-references and the shape are pre-populated from existing work; the
  decisions in *Open questions* are the maintainer's to make.
- **Owner:** maintainer
- **Last touched:** 2026-07-11
- **Related:**
  - Base abstraction seam (landed, additive): `crates/kernel/base/src/algebra.rs`
    (`CertificateAlgebra` + `EqnKernel`, and its **RelKernel recipe** in the module
    docs §"How the future relations base implements this same trait"),
    `crates/kernel/base/src/api.rs` (the facade + stability CONTRACT).
  - Positive relation primitives: `crates/kernel/base/trusted/src/rel.rs`
    (`execute`/`transpose`/`compose`/`meet`/`join` — the positive-only mint sites).
  - TCB-as-data PoC: `crates/app/tcb-db` (`covalence-tcb-db`) — dumps the golden
    manifests + audit into a STRICT-schema `.db` with round-trip tests.
  - Design corpus: [`../vibes/base-abstraction.md`](../vibes/base-abstraction.md)
    (§4 relations impl, §5 TCB-to-SQLite, §6 what-must-be-preserved),
    [`../vibes/base-api-surface.md`](../vibes/base-api-surface.md) (what core/eval
    actually consume — the surface the rewrite must keep),
    [`../vibes/base-relcalc-holomega-design.md`](../vibes/base-relcalc-holomega-design.md)
    (the authoritative relations-as-untrusted-functions redesign, Fronts D/E),
    [`../vibes/tcb-holomega-roadmap.md`](../vibes/tcb-holomega-roadmap.md).
  - The human-readable TCB picture: [`../vibes/kernel/tcb/what-is-the-tcb.md`](../vibes/kernel/tcb/what-is-the-tcb.md).

## Context / problem

The base kernel (`covalence-pure-trusted`, `crates/kernel/base`) mints theorems
through 24 audited `Thm::new` sites (see `docs/deps/tcb-audit.json`). Today,
**computation lives inside trusted `decide` bodies** (`canon`, the `Builtins`
op catalogue) and **axioms are Rust code**. The maintainer's directive is to
refactor severely so that:

1. **all computation = untrusted relation evaluation** — the only primitive mint
   is positive graph membership `⊢ (a, b) ∈ Rel(f)` for an untrusted `f`
   (`rel.rs::execute`, sound for any `f`); and
2. **all axioms = simple propositions** of the shape
   `Computation(i, o) ⟹ SomeRelation(i, o)`.

Once axioms and relation facts are *data* rather than code, the TCB — and, more
ambitiously, the **proven-fact store** — can be **persisted to SQLite** and
**signed**, so a peer can be handed facts (not re-derivations) and check the
signature + re-execute or accept an attestation. `covalence-tcb-db` is the
first, partial step: it already round-trips the *manifests* through a `.db`.

## Goals

- The consumer surface (`covalence_pure::api`) is **unchanged**: core/eval cannot
  observe which base they run on (the `CertificateAlgebra` abstraction already
  proves this is possible — `algebra.rs`).
- Computation is expressed as untrusted `Rel(f)` evaluation; `canon` becomes
  *derived* (execute + admitted functionality axiom), per the RelKernel recipe.
- Axioms become serializable schematic propositions; the per-language TCB is
  *"the relation identities it admits + the schematic propositions it admits."*
- Proven facts (and the TCB itself) persist to a **signed SQLite** artifact, with
  a documented reload discipline: **reload returns rows, not theorems** — a
  `⊢ a R b` is recovered by re-execution or by an attestation axiom, never forged.

## Non-goals

- Migrating `covalence-core`/`covalence-hol-eval` onto the trait *now* — deferred
  until in-flight core work merges (recorded in `crates/kernel/base/SKELETONS.md`;
  order in `base-abstraction.md` §8).
- Changing the proposition vocabulary (`Expr`/`Op`/`App`/`Val`/`Eqn`) or the
  trust enumeration (`Language`/`Rule`/`CanonRule`) — the narrow waist stays
  (`base-abstraction.md` §3, §6).
- The federation/PKI trust-store policy beyond "facts carry signatures" — that is
  its own concern (see the memory notes on signatures-as-meta-assumptions;
  cross-link when a doc exists).

## Proposal

*(Maintainer to flesh out.)* Skeleton, drawn from the existing recipe:

1. **RelKernel: CertificateAlgebra** — a second impl of the algebra alongside
   `EqnKernel`, whose primitive mint is `execute`. See `algebra.rs` module docs
   for the method-by-method plan (`apply` = schematic-axiom instantiation, `canon`
   = derived via `LiftFn<F: CanonRule>` + functionality axiom + `mp`, transport
   unchanged).
2. **Axioms-as-data** — an admitted rule becomes an admitted *proposition with
   schema variables*; `decide` shrinks to "pick a substitution."
3. **The store schema** — extend `covalence-tcb-db`'s STRICT schema
   (`languages`, `language_rules`, `configs`, `mint_sites`) with a `propositions`
   table (serialized ground/schema expressions) and relation-graph tables
   (`rel_edges` keyed by content addresses); add signature columns/envelopes.
4. **Signing + reload discipline** — every persisted fact is signed; reload
   yields rows; `⊢` is regained by re-execution or an attestation axiom (R4).

## Alternatives considered

- **Keep computation in trusted `decide` bodies, only dump the manifest** — this
  is today's `covalence-tcb-db` PoC. Rejected as the endpoint: it never shrinks
  the trusted computation surface, so the SQLite dump can't stand in for the code.
- **Serialize theorems directly and trust the deserializer** — rejected: would
  add a forging mint site. The R3 discipline (rows, not theorems) is a standing
  invariant.

## Open questions

*(Maintainer-owned; this is the iteration surface.)*

- Serialization format for schematic propositions and relation edges — reuse
  `covalence-multiformat`'s content-addressed envelopes, or a bespoke SQLite blob
  encoding?
- Signature model: sign individual facts, batches, or the whole store manifest?
  How does this compose with the existing signatures-as-meta-assumptions idea?
- Which attestation axiom (R4) shape lets a peer *accept* a signed fact without
  re-execution, and how is that trust scoped per-language?
- Sequencing against Fronts D/E in `base-relcalc-holomega-design.md` and the core
  migration freeze (`base-abstraction.md` §8).

## Status / next steps

Scaffold only. Next: maintainer fills *Proposal* and *Open questions*; work is
gated behind the core-migration freeze noted in `crates/kernel/base/SKELETONS.md`.

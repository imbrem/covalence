# Layer 1: The Framework

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This document is part of a design proposal generated during a
> planning conversation. It is **not** a committed architecture; the
> shape, vocabulary, and approach are subject to substantial revision
> before any implementation lands. For the canonical view of what is
> *actually built* vs. what is *proposed*, see
> [`where-we-are.md`](../../../where-we-are.md). For the proposal
> index, see [`README.md`](./README.md).

The Framework is the **trust boundary** of the system. It is a small
Rust crate implementing a [Logical Framework
(LF)](./00-glossary.md#logical-framework-lf) in the Isabelle/Pure
style, plus the [authority](./00-glossary.md#authority) and
[store](./00-glossary.md#store) primitives that scope crypto
assumptions honestly.

Everything *outside* the framework — [HOL](./00-glossary.md#hol-higher-order-logic)
derivations, [oracles](./00-glossary.md#oracle),
[mount](./00-glossary.md#mount) machinery, signature schemes, hash
functions, executors, the morphism layer, the eventual surface
compiler — is **untrusted** in the LCF sense: a bug there is caught by
re-checking against the framework, not by exposing false facts.

**Target size:** ~700–800 lines of Rust, no `unsafe`, no external
deps beyond [`covalence-rand`](../../../../crates/covalence-rand).

**Status:** design only. Crate does not yet exist.

This doc partially supersedes [`prover-architecture.md`](../../../prover-architecture.md)
— specifically §§1–4 on the kernel's data model and inference rules.
The disjunct trick (§3.6 of that doc) moves to the
[HOL layer](./00-glossary.md#hol-higher-order-logic), as do the primops.

---

## 1. The five concepts

The framework exposes exactly five primitive concepts:

1. **[Terms](./00-glossary.md#term) and types** — the locally-nameless
   term language and its types-with-kinds.
2. **[Sequents](./00-glossary.md#sequent-γ--φ) `Γ ⊢ φ`** — the
   framework's atomic judgment, with
   [Propositions](./00-glossary.md#proposition-prop--theorem-thm) and
   [Theorems](./00-glossary.md#proposition-prop--theorem-thm) as
   wrapping types.
3. **[Authority](./00-glossary.md#authority) +
   [observation](./00-glossary.md#observation)** — the single trust
   primitive: an authority writes facts under its own opaque relation
   names.
4. **[Store](./00-glossary.md#store)** — scoped sets of blob-names that
   crypto assumptions quantify over.
5. **[Definitions](./00-glossary.md#definition)** — introducing new
   constants by definitional equality.

That's it. No hash functions, no signature schemes, no executors, no
serialization, no WASM, no specific oracle. Each of those is a
separate crate implementing the [Authority](./00-glossary.md#authority)
interface or layering oracle implementations on top.

---

## 2. Term language

### 2.1 Locally-nameless terms

Terms use **de Bruijn indices for bound variables + named
[fresh](./00-glossary.md#fresh-rng-based) free variables**.
α-equivalence is structural equality of the internal `TermDef`;
display names live in a side table (the pretty-printer's concern, not
the kernel's).

Public view (`TermKind`):

```rust
pub enum TermKind {
    Bound(u32),                    // de Bruijn index
    Free(VarName, TypeRef),        // named free variable + type
    Const(ConstName, TypeRef),     // user-declared constant
    App(TermRef, TermRef),         // application
    Abs(TypeRef, TermRef),         // λx:τ. body (body uses de Bruijn)
    MetaImp(TermRef, TermRef),     // φ ⟹ ψ — meta-implication
    MetaAll(TypeRef, TermRef),     // ⋀x:τ. φ — meta-universal
    Eq(TermRef, TermRef),          // t ≡ u — meta-equality
}
```

This is enough to express any propositional and quantificational
structure the framework needs.

**Object-logic connectives** (HOL's `∧`, `∨`, `=` (the HOL one),
`Forall`, `Exists`, `Eps`, …) are **defined inside the [HOL
layer](./00-glossary.md#hol-higher-order-logic)** as ordinary
constants — the framework does not bake them in. The framework's `Eq`
is **meta-equality `≡`**, distinct from object-level `=`.

### 2.2 Types with kinds

```rust
pub enum TypeKind {
    Prop,                              // the kind of meta-propositions
    Type,                              // the kind of object-level types
    Arrow(TypeRef, TypeRef),           // function type
    TVar(TyVarName, KindRef),          // type variable
    TyApp(TyConst, Vec<TypeRef>),      // user-declared type constructor
}
```

**Kinds.** We allow two kinds at framework level: `Prop` (kind of
meta-propositions) and `Type` (kind of object-level types). This is
enough for Pure-style LF. Future extensions to HOL-Omega-style higher
kinds add `KindArrow` etc.; the schema is forward-compatible because
kinds are themselves a sealed enum that can grow.

The decision to **keep kind info on every type** (rather than infer at
use sites) is per
[`prover-architecture.md`](../../../prover-architecture.md)'s open question
on intrinsic typing — we land on intrinsic for the framework redesign
because it makes the well-formedness check O(1) per allocation.

### 2.3 Closed vs open terms

A term is **closed** if it has no `Bound(_)` with index ≥ its
surrounding binder depth and no `Free(_)` reachable. Closed-ness is
tracked per term in a side table; computed once at insertion.

The framework's [observation](./00-glossary.md#observation) primitive
requires the relation arguments to be closed. Open terms exist only
as subterms during proof construction.

### 2.4 No internal content addressing

Per the [conventions](./01-conventions.md) and the planning
discussion: **the framework does not hash its own terms or arenas**.
The Phase H content-hashing in the current `covalence-kernel`
(`Arena::hash()`, `ContentHash`) moves *out* of the framework and into
a separate `TermHasherOracle` (planned). The framework's term IDs are
internal `u32`s only.

---

## 3. Inference rules

Five categories. All implemented in Rust, in the
[meta-trust set](./00-glossary.md#meta-trust-set).

### 3.1 Pure LF rules

```
   φ ∈ Γ                         Γ, φ ⊢ ψ
  ────────  (assume)            ────────────  (imp-i)
   Γ ⊢ φ                         Γ ⊢ φ ⟹ ψ

   Γ ⊢ φ ⟹ ψ    Γ ⊢ φ
  ──────────────────────  (imp-e / MP)
            Γ ⊢ ψ


   Γ ⊢ φ(x)    x ∉ FV(Γ)         Γ ⊢ ⋀x:τ. φ(x)    t : τ
  ────────────────────────  (all-i)   ──────────────────────  (all-e)
       Γ ⊢ ⋀x:τ. φ(x)                       Γ ⊢ φ(t)
```

Standard intro/elim rules for the two meta-connectives `⟹` and `⋀`.
[MP](./00-glossary.md#modus-ponens-mp) and (all-e) compose into
substitution-of-witness, which is enough to derive every Hilbert-style
operation.

### 3.2 Equality rules

```
                              Γ ⊢ t ≡ u   Γ ⊢ u ≡ v
  ──────────  (refl)          ─────────────────────  (trans)
   Γ ⊢ t ≡ t                       Γ ⊢ t ≡ v


   Γ ⊢ t ≡ u                   Γ ⊢ t ≡ u
  ───────────  (sym)         ─────────────────  (cong-app)
   Γ ⊢ u ≡ t                  Γ ⊢ s(t) ≡ s(u)


   Γ ⊢ s(x) ≡ t(x)    x ∉ FV(Γ)
  ──────────────────────────────────  (cong-abs)
   Γ ⊢ (λx:τ. s) ≡ (λx:τ. t)


  ─────────────────────────  (β)         ──────────────────  (η)
   ⊢ (λx:τ. M) N ≡ M[N/x]                ⊢ λx:τ. f x ≡ f
                                          (x ∉ FV(f))
```

[β](./00-glossary.md#β-reduction-η-conversion) and η as
*meta-equality rules*. (sym) is derivable from (refl) + (trans) +
(cong-app) but included as a primitive for ergonomics.

### 3.3 Observation

```
   authority O owns relation R    args : appropriate types : closed
  ────────────────────────────────────────────────────────────────  (observe)
                          · ⊢ O.R(args)
```

The [authority](./00-glossary.md#authority) `O` writes a fact under
its own opaque relation `R`. The conclusion is in the **empty
context** `·` — no Γ — because the observation is *atomic*. To use
it in a larger derivation, the user re-introduces it as a hypothesis
via (assume).

**Soundness.** The relation `R` is *uninterpreted* from the
framework's perspective: there is always a model where its denotation
is "everything true" (or `∅`, vacuously satisfied). So adding
observations is conservative over any interpreted theory — this is
the [safe-axiom class](./00-glossary.md#safe-axiom-class) invariant
at the observation level.

### 3.4 Store rules

```
                                  s : Store    n : Name256
 ──────────────────────────  (member-i)    ─────────────────────────  (member-r)
   framework.record(s, n)                       · ⊢ in_store(s, n)
        produces


   W : SubsetWitness(s₁, s₂)
  ───────────────────────────────────────────  (subset-i)
   · ⊢ ⋀x. in_store(s₁, x) ⟹ in_store(s₂, x)
```

The framework provides a `SubsetWitness` type whose construction
proves member-by-member that every member of `s₁` is also in `s₂`.
The result is an explicit Thm asserting the subset relation;
downstream [meaning-axioms](./00-glossary.md#meaning-axiom) about
crypto assumptions in `s₂` can be transported to `s₁` via this Thm
+ (all-e) + (imp-e).

**Downward closure** of `no_collisions` is *not* a framework
primitive — it's a derived theorem in user-space, proved once and
reused:

```
⋀h. ⋀s₁ s₂. subset(s₁, s₂)
            ⟹ no_collisions(s₂, h)
            ⟹ no_collisions(s₁, h)
```

…which the framework derives via the standard rules from the
`subset` Thm above plus the unfolding of `no_collisions`.

### 3.5 Definition rules

```
   c is a fresh ConstName    d : closed term : τ
  ─────────────────────────────────────────────────  (def)
              · ⊢ c ≡ d    (c : τ recorded)
```

Introducing a [definition](./00-glossary.md#definition) adds `c` to
the kernel's signature and emits the unfolding equation `c ≡ d` as a
Thm. Definitions are *conservative* extensions; they cannot introduce
inconsistency.

Folding (`d → c`) is derived via (sym).

---

## 4. Authorities (concise; see `03-authority.md` for depth)

```rust
pub struct AuthorityId(pub Name256);

pub struct Authority {
    id: AuthorityId,
    owned_relations: BTreeSet<RelationName>,
    kind: AuthorityKind,
}

pub enum AuthorityKind {
    Local,                       // fresh; not cross-kernel referenceable
    Keyed(PublicKey),            // cross-kernel via signature
}

impl Authority {
    pub fn fresh_local(rels: BTreeSet<RelationName>) -> Self;
    pub fn from_public_key(pk: Name256, rels: BTreeSet<RelationName>) -> Self;
}
```

The framework enforces, at the observation rule, that the
relation `R` is in `owned_relations`. Cross-authority interference is
prevented at the trust boundary.

The `check_safe_axiom` operation validates user-asserted axioms of the
form `Γ ⟹ O.R(args)` by checking that the head's authority is one
the writer owns.

---

## 5. Stores (concise; see `04-store.md` for depth)

```rust
pub struct StoreId(pub Name256);

pub struct Store {
    id: StoreId,
    members: BTreeSet<Bytes>,    // names of known members
}

impl Store {
    pub fn fresh() -> Self;
    pub fn record(&mut self, name: Bytes);
    pub fn members(&self) -> impl Iterator<Item = &Bytes>;
}
```

**Important distinction.** A framework
[Store](./00-glossary.md#store) is a *set of names*, not a *byte
backend*. The byte backend (`covalence-store`'s `BlobStore`) is
[content-addressed blob store](./00-glossary.md#content-addressed-blob-store)
— different concept, different layer. The two compose: a kernel
typically has both, with the invariant `∀n ∈ S. byte_backend.get(n)`
is defined.

This separation is what makes the SHAttered/Git-repo discussion clean:
the *byte backend* can be a Git repo containing SHA-1 oids; the
framework *Store* records "which names we've seen from that repo";
the scoped no-collision assumption is about the Store, not about
SHA-1 or Git.

---

## 6. What is NOT in the framework

These are deliberately *not* framework primitives, and must not creep
in during implementation. Each is an example of an
[oracle](./00-glossary.md#oracle) or untrusted layer that calls
*into* the framework, not the other way around.

| Not in framework                          | Lives in                                                |
|-------------------------------------------|---------------------------------------------------------|
| Hash functions (BLAKE3, SHA-256, …)        | `covalence-hash` + per-hash oracle crates               |
| Signature schemes (Ed25519, …)             | `covalence-sig` + verifier oracle crates                |
| Executors (WASM, x86, native)              | `covalence-wasm` + executor oracle crates               |
| Mount-as-Horn-clause helpers               | `covalence-mount` (planned)                             |
| Content-addressed type identity (Phase H)  | `TermHasherOracle` (planned)                            |
| HOL connectives (`∧`, `=`, `∃`, ε, …)      | `covalence-hol` (the new one)                           |
| Equality saturation / egraphs              | `covalence-egraph` (planned), as an oracle              |
| Federation protocol                        | `covalence-federation` (planned)                        |
| Serialization formats                      | `covalence-serial` (planned) or just `serde` downstream |

**β-reduction stays in the framework** as a Rust implementation
(meta-trust), per the [glossary](./00-glossary.md#β-reduction-η-conversion):
it's pure syntactic, doesn't reference any
[store](./00-glossary.md#store) or
[authority](./00-glossary.md#authority), and exposing it as
observations would be net-negative for both ergonomics and audit
clarity.

---

## 7. Proposed Rust API (interface only)

Crate layout:

```
covalence-framework/
  Cargo.toml
  src/
    lib.rs           — re-exports, crate-level docs
    error.rs         — Error enum (thiserror)
    term.rs          — TermKind, TypeKind, TermRef, TypeRef
    sequent.rs       — Prop, Thm, ContextRef
    beta.rs          — β/η-reduction (meta-trust)
    authority.rs     — Authority, AuthorityId, RelationName
    store.rs         — Store, StoreId, SubsetWitness
    elide.rs         — ElidePolicy + Thm::elide
    fresh.rs         — RNG-backed Name256 minting
    framework.rs     — the top-level Framework struct + methods
  examples/
    01_hello.rs      — derive a trivial Thm
    02_observation.rs — make an observation, discharge via meaning-axiom
    03_store.rs      — record members, prove subset, transport no-collisions
    04_define.rs     — define a constant, fold/unfold
  tests/
    inference.rs     — exhaustive rule tests
    soundness.rs     — round-trip + tampering tests
```

Top-level API sketch:

```rust
//! covalence-framework
//! Pure-style logical framework + authority + store.

pub use term::{TermKind, TypeKind, TermRef, TypeRef, VarName};
pub use sequent::{Prop, Thm, ContextRef};
pub use authority::{Authority, AuthorityId, AuthorityKind, RelationName};
pub use store::{Store, StoreId, SubsetWitness};
pub use elide::ElidePolicy;
pub use error::{Error, Result};

use covalence_rand::CovRng;

pub struct Framework {
    rng: CovRng,
    // ... internal state: signature, authority registry, term arena
}

impl Framework {
    pub fn new() -> Self;

    // ── Terms ───────────────────────────────────────────────────
    pub fn term_kind(&self, t: TermRef) -> TermKind;
    pub fn type_kind(&self, t: TypeRef) -> TypeKind;
    pub fn alloc_term(&mut self, def: TermKind) -> Result<TermRef>;
    pub fn alloc_type(&mut self, def: TypeKind) -> Result<TypeRef>;

    // ── Pure LF rules (§3.1) ────────────────────────────────────
    pub fn assume(&mut self, ctx: ContextRef, prop: TermRef) -> Thm;
    pub fn imp_intro(&mut self, hyp: TermRef, body: Thm) -> Thm;
    pub fn imp_elim(&mut self, imp: Thm, hyp: Thm) -> Result<Thm>;
    pub fn all_intro(&mut self, var: VarName, body: Thm) -> Result<Thm>;
    pub fn all_elim(&mut self, all: Thm, witness: TermRef) -> Result<Thm>;

    // ── Equality rules (§3.2) ───────────────────────────────────
    pub fn refl(&mut self, t: TermRef) -> Thm;
    pub fn trans(&mut self, ab: Thm, bc: Thm) -> Result<Thm>;
    pub fn sym(&mut self, ab: Thm) -> Result<Thm>;
    pub fn cong_app(&mut self, eq: Thm, s: TermRef) -> Result<Thm>;
    pub fn cong_abs(&mut self, eq: Thm) -> Result<Thm>;
    pub fn beta(&mut self, app: TermRef) -> Result<Thm>;
    pub fn eta(&mut self, abs: TermRef) -> Result<Thm>;

    // ── Observation (§3.3) ──────────────────────────────────────
    pub fn observe(
        &mut self,
        auth: &Authority,
        rel: RelationName,
        args: &[TermRef],
    ) -> Result<Thm>;
    pub fn check_safe_axiom(
        &self,
        ax: TermRef,
        writer: &Authority,
    ) -> Result<()>;

    // ── Stores (§3.4) ───────────────────────────────────────────
    pub fn fresh_store(&mut self) -> Store;
    pub fn record_member(&mut self, s: &mut Store, name: Bytes) -> Thm;
    pub fn prove_subset(&mut self, w: SubsetWitness) -> Result<Thm>;

    // ── Definitions (§3.5) ──────────────────────────────────────
    pub fn define(
        &mut self,
        c: ConstName,
        d: TermRef,
    ) -> Result<Thm>;

    // ── Fresh names ────────────────────────────────────────────
    pub fn fresh_name(&mut self) -> Name256;

    // ── Elision (for export; see 05-trust.md) ──────────────────
    pub fn elide(
        &mut self,
        t: Thm,
        policy: ElidePolicy,
    ) -> Result<Thm>;
}
```

**Estimated total LoC:** 600–800 (Rust), plus tests.

---

## 8. What this enables (layered above the framework)

Once the framework is shipping, the following land as **separate
untrusted crates**, each consuming the framework via its public API:

- **`covalence-hol`** (new) — classical
  [HOL](./00-glossary.md#hol-higher-order-logic) as object theory via
  (def) + axioms. Subset typedef with disjunct trick. The
  existentials. ε-choice. Primops.
- **`covalence-oracles-blake3`** — BLAKE3 hasher oracle + the three
  modes (unkeyed / keyed / derive-key) + their meaning-axiom
  templates.
- **`covalence-oracles-ed25519`** — signature verifier oracle.
- **`covalence-oracles-wasm`** — WASM evaluator oracle, wrapping
  `covalence-wasm`.
- **`covalence-mount`** — mount-as-Horn-clause helpers; safe-axiom
  builders; FS-projection.
- **`covalence-egraph`** — equality saturation as an oracle.
- **`covalence-morphism`** — the morphism layer; embeddings;
  base-shift functor.
- **`covalence-federation`** — signed Thm exchange protocol with
  [ElidePolicy](./00-glossary.md#elidepolicy).

The existing `covalence-repl`, `covalence-serve`, etc. then rebind
from the legacy kernel to this stack — but only once the layers
above are stable enough.

---

## 9. Migration from the current code

The framework crate **lands alongside** the existing
`covalence-kernel`, `covalence-hol`, and `covalence-opentheory`
crates. We do not wipe anything.

Once the framework is solid:

1. Port [`covalence-hol`'s](../../../../crates/covalence-hol) HOL Light
   rules onto the framework's API as `covalence-hol-2` (working
   title). Most of the rule logic stays the same; only the
   underlying term/equality machinery changes.
2. Port [`covalence-opentheory`'s](../../../../crates/covalence-opentheory)
   interpreter to target `covalence-hol-2` instead of
   `covalence-hol`.
3. Migrate `covalence-repl` / `covalence-serve` / etc. to bind to the
   new stack.
4. Retire `covalence-kernel` (current),
   `covalence-hol` (original), `covalence-opentheory` (original).

Each step is its own migration commit, with passing tests
end-to-end. No big-bang flip.

---

## 10. Open questions

- **η vs not?** Default: include η (Pure style). HOL Light omits
  it; including it costs nothing and simplifies definitional
  unfolding. Confirm.

- **Meta-equality `≡` vs object equality `=`.** Framework uses `≡`
  for meta-equality (Pure style). The HOL layer will add its own
  `=` as an object-level constant; they are *distinct* connectives
  with distinct rules. Confirm OK with the layering plan.

- **Whether definitions are reversible.** Default: no. Definitions
  are append-only; retracting a definition is unsound in general.
  Confirm.

- **Whether to expose `unfold` / `fold` as named primitives.**
  Default: no. They derive from the (def) Thm + (sym) + (trans) +
  (cong). No special primitive needed.

- **`SubsetWitness` representation.** A finite mapping from `s₁`'s
  member names to `s₂`'s member names, validated by the framework
  walking both stores' member sets. Proposed: `Vec<(Bytes, Bytes)>`
  plus an audit pass. Confirm before implementation.

- **Tracking [fresh](./00-glossary.md#fresh-rng-based) uniqueness
  within a session.** Framework maintains a `BTreeSet<Name256>` of
  all `fresh_name()` outputs in the current session; collisions
  panic (would indicate RNG failure). Confirm panic is acceptable
  vs. returning an error.

- **`SubsetWitness` for *infinite* subset relationships.** E.g.
  "`s₁ ⊆ s₂` because both are defined to contain all BLAKE3-hashes
  of blobs in some `s₀`." For now this is *not* in the framework;
  it lives in user-space proofs that combine
  observations + (all-i) + (imp-i). Confirm we don't need a
  schematic-subset primitive in the framework.

- **`ContextRef` representation.** A persistent list of
  Props, à la `Arc<Cons<Prop, ContextRef>>`. Cheap to extend, cheap
  to share via Arc; walking is linear. Confirm before
  implementation.

- **β/η implementation.** Use the existing β/η machinery from
  `covalence-kernel` as a reference, but rewrite cleanly against
  the new Term representation. ~150–200 LoC.

These all want concrete decisions before the crate is written.

---

## 11. Cross-references

- [`00-glossary.md`](./00-glossary.md) — vocabulary used here.
- [`01-conventions.md`](./01-conventions.md) — Name256, BLAKE3
  trichotomy, fresh, error handling, Rust idioms.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) — the big-picture
  vision; this framework realizes §1, §2.1 (syntactic
  well-formedness), §2.3 (opaque-relation discharge), §5.3–5.4
  (scoped no-collisions), and §10 (mount-as-implication via the
  safe-axiom class).
- [`prover-architecture.md`](../../../prover-architecture.md) — the
  current kernel's design. Partially superseded by this doc;
  §§1–4 are the relevant overlap.
- [`refactor-plan.md`](../../../refactor-plan.md) — the ongoing kernel
  cleanup. Phase H (content hashing) violates the framework
  separation (see §6); Phase P (egraph in kernel) is layered at
  the wrong layer (egraphs are user-space oracles).
- (Planned) [`03-authority.md`](./) — Authority + observation in
  depth.
- (Planned) [`04-store.md`](./) — Stores in depth.
- (Planned) [`05-trust.md`](./) — Meta-trust vs trust-set, ElidePolicy.

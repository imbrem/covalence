# Glossary

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This document is part of a design proposal generated during a
> planning conversation. It is **not** a committed architecture; the
> shape, vocabulary, and approach are subject to substantial revision
> before any implementation lands. For the canonical view of what is
> *actually built* vs. what is *proposed*, see
> [`where-we-are.md`](../../../where-we-are.md). For the proposal
> index, see [`README.md`](./README.md).

Vocabulary for the Covalence redesign. Every term that has a specific
meaning in our system is defined here. Where the term has a standard
meaning elsewhere (LF, HOL, etc.), the entry states the standard meaning
and then notes any Covalence-specific refinements.

**Cross-references** to other glossary entries appear as Markdown links.
**Cross-references to other docs** in this folder use the file path.

This doc is the *source of truth* for vocabulary. If a term appears in
another doc with a meaning different from the entry here, that other
doc is wrong — fix it (or update the glossary, after discussion).

---

## Contents

- [Logic and proof theory](#logic-and-proof-theory)
  - [Logical Framework (LF)](#logical-framework-lf)
  - [Pure (Isabelle/Pure)](#pure-isabellepure)
  - [HOL (Higher-Order Logic)](#hol-higher-order-logic)
  - [Sequent (Γ ⊢ φ)](#sequent-γ--φ)
  - [Proposition (Prop) / Theorem (Thm)](#proposition-prop--theorem-thm)
  - [Modus Ponens (MP)](#modus-ponens-mp)
  - [β-reduction, η-conversion](#β-reduction-η-conversion)
  - [Definition](#definition)
- [Trust and meta-trust](#trust-and-meta-trust)
  - [Trusted Computing Base (TCB)](#trusted-computing-base-tcb)
  - [Meta-trust set](#meta-trust-set)
  - [Trust set](#trust-set)
- [Authorities and observations](#authorities-and-observations)
  - [Authority](#authority)
  - [Observation](#observation)
  - [Meaning-axiom](#meaning-axiom)
  - [Safe-axiom class](#safe-axiom-class)
  - [Oracle](#oracle)
- [Names and identity](#names-and-identity)
  - [Name256](#name256)
  - [Fresh (RNG-based)](#fresh-rng-based)
  - [Authority ID / Store ID / Oracle ID](#authority-id--store-id--oracle-id)
- [Storage](#storage)
  - [Store](#store)
  - [Store membership](#store-membership)
  - [Store subset](#store-subset)
  - [Scoped no-collision](#scoped-no-collision)
  - [Content-addressed blob store](#content-addressed-blob-store)
- [Federation and elision](#federation-and-elision)
  - [Federation](#federation)
  - [PKI (Public Key Infrastructure)](#pki-public-key-infrastructure)
  - [ElidePolicy](#elidepolicy)
- [Mounts and namespaces](#mounts-and-namespaces)
  - [Mount](#mount)
  - [Namespace](#namespace)
- [Higher-level concepts (forward references)](#higher-level-concepts-forward-references)
  - [Silvered node](#silvered-node)
  - [Mirror](#mirror)
  - [Spec](#spec)
- [Cross-references to existing docs](#cross-references-to-existing-docs)

---

## Logic and proof theory

### Logical Framework (LF)

A *logical framework* is a meta-language in which other logics can be
formalized as object theories. The canonical example is Edinburgh LF
(Harper / Honsell / Plotkin); the practical one used in Covalence is
[Pure (Isabelle/Pure)](#pure-isabellepure)-style.

In Covalence, the **Framework layer**
(see [`02-framework.md`](./02-framework.md)) is an LF. It does not commit
to classical logic, to `bool`, to equality-as-equational-truth, or to
any particular inference system above its own meta-rules.
[HOL](#hol-higher-order-logic) is then an *object theory* inside the
framework.

**Standard meaning:** "LF rules" are the *meta-level* inference rules of
the framework itself. In our framework these are:

- **assume** — introduce a hypothesis into context.
- **⟹-intro / ⟹-elim** — meta-implication introduction/elimination
  ([modus ponens](#modus-ponens-mp)).
- **⋀-intro / ⋀-elim** — meta-universal introduction/elimination.
- **equality rules** — refl, trans, sym, cong-app, cong-abs.
- **[β](#β-reduction-η-conversion)** — beta-conversion as meta-equality.
- **[η](#β-reduction-η-conversion)** — eta-conversion (optional; we
  include it).

**Covalence-specific:** Our framework adds **[observation](#observation)**
as a primitive inference (introducing a fact under the writing
[authority](#authority)'s opaque relation) and **[store](#store)
membership/subset** rules. See [`02-framework.md`](./02-framework.md) §3.

### Pure (Isabelle/Pure)

The minimalist LF underlying Isabelle. Provides:

- A simply-typed term language with α/β/η-conversion.
- Two meta-connectives: `⟹` (meta-implication) and `⋀` (meta-quantifier,
  written `!!x. P x` in Isabelle ASCII).
- Meta-equality `≡` with the usual congruence rules.

Object logics (Isabelle/HOL, Isabelle/ZF) are built by introducing
object-level connectives and axioms inside this framework.

**Covalence's Framework is structurally similar to Pure** with additions
for the trust primitives ([observation](#observation),
[store](#store) operations). See
[`02-framework.md`](./02-framework.md) §2.

### HOL (Higher-Order Logic)

Classical higher-order logic with simply-typed λ-calculus + a
distinguished `bool` type + ε-choice + a `subset`-type former.
The HOL Light variant fixes a specific small kernel (10 inference rules).

**Covalence's HOL layer** is HOL Light–shaped, with one substantive
modification: the **disjunct trick** for `subset`-type formation makes
it unconditional (no inhabitation side-condition). See
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §2.4 and (planned)
[`06-hol.md`](./).

Within the Covalence layering, the HOL layer is an *object theory* in the
Framework (an [LF](#logical-framework-lf)). The kernel does **not** bake
HOL in — it builds it via [definitions](#definition) and axioms.

### Sequent (Γ ⊢ φ)

The framework's atomic judgment. A sequent `Γ ⊢ φ` asserts that under
the hypotheses `Γ` (a list of [Propositions](#proposition-prop--theorem-thm)),
the conclusion `φ` is derivable using the [LF](#logical-framework-lf)
rules.

In Covalence:

- Γ may include [observations](#observation) as hypotheses.
- φ is itself a [term](#term) of the meta-proposition kind (in our
  framework, propositions are just terms of kind `Prop`).

### Proposition (Prop) / Theorem (Thm)

A **Proposition** (`Prop`) is a candidate statement: an arena + a
context + a conclusion term. The framework can construct a Prop without
having proved it.

A **Theorem** (`Thm`) is a Prop the framework *has* derived using its
inference rules. The kernel constructs `Thm` values only via the kernel
API; `Thm` is a compile-time tag (a Rust newtype or phantom-tagged Prop).

The current `covalence-kernel` already distinguishes these; the
distinction is preserved in the Framework redesign.

### Modus Ponens (MP)

Standard rule: from `Γ ⊢ φ ⟹ ψ` and `Γ ⊢ φ` derive `Γ ⊢ ψ`. In
Pure-style LF this is the elimination rule for `⟹`. We will write
"MP" interchangeably with "⟹-elim".

### β-reduction, η-conversion

**β-reduction:** `(λx. M) N ≡ M[N/x]`. The framework treats β as
part of [meta-trust](#meta-trust-set) — it's implemented in Rust,
never exposed as an [observation](#observation). Justification: β is
a pure syntactic operation that doesn't refer to any [store](#store)
or [authority](#authority); exposing it as observations is net-negative
for both ergonomics and audit clarity.

**η-conversion:** `λx. f x ≡ f` when `x ∉ FV(f)`. We include η in
the framework by default (Pure style). Some HOL variants omit it; for
us it simplifies definitional unfolding and costs nothing.

### Definition

Introduces a fresh constant `c` together with its defining term `d`,
yielding the unfolding equation `c ≡ d` as a [Theorem](#proposition-prop--theorem-thm).
Conservative: definitions cannot introduce inconsistency.

In the Framework, `framework.define(c_name, d_term) -> Thm` adds `c`
to the signature and emits the unfolding equation.

---

## Trust and meta-trust

### Trusted Computing Base (TCB)

Standard meaning: the set of components whose correctness is *necessary*
for the system's security guarantees. A bug in the TCB can produce false
facts; a bug outside the TCB is caught by re-checking against the TCB.

**Covalence-specific:** The TCB is the **Framework crate** — the
[LF rules](#logical-framework-lf), the [authority](#authority)
bookkeeping, the [store](#store) operations. Everything else
([oracles](#oracle), executors, hash functions, signature schemes,
[mount](#mount) APIs, the HOL layer derivations, the morphism layer) is
**outside** the TCB.

See also: [meta-trust set](#meta-trust-set) — the same concept, framed
from inside the system's own description.

### Meta-trust set

Operations a kernel implementation trusts *as constitutive of its
identity* — implemented in Rust, never exposed as
[observations](#observation), with no provenance trail. Distinct from
the [trust set](#trust-set) of explicit assumptions.

The meta-trust set:

1. The [LF rules](#logical-framework-lf).
2. [Term](#term) representation operations (α-equivalence via de Bruijn,
   capture-avoiding substitution, [β/η](#β-reduction-η-conversion)).
3. [Authority](#authority) bookkeeping (who owns which relation name).
4. [Store](#store) operations (membership, subset, downward closure).
5. One pre-loaded signature scheme (Ed25519 by convention) for the
   federation I/O boundary — but structurally a regular
   [oracle](#oracle), not a framework primitive.

The meta-trust set should be **tiny**; this is the LCF discipline.
β-reduction is the canonical example: it *could* be an oracle but isn't
worth exposing, because consuming kernels who trust us already implicitly
trust our β implementation as part of trusting us as a peer.

### Trust set

[Propositions](#proposition-prop--theorem-thm) the user has assumed as
hypotheses, including:

- [Meaning-axioms](#meaning-axiom) for [oracles](#oracle).
- [Mount](#mount) edges between [authorities](#authority) or
  [stores](#store).
- "If key K signed it, it's true" assumptions for [federation](#federation)
  peers.
- User-stated axioms about object logics.

The trust set is *honest about being assumptions*: it can be doubted,
mounted under more restrictive assumptions, swapped out. The TCB never
depends on the trust set being correct — assumptions are local to a
particular derivation's context.

---

## Authorities and observations

### Authority

An entity that may [observe](#observation) facts under its own set of
opaque relation names. Authorities are framework primitives; they are
**opaque to the framework** — the framework only tracks who owns what.

Two kinds:

- **Local authority** — [fresh](#fresh-rng-based) gensym at construction.
  Cannot be referenced from another kernel instance.
- **Public-keyed authority** — identified by a public key (a
  [Name256](#name256)). Can be referenced cross-kernel via signed
  observations.

The framework enforces, at the observation rule, that the relation name
being written is in `owned_relations`. This is the
[safe-axiom class](#safe-axiom-class) invariant at the observation level.

### Observation

A single atomic fact written by an [authority](#authority). Shape:
`O.R(args)` where `O` is the authority's ID, `R` is a relation name
`O` owns, and `args` are [terms](#term) of the appropriate types.

Framework primitive: `observe(authority, relation, args) -> Thm`
produces a [theorem](#proposition-prop--theorem-thm) whose context is
empty and whose conclusion is the observation.

Observations are *opaque*: the framework attaches no interpretation.
The user gives observations meaning by writing
[meaning-axioms](#meaning-axiom).

There are **no oracle tags** in Covalence (unlike HOL Light's
`mk_thm`). A Thm doesn't carry "this was produced by oracle X" anywhere
— it just carries observations as hypotheses, which the user
discharges via meaning-axioms.

### Meaning-axiom

A user-asserted hypothesis of the form

```
∀args. O.R(args) ⟹ spec_predicate(args)
```

…that gives an [observation](#observation) its interpretation.
Without a meaning-axiom, observations are uninterpreted noise; with
one, they become evidence that something the user cares about holds.

Hash-indexed: per [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §2.3,
meaning-axioms are keyed to a specific binary/oracle identity by hash.
Under the new design, this happens **structurally** because the
[oracle ID](#authority-id--store-id--oracle-id) itself encodes the
binary (via [BLAKE3 derive-key](./01-conventions.md#the-blake3-mode-trichotomy)).

### Safe-axiom class

The framework's check for whether a user-asserted axiom is
*conservative*. An axiom `Γ ⟹ φ` is safe iff `φ` has the form
`O.R(args)` for some [authority](#authority) `O` that the writer owns.

Adding axioms in this class never makes a previously-unprovable
*interpreted* statement provable: an uninterpreted head always has a
model (denotation = "everything true", or denotation = ∅, vacuously
satisfied).

This is the [mount](#mount) rule generalized: `∀x. Q(x) ⟹ P(x)`
is safe when `P` is an oracle relation; the body `Q(x)` is unrestricted.

### Oracle

An [authority](#authority) that specifically implements a
computational or observational capability — a hasher, a WASM
evaluator, a signature verifier, an egraph engine. Oracles produce
[observations](#observation); users discharge them via
[meaning-axioms](#meaning-axiom).

The distinction between "oracle" and "authority" is **conventional**,
not formal — the framework only knows about authorities. Calling
something an oracle is shorthand for "this authority is implementing
some particular spec, with an expected meaning-axiom shape."

---

## Names and identity

### Term

A locally-nameless λ-term: de Bruijn indices for bound variables,
named [fresh](#fresh-rng-based) free variables. The framework's internal
representation is `TermDef`; users interact via the public `TermKind`
view. See [`02-framework.md`](./02-framework.md) §2.1.

### Name256

A 256-bit opaque value. Physically a `[u8; 32]`; logically refined as
needed. Used for **identities** throughout the system:

- [Authority IDs](#authority-id--store-id--oracle-id)
- [Store IDs](#authority-id--store-id--oracle-id)
- [Oracle IDs](#authority-id--store-id--oracle-id)
- Content-addressed hashes (when chosen)
- Public keys (for [federation](#federation))
- Format IDs (per [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §12)

The conventions for *how* Name256 values are derived (random, hashed,
derived from parents) are in
[`01-conventions.md`](./01-conventions.md).

### Fresh (RNG-based)

A `fresh()` operation produces a [Name256](#name256) **assumed
collision-free** with all other names *in the relevant
[store](#store)*. Implementation: cryptographically secure RNG.

By a birthday-paradox argument on 256-bit RNG outputs, the probability
of accidental collision at any practical scale (N ≤ 2^60) is below
2^-137 — negligible. We *assume* collision-freedom in the
[trust set](#trust-set) under a name like
`∀s. ∀n ∈ FreshIssued. ¬in_store(s, n)`.

See [`01-conventions.md` §Fresh names](./01-conventions.md#fresh-names)
for the full reasoning.

### Authority ID / Store ID / Oracle ID

All three are [Name256](#name256) values; they're typed wrappers around
the same `[u8; 32]`:

- `AuthorityId(Name256)` — identifies an [authority](#authority).
- `StoreId(Name256)` — identifies a [store](#store).
- `OracleId(Name256)` — identifies an [oracle](#oracle); since oracles
  are a kind of authority, `OracleId` is conventionally synonymous with
  `AuthorityId`.

How each is *derived* is per-type convention; see
[`01-conventions.md`](./01-conventions.md#oracle-id-derivation) and
(planned) [`08-oracles.md`](./).

---

## Storage

### Store

A finite, named **set of blob-names** that scopes crypto assumptions.
Framework primitive. The framework treats stores as opaque sets that
may grow over time; the user records membership facts and proves subset
relationships.

**Why stores are framework-primitive:** crypto assumptions like "no
SHA-1 collisions" are mathematically false at universe scope (the
SHAttered PDFs exist) but verifiable at scoped levels (a particular
Git repo, exhaustively). The framework *refuses* to express an
unscoped crypto assumption. See
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §5.3, §5.4 for the "global
store" framing this is built on, and (planned)
[`04-store.md`](./).

### Store membership

The framework relation `in_store(s, name)` asserts that a `name` has
been recorded as a member of [store](#store) `s`. Created by
`framework.record_member(s, n)`, which yields the Thm
`⊢ in_store(s, n)`.

### Store subset

A framework relation `subset(s₁, s₂)` asserts
`∀x. in_store(s₁, x) ⟹ in_store(s₂, x)`. Proved by furnishing a
`SubsetWitness` — a finite mapping from `s₁`'s members to
corresponding members of `s₂`, validated by the framework.

**Downward closure:** if `subset(s₁, s₂)` and
[`no_collisions(s₂, h)`](#scoped-no-collision) then
`no_collisions(s₁, h)`. The framework derives this transitively from
the subset edge.

### Scoped no-collision

For a hash function `h` (BLAKE3, SHA-256, Git-SHA-1, …) and a
[store](#store) `s`, the assumption `no_collisions(s, h)` is

```
∀x y ∈ s.  h(x) = h(y) ⟹ x = y
```

This is *verifiable* (by exhaustion if `s` is small) or *assumable*
(under collision-resistance assumptions about `h`). It is **never**
asserted unscoped.

### Content-addressed blob store

Not to be confused with [Store](#store). The
*content-addressed blob store* (`covalence-store`) is the **byte
backend** — a `name → bytes` lookup. A framework [Store](#store) is
just a *set of names*, with no commitment to where the bytes live.

The two are commonly composed: a kernel can have a Store `S` and a
content-addressed blob backend `B` such that for every `n ∈ S`, `B(n)`
is the byte content addressed by `n`.

---

## Federation and elision

### Federation

The act of one kernel instance consuming theorems produced by another.
In Covalence, federation is the **only** form of cross-instance
communication — including same-process kernels in different threads.
See (planned) [`09-federation.md`](./).

### PKI (Public Key Infrastructure)

The framework treats every "other kernel" as a public key. Cross-instance
trust is exactly the assumption "I will accept observations signed by
this key." This is uniform across:

- Threads in the same process.
- Different processes on the same machine.
- Browser ↔ server.
- WAN federation peers.

The framework has no shared-memory fast path; downstream implementations
may optimize the *implementation*, but the *interface* is
signed-blob-in / signed-blob-out everywhere.

### ElidePolicy

When exporting a [theorem](#proposition-prop--theorem-thm) to a peer,
the local kernel may strip its own local-instance
[authority](#authority) names from the conclusion, substituting
abstract spec-level identities the peer also recognizes. This is the
**honest abstraction** of "we ran *a* WASM evaluator, not specifically
*our* instance."

The Framework's `ElidePolicy` is **explicit and per-export**: the
caller specifies what to elide. Silent elision is forbidden — that
would be a global lie at the namespace layer.

See (planned) [`05-trust.md`](./).

---

## Mounts and namespaces

### Mount

A conservative implication `∀x. Q(x) ⟹ P(x)` connecting two
[authority](#authority) namespaces. Sound for free because `P` is an
oracle relation (an uninterpreted head always has a model). The body
`Q` is unrestricted.

In FS projection (planned), mounts are literally directories that
"look up" in two namespaces at once. See
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §10.2.

### Namespace

A prefix-indexed family of relations. Operationally: an
[authority](#authority) together with the set of relation names it
owns. `enter` (currying) and `mount` (extension under a fresh prefix)
are the only two combinators; union is the only associative.

---

## Higher-level concepts (forward references)

### Silvered node

A node in the [logic-graph / mirror-graph](#mirror) whose trust is
established by **direct human inspection** — the endpoint of trust
propagation along edges. See
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §4.

### Mirror

An independent path to the same conclusion. Confidence in a result
comes from *agreement* between mirrors, not from any single one being
authoritative. See [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §4.

### Spec

A structured document describing an [oracle](#oracle)'s identity,
relations, sub-oracle derivation scheme, and suggested
[meaning-axioms](#meaning-axiom). A spec is itself a content-addressed
artifact (a blob with a [Name256](#name256)). Specs are the unit of
*cross-kernel agreement* — two engines reading the same spec text
derive the same [oracle ID](#authority-id--store-id--oracle-id) and
sub-oracle names. See (planned) [`08-oracles.md`](./).

---

## Cross-references to existing docs

Most concepts here are present (sometimes under different names) in
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) v2. The mapping:

| Glossary term                                 | ARCHITECTURE.md section                                 |
|-----------------------------------------------|---------------------------------------------------------|
| [LF](#logical-framework-lf)                   | §1, §3 (the "base")                                     |
| [Meta-trust set](#meta-trust-set)             | §1 (TCB), §13                                           |
| [Authority](#authority)                       | §2.3 (opaque relations); §6 (concepts)                  |
| [Observation](#observation)                   | §2.3, §9 (evidence corner)                              |
| [Meaning-axiom](#meaning-axiom)               | §2.3                                                    |
| [Mount](#mount)                               | §10.2                                                   |
| [Store](#store)                               | §11, §5.3, §5.4 (global store)                          |
| [Scoped no-collision](#scoped-no-collision)   | §5.3 (SHAttered example), §5.4                          |
| [Silvered node](#silvered-node)               | §4                                                      |
| [Mirror](#mirror)                             | §4                                                      |
| [Name256](#name256)                           | §12.1                                                   |
| BLAKE3 trichotomy (see `01-conventions.md`)   | §12 (format plane), refined in this redesign            |
| [Federation](#federation) / [PKI](#pki-public-key-infrastructure) | §10.2 (two-layer import), §6 |
| [ElidePolicy](#elidepolicy)                   | implicit in §10.2                                       |

The legacy docs [`MVP_DESIGN.md`](../../../../MVP_DESIGN.md) and
[`DESIGN.md`](../../../../DESIGN.md) predate most of this vocabulary; use
[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) as the reference for any
term that appears in legacy docs and is not in this glossary.

# Authorities and Observations

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This document is part of a design proposal generated during a
> planning conversation. It is **not** a committed architecture; the
> shape, vocabulary, and approach are subject to substantial revision
> before any implementation lands. For the canonical view of what is
> *actually built* vs. what is *proposed*, see
> [`where-we-are.md`](../../../where-we-are.md). For the proposal
> index, see [`README.md`](./README.md).

The framework's **single trust primitive**.
[Authorities](./00-glossary.md#authority) own opaque relations;
[observations](./00-glossary.md#observation) write facts under those
relations; [meaning-axioms](./00-glossary.md#meaning-axiom) give
observations their interpretation. There are **no oracle tags** —
trust is recorded as ordinary hypotheses in the
[trust set](./00-glossary.md#trust-set), not as a side-channel
attached to [Thms](./00-glossary.md#proposition-prop--theorem-thm).

This doc expands on [`02-framework.md`](./02-framework.md) §3.3
(the observation inference rule) and §4 (the Authority struct). It is
the deepest dive on the framework's trust boundary.

**Prerequisites:** [`00-glossary.md`](./00-glossary.md) (vocabulary),
[`01-conventions.md`](./01-conventions.md) §1 (Name256), §4 (oracle
ID derivation).

---

## Contents

1. [What an Authority is](#1-what-an-authority-is)
2. [The two kinds: Local vs Keyed](#2-the-two-kinds-local-vs-keyed)
3. [RelationName: per-authority opaque labels](#3-relationname-per-authority-opaque-labels)
4. [Observation: the primitive in detail](#4-observation-the-primitive-in-detail)
5. [Safe-axiom class checking](#5-safe-axiom-class-checking)
6. [Meaning-axioms in detail](#6-meaning-axioms-in-detail)
7. [Sub-authorities (deriving child authorities)](#7-sub-authorities-deriving-child-authorities)
8. [Authority lifecycle](#8-authority-lifecycle)
9. [Mount-as-authority-bridge](#9-mount-as-authority-bridge)
10. [Worked examples](#10-worked-examples)
11. [The "no oracle tags" property, formally](#11-the-no-oracle-tags-property-formally)
12. [Open questions](#12-open-questions)
13. [Cross-references](#13-cross-references)

---

## 1. What an Authority is

An **Authority** is an entity that may write atomic facts under a set
of opaque relation names that *it owns*. The framework treats an
authority as a [Name256](./00-glossary.md#name256) identity plus a
declared set of [RelationName](#3-relationname-per-authority-opaque-labels)
strings; it has no idea what the authority *does* — it only enforces
that the authority writes within its lane.

Rust shape:

```rust
pub struct AuthorityId(pub Name256);
pub struct RelationName(pub SmolStr);

pub struct Authority {
    id: AuthorityId,
    owned_relations: BTreeSet<RelationName>,
    kind: AuthorityKind,
    // implementation detail: capability token proving the caller can
    // act as this authority (gensym handle for Local; verified signature
    // for Keyed; an opaque cap for sub-authorities — see §7).
}
```

The framework's role at the [observation](./00-glossary.md#observation)
rule (see [§4](#4-observation-the-primitive-in-detail)) is exactly to
check that `relation ∈ authority.owned_relations` and that the caller
is acting as `authority`.

**Two reads of "what an Authority is":**

- **Mechanically:** an Authority is a typed capability + a relation
  whitelist. Owning the capability lets you create
  [Theorems](./00-glossary.md#proposition-prop--theorem-thm) whose
  conclusions are `authority.relation(args)`.
- **Conceptually:** an Authority is a *named actor* — a hash function,
  a WASM evaluator, a peer kernel, a signature verifier, a human
  oracle — whose observations the user has decided to interpret via
  [meaning-axioms](#6-meaning-axioms-in-detail).

The two reads stay separate: the framework only sees the mechanical
form. The conceptual layer lives in user-space documentation
([specs](./00-glossary.md#spec)) and in the
[trust set](./00-glossary.md#trust-set).

---

## 2. The two kinds: Local vs Keyed

```rust
pub enum AuthorityKind {
    Local,                          // gensym; not cross-kernel referenceable
    Keyed(PublicKey),               // identified by public key; signed observations
}
```

### Local authorities

Created by `Authority::fresh_local(relations)`. Their
[AuthorityId](./00-glossary.md#authority-id--store-id--oracle-id) is a
[fresh](./00-glossary.md#fresh-rng-based) 32-byte RNG output. The
authority exists only within the current kernel instance — its
identity is not externally meaningful.

Use for:

- Your own kernel's "actual" hash function instance — the gensym is
  `MyKernel_Blake3_Process47_Instance3` in spirit, but as 32 random
  bytes in form.
- Process-local sub-authorities derived from a parent (see
  [§7](#7-sub-authorities-deriving-child-authorities)).
- Anything that shouldn't be cited cross-kernel by direct name.

Observations under a local authority **cannot be serialized for export
to a peer**: there is no way for the peer to refer to the local
authority's gensym ID. Use [ElidePolicy](./00-glossary.md#elidepolicy)
([`05-trust.md`](./05-trust.md)) to substitute a public-keyed or
well-known authority before export.

### Keyed authorities

Created by `Authority::from_public_key(pk, relations)`. Their
[AuthorityId](./00-glossary.md#authority-id--store-id--oracle-id) *is*
the public key (a [Name256](./00-glossary.md#name256)).

Use for:

- Federation peers — the other kernel's public key.
- Well-known oracle specs — the authority ID derived as
  `BLAKE3::derive_key("covalence-oracle-spec-v1", spec_bytes)` (see
  [01-conventions.md §4](./01-conventions.md#4-oracle-id-derivation)).
  Strictly speaking these aren't "public-key-backed" in the
  signature-verification sense; they're identity-backed by content.
  The same `AuthorityKind::Keyed` slot holds both — the framework
  doesn't care, only the federation layer does.
- Long-lived authorities that other kernels need to refer to.

The capability to *act as* a keyed authority is held by whoever
controls the corresponding private key (for signature-backed) or by
whoever can produce observations the framework accepts under that
ID (for spec-backed local instances). The chicken-and-egg is resolved
by [05-trust.md](./05-trust.md) (the meta-trust pre-load of a
signature verifier).

---

## 3. RelationName: per-authority opaque labels

A [RelationName](./00-glossary.md#authority) is a short string scoped
to its owning authority. Within one authority, relation names must be
unique; across authorities, they can repeat without conflict (because
the relation is implicitly *qualified* by the authority).

Why short strings rather than [Name256](./00-glossary.md#name256)?

- Relation names live *inside* an authority's namespace; they don't
  need global uniqueness.
- Spec documents are easier to read with `"eval"`, `"hashed"`,
  `"verifies"` than with 64 hex chars.
- The qualified relation `authority.eval` is globally unique because
  `authority` is a 256-bit identity; the relation name only needs
  per-authority uniqueness.

Encoding: `SmolStr` (small-string optimization, common in `covalence-*`
crates). Length cap: 64 bytes by convention; longer relation names
trigger a kernel warning. (Decision pending — see
[§12 Open questions](#12-open-questions).)

**Reserved relation names** (the framework recognizes these):

- `in_store(name)` — see [`04-store.md`](./04-store.md). Owned
  conceptually by "the framework itself" (every Store is implicitly
  the authority over `in_store(self_id, _)`).

No other names are reserved at framework level. HOL connectives,
hash predicates, signature predicates — all of those are oracle
relations, named by the oracle's spec.

---

## 4. Observation: the primitive in detail

### 4.1 The inference rule (restated)

```
   authority O owns relation R    args : closed terms : matching arity/types
  ────────────────────────────────────────────────────────────────────────  (observe)
                          · ⊢ O.R(args)
```

The conclusion is in the **empty context**: no Γ.

### 4.2 What "matching arity/types" means

Each [RelationName](#3-relationname-per-authority-opaque-labels) `R`
within an authority `O` has a fixed signature:

```rust
pub struct RelationSig {
    pub arg_types: Vec<TypeRef>,
}
```

declared at the time `O` is created (or when `R` is added to `O`'s
namespace). Calls to `observe(O, R, args)` are rejected if
`args.len() != R.arg_types.len()` or if any `args[i]` has the wrong
type (where "wrong type" means: structurally inequal to
`R.arg_types[i]`).

The type check is *structural*: the framework walks both types and
matches their `TypeKind` views. There is no UF / no unification at
the type level (consistent with
[`prover-architecture.md`](../../../prover-architecture.md) §2.2 "Types
have no union-find").

### 4.3 Why args must be closed

A closed term has no free variables — it is fully ground. The
observation `O.R(args)` is supposed to be an *atomic fact* about the
specific arguments; allowing open args would mean facts contain
"placeholders" that interact with binding contexts in unexpected
ways.

This matches [`prover-architecture.md`](../../../prover-architecture.md)
§3.3's closed-term discipline at the union-find boundary.

To observe something universal (`∀x. O.R(x)`), the caller must
generate observations one ground instance at a time and combine via
([⋀-intro](./02-framework.md#31-pure-lf-rules)) at the user level.
The framework does not let an oracle write quantified facts directly.

### 4.4 Soundness

The relation `R` is *uninterpreted* from the framework's perspective:
there is always a model `M` in which `O.R^M` is "everything" (or
`∅`, vacuously satisfied). Adding `O.R(args)` as a fact does not
contradict any model — it just restricts the class of models we're
willing to consider.

This is the [safe-axiom class](#5-safe-axiom-class-checking)
invariant at the observation level. The user's
[meaning-axioms](#6-meaning-axioms-in-detail) further restrict the
model class; trust flows in that direction.

### 4.5 The atomic-fact discipline

Each observation is a *single* atomic fact. If a WASM evaluator
"observes" that on input `i`, binary `B`'s outputs were `o₁` and
`o₂` (nondeterministically), those are *two* observations:

```
WASMRun(B).eval(i, o₁)
WASMRun(B).eval(i, o₂)
```

…not one observation with a list-valued output. The framework
doesn't disallow list-typed args (a relation could be `eval(input,
list-of-outputs)`), but the convention is one observation = one fact.

---

## 5. Safe-axiom class checking

### 5.1 What it checks

The framework provides `Framework::check_safe_axiom(ax, writer)` to
validate that a user-asserted axiom is in the
[safe-axiom class](./00-glossary.md#safe-axiom-class):

```
ax : Γ ⟹ O.R(args)   where O is owned by `writer`
```

i.e., the conclusion (head) of the axiom must be an observation under
an authority the asserting party owns. The body Γ is unrestricted.

### 5.2 Why this is conservative

An axiom of this form adds the implication "if Γ then `O.R(args)`"
to the trust set. Since `O.R(args)` is an uninterpreted relation
(see [§4.4](#44-soundness)), there is always a model where the axiom
is vacuously satisfied (by making `O.R^M` true for everything
satisfying Γ — which is at least possible since `O.R` is otherwise
unconstrained).

Therefore: adding such axioms cannot make a previously-unprovable
*interpreted* statement provable. The axiom is **conservative** over
the interpreted theory.

### 5.3 Why "the head must be owned" matters

If the head were *any* uninterpreted relation — including one owned
by *another* authority — the asserter could effectively forge
observations on behalf of others. The "you can only write to your
own relation namespace" rule preserves the
[trust corner](./00-glossary.md#observation) separation:
"observation = fact = evidence" depends on each authority controlling
its own evidence stream.

### 5.4 The check's implementation

```rust
fn check_safe_axiom(&self, ax: TermRef, writer: &Authority)
    -> Result<(), AxiomError>
{
    let head = ax.peel_meta_implications().head();
    match head.kind() {
        TermKind::App(rel_app, _) => {
            let (auth_id, rel_name) = extract_authority_relation(rel_app)?;
            if auth_id != writer.id { Err(AxiomError::WrongAuthority) }
            else if !writer.owned_relations.contains(&rel_name) {
                Err(AxiomError::UnownedRelation)
            }
            else { Ok(()) }
        }
        _ => Err(AxiomError::NotAnObservation),
    }
}
```

The check is purely syntactic — no provability inspection. This
matches the
[syntactic well-formedness invariant](../../../../ARCHITECTURE.md#21-the-overriding-invariant)
from `ARCHITECTURE.md` §2.1.

---

## 6. Meaning-axioms in detail

### 6.1 The typical shape

A [meaning-axiom](./00-glossary.md#meaning-axiom) is a user-asserted
hypothesis of the form

```
⋀args. O.R(args) ⟹ spec_predicate(args)
```

…where `spec_predicate` is some user-defined relation (an
HOL-layer connective, or another oracle's relation, or an interpreted
property in some logic).

It is **not** in the safe-axiom class — the head is
`spec_predicate(args)`, not `O.R(args)`. So adding a meaning-axiom is
**not** automatically conservative; the user is opting into trusting
that the oracle's observations *really do* satisfy the spec.

### 6.2 Hash-indexing via authority ID

Per [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §2.3, meaning-axioms
must be keyed to a specific binary/oracle by hash, *not* by name. In
the new design, this happens **structurally**:

```
⋀i o. WASMRun(H_B).eval(i, o) ⟹ wasm_spec_eval(H_B, i, o)
```

The constant `WASMRun(H_B)` is the
[AuthorityId](./00-glossary.md#authority-id--store-id--oracle-id) of
the sub-authority for binary `H_B`. It is a literal 256-bit constant
in the term language. Instantiating this axiom against a *different*
binary `H_B'` would require a different authority `WASMRun(H_B')`,
which is a different 256-bit literal — the axiom literally cannot
apply.

This recovers the §2.3 invariant ("impossible to apply to a different
binary") for free, with no special "binary-hash" arg in the relation.

### 6.3 How meaning-axioms produce useful Thms

Given:

- An observation: `· ⊢ O.R(a)` (from the `observe` rule).
- A meaning-axiom in the trust set: `⊢ ⋀x. O.R(x) ⟹ S(x)`.

The user derives `· ⊢ S(a)` by:

1. (⋀-elim) on the axiom with witness `a` → `· ⊢ O.R(a) ⟹ S(a)`.
2. (⟹-elim / MP) with the observation → `· ⊢ S(a)`.

The observation has been *promoted* to a statement about the spec
property `S`. This is how oracle observations become useful facts.

### 6.4 Conservativity vs trust

Meaning-axioms are *not* conservative: they meaningfully add
restrictions on the model class. The user is *making a claim* —
"my WASM oracle satisfies the WASM spec" — and the framework
records this claim as a hypothesis. If the claim is wrong, downstream
Thms are unsound.

This is **correct, not a flaw**. The point of the system is to make
trust *explicit*. The framework's job is to ensure that:

- Meaning-axioms appear in the [trust set](./00-glossary.md#trust-set)
  of every Thm derived using them.
- The trust set is honestly preserved through serialization, mount,
  and federation.

The user inspects the trust set to see what's actually being
assumed.

---

## 7. Sub-authorities (deriving child authorities)

### 7.1 The derivation primitive

Given a parent authority `O` and some context (a binary hash, a
session nonce, etc.), the user can derive a sub-authority `O'`:

```rust
let parent = Authority::from_public_key(WASM_EVALUATOR_UUID, ...);
let child = parent.derive_sub(
    scheme: "binary",
    payload: &binary_hash.as_bytes(),
    relations: btreeset!{RelationName("eval")},
);
```

The child's ID is computed by the
[recommended convention](./01-conventions.md#4-oracle-id-derivation):

```
child.id = BLAKE3::derive_key(
    "covalence-suboracle-v1",
    parent.id || scheme || 0u8 || payload
)
```

The framework checks that `scheme` is in the parent's *declared
sub-authority schemes* (part of the parent's spec).

### 7.2 What sub-authorities buy

- **Hierarchical namespaces.** `WASMEvaluatorUUID` is the
  "general WASM evaluator"; `WASMRun(H_B)` is "the WASM evaluator
  running binary `H_B`". Their identities are related by the
  derivation, but they're distinct authorities.

- **Cross-kernel agreement.** Two kernels with the same parent
  authority spec and the same binary hash derive the same child
  authority ID *deterministically*. Cross-kernel observation
  comparison falls out for free.

- **Meaning-axiom precision.** The meaning-axiom for `WASMRun(H_B)`
  applies *only* to observations under that exact ID; a different
  binary or a different parent gives a different ID and the axiom
  can't be instantiated.

### 7.3 Sub-authority lifecycle

Sub-authorities inherit their parent's
[kind](#2-the-two-kinds-local-vs-keyed): a sub-authority of a Local
parent is Local; a sub-authority of a Keyed parent is Keyed (with
the child's "public key" being the derived hash, conceptually a
self-binding pseudo-pubkey).

The capability to *act as* a sub-authority is held by:

- Whoever holds the parent's capability (parents can speak as their
  children).
- Whoever is granted the child capability explicitly.

The framework does not enforce a permissioning model beyond
"to observe under authority `O`, you need an `Authority` value with
`O`'s ID." How `Authority` values are minted and shared is
user-space concern.

---

## 8. Authority lifecycle

### 8.1 Creation

- `Authority::fresh_local(rels)` — gensym ID, Local kind.
- `Authority::from_public_key(pk, rels)` — pk ID, Keyed kind.
- `parent.derive_sub(scheme, payload, rels)` — derived ID,
  inherited kind.

All creation is local: the kernel doesn't "publish" authority IDs
anywhere. Sharing happens via [spec documents](./00-glossary.md#spec)
out-of-band.

### 8.2 Use

Each call to `framework.observe(&auth, rel, args)` consumes the
`Authority` value by reference. The framework checks `rel ∈
auth.owned_relations` and writes the observation Thm.

### 8.3 No retirement

Authorities are **never retired** within a session. An observation
once made is a Thm that may be referenced later; retiring the
authority retroactively would invalidate that Thm.

If an authority's meaning-axiom is *withdrawn* (the user no longer
trusts it), the Thms that depended on it still exist — they just
have an open assumption in their trust set that nobody discharges.
This is *honest*: previously-derived Thms aren't retroactively
forged, just unmoored.

### 8.4 Across sessions

Authority IDs persist (they're 256-bit constants). A Local authority
from yesterday's session is *gone* if not re-imported via
serialization. A Keyed authority can be reconstructed by re-supplying
the public key + relations + spec.

A Local authority's observations cannot survive into a new session
without being elided to a Keyed authority first (see
[`05-trust.md`](./05-trust.md)).

---

## 9. Mount-as-authority-bridge

A [mount](./00-glossary.md#mount) `mount Q at P` is the assertion

```
⋀x. Q(x) ⟹ P(x)
```

where `P` is an oracle relation. This is **in the safe-axiom class**
(see [§5.3](#53-why-the-head-must-be-owned-matters)) because the head
`P(x)` is an oracle relation owned by *some* authority.

So a mount is **literally a meaning-axiom whose body is another
authority's relation**. The two-layer namespace import
([`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §10.2) is:

1. **Signature/identity fact** (evidence): "key K signed Thm T"
   — an observation by an Ed25519 verifier authority.
2. **Translation** (logic): "K's authority is mounted at our
   abstract spec authority" — a mount edge / meaning-axiom in the
   safe class.

Keep these distinct: fusing them re-welds the
[evidence and proof corners](./00-glossary.md#observation) of the
trinity.

---

## 10. Worked examples

### 10.1 WASM evaluator oracle

**Spec.** `WASMEvaluatorUUID = BLAKE3::derive_key(
  "covalence-oracle-spec-v1", wasm_spec_text_v1)`.

**Relations owned at the root:**

- `binary_well_formed(binary_hash : Name256)` — the binary is a valid
  WASM module.

**Sub-authority scheme:** `"binary"`, payload is the binary's
content hash. Derived authority `WASMRun(H_B)` owns:

- `eval(input : Bytes, output : Bytes)` — running `H_B` on input
  produced output.

**Local instance.** The kernel mints a Local sub-authority of itself
(`MyKernel_WASM_Local`) for the actual WASM process. When the kernel
runs `H_B` on input `i` and observes output `o`, it issues:

```
observation:  MyKernel_WASM_Local.eval(i, o)
```

…and *separately* makes a meaning-axiom assertion:

```
mount-edge:  ⋀i o. MyKernel_WASM_Local.eval(i, o)
                ⟹ WASMRun(H_B).eval(i, o)
```

This is in the safe-axiom class (head is a `WASMRun(H_B)` relation;
owner is the spec authority; the *body* mentions
`MyKernel_WASM_Local`, which is fine).

**At export time:** the kernel uses
[ElidePolicy::SubstituteSpec](./05-trust.md) to replace
`MyKernel_WASM_Local` with `WASMRun(H_B)` in exported Thms, citing
the mount-edge as rationale.

### 10.2 BLAKE3 hasher oracle

**Spec.** `BLAKE3HasherUUID = BLAKE3::derive_key(
  "covalence-oracle-spec-v1", blake3_spec_text)`.

**Sub-authority scheme:** `"mode"` (unkeyed / keyed / derive-key).
Derived authorities like `BLAKE3HasherUUID_Unkeyed`,
`BLAKE3HasherUUID_Keyed`, etc.

**Relations:**

- `hashed(blob_name : Name256, digest : Name256)` — the blob with
  this name has this hash digest.

**Meaning-axiom (user-supplied):**

```
⋀b h.  BLAKE3HasherUUID_Unkeyed.hashed(b, h)
   ⟹ BLAKE3_unkeyed_digest(get_bytes(b)) == h
```

This is a *meaning-axiom* (not in the safe class): the head is the
interpreted predicate `BLAKE3_unkeyed_digest(...) == h`. The user
asserts that the hasher really computes BLAKE3.

### 10.3 Ed25519 signature verifier oracle

**Spec.** `Ed25519VerifierUUID = BLAKE3::derive_key(
  "covalence-oracle-spec-v1", ed25519_spec_text)`.

**Relations:**

- `verifies(public_key : Name256, msg : Bytes, sig : Bytes)` —
  the signature is valid for this message under this key.

**Meaning-axiom (typically pre-loaded as part of meta-trust
convention):**

```
⋀pk m s. Ed25519VerifierUUID.verifies(pk, m, s)
   ⟹ ed25519_spec_verifies(pk, m, s)
```

Where `ed25519_spec_verifies` is the *intended interpretation* of
Ed25519 verification. The user trusts that the implementation matches
the spec; this is one of the few meaning-axioms commonly elevated to
[meta-trust convention](./05-trust.md).

---

## 11. The "no oracle tags" property, formally

Standard LCF kernels (HOL Light, OpenTheory) carry an *oracle tag*
on each Thm: a set of strings recording which "external oracles"
contributed to the proof. The tag is checked at point of use to
decide whether to trust the Thm.

Covalence **does not have oracle tags**. The formal statement:

> **No-Oracle-Tags Invariant.** For every Thm `t : Γ ⊢ φ` produced
> by the framework, every fact that contributed to `t` is either
> derivable from the LF rules alone or appears explicitly in `Γ`.
> The framework attaches *no* metadata to `t` beyond `Γ` and `φ`.

This is what makes the system *honest* about oracle use:

- You can't introduce a "trusted-because-from-oracle-X" Thm into
  proof and have downstream Thms silently inherit the trust.
- Every oracle's contribution appears as a hypothesis in some
  predecessor's context.
- Stripping or mishandling the context is impossible without
  rewriting the trust set — which the framework rejects.

**Corollary.** The standard pattern "the kernel has a sealed Thm
type plus oracle tags" is replaced by "the kernel has a sealed Thm
type plus an explicit trust set in `Γ`". The trust set is *in the
Thm*, not beside it.

This is also why [ElidePolicy](./00-glossary.md#elidepolicy) is
explicit and per-export ([`05-trust.md`](./05-trust.md)): silently
"removing" trust assumptions at export would be the equivalent of
silently changing oracle tags, which we forbid.

---

## 12. Open questions

- **RelationName length cap.** Proposed: 64 bytes (SmolStr inline
  capacity). Reject longer names at construction. Confirm.

- **Reserved relation names.** Proposed: only `in_store`. Are there
  others the framework should reserve (e.g., for definitions, for
  mount edges)? Probably not — definitions emit term-equality Thms,
  not relations.

- **`RelationSig` storage.** Where do relation signatures live? Two
  options: (a) inside the `Authority` struct (one signature table per
  authority); (b) globally in the framework, keyed by `(AuthorityId,
  RelationName)`. Default: (a), for locality.

- **Type-polymorphic relations.** Can a relation have type-variable
  args (e.g., `O.R(x : α)` for any `α`)? Or are relation signatures
  always type-concrete? Default: concrete only; polymorphism happens
  at the meaning-axiom level by quantifying types in user-space.

- **Authority value semantics.** Is `Authority` `Clone`? If two parts
  of user code hold separate `Authority` values referring to the
  same ID, are they the same authority? Default: `Clone` is allowed;
  identity is by `AuthorityId`.

- **Capability proof for keyed authorities.** When constructing an
  `Authority::from_public_key(pk, ...)`, does the framework require a
  proof that the caller controls the private key? Default: **no**.
  Anyone can construct an `Authority` value with a given public key;
  whether observations under that key get *believed by peers* is a
  federation question, not a framework question.

  This is consistent with the no-oracle-tags principle: the framework
  doesn't check provenance, it just records what happened.

- **Sub-authority capability inheritance.** Does
  `parent.derive_sub(...)` require the caller to *also* hold the
  parent's capability? Default: yes — sub-authority derivation is
  conceptually "the parent speaking on behalf of a sub-namespace,"
  so the caller must be able to speak as the parent.

- **Concurrent observation.** If two threads share an `Authority` and
  both call `observe()` concurrently, does the framework serialize?
  Default: yes, via interior `Mutex` on the framework state. Each
  observation is atomic.

---

## 13. Cross-references

- [`00-glossary.md`](./00-glossary.md) — vocabulary used here.
- [`01-conventions.md`](./01-conventions.md) §1, §4 — Name256
  conventions and oracle-ID derivation.
- [`02-framework.md`](./02-framework.md) §3.3, §4 — the observation
  inference rule and the Authority API.
- [`04-store.md`](./04-store.md) — stores, the other framework
  primitive. Stores have a *bookkeeping* relationship with authorities
  (the framework owns `in_store(s, _)`), but they are not authorities.
- [`05-trust.md`](./05-trust.md) — meta-trust vs trust-set,
  ElidePolicy. Where the discussion of "how authorities are exported
  to peers" lives.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §2.3 — opaque-relation
  discharge (the original framing).
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §10.2 — mount-as-Horn
  clause, the two-layer import distinction.
- [`prover-architecture.md`](../../../prover-architecture.md) §6 (concepts)
  — current kernel's concept system, the predecessor to authorities.
  Mostly superseded; the safe-axiom class survives.
- (Planned) [`08-oracles.md`](./) — oracle conventions, spec format,
  worked oracle implementations.
- (Planned) [`09-federation.md`](./) — signed Thm exchange and the
  PKI-as-universal-substrate model.

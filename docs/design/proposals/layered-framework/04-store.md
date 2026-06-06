# Stores

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This document is part of a design proposal generated during a
> planning conversation. It is **not** a committed architecture; the
> shape, vocabulary, and approach are subject to substantial revision
> before any implementation lands. For the canonical view of what is
> *actually built* vs. what is *proposed*, see
> [`where-we-are.md`](../../../where-we-are.md). For the proposal
> index, see [`README.md`](./README.md).

Stores are the framework's primitive for **scoping crypto
assumptions**. A [Store](./00-glossary.md#store) is a finite, named set
of blob-names; the framework records what has been observed in a store
and tracks subset relationships between stores. Crypto assumptions
(e.g., "no SHA-1 collisions") are *always* asserted relative to a
particular store — never universally.

This doc expands on [`02-framework.md`](./02-framework.md) §3.4 (the
store inference rules) and §5 (the Store struct). It explains why
stores are framework-primitive rather than oracle-mediated, and walks
through the worked examples (SHAttered, the Git-repo demo).

**Prerequisites:** [`00-glossary.md`](./00-glossary.md) (vocabulary),
[`02-framework.md`](./02-framework.md) (the framework as a whole),
[`03-authority.md`](./03-authority.md) (for context — stores are
*not* authorities, but they coexist).

---

## Contents

1. [What a Store is](#1-what-a-store-is)
2. [Store vs content-addressed blob store](#2-store-vs-content-addressed-blob-store)
3. [Why Stores are framework-primitive](#3-why-stores-are-framework-primitive)
4. [Store membership](#4-store-membership)
5. [Store subset and SubsetWitness](#5-store-subset-and-subsetwitness)
6. [Downward closure (derived theorem)](#6-downward-closure-derived-theorem)
7. [The global-store framing](#7-the-global-store-framing)
8. [Worked example: SHAttered](#8-worked-example-shattered)
9. [Worked example: Git-repo demo](#9-worked-example-git-repo-demo)
10. [Stores and authorities (relationship)](#10-stores-and-authorities-relationship)
11. [Store growth, freezing, and serialization](#11-store-growth-freezing-and-serialization)
12. [Multi-store reasoning](#12-multi-store-reasoning)
13. [Open questions](#13-open-questions)
14. [Cross-references](#14-cross-references)

---

## 1. What a Store is

A **[Store](./00-glossary.md#store)** is:

- A finite **set of blob-names** (each name is opaque bytes, often a
  [Name256](./00-glossary.md#name256), but not required to be —
  external systems contribute names of various widths and we wrap them
  by hashing or by adopting them as-is).
- A 256-bit [StoreId](./00-glossary.md#authority-id--store-id--oracle-id),
  [fresh](./00-glossary.md#fresh-rng-based) at construction.
- The accumulated record of *which names we've actually observed* as
  belonging to this store, across the lifetime of the kernel's view.

Rust shape:

```rust
pub struct StoreId(pub Name256);

pub struct Store {
    id: StoreId,
    members: BTreeSet<Bytes>,  // names of recorded members
}

impl Store {
    pub fn fresh() -> Self;
    pub fn record(&mut self, name: Bytes);       // mutates
    pub fn members(&self) -> impl Iterator<Item = &Bytes>;
    pub fn id(&self) -> StoreId;
}
```

The Store's *members* set is mutable: a Store grows as the kernel
observes more blob-names belonging to it. But each `record()` call
also emits a Theorem `⊢ in_store(s, name)` that is **immutable** and
remains valid even if the store later grows further.

A Store does **not** know anything about the *byte contents* of its
members — only their *names*. The byte content lives in a
[content-addressed blob store](#2-store-vs-content-addressed-blob-store)
(or wherever), looked up by name via an
[oracle](./00-glossary.md#oracle).

---

## 2. Store vs content-addressed blob store

This distinction is **critical** and easy to confuse.

| Concept                                 | What it is                              | Where it lives          |
|----------------------------------------|------------------------------------------|--------------------------|
| **Store** (framework primitive)         | A *set of names* + membership facts     | `covalence-framework`    |
| **Content-addressed blob store**        | A *name → bytes* lookup                  | `covalence-store` etc.   |

A framework Store is *purely a set of names*. There is no byte
content inside it. The membership relation `in_store(s, n)` asserts
"`n` has been recorded as a member of `s`" — nothing about what
bytes `n` names.

A byte backend (e.g., `BlobStore` from
[`covalence-store`](../../../../crates/covalence-store)) is *separately* an
[oracle](./00-glossary.md#oracle) that observes facts like

```
BlobLookupOracle.has_bytes(name, bytes_hash)
```

…with a meaning-axiom interpreting this as "the bytes addressed by
`name` hash to `bytes_hash`."

**Why split this way:**

1. **Crypto assumptions scope to *what we've seen*, not to the byte
   backend.** "No SHA-1 collisions in this repo" is about the names
   we've observed, not about the storage technology. Multiple
   byte-backends could co-exist (an in-memory one, a SQLite-backed
   one, a remote HTTP one); the framework's Store concept is
   indifferent.

2. **Re-hashing is a separate operation.** When we observe a Git
   commit (a SHA-1 oid) and *also* its BLAKE3 re-hash, both names go
   in the same logical store — but to the framework, the store just
   has two names whose relationship is recorded by oracle
   observations (not by store internals).

3. **The framework's TCB stays small.** Byte lookup is potentially
   complex (caching, network, error recovery); none of that needs to
   be in the trust boundary. The framework just sees the *names that
   appeared*.

---

## 3. Why Stores are framework-primitive

The honest cryptographic assumption is never:

> ❌ "SHA-1 has no collisions."

…because that's mathematically false (the SHAttered PDFs exist). The
honest form is:

> ✓ "Store `S` contains no two distinct blob-names whose SHA-1
>    digests coincide."

…which is *verifiable* for finite scopes (you can iterate `S`'s
members and check) or *assumable* under collision-resistance
hypotheses (with the assumption now scoped to the specific store, not
the universe).

This requires the framework to **directly handle scoping**. Hashing
itself is an oracle — but the *scoping primitive* must be inside the
trust boundary, or else there's no way to write crypto assumptions
honestly.

Concretely:

- The framework refuses to express `∀x y. hash(x) = hash(y) ⟹ x = y`
  without a Store argument. The crypto assumption literally cannot be
  stated unscoped, because there's no place to put it.
- All meaning-axioms that talk about collision-resistance,
  preimage-resistance, etc., quantify over a store ID.
- The downward-closure derived theorem ([§6](#6-downward-closure-derived-theorem))
  transports scoped assumptions along subset edges.

This is the answer to the planning-conversation question "should
content addressing be an oracle like any other?" Yes — *hashing* is
an oracle. But *scoping* is a framework primitive, because without it
you cannot write the trust set honestly.

---

## 4. Store membership

### 4.1 The inference rule (restated)

```
                              s : Store    n : Bytes
 ──────────────────────────  (member-i)    ─────────────────────────  (member-r)
   framework.record(s, n)                       · ⊢ in_store(s.id, n)
        produces
```

Calling `framework.record_member(&mut s, n)`:

- Mutates `s` to add `n` to `s.members`.
- Returns a Thm `· ⊢ in_store(s.id, n)`.

The Thm's conclusion mentions `s.id` (a constant
[Name256](./00-glossary.md#name256)) and `n` (constant bytes). Both
are ground; the Thm is in the empty context.

### 4.2 What `in_store` *means*

`in_store(s, n)` is a framework-built-in relation, *not* a regular
oracle relation. The framework owns it implicitly (every Store's ID
acts as the implicit authority over `in_store(self_id, _)`).

The relation has no further interpretation at the framework level —
it's *just* the recorded set membership. Users layer interpretations
on top via meaning-axioms about the store, e.g., "every name in this
store is the BLAKE3 hash of some Git tree."

### 4.3 Idempotence and ordering

`record_member(s, n)` is idempotent: calling it twice with the same
`n` adds `n` once to the set; the second call returns the same Thm
shape but a fresh Thm (Thms are not interned).

The order in which members are recorded is irrelevant for soundness;
the membership relation is set-based.

---

## 5. Store subset and SubsetWitness

### 5.1 The inference rule (restated)

```
   W : SubsetWitness(s₁, s₂)
  ──────────────────────────────────────────────  (subset-i)
   · ⊢ ⋀x. in_store(s₁, x) ⟹ in_store(s₂, x)
```

The framework provides a `SubsetWitness` type whose successful
construction proves member-by-member that every member of `s₁` is
also in `s₂`.

### 5.2 The witness shape

Proposed (subject to [§13](#13-open-questions)):

```rust
pub struct SubsetWitness {
    from: StoreId,
    to: StoreId,
    // The witness body: explicit listing of from's members and
    // their image in to.  The framework checks each is actually in
    // `to.members`.
    body: Vec<Bytes>,
}

impl SubsetWitness {
    pub fn new(from: &Store, to: &Store) -> Self;
    pub fn validate(&self, from: &Store, to: &Store)
        -> Result<(), SubsetError>;
}
```

`framework.prove_subset(witness)` runs `validate()` — which checks
that every member of `from` is *also* recorded in `to` — and emits
the subset Thm.

### 5.3 Variants

- **Identity subset.** `subset(s, s)`. Trivially provable: every
  member's image is itself. The framework can provide a fast path.

- **Inclusion subset.** `s₁ ⊆ s₂` where `s₂` is a strict superset
  of `s₁`. Standard case for the Git-repo demo: re-hash the repo's
  blobs into a new store and prove the old store is contained.

- **Filtered subset.** `s₁ ⊆ s₂` where `s₁`'s members are a
  *predicate-defined* subset of `s₂`'s. Not directly supported by
  `SubsetWitness`; user-space proves this via (assume) + (⋀-intro)
  + (⟹-intro) over the predicate.

- **Mapped subset.** `f(s₁) ⊆ s₂` where `f` is a name-transformation.
  Discussed in [§12.3](#123-mapped-stores).

### 5.4 What the framework does *not* do

- The framework does not *automatically* derive subset Thms.
  `prove_subset` requires an explicit witness.
- The framework does not maintain a subset graph. If you want to know
  whether `s₁ ⊆ s₃` via `s₁ ⊆ s₂ ⊆ s₃`, you derive that yourself by
  (⟹-elim) + (⋀-elim) on the two subset Thms.

This matches the no-automatic-work discipline from
[`prover-architecture.md`](../../../prover-architecture.md) §4.

---

## 6. Downward closure (derived theorem)

Downward closure is **not** a framework primitive — it's a derived
theorem in user-space, proved once and reused:

```
⋀h. ⋀s₁ s₂. subset(s₁, s₂)
            ⟹ no_collisions(s₂, h)
            ⟹ no_collisions(s₁, h)
```

…where `no_collisions(s, h)` unfolds (per the user's definition of
"no collisions") to

```
⋀x y. in_store(s, x) ⟹ in_store(s, y)
   ⟹ h.hashed(x, d) ⟹ h.hashed(y, d)
   ⟹ x ≡ y
```

The framework derives this transitively from the subset Thm plus
the (⋀-elim) + (⟹-elim) machinery. The user lifts it once into
their library.

**Why not framework-primitive:** because the definition of
`no_collisions` mentions a *hash oracle* relation (`h.hashed`), which
is per-hash-function. The framework doesn't know what
"collision-free" means for an arbitrary oracle's hashed-relation; the
user supplies the definition and gets the downward-closure theorem in
return.

---

## 7. The global-store framing

[`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §5.4 introduces the
**open-store problem**: stores are *open* (more blobs can be added at
any time), so a later load could retroactively falsify a snapshot
theorem. The fix is to "change the quantifier domain":

> Assume a global store of everything seen by everyone in your
> interaction graph lacks `$BAD`; assert each local store — possibly
> mapped/filtered — is a subset.

In our redesign, this is **literally how stores work**:

- Each [federation](./00-glossary.md#federation) peer (kernel
  instance) maintains its own local store(s).
- Cross-peer assumptions (e.g., "no SHA-1 collisions across all
  observed blobs anywhere") are framed as *subset edges*: each peer
  proves their local store is a subset of the assumed-collision-free
  global.
- "No `$BAD`" is downward-closed: subset preserves it (§6). Growth
  of one peer's local store never retroactively falsifies another's
  theorem — at worst, it adds new obligations.

The "global store" is just *one specific Store* in some peer's view.
It's not privileged at the framework level; it's a convention.

This makes the cryptographer's honest discipline mechanizable:

- The trust set explicitly mentions which store the assumption
  applies to.
- Subset edges discharge transport obligations.
- The framework refuses to silently fuse different stores' contents.

---

## 8. Worked example: SHAttered

### 8.1 The setup

Two distinct PDFs with the same SHA-1 hash:

```
PDF_A : Bytes  with  SHA1(PDF_A) = collision_hash
PDF_B : Bytes  with  SHA1(PDF_B) = collision_hash
PDF_A ≠ PDF_B
```

A naive system asserts `∀x y. SHA1(x) = SHA1(y) ⟹ x = y`. Loading
both PDFs into the system makes the assertion *retroactively false*,
and every theorem that used it is now suspect.

### 8.2 In our system

Suppose we have a Store `S` containing the names of various blobs
the kernel has seen. We can:

1. *Assume* `no_collisions(S, SHA1)`.
2. Derive theorems about S's contents using this assumption.

If we then `record_member(S, name_of_PDF_A)` and
`record_member(S, name_of_PDF_B)`, the assumption is **still
syntactically intact**: the framework doesn't auto-invalidate it.
But:

3. The SHA1HasherOracle observes
   `SHA1HasherUUID.hashed(name_of_PDF_A, collision_hash)` and
   `SHA1HasherUUID.hashed(name_of_PDF_B, collision_hash)`.
4. The user's
   [meaning-axiom](./03-authority.md#6-meaning-axioms-in-detail)
   interprets these as actual SHA1 hash equalities.
5. From `in_store(S, name_of_PDF_A)`,
   `in_store(S, name_of_PDF_B)`, the two hashed-facts, and
   `no_collisions(S, SHA1)`, the framework derives
   `name_of_PDF_A ≡ name_of_PDF_B`.
6. The user's separate observations
   (`name_of_PDF_A ≠ name_of_PDF_B`, presumably from a content-byte
   comparison oracle) contradict this.

**Result:** the trust set is **honestly inconsistent**. The
framework reports the inconsistency at the point of use — not by
retroactively invalidating earlier theorems, but by exposing that
they were premised on a now-falsified assumption.

The user's recourse:

- **Withdraw the assumption.** Remove `no_collisions(S, SHA1)` from
  the trust set. Theorems that depended on it have an undischarged
  hypothesis in their context — they're still Thms, just less useful.
- **Restrict the store.** Define a smaller `S' ⊊ S` whose members
  don't include the colliding PDFs; assume `no_collisions(S', SHA1)`
  fresh. Re-derive the theorems against `S'`.
- **Switch hash function.** Re-hash everything to BLAKE3, build a
  store `S_blake3` of the new names, assume
  `no_collisions(S_blake3, BLAKE3)`. The old SHA-1-keyed theorems
  don't transfer automatically; they need to be re-proved against the
  new store with a bijection oracle observing the SHA1↔BLAKE3
  correspondence.

In every case, the **trust set carries the assumption explicitly** —
the user can see what was assumed and reason about the consequences.

---

## 9. Worked example: Git-repo demo

This is the planning conversation's chosen MVP demo target.

### 9.1 Setup

The user wants to prove a theorem about a specific Git repository —
say, "commit `c0ffee` in repo `R` has a tree containing a file
`src/lib.rs` whose content begins with the bytes `pub fn`."

### 9.2 Concrete steps

1. **Clone the repo.** Out-of-band; results in a working directory
   with the repo's blobs.

2. **Create a framework Store** `R_store`:

   ```rust
   let mut r_store = framework.fresh_store();
   ```

3. **Walk the repo, record each Git oid as a member.**

   ```rust
   for git_oid in git_repo.iter_objects() {
       framework.record_member(&mut r_store, git_oid.as_bytes());
   }
   ```

   Each call emits a `⊢ in_store(r_store.id, oid)` Thm. The user
   accumulates these (they're the framework's record of "what we
   observed").

4. **Prove no SHA-1 collisions in `r_store`, by exhaustion.** Because
   `r_store.members` is finite and the user has it in hand, the user
   can iterate all pairs and verify `SHA1(x) ≠ SHA1(y)` for all
   distinct `x, y`. The result is a Thm:

   ```
   ⊢ no_collisions(r_store.id, SHA1)
   ```

   This is **not** a framework primitive — it's user-space, using
   the SHA1HasherOracle's observations + the user's exhaustive
   case analysis. The framework just provides the membership facts.

5. **Optionally re-hash to BLAKE3.** Create a second Store
   `r_store_blake3`:

   ```rust
   let mut r_store_blake3 = framework.fresh_store();
   for git_oid in git_repo.iter_objects() {
       let bytes = git_repo.read(git_oid)?;
       let blake3_name = framework.observe(&blake3_oracle, ...).result;
       framework.record_member(&mut r_store_blake3, blake3_name);
       // user records: blake3_oracle.hashed(blake3_name, /*expected*/)
       //               + bijection_oracle.bijects(git_oid, blake3_name)
   }
   ```

   The bijection oracle's meaning-axiom lets the user transport
   theorems about `r_store`'s members to `r_store_blake3`'s
   members (or vice versa).

6. **Prove the property.** Use the membership facts, the
   hash-observation facts, and any other oracles (Git tree
   structure, byte content) to derive the conclusion:

   ```
   ⊢  in_store(r_store, c0ffee)
      ∧  git_oracle.tree_contains(c0ffee, "src/lib.rs", lib_oid)
      ∧  blob_oracle.bytes_prefix(lib_oid, "pub fn")
   ```

   …possibly under the trust assumptions
   `no_collisions(r_store, SHA1)` + `git_oracle_meaning_axiom` +
   `blob_oracle_meaning_axiom`.

### 9.3 Why this works without a "no SHA-1 collisions ever" assumption

The crypto assumption is scoped to `r_store`, *which we exhaustively
verified*. The assumption is **literally true** for that store (by
the exhaustion check); no honest doubt about it.

If a future revision of the repo introduces a colliding pair (very
unlikely but mathematically possible), it would land in a *different*
store snapshot (`r_store_v2`), and the earlier theorem stays valid
about `r_store`.

This is the **honest cryptographic discipline** ARCHITECTURE.md §5.3
talks about, mechanized into the framework's normal operations.

---

## 10. Stores and authorities (relationship)

### 10.1 They are orthogonal

Stores are **not** [authorities](./00-glossary.md#authority). A Store
is a set of names; an authority is a writer of observations.

The framework reserves the `in_store` relation as implicitly owned by
"the framework itself" rather than by any user-creatable authority.
This is the only relation the framework owns directly.

### 10.2 The bookkeeping interaction

Each [observation](./00-glossary.md#observation) about a blob
implicitly references some store — but the framework doesn't track
which one. The user is responsible for keeping track of "which
oracle's observations belong to which store" via meaning-axioms.

For example: the `BLAKE3HasherOracle.hashed(name, h)` observation
contains a `name` arg. The user's meaning-axiom typically reads:

```
⋀n h.  in_store(my_blake3_store, n)
   ⟹ BLAKE3HasherOracle.hashed(n, h)
   ⟹ BLAKE3_unkeyed_digest(get_bytes(n)) == h
```

The store membership *qualifies* the meaning-axiom: we only believe
the hash claim for blobs we've actually observed in `my_blake3_store`.

### 10.3 No cross-talk

A user could declare a *terrible* meaning-axiom that mixed stores
incoherently — e.g., "for blobs in `S_A`, the hash function `H_B`
holds." The framework would accept it (in the safe class), and the
user would get nonsense theorems. The framework does **not** police
this.

This matches the framework's "scoped assumptions, never the global
lie" rather than "infinite oversight": users get to make false
assumptions; they just can't blame the framework for the
consequences.

---

## 11. Store growth, freezing, and serialization

### 11.1 Growth

Stores **can grow at runtime**. Each `record_member` adds to
`store.members`. Previously-derived theorems referencing the store
remain valid — they assert facts about specific named members, not
about "all current members" (unless the user took such a Thm under
an explicit quantifier).

### 11.2 Freezing

A *frozen* Store is a Store whose `members` set is fixed and from
which no more `record_member` calls are allowed:

```rust
impl Store {
    pub fn freeze(self) -> FrozenStore;
}

pub struct FrozenStore(Store);  // members is immutable
```

Freezing is *useful* for:

- Producing a stable hash of the store (for content-addressing the
  exact snapshot of recorded members).
- Exporting the store's full content to a peer.
- Marking "no more observations will be added; this store represents
  exactly what we've seen."

### 11.3 Serialization

A frozen Store can be serialized as:

```
store_serialized = {
    store_id: Name256,
    members: Vec<Bytes>,
}
```

A peer kernel can ingest this and call `framework.record_member` to
add each name into a peer-local Store, producing the corresponding
membership Thms. The peer can then `prove_subset(peer_store_via_export,
peer_existing_store)` if they want to merge contents.

### 11.4 Open question: store-content hash

Should a Store have a content hash? Yes, eventually — `FrozenStore`
gets a hash defined as

```
BLAKE3::keyed_hash(STORE_CONTENT_FORMAT_ID,
                   sorted-encoding(members))
```

…using the [keyed BLAKE3 mode](./01-conventions.md#2-the-blake3-mode-trichotomy)
(the store's content is a *typed value*). This is *not* a framework
primitive (the framework doesn't hash anything) — it's an oracle
operation (the BLAKE3HasherOracle observes the hash, which the user's
meaning-axiom interprets).

---

## 12. Multi-store reasoning

### 12.1 Disjoint stores

Two Stores `s₁`, `s₂` with disjoint members can be reasoned about
independently. The framework provides no "disjointness" primitive —
the user proves disjointness with a side theorem if needed.

### 12.2 Union of stores

There is no framework primitive for "the union of `s₁` and `s₂`."
Instead, the user creates a new store `s_union`, records all members
of both, and proves the two subset edges
`s₁ ⊆ s_union`, `s₂ ⊆ s_union`. Membership facts in `s_union`
follow from the subsets.

### 12.3 Mapped stores

If a name-transformation `f` (e.g., re-hashing under a different hash
function) is applied to every member of `s₁` to produce `s₂`'s
members, the relationship is a **mapped subset**:

```
⋀x. in_store(s₁, x) ⟹ in_store(s₂, f(x))
```

This is **not** the same as `subset(s₁, s₂)`. The framework does not
directly express mapped subsets; the user states the relationship as
a meaning-axiom (or proves it from oracle observations).

In the Git-repo demo ([§9.5](#9-worked-example-git-repo-demo)), the
relationship between `r_store` and `r_store_blake3` is a mapped
subset under the BLAKE3 re-hashing transformation, witnessed by a
bijection oracle's observations.

### 12.4 The "global store" assumption

A common pattern: assume a `global_store` exists, and prove every
local store is a subset of it. Crypto assumptions about
`global_store` then transport down to every local store via §6.

The "global store" is just another Store in the framework's view —
nothing privileged about it. The privilege lives in the *trust set*:
users assume crypto properties of `global_store`, treat subset edges
to it as "we believe we're inside the global universe of
non-pathological blobs."

---

## 13. Open questions

- **`SubsetWitness` representation.** Proposed: `Vec<Bytes>` listing
  the from-side members (each must be in the to-side). Confirm. An
  alternative is a `Vec<(Bytes, Bytes)>` if we want to support
  mapped subsets uniformly — but mapped subsets are user-space, not
  framework, so probably not.

- **Frozen vs mutable store API.** Proposed: `Store` is mutable;
  `FrozenStore` is the immutable view. The framework operations
  that produce membership Thms take `&mut Store`; subset proofs
  take `&Store` (or `&FrozenStore`). Confirm.

- **Store-content hash.** As discussed in
  [§11.4](#114-open-question-store-content-hash), this is an oracle
  operation, not a framework primitive. Confirm we don't need a
  framework-level `Store::hash()` for any purpose.

- **Member encoding (Bytes vs Name256).** Proposed: members are
  arbitrary `Bytes` (not constrained to 256 bits), because external
  systems contribute names of various widths (Git SHA-1 = 160 bits,
  IPFS variable). Confirm. If we want to enforce 256-bit member
  names, that would be a convention layer, not a framework one.

- **`record_member` returning the Thm vs the store**. Proposed:
  returns just the Thm; the store is mutated in place. Alternative
  is to return `(Store, Thm)` for a more functional API; but stores
  are typically used mutably during a session, so the in-place
  shape is more ergonomic.

- **Schematic / unbounded stores.** A store defined by a predicate
  (e.g., "all hashes of blobs reachable from this Git commit") rather
  than by enumeration. This is **not** in the framework; user-space
  proves membership-by-derivation. Confirm.

- **Concurrent record_member.** Should the framework serialize
  concurrent `record_member` calls on the same store? Default: yes,
  via interior `Mutex` on the framework state.

---

## 14. Cross-references

- [`00-glossary.md`](./00-glossary.md) — vocabulary used here.
- [`02-framework.md`](./02-framework.md) §3.4, §5 — the store
  inference rules and the Store struct in summary form.
- [`03-authority.md`](./03-authority.md) — authorities, the other
  framework primitive. Stores are not authorities; the framework
  implicitly owns the `in_store` relation.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §5.3 — scoped no-collision,
  the SHAttered worked example, the conceptual basis for stores.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §5.4 — the open-store
  problem and the global-store framing; now realized as
  ordinary stores + subset edges in the framework.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §11 — storage (the VCS
  layer, Git-like trees, prolly-tree tables). This is the *byte
  backend* layer, separate from the framework's Store concept (see
  [§2](#2-store-vs-content-addressed-blob-store)).
- (Planned) [`08-oracles.md`](./) — the BLAKE3/SHA-1/Ed25519/WASM
  oracles that produce observations users discharge into
  store-scoped theorems.
- (Planned) [`09-federation.md`](./) — how stores travel between
  kernel instances via signed serialization.
- [`prover-architecture.md`](../../../prover-architecture.md) — current
  kernel's design, which has no store primitive. This is the most
  visible new addition.

# Conventions

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This document is part of a design proposal generated during a
> planning conversation. It is **not** a committed architecture; the
> shape, vocabulary, and approach are subject to substantial revision
> before any implementation lands. The word "Settled" below means
> "proposed-as-settled within this draft," not "decided by the team."
> For the canonical view of what is *actually built* vs. what is
> *proposed*, see [`where-we-are.md`](../../../where-we-are.md). For
> the proposal index, see [`README.md`](./README.md).

Settled conventions for the Covalence redesign. These are **commitments**:
they shape APIs, serialization formats, and what we mean by certain
words. Changes require explicit revisit and a note in the corresponding
doc.

Each convention has:

- **Rule** — what to do.
- **Why** — the reasoning, including alternatives considered.
- **Where it applies** — concrete touch-points in code.

Vocabulary used here is defined in [`00-glossary.md`](./00-glossary.md).

---

## 1. 256-bit opaque names for identities

### Rule

Every **identity** in the system is a 256-bit opaque value, typed as
[`Name256`](./00-glossary.md#name256). This includes:

- [Authority IDs](./00-glossary.md#authority-id--store-id--oracle-id)
- [Store IDs](./00-glossary.md#authority-id--store-id--oracle-id)
- [Oracle IDs](./00-glossary.md#authority-id--store-id--oracle-id) and
  sub-oracle IDs
- Content-addressed blob hashes (when we choose to expose them as
  identities)
- Public keys (for [federation](./00-glossary.md#federation))
- Format IDs (per [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §12)
- Thm / Prop IDs when serialized for export
- Fresh gensyms (see [§3](#3-fresh-names))

**Non-identities** that are *not* required to be Name256:

- Internal arena indices (`TermId`, `TypeId`, `ImportId`, …) — 32-bit
  or smaller for memory efficiency.
- Relation names within an authority (`"eval"`, `"validates"`,
  `"hashed"`) — short strings, scoped to the owning authority.
- User-facing display names — strings of any length.

### Why

Reasoning through the alternatives:

1. **Uniformity at the type-level.** With everything 256-bit, an
   identity *can be* a BLAKE3 hash, a SHA-256 hash, an Ed25519 public
   key, an RNG-fresh gensym, a derived name — and code that handles
   "an identity" doesn't need to dispatch on which it is. The
   identity's *origin* is recorded by *how it was constructed* (a
   trace in the trust set), not by its bit-width.

2. **Cryptographic output match.** BLAKE3-256, SHA-256, Ed25519 public
   keys are all 256-bit. Choosing 256 universally avoids
   wrapper/extractor noise at every hash↔identity boundary. We never
   have to write "extract the first 32 bytes of this hash."

3. **No commitment to a hash algorithm.** This is the core insight
   from the planning discussion: the framework is *hash-agnostic*. A
   Name256 doesn't say "this is a BLAKE3 hash." The same identity
   could equally well be a SHA-256 hash, a derived name, or a fresh
   gensym. Communities are free to use different hash functions for
   different purposes; the framework only sees the resulting 256-bit
   identities.

4. **[Fresh-as-RNG](#3-fresh-names) is rigorously honest at 256 bits.**
   Birthday-paradox: with N random 256-bit values, the probability of
   any collision is bounded by `N² / 2^257`. For N = 2^60 (a
   quintillion fresh names — way more than any practical scenario),
   collision probability is

   ```
   N² / 2^257  =  2^120 / 2^257  =  2^(-137)
   ```

   …which is negligible. We can *honestly* assume collision-freedom
   of [fresh](./00-glossary.md#fresh-rng-based) names in any
   practical [store](./00-glossary.md#store). At 160 bits (Git/SHA-1)
   the same calculation gives 2^(-41) at N = 2^60 — still small but
   notable; at 128 bits (UUID v4) it's 2^(-9), uncomfortably close to
   the birthday threshold for large stores. 256 bits is the natural
   landing.

5. **Domain separation comes for free.** Via context-keyed BLAKE3
   (see [§2](#2-the-blake3-mode-trichotomy)), we can derive any
   structured name into 256 bits with provable cryptographic
   separation. We don't need shorter names + per-namespace tag bytes;
   the keying handles separation.

6. **FS projection legibility.** Eventually
   ([`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §10–11) the system
   exposes mount hierarchies as a filesystem. Uniform 32-byte path
   components (base32 or base64-encoded) make `ls -l` output
   predictable — every directory at the same depth has the same name
   width.

7. **External system compatibility is cheap.** External hashes that
   aren't 256-bit (Git's 160-bit SHA-1, IPFS variable-width CIDs,
   NIST-P public keys, …) are *wrapped* into Name256 by hashing
   their canonical encoding under a dedicated context label:

   ```
   git_oid_to_name256(oid)  = BLAKE3::derive_key(
                                "covalence-import-git-oid-v1", oid)
   ipfs_cid_to_name256(cid) = BLAKE3::derive_key(
                                "covalence-import-ipfs-cid-v1", cid)
   ```

   The wrapping is honest: the resulting Name256 doesn't *claim*
   equivalence to the external hash — it names "the Covalence shadow
   of this external object."

### Trade-offs considered

- **Memory cost.** 32 bytes per identity vs. 4–8 for shorter IDs. We
  mitigate by reserving 32-bit IDs for *internal* references (arena
  indices); only **exported identities** are 256-bit. The cost is
  paid at the trust boundary, where audit clarity matters more than a
  few bytes.
- **Hash digest size vs. RNG output size.** Both BLAKE3 and SHA-256
  are 256-bit; the RNG output of 32 bytes is `getrandom(&mut [u8; 32])`.
  These align perfectly.
- **What about 128-bit UUIDs?** Insufficient collision margin under
  birthday paradox at large scale. See item 4 above.
- **What about 512-bit names?** Overkill. 256 bits is already 10^77
  values; 512 buys nothing practical.

### Where it applies

- `covalence-framework::Name256` (the wrapper type).
- All Authority, Store, Oracle types.
- The serialization format for exported Thms.
- Every public-key type at the federation boundary.
- All hash-output types in `covalence-hash` (already 256-bit for BLAKE3
  and SHA-256; Git wrappers documented).

---

## 2. The BLAKE3 mode trichotomy

### Rule

We use three BLAKE3 modes for three **conceptually distinct** purposes.
Mixing them is a soundness hazard; BLAKE3 enforces cryptographic
separation between the modes via mode bits, so the *choice* of mode
also functions as typed domain separation.

| Mode                      | API                                | Purpose                  |
|---------------------------|------------------------------------|--------------------------|
| **Unkeyed** (`hash`)      | `BLAKE3::hash(bytes)`              | Raw content addressing   |
| **Keyed** (`keyed_hash`)  | `BLAKE3::keyed_hash(K, bytes)`     | Typed values / Merkle    |
| **Context-keyed** (KDF)   | `BLAKE3::derive_key(ctx, key)`     | Semantic naming          |

### Why

These three uses correspond to the three corners of the trinity
([`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §9):

- **Unkeyed → evidence corner.** Bytes are bytes; the hash is their
  address. Pure content addressing. Use for blob identity.

- **Keyed → format corner.** The 32-byte key *is* the format ID;
  `keyed_hash(format_id, payload)` is the typed value's
  [Name256](./00-glossary.md#name256). This is the
  `keyed(format_id, payload)` construction from
  [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §12: domain separation
  for free, no concatenation ambiguity, the id is a *genuine third
  thing* (not format alone, not payload alone).

- **Context-keyed → meaning corner.** The context string is a
  **static string literal** (BLAKE3's API enforces this — it cannot
  be dynamically computed at compile time). Used to name oracles,
  specs, sub-oracles, and other semantic objects. The context string
  is part of source code, human-auditable, can't be forged
  dynamically.

### Citation discipline

- When we write **"BLAKE3"** without qualification, we mean **unkeyed
  BLAKE3**. Default behavior. Most code paths.
- To use a keyed mode, write **"BLAKE3 keyed"**, **"keyed BLAKE3"**,
  or `BLAKE3::keyed_hash(...)`. This is *not* a generic keyed-hash;
  it's specifically BLAKE3's mode.
- To use the KDF, write **"BLAKE3 derive-key"**, **"BLAKE3 KDF"**,
  or `BLAKE3::derive_key(...)`.

These are the names used in
[`covalence-hash`](../../../../crates/covalence-hash)'s API and in spec
documents.

### Cross-mode separation

BLAKE3 internally uses mode bits in its compression function:

- Unkeyed mode: regular hash bits.
- Keyed mode: keyed-hash mode bits.
- Derive-key mode: derive-key mode bits, with the context string
  hashed into a derived key first.

This means there is **no input** to one mode that produces the same
output as another mode on the same input. We can use the same byte
sequence under all three modes without collision. This is the
cryptographic guarantee that makes the trichotomy honest.

### Where it applies

- All hashing operations should be a clearly-named one of the three
  modes.
- Spec documents stating "the oracle name is BLAKE3(X)" must specify
  the mode (unkeyed/keyed/derive-key).
- Code reviewers: flag any `BLAKE3` call where the mode is ambiguous.

---

## 3. Fresh names

### Rule

`Framework::fresh() -> Name256` returns a 256-bit value **assumed not
to collide** with any name in any
[store](./00-glossary.md#store) of interest in the current
computation. Implementation: cryptographically secure RNG.

### Why

The alternatives are deterministic gensym schemes (counter + process
ID, sequential IDs, hash-of-context). RNG-based fresh names win on:

1. **Uniformity across instances.** A second-thread kernel mints fresh
   names that don't collide with the first thread's, *for free*
   (probabilistically), with no shared counter or coordination. This
   is essential to the [PKI](./00-glossary.md#pki-public-key-infrastructure)-as-universal-substrate
   framing.

2. **Trivial serialization.** A fresh name is 32 bytes; no
   surrounding context (process ID, machine ID) needs to come along.
   This means a fresh name can be exported as-is.

3. **Same primitive as cryptographic key generation.** Reading 32
   bytes from a CSPRNG *is* the operation that generates an Ed25519
   private key, an HMAC key, a fresh authority ID, a fresh store ID.
   No new code path.

4. **Honest about the collision assumption.** Counter-based gensyms
   *hide* the collision question (they pretend deterministic ⇒
   collision-free, but only within a known scope); RNG-based gensyms
   make it explicit and quantifiable (see
   [§1 item 4](#why)).

### The collision-freedom assumption

We add to the [trust set](./00-glossary.md#trust-set) the standing
assumption:

```
∀s ∈ Stores. ∀n ∈ FreshNamesIssued.  ¬in_store(s, n)
```

…with the discharge being the birthday-paradox argument plus
"our RNG is in fact cryptographically secure" (which is a
[meta-trust](./00-glossary.md#meta-trust-set) commitment about our
RNG implementation, mediated by
[`covalence-rand`](../../../../crates/covalence-rand)).

### Implementation

Read 32 bytes from the platform's CSPRNG via
[`covalence-rand`](../../../../crates/covalence-rand). Default backend is
BLAKE3-DRBG seeded from OS entropy on first use, with re-seeding per
the BLAKE3-DRBG spec. The wrapper crate handles this.

### Where it applies

- `Framework::fresh() -> Name256` — every place a new identity is
  created.
- `Authority::fresh_local(rels)` — creates an authority with a fresh
  ID.
- `Framework::fresh_store()` — creates a store with a fresh ID.
- Internal kernel use only — the framework itself uses `fresh()` for
  bookkeeping; user code calling these is downstream.

---

## 4. Oracle ID derivation

### Rule (recommended, not framework-primitive)

Well-known [oracle IDs](./00-glossary.md#authority-id--store-id--oracle-id)
are derived as:

```
oracle_id  =  BLAKE3::derive_key("covalence-oracle-spec-v1", spec_bytes)
```

Sub-oracle IDs:

```
sub_id = BLAKE3::derive_key(
    "covalence-suboracle-v1",
    parent_id || scheme_label || 0u8 || payload
)
```

The context strings are **published as part of the framework spec**;
no kernel implementation may use different strings without versioning
the convention (e.g. `-v2`).

### Why it's recommended, not framework-primitive

The framework doesn't enforce a particular derivation scheme. It just
sees Name256 values arriving at the
[observation](./00-glossary.md#observation) interface. Different
communities could publish their own conventions (e.g. "we derive
oracle IDs as SHA-256 of the spec"); the framework would happily run
both.

We recommend this BLAKE3-derive-key scheme because:

1. **Self-witnessing identities.** An oracle ID computed as
   `derive_key(...,spec_bytes)` literally *points at* its own
   definition. Anyone who has the spec text can verify the ID.
2. **Cross-kernel agreement comes for free.** Two engines with the
   same spec text derive the same ID. No central registry; no signing
   of "this name means this spec."
3. **Spec revisions naturally produce new IDs.** Edit the spec, hash
   changes, new oracle. This is *correct* — a new spec is a new
   oracle.
4. **The BLAKE3-mode separation matches the trinity.** Oracle IDs are
   semantic objects, so they belong in the **context-keyed** corner.

### Where it applies

- Every published oracle spec includes its `oracle_id`, computed by
  this scheme. Reviewers verify the computation.
- Sub-oracle derivation in oracle implementations.
- Documentation in (planned) [`08-oracles.md`](./).

---

## 5. Wrapper-crate discipline (continuing)

### Rule

All external dependencies go through wrapper crates. This is
already established in [`CLAUDE.md`](../../../../CLAUDE.md#wrapper-crates)
and continues through the redesign.

### Why

- Centralization: changing a dep doesn't touch every consumer.
- Project-specific extensions: e.g. `covalence-rand` adds
  `Framework::fresh()` semantics on top of `rand`.
- Audit clarity: a `cargo deps` view shows only the wrapper crates at
  the boundary.

### New wrapper crates the redesign needs

| Wrapper                  | Purpose                                                   |
|--------------------------|-----------------------------------------------------------|
| `covalence-framework`    | The Framework crate (new; this is the TCB).               |

(Most other wrappers already exist; see
[`where-we-are.md`](../../../where-we-are.md) §1.)

### Where it applies

- Never `use blake3` directly outside `covalence-hash`.
- Never `use ed25519_dalek` directly outside `covalence-sig`.
- Never `use rand` directly outside `covalence-rand`.
- The framework crate uses only `covalence-rand` as an external
  dependency (plus standard library).

---

## 6. Error handling

### Rule

- **Library crates:** `thiserror`-derived enums.
- **Binaries:** `eyre` for the top-level error type, `color-eyre`
  for display.
- **Framework crate:** `thiserror` enums per concept
  (`AuthorityError`, `StoreError`, `ProofError`, …), all re-exported
  under `covalence_framework::Error`.

Don't fall back to `anyhow` in library code; that erases the error
shape. The Framework's errors are part of its API — callers need to
discriminate by kind for reporting and recovery.

---

## 7. Rust idioms (framework-specific)

### Rule

- **Sealed IDs.** Internal indices (`TermId`, `TypeId`, `AuthorityId`,
  …) are newtypes around `u32` or `[u8; 32]` with no public field.
  Construction goes through the kernel API.
- **`Arc<T>` for shared frozen state.** `Arc<Arena>` is the canonical
  share pattern.
- **`Copy` for sealed 32-bit IDs.** `TermId`, `TypeId`, etc. are
  `Copy`. 256-bit identity types are `Copy` (the byte array is), but
  pass by reference in hot paths to avoid 32-byte copies.
- **`pub(crate)` for non-API internals.** The `TermDef` / `TypeDef`
  representations are private; users interact through `TermKind` /
  `TypeKind` view enums.
- **No `unsafe`** in the framework crate. We may allow `unsafe` in
  wrapper crates and in the WASM oracle, but not at the trust
  boundary.

### Why

These are pre-existing patterns in `covalence-kernel`; the redesign
continues them. See
[`prover-architecture.md`](../../../prover-architecture.md) §2.2, §3.1 for
the established conventions.

---

## 8. File layout convention (for new crates)

```
covalence-X/
  Cargo.toml
  src/
    lib.rs       — re-exports, crate-level docs
    error.rs     — thiserror error enum(s)
    <concept>.rs — one file per top-level concept
  examples/      — end-to-end usage examples (one per concept ideally)
  tests/         — integration tests
  README.md      — one-line summary at top, full design link below
```

Avoid `mod.rs`-style directories at the top; flat is friendlier for
navigation. For the framework crate specifically, see
[`02-framework.md`](./02-framework.md) §7 for the proposed
`src/` layout.

---

## 9. Documentation conventions

### Rule

- **Inference rules** use display form: numerator above a horizontal
  bar, denominator below, rule name in parens to the right.
- **Vocabulary terms** are linked to
  [`00-glossary.md`](./00-glossary.md) on first occurrence in each
  doc.
- **Cross-doc references** use Markdown links: `[term](file.md#anchor)`.
- **Open questions** at the end of each doc list explicit decisions
  to make before implementation.
- **"Why" sections** are required for any non-obvious decision; future
  agents need to understand the reasoning.

### Where it applies

All docs in [`docs/design/`](./).

---

## 10. Cross-reference summary

This conventions doc is referenced from:

- [`00-glossary.md`](./00-glossary.md) — for the meanings of the terms
  it conventionalizes.
- [`02-framework.md`](./02-framework.md) — for the API conventions
  the framework follows.
- Future docs (`03`–`09`) — each builds on conventions established
  here.

If a convention here is found insufficient during deeper design work,
the right move is to **update this doc** rather than diverge silently
in a downstream doc.

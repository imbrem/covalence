# Trust: Meta-Trust, Trust Set, and ElidePolicy

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> This document is part of a design proposal generated during a
> planning conversation. It is **not** a committed architecture; the
> shape, vocabulary, and approach are subject to substantial revision
> before any implementation lands. For the canonical view of what is
> *actually built* vs. what is *proposed*, see
> [`where-we-are.md`](../../../where-we-are.md). For the proposal
> index, see [`README.md`](./README.md).

The framework's TCB is split into **two levels**. The
[**meta-trust set**](./00-glossary.md#meta-trust-set) is what we
trust *as constitutive of our kernel's identity* — implemented in
Rust, never exposed as observations, with no provenance trail. The
[**trust set**](./00-glossary.md#trust-set) is the set of explicit
assumptions a particular derivation depends on — meaning-axioms,
mount edges, peer trust, user-stated axioms. These are
*honestly assumptions*: visible in context, mountable,
withdrawable, doubtable.

This is the **LCF discipline generalized**. Standard LCF says "keep
the TCB tiny." We say more: "and be honest about what trust comes
from inside (meta-trust) vs. from a deliberate assumption (trust
set)."

[**ElidePolicy**](./00-glossary.md#elidepolicy) is the operation
that bridges the two when exporting: it lets the kernel substitute
abstract spec-level identities for local-instance ones, *citing the
mount edges that justify the substitution*.

**Prerequisites:** [`00-glossary.md`](./00-glossary.md) (vocabulary),
[`03-authority.md`](./03-authority.md) (authorities, observations,
meaning-axioms), [`04-store.md`](./04-store.md) (stores).

---

## Contents

1. [The two-level distinction](#1-the-two-level-distinction)
2. [What's in meta-trust (canonical list)](#2-whats-in-meta-trust-canonical-list)
3. [What's in the trust set (typical examples)](#3-whats-in-the-trust-set-typical-examples)
4. [The honesty discipline](#4-the-honesty-discipline)
5. [β-reduction as the canonical meta-trust example](#5-β-reduction-as-the-canonical-meta-trust-example)
6. [The hidden-meta-trust hazard](#6-the-hidden-meta-trust-hazard)
7. [ElidePolicy: what and why](#7-elidepolicy-what-and-why)
8. [ElidePolicy: how it's structured](#8-elidepolicy-how-its-structured)
9. [Worked example: exporting a Thm to a peer](#9-worked-example-exporting-a-thm-to-a-peer)
10. [The trust graph (who trusts whom)](#10-the-trust-graph-who-trusts-whom)
11. [Open questions](#11-open-questions)
12. [Cross-references](#12-cross-references)

---

## 1. The two-level distinction

There are **two qualitatively different things** we currently
sometimes call "trust":

| Level                                    | What it is                                                                  | Honest name                | Should be                  |
|------------------------------------------|------------------------------------------------------------------------------|----------------------------|----------------------------|
| **Meta-trust**                           | Operations we trust *as part of our own identity* — implemented in Rust, never exposed as observations, no provenance trail | "constitutive trust" / "kernel-self" | **Tiny.** ~700-800 LoC.    |
| **Trust set**                            | Assumptions we acknowledge as such — meaning-axioms, mount edges, peer trust, user axioms | "scoped assumptions"       | Arbitrarily large; audited |

A bug in **meta-trust** can produce false Thms.
A wrong **trust set assumption** produces unmoored Thms (the
assumption-as-hypothesis stays in their context; you can find them
and re-examine).

This is the LCF discipline applied **explicitly at two levels**.
HOL Light has one big TCB (the kernel); we deliberately distinguish
"what is silently implemented" from "what is explicitly assumed."

### Why this matters

- **Meta-trust is small and audited once.** Bugs are catastrophic
  but the surface is bounded.
- **The trust set is *honest*.** Every Thm carries the assumptions
  it depends on as visible hypotheses. Withdrawing an assumption
  doesn't *invalidate* a Thm (the Thm still exists, with that
  assumption in its context) — it leaves the Thm with an
  undischarged hypothesis, which is information.

The distinction is what makes "we trust K as a federation peer" and
"we trust BLAKE3 is collision-resistant" and "we trust our Rust
β-implementation is correct" cleanly separate. The first two are
trust-set assumptions; the third is meta-trust.

---

## 2. What's in meta-trust (canonical list)

The meta-trust set has **five** entries:

### 2.1 The LF inference rules

- (assume), (imp-i), (imp-e/MP), (all-i), (all-e), (refl), (trans),
  (sym), (cong-app), (cong-abs), (β), (η), (observe), (member-i),
  (member-r), (subset-i), (def).

Listed in [`02-framework.md` §3](./02-framework.md#3-inference-rules).
The framework's Rust implementation of these rules is meta-trust:
if the Rust code does (imp-e) wrong, false Thms result.

This is the standard LCF kernel concept.

### 2.2 Term and type representation operations

- α-equivalence (free via de Bruijn).
- Capture-avoiding substitution (used in (all-e), (β)).
- [β/η-reduction](./00-glossary.md#β-reduction-η-conversion) as
  syntactic operations.

These are *not* exposed as observations (see [§5](#5-β-reduction-as-the-canonical-meta-trust-example)).

### 2.3 Authority bookkeeping

- The `Authority::owned_relations` membership check at (observe).
- The `safe-axiom class` check at axiom assertion.
- The relationship-name uniqueness check within an authority.

[`03-authority.md`](./03-authority.md) §5 details these checks. A bug
here would let one authority forge observations under another's
namespace.

### 2.4 Store operations

- The `Store::members` set tracking.
- The `SubsetWitness::validate()` check.
- The implicit framework-owned `in_store` relation.

[`04-store.md`](./04-store.md) details these. A bug here would let a
user "prove" `in_store(s, n)` for an `n` that wasn't actually
recorded — which would break the scoped crypto assumptions.

### 2.5 RNG for fresh names

The platform CSPRNG, accessed via
[`covalence-rand`](../../../../crates/covalence-rand). The "fresh names
don't collide" assumption (the [trust-set assumption](./01-conventions.md#3-fresh-names)
that bottoms out in birthday-paradox math) is only honest if our
RNG output is actually random.

A weak RNG is a meta-trust bug: not directly exposed in any
observation, just silently makes the birthday-paradox argument false.

**Not in meta-trust** (despite their importance):

- **Hash functions** (BLAKE3, SHA-256). They're
  [oracles](./00-glossary.md#oracle).
- **Signature schemes** (Ed25519). Also oracles, with a
  conventionally pre-loaded meaning-axiom in
  the trust set (see [§3](#3-whats-in-the-trust-set-typical-examples)).
- **Executors** (WASM, native). Oracles.
- **The byte backend** (`covalence-store`'s `BlobStore`). An oracle
  for "looking up bytes by name."
- **Serialization formats.** Userspace concern.

These produce *observations*; the user discharges via meaning-axioms.
They're outside the trust boundary.

---

## 3. What's in the trust set (typical examples)

The [trust set](./00-glossary.md#trust-set) of any given Thm is just
the context Γ in `Γ ⊢ φ`. Common assumptions:

### 3.1 Meaning-axioms for oracles

For each oracle the user wants to interpret, a meaning-axiom in the
[safe-axiom-violating](./03-authority.md#6-meaning-axioms-in-detail)
shape:

```
⋀args. O.R(args) ⟹ spec_predicate(args)
```

These are *not conservative* — they make a substantive claim about
what the oracle's observations mean. The user opts in explicitly.

### 3.2 Mount edges

`⋀x. Q(x) ⟹ P(x)` connecting two authorities' relations. Per
[`03-authority.md` §9](./03-authority.md#9-mount-as-authority-bridge),
mounts are in the [safe-axiom class](./00-glossary.md#safe-axiom-class)
when the head is the consumer's relation. They're commonly used to
bridge "my local instance" to "the abstract spec":

```
⋀i o. MyKernel_WASM_Local.eval(i, o) ⟹ WASMRun(H_B).eval(i, o)
```

### 3.3 Peer trust assumptions

"If key K signs an observation, we will treat the observation as
true." Concretely:

```
⋀msg sig.  Ed25519VerifierUUID.verifies(K_pub, msg, sig)
       ⟹  msg_well_formed_thm_with_context_C
       ⟹  C ⊢ thm_in_msg
```

These are *not* in the safe class; they meaningfully shift trust to
the peer.

### 3.4 User axioms about object logics

E.g., "HOL is consistent" or "this object logic's induction axiom
holds." These are
[`covalence-hol`](./) layer concerns; the framework supports them as
ordinary user-asserted axioms.

### 3.5 Scoped crypto assumptions

`no_collisions(specific_store, specific_hash)` etc. See
[`04-store.md` §7](./04-store.md#7-the-global-store-framing).

### 3.6 The "fresh names don't collide" assumption

```
⋀s n. n ∈ FreshIssued ⟹ ¬in_store(s, n)
```

Standing assumption, discharged by birthday paradox + meta-trust of
the RNG. Usually pre-loaded into a session's root context.

### 3.7 The "Ed25519 verifier implementation is correct" convention

Most kernels ship with this meaning-axiom pre-loaded:

```
⋀pk m s. Ed25519VerifierUUID.verifies(pk, m, s)
     ⟹ ed25519_spec_verifies(pk, m, s)
```

This is **trust-set, not meta-trust** — it's a *meaning-axiom*, not
a Rust impl. But by convention it's nearly always assumed. The
honest move is: it's still listed in the trust set; users can
withdraw it if they want to reason about a kernel where Ed25519
verification might be wrong.

---

## 4. The honesty discipline

> **The meta-trust set should be tiny; the trust set should be
> explicit.**

This means:

- **Keep meta-trust as small as possible.** Every Rust line in the
  framework that affects soundness is meta-trust. Audit it once,
  cite it forever.
- **Never silently fold a trust-set assumption into meta-trust.**
  The β-reduction case is *deliberate*: we *could* expose β as an
  oracle observation, but it provides no value and adds enormous
  noise. We *don't* hide BLAKE3 in the framework, because doing so
  would silently couple the kernel's identity to a specific hash
  function.
- **Be honest about silent assumptions.** If a meta-trust component
  has implicit dependencies (e.g., "we trust libc's memcpy doesn't
  corrupt memory"), they're listed in the system's bottom-of-stack
  trust description — not in the kernel's trust set, but in the
  *operator's* trust set when running the kernel.

Where the line falls is a *deliberate engineering decision*, not a
mathematical one. The line moves over time as we learn what is and
isn't worth exposing.

---

## 5. β-reduction as the canonical meta-trust example

### 5.1 Why β is meta-trust

β-reduction `(λx. M) N ≡ M[N/x]` could, in principle, be modeled as
an oracle observation: `BetaReducerUUID.beta_reduces(t1, t2)`. The
framework would then require a meaning-axiom to interpret the
observation.

We don't do this because:

1. **β is purely syntactic.** It refers to no [store](./00-glossary.md#store),
   no external state, no I/O. The reduction `M[N/x]` is computed by
   walking the AST and substituting.
2. **The "meaning" is trivial.** The meaning-axiom would be
   `⋀t1 t2. BetaReducerUUID.beta_reduces(t1, t2) ⟹ t1 ≡ t2` — just
   spelling out that the reducer is correct.
3. **Adding it as an oracle gains nothing.** No one wants to *doubt*
   our β implementation while trusting the rest. If they doubt β,
   they doubt the whole kernel, and the right move is to read the
   Rust source.
4. **The audit cost is small.** Our β implementation is ~50 LoC of
   substitution + α-renaming via de Bruijn. Auditable in an
   afternoon.

So β is exposed as a *direct LF rule* — the (β) rule in
[`02-framework.md` §3.2](./02-framework.md#32-equality-rules) — and
the Rust impl is meta-trust.

### 5.2 The same logic applies to η

η is similarly pure-syntactic. Meta-trust.

### 5.3 The same logic applies to substitution

Capture-avoiding substitution under (all-e) is pure-syntactic. Used
internally by other rules; meta-trust.

### 5.4 The same logic applies to α-equivalence

De Bruijn-encoded terms are α-equivalent iff structurally equal.
The comparison is `==` on the `TermDef` enum. Meta-trust.

### 5.5 What it doesn't apply to

Counter-examples — operations that *look* trivially syntactic but
*shouldn't* be meta-trust:

- **Content addressing of terms.** "The hash of this term is `h`"
  is technically a syntactic operation (walk the term, hash). But
  exposing it as oracle observations means: (a) we can swap hash
  functions; (b) we can compare hashes across kernels with different
  hash choices; (c) the framework's TCB doesn't depend on BLAKE3.
  These are real benefits. So content addressing is **outside**
  meta-trust, despite being syntactic.

- **Type checking.** "This term has this type" is syntactic, but the
  framework computes types lazily and *records* them in the
  `TermProps` side table — that recorded type is the framework's
  view, and it's meta-trust because it gates well-formedness.

The principle: **meta-trust is what's worth the audit cost of
silent reliance**. Β-reduction is worth it (50 LoC of well-understood
code). BLAKE3 isn't worth it (we don't want to be locked to one hash
function; we want pluralism).

---

## 6. The hidden-meta-trust hazard

A subtle hazard: **implicit dependencies** that aren't named in
either meta-trust *or* the trust set.

Examples:

- **The RNG.** We name it in meta-trust ([§2.5](#25-rng-for-fresh-names)).
  But the RNG itself depends on OS entropy, which depends on the
  kernel's `/dev/urandom`, which depends on the hardware. None of
  these are listed.
- **The compiler.** Rustc, LLVM, the OS kernel, the CPU. None
  listed.
- **The clock.** Time-based primitives (sessions, lockouts) depend on
  a clock that may be wrong.
- **The signing scheme's underlying hash.** Ed25519 internally uses
  SHA-512. SHA-512's correctness is in meta-trust by transitive
  inclusion.

These all live in what we might call the **operator's trust set** —
the things the human running the kernel implicitly accepts. The
framework can't fully capture this; documentation does.

The honest move: **document the operator's trust set** in
[`docs/where-we-are.md`](../../../where-we-are.md) or a dedicated doc, so
operators can audit it. We aren't there yet; this is a planned
follow-up.

---

## 7. ElidePolicy: what and why

### 7.1 The problem

A kernel's local observations cite a *local instance* authority —
e.g., `MyKernel_WASM_Local`, a gensym ID for the specific WASM
process running in this kernel. A peer cannot refer to that gensym
(it's not exposed cross-kernel, by design).

But the peer *can* refer to the **abstract spec authority**
`WASMRun(H_B)`, derived deterministically from the binary's hash. If
the local kernel asserts a mount edge

```
⋀i o. MyKernel_WASM_Local.eval(i, o) ⟹ WASMRun(H_B).eval(i, o)
```

then any Thm using `MyKernel_WASM_Local.eval(i, o)` can be
*translated* via the mount edge to a Thm using
`WASMRun(H_B).eval(i, o)`. The peer sees a Thm in terms it
understands.

[**ElidePolicy**](./00-glossary.md#elidepolicy) is the framework
operation that performs this translation explicitly and per-export.

### 7.2 Why it's not silent

Silent elision — automatically substituting abstract for concrete at
every cross-kernel boundary — would be a [global lie](./00-glossary.md#trust-set):
the peer would think "WASMRun(H_B) says this" when really
"MyKernel_WASM_Local says this, *which the user claims* satisfies
the abstract spec."

The "*which the user claims*" matters: if the user is wrong about
the local instance satisfying the spec, the Thm is unsound. Silent
elision hides this dependency.

Explicit per-export elision **keeps the dependency visible**:

- The export carries the mount edge (as a meaning-axiom in the
  exported Thm's context).
- The peer sees: "Thm φ holds, *given* the mount edge from
  MyKernel_WASM_Local to WASMRun(H_B)."
- The peer can choose to discharge the mount edge (assume it true)
  or carry it as an open assumption.

### 7.3 The other direction: not eliding

For some Thms, the kernel *doesn't want* to elide — it wants the
peer to see "MyKernel_WASM_Local says X" as the actual claim. This
is when the peer is going to do their own re-checking, or when the
local instance's identity is relevant (e.g., audit-of-this-machine
Thms).

The default ElidePolicy is `Verbatim` (no elision). Substitution is
opt-in per export.

---

## 8. ElidePolicy: how it's structured

### 8.1 The API

```rust
pub enum ElidePolicy {
    /// No elision. Local authority names preserved verbatim.
    Verbatim,

    /// Strip local-only gensym authorities, replacing references
    /// with a placeholder error if any survive in the conclusion.
    /// Fails if any local-only authority is unbridgeable.
    EraseLocal,

    /// Substitute specific local authority IDs with abstract ones.
    /// The framework checks that a mount edge exists in the trust
    /// set for each substitution, and inlines the edge as a
    /// hypothesis in the exported Thm's context.
    SubstituteSpec(Vec<(AuthorityId, AuthorityId)>),
}

impl Framework {
    pub fn elide(
        &mut self,
        t: Thm,
        policy: ElidePolicy,
    ) -> Result<Thm, ElideError>;
}
```

### 8.2 `Verbatim`

No-op. Returns the Thm unchanged.

### 8.3 `EraseLocal`

Scans the Thm's conclusion + context for local-kind authority IDs.
If any are present, the operation fails (the Thm cannot be exported
verbatim without leaking gensym IDs).

Useful as a sanity check: "I think this Thm is fully abstract;
verify."

### 8.4 `SubstituteSpec`

For each pair `(local_id, abstract_id)`:

1. Look up the mount edge `⋀args. local.R(args) ⟹ abstract.R(args)`
   in the trust set. If absent, fail.
2. Substitute `local_id` for `abstract_id` in the Thm's conclusion.
3. Inline the mount edge as a hypothesis in the Thm's context, so
   the substitution is *justified* and the peer can see exactly
   what was assumed.

The result is a new Thm with:
- Conclusion: rewritten to use abstract authority IDs.
- Context: extended with the mount-edge hypotheses.

This is **honest** in the sense that the peer sees:
- The conclusion they can use directly (in their vocabulary).
- The assumption the exporter relied on (the mount edge).

The peer can independently verify the mount edge if they have a
reason to trust the local kernel's claim, or carry it as an open
assumption.

### 8.5 What happens to the unfolded mount edges

After elision, the exported Thm's context contains:

```
⋀args. local.R(args) ⟹ abstract.R(args)         (the mount edge)
```

This is in the [safe-axiom class](./00-glossary.md#safe-axiom-class)
on the *exporter's* side (the exporter owns the abstract authority
or has its capability). On the importer's side, it's just an
unattributed hypothesis — the peer can choose to assume it (trust
the exporter), discharge it via independent evidence, or carry it
open.

---

## 9. Worked example: exporting a Thm to a peer

### Setup

Local kernel L has proved:

```
T : Γ ⊢ ∃c. MyKernel_WASM_Local.eval(input, c) ∧ c_meets_spec(c)
```

…where `MyKernel_WASM_Local` is L's gensym authority for its WASM
process. L wants to send `T` to peer kernel K.

L holds in Γ:

```
M : ⋀i o. MyKernel_WASM_Local.eval(i, o) ⟹ WASMRun(H_B).eval(i, o)
```

…the mount edge bridging local-to-abstract.

### Elision

L invokes:

```rust
let t_exportable = framework.elide(t, ElidePolicy::SubstituteSpec(
    vec![(my_kernel_wasm_local_id, wasmrun_hb_id)],
))?;
```

The framework:

1. Locates `M` in the trust set.
2. Rewrites `T`'s conclusion: every occurrence of
   `MyKernel_WASM_Local.eval(...)` becomes `WASMRun(H_B).eval(...)`.
3. Adds `M` to the context of the new Thm.

`t_exportable` is:

```
T' : Γ, M ⊢ ∃c. WASMRun(H_B).eval(input, c) ∧ c_meets_spec(c)
```

### Signing and sending

L serializes `T'` and signs it:

```
sig = sign(L_privkey, serialize(T'))
send_to_peer(serialize(T'), sig, L_pubkey)
```

### Reception by K

K verifies the signature:

```
SigOracle.verifies(L_pubkey, serialize(T'), sig)  ✓
```

K trusts L as a peer (in K's trust set):

```
trust_L : ⋀msg. SigOracle.verifies(L_pubkey, msg, _)
       ⟹ msg deserializes to a valid Thm-shape
       ⟹ K imports the deserialized Thm
```

K imports `T'` into its own framework. K's view of the imported Thm:

```
T'' : Γ, M ⊢ ∃c. WASMRun(H_B).eval(input, c) ∧ c_meets_spec(c)
```

Note `Γ, M` — K can see *exactly* what L assumed.

### What K does with it

K has its **own** mount edge in K's trust set, claiming K's local
WASM runner also satisfies the WASMRun(H_B) spec:

```
M_K : ⋀i o. MyKernel_K_WASM_Local.eval(i, o)
       ⟹ WASMRun(H_B).eval(i, o)
```

K can:

- **Use `T''` directly** about `WASMRun(H_B)`. Discharges only `M`
  (L's mount edge) — K trusts L, so K is OK with this.
- **Test for agreement**: K runs the same binary in its own runner,
  observes the same input/output, derives `WASMRun(H_B).eval(input,
  c)` via `M_K`, *compares* against `T''`'s conclusion. If they
  agree, this is **independent corroboration** — a mirror.
- **Reject** if K doesn't trust L (then `T''` sits in K's context
  with an undischarged `M`-assumption; useful information, not a
  valid theorem).

This is exactly the
[mirror-and-edge model](../../../../ARCHITECTURE.md#4-the-mirror-principle-adequacy-as-reachability)
made operational.

---

## 10. The trust graph (who trusts whom)

### 10.1 The graph

- **Nodes:** kernel instances, identified by public key.
- **Directed edges:** "A trusts B" — A's root context contains a
  peer-trust assumption about B's public key.

Trust is *not* symmetric in general. K may trust L (importing L's
Thms) without L trusting K.

### 10.2 Trust flow

A Thm produced by L can flow to K only if:
- K trusts L (or trusts someone who trusts L, with that intermediate
  also serving the Thm via re-signing).
- The Thm's [trust set](./00-glossary.md#trust-set) is acceptable to
  K (K is willing to assume the same things L did).

### 10.3 Different trust contexts

A single kernel may maintain *multiple* root contexts, each with a
different trust set:

- **Production context.** Trusts only signed Thms from known peers.
- **Experimental context.** Trusts a researcher's unverified
  meaning-axioms.
- **Federated context.** Trusts a broader set of peers but only
  for non-critical claims.

The framework treats each context independently. A Thm proved in
context C₁ doesn't automatically transfer to C₂; the user re-derives
or imports it via an explicit edge.

### 10.4 Sub-kernels

A "kernel within a kernel" — e.g., a thread running its own
framework instance — is just another peer in the trust graph. Same
PKI rules apply. No special primitive.

This is the
"[PKI as universal substrate](./00-glossary.md#pki-public-key-infrastructure)"
property: multi-threading is not a kernel concern, it's a federation
concern.

---

## 11. Open questions

- **How to handle "transient" meta-trust components.** E.g., the
  RNG: it's meta-trust now, but if we ever support proving things
  about RNG choice, RNG selection might move into the trust set.
  Default: meta-trust for now; revisit if RNG-choice reasoning
  becomes a use case.

- **Whether ElidePolicy should support `Verbatim with audit`.** A
  policy that doesn't elide but *records* what would have been
  elided. Useful for debugging. Default: not in MVP; add if needed.

- **Cross-elision: substituting peer authorities for our own.** E.g.,
  "this Thm cites K's authority; rewrite to cite ours instead."
  Default: not supported. Cross-elision requires a mount edge *we*
  control, which is a different relationship.

- **Audit trail.** Should the framework keep a log of all elisions
  performed? Default: no; this is observability concern, not
  soundness.

- **Whether the Ed25519 meaning-axiom should be auto-pre-loaded.**
  Currently proposed: kernels ship with it pre-loaded by convention,
  but it's *structurally* a trust-set assumption (not meta-trust).
  Confirm.

- **Meta-trust documentation conventions.** Every framework
  function should be tagged in its rustdoc with whether it's
  meta-trust or trust-set-mediated. Establish a doc-comment
  convention.

- **Operator trust set.** A separate doc cataloging the implicit
  dependencies of the framework on its operating environment (RNG,
  compiler, OS). Not started yet.

- **What happens if a Thm's trust set is *empty***. (No assumptions
  at all.) Such a Thm follows purely from LF rules; it's a
  meta-theorem of the framework itself. These are rare in practice
  but should be exportable verbatim (no elision needed).

---

## 12. Cross-references

- [`00-glossary.md`](./00-glossary.md) — [meta-trust
  set](./00-glossary.md#meta-trust-set), [trust set](./00-glossary.md#trust-set),
  [ElidePolicy](./00-glossary.md#elidepolicy), TCB.
- [`01-conventions.md`](./01-conventions.md) §3 — [fresh names](./01-conventions.md#3-fresh-names),
  whose collision-freedom assumption sits in trust set.
- [`02-framework.md`](./02-framework.md) — the framework crate, whose
  Rust impl *is* the meta-trust set.
- [`03-authority.md`](./03-authority.md) — authorities, observations,
  meaning-axioms. Most trust-set assumptions are about authority
  observations.
- [`04-store.md`](./04-store.md) — stores; scoped crypto assumptions
  in the trust set.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §1 (TCB), §13 (invariant
  checklist) — the original TCB framing; refined here into the
  two-level distinction.
- [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §4 (mirror principle) —
  trust by reachability from silvered nodes; this doc operationalizes
  it via the trust graph and elision.
- (Planned) [`09-federation.md`](./) — the signed-Thm exchange
  protocol that uses ElidePolicy at export and accepts trust
  assumptions at import.
- (Planned) Operator trust set doc — implicit meta-trust dependencies
  on hardware, OS, compiler.

# Modified HOL

> **STATUS: WORKING NOTE — extracted from session conversation.** A
> companion note to the
> [layered-framework proposal](../README.md). Captures what
> "modified HOL" means as the design target, what modifications are
> committed vs. speculative, and the broader three-layer / reverse-math
> architecture they fit inside. Not committed; under active mining.
> Read alongside [`facts-not-proofs.md`](./facts-not-proofs.md) — both
> are load-bearing principles for the bottom layer.

The phrase "modified HOL" surfaced in the
[2026-06-06 session](../../shared-backbone/notes/session-2026-06-06.md)
as the design target for the HOL layer of the layered framework, and
as the reason `covalence-hol` is the *easiest* shell (rather than just
the first). This note unpacks what it means.

---

## Contents

1. [The short form](#1-the-short-form)
2. [The modifications](#2-the-modifications)
3. [The three-layer stack](#3-the-three-layer-stack)
4. [Reverse-math workflow](#4-reverse-math-workflow)
5. [What this implies for the kernel](#5-what-this-implies-for-the-kernel)
6. [What this implies for the HOL shell](#6-what-this-implies-for-the-hol-shell)
7. [Open questions](#7-open-questions)
8. [Cross-references](#8-cross-references)

---

## 1. The short form

Covalence's HOL is **HOL + observations**, with **no privileged root
context**, and with **purely-syntactic well-formedness** throughout.
The modifications are exactly what's needed to make oracle
observations a first-class part of the logic (rather than a side-channel
the kernel tags with `mk_thm`-style oracle marks), and to make
content-addressing of theories work without canonicalization games.

The logical *strength* of the modified HOL is the same as classical
HOL — every modification has a derivation showing it's
expressively equivalent to a standard HOL construct. The
modifications buy *uniformity, content-addressability, and
ergonomics for the metatheoretic workflow*, not new theorems.

---

## 2. The modifications

Four committed, plus a category of speculative-but-likely.

### 2.1 First-class observations

The kernel's [observation](../00-glossary.md#observation) primitive —
`O.R(args)` asserted under [authority](../00-glossary.md#authority)
`O` owning relation `R` — is **baked into the logic**, not bolted on
as a side-channel.

In HOL Light, an oracle result enters via `mk_thm`, which tags the
resulting `thm` with the oracle's identity for audit but is otherwise
indistinguishable from an axiom. The Covalence move is different: an
observation is its own kind of fact, with its own well-formedness
rule (per [`02-framework.md`
§3.3](../02-framework.md#33-observation)), and it lives in the
hypothesis context like any other assumption. There is **no
"this thm was produced by oracle X" tag** — the oracle's identity
appears *inside* the conclusion's term (as the authority's ID) and
*in* the hypothesis (as the observation itself). What you do with the
observation is up to you: discharge via a
[meaning-axiom](../00-glossary.md#meaning-axiom), reason about its
shape directly, transport it through morphisms, etc.

**Why this is "modified HOL" and not "HOL + oracle interface."**
Because the *logic* changes — the language of well-formed terms
includes observation shapes, and the inference rules include the
observation introduction rule. A pure HOL Light kernel can't express
"the observation `O.R(args)` was made"; modified HOL can.

### 2.2 Oracle naming discipline

For observations to be first-class, oracles need first-class
identities. The discipline:

- An [authority](../00-glossary.md#authority) is a
  [`Name256`](../00-glossary.md#name256) identity (per
  [`01-conventions.md`](../01-conventions.md)) plus a set of owned
  relation names.
- The authority's identity is *either* an RNG-fresh gensym
  ([local authority](../00-glossary.md#authority), un-shareable across
  kernel instances) *or* a public key
  ([keyed authority](../00-glossary.md#authority), shareable via
  cryptographic signature).
- Relation names are short strings (`"eval"`, `"hashed"`, `"signed"`,
  `"in_store"`) scoped to their owning authority — i.e., disambiguated
  globally as `(authority_id, relation_name)`.
- The framework enforces, at the observation rule, that the relation
  being written is in the authority's owned set ([safe-axiom
  class](../00-glossary.md#safe-axiom-class)).

This is the **discipline for naming oracles** that the user flagged
as a thing-we-need. It's not novel cryptographically (it's basically
PKI), but as a *logic* discipline it's the move that lets
observations be first-class without a privileged tagging mechanism.

### 2.3 No privileged root context

The empty context is **not special**. Specifically:

- There is no "axiom" vs "assumption" distinction at the kernel level.
  An "axiom" is just an assumption you've decided not to discharge.
- Well-formedness is purely syntactic
  ([`SYNTACTIC-WF`](../../../../../AGENTS.md) invariant from
  AGENTS.md): a type or term is well-formed by structural recursion,
  *never* inspecting any provability-in-empty-context claim.
- Any primitive that would normally inspect the root context is
  reworked via the [disjunct trick (§2.4
  below)](#24-disjunct-trick-for-subset-type-formation) — the side
  condition becomes an object-level disjunct on the result.

This is the **load-bearing modification** for the reverse-math
workflow ([§4](#4-reverse-math-workflow)): if the root context were
privileged, every theory-to-theory morphism would have to drag along
"this was proven in the empty context" vs "this was proven under
assumptions" as a separate distinction. Without root privilege, every
theorem is *uniformly* "true under its hypothesis set" — including the
empty set.

The corollary the user emphasized: **no special oracle tags.** An
oracle result is just a Thm whose hypothesis is the observation; if
you discharge the observation via a meaning-axiom, the meaning-axiom
becomes the hypothesis; nothing special happens.

### 2.4 Disjunct trick for subset-type formation

The concrete example the user gave for "modified HOL."

**Classical HOL.** To make a subset type for predicate `P : α → bool`,
you must *first* prove `∃x. P x`. Type formation is *contingent on
provability*. This is the textbook approach: a non-empty predicate
makes a non-empty type; an empty predicate has no type to embed into.

**Modified HOL.** You **always** make a subset type for `P`. The
embedding satisfies:

- `abs (rep a) = a` unconditionally.
- `rep (abs x) = x ↔ P x ∨ ¬∃y. P y`.

The second axiom is the disjunct trick: if `P` is inhabited (the
classical case), the disjunct collapses to `P x` and you have the
ordinary subset-type semantics. If `P` is empty, the disjunct
collapses to `True` and `abs/rep` becomes an arbitrary bijection (the
type becomes degenerate but coherent).

**Equivalence.** Logical power is the same as classical HOL — any
classical-HOL subset-type derivation works in modified HOL; the
disjunct is automatically satisfied when classical HOL would have let
you form the type. Modified HOL also lets you form the *uninhabited*
subset type, but you can't derive anything useful from it (you'd need
`∃y. P y` to instantiate any quantifier into it, which you can only
get back from the disjunct — and the disjunct's other branch is
`¬∃y. P y`, so you're stuck).

The user's reformulation: the modified subset type for `P` has the
same logical content as the classical subset type for `Q x = (¬∃y.
P y) ∨ P x`. The disjunct trick is just choosing the modification
that lives in the *type-formation rule* rather than in every use
site's predicate.

**Why this matters.** Type formation is now **purely syntactic** —
the kernel checks `P : α → bool`, local closure, no free term
variables, and forms the type. No provability obligation; no
contingent rule. The empty context stops being privileged at the
type-formation layer too, not just at the inference-rule layer.
([`ARCHITECTURE.md` §2.4](../../../../../ARCHITECTURE.md) has the long
rationale.)

### 2.5 Speculative: content-addressing-friendly representations

The user flagged a category of modifications they "may or may not"
make, depending on whether equivalence with standard HOL can be
preserved:

- **E-graph representation modifications** — to make the kernel's
  internal data structures easier to serialize, deserialize, and
  mutate efficiently. The current
  [Phase P](../../../../prop-egraph-design.md) prototype goes some
  distance here; more modifications may follow.
- **Term-canonicalization tweaks** — possibly. The current
  [Phase H decision](../../../../refactor-plan.md) bets *no*
  canonicalization (hash the linear buffers; injective on `hash → bytes`,
  not on `bytes → hash`). This may flip if practical experience shows
  the non-canonical form is too painful.
- **Bottom-layer simplifications** — the user noted that "at the
  bottom of the stack we shouldn't" modify for content-addressing.
  This suggests the **foundation layer** stays as plain as possible
  (LF, no modifications); the *HOL layer* gets the modifications; the
  *current-theory layer* gets whatever it needs. Modifications live in
  the middle.

Status: speculative. The principle (preserve equivalence with
standard HOL; modify only where it buys uniformity or
content-addressability) is firm. The specific modifications are
TBD as the implementation surfaces real friction.

> Per auto-memory `phase-h-no-normalization`: the current Phase H
> bet is "no canonicalization; hash linear arena buffers; injective
> `hash → bytes`, not `bytes → hash`." This is the baseline; any
> §2.5 modification would need to preserve or improve on it.

---

## 3. The layered structure

The bigger architectural claim that "modified HOL" lives inside.

The user's framing has stabilized as **bottom + top**, with the bottom
*optionally* factored into inner + outer halves to manage complexity.
The two halves of the bottom are *not* swappable independently within
a single kernel session (think Isabelle/HOL — Pure and HOL are
distinguishable but locked in once chosen); the factoring exists for
**audit clarity**, not modularity.

```
┌────────────────────────────────────────────────────────┐
│  Theories + morphisms + interpretations                │
│    LOTS, CHANGING, untrusted                           │
│                                                        │
│    classical HOL, Isabelle/HOL, ZFC, HoTT, $THEORY;    │
│    morphisms between them (MVP-scope);                 │
│    categorical interpretations into model classes;     │
│    oracle programs + their soundness proofs            │
├────────────────────────────────────────────────────────┤
│  Bottom layer: enables metatheory                      │
│    UNCHANGING, HOL-strength, TCB-discharged             │
│                                                        │
│  ┌──────────────────────────────────────────────────┐ │
│  │  Outer: + content-addressing assumption package  │ │
│  │                                                  │ │
│  │  "what does the SYSTEM believe under these       │ │
│  │   assumptions?"                                  │ │
│  │                                                  │ │
│  │  Operational machinery for hashes, signatures,   │ │
│  │  stores, ZKPs, range proofs. Each rule is        │ │
│  │  discharged by an inner-layer ASSUMPTION rather  │ │
│  │  than baked-in axiom.                            │ │
│  ├──────────────────────────────────────────────────┤ │
│  │  Inner: pure meta-meta-reasoning    TCB          │ │
│  │                                                  │ │
│  │  "what does THIS LOCAL NODE believe?"             │ │
│  │                                                  │ │
│  │  Small, auditable, performance-preserving.       │ │
│  │  No content addressing — only assumptions        │ │
│  │  ABOUT content addressing (which the outer       │ │
│  │  layer discharges).                              │ │
│  └──────────────────────────────────────────────────┘ │
│                                                        │
│  Can also be implemented as a single layer;            │
│  factoring is for AUDIT, not modularity.               │
└────────────────────────────────────────────────────────┘
```

### 3.1 Bottom-inner: pure meta-meta-reasoning

The actual TCB. "What does this local node believe?" Pure logic, no
content addressing, no infrastructure.

**Defining properties** (the user's emphasis):

1. **Simple, auditable implementation.** Small enough to read
   end-to-end; each rule's correctness obvious by inspection. The
   [silvered node](../00-glossary.md#silvered-node).
2. **Doesn't constrain performance of the layers above.** Operations
   must bottom out in primitives fast enough for practical use.
3. **Widely accepted logic — HOL is the natural balance, but not a
   hard ceiling.** The constraint is "use a logic the mathematical
   community already trusts," because we're going to *work inside*
   this logic day-to-day. HOL is the default — well-understood,
   strong enough for everything we need, comfortable to write in.
   Stronger logics (e.g., ZFC) are acceptable if they simplify the
   *implementation*; the same goes for weaker (Pure LF). Bespoke
   logics that need their own audit story are out.

> **The user's framing (combined, verbatim):** *"The bottom
> foundation's core property is not weakness (though it shouldn't be
> stronger than HOL) but having a simple, auditable implementation
> which doesn't constrain the performance of our system."* + *"I'm
> also fine with stronger-than-HOL if it makes implementation simpler
> (so long as it's still something widely accepted like ZFC), since
> remember the idea is we're working inside the prover. But HOL is a
> nice balance point, and very well understood."*

The first quote treated HOL as an upper bound; the second relaxed
that. The synthesized constraint: **widely-accepted logic +
implementation simplicity + daily-use ergonomics**, with HOL as the
default if no other constraint dominates.

**What's in the inner.** LF-style rules for meta-`⟹` and meta-`⋀`,
equality with congruence rules, β/η, definitions, the
[disjunct-trick subset types](#24-disjunct-trick-for-subset-type-formation),
[no-root-privilege discipline](#23-no-privileged-root-context). **No
observation primitive, no `Authority`, no `Name256`** — those land in
the outer.

**What it *contains as assumptions* (not as built-in rules).** Things
about content addressing the outer layer will operationalize:

- "There are no hash collisions *in the store*."
- "There are no false ZKPs *in the store*."
- "Signatures verify as the meaning-axiom claims, *for this key*."
- "Range proofs validate, *for this scheme*."

These are *assumptions* (per the user's lean: "assumptions mean they
can be communicated and changed") expressible in the inner-layer
logic. The inner doesn't *implement* hashing or ZKP verification; it
just provides the language to talk about their properties.

**Implication for crate selection.** Inner-bottom could be Pure-style
LF *or* plain HOL — the choice is driven by implementation simplicity
and performance, not logical purity. Plain HOL implemented as one
small kernel may end up simpler than "Pure LF + HOL as object theory
on top," even though the latter sounds more modular. The decision is
deferred.

### 3.2 Bottom-outer: content-addressing assumption package

The inner bottom plus the **operational machinery that discharges the
inner's content-addressing assumptions**.

"What does the system believe under these assumptions?" — once you
trust the standard assumption package (no collisions, no false ZKPs,
signature scheme works, etc.), the outer layer gives you ergonomic
operational primitives for hashing, signing, storing, range-proving,
ZKP-verifying.

**The defining move.** The outer layer is **not** a bag of new axioms
extending the inner. It's a bag of **operational implementations**
where each implementation discharges *one assumption* from the inner
layer. If the implementation is buggy, the corresponding assumption
becomes provably false (a "we lied about no collisions" event), which
is an **honest failure mode**, not silent corruption.

This is the global-no-lies discipline applied at the foundation:
**there are no foundation-level lies either, only scoped assumptions
that can be discharged or refuted**.

**What's in the outer.**

- Hash function operational primitives (BLAKE3, SHA-256, …) →
  discharge "hash relation behaves as collision-resistant function".
- Signature verification primitives (Ed25519, …) → discharge
  "signature relation behaves as the signature scheme spec".
- Store operational primitives (read, write, membership, subset
  witness construction) → discharge "store rules behave as set
  operations".
- ZKP verification primitives → discharge "ZKP relation behaves as
  the proof system spec".
- Range proof primitives → discharge "range relation respects bounds".
- The four modifications' content-addressing pieces:
  [first-class observations (§2.1)](#21-first-class-observations) +
  [oracle naming discipline (§2.2)](#22-oracle-naming-discipline) —
  these are operational, not pure-logic.

**Why factor this way.** The user's framing: *"the bottom layer
itself is very complex, as it contains all this content addressing
stuff (e.g. range proofs) which have a big TCB."* Range proofs and
ZKPs are operationally heavy (elliptic curve arithmetic, constraint
system verification); putting them in the outer with their
correctness reduced to one assumption-per-scheme keeps the inner
small enough to audit by inspection.

**Could be one layer.** The user noted: "we can also just do it as
one layer" — implementing inner and outer together is a valid
implementation choice. The factoring is for **conceptual / audit
clarity**, not enforced by code structure.

### 3.3 Top: theories, morphisms, interpretations

Everything that **changes**. Lots of theories; many morphisms between
them; interpretations into categorical models. All untrusted in the
LCF sense — soundness comes from constructional Thms in the bottom,
not from these theories being correct.

**The morphism layer is MVP-scope** (per the user's explicit
decision in this session). This is what makes the reverse-math /
multiple-models workflow operational rather than aspirational.

The "HOL/HOL/$THEORY" and "Isabelle/HOL/$THEORY" stacks the user
mentioned earlier are **all in this layer**:

- **Leftmost slot** — your chosen "standard metatheory" (classical
  HOL Light, Isabelle/HOL, ZFC, HoTT, …). Imported into the bottom
  as a theory.
- **Middle slot(s)** — refinements / specializations.
- **Rightmost slot ($THEORY)** — your specific current concern.

Multiple stacks coexist on the same bottom. Morphisms between stacks
transport theorems across.

### 3.4 Why the bottom needs HOL strength

Three independent justifications, each independently sufficient:

1. **To reason about derivations and morphisms.** Theories-as-objects,
   morphisms-between-theories — these need at least HOL strength to
   formalize comfortably. Pure LF can express them only awkwardly.
2. **To formalize executor semantics.** The
   [self-extending-oracles pattern (§3.7)](#37-self-extending-via-proven-oracles)
   requires HOL strength to express WASM operational semantics and
   prove "this bytecode implements this spec" as a theorem.
3. **To formalize categorical-semantics interpretations.** Lambek/Scott
   style "theorem in T → valid in every model of T" theorems need HOL
   strength to be stated and proved at industry-standard granularity.

All three want the same logical power for related-but-distinct
reasons. Together they justify the upper bound being HOL, not
something weaker like equational logic.

### 3.5 Borrowing power via `Con(T)`

The user's example:

> *We can then "borrow more power" by assuming theory T is consistent
> — e.g. "assuming that there does not exist a proof in ZFC that
> {} = {{}}".*

The bottom is, by Gödel, weaker than ZFC. If you need ZFC's strength,
you don't make ZFC the foundation — you stay in the bottom, assume
`Con(ZFC)` as a hypothesis, and prove "ZFC ⊢ P" results without your
foundation actually being ZFC.

The concrete formulation — "ZFC does not prove `{} = {{}}`" — is
equivalent to `Con(ZFC)`: if ZFC could prove `⊥`, it could prove
anything including `{} = {{}}`. Specifying a single false-looking
formula makes the assumption operational rather than a meta-claim.

This is **scope-limited strength borrowing**: the foundation stays
fixed; the *trust set* gains access to stronger reasoning, with the
dependency explicit in every theorem's hypothesis list. If
`Con(ZFC)` turns out to be wrong, theorems that borrowed it become
Thms-with-falsified-hypotheses — still Thms, just less useful. Per
[`ARCHITECTURE.md` §3](../../../../../ARCHITECTURE.md) ("Need more
power? Borrow `L`'s strength by assuming '`L` consistent'").

The same move applies to any theory: `Con(HoTT)`, `Con(CIC)`,
`Con(YourLibrarysAxioms)`. The mirror principle suggests
cross-checking — if `Con(ZFC)` and `Con(NF)` give you the same
theorem via independent edges, confidence rises.

### 3.6 What changes vs what doesn't

| Component | Stability | TCB role |
|---|---|---|
| Bottom-inner | unchanging | **direct TCB** (audited by inspection) |
| Bottom-outer | unchanging | **TCB-by-assumption-discharge** (audited via the inner-layer assumptions it implements) |
| Top layer (theories, morphisms, interpretations, oracle programs) | LOTS, CHANGING | **not TCB** (constructional soundness via bottom-layer rules) |

**The TCB ratchet.** The inner is audited once and never grows. The
outer's correctness reduces to "do the inner-layer assumptions hold?"
— a small fixed set the user audits. The top never enters the TCB.

A new hash scheme = a new outer-layer implementation = one new
inner-layer assumption to audit. A new theory = zero TCB change. A
new oracle (under the self-extending pattern, §3.7) = zero TCB
change.

### 3.7 Self-extending via proven oracles

The HOL-strength of the middle layer pays off concretely: it lets the
system natively reason about the operational semantics of WASM (and
other executors), which lets **new oracles enter the system by proof
rather than by assumption** — the kernel extends itself without
growing the TCB.

**The standard oracle pattern (without self-extension).** New oracle
`Z` computes function `f`. To use `Z`'s observations, the user adds a
meaning-axiom: *"`Z`'s observation that `f(x) = y` is true."* The
trust set grows by one assumption per oracle. Over time, the trust
set bloats; each added oracle is a new thing to audit.

**The self-extending pattern.** With HOL-strength in the middle:

1. **Formalize WASM operational semantics once**, as a theory `T_wasm`
   in layer 3. Either import a mechanization (WasmCert-Isabelle,
   WasmCert-Coq) or develop one locally.
2. **One meaning-axiom for `T_wasm`:** "`T_wasm` correctly describes
   WASM execution as performed by the executor we trust." Audit this
   axiom carefully; it's the only WASM-related thing in the trust set.
3. **New WASM oracle `Z` arrives.** Its bytecode `B` is a
   content-addressed blob. Prove (in modified HOL, using `T_wasm`):
   *"for all inputs `x`, executing `B` yields `f(x)`."*
4. **`Z`'s observations are discharged by this theorem**, not by a
   fresh meaning-axiom.

The trust set grew by **zero**. The theorem set grew by **one**. The
TCB did not change.

**Why this works.** The middle layer is HOL-strength specifically
because that's enough to formalize operational semantics and prove
program correctness. Pure LF is too weak; you'd need to embed each
oracle's spec as an axiom rather than proving it. HOL (or stronger)
lets you say "the WASM program with hash `H` implements specification
`S`" *as a theorem*.

**Why this matters for long-term sustainability.**

- **TCB stays flat.** Layers 1+2 are unchanged regardless of how many
  oracles you add. A system with 10,000 WASM oracles has the same TCB
  as a system with 10.
- **Trust set centralizes.** One assumption (`T_wasm` describes WASM
  correctly) supports unlimited oracles. Adding a new oracle adds
  proof effort, not trust burden.
- **Mirror principle applies.** Two independent WASM semantics
  formalizations (WasmCert-Isabelle and a local one) agreeing on an
  oracle's fragment → consilience without trusting either alone. Per
  [`ARCHITECTURE.md` §5.2](../../../../../ARCHITECTURE.md).
- **Generalizes to other executors.** Same pattern works for x86,
  RISC-V, a future RISC-V-on-WASM emulator: formalize the executor's
  semantics; prove each oracle's program matches its spec.
- **Connects to base-shift.** The whole development is parametric in
  the WASM semantics formalization; swapping `T_wasm` for a refined
  version is a layer-3 base-shift, not a kernel rewrite.

**What this requires.**

- Middle layer strong enough to formalize operational semantics —
  HOL is the lower bound that makes this comfortable.
- Layer 3 theory `T_wasm` exists, is well-formed, has a clear
  interface to the executor's actual implementation.
- Practical proof tooling for "this WASM bytecode implements this
  spec" — tedious but mechanizable. Most oracle soundness proofs
  will reuse generic verified-component templates rather than be
  ad-hoc.

**What this doesn't solve.**

- The WASM executor implementation is still trusted (via `T_wasm`'s
  meaning-axiom). But it's trusted *once*, not per-oracle.
- Proving correctness of arbitrary WASM bytecode is hard work; the
  payoff is that the work is *checked*, not *assumed*.
- Some oracles will resist proof (a learned heuristic, an SMT solver
  with no clean spec). Those still enter as meaning-axioms; the
  self-extending pattern is the *preferred* mode, not the only mode.

> **The full picture.** The trust set under self-extension looks like:
> `{ Con(modified HOL), T_wasm describes WASM, [optionally Con(T)
> for borrowed-strength theories] }` — a small, stable set, with
> arbitrarily many oracles riding on top via proof. Contrast with the
> classical pattern where the trust set grows linearly with oracle
> count.

### 3.8 Format graph: shell traits as interfaces

A specific instance of the shell pattern the user emphasized: **the
HOL Light API is an *interface*, not an implementation choice**, and
the same applies to every other proof-format API (Metamath, Lean,
Isabelle, SMT-LIB).

Each format gets a Rust trait (in Covalence:
[`HolLightKernel`](../../../../../crates/covalence-hol/src/traits.rs)
for HOL Light). Multiple backends implement the same trait:

1. **Direct kernel backend.** Drive the framework's primitives
   directly. (Today:
   [`HolPrim`](../../../../../crates/covalence-shell/src/hol.rs) —
   routes HOL Light operations to `covalence-kernel`.)
2. **Self-contained reference backend.** A pure-Rust implementation
   of the format's logic, independent of the framework. Useful for
   differential testing. (Today:
   [`HolKernel`](../../../../../crates/covalence-hol/src/light.rs).)
3. **Driving the format *as a theory* in the kernel.** Implement the
   format's API by treating it as a [layer-3 theory](#33-top-theories-morphisms-interpretations)
   inside the framework's modified HOL. Each HOL Light operation
   translates to an operation in that theory. (Planned — lands once
   the framework has matured.)
4. **Driving via a different foundation.** E.g., implementing
   `HolLightKernel` by translating to ZFC operations. **Normally
   you'd use a morphism instead** — prove things in HOL, transport
   via a HOL→ZFC morphism — but the direct-implementation path is
   architecturally available.
5. **Null backend.** Terms and types work; all proof rules return
   "unsupported." The LCF discipline at the API level: a no-op
   implementation must compile. (Today:
   [`NullKernel`](../../../../../crates/covalence-hol/src/null.rs).)
6. **Recording backend.** Wraps another backend; logs the
   rule-application trail to a sidecar for export. (Planned;
   per [`facts-not-proofs.md` §"Optional proof recording"](./facts-not-proofs.md).)
7. **Remote backend.** Implements the trait by RPC against another
   kernel instance. (Planned; federation pathway.)

**Implications for trait design.**

- **Shell traits stay pure to their format.** `HolLightKernel`
  contains exactly the classical HOL Light operations — no
  observations, no disjunct trick, no content-addressing primitives.
  These are how OpenTheory expects to talk to HOL.
- **Modified-HOL features live on a different trait** (in
  Covalence, the `Prover` trait in `covalence-shell`). A backend
  with capability beyond classical HOL implements *both* traits; an
  OpenTheory consumer only sees the classical surface.
- **Morphisms between formats are theorems, not trait
  implementations.** Translating Lean to HOL is normally a morphism
  in the framework's morphism layer (a theorem), not a backend
  implementing `HolLightKernel` via Lean primitives. Both are
  possible; the morphism approach scales better because the
  translation is proved once and reused.
- **The format graph mirrors the theory graph.** Many formats; many
  backends per format; many morphisms between formats. The framework
  is the substrate that holds the graph together.

This is what makes the proof-format ecosystem work: one substrate,
many shell traits as interfaces, many backends per interface, many
morphisms between formats.

---

## 4. Reverse-math workflow

**The core workflow is proving morphisms between theories** and
proving things in the simplest theory we can — reverse-math style.

[Reverse mathematics](https://en.wikipedia.org/wiki/Reverse_mathematics)
classically asks: "what axioms are *strictly necessary* for theorem
T?" The answer is a hierarchy — RCA₀ ⊂ WKL₀ ⊂ ACA₀ ⊂ ATR₀ ⊂ Π¹₁-CA₀
— and a theorem's *home* is the weakest subsystem that proves it.

The Covalence move: **make this the prover's primary mode**. Not as a
research curiosity, but as the day-to-day workflow.

### 4.1 Why reverse math here is not academic

The user emphasized:

> *The reverse math here is not just academic — it also means we can
> take a theorem "P is provable in T" and then interpret that in many
> different models of T — in the style of "Categories for Types",
> where algebraic rewrites can be interpreted in any Cartesian
> category.*

The point is **categorical semantics at scale**:

- A theory `T` has an *internal language*.
- Any category `C` with the structure to model `T`'s internal language
  is a *model* of `T`.
- A theorem `P` provable in `T` is *valid in every model* of `T` — a
  generalized soundness theorem (Lambek/Scott; Crole's *Categories
  for Types*).
- The weaker `T` is, the *more* categories model it. Equational logic
  models in any Cartesian category; simply typed λ-calculus models in
  any Cartesian closed category; HOL models in any elementary topos;
  ZFC models in only set-theoretic universes.
- **Reverse math = maximum categorical reach.** Finding the weakest
  `T` that proves `P` is the same operation as finding the *broadest
  class of categories* in which `P` interprets.

This makes the workflow concrete and useful:

- A user proves a result in equational logic. **For free**, the result
  holds in every Cartesian category — categorical algebraists,
  topologists, type theorists, all consume it without re-proof.
- A user proves a result in classical HOL. The result holds in every
  topos satisfying classical principles (Boolean toposes).
- A user proves a result in modified HOL with `Con(ZFC)`. The result
  holds in any model where ZFC is consistent — narrower, but still
  more than ZFC's "the" universe.

The morphism layer is *not optional decoration*; it's the mechanism
that lets a single proof feed many model-class consumers.

### 4.2 What this implies practically

- **Theories are first-class objects.** Each is a HOL theory in the
  layered-framework sense; each has an identity (`Name256`); each is
  serializable as a content-addressed artifact.
- **Morphisms are first-class objects.** Embeddings,
  equiconsistencies, conservativity proofs — all are theorems *in*
  the middle layer, *about* theories. Per
  [`ARCHITECTURE.md` §4](../../../../../ARCHITECTURE.md), they're the
  edges of the
  [logic graph / mirror](../00-glossary.md#mirror) graph.
- **Model-class interpretations are also first-class.** "Theory `T`
  models in every category satisfying structure `S`" is a theorem in
  the middle layer. Lambek/Scott style: STLC interprets in any CCC;
  equational logic interprets in any Cartesian category; HOL
  interprets in any topos. These interpretations form their own kind
  of edge in the morphism graph — *into model classes*, not just
  *between syntactic theories*.
- **Proving morphisms efficiently is the bottleneck.** Most user
  work goes into morphism construction. The framework needs
  ergonomics for this — the commutative-diagram API from
  `ARCHITECTURE.md` §4.2 is the obvious target.
- **"Simplest theory" replaces "the theory we work in."** Instead of
  picking ZFC and proving everything there, you pick the weakest
  theory each particular theorem needs. Transport along morphisms
  to get the strongest statement-of-record; transport along model
  interpretations to apply the result in arbitrary semantic settings.

### 4.3 Why modified HOL is well-suited to this

- First-class observations
  ([§2.1](#21-first-class-observations)) mean "this theorem requires
  an oracle to be honest" is uniformly expressible across all
  theories at all stack positions. You can transport "uses the BLAKE3
  collision-resistance oracle" along a theory morphism the same way
  you transport any other hypothesis.
- No root-context privilege ([§2.3](#23-no-privileged-root-context))
  means a theorem provable "in $WEAK under assumptions H" transports
  to a theorem in $STRONG under assumptions H without any
  context-fiddling — context is just a hypothesis set, not a special
  kind-of-thing.
- Disjunct-trick subset types
  ([§2.4](#24-disjunct-trick-for-subset-type-formation)) mean type
  formation is the same in every theory; morphisms between theories
  don't have to negotiate "what counts as a valid type here."
- HOL-strength middle layer
  ([§3.2](#32-middle-layer-modified-hol-with-content-addressing)) is
  strong enough to formalize categorical-semantics interpretation
  theorems. Pure LF can state them only awkwardly; HOL can state
  *and prove* them at industry-standard granularity.

---

## 5. What this implies for the kernel

The kernel (the
[framework crate](../02-framework.md)) needs to support:

1. **Observation as a built-in term shape.** Not just as a hypothesis
   that *looks* like `O.R(args)` — but as a *kind of term* the
   well-formedness check recognizes, with the (observe) rule producing
   it. This is already in
   [`02-framework.md` §3.3](../02-framework.md#33-observation).
2. **Authority bookkeeping in the trust boundary.** Authority IDs,
   owned-relation registries, safe-axiom-class check. Already in
   [`02-framework.md` §4](../02-framework.md#4-authorities).
3. **Disjunct-trick subset types.** Type formation rule must produce
   the unconditional version. This belongs in the HOL shell, not the
   foundation — the foundation doesn't have subset types. But the
   foundation must support whatever primitive the shell uses to
   *implement* subset types (probably definitions + axioms).
4. **No-canonicalization content hashing for theories.** Per
   auto-memory `phase-h-no-normalization`. Theory identity = hash of
   linear arena buffers. This composes with the three-layer stack:
   each layer hashes its own contents; morphisms between layers
   reference the input theories by hash.
5. **First-class theory objects.** A "theory" needs to be a value the
   kernel manipulates — load, serialize, name, import, hash. This is
   the [arena/freeze/import](../../../../prover-architecture.md) machinery
   the legacy kernel already had in primitive form.

---

## 6. What this implies for the HOL shell

This is why
[`covalence-hol`](../../../../../crates/covalence-hol) is the
**easiest** shell (the user's word), not just the first:

- **The HOL shell *is* the standard-metatheory layer.** It implements
  the four modifications (§2.1–§2.4) on top of the foundation's
  primitive rules. The user's mental model of "HOL" is the modified
  version — so the shell's job is to *expose* the modifications, not
  to *paper over* them.
- **The legacy `covalence-hol` is closer to modified HOL than it
  looks.** Per
  [`where-we-are.md`](../../../../where-we-are.md), `covalence-hol`
  is HOL-Light-shaped with its own arena, term/type system, and
  LCF-style rules. Reshaping it into a shell over `covalence-kernel`
  is a port, not a redesign — the modifications (especially the
  disjunct trick) are already in the design target.
- **OpenTheory import is the validation.** OpenTheory articles are
  *classical* HOL Light derivations. Modified HOL is conservative
  over classical HOL, so every OpenTheory article should be
  importable; importing the standard prelude is a strong
  validation that the modifications haven't broken anything. (Per
  auto-memory `opentheory-define-type-op`,
  some article specs need wrapping in the interpreter for the
  modified form — that wrapping is the visible cost.)
- **Future shells (SAT, SMT, Lean, Metamath) follow the same
  pattern.** Each format becomes a shell over modified HOL (or
  over the foundation directly, if the format doesn't need HOL's
  strength). The shell's job is to translate the format's facts into
  modified-HOL Thms.

---

## 7. Open questions

Surfaced in the session, not yet resolved.

### About the modifications

- **Which §2.5-speculative modifications are likely to land?** The
  user said "may or may not" for E-graph + canonicalization tweaks.
  Concrete criteria for accepting one: "preserves logical equivalence
  with standard HOL" + "removes a content-addressing or serialization
  pain point we've actually hit."
- **Is the observation primitive part of HOL or part of the
  foundation?** The user's framing says HOL = HOL + observations.
  But the framework's `(observe)` rule lives at the foundation
  level (per [`02-framework.md`](../02-framework.md)). Resolution:
  observations are a *foundation* primitive available to every layer;
  HOL "uses" them; "modified HOL" includes the discipline for how a
  HOL theory uses them. Confirm.
- **Are there modifications specific to enabling the reverse-math
  workflow (beyond §2.3 no-root-privilege)?** E.g., something that
  makes theory-to-theory morphisms cheaper to state or prove?

### About the three-layer stack

- **What's the foundation crate concretely?** Is it
  [`covalence-framework`](../02-framework.md) under the layered
  proposal, or is the user thinking of an even smaller substrate?
- **Can the bottom layer support multiple standard metatheories
  simultaneously?** I.e., can you have HOL and Isabelle/HOL and ZFC
  all on top of the same foundation in one session? The
  [base-shift functor discussion](../../../../../ARCHITECTURE.md) says
  yes in principle ("internal re-hosting"). Concretely, does the
  framework give you primitives for this, or do you build it as a
  Phase 3 user-space library?
- **What's the *content-addressing* job of the bottom layer
  specifically?** "Root content addressing" — root of what? Of the
  theory DAG? Of the observation graph? Of both?

### About the reverse-math workflow

- **What's the morphism-construction toolkit?** The
  [commutative-diagram API](../../../../../ARCHITECTURE.md) is the
  obvious answer but lives in
  [`covalence-morphism`](../README.md), which is planned-not-yet-written.
  How much of it is MVP-scope?
- **Does the user's "simplest theory" have a metric, or is it
  human-judgment?** Reverse-math has the Σ¹/Π¹ hierarchy as a metric;
  Covalence's "graph of theories" is more open-ended.
- **Are oracles theories?** An oracle's spec is a theory (per
  [`08-oracles.md` planned](../README.md)). Does the reverse-math
  workflow apply to *oracles* — finding the weakest oracle that lets
  you discharge a goal?

### About the implementation order

- **When does the second standard metatheory show up?** HOL is the
  first; when does Isabelle/HOL or ZFC become a real target rather
  than an example? Probably post-MVP — but worth being explicit.
- **When does the morphism API show up?** It's the workflow's
  central machinery; deferring it deferred the workflow. But
  building it before HOL is solid is premature. Best guess: HOL shell
  matures → first inter-theory morphism (probably HOL → HOL-with-a-tiny-extension)
  → general morphism API.

---

## 8. Cross-references

- [Layered-framework README](../README.md) — proposal index.
- [`02-framework.md`](../02-framework.md) — the foundation layer that
  modified HOL sits on top of. §3.3 observation rule; §4 authorities.
- [`facts-not-proofs.md`](./facts-not-proofs.md) — sibling note. The
  LCF discipline applies uniformly to modified HOL: facts (Thms) are
  stored; justifications are not.
- [`../shared-backbone/00-overview.md`](../../shared-backbone/00-overview.md)
  — the path. The HOL shell is Phase 2 / P5 work; modified HOL is the
  design target that work converges on.
- [`../shared-backbone/notes/session-2026-06-06.md`](../../shared-backbone/notes/session-2026-06-06.md)
  §3.6, §7 — where the "modified HOL" question was raised and
  partially answered.
- [`../../../../prover-architecture.md`](../../../../prover-architecture.md)
  — current `covalence-kernel`'s design. Predates the layered-framework
  framing; some of its HOL-shape design notes carry over to modified
  HOL.
- [`../../../../../ARCHITECTURE.md`](../../../../../ARCHITECTURE.md) §2
  (kernel), §2.4 (disjunct trick), §3 (idiomatic use: metalogic),
  §4 (mirror principle), §5 (planes), §8 (base-shift functor) — the
  big-picture vision that the modified-HOL choices realize.
- [`covalence-hol` crate](../../../../../crates/covalence-hol) — the
  shell-to-be. Currently HOL-Light-shaped; being reshaped per the
  session's §3.6 decision.

# Covalence — Vision

> **STATUS: WORKING DRAFT.** Top-level navigation doc capturing the
> system's organizing ideas. Sits between the absolute summary
> (sentence + bullets) and the full vision in
> [`ARCHITECTURE.md`](../ARCHITECTURE.md). Read in ~10 minutes; from
> here, follow the cross-reference table in §7 to depth.

---

## 1. The vision in one sentence + five bullets

> **Covalence is a theorem prover where metatheory — *symbolic* over
> theories and *computational* over executors — is the default mode,
> so theorems can have multiple models and the system can extend
> itself by proof rather than by trust.**

1. **Metatheory is the default mode.** Two flavors — *symbolic*
   (reasoning about theories, derivations, morphisms, models as
   first-class objects) and *computational* (reasoning about
   executors, programs, oracles as first-class objects). Both produce
   theorems in the kernel's HOL-strength bottom.
2. **Symbolic metatheory: multiple models per theorem.** Theories and
   morphisms between them are first-class; categorical-semantics
   interpretations are theorems. Reverse-math style — prove in the
   simplest sufficient theory, transport to wherever you want the
   statement-of-record. **Morphism layer is MVP-scope.**
3. **Computational metatheory: self-editing via proven extensions.**
   WASM oracles, and future x86 / RISC-V / other executor-substrate
   analogues, join by proving their bytecode satisfies a spec under
   the executor's formal semantics. Complex software like SMT solvers
   enters by running *on* an executor and producing checkable
   certificates, not by being formalized directly. TCB stays flat as
   the oracle catalog grows.
4. **Scoped truths only; no global lies.** Every assumption is bound
   to a named artifact (store, theory, executor). Even content
   addressing is expressed as scoped assumptions discharged
   operationally by the outer-bottom layer. Three corners (computation
   / logic / evidence) stay categorically distinct. Mirror principle:
   confidence comes from independent paths agreeing.
5. **HOL strength is the natural choice.** Strong enough for both
   flavors of metatheory and for executor-semantics formalization.
   Widely-accepted (HOL or ZFC; bespoke logics are out). Daily-use
   ergonomic (we work *inside* this logic, not just on top). The
   bottom-inner layer small enough to audit by inspection without
   paying performance for it.

---

## 2. Symbolic metatheory

Reasoning **about** theories, not just within one.

In a conventional prover (HOL Light, Isabelle, Coq, Lean), you pick a
foundation and prove theorems inside it. Covalence inverts the default:
the user spends most of their time **constructing and reasoning about
theories**, with proving-things-inside-a-theory being one operation
among several.

### What's first-class

- **Theories.** Each is a HOL-style theory object — a set of
  declarations and axioms — with a content-addressed identity
  ([`Name256`](./design/proposals/layered-framework/00-glossary.md#name256)).
  Classical HOL (imported via OpenTheory), Isabelle/HOL, ZFC, HoTT, an
  intuitionistic propositional logic, your specific domain theory —
  all live side-by-side.
- **Morphisms between theories.** Embeddings, equiconsistencies,
  conservativity proofs, language translations. A morphism is itself
  a theorem about the two theories it connects.
- **Categorical interpretations.** A theorem in theory `T` is valid
  in every category that models `T`'s internal language — the
  classical Lambek/Scott correspondence (cf. Crole's *Categories for
  Types*). Equational logic interprets in every Cartesian category;
  simply typed lambda calculus in every Cartesian closed category;
  HOL in every elementary topos. **Reverse math = maximum categorical
  reach**: the weaker your theory, the more categories model it, the
  more contexts your theorem applies in.

### Worked micro-example

You prove a property `P` of the multiplication operation in
*equational logic*. **For free**, `P` holds in every Cartesian
category — so categorical algebraists, topologists, type theorists
all consume it without re-proof. Had you proved `P` in classical HOL,
your audience would be restricted to (classical) topoi. Had you
proved it in ZFC, your audience would be restricted to set-theoretic
universes. **Weakest-sufficient-theory = broadest applicability**;
this is what makes reverse-math an everyday workflow rather than a
research curiosity.

### Borrowing power without changing the foundation

The kernel's HOL strength sometimes isn't enough on its own. If you
need ZFC-strength reasoning, you don't make ZFC the foundation —
you assume `Con(ZFC)` (concretely: "ZFC does not prove `{} = {{}}`")
in your trust set and prove "ZFC ⊢ P" results from there. The
foundation stays fixed; the dependency on ZFC is explicit in every
theorem's hypothesis list. If `Con(ZFC)` ever turns out to be wrong,
the theorems become Thms-with-falsified-hypotheses — still Thms,
just less useful.

Full treatment: [`modified-hol.md`
§3.5](./design/proposals/layered-framework/notes/modified-hol.md#35-borrowing-power-via-cont)
and [`modified-hol.md`
§4](./design/proposals/layered-framework/notes/modified-hol.md#4-reverse-math-workflow).

---

## 3. Computational metatheory

Reasoning about **executors and programs** with the same discipline as
theories.

In a conventional prover, an "oracle" is a black box you trust: SMT
solver says UNSAT, you believe it; hash function says `H(x) = y`, you
believe it. Each black box is a separate trust assumption.

Covalence inverts this: **oracles enter the system as theorems**, by
proving their bytecode does what they claim under the executor's
formal semantics. The trust set has one entry per *executor*
(WASM's spec, x86's spec, …), not one per *oracle*.

### What's first-class

- **Executor semantics.** A theory `T_wasm` describes how WASM
  bytecode executes. One meaning-axiom: *"`T_wasm` correctly
  describes how WASM is actually run by the executor we trust."*
  Audit this once; reuse it for every WASM oracle ever.
- **Oracle programs.** Each oracle is a content-addressed WASM blob
  plus a soundness theorem: *"this bytecode, run under `T_wasm`, on
  input `x`, yields `f(x)`."* No fresh meaning-axiom needed.
- **Other executors.** The same pattern applies to x86, RISC-V, a
  verified-RISC-V-on-WASM emulator — each gets its own semantics
  theory and meaning-axiom; oracles for each executor stack on top.

### Worked micro-example: a SHA-256 oracle

You ship a WASM component `B` that implements SHA-256. Bytecode hashes
to `B_hash`. You prove (in the kernel's HOL-strength bottom, using
`T_wasm` and a spec `T_sha256`):

> ∀ x. exec_wasm(B, x) = SHA256_spec(x)

That theorem is the oracle's "license." Future invocations of `B` are
discharged by it — the kernel accepts `B`'s observations as theorems
about SHA-256, without growing the trust set by one bit. A second
SHA-256 implementation `B'` ships with its own soundness theorem; same
trust set; both are usable.

### Aside: where do SMT solvers fit?

An SMT solver is a 100K-LoC program with no clean formal spec; you
don't want to formalize its behavior directly. Instead, **the LCF
discipline applies computationally**:

- Run the solver as a WASM program — *untrusted*; no soundness proof
  required.
- The solver emits a proof certificate (UNSAT proof, model witness).
- A small certificate-checker — also a WASM program, *with* a
  soundness proof against the certificate format's semantics —
  verifies the certificate.
- The trusted thing is the **checker** (small, proven). The solver
  stays untrusted; its bugs at worst produce certificates the checker
  rejects.

Same pattern as everywhere else in the system: simple trusted core
plus arbitrarily clever untrusted machinery plus soundness by
re-checkability. The certificate-checker is to the SMT solver what
the kernel's inference rules are to a tactic engine.

Full treatment: [`modified-hol.md`
§3.7](./design/proposals/layered-framework/notes/modified-hol.md#37-self-extending-via-proven-oracles).

---

## 4. Why the two flavors unify

Both flavors of metatheory implement the same move: **external thing
enters the system as a symbolic object you prove about, not as a
black-box trust.**

- *Symbolic*: an external theory (classical HOL, ZFC, …) enters as
  a content-addressed theory object you can morph into, interpret,
  and prove conservativity for.
- *Computational*: an external program (a WASM oracle, an SMT
  certificate-checker, …) enters as a content-addressed bytecode blob
  you prove correct under the executor's semantics.

Both ride the same HOL-strength bottom layer. Both produce
top-layer theorems. Both feed federation: signed Thms exchanged
between peers can be symbolic-metatheory artifacts (proofs in
theories) *or* computational-metatheory artifacts (verified oracle
programs) — the protocol doesn't care.

The distinction matters for **engineering decomposition** (different
crates, different specs, different worked examples) but not for
**trust architecture** (one bottom layer, one TCB, one discipline).

---

## 5. The architecture in one diagram

```
┌────────────────────────────────────────────────────┐
│  Theories + morphisms + interpretations            │
│  + oracle programs + their soundness proofs        │
│    LOTS, CHANGING, untrusted                       │
├────────────────────────────────────────────────────┤
│  Bottom layer: enables metatheory  (HOL strength)  │
│    UNCHANGING                                      │
│                                                    │
│   ┌──────────────────────────────────────────────┐ │
│   │  Outer: + content-addressing assumption pkg  │ │
│   │     (operational machinery; each rule        │ │
│   │      discharges one inner-layer assumption)  │ │
│   ├──────────────────────────────────────────────┤ │
│   │  Inner: pure meta-meta-reasoning   ← TCB     │ │
│   │     (small, auditable, perf-preserving;      │ │
│   │      no content addressing — only            │ │
│   │      assumptions ABOUT it)                   │ │
│   └──────────────────────────────────────────────┘ │
└────────────────────────────────────────────────────┘
```

Top layer changes constantly. Bottom layer never changes. The
inner/outer factoring of the bottom is for **audit clarity**, not
modularity — they could be implemented as one layer, but separating
"pure logic" from "operational machinery for hashes / signatures /
ZKPs / range proofs" makes the audit story tractable. Full treatment:
[`modified-hol.md`
§3](./design/proposals/layered-framework/notes/modified-hol.md#3-the-layered-structure).

---

## 6. What's deliberately not in this doc

Each of these is real and on the roadmap, but reading them would
distract from the load-bearing claims above. They live in the
sub-docs.

- **Federation.** Cross-instance Thm exchange via signed blobs; one
  kernel consumes another's facts under a PKI assumption. Same as
  trusting any other authority — federation is the special case where
  the authority is another kernel instance. Post-MVP; see
  [`ARCHITECTURE.md` §10.2](../ARCHITECTURE.md) and the planned
  [`09-federation.md`](./design/proposals/layered-framework/README.md).
- **Mount / namespaces.** The mountable-filesystem-view of theorem
  storage; mount-as-Horn-clause-assertion. Post-MVP; see
  [`ARCHITECTURE.md` §10](../ARCHITECTURE.md).
- **Format plane.** `valid(format, data)` as an oracle relation;
  keyed-BLAKE3 typed identity. Post-MVP; see
  [`ARCHITECTURE.md` §12](../ARCHITECTURE.md).
- **Base-shift functor.** Porting the entire development to a new
  foundation (HOL → ZFC, HOL → HoTT, …) via a single functor. Internal
  re-hosting (the default plan) is post-MVP; external re-hosting is a
  later consilience upgrade. See
  [`ARCHITECTURE.md` §8](../ARCHITECTURE.md).
- **Probability as an internal logic.** `L_prob` for quantifying
  confidence in mirror-agreement and crypto assumptions. Post-MVP;
  see [`ARCHITECTURE.md` §7](../ARCHITECTURE.md).
- **VCS as a particular theory inside the prover.** The endgame
  reunification — VCS operations defined inside the kernel's logic;
  the trusted Rust VCS proven to match the theory. Long-tail; see
  [shared-backbone Phase 4](./design/proposals/shared-backbone/00-overview.md#5-the-four-phases).

---

## 7. Where to read next

Different docs for different questions.

| Question | Read | Length |
|---|---|---|
| The full vision; planes, mirrors, oracles, base-shift | [`../ARCHITECTURE.md`](../ARCHITECTURE.md) | ~600 lines |
| Operational invariants for kernel work | [`../AGENTS.md`](../AGENTS.md) | ~270 lines |
| What "modified HOL" means; the bottom layer in depth | [`design/proposals/layered-framework/notes/modified-hol.md`](./design/proposals/layered-framework/notes/modified-hol.md) | ~750 lines |
| The kernel layer's design | [`design/proposals/layered-framework/`](./design/proposals/layered-framework/) | proposal set |
| The path to the vision (substrate + parallel streams + kill list) | [`design/proposals/shared-backbone/00-overview.md`](./design/proposals/shared-backbone/00-overview.md) | ~350 lines |
| The trajectory of how this vision was extracted | [`design/proposals/shared-backbone/notes/session-2026-06-06.md`](./design/proposals/shared-backbone/notes/session-2026-06-06.md) | ~570 lines |
| Honest snapshot of what's built today | [`where-we-are.md`](./where-we-are.md) | ~300 lines |
| Build commands and crate conventions | [`../CLAUDE.md`](../CLAUDE.md) | ~140 lines |

### Reading paths

- **Just want the elevator pitch?** Stop here.
- **Going to write kernel code?** This doc → [`../AGENTS.md`](../AGENTS.md)
  → [`modified-hol.md`](./design/proposals/layered-framework/notes/modified-hol.md).
- **Going to write shells / oracles / VCS code?** This doc →
  [`shared-backbone/00-overview.md`](./design/proposals/shared-backbone/00-overview.md)
  → [`where-we-are.md`](./where-we-are.md).
- **Want the full design philosophy?** This doc →
  [`../ARCHITECTURE.md`](../ARCHITECTURE.md).
- **Want to know why a specific decision was made?** Search the
  session notes in
  [`design/proposals/shared-backbone/notes/`](./design/proposals/shared-backbone/notes/).

# Covalence — Vision

> **The canonical kernel / foundation vision** — read in ~10 minutes. Its
> frontend/UX counterpart is [`frontend.md`](./frontend.md). See
> [`notes/vibes/README.md`](./README.md) for the full doc index. (The older,
> longer `ARCHITECTURE.md` was retired to `backup/pre-hol-cleanup`.)

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

### The three-layer stack (bottom → middle → top)

The organizing structure, each layer the *root of trust* for the one above:

- **Bottom — executors + content addressing (disk and CPU).** The literal root
  of trust: store bytes (content-addressed) and run bytes (an executor — WASM
  today, x86 / ARM / RISC-V later). Everything physical bottoms out here.
- **Middle — HOL (HOL Light now, HOL-ω eventually): the metalogic, "generalized
  Haskell."** The logic we reason *in* and implement everything else *with*. Two
  properties make it Haskell-on-steroids: (1) you can **compile a program in
  arbitrary ways** and trust the output because the compilation is *proven sound*
  (e.g. to WASM); and (2) you **don't have to execute everything** — *"math is the
  ultimate laziness"*: a theorem about a computation's result stands without
  running it.
- **Top — *internal* Metamath, the thin waist.** Reified inside HOL, the single
  primitive is the proof-irrelevant existential **"there exists a derivation `D`,
  with axiom-set `Ax`, of `P`."** *Every* internal logic — internal FOL, internal
  HOL, internal ZFC / Grothendieck-Tarski, internal MLTT, internal LF / Dedukti, …
  — goes **through this one waist**. That is what it buys:
  - a **standard way to relate axiom-sets** — "`Ax` is a conservative extension of
    `Ax'`", "`Ax ⟹_σ Ax'`";
  - **syntax translations** as ordinary functions / partial functions / relations
    `P ↦ Translate(P)`;
  - **freedom to work in whatever is convenient** — Metamath in a rich conservative
    extension, *or* an efficient internal data structure — while *knowing we prove
    what we think we prove*, because we prove **soundness w.r.t. the Metamath base**
    of our axiom sets.

**Encodings are HOL data structures, proven sound against the Metamath base.**
Every efficient encoding (de Bruijn indices, structured ASTs, …) is a HOL data
structure with a soundness theorem relating it to internal Metamath. The waist
does two jobs at once: it **pins the meaning** (we are proving what we think) and
it **lets us experiment freely with encodings** (swap representations behind a
proven equivalence). And because we **never need to look at the Metamath proofs**
— only that one *exists* — the databases stay **dead-simple**: efficiency is
irrelevant at the waist, so ZFC, CTL, MLTT, … are *just their Metamath axiom
sets*. (Full treatment: [`theories-models-and-logics.md`](./theories-models-and-logics.md)
§5.6.)

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
  (`Name256`).
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
ZKPs / range proofs" makes the audit story tractable.

---

## 6. What's deliberately not in this doc

Each of these is real and on the roadmap, but reading them would
distract from the load-bearing claims above. All are **post-MVP**; the
pre-collapse detail lives in the retired `ARCHITECTURE.md` (and the
`shared-backbone` proposal set) on the `backup/pre-hol-cleanup` branch.

- **Federation.** Cross-instance Thm exchange via signed blobs; one
  kernel consumes another's facts under a PKI assumption. Same as
  trusting any other authority — federation is the special case where
  the authority is another kernel instance.
- **Mount / namespaces.** The mountable-filesystem-view of theorem
  storage; mount-as-Horn-clause-assertion.
- **Format plane.** `valid(format, data)` as an oracle relation;
  keyed-BLAKE3 typed identity.
- **Base-shift functor.** Porting the entire development to a new
  foundation (HOL → ZFC, HOL → HoTT, …) via a single functor. Internal
  re-hosting (the default plan) first; external re-hosting is a later
  consilience upgrade.
- **Probability as an internal logic.** `L_prob` for quantifying
  confidence in mirror-agreement and crypto assumptions.
- **VCS as a particular theory inside the prover.** The endgame
  reunification — VCS operations defined inside the kernel's logic;
  the trusted Rust VCS proven to match the theory.

---

## 7. Where to read next

See [`notes/vibes/README.md`](./README.md) for the full doc index. Older
deep-dives (the full `ARCHITECTURE.md`, the `layered-framework` and
`shared-backbone` proposal sets, the session notes) were retired to the
`backup/pre-hol-cleanup` branch.

# The K-framework north star — full K + all its sublanguages

**Status:** north-star vision note (AI-drafted). Aspirational; the concrete
existing scaffolding it composes with (`covalence-spectec`, the WASM front end)
is real and linked below. Not yet a `notes/design/` proposal — when a slice is
picked to build, promote it to a design doc via
[`../design/TEMPLATE.md`](../design/TEMPLATE.md).

**Companions:** [`wasm-spec.md`](./wasm-spec.md) (the SpecTec/WASM front end that
already exists), [`VISION.md`](./VISION.md) (the metatheory-as-default stack),
[`logic-frontends.md`](./logic-frontends.md) (bringing external systems in as
object logics), [`project-map.md`](./project-map.md) (where the pieces live).

## The north star, in one line

**Support the full [K framework](https://kframework.org) and all of its
sublanguages — WASM, x86, C, and K itself — inside Covalence, and *relate* the K
semantics of WASM to the official WASM specification (via SpecTec).**

K is a semantic framework: you write an operational semantics for a programming
language once (its *K definition*), and K derives an interpreter, a symbolic
execution engine, a deductive verifier (reachability logic), and more. Major
real semantics exist in K: **KWasm** (WebAssembly), **K-x86-64**, a **C
semantics** (the flagship, used to find bugs in production compilers), and K's own
meta-language. Covalence's ambition is to host these *as object logics/semantics*
the way it already hosts HOL, Metamath, and the WASM spec — and then to *prove
things across them* (transport, agreement, refinement).

## Why K + WASM makes the tool very useful

- **WASM is the universal execution substrate** the rest of Covalence already
  bets on: the base kernel's endgame is *"all computation = untrusted relation
  evaluation"* with a real WASM engine as the untrusted oracle
  ([`base-abstraction.md`](./base-abstraction.md) §4,
  [`sha256-round-keystone.md`](./sha256-round-keystone.md)). A K semantics of WASM
  gives an *independent, executable, formal* reference for exactly that oracle.
- **Two definitions of WASM, cross-checked.** We already lower the **official
  SpecTec** WASM 3.0 spec into the kernel (`covalence-spectec` +
  `covalence-init/src/grammar/spectec`, [`wasm-spec.md`](./wasm-spec.md)).
  KWasm is a *second*, independently maintained formalization. **Relating them —
  proving KWasm's transition relation agrees with SpecTec's reduction relation —**
  is a high-value metatheorem: it certifies both against each other and turns "the
  WASM semantics" into a fact with two witnesses instead of one trusted artifact.
- **Reachability logic = program verification for free.** K's proof system is
  reachability logic (all-path/one-path reachability claims `φ ⇒ φ'`). Hosting it
  lets Covalence state and check *program-level* theorems (this x86 routine
  computes SHA-256; this C function has no UB) in the same certificate substrate
  as its math theorems — the "SQL with set theory + LLM query planner" surface
  extended to *code*.
- **One tool spanning math and systems.** HOL/Metamath give the mathematics;
  K gives real-language operational semantics; WASM is the shared executable
  floor. Covalence's differentiator is holding all of these in *one* content-
  addressed, transport-aware certificate world.

## First-pass mapping onto Covalence

The mapping reuses the machinery already built for SpecTec and Metamath. Recall
the existing duality ([`wasm-spec.md`](./wasm-spec.md)): **Metamath ships proofs
to replay; SpecTec ships a specification to define.** K sits on the *define* side,
like SpecTec, but adds a *reachability* proof layer.

1. **A K definition → an object semantics (untrusted relations).** A K definition
   is, at core, a set of **rewrite/transition rules** over configurations. Lower
   each K rule to an inductively-defined relation exactly as the SpecTec front end
   lowers a WASM reduction rule: each relation `R` becomes an impredicative
   `Derivable_R` least-fixpoint predicate, driven by the *same* rule-induction
   engine SpecTec uses (`covalence-init/src/grammar/spectec` reuses the metalogic
   engine). "Construct, don't trust": the K definition is an **untrusted driver**;
   what it produces is re-checked by the kernel.

2. **K configurations → kernel terms; K's cells → structured data.** A K
   configuration is a nested multiset of labelled cells. This is content-addressed
   structured data — the kernel's home turf (the `sexpr`/carved-inductive machinery
   in `covalence-inductive` + `covalence-init::init::lisp`).

3. **Reachability claims → theorems.** A K reachability rule `φ ⇒ φ'` (reach `φ'`
   from `φ` along the transition relation) becomes a theorem *about* the lowered
   transition relation — a reachability/closure statement, the kind of positive,
   composable relation fact the base already mints and recombines
   (`rel.rs::execute`/`compose`/`transpose`; the relations base of
   [`base-relcalc-holomega-design.md`](./base-relcalc-holomega-design.md)). Symbolic
   execution = building the reachability derivation; the engine (untrusted) can
   even be a real K/WASM run whose *trace* we certify.

4. **KWasm ⟷ SpecTec agreement (the headline metatheorem).** Both are relations
   over WASM configurations lowered into the kernel. Relating them is a **theory
   morphism / transport** result ([`metatheory.md`](./metatheory.md),
   [`theories-models-and-logics.md`](./theories-models-and-logics.md)): exhibit a
   map between their configuration encodings and prove step-for-step (or
   refinement) agreement. This is the K analogue of the set.mm-in-GT benchmark —
   a whole-semantics cross-check rather than a single theorem.

5. **The sublanguage ladder.** WASM first (it composes directly with the existing
   `covalence-spectec`/`covalence-wasm` work and the WASM-oracle endgame), then C
   and x86-64 (bigger configurations, same lowering shape), then **K itself**
   (K's meta-semantics as an object semantics — the reflective capstone, letting
   Covalence reason about K definitions generically, not one language at a time).

## How it composes with existing work

- **`covalence-spectec`** (`crates/lib/wasm/spectec`) + **`covalence-init/src/grammar/spectec`**
  — the AST-first SpecTec front end and its lowering to byte/relation predicates.
  The KWasm⟷SpecTec relating goal lives directly on top of this.
- **`covalence-wasm`** (`crates/lib/wasm/core`) + **`covalence-wasm-spec`** — the
  WASM engine wrapper + multi-variant component machinery: the untrusted oracle
  side and the artifact side.
- **The metalogic engine** (`covalence-init/src/metalogic`) — the impredicative
  rule-induction machinery that turns "a relation defined by rules" into a
  `Derivable_R` predicate; shared by Metamath, SpecTec, and (proposed) K.
- **The relations base** ([`base-relcalc-holomega-design.md`](./base-relcalc-holomega-design.md),
  [`base-abstraction.md`](./base-abstraction.md)) — positive relation facts +
  execute/compose/transpose are exactly the substrate reachability derivations
  want; a K/WASM engine slots in as an `UntrustedFn` oracle.
- **CFG stratum** — the SpecTec/regex front ends currently cover only the *regular*
  base case (`Var` non-terminals rejected — the CFG skeleton in the root
  `SKELETONS.md` #8). Full K needs the CFG stratum too; the K work and the CFG
  work share this dependency.

## Open questions

- **Input surface for K definitions.** SpecTec gave us an elaborated AST to consume
  (no `.watsup` frontend). What is the analogous *stable, elaborated* surface for K
  — the KORE/kompiled definition (K's intermediate representation), or something
  higher? Consuming KORE keeps us "AST-first" and out of K's frontend.
- **Reachability logic vs. our positive-relation calculus.** How much of K's
  all-path/one-path reachability proof system maps cleanly onto positive relation
  facts + composition, and where do we need genuine coinduction/circular
  reasoning (K's core proof principle) that the base doesn't yet express?
- **Configuration encoding stability.** For KWasm⟷SpecTec agreement to be
  statable, both must encode WASM configurations into *comparable* kernel terms.
  Who owns the canonical encoding, and does it match SpecTec's already-lowered one?
- **Scale.** The C semantics and set.mm are both "whole-database" scale. Does the
  verify-auto-scales / prove-doesn't asymmetry ([`roadmap.md`](./roadmap.md)) carry
  over — i.e. is *checking a K execution trace* cheap (oracle + certificate) while
  *proving a reachability metatheorem* is the expensive lean part?
- **Trust.** K's own tooling is large; keeping it an untrusted oracle (trace
  certification) is the discipline. What is the smallest end-to-end demo — a KWasm
  step certified against SpecTec — analogous to the SHA-256-round keystone?

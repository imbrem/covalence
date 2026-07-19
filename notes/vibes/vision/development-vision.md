+++
id = "N0037"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-15T23:14:14+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Development vision — consilience, computation-grounded foundations, verified I/O

> Status: **north-star / aspirational.** A map of the parallel projects we want
> to pursue once the dev-experience groundwork (build orchestration, caches,
> reproducible env, cleaned docs) is in place. Complements the core
> [`VISION.md`](./VISION.md) and [`roadmap.md`](./roadmap.md); this doc is about
> *breadth* — the many libraries and frontends we build on the kernel and how
> they interlock. Dates are absolute; today is 2026-07-15.

## The through-lines

Three ideas tie the otherwise-sprawling project list together. Everything below
is an instance of one or more of them.

1. **Consilience.** The same object (a theorem, a program, a datatype, a
   grammar) is reachable from many independent directions — HOL, Metamath,
   SpecTec, K, WASM, Lisp/ACL2 — and we *relate* those views inside the kernel.
   A fact grounded in several systems at once is far more trustworthy than one
   grounded in a single formalism. Metamath is the shared substrate for
   *defining* logics; HOL is the narrow computational waist; the others are
   frontends and accelerators that must agree.

2. **Grounding in computation.** We do not want arithmetic, datatypes, and
   metatheory to float on axioms alone. We want them anchored to concrete models
   of computation — lambda calculus, combinators, machines — themselves
   represented as **bytestrings** and proven equivalent, so a theorem can be
   given an operational meaning and (later) a complexity. WASM is the executor at
   the bottom; the classical models sit alongside it as the theory.

3. **Verified I/O.** Covalence already *parses* untrusted input into kernel
   objects (Lisp S-expressions, `.mm`, SpecTec, OpenTheory articles). The dual —
   **verified output** — is the frontier: emit bytes/strings (MathML, DOT, …)
   *certified* to denote a specific internal object under a specific, hashed
   **dialect**, with proofs relating dialects. Parse and deparse become a
   verified round-trip on raw bytes.

The unifying substrate under all three is the **base layer**: a first-order,
content-addressed, WASM-executable core. Its rewrite is the enabling step.

---

## 0. The base-layer rewrite (enabling work)

The user has a cleaner base design worked out on paper (roughly the same
high-level API and theoretical foundations as today's `crates/kernel/base`
=`covalence-pure`, but a much cleaner realization) that needs typing up. It is
the foundation the rest depends on, because it is where **WASM execution** and
**content addressing** become first-class rather than bolted on.

- Keep the current high-level contract (`Thm<L,P>` LCF certificate, `Op`/`Expr`/
  `Eqn`, parameter-free `Language`, definitional equality) — see
  [`../kernel/closed-world-kernel.md`](../kernel/closed-world-kernel.md) and
  [`../kernel/base-relcalc-holomega-design.md`](../kernel/base-relcalc-holomega-design.md).
- Make **content addressing** intrinsic: every term/definition/theorem has a
  stable hash; the store ([`../web/web-kernel.md`](../web/web-kernel.md),
  federation) and the surface language both address objects by hash. `$DEFINITION_HASH`
  and `$DIALECT_HASH` in the verified-I/O story below are the *same* hashes.
- Make **WASM execution** a base-layer logic: facts of the form "this WASM
  module, applied to these bytes, evaluates to those bytes" as trusted-observer
  primitives, so kernel reasoning can be *accelerated* by running verified WASM
  and *about* WASM at the same time (the "strange loop"). Ties to
  [`../logics/wasm-spec.md`](../logics/wasm-spec.md) and the base `wasm/` logic
  in [`../../plans/next-stage.md`](../../plans/next-stage.md).

Everything else in this doc is a **library or frontend over this base**. They can
proceed in parallel once the base API is fixed, because they depend on the API,
not its internals.

---

## 1. Datatypes: records, variants, polynomial functors, (co)inductive types

A general high-level datatype API, built on the HOL tier (`crates/kernel/hol`):

- **Records** (labelled products) and **variants** (labelled sums) as the
  ergonomic surface.
- **Polynomial functors** as the underlying theory: a functor built from
  constants, sums, products, and exponentials. Records/variants are the degree-0
  and sum-of-products cases.
- **Least fixpoints** `μF` → **inductive** datatypes (with their recursors /
  induction principles); **greatest fixpoints** `νF` → **coinductive** datatypes
  (with corecursion / bisimulation). One functor language, two fixpoints, both
  with their universal properties proven, not postulated.

Builds on today's inductive support — see
[`../kernel/inductive/inductive-support.md`](../kernel/inductive/inductive-support.md)
and [`../kernel/inductive/inductive-api-design.md`](../kernel/inductive/inductive-api-design.md).
The `nat` recursion theorem and `list`/`prod` theories are the seed; generalise
to arbitrary polynomial functors.

## 2. Arrows and monads

Solid libraries for the standard categorical structures — functors, applicatives,
**monads**, and **arrows** — as reusable theories (a theory = signature + laws +
many models; see [`../logics/theories-models-and-logics.md`](../logics/theories-models-and-logics.md)
and [`../surface/surface-compiler.md`](../surface/surface-compiler.md)). These are
the glue for effectful/streaming computation descriptions and for the reduction
relations below. Pairs naturally with the datatype API (monads *are* particular
(co)inductive/algebraic structures) and with graph theory (arrows ≈ morphisms in
a chosen category).

## 3. Graph theory

APIs and libraries for graphs: directed/undirected, labelled, typed, with the
usual constructions (reachability, paths, components, morphisms). We already have
an ordered/typed graph substrate (`covalence-graph`, `crates/lib/graph`) to build the
*theory* on top of. Graph theory is load-bearing twice over: (a) it underlies
content addressing (Merkle DAGs), the store's supervision trees, and dependency
graphs; (b) it is the target of the **verified DOT** deparser (§7).

## 4. Computation theory (bytestring-grounded, proven equivalent)

The distinctive bet. Give each classical model of computation a **concrete
bytestring representation** inside the kernel and prove them **equivalent**, so
theorems can be grounded operationally:

- untyped **λ-calculus** with de Bruijn indices,
- **binary lambda calculus** (a canonical bytestring encoding of λ-terms),
- **SKI** (and BCKW) combinators,
- **Turing machines**, **register machines**, **stack machines**.

For each: an encoding to `bytes`, an evaluation/reduction relation, and
cross-model simulation theorems (`⟦M⟧ ↝ ⟦N⟧` under a compiler proven to preserve
semantics). This gives every downstream theory a choice of operational model and
a way to *transport* results between them. It also seeds:

- **λ_iter / deep embeddings** already in flight (the `covalence-init` lambda embedding, `crates/kernel/hol/init`);
- the reduction-relation machinery shared with Lisp/K — see
  [`../lisp/initial-ideas/reduction-relation-on-binary-engine.md`](../lisp/initial-ideas/reduction-relation-on-binary-engine.md)
  and the mid-level rewrite relation (K API layering).

### Complexity theory (later)

Once evaluation relations carry **step/space measures**, we get complexity as a
layer on top: cost models per machine, and the ability to state and relate
complexity claims. We will use this specifically in the **study of WASM and
Lisp** (cost of execution, size of encodings). Deferred, but the computation
representations above should carry the measures from the start so complexity is a
refinement, not a rewrite.

## 5. Lisp / ACL2

Continue the Lisp frontend (already parsing + reducing S-expressions — see
[`../lisp/README.md`](../lisp/README.md) and [`../lisp/STATUS.md`](../lisp/STATUS.md))
toward **ACL2 book imports**: read ACL2 events/theorems and replay them against
our kernel, with the Lisp reduction relation grounded (via §4) in a concrete
machine. Clean traits for producing S-expressions, parsing them *out* of their
HOL representations (a deparse dual to parse — the verified-I/O pattern in the
small), and casting between S-expression representations.

## 6. Prolog

A Prolog frontend: SLD resolution as a reduction/search relation, unification on
our terms, and Horn-clause theories as a logic we can define in the Metamath
substrate and relate to the others. Shares the parsing-relation and
reduction-relation infrastructure with Lisp and K.

## 7. Consilience frontends: K, Metamath, SpecTec, WASM

Continue first-class support for the four "grounding" systems so the same claim
is corroborated from independent directions:

- **Metamath** — the shared logic-definition substrate; set.mm as a corpus;
  axiom-set metatheory and interpretation ([`../logics/metamath-axiom-set-metatheory.md`](../logics/metamath-axiom-set-metatheory.md)).
- **SpecTec** — the WASM spec as a frontend; CFG stratum; grammar metatheorems
  ([`../logics/wasm-spec.md`](../logics/wasm-spec.md), [`../logics/cfg-stratum-design.md`](../logics/cfg-stratum-design.md)).
- **K** — full K and its sublanguages; relate K-WASM to SpecTec-WASM
  ([`../k/README.md`](../k/README.md), [`k-framework-vision.md`](./k-framework-vision.md)).
- **WASM** — both as executor (base-layer §0) and as an object of study, with the
  stretch goal of cross-referencing SpecTec-WASM and K-WASM as **the same
  language reached two ways**.

The payoff is *layers of consilience*: WASM semantics established via SpecTec,
via K, and via direct execution, proven to agree.

## 8. Verified output (the frontier)

We already parse untrusted bytes into kernel objects. The dual is to **emit**
bytes certified to denote a specific internal object under a **dialect**:

- A **dialect** is a mapping from a concrete syntax tree (e.g. the MathML tree,
  the DOT AST) to a mathematical object. Different applications need different,
  possibly incompatible dialects — so a dialect is itself a first-class,
  **hashed** object (`$DIALECT_HASH`).
- **Verified MathML**: emit a MathML fragment tagged "verified to correspond to
  definition `$DEFINITION_HASH` under dialect `$DIALECT_HASH`", i.e. a certificate
  that *parsing this MathML back through the dialect yields exactly that object*.
  Plus **proofs relating dialects** (dialect A's rendering ≡ dialect B's under a
  translation), so a rendering is portable across applications with a proof, not
  a hope.
- **Verified graphs / DOT**: a verified **parser + deparser** for DOT relating
  the bytes to a graph + metadata (§3). A round-trip theorem (`deparse ∘ parse ≡
  id` on well-formed inputs, and `parse ∘ deparse` denotes the same graph) makes
  a rendered diagram a *checked* view of an internal graph.
- **Not pixels (yet).** We stop at the structured-text layer (MathML, DOT,
  SVG-as-AST) for the foreseeable future; pixel-level rendering is far-future.

The general pattern — **parse/deparse as a verified pair on raw bytes/strings,
mediated by a hashed dialect** — is the same one Lisp (§5) exercises in the small
and the store (§0) exercises for content addressing. Verified I/O is where the
kernel stops being an internal calculator and starts producing artifacts the
outside world can trust.

---

## Sequencing & infra implications

- **First:** the base-layer rewrite (§0) — it fixes the API the rest target and
  makes content addressing + WASM execution first-class. Parallel projects
  (§1–§8) depend on the *API*, so they can then proceed concurrently, TDD-style
  on spike branches that graduate into feature branches (the workflow in
  [`../../plans/sketch-separation.md`](../../plans/sketch-separation.md)).
- **Infra we need now** (partly landed this cycle): a build system that tracks
  cross-toolchain artifact dependencies (done — [`../../../scripts/build.mjs`](../../../scripts/build.mjs)),
  shared caches, reproducible env. Next: **solid generation and bundling of WASM
  modules and native code** — a standard way to compile a "covalence library" to
  a `.wasm` that imports the covalence WIT and constructs itself (and to bundle
  native artifacts), since §0/§4/§7/§8 all emit and consume WASM. This is the
  build-orchestrator's natural next capability (WASM-artifact nodes in the graph:
  compile → componentize → bundle).
- **APIs vs applications:** per [`../../plans/sketch-separation.md`](../../plans/sketch-separation.md),
  split each project into its *API* (traits/theories others build on) and its
  *application* (the concrete tool). Prefer isomorphic models and transport over
  bespoke one-offs, so consilience is structural.

## Related notes

Core: [`VISION.md`](./VISION.md) · [`roadmap.md`](./roadmap.md) ·
[`project-map.md`](./project-map.md) · [`k-framework-vision.md`](./k-framework-vision.md).
Deeper design: [`../kernel/closed-world-kernel.md`](../kernel/closed-world-kernel.md) ·
[`../logics/theories-models-and-logics.md`](../logics/theories-models-and-logics.md) ·
[`../surface/surface-compiler.md`](../surface/surface-compiler.md).
Frontiers with their own notes below: computation theory
([`../logics/computation-theory.md`](../logics/computation-theory.md)) and verified
I/O ([`../logics/verified-io.md`](../logics/verified-io.md)).

+++
id = "N0029"
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

# Computation theory — bytestring models, proven equivalent

> Status: **aspirational design note.** Frontier detail for §4 of
> [`../vision/development-vision.md`](../vision/development-vision.md). The goal:
> ground kernel theorems in concrete models of computation, each a **bytestring**,
> proven mutually simulable, with cost measures baked in for a later complexity
> layer.

## Why

Axioms alone leave arithmetic and datatypes floating. If a claim can be *run* —
and run in several equivalent models — it gains an operational meaning and,
eventually, a complexity. WASM is the executor at the bottom (base-layer logic);
the classical models are the *theory* that sits beside it, so we can relate
"what WASM does" to "what a Turing machine does" with a proof rather than a
handwave. This is the computation-theory half of **consilience**.

## The models

Each model gets: (1) a **datatype** for its programs/configurations, (2) a
**concrete `bytes` encoding** (a total, injective serializer with a verified
parser — a verified-I/O round-trip in the small, see
[`verified-io.md`](./verified-io.md)), and (3) a **small-step relation** `↝` with
a step counter.

- **Untyped λ-calculus, de Bruijn.** The hub. Terms as `Var n | Lam t | App a b`;
  β-reduction; normal-order and applicative strategies. Connects to the
  `covalence-init` lambda embedding already in flight (`crates/kernel/hol/init`).
- **Binary lambda calculus (BLC).** The canonical bytestring encoding of λ-terms
  (`00 M` for λ, `01 M N` for application, `1ⁿ0` for de Bruijn `n`). This is the
  *bridge between "λ-term" and "bytes"* — the encode/decode pair whose round-trip
  theorem makes "a program is a bytestring" literal.
- **SKI / BCKW combinators.** Combinatory logic: no binders, so no α-equivalence
  machinery — a clean target for compilation from λ (bracket abstraction) and a
  clean source for equivalence proofs.
- **Turing machines.** Tape + head + state table; the classical yardstick for
  computability and (with the step counter) time/space complexity.
- **Register machines** (counter/RAM) and **stack machines.** The models closest
  to real execution and to WASM (a stack machine!), making the WASM bridge short.

## The equivalences

The point is not the models individually but the **web of simulation theorems**
between them. For a compiler `C : ModelA → ModelB` we want a preservation
theorem: `∀ p x. eval_A(p, x) = y  ⟹  eval_B(C(p), enc(x)) = enc(y)` (and, for
totality-sensitive results, the converse / reflection). Concretely:

- λ ↔ SKI via bracket abstraction (both directions),
- λ ↔ BLC (encode/decode, a pure serialization equivalence),
- λ / SKI → stack machine (a "SECD/Krivine"-style abstract machine),
- Turing ↔ register ↔ stack (the classical simulations),
- stack machine ↔ **WASM** (the payoff link: relate the theoretical stack model
  to the base-layer WASM executor).

Composing these gives a **transport** facility: prove a result in whichever model
is most convenient, move it to any other with a proof. A `nat`-arithmetic fact,
for instance, can be tied to an actual λ-term or WASM module computing it.

## Cost measures (seeds the complexity layer)

Every `↝` relation carries a **step count**; encoders expose a **size**. Keep
these from day one so complexity theory (deferred — §4 of the vision) is a
*refinement* (add cost models, relate them across simulations up to polynomial
factors) rather than a rewrite. First uses: cost of WASM execution and size of
encodings, in the study of WASM and Lisp.

## Relation to existing work

- Reduction-relation infrastructure is shared with Lisp and K — see
  [`../lisp/initial-ideas/reduction-relation-on-binary-engine.md`](../lisp/initial-ideas/reduction-relation-on-binary-engine.md)
  and the mid-level term-rewrite relation (K API layering). Computation theory is
  another consumer of the same relation machinery, specialised to fixed models.
- `bytes` is a first-class kernel literal (the kernel is a binary-data
  substrate), so "program = bytestring" is native, not an encoding hack.
- The datatype API ([vision §1](../vision/development-vision.md)) supplies the
  (co)inductive machine-configuration types and their recursors.

## Implemented API boundary (2026-07-19)

The first implementation slice lives in `covalence-computation`. Its primary
surface is proof-oriented:

- a `TheoryBackend<L, Spec>` realizes plain model data as a vocabulary whose
  machine, input, state, output, step, and halting objects are `L::Type` and
  `L::Term`;
- proof laws and replay operations return an associated `Certificate`, not a
  fixed theorem representation;
- `TheoremCertificate<L>` is an optional projection for artifacts which do
  expose `L::Thm`, while `TheoremArtifact<L, M>` carries interpretation
  metadata beside it;
- host-language evaluators produce only `SearchWitness` candidates. A replay
  backend must validate a candidate against the realized HOL theory before it
  can return a certificate.

This division is intentional. The Rust BLC, SKI, Turing, Minsky, finite
automata, and pushdown-automata code is an independently auditable codec and
proof-search layer, not the semantics and never a proof authority. Multiple
HOL representations of the same serialized specification meet at the theory
and certificate traits.

The compiler layer follows the same rule. `Compiler<Source, Target>` and
`PartialCompiler<Source, Target>` produce representation-rich target artifacts;
their law capabilities separately provide preservation and reflection
certificates. Partial compilation distinguishes a certified failure of the
source-domain predicate from an operational error. A computational equivalence
is paired forward/backward compilers plus explicit round-trip and observational
certificates—not merely the existence of two host functions. This is intended
to support both the classical equivalence web and restricted translations such
as finite-state fragments of otherwise unbounded machines.

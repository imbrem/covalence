# Egglog-Integration Proposal

> **STATUS: PROPOSED — working-draft design, not committed.**
>
> Research + design notes generated during a planning conversation
> about how Covalence should integrate with the egglog ecosystem. The
> shape, vocabulary, and scope are subject to substantial revision
> before any implementation lands. For what is *actually built* vs.
> what is *proposed*, see [`../../../where-we-are.md`](../../../where-we-are.md).
> For the design directory index, see [`../../README.md`](../../README.md).

## What this proposal is about

Egglog ([repo](https://github.com/egraphs-good/egglog), [tutorial](https://egraphs-good.github.io/egglog-tutorial),
[paper PLDI '23](https://mwillsey.com/papers/egglog)) is the
next-generation equality-saturation engine: e-graphs from
[`egg`](https://github.com/egraphs-good/egg) crossed with bottom-up
Datalog. Version 2.0 also ships a proof-production module
([`src/proofs/proof_format.rs`](https://github.com/egraphs-good/egglog/blob/main/src/proofs/proof_format.rs))
that emits explicit justification DAGs over a small set of axioms
(Fiat / Rule / MergeFn / Trans / Sym / Congr).

Covalence already has the seeds of an e-graph kernel: see
[`prop-egraph-design.md`](../../../prop-egraph-design.md) and
`crates/covalence-kernel/src/egraph.rs` + `eprop.rs`. The
`EThm` type bundles an arena, a union-find, and a precondition chain
into a single proof environment; rules mutate the egraph and union
matched terms with a user-supplied `truth` ref.

### The framing: a theory catalogue, not a frontend

The goal is **not** to support all of egglog. The goal is to curate
a **patchwork of small, well-understood (theory, decision question)
pairs** where egglog is genuinely the right engine — pure equational
theories, EUF, the theory of arrays, AC word problems, Datalog
reachability, lattice-valued analyses, and so on. Each entry in the
catalogue ships:

* a small signature (sorts + function symbols);
* a precise *decision question* egglog answers on that signature;
* an egglog encoding the question, plus the rules egglog uses to
  decide it;
* a replay path into the kernel as a family of `EThm`s.

[`04-theory-catalogue.md`](./04-theory-catalogue.md) lists the
candidate entries. Most are bite-sized; the catalogue grows entry by
entry, and adding an entry doesn't require touching the others.

### Two engineering layers under the catalogue

| Layer | What it is | Trust model | Status |
|---|---|---|---|
| **A — Oracle replay** | A reusable scaffold for running external `egglog` against a catalogue entry, requesting a proof DAG via `(prove …)`, and replaying it through `EThm`. Each catalogue entry instantiates the scaffold with its own rule catalog. | egglog is fully untrusted; only the kernel-checked replay produces a `Thm`. | proposed |
| **B — Native runner** | A small e-matcher + saturation loop over Covalence's `Egraph`, used by catalogue entries that benefit from owning the loop (smaller deps; better integration with the kernel; no external egglog required). | The runner is untrusted; the `EThm` constructors are the trust boundary. | proposed |

Both layers reuse `EThm` as the trust boundary. They share the
egglog AST, the rule catalog, and the proof walker; they differ
only in where the matched-and-justified inferences come from
(external solver for A; our own runner for B).

A catalogue entry can ship as A, B, or both. Some entries (pure
equational + EUF) are trivial enough that B is the obvious choice;
others (Datalog reachability with non-trivial joins) benefit from
A's mature solver until B catches up.

### A long-term third mode (not built here)

A possible **Layer C** sits orthogonally: instead of replaying a
proof DAG into `EThm` to get `Thm P`, *reify* the same DAG as a HOL
term of type `EggDeriv` and obtain `Thm (Provable_T(⌜P⌝))` — a
*meta*-claim that the egglog theory `T` derives `P`, independent of
any model.

The catalogue framing makes Layer C particularly clean: each entry
*already* fixes a small `T`, so `Provable_T(P)` is a concrete
proposition rather than a parameterised template. That's the right
shape for theory-parametric reasoning ("explore multiple models of
this catalogue entry's theory without re-running egglog") and for
proving things *about* the engine inside HOL.

Layer C is **not in scope for this proposal** — it requires a HOL
embedding of egglog syntax plus a verified `check_deriv` checker.
What this proposal *does* commit to is making the architectural
choices that keep Layer C reachable; see
[`03-integration-plan.md`'s "Forward compatibility" section](./03-integration-plan.md#forward-compatibility-with-a-meta-provability-layer).

## Read in this order

1. [`00-foundations.md`](./00-foundations.md) — what an egglog
   program *is* semantically: e-graphs, Datalog, rules vs. rewrites,
   the merge function, seminaive evaluation, and the 2.0 proof
   system. Background needed to evaluate which (theory, question)
   pairs are eligible for the catalogue.
2. [`01-commands.md`](./01-commands.md) — the egglog command
   language in full, with a per-command **K/P/O** map. In the
   catalogue framing this is a **constraint** on admissible entries
   (every rule a catalogue entry uses has to land in **K** ∪ **P**),
   not a roadmap toward egglog-completeness.
3. [`02-python-api.md`](./02-python-api.md) — the
   [`egglog-python`](https://github.com/egraphs-good/egglog-python)
   typed wrapper API, as a model for how a "Covalence theory" might
   look as a typed Python frontend over a catalogue entry.
4. [`03-integration-plan.md`](./03-integration-plan.md) — phased
   build-out, where phases are *catalogue entries shipped* rather
   than *egglog features supported*.
5. [`04-theory-catalogue.md`](./04-theory-catalogue.md) — the
   actual list of candidate (theory, decision question) pairs, each
   with a one-page entry. This is the load-bearing document.

## Recommendation in one sentence

**Build the Layer A scaffold first** (egglog as Alethe-style oracle
whose proof DAG we replay through `EThm`, reusing the SAT/SMT
replay pattern), then **instantiate it for two catalogue entries**
(EUF + one pure equational theory) end-to-end. Only once those land
should we start work on Layer B's runner. Layer C waits until the
catalogue is non-trivial enough to make `Provable_T(P)` interesting.

## Not in scope

- Implementation. These are design notes; nothing ships from this
  proposal directly.
- A custom proof format. Egglog's `Justification` set is small and
  maps cleanly onto our existing `EThm` rules; we should consume it,
  not invent our own.
- "Support all of egglog." The catalogue is explicitly a curated
  subset. If a problem doesn't fit an entry, the answer is "not
  covered" — not "extend the runtime".
- The egglog *Python wrapper* code. Documenting its API for our
  purposes; not committing to vendor or fork it.
- Containers (`Map`, `Vec`, `Set`) and primitive-sort merge
  functions beyond a sketch — those are at most a single late-phase
  catalogue entry.

# Design (planning-stage)

This directory holds **design discussions and proposals** for Covalence.
Nothing here is a committed architecture; everything is a draft awaiting
review, revision, and eventual implementation (or rejection).

For an honest snapshot of what is *actually built* (and what's stale or
superseded), see [`../where-we-are.md`](../where-we-are.md).

For the big-picture vision the proposals are working toward, see
[`../../ARCHITECTURE.md`](../../ARCHITECTURE.md) (v2) and
[`../../AGENTS.md`](../../AGENTS.md).

---

## How this directory is organized

```
docs/design/
  README.md             — this file (design directory index)
  proposals/            — concrete proposals, each in its own subdir
    <proposal-name>/
      README.md         — proposal's own index
      <doc>.md          — the proposal's design docs
```

A "proposal" here is a coherent set of design choices that hang
together. Two different proposals in this directory may make
*incompatible* claims — that's expected; they're alternatives or
revisions. The status of each proposal (proposed, under-review,
accepted, rejected, superseded) is recorded in the proposal's own
`README.md`.

---

## Active proposals

| Proposal                                                                                              | Status   | Summary                                                                                                                                  |
|-------------------------------------------------------------------------------------------------------|----------|------------------------------------------------------------------------------------------------------------------------------------------|
| [`proposals/layered-framework/`](./proposals/layered-framework/)                                       | proposed | Carve the kernel into three layers (Framework / HOL / Morphism), with stores and authorities as the framework's only trust primitives. Hash functions, signatures, executors all become oracles outside the trust boundary. |
| [`proposals/shared-backbone/`](./proposals/shared-backbone/)                                           | proposed | The *path* to the vision. Substrate-first with two parallel streams (prover + VCS) sharing a content-addressed backbone; oracle-everything stratification (Stores leave the framework; verifiable reads become oracle observations); `attest`/`decide` reframed as the first concrete oracle. Sibling to `layered-framework/`, not an alternative. |
| [`proposals/egglog-integration/`](./proposals/egglog-integration/)                                     | proposed | Curate a **patchwork of small (theory, decision question) entries** where egglog is the right engine — EUF, pure equational theories, arrays, lists, AC word problems, Datalog reachability, lattice analyses — each shipping into the kernel as its own family of `EThm`s. Two engineering layers under the catalogue (oracle replay vs. native runner) and a long-term meta-provability mode. |
| [`proposals/wasm-runtime/`](./proposals/wasm-runtime/)                                                 | proposed | Abstract `covalence-wasm`'s engine surface behind a sync-first `cov:wasm/*@0.1.0` WIT API (runtime / inspect / build) so the same code can target wasmtime, a browser JS host, or guest components; layer **process** (shared-fate graph of components) and **container** (tree of processes with restart policies) on top; end goal is a browser-resident covalence kernel powering a fully static `covalence-ui`, with federation as a longer-term follow-up. |
| [`proposals/wasm-store-composition/`](./proposals/wasm-store-composition/)                             | sketch   | Stores as content-addressed WASM components carrying their own JSON manifest in a custom section. Tree-shaped composition via a resource-typed `cov:store/api` and a `build(list<store>) -> store` factory. Roadmap: resource WIT → hash-keyed `StoreRef` → `StoreRegistry` that walks the graph. Naturally rides on top of `wasm-runtime`'s `cov:wasm/*@0.1.0` abstraction (composer-side host calls become `cov:wasm/runtime` API calls, browser/native parity for free). |

---

## Accepted / rejected proposals

(none yet)

---

## How proposals become decisions

The intent is that a proposal here is *one of several possible* design
directions. Adoption requires:

1. A round of discussion and revision in the proposal's docs.
2. Explicit acknowledgment that this is the direction we're taking
   (e.g., a note in [`../where-we-are.md`](../where-we-are.md) marking
   the proposal as "accepted" and updating the `ARCHITECTURE.md` /
   `AGENTS.md` to reflect the new direction).
3. A migration / implementation plan with phased steps that don't
   require committing to the whole proposal up front.

Until those steps are done, a proposal in this directory is just a
record of a planning conversation — useful for cross-referencing, but
not load-bearing for the codebase.

---

## What's NOT here

- **Implementation plans** for the *current* kernel. Those live in
  [`../refactor-plan.md`](../refactor-plan.md) and
  [`../prover-mvp-plan.md`](../prover-mvp-plan.md).
- **Current kernel internals.** Documented in
  [`../prover-architecture.md`](../prover-architecture.md) and
  [`../prover-primops.md`](../prover-primops.md).
- **The S-expression syntax.** Documented in
  [`../prover-sexpr.md`](../prover-sexpr.md).
- **The Prop-egraph (Phase P) design.** Documented in
  [`../prop-egraph-design.md`](../prop-egraph-design.md).

These are descriptions of what exists or what's in-flight, not
proposals for new directions.

# Shared-Backbone Proposal

> **STATUS: PROPOSED — working-draft architecture, not committed.**
>
> Sibling proposal to [`../layered-framework/`](../layered-framework/).
> Where the layered-framework proposal designs the **kernel layer**, this
> proposal designs **the path** — how the existing tree gets from where
> it is today (in [`where-we-are.md`](../../../where-we-are.md)) to a
> working substrate that both the prover and the VCS can ride.
>
> The two proposals are complementary, not alternatives:
> layered-framework says *what the kernel is*; shared-backbone says
> *how we build it without stalling everything else*.

## The shape of the proposal

- **[`00-overview.md`](./00-overview.md)** — the path. Substrate-first
  with two parallel streams (prover + VCS) sharing a content-addressed
  backbone, an oracle-everything stratification (verifiable reads,
  stores, hash schemes, executors all *outside* the TCB), and
  `attest`/`decide` reframed as the first concrete instance of an
  oracle. Four phases, each with a working tree.

## Why this exists

Two things are true at once:

1. The
   [layered-framework](../layered-framework/) proposal has the right
   kernel shape, but says nothing about how the **rest of the
   in-flight work** (three coexisting kernels, application shells
   bound to a superseded API, Phase A–H refactor, Phase P
   EProp/EThm, an unmounted FUSE scaffold, a `covalence-store`
   trait that doesn't yet expose verifiable reads) gets unwedged.
2. The prover and the VCS share a substrate that
   [`ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §11 already
   commits to (content-addressed blob store + tree store), but the
   path docs ([`prover-mvp-plan.md`](../../../prover-mvp-plan.md),
   [`refactor-plan.md`](../../../refactor-plan.md)) all design as if
   only one of them existed.

The shared-backbone proposal closes both gaps. It declares the
substrate explicitly, schedules both streams over it in parallel, and
specifies which of the in-flight phases continue, terminate, or get
absorbed.

## Cross-references

- [`../layered-framework/`](../layered-framework/) — the kernel
  layer this path targets. `02-framework.md` is the kernel
  blueprint; `04-store.md` describes Stores as a framework primitive
  — this proposal pushes them *out* of the framework into the
  oracle layer (see `00-overview.md` §3).
- [`../../../where-we-are.md`](../../../where-we-are.md) — the
  honest snapshot this proposal works from.
- [`../../../prover-mvp-plan.md`](../../../prover-mvp-plan.md) —
  superseded by this proposal's path; remains as historical
  reference.
- [`../../../refactor-plan.md`](../../../refactor-plan.md) — Phase
  A–H and Phase P are terminated by this proposal; see `00-overview.md`
  §1.
- [`../../../../ARCHITECTURE.md`](../../../../ARCHITECTURE.md) §11
  (storage) and §12 (formats) — the substrate vocabulary this
  proposal builds on.
- [`../../../../AGENTS.md`](../../../../AGENTS.md) — the TCB list.
  This proposal *narrows* it further than AGENTS.md does today
  (verifiable reads + merge-certificate checker move out into
  oracles).

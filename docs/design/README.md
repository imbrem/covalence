# Design Proposals

This directory holds design work that is intentionally separate from the
current implementation snapshot.

Nothing here should be read as “this is how the repo works today” unless some
other current-state document explicitly says that a proposal has been adopted.

For the code as it exists now, read [`../where-we-are.md`](../where-we-are.md).
For the architectural north star, read [`../../ARCHITECTURE.md`](../../ARCHITECTURE.md)
and [`../../AGENTS.md`](../../AGENTS.md).

## What Lives Here

- proposal sets for possible future architecture,
- design sketches around specific subsystems,
- planning and migration notes that are useful context but not current-state
  truth.

## Active Proposal Sets

| Proposal | Status | Summary |
|---|---|---|
| [`proposals/layered-framework/`](./proposals/layered-framework/) | proposed | Three-layer kernel direction: Framework / HOL / Morphism, with more machinery pushed out of the TCB. |
| [`proposals/stacked-pure-hol/`](./proposals/stacked-pure-hol/) | proposed | Minimal Pure/LF + HOL stack in the Isabelle/Pure tradition. |
| [`proposals/shared-backbone/`](./proposals/shared-backbone/) | proposed | Migration path centered on a shared content-addressed substrate for prover and VCS work. |
| [`proposals/egglog-integration/`](./proposals/egglog-integration/) | proposed | Catalogue-style egglog integration for selected theories and decision questions. |
| [`proposals/wasm-runtime/`](./proposals/wasm-runtime/) | proposed | WIT-shaped runtime abstraction for `covalence-wasm` across native and browser hosts. |
| [`proposals/wasm-store-composition/`](./proposals/wasm-store-composition/) | sketch | WASM components as composable content-addressed stores. |

## How To Use This Directory

- Treat proposal docs as candidate designs, not as implementation references.
- When a proposal is adopted, the current-state docs and root architecture docs
  should be updated to say so explicitly.
- If a proposal is abandoned or superseded, keep it for history but label it
  clearly.

## What Does Not Belong Here

- Literal descriptions of the current runtime surfaces
- Verified build/test instructions
- File-by-file workspace maps

Those belong in:

- [`../where-we-are.md`](../where-we-are.md)
- [`../c4.md`](../c4.md)
- [`../../README.md`](../../README.md)

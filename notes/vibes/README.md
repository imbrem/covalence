+++
id = "N000H"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "vision-consolidation"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Design corpus

`notes/vibes/` contains agent-authored design and analysis. It is deliberately
disposable: source code and generated audits describe what exists; stable TODOs
describe implementation gaps; Git preserves deleted design history.

## Read first

1. [`vision/neel-meeting-synthesis.md`](./vision/neel-meeting-synthesis.md) —
   current vision, extracted from the maintainer's meeting notes.
2. [`kernel/substrate-rewrite.md`](./kernel/substrate-rewrite.md) — nucleus,
   proton/neutron boundaries, invariants, and first rewrite plan.
3. [`plans/current-program.md`](./plans/current-program.md) — priorities and the
   portfolio DAG.
4. [`kernel/kernel-design.md`](./kernel/kernel-design.md) — current HOL kernel
   implementation, useful during migration but not the new architecture.
5. [`kernel/tcb/what-is-the-tcb.md`](./kernel/tcb/what-is-the-tcb.md) — current
   trusted surface and audit vocabulary.

## Organization

- `vision/`: durable goals and research direction.
- `kernel/`: substrate, TCB, data, and inductive designs.
- `logics/`: object logics, imports, K/SpecTec/WASM, and metatheory.
- `lisp/`: reusable Lisp semantics and ACL2 work.
- `surface/`: future mathematical authoring language.
- `web/`: browser/runtime/product designs.
- `research/`: sourced investigations and note-system conventions.
- `plans/`: only the current portfolio plan and bounded active plans.
- `handoff/`: temporary branch state; delete once absorbed.
- `sketches/`: explicitly speculative material.

## Maintenance rules

- Prefer one short authoritative note per decision boundary.
- Put acceptance criteria in source-local TODOs, not duplicated prose lists.
- Mark implementation descriptions with a date or commit when staleness matters.
- A new plan must replace or delete an old plan that covers the same scope.
- A superseded note should be deleted unless live code still needs it as
  implementation history; retained history must link to its replacement.
- Keep raw human notes intact under `notes/chats/`; syntheses belong here and
  must cite them.
- Never infer theorem authority from a database row, observation, or signature
  alone. Follow the nucleus trust policy in `kernel/substrate-rewrite.md`.

The map application and `bun run notes` provide the complete searchable index;
this README is a reading route, not a catalogue of every file.

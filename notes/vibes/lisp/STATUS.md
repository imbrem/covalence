+++
id = "N001E"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T21:35:45+01:00"
source = "legacy"
agent = "claude"
harness = "claude"

[[contributions]]
role = "editor"
actor = "agent:gpt-5.6-sol"
at = "2026-07-21T00:00:00+01:00"
source = "lisp-docs-index"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Lisp implementation snapshot

Snapshot against `f5e18d6e` (2026-07-21). This page describes implemented
boundaries, not planned features. Stable TODO markers remain the work queue.

## Implemented

- `covalence-kernel-lisp` owns backend-neutral `CoreExpr`, evaluation strategy,
  CEK transitions, finite traces, bounded relational exploration, effects, and
  admission capability interfaces.
- The same CEK transition code runs over direct Rust values, opaque resource
  arenas, and an inductive S-expression realization.
- Scheme supports lexical closures, recursive definitions, first-class
  `apply`, atomic duplicate-checked definition groups, and handled I/O in the
  host/runtime path. ACL2 consumes the same lowered `Definition` boundary.
- Forsp uses the separate generic stack-machine capability because its
  concatenative semantics is not CEK application in disguise.
- The HOL frontend has equational and relational adapters. Concrete checked
  executions can cross into HOL without treating host evaluation as theorem
  authority.
- ACL2 has readers, event/world handling, book linking, a checked derivation
  path, corpus reporting, and concrete operational evidence through the common
  Lisp runtime.

The narrow regression commands are:

```sh
cargo test -p covalence-kernel-lisp
cargo test -p covalence-lisp --lib --all-features
cargo test -p covalence-lisp --features hol --test backend_conformance
```

## Open gates

| Boundary | Stable TODOs |
|---|---|
| Honest ACL2 totalization over common Lisp execution | `lisp.acl2.admission-layer` |
| Proof-producing frontend parity | `lisp.frontends.scheme-forsp` |
| HOL list/application semantics | `lisp.hol.apply-list`, `lisp.hol.variadic-closures` |
| HOL evaluation strictness and values | `lisp.hol.strict-sequence`, `lisp.hol.first-class-primitives`, `lisp.hol.numeric-datum-sum` |
| Recursive Scheme in HOL | `lisp.scheme.letrec-hol` |
| ACL2 read-time fidelity | `acl2.api.read-time-capability-split`, `acl2.reader.dispatch-macros` |
| ACL2 test latency | `lisp.acl2.induction-test-performance` |

The severe gate is the ACL2 admission boundary. Concrete traces establish only
that a particular execution reaches a value. Total HOL functions require
checked termination plus existence and uniqueness for every admitted input.

## Avoided collapses

- Do not put ACL2 worlds, events, or totality assumptions in `kernel/lisp`.
- Do not identify host execution with proof replay.
- Do not merge the equational and relational HOL adapters merely because both
  return theorems; their judgments differ.
- Do not force Forsp through an applicative machine.
- Do not duplicate open-work prose here. Update the stable marker and regenerate
  the TODO database.

Start from [`README.md`](./README.md) for source and design links.

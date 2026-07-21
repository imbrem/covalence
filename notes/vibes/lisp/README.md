+++
id = "N001D"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T21:25:20+01:00"
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

# Lisp and ACL2

This is the entry point for the reusable Lisp foundation and the ACL2 layer
above it. For current implementation facts, read [`STATUS.md`](./STATUS.md).
For concrete work, query the `lisp-foundation` project and its stable TODOs:

```sh
bun run notes -- --task lisp-foundation
bun run todos -- --list --search lisp
bun run todos -- --list --search acl2
```

## Layering

```text
S-expression data
  → backend-neutral syntax, values, environments, and partial execution
  → Scheme, Sector, and Forsp frontend policy
  → ACL2 terms, events, admissible worlds, and checked derivations
  → HOL transport
```

Generic Lisp permits divergence and stuck states. ACL2 adds checked termination,
uniqueness, admission, and proof rules; it must not make the generic layer
total. [`lisp-first-acl2-redirect.md`](./lisp-first-acl2-redirect.md) records
this boundary.

## Source map

| Concern | Source |
|---|---|
| Abstract S-expressions | [`crates/kernel/lisp/sexpr`](../../../crates/kernel/lisp/sexpr/) |
| Core syntax and strategies | [`kernel/lisp/src/syntax.rs`](../../../crates/kernel/lisp/src/syntax.rs) |
| CEK machine and transition labels | [`kernel/lisp/src/host.rs`](../../../crates/kernel/lisp/src/host.rs) |
| Runtime/value capabilities | [`kernel/lisp/src/runtime.rs`](../../../crates/kernel/lisp/src/runtime.rs) |
| Trace, exploration, and replay APIs | [`kernel/lisp/src/relation.rs`](../../../crates/kernel/lisp/src/relation.rs) |
| Direct, resource, and inductive runtimes | [`host.rs`](../../../crates/kernel/lisp/src/host.rs), [`arena.rs`](../../../crates/kernel/lisp/src/arena.rs), [`inductive_runtime.rs`](../../../crates/kernel/lisp/src/inductive_runtime.rs) |
| Scheme/Sector/Forsp frontends | [`crates/lang/lisp/src`](../../../crates/lang/lisp/src/) |
| ACL2 frontend, worlds, and books | [`acl2.rs`](../../../crates/lang/lisp/src/acl2.rs), [`world.rs`](../../../crates/lang/lisp/src/world.rs), [`book.rs`](../../../crates/lang/lisp/src/book.rs) |
| ACL2 proof model | [`crates/kernel/hol/init/src/init/acl2`](../../../crates/kernel/hol/init/src/init/acl2/) |

The shared API is tagged `A0022` in
[`kernel/lisp/src/lib.rs`](../../../crates/kernel/lisp/src/lib.rs). The project
manifest is [`notes/projects/lisp-foundation.toml`](../../projects/lisp-foundation.toml).

## Read by task

- Architecture and current gaps: [`STATUS.md`](./STATUS.md).
- Lisp/ACL2 semantic boundary: [`lisp-first-acl2-redirect.md`](./lisp-first-acl2-redirect.md).
- Representation boundary: [`abstract-sexpr-api.md`](./abstract-sexpr-api.md).
- ACL2 behavior deviations: [`acl2-fidelity.md`](./acl2-fidelity.md).
- Corpus milestone and commands: [`acl2-green-islands.md`](./acl2-green-islands.md).
- ACL2 implementation orientation: [`acl2-agent-guide.md`](./acl2-agent-guide.md).

The `acl2-s*` plans and `initial-ideas/` explain how the present code arose.
They are historical design material, not current task lists. Branch handoffs are
temporary evidence and should be deleted after their facts reach this index,
the fidelity ledger, or source-local TODOs.

## Shared reduction work

Lisp and K both need checked finite reduction evidence, but their semantics are
not one API: Lisp uses environments, closures, continuations, and effects; K
uses matching and congruence over rewrite rules. Reuse should occur below those
policies—in relation closure, trace evidence, rule replay, and theorem
transport—only when the proof obligations coincide. See the
[`K index`](../k/README.md) before extracting a common layer.

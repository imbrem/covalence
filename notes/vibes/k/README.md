+++
id = "N000N"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T19:57:49+01:00"
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

# K

This is the entry point for K surface/KORE ingestion and checked HOL
rewriting. Query the project and stable TODOs before starting work:

```sh
bun run notes -- --task k-framework
bun run todos -- --list --search lang.k
bun run todos -- --list --search kernel.hol.init.src.k
```

## Implemented path

```text
.k tutorial fragment ─┐
                     ├→ rewrite rules → matcher/driver → checked KStep/KReduces
textual KORE ─────────┘
```

- [`crates/lang/k`](../../../crates/lang/k/) is untrusted parsing and data:
  textual KORE, a `.k` tutorial fragment, fragment classification, grammar
  lowering, and S-expression rendering.
- [`crates/kernel/hol/init/src/k`](../../../crates/kernel/hol/init/src/k/) owns
  HOL encoding, matching, congruence, rule replay, reflexive-transitive
  reduction, and sessions.
- [`examples/k-demo`](../../../crates/lang/k/examples/k-demo/) exercises Peano,
  boolean simplification, and the K tutorial color example.

## Open gates

The next semantic layers are recorded beside the implementation:

- builtin hooks and guarded rewriting:
  `kernel.hol.init.src.k.no-builtin-hooks-f1` and
  `kernel.hol.init.src.k.guarded-rewriting-is-stratified-sound-incomplete`;
- cells, KSequence, and heating/cooling:
  `kernel.hol.init.src.k.no-cells-ksequence-heating-cooling`;
- capture-avoiding substitution and binders:
  `kernel.hol.init.src.k.no-substitution-binders`;
- KORE claims and frontend parity:
  `lang.k.claims-reachability-layer-unconsumed`,
  `lang.k.no-k-kore-bridge`, and the remaining `lang.k.*` ingestion markers.

[`reduction-demo-scope.md`](./reduction-demo-scope.md) is the detailed design
and implementation history. [`../vision/k-framework-vision.md`](../vision/k-framework-vision.md)
states the longer-term role. The files in [`research/`](./research/) are sourced
background, not implementation status.

## Reuse boundary with Lisp

K rewriting and Lisp evaluation share closure and replay concepts, but not
machine state or rule policy. A common abstraction is justified only where it
removes duplicate relation-closure or theorem-replay code while preserving the
distinct K matcher/congruence and Lisp environment/continuation semantics. See
the [`Lisp index`](../lisp/README.md) and keep such extraction below both
frontends.

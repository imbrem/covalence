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
  admission capability interfaces. Its shared `LispAtom<I, B, F>` independently
  abstracts exact integers, text bytes, and string-format labels;
  `LispPrimitive` supplies stable applicative primitive identifiers and
  structural metadata without fixing their implementation.
- The same CEK transition code runs over direct Rust values, opaque resource
  arenas, and an inductive S-expression realization.
- Scheme supports lexical closures, recursive definitions, first-class
  `apply`, sequential and named `let`, short-circuit `and`/`or`, Scheme `cond`
  test-value, `=>`, and sequence clauses, nested quasiquotation with unquote
  and list splicing, atomic
  duplicate-checked definition groups, and handled I/O in the host/runtime
  path. Derived forms lower hygienically to the common core and run unchanged
  over direct, resource-handle, and inductive values. Top-level values and
  recursive procedures are distinct in the shared API. Groups expose lexical
  call dependencies. ACL2 consumes
  the same lowered `Definition` boundary; dependency-first recursive
  components identify definitions that must be admitted together. ACL2
  specializes the common structural recursion checker with its `car`/`cdr`
  descent policy.
- Forsp uses the separate generic stack-machine capability because its
  concatenative semantics is not CEK application in disguise. The same
  program produces checked `MayEval` evidence over direct, opaque-resource,
  and `data/inductive` stack-value representations.
- The HOL frontend has equational and relational adapters. Concrete checked
  executions can cross into HOL without treating host evaluation as theorem
  authority. Ground S-expression equality is structural and proof-producing:
  it recursively uses the shared carved constructors' injectivity and
  distinctness theorems. `null?` and Scheme `not` therefore use exact equality
  with `nil`, rather than conflating every non-cons atom with the false value.
  The default `#lang lisp` selects the relational exact-datum backend, so
  integers inhabit the `int ⊕ bytes` atom payload and remain ordinary data
  under quotation, projection, predicates, and arithmetic. The older
  auxiliary-injection backend remains available for backend comparisons.
- ACL2 has readers, event/world handling, book linking, a checked derivation
  path, corpus reporting, and concrete operational evidence through the common
  Lisp runtime. Scheme lowering and ACL2 event-time macros now consume the
  same depth-checked quasiquote plan, while interpreting evaluations in their
  respective runtimes. Their quote-family reader abbreviations share one
  scanner, parameterized by Scheme versus ACL2 case, string, character, radix,
  block-comment, and sharp-dot policy.
- Plain, Scheme, and ACL2 readers can lower directly through the shared
  `SExprSyntax` constructor capability. Forsp quotation now uses that same
  fold into the free inductive backend instead of maintaining its own list
  recursion. The carved HOL and ACL2 carriers implement the same constructor
  and one-layer view capabilities. Surface numeral and ACL2 canonicalization
  live in the higher `LispDatum` codec; the duplicate parser-owned
  `AbstractSExpr` trait has been removed.
- The obsolete language-local `Lisp` trait has also been removed. `LispHol`
  now implements `SExprSyntax` plus the narrowly layered `LispDatumSyntax`;
  symbolic theorem production remains a separate strategy. The kernel's
  `LispSyntax` name is reserved for executable core-expression construction.
- The equational HOL compiler eliminates constant-condition branches before
  type checking, so Scheme `cond` with a final true clause supports recursive
  integer results without forcing its unreachable fallback into `sexpr`.
- Equational definitions expose `DefinitionResult` and
  `install_core_definition_as`: typed ACL2/Scheme clients can select and
  transactionally verify Bool, Datum, or Integer results. Unannotated source
  remains a compatibility inference layer over that checked API.

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

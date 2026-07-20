+++
id = "N005B"
status = "draft"
review = "unreviewed"
[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "repository-snapshot-cd384d36"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Lisp at `cd384d36`

## Implemented

`crates/kernel/lisp` supplies neutral `CoreExpr` import/export, scope and
evaluation strategies, generic runtime/environment/closure APIs, opaque arena
resources, applicative and stack machines, finite traces, `MayEval`, bounded
exploration, replay/transport, suspend/resume effects, and total-admission
vocabulary. `crates/lang/lisp` supplies Scheme, Sector/Forsp, and ACL2-facing
sessions, readers, host execution, HOL semantics, and conformance tests.

## Holes

- The legacy REPL bypasses the abstract reduction strategy.
- HOL semantics lack strict sequencing, variadic closures, proper-list `apply`,
  first-class primitives, `letrec`, and uniform exact-integer data.
- The abstract S-expression migration and naming cleanup are incomplete.
- Legacy typing still guesses some function shapes.
- Forsp lacks a proof-producing backend.

## Substrate role

Machine configurations, steps, traces, recursive definitions, and effects fit
relations; proton runtimes remain fast indexes. Lisp tests whether the SQLite
form can remain canonical without forcing all execution through slow row-wise
operations.


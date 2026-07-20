+++
id = "N005C"
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

# ACL2 at `cd384d36`

## Implemented

The ACL2 wave has reader/session and API seams; ordered worlds, events,
packages, includes, local/generated events, linked books and blockers; corpus
progress CLI/benchmarks; selected `acl2-count`, `NFIX`, and `IFIX` green
islands; definition, ordinal, simplification, fixer, count, and APPEND
machinery; concrete common-Lisp traces transported into relational/equational
HOL; universal APPEND reachability; and a reified APPEND graph with checked
existence/uniqueness.

## Holes

- `lisp.acl2.admission-layer`: general configurations and terminal values are
  not reified enough for honest arbitrary-definition existence/uniqueness.
- APPEND graph adequacy is specialized, not a generic admission pipeline.
- S7 measured/mutual recursive admission is incomplete.
- Reader dispatch macros and read-time capability separation remain open.
- Community-books and x86 coverage are far from complete.
- Cold proof tests take minutes; an APPEND integration test remains disabled.

## Forward path

Keep ACL2 over reusable partial Lisp. Store worlds, events, admission evidence,
definitions, and corpus progress relationally; use joins for analysis but
checked replay for theorem authority. The next semantic milestone is one
recursive definition with termination, existence, uniqueness, conservative HOL
totalization, and one open theorem transported without hypotheses.


+++
id = "N0059"
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

# Substrate at `cd384d36`

## Implemented

- Audited base/HOL crates and generated dependency/TCB reports.
- Backend-independent logic/relation, data, Nat, and Int APIs.
- Memory and SQLite content stores under `crates/store/core` and sync/async
  storage capabilities under `crates/store/kv`.
- Content-addressed table/tree/commit objects under `crates/vcs/object`.
- The current content-store-oriented `crates/kernel/core` shell.

These are candidates for reuse, not the settled substrate. The current audit is
1,496 base source lines, zero unsafe, and 24 mint sites; base+HOL is 6,951 lines
and the eval tier is 13,281.

## Designed, not implemented

[`N0056`](../../plans/relational-design.md),
[`N0054`](../../vibes/kernel/substrate-rewrite.md), and
[`N0057`](../../vibes/kernel/trusted-database-algebra.md) define the target:
SQLite neutron state, optimized proton witnesses, future e-graphs, and a tiny
trusted SQL/multi-database algebra.

## Largest holes

- No `Set`/`Relation`/`Witness`/`MThm` substrate API or schema metamodel.
- No `DEF`/`USE`/`NAME`, projections, or scoped completeness.
- No trusted/untrusted DB capabilities, trusted merge, candidate filtering,
  proof promotion, or rooted subDB extraction.
- No canonical signed snapshot format.
- Proton/neutron atomicity, handle generations, rollback, and concurrency are
  not implemented.
- Consumers remain coupled to the current HOL representation and init layer.

## Next acceptance point

Build `Tm`, `Ty`, `App`, and `HasTy` twice. Cross-check lookup, projection,
equi-join, trusted union, candidate intersection, and promotion between SQLite
and a tiny interpreter, including canonical rows, `MThm`s, and trust manifests.


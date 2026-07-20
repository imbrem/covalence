+++
id = "N005D"
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

# K at `cd384d36`

## Implemented

`crates/lang/k` is kernel-free data plumbing: textual KORE parsing, plain ASTs,
deterministic S-expression rendering, axiom classification, and rewrite-rule
extraction. A separate small `.k` frontend parses syntax declarations and
lowers grammar/rules to shared CFG and rule structures. Examples and tests cover
the current fragments.

## Holes

- No checked KORE-to-HOL relation/rewrite lowering.
- No checked `.k` ↔ KORE bridge.
- No KORE-JSON or KAST-JSON ingestion.
- Matching-logic claims, reachability, side conditions, cells, collections, and
  configuration semantics are not end-to-end.
- K-WASM versus SpecTec-WASM consilience remains a north star.

## Substrate role

Rules, premises, claims, and reachability edges naturally form neutron tables;
trusted joins can select applicable rules after the exact rule API exists. The
first milestone is a tiny KORE fragment lowered to the same relation as a
hand-authored ruleset, with equal exported steps.


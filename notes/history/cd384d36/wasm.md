+++
id = "N005E"
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

# WASM and SpecTec at `cd384d36`

## Implemented

`crates/lib/wasm/spectec` has SpecTec parsing, bundled WASM 3 grammar,
parameterized/indexed grammar IR, regex conversion, byte-CFG lowering,
recognition mode, coverage, and tests. `covalence-init` has SpecTec expression
encoding/denotation, sort/type-family analysis, semantic relations, builtin and
decision lowering, slicing, totality scaffolding, trace chains, and transport
hooks.

## Holes

- Sortless metavariable, condition, and store-update approximations remain.
- Exact carriers, closed Church signatures, constructor laws, and dependent
  refinements are incomplete.
- Only 5/125 semantic relations have exact structural lifting.
- Composite applicability/totality and several builtins remain opaque.
- Only WASM 3 is wired; `.watsup`, indexed grammar lowering, and end-to-end
  `parse_defs` semantics are incomplete.
- Real-engine trace certification and the WIT kernel API have not started.

## Substrate role

Model start-init, linking, finish-init, and calls as state relations. Runtime,
version, subset, and concrete executor trust remain separate. Lift observations
uninterpreted into HOL, then compare SpecTec and K semantic bridges. Workers can
return execution subDBs for signature acceptance or replay.


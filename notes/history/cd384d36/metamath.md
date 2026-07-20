+++
id = "N005A"
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

# Metamath at `cd384d36`

## Implemented

`crates/proof/metamath` has include-aware parsing and `DatabaseSink`, database
and substitution models, compressed/uncompressed verification, proof traces,
emission, typesetting metadata, axiom/provability closure, theory families,
interpretation/renaming structures, HOL tests, set.mm tests, and a benchmark.
It is the most mature importer and primary scale baseline.

## Holes

- `proof.metamath.kernel-level-transport`: interpretation certificates remain
  substantially Rust-checked.
- Definitional-extension conservativity and derived witness bridges are open.
- `$d` reshaping, emitter fidelity, and proof search are incomplete.
- set.mm parsing is not fully streaming and symbols are not interned.
- Native-HOL/Metamath equivalence and the headline Peano proof remain open.

## Substrate role

Use table-backed symbols, statements, hypotheses, dependencies, and theorem
roots while keeping parser/verifier APIs stable. Compare statements,
assumptions, time, memory, rows, and snapshot size across old/new backends.


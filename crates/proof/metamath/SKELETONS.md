# Skeletons — covalence-metamath

Deferred work in this crate (the Metamath substitution engine + `.mm` format/IO
reader, the lower HOL-free crate). Consumer-side bridge deferrals (`#logic` /
`Derivable_L`, the import tactic + representation-equivalence metatheorem) live in
`covalence-init` ([`metalogic/SKELETONS.md`](../../kernel/hol/init/src/metalogic/SKELETONS.md),
[`peano/SKELETONS.md`](../../kernel/hol/init/src/peano/SKELETONS.md)). See repo
[`CLAUDE.md`](../../../CLAUDE.md) § Skeletons and the [root index](../../../SKELETONS.md).

## Deferred features (north stars)

- **HOL-backed `DatabaseSink` over an arbitrary database.** The prop fragment is
  done (`covalence-init`'s `HolPropSink` → `⊢ Derivable_Prop ⌜S⌝`). Remaining: a HOL
  sink over an arbitrary database (`RuleSet`-from-`Database` / schema-database
  replay → `⊢ Derivable_DB ⌜db⌝ ⌜S⌝`) — tracked in `covalence-init`'s
  `metalogic/SKELETONS.md`.
- **`set.mm`-scale streaming/incremental parsing.** The reader tokenises the whole
  source string up front (`parse` takes `&str`), so all ~48 MB of `set.mm` must be
  in memory. Acceptable today (~6 s parse+verify in release); a streaming reader is
  still a north star.
- **Canonical `.mm` serializer.** No in-crate emitter; the round-trip test
  (`tests/mm_file.rs`) ships a minimal test-local one.
- **Structured-tree (grammar-parsed) expression encoding.** `Expr` is a typecode +
  flat `body: Vec<Symbol>` (faithful flat sequences). A grammar pass to structured
  trees would help metatheory but reintroduces grammar ambiguity, so it's deferred
  to the untrusted bridge layer.
- **Symbol interning for `set.mm` scale.** `Symbol` is an owned `SmolStr`; tables
  use `HashMap`, no interning/arenas. Not a correctness or practical-speed blocker
  (~5 s for 47,394 theorems); interning + a flat statement arena + incremental
  construction remain a perf/memory north star (~50 MB footprint).

(`tests/set_mm.rs` is an intentional env-gated `#[ignore]` — needs
`COV_SET_MM=/path/to/set.mm`, ~48 MB not vendored — not deferred work.)

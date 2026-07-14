# Skeletons — covalence-metamath

Deferred work in this crate (the Metamath substitution engine + `.mm` format/IO
reader, the lower HOL-free crate). Consumer-side bridge deferrals (`#logic` /
`Derivable_L`, the import tactic + representation-equivalence metatheorem) live in
`covalence-init` ([`metalogic/SKELETONS.md`](../../kernel/hol/init/src/metalogic/SKELETONS.md),
[`peano/SKELETONS.md`](../../kernel/hol/init/src/peano/SKELETONS.md)). See repo
[`CLAUDE.md`](../../../CLAUDE.md) § Skeletons and the [root index](../../../SKELETONS.md).

## Axiom-set / interpretation metatheory (`axioms.rs`, `interpret.rs`)

- **Definitional-extension conservativity.** `check_implication` / interpretation
  *admit* `df-*` definitions (reported, not discharged): the reals result is
  "reals ⊆ ZFC **+ definitions**". A metatheorem that a definitional extension
  is conservative (each `df-*` eliminable) would discharge them. Includes
  definition unfolding/renaming as statement transformers.
- **Derived-witness bridges.** Implication/interpretation witnesses are existing
  `tgt` assertions with an *identical* statement. The 3 unmatched core IZF
  axioms (`ax-coll`/`ax-setind`/`ax-iinf`, see `tests/interpret.rs`) need a
  witness that is a small `tgt` *proof* (collection from replacement, set
  induction from foundation), not an existing same-statement assertion.
- **`$d`-reshaping statement matching.** `same_statement_mod_renaming`
  (`interpret.rs`) now matches up to a *bijective variable renaming* (constants
  and typecodes fixed). Witnesses that differ only by a `$d`-*reshaping* beyond a
  bijective renaming (e.g. splitting/merging distinct-variable groups, or a
  witness needing a genuinely different `$d` structure) are still rejected; a
  fuller `$d`-normalising matcher would widen witness auto-search further.
- **Kernel-level transport.** `Implication`/`InterpretationCert` are Rust-checked
  certificates (untrusted tooling), not kernel `⊢ Derivable_A ⌜S⌝ ⟹
  Derivable_B ⌜σS⌝` theorems. Reifying them via the metalogic engine is the
  `transport_db` structural-σ program (`covalence-init` metalogic SKELETONS).

## Deferred features (north stars)

- **HOL-backed `DatabaseSink` over an arbitrary database.** A HOL
  sink over an arbitrary database (`RuleSet`-from-`Database` / schema-database
  replay → `⊢ Derivable_DB ⌜db⌝ ⌜S⌝`) — tracked in `covalence-init`'s
  `metalogic/SKELETONS.md`.
- **`set.mm`-scale streaming/incremental parsing.** The reader tokenises the whole
  source string up front (`parse` takes `&str`), so all ~48 MB of `set.mm` must be
  in memory. Acceptable today (~6 s parse+verify in release); a streaming reader is
  still a north star.
- **Structured-tree (grammar-parsed) expression encoding.** `Expr` is a typecode +
  flat `body: Vec<Symbol>` (faithful flat sequences). A grammar pass to structured
  trees would help metatheory but reintroduces grammar ambiguity, so it's deferred
  to the untrusted bridge layer.
- **Symbol interning for `set.mm` scale.** `Symbol` is an owned `SmolStr`; tables
  use `HashMap`, no interning/arenas. Not a correctness or practical-speed blocker
  (~5 s for 47,394 theorems); interning + a flat statement arena + incremental
  construction remain a perf/memory north star (~50 MB footprint).
- **Emitter fidelity (`emit.rs`).** `Database::to_mm_string` re-parses to a
  *structurally-equivalent* database (verified on demo0 + hol.mm), but is
  **normalising**: it emits one global `$f` per label (a *scoped* `$f` that
  re-types the same variable in two scopes is flattened), re-labels shared `$e`
  per block, and drops source comments / `$[ include $]`. Byte-faithful,
  comment-preserving re-serialisation is a north star.

(`tests/set_mm.rs` is an intentional env-gated `#[ignore]` — needs
`COV_SET_MM=/path/to/set.mm`, ~48 MB not vendored — not deferred work.)

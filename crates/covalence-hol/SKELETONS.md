# Skeletons — `covalence-hol`

Crate-level index of intentional placeholders in `covalence-hol` (the non-TCB
HOL shell over `covalence-core`). Entries live in the per-module `SKELETONS.md`
files co-located with the code. See [`CLAUDE.md`](../../CLAUDE.md) § Skeletons
and the [root index](../../SKELETONS.md).

## Per-module registries

- **[`src`](./src/SKELETONS.md)** — crate-root `*.rs`: the multi-file `.cov` project loader (`project.rs`) — Rust↔`.cov` mutual recursion, single-`Project` `init/mod.rs` fold, WASM project units, concurrent compilation.
- **[`src/init`](./src/init/SKELETONS.md)** — theory catalogue: `rat`/`real` postulates pending proof; partial inductive engine, `list`, `prod`.
- **[`src/script`](./src/script/SKELETONS.md)** — `.cov` proof authoring + replay: pluggable unifier, proof/`Term` printer, async core + holes, `#dep`/`#spawn`, error spans, typed pipeline, WASM/WIT kernel API.
- **[`src/models`](./src/models/SKELETONS.md)** — surface-compiler core: general `Signature`/`HandlerSet`, `#model` directive, multi-theory/iso shape.
- **[`src/regex`](./src/regex/SKELETONS.md)** — regex → byte-predicate compiler: recognizer acceleration, `prove_member` discharge, `prove_word` variable matching, word normalisation.
- **[`src/spectec`](./src/spectec/SKELETONS.md)** — SpecTec grammar front end: primitive CFG stratum (`Var`/`Derives`), whole-`gram`/full-WASM-binary coverage.
- **[`src/metalogic`](./src/metalogic/SKELETONS.md)** — generic `Derivable_L` engine: `set.mm` rule-set scaling (`transport_db`), `S`-transport / `Metamath-L ≅ native-L` north stars.
- **[`src/peano`](./src/peano/SKELETONS.md)** — deep PA embedding: quantifier/induction/Leibniz derivation constructors (β-capture wall), the `.cov` surface (Phase C).
- **[`src/ring`](./src/ring/SKELETONS.md)** — sum-of-monomials normalizer: coefficient collection, `neg`/`sub` expansion, literal folding, `Semiring`/`Ring`-generic rewrite.

`src/surface/` was **removed** — superseded by the `script`
`#sig`/`#thy`/`#model`/`#models` fusion (`notes/surface-compiler.md §3.0`); to be
rebuilt as the elaborator down to `.thy` (`§3.0.4`). Recover the old sketch from
git history.

The Metamath substitution engine moved to the HOL-free
[`covalence-metamath`](../covalence-metamath/SKELETONS.md) crate; its
engine/reader deferrals are tracked there, the consumer-side bridge in
`src/metalogic` above.

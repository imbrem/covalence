# Skeletons — `covalence-init`

Crate-level index of intentional placeholders in `covalence-init` (the
semi-trusted API over `covalence-core`). Entries live in the per-module
`SKELETONS.md` files co-located with the code. See [`CLAUDE.md`](../../../../CLAUDE.md)
§ Skeletons and the [root index](../../../../SKELETONS.md).

## Per-module registries

- **[`src`](./src/SKELETONS.md)** — crate-root `*.rs`: the multi-file `.cov` project loader (`project.rs`) — Rust↔`.cov` mutual recursion, single-`Project` `init/mod.rs` fold, WASM project units, concurrent compilation; `sexp.rs` one-way `nat-lit`/`int-lit`/`bool-lit` serialize forms (no parse arms).
- **[`src/init`](./src/init/SKELETONS.md)** — theory catalogue: `rat`/`real` postulates pending proof; partial inductive engine, `list`, `prod`.
- **[`src/script`](./src/script/SKELETONS.md)** — `.cov` proof authoring + replay: pluggable unifier, proof/`Term` printer, async core + holes, `#dep`/`#spawn`, error spans, typed pipeline, WASM/WIT kernel API.
- **[`src/models`](./src/models/SKELETONS.md)** — surface-compiler core: general `Signature`/`HandlerSet`, `#model` directive, multi-theory/iso shape.
- **[`src/grammar/regex`](./src/grammar/regex/SKELETONS.md)** — regex → byte-predicate compiler: recognizer acceleration, `prove_member` discharge, `prove_word` variable matching, word normalisation.
- **[`src/grammar/spectec`](./src/grammar/spectec/SKELETONS.md)** — SpecTec grammar front end: primitive CFG stratum (`Var`/`Derives`), whole-`gram`/full-WASM-binary coverage.
- **[`src/wasm`](./src/wasm/SKELETONS.md)** — SpecTec → kernel (WASM-spec acceleration): relation→`Derivable_R` lowering built; syntax/function lowering, richer premises/exprs, trace certification, mirror-principle check pending.
- **[`src/metalogic`](./src/metalogic/SKELETONS.md)** — generic `Derivable_L` engine: `set.mm` rule-set scaling (`transport_db`), `S`-transport / `Metamath-L ≅ native-L` north stars.
- **[`src/peano`](./src/peano/SKELETONS.md)** — deep PA embedding: quantifier/induction/Leibniz derivation constructors (β-capture wall), the `.cov` surface (Phase C).
- **[`src/algebra/ring`](./src/algebra/ring/SKELETONS.md)** — sum-of-monomials normalizer: coefficient collection, `neg`/`sub` expansion, literal folding, `Semiring`/`Ring`-generic rewrite.

`src/surface/` was **removed** — superseded by the `script`
`#sig`/`#thy`/`#model`/`#models` fusion (`notes/vibes/surface-compiler.md §3.0`); to be
rebuilt as the elaborator down to `.thy` (`§3.0.4`). Recover the old sketch from
git history.

The Metamath substitution engine moved to the HOL-free
[`covalence-metamath`](../../../proof/metamath/SKELETONS.md) crate; its
engine/reader deferrals are tracked there, the consumer-side bridge in
`src/metalogic` above.

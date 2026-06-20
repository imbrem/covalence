# Skeletons — `covalence-hol`

Crate-level index of intentional placeholders in `covalence-hol` (the non-TCB
HOL shell over `covalence-core`). Per the new per-crate / per-module policy,
the actual entries live in `SKELETONS.md` files co-located with the code they
describe. See `CLAUDE.md` § Skeletons for the rules and the [root
index](../../SKELETONS.md).

## Per-module registries

- **[`src/SKELETONS.md`](./src/SKELETONS.md)** — crate-root `src/*.rs` modules:
  the multi-file `.cov` project loader (`project.rs`) — deferred Rust↔`.cov`
  mutual recursion, the single-`Project` `init/mod.rs` fold, and the
  WASM-against-abstract-API + Cargo-features distribution framing.
- **[`src/init/SKELETONS.md`](./src/init/SKELETONS.md)** — the `init/*` theory
  catalogue: the `rat` quotient + ordered-field theory and the `real`
  Dedekind-cut theory (postulates pending proof), and the partial subsystems —
  the inductive-type engine (`init/inductive/`), the `list` theory, and the
  `prod` theory.
- **[`src/script/SKELETONS.md`](./src/script/SKELETONS.md)** — the
  S-expression proof authoring + replay layer: best-effort inference, the
  first-order unifier / pluggable-unifier gap, the missing proof/`Term`
  printer, the async core + channel/hole rebuild, `#dep`/`#spawn` semantics,
  error spans + traces, the typed pipeline, async const lookup, term-level
  holes, and the WASM/WIT kernel API.
- **[`src/surface/SKELETONS.md`](./src/surface/SKELETONS.md)** — the
  surface-syntax authoring sketch (the elaborator, `#by` tactic grammar, and
  `#import` content addressing are stubbed above the implemented AST / builtin
  registry / parser).

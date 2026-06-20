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
- **`src/surface/` was removed** — the surface-syntax design sketch (AST /
  builtin registry / parser, with a stubbed elaborator) is superseded by the
  `script` `#sig`/`#thy`/`#model`/`#models` fusion (`docs/surface-compiler.md
  §3.0`). The Haskell-like surface is to be rebuilt as the elaborator *down to*
  `.thy` (`§3.0.4`); recover the old sketch from git history if needed.
- **[`src/models/SKELETONS.md`](./src/models/SKELETONS.md)** — the minimal
  surface-compiler core (the `Logic`/`Model` triad + cross-model `add_comm`
  replay): the `Nat`-specialized `Logic` (no general `Signature`/`admits`/full
  `HandlerSet`), the unbuilt `#model` directive, the `#thm`-only `#in` block,
  and the single-theory/two-model/no-iso shape.

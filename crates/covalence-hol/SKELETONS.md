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
- **[`src/peano/SKELETONS.md`](./src/peano/SKELETONS.md)** — the deep
  Peano-arithmetic embedding (Phases A–B done: reified locally-nameless FOL
  syntax + substitution, the `nat` denotation, the PA axioms/rules/induction
  schema, and the worked `∀x. x+0=x` by induction-on-derivations, all proven).
  Deferred: the ∀-closed *impredicative* soundness theorem (`prop.rs`-style
  `inst d := ⟦·⟧` fold — soundness is currently constructive per-derivation),
  and the `.cov` surface (Phase C: `(pa-induct …)` + β/η-aware `#concl`).
- **[`src/metamath/SKELETONS.md`](./src/metamath/SKELETONS.md)** — the Metamath
  substitution engine (expression model + substitution + frames + RPN checker):
  the not-yet-built `#logic` / `Derivable_L` / `S`-transport correspondence
  layer, the import-tactic + representation-equivalence metatheorem bridge, the
  deferred structured-tree encoding, and `set.mm` scale. (The `.mm` *reader*
  deferrals live in the separate `covalence-metamath` crate.)
- **[`src/metalogic/SKELETONS.md`](./src/metalogic/SKELETONS.md)** — databases
  as first-class HOL data + the relation lattice (`docs/theories-models-and-logics.md`
  §5.6; the first cut of `metamath`'s deferred `Derivable_L` layer). Done:
  `Database := Φ → bool`, `Derivable_DB` on the impredicative engine, extension
  `⊑` + the proved monotonicity theorem with a concrete transport. Deferred:
  the `∃ValidProof ⟺ impredicative` grounding bridge, the `⟹_σ` interpretation
  transport (stretch), and the north stars (conservative extension, `≅`, the
  category of databases, lifting `metamath::Database` / `peano::mm_pa`).

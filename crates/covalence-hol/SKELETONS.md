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
- **[`src/metalogic/SKELETONS.md`](./src/metalogic/SKELETONS.md)** — the
  generic `Derivable_L` engine (`Derivable_L` + `Closed_L` over a `RuleSet`,
  `rule_induction`, one-step `project`; the `toy` second instance; PA wired in
  as an instance). Deferred: the Metamath-`Database` → `Derivable_L` connection
  (the `#logic`-semantics seed) and the `S`-transport / `Metamath-L ≅ native-L`
  north stars.
- **[`src/peano/SKELETONS.md`](./src/peano/SKELETONS.md)** — the deep
  Peano-arithmetic embedding (Phases A–B done: reified locally-nameless FOL
  syntax + substitution, the `nat` denotation, the PA axioms/rules/induction
  schema, the **pure `Derivable_PA` + single internalized soundness theorem +
  one-step projection** — now an *instance* of the generic
  [`metalogic`](./src/metalogic/SKELETONS.md) engine). Deferred: the
  quantifier/induction/Leibniz **derivation constructors** (the motive
  β-capture wall — see the peano registry for the corrected diagnosis) and the
  `.cov` surface (Phase C: `(pa-induct …)` + β/η-aware `#concl`).
- The **Metamath substitution engine** (expression model + substitution +
  frames + RPN checker) now lives in the lower, HOL-free
  [`covalence-metamath`](../covalence-metamath/SKELETONS.md) crate (the engine
  is pure `SExpr` manipulation, so `covalence-hol` depends on *it*). Its engine-
  and reader-side deferrals are tracked there; the consumer-side bridge work
  (the `#logic` / `Derivable_L` correspondence, the import tactic +
  representation-equivalence metatheorem) is tracked in the `metalogic` and
  `peano` registries below.
- **[`src/metalogic/SKELETONS.md`](./src/metalogic/SKELETONS.md)** — databases
  as first-class HOL data + the relation lattice (`docs/theories-models-and-logics.md`
  §5.6; the first cut of `metamath`'s deferred `Derivable_L` layer). Done:
  `Database := Φ → bool`, `Derivable_DB` on the impredicative engine, extension
  `⊑` + the proved monotonicity theorem with a concrete transport, and the
  interpretation relation `⟹_σ` + its proved transport theorem (for any
  `⟹`-homomorphic `σ`, demonstrated at the identity). Deferred: the
  `∃ValidProof ⟺ impredicative` grounding bridge, a non-trivial structural `σ`,
  and the north stars (conservative extension, `≅`, the category of databases,
  lifting `metamath::Database` / `peano::mm_pa`).

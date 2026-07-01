# Skeletons — `covalence-init/src/wasm`

The SpecTec → kernel front end (WASM-spec acceleration). Input is SpecTec AST
S-expressions (`covalence_spectec::parse`); no `.watsup` frontend. Design +
phasing: [`notes/wasm-spec.md`](../../../../notes/wasm-spec.md). Live coverage:
`spec::coverage_report` (bundled WASM 3.0 spec — leg A: 274 rules / 64-of-125
relations; leg B: 72-of-207 types rendered). See
[CLAUDE.md](../../../../CLAUDE.md) § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../SKELETONS.md).

## Severe / blocking

- **Recursive variant types → HOL datatypes.** `wasm::syntax` now renders
  aliases / primitives / tuples / iteration / **non-recursive variants + structs**
  (72-of-207 spec types) via the generic `crate::init::inductive::VariantBackend`
  (`CoprodBackend` = coproduct-of-payloads). Still deferred: **recursive** /
  mutually-recursive variants (`instr`, `valtype`↔…, caught by the cyclic-alias
  guard) — these need the recursion engine (`init/inductive` recursor) to synthesize
  a real fixpoint type + induction, and a backend for it behind `VariantBackend`.
  Plus parametric types (`vec(X)`) and `text`/`rat`/`real`.
- **Constructor freeness lemmas not threaded.** `denote` renders variant `case`
  constructor *terms* (via `DenoteCtx::from_spec` + `CoprodBackend::ctor`), but the
  coproduct injectivity/disjointness *lemmas* aren't surfaced yet — needed once
  relations reason about constructors (case analysis / no-confusion). Also
  `uncase`/`case`-elimination and record field projection aren't rendered.
- **`Dec` functions → real `define`s.** The 462 metafunctions have no recursive
  `define` + computation rules yet (`wasm/function.rs`). `denote` covers the value
  *expressions* they're built from, not the definitions.
- **Relations → HOL predicates over those types (leg B) not started.** Once
  `syntax` (variants) + `function` land, lift each `Rel` to a real HOL inductive
  predicate (the denotational mirror of `relation`'s `Derivable_R`).
- **Side-condition premises (`if`/`let`) skipped** — 221 rules of the spec. These
  need the denotational leg (a side condition is a decidable *function* predicate,
  `denote`-d to a `bool`, not an inductive premise). Biggest single coverage
  blocker.
- **Iterated premises (`…*`) skipped** — 63 rules. Need list recursion over
  premises (`init/list` recursion, cf. `grammar` word normalisation).

## Polish / increments

- **Coarse-tagged encoding positions.** `encode::shape` drops iteration binders
  (`xes`), `upd`/`ext` path index exps, non-expression `call` arguments, and `sub`
  types from the tag/children — collisions there lose faithfulness (never
  soundness). Tighten as needed.
- **No end-to-end `parse_defs` test.** Derivation tests build the `rel` AST
  directly; add one driving a real SpecTec S-expression through
  `covalence_spectec::parse::parse_defs → spec_rule_set → derive`.
- **`derive` addresses combined clauses by flat index.** For `spec_rule_set`, map
  `(relation, rule)` → clause index (a name/index table) so whole-spec derivations
  can address a specific rule.
- **Trace certification (WASM acceleration payoff) not started.** Run a WASM engine
  (`covalence-wasm`) as an untrusted oracle and certify each step against the
  reduction relation (`Step`/`Step_pure`/`Step_read`), à la Metamath proof replay
  (`notes/wasm-spec.md` phase 4).
- **Mirror-principle cross-check not started.** `SpecTec ⟶ our-prover` vs
  `SpecTec ⟶ HOL ⟶ HOL-in-our-prover` commutative-diagram confidence
  (`notes/wasm-spec.md` phase 5).

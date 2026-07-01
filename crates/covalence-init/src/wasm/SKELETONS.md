# Skeletons — `covalence-init/src/wasm`

The SpecTec → kernel front end (WASM-spec acceleration). Input is SpecTec AST
S-expressions (`covalence_spectec::parse`); no `.watsup` frontend. Design +
phasing: [`notes/wasm-spec.md`](../../../../notes/wasm-spec.md). See
[CLAUDE.md](../../../../CLAUDE.md) § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../SKELETONS.md).

## Severe / blocking

- **Syntax (`SpecTecDef::Typ`) not lowered.** No reified datatype for
  `valtype`/`instr`/`store`/… — encodings are untyped `nat` leaves. Needs the
  `crate::init` inductive engine wired in (a `wasm/syntax.rs`).
- **Functions (`SpecTecDef::Dec`) not lowered.** Metafunctions (`expand`,
  `default_`, …) have no `define` + computation rules yet (a `wasm/function.rs`).
- **Relation premises are inductive-only.** `relation::lower_rule` accepts only
  same-relation `SpecTecPrem::Rule` premises; `if`/`let` side conditions,
  cross-relation premises, and iterated (`…*`) premises are rejected — a rule
  using them contributes no clause. Side conditions need the function layer;
  cross-relation needs a multi-`d` rule set; iteration needs list recursion.

## Polish / increments

- **`encode::encode_exp` covers the structural core only.** Arithmetic
  (`Un`/`Idx`/`Slice`), records (`Str`/`Dot`/`Upd`/`Ext`), `Iter`/`Proj`/`Comp`/
  `Cat`/`Cvt`/`Sub`/`Len`/… return `unsupported`. Grow as relations need them.
- **No end-to-end `parse_defs` test.** The derivation tests build the `rel` AST
  directly; add one driving a real SpecTec S-expression through
  `covalence_spectec::parse::parse_defs → rule_set → derive`.
- **Trace certification (WASM acceleration payoff) not started.** The goal —
  run a WASM engine (`covalence-wasm`) as an untrusted oracle and certify each
  step against the reduction relation's `Derivable_R`, à la Metamath proof
  replay — is design-only (`notes/wasm-spec.md` phase 4).
- **Mirror-principle cross-check not started.** `SpecTec ⟶ our-prover` vs
  `SpecTec ⟶ HOL ⟶ HOL-in-our-prover` commutative-diagram confidence
  (`notes/wasm-spec.md` phase 5).

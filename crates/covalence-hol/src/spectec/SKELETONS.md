# Skeletons — `covalence-hol/src/spectec`

Open placeholders in the SpecTec-grammar → byte-predicate front end. The regex
engine it sits on is [`crate::regex`](../regex/SKELETONS.md). See
[CLAUDE.md](../../../../CLAUDE.md) § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../SKELETONS.md).

## Severe / blocking

- **The CFG stratum (headline next step).** Front end covers only the *regular*
  base case (`grammar::sym_to_core` bridges into `crate::regex`; `Var` non-terminal
  refs are rejected). We want our own primitive CFG one stratum up, like
  `init/regex`: a reified CFG datatype (impredicative-encoded), a `Derives`
  judgement with rule induction + soundness theorem, and `gram` lowering with `Var`
  → non-terminal. (`regex::tactic::prove_word`'s "variable parses as category"
  assumptions are the forward-compatible seed.)

## Polish / increments

- **Binary-grammar coverage.** Only single-symbol `grammar::compile_sym` is wired —
  no walk of a whole `gram` definition's productions. Full WASM binary format is
  gated on the CFG stratum above + richer upstream dumps (see `covalence-spectec`'s
  `SKELETONS.md`); the bundled WASM 3.0 AST exposes only a handful of `B*` grammars.

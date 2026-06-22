# Skeletons — `covalence-hol/src/spectec`

Intentional placeholders in the SpecTec-grammar → byte-predicate front end. The
regex engine it sits on (compiler + matcher) is the separate
[`crate::regex`](../regex/SKELETONS.md) module. See
[CLAUDE.md](../../../../CLAUDE.md) § Skeletons.

## Partial subsystems

- **The CFG stratum (the headline next step).** This front end covers only the
  **regular** base case: `grammar::sym_to_core` routes a SpecTec symbol through
  the byte bridge into [`crate::regex`], and `Var` (non-terminal reference) is
  rejected. We want our **own primitive notion of CFG**, one stratum up — exactly
  as `init/regex` is our own primitive notion of regular expression. That means:
  - a reified context-free grammar datatype (non-terminals + productions,
    impredicative-encoded like `init/regex`'s `regex` / `init/prop`'s `Prop`);
  - a `Derives` judgement closed under the productions, with rule induction over
    derivation trees;
  - a SpecTec `gram` definition lowering to those productions, with `Var`
    becoming a non-terminal symbol rather than a `BridgeError::GrammarRef`.

  `crate::regex::tactic::prove_word`'s "variable parses as category" assumptions
  are the forward-compatible seed (a variable token = a non-terminal expansion),
  but the reified CFG datatype, the `Derives` judgement, and its soundness
  theorem are all unbuilt.

- **Binary-grammar coverage.** Only `grammar::compile_sym` of a single symbol is
  wired; there is no walk of a whole `gram` definition's productions, and the
  bundled WASM 3.0 AST exposes only a handful of `B*` binary grammars (the bulk
  of the binary format is specified via decode `def`s, not `gram`s). Pulling the
  full WASM binary format in is gated on both the CFG stratum above and richer
  upstream dumps (see `covalence-spectec`'s `SKELETONS.md`).

# Skeletons — `covalence-init/src/grammar/spectec`

Open placeholders in the SpecTec-grammar → byte-predicate front end. The regex
engine it sits on is [`crate::grammar::regex`](../regex/SKELETONS.md). See
[CLAUDE.md](../../../../../../../CLAUDE.md) § Skeletons, the
[crate index](../../../SKELETONS.md), and the [root index](../../../../../../../SKELETONS.md).

The CFG stratum itself lives in [`crate::grammar::cfg`](../cfg/SKELETONS.md)
(binary engine [`crate::metalogic::binary`], `Derives_E` + family soundness,
parsing tactic); the SpecTec→`Cfg<u8>` lowering is `covalence_spectec::cfg`.
[`cfg::spec_grammar_env`](./cfg.rs) wires the two, and
[`tests/cfg_grammar.rs`](../../../tests/cfg_grammar.rs) proves the north star
(real WASM 3.0 bytes). Design:
[`notes/vibes/logics/cfg-stratum-design.md`](../../../../../../../notes/vibes/logics/cfg-stratum-design.md).

## Polish / increments

- **Whole-corpus binary coverage.** `spec_grammar_env` walks the dependency
  closure of named `B*` grammars, but the *under-approximating* lowering skips
  productions that carry premises (11 grammars incl. `Bmodule`/`Bname`/
  `Bheaptype`'s `Bs33` branch), parametric `Var{as1}` refs
  (`BuN`/`Blist`/`Bsection_` — needs monomorphisation, M6), and `ListN`
  length-prefixed vectors (context-sensitive). So `Bmodule`-scale parses need
  those layers; residuals tracked in [`../cfg/SKELETONS.md`](../cfg/SKELETONS.md).
- **WASM 1.0 / 2.0.** Only the 3.0 dump is bundled; validated 1.0/2.0 SpecTec AST
  dumps are producible (staged in `~/tmp/spectec-dumps`, not yet embedded — see
  the design note's version-lattice section) and unlock the
  `1.0 ⊆ 2.0 ⊆ 3.0` inclusion metatheorems via env transport.

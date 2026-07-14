# Skeletons — `covalence-init/src/grammar/spectec`

Open placeholders in the SpecTec-grammar → byte-predicate front end. The regex
engine it sits on is [`crate::grammar::regex`](../regex/SKELETONS.md). See
[CLAUDE.md](../../../../../../../CLAUDE.md) § Skeletons, the
[crate index](../../../SKELETONS.md), and the [root index](../../../../../../../SKELETONS.md).

The CFG stratum itself lives in [`crate::grammar::cfg`](../cfg/SKELETONS.md)
(binary engine [`crate::metalogic::binary`], `Derives_E` + family soundness,
parsing tactic); the SpecTec→`Cfg<u8>` lowering is `covalence_spectec::cfg`.
[`cfg::spec_grammar_env`](./cfg.rs) (under-approx) and
[`cfg::spec_grammar_env_recognition`](./cfg.rs) (recognition mode: LEB128 +
monomorphisation) wire the two;
[`tests/cfg_grammar.rs`](../../../tests/cfg_grammar.rs) proves the north star
(real WASM 3.0 bytes, incl. LEB128 `Bu32`/`Btypeidx` varints). Design:
[`notes/vibes/logics/cfg-stratum-design.md`](../../../../../../../notes/vibes/logics/cfg-stratum-design.md).

## Polish / increments

- **Grammar-valued parametric params.** Recognition mode monomorphises
  `Exp`/`Nat`-valued parametric refs (LEB128 `BuN`/`BsN`/`BiN`/`BfN`,
  `Bu32`/`Bu64`, all `*idx` now lower), but `Blist`/`Bsection_` take
  *grammar-valued* params (`BX`); `fold_args` returns `None` on a `Gram` arg so
  they still `ParametricRef`-skip. Substituting the arg grammar (plus their
  `ListN` + parameter-equality attrs) is the remaining coverage gap toward
  whole-section / `Bmodule` parses. Residuals in [`../cfg/SKELETONS.md`](../cfg/SKELETONS.md).
- **`Bname` UTF-8 premise + `Bmodule` coherence premises.** Under-approx mode
  skips these; recognition mode drops the value-range ones but `Bname`'s utf8
  and `Bmodule`'s structural premises are not yet modelled.
- **WASM 1.0 / 2.0.** Only the 3.0 dump is bundled; validated 1.0/2.0 SpecTec AST
  dumps are producible (staged in `~/tmp/spectec-dumps`, not yet embedded — see
  the design note's version-lattice section) and unlock the
  `1.0 ⊆ 2.0 ⊆ 3.0` inclusion metatheorems via env transport.

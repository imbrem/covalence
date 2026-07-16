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
monomorphisation) wire the two per-root; [`cfg::spec_grammar_env_all`](./cfg.rs)
loads the **whole 231-grammar spec** (`B*` + `T*`) in either mode, with
`derives_meaning` classifying the per-NT guarantee and `left_recursion_cycle`
surfacing the `T*` `Thexnum` cycle.
[`tests/cfg_grammar.rs`](../../../tests/cfg_grammar.rs) proves the north star
(real WASM 3.0 bytes: LEB128 `Bu32`/`Btypeidx` varints, and T5/T5b — a real
27-byte module recognized end-to-end as `⊢ Derives_E ⌜Bmodule⌝ w`). Design:
[`notes/vibes/logics/cfg-stratum-design.md`](../../../../../../../notes/vibes/logics/cfg-stratum-design.md).

## Polish / increments

- **Exact (Under-mode) `Bmodule`.** Whole-module parsing is RECOGNITION-only
  (read T5's doc for the pinned byte-sink over-approximations: dropped
  section-`len` premises, star-widened `ListN` vectors, custom-section
  `byte*`). Exact `Bmodule` needs value-coupled `ListN` (length-tied vectors)
  + faithful section-`len`/`Iter` premises — the value-parser story, beyond
  the CFG stratum.
- **`T*_` identifier-context params.** Recognition mode monomorphises integer
  *and grammar-valued* args (`Bsection_`/`Blist` `BX` — `Bmodule` + the 14
  `B*sec` chain lower), but the `T*_` context params (`I`, context-valued
  `Exp` args) never const-fold: 66 `T*` grammars stay dead (Recognition 204
  skipped prods; Under 236), so text-format parses stay blocked. Residuals in
  [`../cfg/SKELETONS.md`](../cfg/SKELETONS.md).
- **`rule`/`let` premises.** `classify_premises` drops `if`s and
  `iter`-wrapped `if`s over production-locals; `rule`/`let` shapes (4 prods,
  `T*`-side) still skip in recognition mode; under-approx also skips `Bname`'s
  utf8 and `Bmodule`'s structural premises.
- **2 bridge terminals.** Two `T*`-side terminal fragments fall outside the
  byte-regex subset (`SkipReason::Bridge`) in both modes.
- **Faithful `ListN`.** Under-approx skips parametric-length vectors;
  recognition widens them to a star. An exact length-coupled encoding belongs
  to the value-coupled/`Iter`-premise story, not the CFG stratum.
- **Whole-module tactic cost.** T5/T5b run on the 64 MiB
  `wasm::lower::total::with_total_stack` thread (kernel term walks recurse
  over ~800–1500-clause `Closed_E` conjunctions) and take tens of seconds per
  proof in debug builds; the per-NT production index in
  `grammar/cfg/tactic.rs` keeps the search polynomial. T5b (the whole-spec-env
  variant, ~90 s debug) is `#[ignore]`d as a perf lever — run
  `cargo test -p covalence-init --test cfg_grammar t5b -- --ignored`; T5 (the
  headline 27-byte `Bmodule` proof) stays in the default suite. Iterative
  kernel walks / clause-set addressing are the recorded escape hatches (same
  scale risk as the relation leg's total load).
- **WASM 1.0 / 2.0.** Only the 3.0 dump is bundled; validated 1.0/2.0 SpecTec AST
  dumps are producible (staged in `~/tmp/spectec-dumps`, not yet embedded — see
  the design note's version-lattice section) and unlock the
  `1.0 ⊆ 2.0 ⊆ 3.0` inclusion metatheorems via env transport.

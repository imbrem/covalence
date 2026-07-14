# Skeletons — `covalence-init/src/grammar/cfg`

The CFG stratum: a kernel-checked `Derives_E n w` judgement over context-free
grammars whose terminals are byte regexes (design:
[`notes/vibes/logics/cfg-stratum-design.md`](../../../../../../../notes/vibes/logics/cfg-stratum-design.md)).
Sits on [`crate::metalogic::binary`](../../metalogic/binary.rs) and the regex
stratum [`crate::grammar::regex`](../regex/SKELETONS.md). See
[CLAUDE.md](../../../../../../../CLAUDE.md) § Skeletons and the
[crate index](../../../SKELETONS.md).

## Severe / blocking

- **SpecTec wiring + north-star demo (M5).** `spec_grammar_env` bridging
  `wasm3_binary()` → `covalence_spectec::cfg::lower` → `GrammarEnv`, and the
  `tests/cfg_grammar.rs` real-bytes theorems (Bmagic/Bversion preamble, the
  Breftype→Bheaptype→Babsheaptype chain). `soundness::derives_in_family` is the
  T3 hook M5 calls.

## Minor / later

- **S2 comprehension family least-ness.** The full fixpoint characterisation
  `L_E := λn. {w | Derives_E n w}` is E-closed *and* least; `soundness.rs` has
  only the upper-bound half (S1). The dual (leastness → completeness) is unbuilt.
- **S3 at scale / per-env discharge cost.** `derives_in_family_regular` discharges
  `ClosedFam_E F_reg` per-env via regex `soundness_at`; it cannot reuse regex's
  polymorphic `Closed-D` cache across envs, and only covers a *single-production
  Var-free* env. Multi-production regular envs + a general S3 are unbuilt.
- **Env transport for version-inclusion metatheorems.** `⊢ Derives_E n w ⟹
  Derives_E' (ρ n) w` (ρ = tag remapping) for WASM 1.0 ⊆ 2.0 ⊆ 3.0 and subset
  grammars — `rule_induction2` at `pred := λn w. Derives_E' (ρ n) w` discharged
  per-matched-production (design note §"Version lattice"). Unbuilt.
- **Tactic recognizer acceleration (`tactic.rs`).** The phase-1 recognizer is a
  plain memoised top-down parser (`O(n³)`-ish span enumeration, terminal match
  delegated whole-slice to the regex tactic per span). No WASM/builtin
  accelerator seam yet; the `(NodeRef, lo, hi)` memo is the natural drop-in point.
- **Terminal sub-span plan reuse (`tactic.rs`).** Terminal segments are recognised
  twice: phase 1 calls `matches_core` for a yes/no verdict (result discarded),
  phase 2 calls it again to build the `Thm`. The regex tactic's `Plan`/word are
  not threaded through the CFG plan, so the winning regex derivation is rebuilt.
- **Word flattening.** Conclusion words are rule-shaped `cat`/`cons`/`nil`
  trees, not flattened cons-lists (inherited from the regex stratum). The tactic
  extracts terminal words from `Matches` conclusions (`matches_word`) rather than
  a shared word helper.
- **First-class grammar values.** `Derives` is per-env (grammar baked into the
  clause set); a reified `g : set (prod nat (list sym))` with one
  grammar-independent rule set + `monotone` (à la `metalogic::database`) is the
  recorded upgrade once a consumer needs it.

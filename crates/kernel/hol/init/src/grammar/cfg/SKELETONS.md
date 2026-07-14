# Skeletons — `covalence-init/src/grammar/cfg`

The CFG stratum: a kernel-checked `Derives_E n w` judgement over context-free
grammars whose terminals are byte regexes (design:
[`notes/vibes/logics/cfg-stratum-design.md`](../../../../../../../notes/vibes/logics/cfg-stratum-design.md)).
Sits on [`crate::metalogic::binary`](../../metalogic/binary.rs) and the regex
stratum [`crate::grammar::regex`](../regex/SKELETONS.md). See
[CLAUDE.md](../../../../../../../CLAUDE.md) § Skeletons and the
[crate index](../../../SKELETONS.md).

## Severe / blocking

- **Soundness (`soundness.rs`).** Stub only. Needs the discharge-free family
  least-fixpoint theorem `⊢ ∀F. ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹
  mem w (F n)` via `metalogic::binary::rule_induction2` (S1), the `ClosedFam`
  builder with the 2-outer-β normal form, the trivial-family witness (S0), and a
  toy regular-fragment agreement (S3).

## Minor / later

- **SpecTec wiring + north-star demo (M5).** `spec_grammar_env` bridging
  `wasm3_binary()` → `covalence_spectec::cfg::lower` → `GrammarEnv`, and the
  `tests/cfg_grammar.rs` real-bytes theorems (Bmagic/Bversion preamble, the
  Breftype→Bheaptype→Babsheaptype chain).
- **S2 comprehension family** (least-ness), **S3 at scale** (per-env
  discharge cost), and **env transport** (`Derives_E ⟹ Derives_E' ∘ ρ` for the
  WASM version-inclusion metatheorems) — see the design note.
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

# Skeletons — `covalence-init/src/grammar/cfg`

The CFG stratum: a kernel-checked `Derives_E n w` judgement over context-free
grammars whose terminals are byte regexes (design:
[`notes/vibes/logics/cfg-stratum-design.md`](../../../../../../../notes/vibes/logics/cfg-stratum-design.md)).
Sits on [`crate::metalogic::binary`](../../metalogic/binary.rs) and the regex
stratum [`crate::grammar::regex`](../regex/SKELETONS.md). See
[CLAUDE.md](../../../../../../../CLAUDE.md) § Skeletons and the
[crate index](../../../SKELETONS.md).

## Severe / blocking

- **The parsing tactic (`tactic.rs`).** Stub only. Needs the two-phase
  recognizer→plan→builder over concrete bytes (mirror `grammar/regex/tactic.rs`:
  memoised `(NodeRef, lo, hi)` search, left-recursion in-progress guard, then a
  builder discharging terminal segments via the regex tactic and non-terminal
  segments by recursion). Public target: `prove_derives(env, nt, bytes)
  -> Result<Option<Thm>>` yielding hypothesis-free `⊢ Derives_E ⌜nt⌝ w`.
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
- **Word normalisation.** Conclusion words are rule-shaped `cat`/`cons`/`nil`
  trees, not flattened cons-lists (inherited from the regex stratum).
- **First-class grammar values.** `Derives` is per-env (grammar baked into the
  clause set); a reified `g : set (prod nat (list sym))` with one
  grammar-independent rule set + `monotone` (à la `metalogic::database`) is the
  recorded upgrade once a consumer needs it.

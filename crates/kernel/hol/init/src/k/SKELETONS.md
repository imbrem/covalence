# Skeletons — `covalence-init::k`

The K-framework lowering + reducer. Design + fragment ladder:
`notes/design/k-frontend.md`. Layers: `session` (KSession, K-shaped) → `rewrite`
(K reducer) → `crate::metalogic::rewrite` (generic term-rewrite: congruence +
matcher + driver) → `crate::metalogic::binary` → HOL-omega. `reduce`/`relation`
are the earlier F0/F2 single-relation slices (kept; superseded for reduction by
`rewrite`/`session`, which add congruence + a matcher + a fuel driver).

**Reducing works end-to-end** (`.k` source → `⊢ Reduces program nf`): PEANO,
K tutorial Lesson 1.2, boolean simplification (`tests/k_demo.rs`, `cov k demo`).

## Severe

- **Conditional rules skipped (F1).** Rules with a `requires` are dropped
  (reported). Modelling boolean side conditions needs the hooked-`Bool` /
  hooked-`Int` theories (KORE `\dv`/`\equals` → kernel catalogue types with
  computation rules) — the biggest F1 unknown (hooked `MAP` after). Unlocks
  Lesson 1.7 and arithmetic-bearing languages.
- **No cells / `~>` KSequence / heating-cooling.** Only top-level + function-rule
  (anywhere) rewriting over constructor terms. K's `<k>`/`<state>` cell
  configurations, the `~>` computation sequence, and `strict`/`seqstrict`
  heating/cooling are unmodelled — needed for Lesson 1.13/1.14 and IMP.
- **No substitution / binders.** LAMBDA's β (`E[V/X]`) needs a capture-avoiding
  substitution metafunction and a binder discipline — unbuilt.

## Minor

- **First-order matching only; leftmost-innermost, deterministic.** The
  `Innermost` matcher assumes a confluent, deterministic system (unique redex);
  non-confluent K (`--search`) needs a branching driver. No non-linear-pattern
  or AC matching.
- **Priority / `owise` unmodelled.** Rule order is taken as-is (the
  priority-as-rule-choice convention + its disjointness assumption is not
  represented). Fine while rules don't overlap.
- **Encoding covers only the configuration fragment.** `encode_pattern` handles
  evar / app / dv / string; set variables and the logical connectives are
  rejected; sorts are dropped (only symbol identity matters).
- **No cross-relation / K-`claim` consumption.** `claim` reachability sentences
  (F3) are unconsumed.
- **No `/k` REPL / web route.** `cov k` (CLI) exists; the `repl-core`
  `Semantics`/`Strategy` instantiation and a `/k` web route are not built.

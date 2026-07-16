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

- **No builtin hooks (F1).** `requires` conditions over the language's *own*
  boolean constructors work (`metalogic::rewrite` stratified guards → Lesson 1.7
  mechanism, `examples/k-demo/peano-max.k`), but genuine builtin hooks —
  `+Int`/`<=Int`/`andBool`/`notBool`, `\dv`/`\equals` → kernel catalogue types
  with computation rules — are unbuilt. This is what the tutorial's actual
  `requires I >=Int 90` and all arithmetic need. (`MAP`/collection hooks after.)
- **Guarded rewriting is stratified (sound, incomplete).** A `requires` condition
  is evaluated in the *unconditional* sub-relation only (to break the
  `Step`↔`Reduces` cycle); a guard that holds only by using another guarded rule
  cannot be proven, so that rule silently doesn't fire. Faithful for tutorial
  guards (pure computations); a fully-general condition semantics would need a
  mutually-recursive `Step`/`Reduces` construction.
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

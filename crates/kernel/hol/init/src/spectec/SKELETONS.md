# Skeletons — `covalence-init/src/spectec`

The high-level, trait-based SpecTec-fragment API (`Fragment` + `RelationEnv`,
peer of `crate::grammar::cfg::GrammarEnv`). See
[CLAUDE.md](../../../../../../CLAUDE.md) § Skeletons and the
[crate index](../../SKELETONS.md).

## Minor / later

- **Only `Rel` + `Gram` fragment kinds.** `RelationEnv` (relations) and
  `GrammarEnv` (grammars) implement `Fragment`. The other SpecTec kinds — `Typ`
  (reified datatype, `wasm::syntax`) and `Dec` (recursive function) — have no
  `Fragment` impl yet; they need `syntax`/`denote` wrapped the same way.
- **Relation coverage = engine coverage.** `RelationEnv::spec` lowers only rules
  with inductive premises (the `if`/`let` side-condition and iterated `…*`
  premises are still skipped by `wasm::relation::lower_rule` — 221 + 63 rules).
  So the single-step `Step`/reduction relation doesn't fully lower; only its
  reflexive closure `Steps/refl` and the premise-free typing rules do. Real
  reduction traces need those premise forms (side conditions → the denotational
  `wasm::denote` leg; iteration → list recursion).
- **No `state` in the `Fragment` trait.** Judgement *statement* differs per kind
  (relation: `(rel, expr)`; grammar: `(nt, word)`), so it stays an inherent
  method (`RelationEnv::derivable`, `GrammarEnv::derivable`). Unify later if a
  consumer needs to state judgements generically.
- **Low-level convergence (deferred).** `wasm::relation::derive` hand-rolls the
  `derive_via_closed` construction; re-pointing it at `metalogic::apply::apply_rule`
  would share one forward constructor with grammars. Invisible to `Fragment`
  callers — a demonstration of the layering, when done.

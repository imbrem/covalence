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
- **Side conditions: engine discharges `Side` premises; `lower_rule` wiring is
  the missing piece.** The unary engine now takes mixed premises
  (`metalogic::derive_mixed` / `RelationEnv::derive_mixed`; `Fragment` routes
  `Side`), and `side_cond::prove_side_condition` soundly discharges
  value-fragment `if` conditions (it *gates*, never fabricates) — but
  `lower_rule` still SKIPS `if`/`let`/iterated premises, so no whole conditional
  rule lowers yet. Wiring needs: `lower_rule` emitting the condition as a clause
  antecedent (mangled metavars vs real-nat instantiation), plus `let` bindings +
  iteration (every value-fragment rule also carries an `Iter`/`Let`); branch
  rules (`Proj(Uncase c)≠0`) need the datatype leg. Design + analysis:
  `notes/vibes/logics/spectec-fragment-api.md`.
- **No `state` in the `Fragment` trait.** Judgement *statement* differs per kind
  (relation: `(rel, expr)`; grammar: `(nt, word)`), so it stays an inherent
  method (`RelationEnv::derivable`, `GrammarEnv::derivable`). Unify later if a
  consumer needs to state judgements generically.

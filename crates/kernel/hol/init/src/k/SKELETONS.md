# Skeletons — `covalence-init::k`

The K-framework lowering: KORE rewrite rules → `Derivable_KStep` reduction
relations. Design + fragment ladder: `notes/design/k-frontend.md`. This module
is **F0** (unconditional single steps); the rungs below are open.

## Severe

- **No multi-step / reflexive-transitive closure.** `reduce::step` mints one
  `⊢ Derivable_KStep ⌜Step(a,b)⌝`; `A →* B` (with `B` open) needs a `Step*`
  relation over the single-step one — the F2 rung, shared with the SpecTec
  reduction work. Chaining is currently manual (caller threads `to`→`from`).
- **No automatic matching.** `reduce::step` takes the element-variable
  witnesses explicitly; the untrusted redex matcher (find the rule + substitution
  that fires at a concrete configuration) is not built — the "construct" driver
  that would make this a real reducer.
- **Conditional rules skipped (F1).** Rules with a `requires` are dropped by
  `rule_set` (reported). Modelling boolean side conditions needs the hooked-`Bool`
  / hooked-`Int` theories (KORE `\dv`/`\equals` → kernel catalogue types with
  computation rules) — the biggest F1 unknown (hooked `MAP` after).

## Minor

- **Priority / `owise` unmodelled.** Rule order is taken as-is; the
  priority-as-rule-choice convention (and its disjointness assumption) is not
  represented. Fine while rules don't overlap.
- **Encoding covers only the configuration fragment.** `encode_pattern` handles
  evar / app / dv / string; set variables, `\and`-constrained cells, and the
  logical connectives are rejected. Cells encode as plain symbol applications
  (no structured cell theory); sorts are dropped.
- **No cross-relation / K-`claim` consumption.** Only the `Step` relation is
  lowered; `claim` reachability sentences (F3) are unconsumed.
- **No `/k` REPL wiring.** The `repl-core` `Semantics`/`Strategy` stack (used by
  `/lisp`) is not yet instantiated for K, and there is no web route.

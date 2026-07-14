# Skeletons — `covalence-init::k`

The K-framework lowering: KORE rewrite rules → K reduction relations. Design +
fragment ladder: `notes/design/k-frontend.md`. `reduce` = F0 single steps (unary
engine); `relation` = **F2** `KStep`/`KReduces = KStep*` on the binary engine.

## Severe

- **No automatic matching / no reduction driver.** `relation::prove_step` and
  `reduce::step` take the element-variable witnesses explicitly; the untrusted
  redex matcher (find the rule + substitution that fires at a concrete
  configuration, and drive leftmost-innermost to a normal form building the
  `KReduces` chain) is not built — the "construct" driver that makes this a real
  reducer. Cf. the Lisp `relation::prove_reduces` fuel-bounded driver.
- **No congruence clauses.** `KStep` has only redex (root-rewrite) clauses; there
  are no `∀a a'. KStep a a' ⟹ KStep (C[a]) (C[a'])` context clauses, so a redex
  buried inside a configuration can't step without the matcher rewriting the
  whole term. K's rewriting is inside-out over the cell structure — needs a
  congruence/context story (cf. Lisp's per-elimination-context clauses).
- **Conditional rules skipped (F1).** Rules with a `requires` are dropped
  (reported). Modelling boolean side conditions needs the hooked-`Bool` /
  hooked-`Int` theories (KORE `\dv`/`\equals` → kernel catalogue types with
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

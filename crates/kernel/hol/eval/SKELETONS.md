# Skeletons — covalence-hol-eval

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Minor

- **`prove_true` is single-step only.** It reduces one redex and bridges `= T`;
  the recursive normalise-then-decide workhorse stays `TermExt::prove_true` in
  `covalence-init` until the S6 re-route lands the weak βι folder here.
- **Consumers not yet re-routed.** `TermExt::reduce*`/script `reduce-prim` still
  call the legacy `Thm::reduce_prim`; re-routing them here (and then deleting
  `ReducePrim` + `builtins.rs`) is purge S6–S8. The differential suite
  (`tests/differential.rs`) dies with `reduce_prim`.

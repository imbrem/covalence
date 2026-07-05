# Skeletons — covalence-hol-eval

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Minor

- **`prove_true` is single-step only.** It reduces one redex and bridges `= T`;
  the recursive normalise-then-decide workhorse remains `TermExt::prove_true` in
  `covalence-init` (whose ι steps route here since the S6 re-route).

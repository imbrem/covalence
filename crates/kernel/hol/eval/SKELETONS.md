# Skeletons — covalence-hol-eval

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Minor

- **`prove_true` is single-step only.** It reduces one redex and bridges `= T`;
  the recursive normalise-then-decide workhorse remains `TermExt::prove_true` in
  `covalence-init` (whose ι steps route here since the S6 re-route).
- **Legacy `ReducePrim` still alive in the kernel.** All prod callers now route
  here, but `Thm::reduce_prim` + `builtins.rs` still exist in `covalence-core`;
  deleting them is purge S8. The differential suite (`tests/differential.rs`)
  dies with them.

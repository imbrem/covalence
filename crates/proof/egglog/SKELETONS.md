# covalence-egglog — Skeletons

See [`CLAUDE.md`](../../../CLAUDE.md) § Skeletons and the [root index](../../../SKELETONS.md).

- **`EgglogBridge` is Stage 0 — only `fiat` succeeds.** The `rule`/`merge_fn`/
  `trans`/`sym`/`congr` justification-replay handlers default to
  `BridgeError::NotImplemented` (`src/bridge.rs`), and no concrete kernel-backed
  `impl EgglogBridge` exists in the workspace.
- **egglog `external` bridge disabled.** The real-solver bridge (`src/external.rs`:
  run `(prove …)`, convert egglog's proof DAG into our `proof` types) is switched
  off: the `egglog` dep, the `external-egglog` feature, the `pub mod external`
  line, and the root `[patch.crates-io]` egglog pin are all commented out.
  Released egglog still doesn't expose the `proof` module the bridge needs (only
  an upstream git rev does), and that git dependency breaks sandboxed
  environments (Claude Web). Re-enable all four once a crates.io egglog ships the
  proof API — `external.rs` may need porting to the new term-encoding proof model.

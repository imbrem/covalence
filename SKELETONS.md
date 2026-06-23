# Skeletons — index

The skeleton registry (every intentional placeholder: empty/stub modules,
removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and commented-out / `#[ignore]`d / deleted tests) is
**split per crate**, co-located with the code. See [`CLAUDE.md`](./CLAUDE.md)
§ Skeletons for the policy.

## Per-crate registries

- **[`covalence-pure`](crates/covalence-pure/SKELETONS.md)** — empty base-logic scaffold.
- **[`covalence-core`](crates/covalence-core/SKELETONS.md)** — declaration-only catalogue ops.
- **[`covalence-hol`](crates/covalence-hol/SKELETONS.md)** — split per module (project loader, theory catalogue, `.cov` script layer, models, regex/spectec grammars, metalogic, peano, ring).
- **[`covalence-kernel`](crates/covalence-kernel/SKELETONS.md)** — empty `facts` observer module; removed legacy prover.
- **[`covalence-spectec`](crates/covalence-spectec/SKELETONS.md)** — removed native `.watsup` frontend; single-version WASM grammar; regular-only byte-grammar bridge.
- **[`covalence-alethe`](crates/covalence-alethe/SKELETONS.md)** — Alethe rule coverage.
- **[`covalence-metamath`](crates/covalence-metamath/SKELETONS.md)** — substitution engine + `.mm` reader: compressed proofs, `set.mm` scale, file inclusion, `Database` trait + backends, structured-tree encoding.

A crate with no skeletons has no file. When you add the first skeleton to a
crate (or module) without one, create its `SKELETONS.md` and link it from its
crate index (or here).

## Registry maintenance

**Not yet a complete repo audit.** Entries were recorded as code was written, not
reconciled against a full sweep. Treat a missing entry as "not yet recorded," not
"no skeleton there."

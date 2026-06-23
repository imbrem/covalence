# Skeletons — index

The skeleton registry (every intentional placeholder: empty/stub modules,
removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and commented-out / `#[ignore]`d / deleted tests) is
**split per crate**, co-located with the code. See [`CLAUDE.md`](./CLAUDE.md)
§ Skeletons for the policy: **add a skeleton to the file nearest the code** (the
module's file if one exists, else the crate's); delete the entry when you fill
it in.

## Per-crate registries

- **[`covalence-pure`](crates/covalence-pure/SKELETONS.md)** — empty scaffold
  crate (the base-logic TCB floor; defines no logic yet).
- **[`covalence-core`](crates/covalence-core/SKELETONS.md)** — declaration-only
  catalogue ops (no definitional body yet).
- **[`covalence-hol`](crates/covalence-hol/SKELETONS.md)** — split per module:
  - **[`src/init`](crates/covalence-hol/src/init/SKELETONS.md)** — the theory
    catalogue (rat/real/list/prod/monoid/lang/text/prop, the inductive engine).
  - **[`src/script`](crates/covalence-hol/src/script/SKELETONS.md)** — the
    `.cov` proof-language layer.
  - **[`src/surface`](crates/covalence-hol/src/surface/SKELETONS.md)** — the
    surface-syntax sketch.
- **[`covalence-kernel`](crates/covalence-kernel/SKELETONS.md)** — the empty
  `facts` observer module; the removed legacy prover.
- **[`covalence-spectec`](crates/covalence-spectec/SKELETONS.md)** — removed
  native `.watsup` frontend; WASM grammar versions (only 3.0 bundled) and the
  regular-fragment-only byte-grammar bridge.
- **[`covalence-alethe`](crates/covalence-alethe/SKELETONS.md)** — Alethe rule
  coverage.
- **[`covalence-metamath`](crates/covalence-metamath/SKELETONS.md)** — the
  Metamath substitution engine + `.mm` reader (the lower, HOL-free crate):
  compressed proofs, `set.mm` scale, file inclusion, the `Database` trait +
  pluggable backends, the structured-tree encoding. (The HOL-consuming bridge —
  import tactic + representation-equivalence metatheorem — is tracked in
  `covalence-hol`'s `metalogic`/`peano` registries.)

A crate with no skeletons has no file. When you add the first skeleton to a
crate (or module) without one, create its `SKELETONS.md` and link it here (or
from its crate index).

## Registry maintenance

- **This registry is not yet a complete repo audit.** It records the skeletons
  surfaced as code was written; it has not been reconciled against a full sweep
  of every empty/stub module, `todo!()` / `unimplemented!()` / `NotImplemented`
  stub, and disabled/deleted test across all crates. Treat a missing entry as
  "not yet recorded," not "no skeleton there."

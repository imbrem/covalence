# Skeletons — index

The skeleton registry (every intentional placeholder: empty/stub modules,
removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and commented-out / `#[ignore]`d / deleted tests) is
**split per crate**, co-located with the code. See [`CLAUDE.md`](./CLAUDE.md)
§ Skeletons for the policy: **add a skeleton to the file nearest the code** (the
module's file if one exists, else the crate's); delete the entry when you fill
it in.

## Per-crate registries

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
- **[`covalence-spectec`](crates/covalence-spectec/SKELETONS.md)** — the
  SpecTec → HOL lowering driver (covered fragment vs deferred).
- **[`covalence-alethe`](crates/covalence-alethe/SKELETONS.md)** — Alethe rule
  coverage.
- **[`covalence-metamath`](crates/covalence-metamath/SKELETONS.md)** —
  compressed proofs, `set.mm` scale, file inclusion, the `covalence-hol` import
  tactic + representation-equivalence metatheorem.

A crate with no skeletons has no file. When you add the first skeleton to a
crate (or module) without one, create its `SKELETONS.md` and link it here (or
from its crate index).

- **`covalence-hol` ring rewriter** in
  `crates/covalence-hol/src/ring/normalize.rs` (`RingNormalizer` / `RingOps`).
  **In place:** a general `(+, ·, 0, 1)` normalizer to a canonical
  **sum-of-monomials** form, built on the AC tactic (`crate::ac`). Decides
  distributivity (left + the *derived* right), `+`/`·` associativity +
  commutativity, and the `0`/`1` identities — so two expressions equal as
  *formal* polynomials over their atoms get `⊢ e₁ = e₂` (tested over `nat` and
  `int`). Every step is a kernel-checked equality. **Deferred:**
  - **coefficient collection** — like monomials are *not* combined: `x + x`
    stays `x + x` (not folded to `2·x`), and `x·y + y·x` stays two summands
    (not `2·(x·y)`). Needs literal-coefficient arithmetic on monomials and a
    "merge equal monomials" pass over the sorted sum.
  - **negation / subtraction** — `neg` / `sub` are treated as opaque atoms,
    not expanded through the `Ring` (`add_neg` / `sub_def`) axioms; an
    expression mentioning them normalizes only down to its `+`/`·` structure.
  - **literal folding inside monomials** (e.g. `2·3·x → 6·x`).
  The rewriter is currently a HOL-`Term`/`Thm` instance (`RingOps` over a
  catalogue carrier); a fully `Semiring`/`Ring`-trait-generic version (so it
  runs against any model, not just the shallow HOL one) is a later step.

## Registry maintenance

- **This registry is not yet a complete repo audit.** It records the skeletons
  surfaced as code was written; it has not been reconciled against a full sweep
  of every empty/stub module, `todo!()` / `unimplemented!()` / `NotImplemented`
  stub, and disabled/deleted test across all crates. Treat a missing entry as
  "not yet recorded," not "no skeleton there."

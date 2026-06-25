# Splitting `covalence-hol` → thin `covalence-hol` + `covalence-init`

> **STATUS: DONE (initial split landed).** The bulk moved to `covalence-init`;
> the thin `covalence-hol` is the 3-module HOL surface (`types`/`traits`/
> `hol_light_obs`) depending only on `covalence-core`. Remaining follow-ups:
> merge `covalence-opentheory` behind an `opentheory` feature; decouple
> `covalence-hol` from `covalence-core` (the core-free peer-of-metamath goal).
> Note: the algebra cluster (`category`/`monoidal`/`semiring`/`ring`) turned out
> **live** (used by `init/cat`, `init/coprod`, `init/nat`, `ac`) — kept, not
> pruned. `PureHol` was already dead and is removed.

## Goal

Today's `covalence-hol` is one ~60k-line megacrate. Factor it in two:

- **`covalence-hol` (repurposed → thin)** — just the HOL builder/trait surface
  that proof *consumers* need (the surface the old OpenTheory importer uses).
  Eventually the metamath-style HOL substrate; **merge `covalence-opentheory`
  into it behind an `opentheory` feature**.
- **`covalence-init`** — everything else: the semi-trusted catalogue, proof
  machinery, and the `.cov` surface. This is what `covalence-hol` mostly *is*
  today.

The split is deliberately simple first (move modules, keep it green); the deeper
goals (decoupling `covalence-hol` from `covalence-core`, the `init` subcrate
family) come after.

## New `covalence-hol` (thin) — contents

The OpenTheory importer (`covalence-opentheory`) uses exactly:
`covalence_hol::{traits::HolLightKernel, HolLightTerms, types::{NameId, HolError, …}, HolLightCtx, PureHol}`.

So the thin crate is **3 modules** (~530 lines), already nearly self-contained:

| Module | Lines | Deps |
|---|---|---|
| `types.rs` | ~76 | none (the `NameId`/`HolError`/ID constants) |
| `traits.rs` | ~248 | `crate::types` only — the `HolLightKernel`/`HolLightTerms`/`HolLightTypes` traits |
| `hol_light_obs.rs` | ~205 | `covalence_core::{Term,TermKind,Type,defs}` — `HolLightCtx` |

Plus the crate-root re-exports of `covalence_core::{Term,Thm,Type,…}` so consumers
reach the kernel through `covalence-hol`.

**Dependency reality:** this thin crate still depends on `covalence-core` (the
builder traits construct `covalence_core::Term`/`Thm`). The longer-term
"`covalence-hol` is a core-free HOL-syntax/proof peer of `covalence-metamath`"
(refactor-plan §4) is a *later* decoupling, not this move. Flag it; don't block on it.

**`opentheory` feature (next):** move `covalence-opentheory`'s modules in under
`#[cfg(feature = "opentheory")]`, with its `ureq` network dep gated too. Delete
the `covalence-opentheory` crate once consumers (`cov hol`) point at the feature.

## `covalence-init` — contents

Everything else moves here (`git mv` to preserve history). Depends on the thin
`covalence-hol` + `covalence-metamath` + `covalence-core`, and **re-exports the
`covalence-hol` surface** so downstream keeps compiling through one import.

| Module(s) | Keep? |
|---|---|
| `init/` (the catalogue, ~36k), `script/`, `project.rs`, `metalogic/`, `peano/`, `models/` | **Keep** — the live semi-trusted API + `.cov` layer. |
| `proofs/`, `ac.rs`, `sexp.rs`, `hash.rs`, `debug.rs` | **Keep** as machinery (`hash.rs` later → `covalence-cons`; `sexp.rs` is the syntax). |
| `regex/`, `spectec/` | **Keep** — the verified-WASM / grammar seeds (`covalence-eval` later). |
| `category/`, `monoidal/`, `semiring/`, `ring/` | **Cruft review** (below). |

## Cruft to remove during the split

Evidence-backed; each removal its own commit, recoverable from git.

1. **`PureHol` is dead code.** Every use is gated off — the OpenTheory
   integration test (`interp.rs` `#[cfg]`-disabled) and `cov hol check`
   ("temporarily disabled while the PureHol kernel …"). Decide: revive it on the
   thin `covalence-hol`, or **delete it now** and keep one skeleton ("reinstate a
   HOL-kernel binding"). Recommend delete + skeleton — it's blocking nothing.
2. **Algebra/category cluster** (`category` 690, `monoidal` 441, `semiring` 520,
   `ring` 658). **Zero external-crate users**; they only reference each other
   inside `covalence-hol`. Assess whether this is live theory work or a stalled
   experiment. `ring`'s normalizer is tested (nat/int) — keep it; `category`/
   `monoidal`/`semiring` look like an unfinished categorical-algebra layer →
   strong prune candidates (move to `covalence-init` only if `init`/tests use
   them; otherwise drop with a one-line note in the refactor plan).
3. **`debug.rs`** (41 lines) — confirm it's still wired; drop if it's a scratch
   helper.
4. Re-check `#[ignore]`d / `#[cfg(false)]` tests surfaced while moving (e.g. the
   OpenTheory `PureHol` tests) — delete rather than carry dead tests.

## Mechanics

1. `git mv crates/covalence-hol crates/covalence-init`, then re-create a fresh
   `crates/covalence-hol` with just `types.rs`/`traits.rs`/`hol_light_obs.rs` +
   the kernel re-exports (move those three back out of init).
2. `covalence-init/Cargo.toml`: depend on `covalence-hol`, `covalence-metamath`,
   `covalence-core`; `pub use covalence_hol::*` (or a `pub use` of the specific
   surface) so `crate::traits`/`crate::types`/`HolLightCtx` keep resolving inside
   the moved modules — minimize import churn.
3. Repoint internal `crate::{traits,types,hol_light_obs}` references in the moved
   modules to the re-export (or `covalence_hol::…`).
4. **Downstream** (`repl`, `serve`, `alethe`, `cov`, `python`, `shell`): they
   import `covalence_hol::…` today. Point the catalogue/script users at
   `covalence-init`; leave the builder-API users on `covalence-hol`. A blanket
   `covalence-init` re-export keeps the diff small; tighten later.
5. Update workspace `members`, the root `SKELETONS.md` index, `crate-map` skill,
   and `notes/crate-graph.md`.
6. Verify with `bun test` (Rust + Python) before merge. Watch for the re-entrant
   `LazyLock` class of failure when `init`/`defs`/env move — it only shows at
   runtime, so this MUST be cargo-test-gated, never merged build-only.

## Sequence (small commits)

1. Cruft pass on `covalence-hol` (delete `PureHol`, prune the algebra/category
   experiment if dead, drop dead tests) — *before* moving, so less moves.
2. Create `covalence-init`, move the bulk, wire deps + re-exports, fix imports.
3. Carve the thin `covalence-hol` (3 modules) back out.
4. Repoint downstream crates; `bun test`.
5. (Next branch) merge `covalence-opentheory` in behind the `opentheory` feature.

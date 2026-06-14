# Skeletons

Authoritative registry of intentional placeholders in the repo: empty/stub
modules, removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and tests that are commented out, `#[ignore]`d, or
deleted "for later".

See `CLAUDE.md` § Skeletons for the rules: **add an entry whenever you leave a
skeleton; delete the entry when you fill one in.** Keep this list complete —
it is how unfinished work stays discoverable.

## Empty / stub modules

- **`crates/covalence-kernel/src/facts.rs`** — empty module. The *observer*
  layer that records and content-addresses proven `covalence-hol` theorems
  will land here as the HOL-on-store stack comes online. See the
  `covalence-kernel` crate-root docs and `docs/roadmap.md`.

## Postulates pending proof

- **The six structural Peano axioms** in `crates/covalence-hol/src/init/nat.rs`
  (`Hol::{zero_ne_succ, succ_inj, add_base, add_step, mul_base, mul_step}`) are
  **postulated** via `Thm::assume`, not proved. The kernel reduces `succ` /
  `natRec` only on closed literals and exposes neither `natRec`'s computation
  equations nor `nat`'s freeness (`S` injective, `0 ≠ S n`) over variables, so
  these are not yet derivable HOL theorems. Only induction (`Peano::induct` →
  `Thm::nat_induct`) is genuine.

  Discharging them — the *soundness of PA in HOL* step — needs new
  `covalence-core` kernel primitives: the `natRec` base/step equations and
  `nat` freeness. When those land, replace the `Hol::axiom` calls with real
  derivations; the `Peano` trait/API does not change.

## Registry maintenance

- **`SKELETONS.md` itself is incomplete.** This file was created to fix the
  missing `facts` module and currently records only the `covalence-kernel`
  skeletons surfaced there. It still needs a full repo audit — empty/stub
  modules, `todo!()` / `unimplemented!()` / `NotImplemented` stubs, and
  disabled / deleted tests across all crates — to become the authoritative
  registry `CLAUDE.md` describes.

## Removed-pending-rewrite subsystems

- **`covalence-kernel` legacy prover** — the arena + e-graph + union-find
  prover kernel that used to live in `covalence-kernel` was removed in the
  kernel rewrite. What remains is the content-addressed store wiring
  (`backend.rs`, `store.rs`) plus the empty `facts` module above. Recover the
  old prover from the `backup/pre-hol-cleanup` branch if needed.

# Skeletons — covalence-hol-eval

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Declaration-only catalogue ops (no definitional body yet)

These `defs/` term-specs carry `tm = None`: sound/complete on literals (via
the family certificate rules) but no open-form body, so nothing is provable by
`unfold_term_spec`. Each should become a `let_term!` def; on adding a body,
delete here and — if reducible — add to
`tests/audit_reduce.rs::audit_reduce_matches_body`. (Moved here from
`covalence-core` with the catalogue, stage E2.)

- **`sN.shr` (arithmetic right shift), `defs/int_ops.rs`** — needs floor-division
  (round toward −∞), not yet exposed (`int.div` truncates toward zero).
- **`nat` ops, `defs/nat.rs`** — `natBitAnd/Or/Xor`, `natToBytesLe/Be`,
  `natFromBytesLe/Be` are declaration-only (`term_decl!`).
- **`bytes` ops, `defs/blob.rs`** — `bytesConsNat`, `bytesAt` declaration-only
  (need a `nat ↔ u8` conversion).

(Fixed-width conversions `toNat`/`toInt`/`fromNat`/`fromInt`/`zext`/`sext` in
`int_ops.rs` are *intentionally* declaration-only — the primitive reducible
interface, not a stub.)

## defs/core.cov source-of-truth flip (deferred, blocked on re-entrancy)

`core.cov` + the `defs::cov` parser mirror part of the catalogue as data, proven
byte-identical to the hand-written `defs::*` (`cov::tests`), but the accessors
still source from Rust. Flipping `defs::*` to source from `core_env()` is
DEFERRED: a prior attempt deadlocked (a `LazyLock` re-entered the same accessor
during its own init; reverted in `fed9819`). To redo: `parse_core` must resolve
references from the partial env under construction (or a build-local Rust
resolver), never the `core_env`-backed accessors — and must be **test-gated**.
Porting the numeric tower to data is the remaining follow-up.

## Minor

- **`prove_true` is single-step only.** It reduces one redex and bridges `= T`;
  the recursive normalise-then-decide workhorse remains `TermExt::prove_true` in
  `covalence-init` (whose ι steps route here since the S6 re-route).

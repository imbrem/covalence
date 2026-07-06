# Skeletons — covalence-hol-eval

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Pure-HOL unit tests: coverage gaps (stage E3, D5)

`tests/pure_hol_units.rs` checks definition-vs-native per cert family; open
gaps (full scoping in that file's module docs):

- **nat/int definitional derivations are `EvalThm`-typed** — the chains use
  HOL rules only, but `covalence-init` pins `EvalThm`; tier-generic init
  derivations (`Thm<L: HolTier>`) would land them at `Thm<CoreLang>` verbatim.
  Until then the pure tier holds only the δ/β spines (it cannot state literal
  equations at all — the D3 denotation axioms are eval-tier by design).
- **bytes definitional evaluation missing** — blocked on the `Blob` ↔ `list u8`
  bridge + list recursion (covalence-init `init/SKELETONS.md`); the test pins
  only the spine + the cert value.
- **fixed-width definitional evaluation stops at `toNat`/`fromNat`**
  (intentionally declaration-only); the body-forced differential is
  `tests/audit_reduce.rs::audit_reduce_matches_body`.

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
`int_ops.rs` and the F2b bit-level float ops in `defs/floats.rs` are
*intentionally* declaration-only — the primitive reducible interface, not a
stub.)

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

## Minor

- **Connective-rule perf (logic-out).** and/or/imp/not/all/lem are now multi-step
  `CoreLang` derivations (`derived.rs`), not kernel rules — ~1.5–1.7x on the
  hot proving suites (real/int/utf16). Acceptable for now; if it bites, re-admit
  the hottest as `CoreEval` accelerator rules with the derivation as the standing
  soundness witness (same pattern as the arithmetic certs). See
  `notes/vibes/handoff/tohol-purge.md`.

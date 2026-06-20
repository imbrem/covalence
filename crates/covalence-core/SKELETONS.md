# Skeletons — covalence-core

## Declaration-only catalogue ops (no definitional body yet)

These `covalence-core` `defs/` term-specs carry `tm = None`: they are **sound
and complete on literals** (reduced by `builtins.rs`) but have no open-form
definitional body, so nothing about them is provable by `unfold_term_spec`.
Each should become a `let_term!` / `spec_term!` definition (see
`docs/roadmap.md`). When you add a body, delete it here AND — if the body is
reducible — add it to the `audit_reduce.rs::audit_reduce_matches_body`
coupling guard.

- **`sN.shr` (arithmetic right shift), `crates/covalence-core/src/defs/int_ops.rs`**
  — `op_body` returns `None` for the *signed* `Shr`. Needs a floor-division
  (round toward −∞), which `int` does not yet expose (`int.div` truncates
  toward zero). The *unsigned* `uN.shr` and every other `uN`/`sN` op
  (add/sub/mul/neg/and/or/xor/not/lt/le/gt/ge/shl/div/rem) are now defined.
- **`nat` ops, `crates/covalence-core/src/defs/nat.rs`** — `natBitAnd/Or/Xor`,
  `natToBytesLe/Be`, `natFromBytesLe/Be` are `term_decl!`
  (declaration-only). (`natDiv` now carries a def-style Euclidean selector
  predicate; it is not let-style, so its `builtins` reduction is checked
  against the predicate by `nat_div_mod_satisfy_euclidean_law` rather than
  the unfold-based `audit_reduce_matches_body` coupling guard.)
- **`bytes` ops, `crates/covalence-core/src/defs/blob.rs`** — `bytesConsNat`,
  `bytesAt` are declaration-only (need a `nat ↔ u8` conversion).
- **Fixed-width conversions** (`toNat`/`toInt`/`fromNat`/`fromInt`/`zext`/
  `sext`, `int_ops.rs`) are **intentionally** declaration-only — the
  primitive reducible interface the ops above are built on, not a stub.

## defs/core.cov migration (partial)

- **`defs/core.cov` + the `defs::cov` parser** migrate part of the catalogue to
  data (`#def`/`#newtype`/`#subtype`/`#quot` over `covalence-sexp`), byte-identical
  to the hand-written `defs::*` (asserted in `cov::tests`). **Migrated:** the logic
  connectives, `fun` combinators, `unit`/`unit.nil`, `coprod`/`prod`/`option`/
  `result` + ops. **Stayed Rust** (don't fit the four directives): built-in
  literals, ε-selector primitive specs, recursors, nat/int/rat arithmetic. The
  accessors still source from Rust (`.cov` proven equal, not yet authoritative) —
  flipping the source of truth + porting the numeric tower (hand-rolled copy did it)
  is the follow-up.

## defs source-of-truth flip — reverted, pending re-entrancy fix

- **Flipping the public `defs::*` accessors to source from `core_env()` is
  DEFERRED.** An attempt (merge `f349a58`) made `defs::and()` → `spec("bool.and")`
  → `core_env()` (a `LazyLock`) whose own init (`parse_core` over `core.cov`)
  re-entered the same accessor on the same thread → **std `LazyLock` deadlock**,
  freezing the whole `covalence-hol` suite. Reverted (`fed9819`). To redo safely:
  `parse_core` must resolve catalogue references from the **partial env under
  construction** (or a build-local Rust resolver), NEVER from the `core_env`-backed
  `defs::*` accessors — and the change must be **test-gated** (the original was
  build-only). `core.cov` + the byte-identical `cov::tests` remain in place; the
  accessors stay Rust-sourced (`.cov` proven-equal but not yet authoritative).

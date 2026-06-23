# Skeletons — covalence-core

## Declaration-only catalogue ops (no definitional body yet)

These `defs/` term-specs carry `tm = None`: sound/complete on literals (via
`builtins.rs`) but no open-form body, so nothing is provable by
`unfold_term_spec`. Each should become a `let_term!` / `spec_term!` def (see
`docs/roadmap.md`); on adding a body, delete here and — if reducible — add to
`audit_reduce.rs::audit_reduce_matches_body`.

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

## Hash-consing not threaded through the inference rules

Term/type interners (`term::cons`, `ty::cons`) are wired through the
smart-constructor baselines and the `*_with` subst variants, but the rules in
`thm/`, `Ctx`, and `hol.rs` builders construct via plain constructors, so a proof
does not share one interner end-to-end. Thread a caller-supplied
`&mut dyn TrustedCons` through the rule surface (+ a `Ctx`-owned interner) to make
it on-by-default; this would cut the ~29% allocation dominating the list-bootstrap
profile. Soundness unaffected either way. (Then also intern `TermInfo::Wf(Type)`
cached types, currently freshly allocated.)

## Name-only `subst::close` should move out of the TCB

`subst::close(t, name)` is a trusted construction convenience that doesn't belong
in the kernel (rules taking arbitrary theorem terms already use the type-aware
`close_var` / `subst_free` / `has_free_var_typed`). It remains only because ~169
`init/` construction sites in `covalence-hol` call it. Eventually reimplement in
userspace (`TermExt`) or migrate the call sites to `close_var(&Var::new(...))`.
Deferred for call-site churn.

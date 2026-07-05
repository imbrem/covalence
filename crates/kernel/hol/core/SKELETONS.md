# Skeletons — covalence-core

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

Module-local skeletons: [`src/thm/SKELETONS.md`](src/thm/SKELETONS.md) (the
`covalence-pure` mint-gate future seams).

## toHOL purge: Obs leaves await `FreshId` reclassification

The observer *rules* are gone (`notes/vibes/pure-hol-and-build-plan.md`), but
`TermKind::Obs`/`TypeKind::TyConObs` + `Object`/`Observer` remain solely as
`new_type_definition`'s freshness tokens (`rules.rs::NewTypeDefRule`). Replace
them with dedicated private `FreshId` leaves
(`TermKind::FreshConst`/`TypeKind::FreshTyCon`), then delete `Observer`/`Object`
and the `has_no_obs`/`all_obs_match`/`for_each_obs` walkers.

## Declaration-only catalogue ops (no definitional body yet)

These `defs/` term-specs carry `tm = None`: sound/complete on literals (via
`builtins.rs`) but no open-form body, so nothing is provable by
`unfold_term_spec`. Each should become a `let_term!` / `spec_term!` def (see
`notes/vibes/roadmap.md`); on adding a body, delete here and — if reducible — add to
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

## Hash-consing not on-by-default

`Ctx` has no owned interner, `hol.rs` builders construct plain, `TermInfo::Wf(Type)` cached
types are freshly allocated, and the script/init consumers do not thread a cons
(only the metamath replay path in `metalogic/mm_database.rs` does) — so replay
proofs still don't share one interner end-to-end. Making it on-by-default would
cut the ~29% allocation dominating the list-bootstrap profile. Soundness
unaffected either way.

## Name-only `subst::close` should move out of the TCB

`subst::close(t, name)` is a trusted construction convenience that doesn't belong
in the kernel (rules taking arbitrary theorem terms already use the type-aware
`close_var` / `subst_free` / `has_free_var_typed`). It remains only because many
`init/` construction sites in `covalence-init` call it. Eventually reimplement in
userspace (`TermExt`) or migrate the call sites to `close_var(&Var::new(...))`.
Deferred for call-site churn.

## `_with` rules intern post-hoc, not through construction

The cons-threaded `_with` rule variants build via the plain rule then
`intern_concl`/`intern_thm` (table-priming only — the returned theorem keeps its
own `Arc`s). The stranded 9d3673f9 design instead threaded `cons` through term
*construction* (`hol_and_with`-style builders in `hol.rs`), so the theorem itself
holds interned nodes. Pure perf nuance, no soundness role; revisit if profiles
show residual alloc churn on the replay paths.

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

## Hash-consing not yet threaded through the inference rules

- **`crate::term::cons` (`TrustedCons`/`TermCons`/`HashCons`/`Checked`) is wired
  through the `Term` smart-constructor baseline (`Term::alloc`), `Term::cons_with`
  (deep intern), and every term-rebuilding fn in `subst.rs` (the `*_with`
  variants).** What is *not* yet threaded: the inference rules in `thm/`, `Ctx`,
  and `hol.rs` builders all construct terms via the plain (`&mut ()`)
  constructors / plain `subst::*`, so a proof does not yet share one interner
  end-to-end — interning only happens when a caller explicitly routes through a
  `*_with` API. Threading a caller-supplied `&mut dyn TrustedCons` through the
  rule surface (and a `Ctx`-owned interner) is the follow-up that turns this from
  "available" into "on by default for large proofs". Soundness is unaffected
  either way (the rules already accept any structurally-equal term).

## Name-only `subst::close` should move out of the TCB

- **`subst::close(t, name)` (name-only) is a construction convenience that does
  not belong in the trusted kernel.** Free variables are identified by `(name,
  type)` ([`Var`]); the kernel rules that take arbitrary theorem terms (`abs`,
  `all_intro`, `inst`, `nat_induct`) already use the type-aware `close_var` /
  `subst_free(&Var)` / `has_free_var_typed(&Var)`. The name-only `close` remains
  only because ~169 *construction* sites in `covalence-hol`'s `init/` (almost all
  `Term::abs(ty, subst::close(&body, name))`, where the name has a single known
  type by construction) still call it. It is sound there, but it is trusted code
  earning its keep only as a convenience. **Eventually remove it from
  `covalence-core` and reimplement it in userspace** (e.g. `covalence-hol`'s
  `TermExt`, untrusted) — or migrate the 169 sites to `close_var(&Var::new(name,
  ty))`. Slims the TCB surface; deferred only for the call-site churn.

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

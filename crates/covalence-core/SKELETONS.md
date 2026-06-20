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

## defs/core.cov is the source of truth for the migrated catalogue

- **`defs/core.cov` + the `defs::cov` parser** are now the **source of truth**
  for the migrated catalogue (`#def`/`#newtype`/`#subtype`/`#quot` over
  `covalence-sexp`). The parser builds each `TermSpec`/`TypeSpec` directly and
  stores it in the process-shared `cov::core_env()`; the public `defs::*`
  accessors (`defs::and()`, `defs::option_spec()`, …) are now **thin lookups**
  that read those handles back out, so there is a single `Arc` per migrated
  symbol shared everywhere (kernel `Type::unit()`, other `.cov` defs,
  `covalence-hol`). The hand-written `λ`-builder bodies were deleted from
  `defs/{logic,fun,unit,fail,coprod,prod,option,result}.rs`.
  - **Migrated (sourced from `core.cov`):** the logic connectives + quantifiers
    (`bool.{and,or,not,imp,iff,forall,exists}`), `fail`, `fun.{id,const,compose,
    flip}`, `unit`/`unit.nil`, `coprod`/`inl`/`inr`/`coprod.case`, `prod`/`pair`/
    `fst`/`snd`, `signed1`/`signed2`, `option`/`none`/`some`/`option.case`/
    `isSome`/`unwrap`, `result`/`ok`/`err`.
  - **Symbols:** every migrated name still has a `Canonical` variant, so the
    parser tags its spec with the *same* `Canonical` symbol the deleted
    accessor used — object identity (`==`, pointer-based via `symbol_eq`) is
    unchanged. (The parser falls back to an opaque `SmolStr` symbol for names
    without a `Canonical` variant — fine for user `.cov`.)
  - **Verified:** `cov::tests` keeps the byte-identical assertions; the full
    `covalence-hol` suite (509 tests, whose proofs depend on object identity)
    stays green.

### Stayed Rust (cannot be `.cov` data — by design, not stubs)

These are **not** skeletons to fill; they are kept in Rust deliberately:

- **Built-in literals** — `TermKind::Int`/`Blob`/`SmallInt` (binary-data
  substrate efficiency).
- **ε-selector primitive specs** — the recursors (`nat.rec`, `iter`),
  `prod.fst`/`snd` and `coprod.case` *are* migrated (their ε bodies fit `#sel`),
  but the nat/list recursion machinery and the not-yet-migrated selector specs
  stay Rust.
- **nat/int/rat arithmetic + reduction-coupled ops** — anything in
  `builtins.rs::PRIM_TABLE` (nat/int/bytes arithmetic, fixed-width `uN`/`sN`
  ops) is dispatched by `TermSpec` *pointer identity*; its body must be the
  exact Rust the reducer agrees with, so it stays a hand-written `let_term!` /
  `spec_term!` (a `.cov` re-expression would be a *different* `Arc` and break
  reduction dispatch). `cond` likewise stays a Rust `let_term!`.
- **The `bits`/width tower** (`bits`, `bit`, `u2…u512`, `s1…s512`, `char`,
  `string`) — these are subtypes whose predicates reference still-Rust ops
  (`bits.len`, `nat.<`); migrating them is the next batch, blocked on routing
  those still-Rust *term* constants through the parser's `catalogue_term`
  fallback. `bit` is already exposed as a type-ctor fallback so the migrated
  `signed1`/`signed2` can name it.

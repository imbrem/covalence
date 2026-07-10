# base API surface — what core/eval actually consume (inventory)

**Status:** snapshot on branch `base-abstract` (2026-07-09), Track C deliverable 1.
Method: `grep "covalence_pure"` over `crates/kernel/hol/` + `crates/kernel/base/eval/`,
then per-item verification of every use site. Line numbers are as of this snapshot;
items are the durable content.

This is the ground truth behind the `covalence_pure::api` facade
(`crates/kernel/base/src/api.rs`) and the abstraction sketch
(`crates/kernel/base/src/algebra.rs`). See `notes/vibes/base-abstraction.md` for the
design story.

## Consumers

Only three crates import `covalence_pure` at all:

| crate | path | role |
|---|---|---|
| `covalence-core` | `crates/kernel/hol/core` | HOL kernel: `core::Thm` = newtype over `pure::Thm<L, IsThmProp<C>>` |
| `covalence-hol-eval` | `crates/kernel/hol/eval` | eval tier: `CoreEval` language, cert/toHOL rules, reification drivers |
| `covalence-pure-eval` | `crates/kernel/base/eval` | in-group: the `Builtins` language (native `CanonRule` catalogue) |

`covalence-init` has **no** direct `covalence-pure` dependency (it consumes the seam
through `covalence-core::seam` and `covalence-hol-eval`). Neither do
`covalence-hol` (traits) or anything else in the workspace.

## A. Trust-bearing items (the certificate algebra)

These are the items whose *semantics* the consumers rely on for soundness. Any
future base (the relations refactor) must provide the same algebra.

### `Thm<L, P>` — the certificate (type + methods)

- `covalence_pure::Thm` as the wrapped field of `core::Thm`:
  `crates/kernel/hol/core/src/thm/mod.rs:98` (`pub struct Thm<L, C>(covalence_pure::Thm<L, IsThmProp<C>>)`).
- As the premise alias `Prem<L> = covalence_pure::Thm<L, CoreProp>`:
  `crates/kernel/hol/core/src/thm/rules.rs:52`.
- As `PThm` in the reification drivers: `crates/kernel/hol/eval/src/tohol.rs:13`
  (`Thm as PThm`), `crates/kernel/hol/eval/tests/tohol.rs:13`.
- **Methods consumed** (all trust-bearing — each is a mint or a read):
  - `Thm::prop()` (read-only accessor): `core/src/thm/mod.rs:157,164,170,173,176`,
    `core/src/thm/rules.rs:56` (`parts`).
  - `Thm::lift(into)` (gated tier coercion): `core/src/thm/mod.rs:216`,
    `core/src/thm/hol_light_tests.rs:82`.
  - `Thm::refl(e, lang)` (ungated calculus): `hol/eval/src/tohol.rs:81,84,89,169,268,271,298,302,324,327,450,454,463,467,477,481`.
  - `Thm::sym()` : `hol/eval/src/tohol.rs:172` (`isthm_eq.sym()`).
  - `Thm::trans(other)` : `hol/eval/src/tohol.rs:503,506` (spine transport in
    `reify_app`; also exercised in `core/src/thm/hol_light_tests.rs:111,499,649,853`).
  - `Thm::eq_mp(eq)` (Leibniz transport — THE landing step):
    `hol/eval/src/tohol.rs:93,172`.
  - `Thm::cong_app(f)` : `hol/eval/src/tohol.rs:91,171,504`.
  - `Thm::cong_pair(other)` : `hol/eval/src/tohol.rs:90,170,501`.
  - `Thm::lang()` — **not consumed** anywhere outside base.

### Gated mint entry points (free functions)

- `apply(lang, rule, input)` — the sole mint for every HOL rule and cert rule:
  `core/src/thm/rules.rs:195` (the `mint!` macro body, i.e. every core rule),
  `hol/eval/src/lib.rs:39+91` (the eval `mint` helper),
  `hol/eval/src/tohol.rs:13` (all cert applications),
  tests `hol/eval/tests/{tohol.rs:13, audit_reduce.rs:38, floats.rs:25}`.
- `canon(f, arg, lang)` — gated `CanonRule` evaluation:
  `hol/eval/src/tohol.rs:13,505` (`canon(HolApp, (fv, xv), CoreEval)`),
  test `hol/eval/tests/tohol.rs:13`.
- `apply0`, `apply_rewrite`, `of_eq`, `of_eq_with`, `of_ptr_eq`, `semidecide`,
  `execute` — **not consumed** outside base (see §C).

### `Language` — the trust gate trait

- Implemented by consumers (this is how a tier declares its TCB):
  `CoreLang` at `core/src/thm/lang.rs:48` (+ impl below it),
  `CoreEval` at `hol/eval/src/lang.rs:40+57`,
  `Builtins` at `base/eval/src/lib.rs:56`,
  `TestTier` at `core/src/thm/hol_light_tests.rs:48`.
- Methods called by consumers: `admits` (delegation in `CoreEval::admits`,
  audit tests `core/src/thm/rules.rs:776+`, `hol/eval/src/rules.rs:467+`),
  `extends` (`hol/eval/src/lang.rs:70`, `core/src/thm/rules.rs:822`).
  `union` is implemented (trivially, ZST tiers) but never called directly.

### `Manifest` / `RuleRecord` / `LangMeta` / `RuleMeta` — the static TCB tree

- `CORE_MANIFEST`: `core/src/thm/rules.rs:31` (+ the `core_rules!` emission).
- `EVAL_MANIFEST`: `hol/eval/src/rules.rs:28` (+ the `eval_rules!` emission).
- `BUILTINS` manifest: `base/eval/src/lib.rs:56`.
- Golden files: `docs/deps/{core,eval,builtins}-manifest.txt`, pinned by
  `manifest_matches_golden` tests in each crate.

### `Rule<L>` / `CanonRule` — the admitted-rule traits

- `Rule<L>` implemented for every core rule (`core_rules!`,
  `core/src/thm/rules.rs:31`) and every eval cert/toHOL rule (`eval_rules!`,
  `hol/eval/src/rules.rs:28`); bound in the eval `mint` helper
  (`hol/eval/src/lib.rs:91`).
- `CanonRule` implemented by every `covalence-pure-eval` op
  (`base/eval/src/lib.rs` `canon_op!`) and by `HolApp` + the toHOL ops
  (`hol/eval/src/tohol_ops.rs:24`); consumed as a *bound/witness* via
  `CanonRule as _` for native `.eval(..)` calls at
  `hol/eval/src/{rules.rs:202, tohol.rs:13, certs.rs:32}` (the certs dispatch
  computes natively, then states the equation), and as a generic bound at
  `hol/eval/src/tohol.rs:392,423`.

### `Error` (pure error enum)

- Lowered into `core::Error::Pure` at `hol/eval/src/tohol.rs:42-45`; matched as
  `PureError` in `core/src/thm/rules.rs:31`, `hol/eval/src/rules.rs:28,204`
  (`Error::NoMatch` constructed), tests `hol/eval/tests/{floats.rs:25, tohol.rs:13}`.

## B. Expression-grammar items consumed (vocabulary, not mint power)

Freely constructible — writing them proves nothing — but they are the *shape* of
every consumed proposition, so the future base must keep (or provide an
isomorphic image of) exactly these:

- `App` — `IsThmProp<C> = App<IsThm, (Val<Ctx>, C)>` (`core/src/thm/lang.rs:48+103`),
  spine shapes in `hol/eval/src/{rules.rs:28, tohol_ops.rs:24}`, tests
  `hol/eval/tests/{nat_add_symbolic.rs:20, int_bytes_symbolic.rs:28, float_symbolic.rs:28}`.
- `Val` — the leaf seam for `Ctx`/`Term`/`Nat`/… : same sites + `core/src/thm/mod.rs:51`.
- `Op` — implemented by `IsThm` (`core/src/thm/lang.rs:82`), by the toHOL ops
  (`hol/eval/src/tohol_ops.rs:24`), by every pure-eval builtin.
- `Expr` — as a bound (`C: Expr<Ty = Term>`, `core/src/thm/mod.rs:51,98`;
  reify drivers `hol/eval/src/tohol.rs:13`).
- `Eqn` — the equality proposition, conclusion shape of every reification
  equation (`hol/eval/src/{tohol.rs:13+39, rules.rs:28}`).
- `F32` / `F64` — bit-exact float leaf sorts: `hol/eval/src/{tohol.rs:13,
  tohol_ops.rs:24, certs.rs:682,748,755,769, rules.rs:28}`, `base/eval/src/float.rs:23`
  (re-exports the whole trusted `float.rs` op inventory: `F32Abs…F64Trunc`,
  `I32ReinterpretF32`, …), tests `hol/eval/tests/{floats.rs, float_symbolic.rs, typed_floats.rs}`.

## C. NOT consumed outside `crates/kernel/base/` (refactor freedom)

Everything below is exercised only by base-internal tests today. It is exactly
the space the relations refactor may reshape without touching core/eval:

- **Expression shapes:** `Ref`, `Dyn`, `True`, `False`, tuples-as-`Expr` beyond
  the pair inside `IsThmProp`/cert inputs, `TrustedDeref`.
- **Ungated leaf-equality injectors:** `of_eq`, `of_eq_with`, `of_ptr_eq`,
  `semidecide`; `Thm::trans_ptr`.
- **Bool theory:** `And`/`Or`/`Imp`/`Not`, `and_intro`/`and_elim`/`or_inl`/
  `or_inr`/`mp` (pure `Thm` methods — core has its own HOL-level connectives).
- **Matching/rewrite seam:** `MatchApp`, `Rewrite`, `apply_rewrite`, `apply0`.
- **Relation calculus (Front D Phase 0):** `UntrustedFn`, `RelErr`, `Rel`,
  `execute`, `Transpose`/`Compose`/`Join`/`Meet` + `Thm::{transpose, compose,
  meet, join_l, join_r}`.
- **HOL-ω reflection (B-K1..3):** `TyFn`/`TyApp`/`TyBound`/`TyAll`/`TyAbs` +
  helpers (`ty_fn`…), `KStar`/`KArrow`/`k_star`/`k_arrow`/`star`,
  `KindOf`/`RankOf`/`RankLe`, `TyC`/`KindC`.
- **`Thm::lang()`**, `ThmEqn` alias, `Thm::lhs`/`Thm::rhs`.

Caveat: "not consumed" = no compile-time use today. The rel calculus and HOL-ω
reflection are *roadmap-bearing* (Fronts D/E) — freedom to reshape, not to drop.

## D. `covalence-pure-eval` surface consumed by `covalence-hol-eval`

The in-group `Builtins` crate is itself part of the base seam; hol/eval consumes:

- `Builtins` (the language): `hol/eval/src/lang.rs:70` (extends-check),
  `core/src/thm/rules.rs:822` (negative audit), tests `hol/eval/tests/tohol.rs:14`.
- `NatAdd` (direct native eval): `hol/eval/src/rules.rs:202`, `hol/eval/src/tohol.rs:14`.
- `FwRepr` (fixed-width repr trait): `hol/eval/src/certs.rs:34`.
- The op catalogue via `pe::*` in the certs dispatch (`hol/eval/src/certs.rs`,
  `hol/eval/src/tohol.rs`): `Nat*` (Succ/Pred/Add/Mul/Sub/Div/Mod/Pow/Shl/Shr/
  BitAnd/BitOr/BitXor/Le/Lt/ToInt/ToBytesLe/ToBytesBe/FromBytesLe/FromBytesBe),
  `Int*` (Succ/Pred/Neg/Abs/Sgn/Add/Mul/Sub/Div/Mod/Le/Lt), `Bytes*`
  (Cat/ConsNat/Len/At/Slice), `Fw*` (Add/Sub/Mul/Div/Rem/And/Or/Xor/Not/Neg/
  Shl/Shr/Le/Lt/Ge/Gt/FromNat/FromInt/ToNat/ToInt), `Sext`/`Zext`,
  float conversions (`F32ConvertI32`…`F64PromoteF32`, `I32TruncSatF32`…
  `U64TruncSatF64`), and the module fns `pe::nat`/`pe::int`/`pe::bytes`/`pe::bool`.

## E. Reading the split

The **trust-bearing kernel of the consumed surface** is small and stable:

> `Thm` (+ `prop`/`lift`/`refl`/`sym`/`trans`/`eq_mp`/`cong_app`/`cong_pair`),
> `apply`, `canon`, `Language`, `Manifest`/`RuleRecord`(+metas), `Rule`,
> `CanonRule`, `Error`, and the proposition vocabulary
> `Expr`/`Op`/`App`/`Val`/`Eqn` (+ `F32`/`F64` leaf sorts).

That is the facade (`covalence_pure::api`) and precisely the algebra the
abstraction sketch (`covalence_pure::algebra::CertificateAlgebra`) captures.
Everything in §C is implementation detail from the consumers' point of view —
the relations refactor can dissolve, replace, or generalize it behind the same
facade.

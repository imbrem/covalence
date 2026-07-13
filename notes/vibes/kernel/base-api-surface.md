# base API surface — what core/eval actually consume

**Status:** snapshot on branch `base-abstract` (2026-07-09), Track C deliverable 1.
Method: `grep "covalence_pure"` over `crates/kernel/hol/` + `crates/kernel/base/eval/`,
then per-item verification. File:line details are in git as of the snapshot; this
keeps the durable split. Ground truth behind the `covalence_pure::api` facade
(`crates/kernel/base/src/api.rs`) and the abstraction sketch (`algebra.rs`) — see
[`base-abstraction.md`](./base-abstraction.md) for the design story.

## Consumers

Only three crates import `covalence_pure` at all:

| crate | path | role |
|---|---|---|
| `covalence-core` | `crates/kernel/hol/core` | HOL kernel: `core::Thm` = newtype over `pure::Thm<L, IsThmProp<C>>` |
| `covalence-hol-eval` | `crates/kernel/hol/eval` | eval tier: `CoreEval` language, cert/toHOL rules, reification drivers |
| `covalence-pure-eval` | `crates/kernel/base/eval` | in-group: the `Builtins` language (native `CanonRule` catalogue) |

`covalence-init` has **no** direct `covalence-pure` dependency (it consumes the
seam through `covalence-core::seam` + `covalence-hol-eval`). Neither do
`covalence-hol` (traits) or anything else.

## A. Trust-bearing items (the certificate algebra)

The items whose *semantics* the consumers rely on for soundness. Any future base
(the relations refactor) must provide the same algebra.

- **`Thm<L, P>`** — the certificate. Wrapped field of `core::Thm`; premise alias
  `Prem<L>`; `PThm` in the reification drivers. Methods consumed (all
  trust-bearing — each a mint or a read): `prop()` (accessor), `lift(into)` (gated
  tier coercion), `refl`/`sym`/`trans`/`eq_mp` (Leibniz transport — THE landing
  step)/`cong_app`/`cong_pair` (the ungated calculus). `lang()` **not** consumed
  outside base.
- **Gated mint entry points:** `apply(lang, rule, input)` — the sole mint for every
  HOL rule and cert rule (core's `mint!` macro, eval's `mint` helper, all cert
  applications). `canon(f, arg, lang)` — gated `CanonRule` eval (one site:
  `HolApp`). `apply0`/`apply_rewrite`/`of_eq`/`of_eq_with`/`of_ptr_eq`/`semidecide`/
  `execute` — **not** consumed outside base (§C).
- **`Language`** — the trust gate trait, implemented by `CoreLang`/`CoreEval`/
  `Builtins`/`TestTier` (how a tier declares its TCB). Methods called: `admits`,
  `extends`. `union` implemented (trivial, ZST tiers) but never called directly.
- **`Manifest`/`RuleRecord`/`LangMeta`/`RuleMeta`** — the static TCB tree.
  `CORE_MANIFEST`/`EVAL_MANIFEST`/`BUILTINS`, pinned by `manifest_matches_golden`
  tests against `docs/deps/{core,eval,builtins}-manifest.txt`.
- **`Rule<L>` / `CanonRule`** — the admitted-rule traits. `Rule<L>` for every core
  rule (`core_rules!`) and eval cert/toHOL rule (`eval_rules!`). `CanonRule` for
  every pure-eval op + `HolApp` + toHOL ops; consumed as a bound/witness for native
  `.eval(..)` calls in the certs dispatch (compute natively, then state the equation).
- **`Error`** — lowered into `core::Error::Pure`, matched as `PureError`.

## B. Expression-grammar items consumed (vocabulary, not mint power)

Freely constructible (writing them proves nothing), but the *shape* of every
consumed proposition — the future base must keep or provide an isomorphic image:

- **`App`** — `IsThmProp<C> = App<IsThm, (Val<Ctx>, C)>`; the cert/toHOL spine shapes.
- **`Val`** — the leaf seam for `Ctx`/`Term`/`Nat`/….
- **`Op`** — implemented by `IsThm`, the toHOL ops, every pure-eval builtin.
- **`Expr`** — as a bound (`C: Expr<Ty = Term>`).
- **`Eqn`** — the equality proposition; conclusion shape of every reification equation.
- **`F32` / `F64`** — bit-exact float leaf sorts (`base/eval/src/float.rs` re-exports
  the whole trusted float op inventory).

## C. NOT consumed outside `crates/kernel/base/` (refactor freedom)

Exercised only by base-internal tests today — the space the relations refactor may
reshape without touching core/eval:

- **Expression shapes:** `Ref`, `Dyn`, `True`, `False`, tuples-as-`Expr` beyond the
  pair inside `IsThmProp`/cert inputs, `TrustedDeref`.
- **Ungated leaf-equality injectors:** `of_eq`, `of_eq_with`, `of_ptr_eq`,
  `semidecide`, `Thm::trans_ptr`.
- **Bool theory:** `And`/`Or`/`Imp`/`Not`, `and_intro`/`and_elim`/`or_inl`/`or_inr`/
  `mp` (pure `Thm` methods — core has its own HOL-level connectives).
- **Matching/rewrite seam:** `MatchApp`, `Rewrite`, `apply_rewrite`, `apply0`.
- **Relation calculus (Front D Phase 0):** `UntrustedFn`, `RelErr`, `Rel`,
  `execute`, `Transpose`/`Compose`/`Join`/`Meet` + `Thm::{transpose,compose,meet,
  join_l,join_r}`.
- **HOL-ω reflection (B-K1..3):** `TyFn`/`TyApp`/`TyBound`/`TyAll`/`TyAbs`,
  `KStar`/`KArrow`, `KindOf`/`RankOf`/`RankLe`, `TyC`/`KindC`.
- **`Thm::lang()`**, `ThmEqn` alias, `Thm::lhs`/`Thm::rhs`.

Caveat: "not consumed" = no compile-time use today. The rel calculus and HOL-ω
reflection are *roadmap-bearing* (Fronts D/E) — freedom to reshape, not to drop.

## D. `covalence-pure-eval` surface consumed by `covalence-hol-eval`

The in-group `Builtins` crate is part of the base seam; hol/eval consumes:
`Builtins` (extends-check + negative audit), `NatAdd` (direct native eval),
`FwRepr` (fixed-width repr trait), and the op catalogue via `pe::*` in the certs
dispatch — `Nat*`/`Int*`/`Bytes*`/`Fw*` families, `Sext`/`Zext`, float conversions,
and the module fns `pe::{nat,int,bytes,bool}`.

## E. Reading the split

The **trust-bearing kernel of the consumed surface** is small and stable:

> `Thm` (+ `prop`/`lift`/`refl`/`sym`/`trans`/`eq_mp`/`cong_app`/`cong_pair`),
> `apply`, `canon`, `Language`, `Manifest`/`RuleRecord`(+metas), `Rule`,
> `CanonRule`, `Error`, and the vocabulary `Expr`/`Op`/`App`/`Val`/`Eqn`
> (+ `F32`/`F64` leaf sorts).

That is the facade (`covalence_pure::api`) and precisely the algebra
`CertificateAlgebra` captures. Everything in §C is implementation detail from the
consumers' point of view — the relations refactor can dissolve, replace, or
generalize it behind the same facade.

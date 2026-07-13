# The literal-leaf endgame — symbolic-prop design

Authoritative design for the literal-leaf endgame's *additive mechanism* wave.
Companion to [`../../plans/pure-hol-and-build-plan.md`](../../plans/pure-hol-and-build-plan.md)
and [`eg5-preflight.md`](./eg5-preflight.md) (the irreversible deletion). The
winning mechanism is **B1** (generalize the conclusion operand); the alternatives
and judging are summarized in §2.

Scope of this wave: build/audit the *additive, reversible* mechanism proving a
`toHOL` value can appear in a `core::Thm` proposition **without materializing** its
succ-tower. Delete nothing. Bulk deletion of the literal leaves is a later,
maintainer-gated stage (EG5).

## 1. The crux, against the real types

The kernel certificate (`crates/kernel/hol/core/src/thm/mod.rs`):

```rust
pub struct Thm<L: HolTier = CoreLang>(covalence_pure::Thm<L, CoreProp>);
//   CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>   — Val<Term> is a CONCRETE term
```

`CoreProp` pins the conclusion operand to `Val<Term>`. A native value enters HOL as
the **base expression** `App<ToHol_v, Val(v)>` of sort `Term` (uninterpreted
op-application, no `CanonRule`), forced toward a concrete term only by the admitted
unfolding/cert rules. That base expression is an `Expr<Ty = Term>` but **not** a
`Val<Term>` — so to land it in a `core::Thm` today you must reify it first, which
materializes the succ-tower.

The machinery to *build and transport* a symbolic prop already works:
`eval/src/tohol.rs::nat_add_thm` mints `NatAddCert ⊢ IsThm(∅, ⌜nat.add (toHOL a)
(toHOL b) = toHOL(a+b)⌝)` as a `pure::Thm<CoreEval, …NatAddEqE…>` — a fully symbolic
prop whose operand is the nested `App`/`ToHolNat`/`Val` shape — and
`eq_mp`/`trans`/`cong`/`canon` operate on it fine. The pipeline then *reifies* it to
concrete `Val<Term>` before wrapping. **That reification is the only reason the tower
gets built.** The crux: *let a `core::Thm` retain the symbolic prop.*

The base equality calculus (`eqn.rs`) works by **stdlib structural `Eq`** on the
`derive(Eq)` shapes: `eq_mp<Q>` needs `P: Expr<Ty=bool> + Eq`; `trans` needs the
middle `B: Eq`; `cong_*` are structural. `Dyn<T>` (`Arc<dyn Expr<Ty=T>>`, pointer
equality) is the lone escape hatch — sound but *un-restructurable* (you cannot
`eq_mp` a `Dyn` into a structurally-different `Dyn`). That pointer-eq wall is "EG4".

## 2. The chosen mechanism — B1, generalize the conclusion operand

Add a *defaulted* type parameter for the conclusion operand:

```rust
pub type IsThmProp<C> = App<IsThm, (Val<Ctx>, C)>;         // C: Expr<Ty = Term>
pub type CoreProp     = IsThmProp<Val<Term>>;               // unchanged value

pub struct Thm<L: HolTier = CoreLang, C = Val<Term>>(pure::Thm<L, IsThmProp<C>>)
where C: Expr<Ty = Term>;
```

`Thm<L>` still means `Thm<L, Val<Term>>` by the default, so **every existing rule
constructor, accessor, and consumer is unchanged** (the rule catalogue lives in
`impl<L: HolTier> Thm<L>`, resolving to the default `C`). A never-materialized
theorem is `Thm<CoreEval, NatAddEqE>` — the conclusion operand *is* the symbolic base
expression, holding `Val<Nat>` bignum leaves under the uninterpreted `ToHolNat`. No
succ-tower ever exists.

**Base-TCB delta: ZERO.** `Thm` + its landing constructor live in `kernel/hol/core`;
`ToHolNat`/`HolApp`/`NatAddCert` already live in `kernel/hol/eval`. `base/trusted` is
untouched — the base calculus already handles these `App`/`Val` shapes (proven daily
by `nat_add_thm`). `App<IsThm, (Val<Ctx>, NatAddEqE)>` derives `Eq` structurally, so
`eq_mp`/`trans` transport it with no new machinery — the laziness *is* the existing
base `Expr`/`Op`/`Rule` algebra.

**Transport / forcing:** the symbolic operand is rewritten by `eq_mp` along a proven
`⊢ symbolic = more-forced` equation — forcing exactly the subterm a proof inspects
and no more. Never inspecting it (the common case: transport, weaken, use as a
hypothesis-free fact) forces nothing. The never-materialize contract by construction.

**Sequent floor:** `from_pure` re-runs `check_sequent` on a concrete `Term`. The
symbolic landing (`from_pure_sym`) runs a **non-forcing** well-typedness check: each
`App<ToHol*, Val>` node has a *declared HOL sort* (`ToHolNat : nat`, `ToHolInt :
int`, …) read off the op without expanding the value; the rest types structurally.
Bounded, per-`ToHol`-op, audit-grade.

**Cost:** a type parameter on `Thm` + per-shape symbolic constructors; `concl() ->
&Term` exists only at the default `C = Val<Term>`. Heterogeneous collections (a `Vec`
of symbolic theorems with *different* operand shapes) need type erasure — that is the
deferred escape hatch (below).

### The judging (summary)

Three architect proposals were scored (soundness / base-TCB Δ / reversibility / fits
maintainer decisions / perf / migration):

- **A — a base reflected-syntax `Tree` sort.** Correct insight (a *homogeneous
  carrier type whose values vary* keeps the base calculus intact) but wrong vehicle:
  a `Tree` embedding `core::Term` + `Nat`/`Int`/`Bytes` cannot live in `base/trusted`
  (layering), and in core it is a second term language needing a full kernel re-plumb.
  **Graft the insight, drop the vehicle.**
- **B1 — generalized `C`** (winner). Realizes A's insight with the existing
  monomorphic `App`/`Val` shapes; keeps `Val<Term>` as the *default* `C` so the
  concrete kernel is untouched.
- **C — a `TermKind::ToHol(v)` node in `core::Term`, forcing lazily.** Cheapest
  migration but fights the maintainer decision "NO symbolic leaf type" and *only
  solves nat* — a `ToHol(Int)`/`(Bytes)` re-imports the very types `defs-out` removes.
  **Reject as mechanism; graft "keep `Val<Term>` as the default `C`."**

**No genuine maintainer-decision fork for the additive mechanism.** Soundness still
rests on `admits()` alone: the only mint of an `IsThm`-headed symbolic prop is an
admitted cert rule that *derives* (never accepts) its conclusion and self-floors.

### The deferred escape hatch (EG4, maintainer-gated)

`CoreProp = App<IsThm, (Val<Ctx>, Dyn<Term>)>` — one Rust type for *all* symbolic
theorems (homogeneous), so `Vec<Thm>` works. But `Dyn` is pointer-eq, so `eq_mp`/
`trans` cannot rewrite a `Dyn` into a structurally-equal *different-allocation* `Dyn`.
Making that work needs a **new base method** — a structural `eq_mp` for `Dyn`
operands (downcast both `Arc<dyn Expr>` and compare, or decode-and-rematch) — an
innermost-TCB addition needing its own audit. Needed *only* when a real consumer
needs heterogeneous symbolic collections; **not** for the nat/int/bytes slices. The
recorded "next wall"; do not improvise the base method.

## 3. Integration with the maintainer decisions

- **`bool`+`nat` builtin, `Zero`+`Succ` in the enum, `nat_induct` axiom.** The nat
  slice works over `toHOL nat` base exprs (leaves are `Val<Nat>` bignums — no
  `Nat(0)` literal involved). Adding `Zero` (replacing the `Nat(0)` literal) and
  keeping `nat_induct` are a later additive stage. `Succ` already exists.
- **int/u8/bytes defined-in-eval.** Their symbolic props reuse B1 verbatim via
  `ToHolInt`/`ToHolBytes`/`ToHolF32/64` — **no `int`/`bytes` node ever enters
  `core::Term`** (the decisive advantage over C).
- **values symbolic by default (`App<ToHol_v, Val(v)>` base Expr).** B1 *is* this.
- **no symbolic leaf type.** Honored — B1 adds no `Term` leaf.
- **`T`/`F` become defined constants.** Orthogonal to the symbolic-prop mechanism
  but required for the pure-tier connective derivations to drop off the eval tier;
  sequenced alongside `Zero`, not a dependency of the nat slice.
- **ε/rep/abs parameterization.** Deferred.

## 4. Staged reversible plan (additive first, deletion last)

- **EG1 (DONE):** generalized `Thm<L, C>` + `from_pure_sym` + `nat_add_thm_symbolic`
  + a never-materialize test (mint a `core::Thm` on a large nat whose materialized
  `Term`-node count is **O(1)**, independent of the value). Fully revertible.
- **EG2 (DONE — int/bytes; float blocked):** symbolic landers for **int**
  (`int_add/mul/neg`) and **bytes** (`bytes_cat/len`) in `covalence-hol-eval::tohol`,
  reusing B1. Additive; zero base delta; zero new admitted rule.

  The realization that shaped it: unlike `NatAddCert` (which already concludes the
  *symbolic* shape, so `nat_add_thm_symbolic` is one-step), the int/bytes *family*
  certs (`IntArithCert`/`BytesCert`) conclude the *concrete* `CoreProp` and take
  `(TermSpec, Vec<Lit>)` producing heterogeneous per-op results — they cannot carry a
  single symbolic `Concl` type. So the symbolic landers mint the sound family cert and
  **transport it backwards** along a proven `⊢ symbolicE = Val(concrete)` reification
  equation (built with the existing `ToHolIntVal`/`ToHolBytesVal`/`ToHolNatVal` reify
  rules + the shared `reify_app` HolApp-spine driver, then flipped with `sym`),
  landing a symbolic `Thm<CoreEval, …>`. Only the existing base
  `eq_mp`/`cong`/`sym` calculus — B1's "laziness is the existing algebra," in the
  concrete→symbolic direction. Test `int_bytes_symbolic.rs`: a megabyte `bytes.cat`
  operand lands with an O(1) materialized-`Term` footprint.

  **The wall — float.** `FloatCert` also concludes concrete `CoreProp` (with
  `small_int` bit-pattern leaves), but the backward transport needs a proven `⊢
  toHOL_f64(bits) = Val(⌜bits⌝)` reify equation — and **no `ToHolF32Val`/`ToHolF64Val`
  reify rule is admitted**. So a float symbolic lander requires a **new admitted
  rule** (a `ToHolFloatVal` reify rule or a dedicated symbolic `FloatAddCert`). A
  distinct wall from EG4's `Dyn`-transport wall (that one = heterogeneous
  collections; this one = a missing per-family reify rule). Both add to the eval-tier
  TCB, both maintainer-gated. Recorded in `core/src/thm/SKELETONS.md`.
- **EG3 (DONE):** `Zero` added to the term enum (nat theory no longer relies on
  `Nat(0)`); `T`/`F` made defined constants; `nat_induct` unchanged.
- **EG4 (maintainer-gated, base-TCB Δ):** *only if* a real consumer needs
  heterogeneous symbolic collections — the `Dyn<Term>` operand + a new audited
  structural-`eq_mp`-for-`Dyn` base method.
- **EG5 (irreversible bulk deletion, maintainer-gated):** delete
  `TermKind::{Nat,Int,SmallInt,Blob,Bool}`; flip the `Lit` facade to the
  symbolic/defined forms; `core::Term` = textbook HOL Light + `Zero`/`Succ`. Detailed
  swap plan in [`eg5-preflight.md`](./eg5-preflight.md).

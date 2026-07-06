# The literal-leaf endgame — symbolic-prop design (stage EG0)

**Status:** AI-authored design panel (2026-07), the authoritative design for the
literal-leaf endgame's *additive mechanism* wave. Companion to
[`pure-hol-and-build-plan.md`](./pure-hol-and-build-plan.md) (Track 2) and
[`handoff/defs-out-of-core.md`](./handoff/defs-out-of-core.md) ("The next wall").
Records three architect proposals, a judge scoring, the synthesized winner, and
a precise EG1 first-slice spec.

**Scope of this wave (binding):** produce the design + build/audit the
*additive, reversible* mechanism proving a `toHOL` value can appear in a
`core::Thm` proposition **without ever materializing** its succ-tower. Delete
**nothing**. The irreversible bulk deletion of the literal leaves is a later,
maintainer-gated stage (EG5 below).

---

## 0. The crux, stated against the real types

The kernel certificate is (`crates/kernel/hol/core/src/thm/mod.rs:79`):

```rust
pub struct Thm<L: HolTier = CoreLang>(covalence_pure::Thm<L, CoreProp>);
//                                     where  CoreProp = App<IsThm, (Val<Ctx>, Val<Term>)>
//                                                                              ^^^^^^^^^ CONCRETE term
```

`CoreProp` (`thm/lang.rs:89`) pins the conclusion operand to `Val<Term>` — a
*concrete* `core::Term` value. Decision (3) says a native value enters HOL as the
**base expression** `App<ToHol_v, Val(v)>` of sort `Term` (an uninterpreted
op-application, no `CanonRule`), forced toward a concrete term only by the
admitted unfolding/cert rules. That base expression is an
`Expr<Ty = Term>` — but it is **not** a `Val<Term>`. So the symbolic value
*cannot be the `CoreProp` operand as it stands*: to land it in a `core::Thm`
today you must reify it to a concrete `Val<Term>` first (which materializes the
succ-tower).

The machinery to *build and transport* a symbolic prop already exists and works:
`crates/kernel/hol/eval/src/tohol.rs::nat_add_thm` mints
`NatAddCert ⊢ IsThm(∅, ⌜nat.add (toHOL a) (toHOL b) = toHOL(a+b)⌝)` as a
`pure::Thm<CoreEval, App<IsThm, (Val<Ctx>, NatAddEqE)>>` — a fully symbolic prop
whose operand is the nested `App`/`ToHolNat`/`Val` shape `NatAddEqE`
(`tohol_ops.rs:133`) — and `eq_mp`/`trans`/`cong_app`/`cong_pair`/`canon`
operate on it fine. The pipeline then *reifies* it to concrete `Val<Term>`
before `from_pure` wraps it. **The reification is the only reason the succ-tower
gets built.** The crux is narrowly: *let a `core::Thm` retain the symbolic prop.*

The base equality calculus that must keep working (`base/trusted/src/eqn.rs`):
`eq_mp<Q>` needs `P: Expr<Ty=bool> + Eq`; `trans` needs the middle `B: Eq`;
`cong_app`/`cong_pair` are structural. All of these work by **stdlib structural
`Eq`** on the `derive(Eq)` shapes. `Dyn<T>` (`expr.rs:147`) is the lone escape
hatch — `Arc<dyn Expr<Ty=T>>` with **pointer** equality, which is *sound but
un-restructurable* (you cannot `eq_mp` a `Dyn` into a structurally-different
`Dyn`). That pointer-eq wall is "S5".

---

## 1. Architect A — a base reflected-syntax `Tree` sort

**Mechanism.** Introduce a sort `Tree`: a reflected term whose leaves may hold a
native value un-expanded (`Tree::ToHolNat(Nat)`, `Tree::App(Box<Tree>,
Box<Tree>)`, `Tree::Term(Term)`, …). Props become
`App<IsThm, (Val<Ctx>, Val<Tree>)>` (or `core::Thm` gains a Tree-prop variant).
Decoding rules relate `Tree` back to `Term`; forcing rules push a `ToHolNat(n)`
leaf toward its succ-tower only when inspected.

**Why it seems attractive.** `Val<Tree>` is a *single Rust type whose values
vary*, so `eq_mp`/`trans` work **unchanged** by structural `Eq` on `Tree` —
the load-bearing insight (values, not shapes, vary; a homogeneous carrier type
keeps the base calculus intact).

**Base-TCB delta.** LARGE and mislocated. A `Tree` that embeds `core::Term` and
holds `Nat`/`Int`/`Bytes` cannot live in `base/trusted` — base sits *below* core
and must not know `Term`/`covalence_types` (layering). Put in core, `Tree` is "a
second term language": every HOL rule (`refl`, the `IsThm` judgement, the
sequent floor) speaks `Term`, so the kernel must be re-plumbed to `Tree` or
maintain a full `Term↔Tree` bridge.

**Verdict.** Correct insight (homogeneous carrier ⇒ free transport), wrong
realization: it pays a whole new syntax + kernel re-plumb for something a
defaulted type parameter (Architect B) or the existing `Term` (Architect C) gets
for near-zero cost. Fits decisions poorly (a new reflected sort *is* the "new
leaf/sort" decisions 3–4 rule out). **Graft its insight, drop its vehicle.**

---

## 2. Architect B — generalize the conclusion operand

Two sub-variants; **B1 is the proposal, B2 is its deferred escape hatch.**

### B1 — monomorphic generalization (the winning core)

**Mechanism.** Add a *defaulted* type parameter for the conclusion operand:

```rust
pub type IsThmProp<C> = App<IsThm, (Val<Ctx>, C)>;         // C: Expr<Ty = Term>
pub type CoreProp     = IsThmProp<Val<Term>>;               // unchanged value

pub struct Thm<L: HolTier = CoreLang, C = Val<Term>>(pure::Thm<L, IsThmProp<C>>)
where C: Expr<Ty = Term>;
```

`Thm<L>` still means `Thm<L, Val<Term>>` by the default, so **every existing
rule constructor, accessor, and consumer is literally unchanged** (the 39-rule
catalogue lives in `impl<L: HolTier> Thm<L>`, which resolves to the default `C`).
A never-materialized theorem is `Thm<CoreEval, NatAddEqE>` — the conclusion
operand *is* the symbolic base expression `nat.add (toHOL a) (toHOL b) = toHOL
(a+b)`, holding `Val<Nat>` bignum leaves under the uninterpreted `ToHolNat`. It
sits directly in the prop; no succ-tower ever exists.

**Base-TCB delta: ZERO.** `Thm` and its landing constructor live in
`kernel/hol/core`; `ToHolNat`/`HolApp`/`NatAddCert` already live in
`kernel/hol/eval`. **`base/trusted` is not touched at all** — because the base
calculus (`eq_mp`/`trans`/`cong`/`canon`) *already* handles these `App`/`Val`
shapes (proven daily by `nat_add_thm`). `App<IsThm, (Val<Ctx>, NatAddEqE)>`
derives `Eq` structurally (every node is a `derive(Eq)` shape over `Eq` leaves),
so `eq_mp`/`trans` transport it with no new machinery — the laziness *is* the
existing base `Expr`/`Op`/`Rule` algebra, exactly as decision (3) states.

**Transport / forcing story.** The symbolic operand is rewritten by `eq_mp`
along a proven `⊢ symbolic = more-forced` equation — forcing exactly the subterm
a proof inspects and no more. Never inspecting it (the common case: transporting,
weakening, using it as a hypothesis-free fact) forces nothing. This is the
never-materialize contract, delivered by construction.

**Sequent floor.** `from_pure` re-runs `check_sequent` on a concrete `Term`. The
symbolic landing (`from_pure_sym`) runs a **non-forcing** well-typedness check:
each `App<ToHol*, Val>` node has a *declared HOL sort* (`ToHolNat : nat`,
`ToHolInt : int`, …) read off the op without expanding the value; the rest of
the equation types structurally. Bounded, per-`ToHol`-op, audit-grade. (Minimal
EG1 fallback: trust the cert's own `seq` floor, since the *only* mint of an
`IsThm`-headed symbolic prop is an admitted rule whose `decide` already floored
it — the same "hygiene-only" reasoning `from_pure`'s docstring uses. The decode
is preferred for audit-cleanliness.)

**Cost.** A type parameter on `Thm` and per-shape symbolic constructors;
`concl() -> &Term` exists only at the default `C = Val<Term>` (symbolic
theorems expose their operand as an `Expr`, not a forced `Term`). Heterogeneous
collections (a `Vec` of symbolic theorems with *different* operand shapes) need
type erasure — see B2.

### B2 — `Dyn<Term>` homogeneity + a new base transport method (DEFERRED)

**Mechanism.** `CoreProp = App<IsThm, (Val<Ctx>, Dyn<Term>)>` — one Rust type
for *all* symbolic theorems (homogeneous), heterogeneous values, so `Vec<Thm>`
works. **But** `Dyn` is pointer-eq, so `eq_mp`/`trans` cannot rewrite a `Dyn`
into a structurally-equal *different-allocation* `Dyn`. Making that work needs a
**new base method** — a structural `eq_mp` for `Dyn` operands (downcast both
`Arc<dyn Expr>` to a common concrete shape and compare, or a decode-and-rematch)
— which is an innermost-TCB addition requiring its own soundness audit.

**Verdict.** B2 is the honest answer *only when a real consumer needs
heterogeneous symbolic collections*. It is **not** needed for the nat slice, nor
for EG1–EG3. Building the new base method now would violate the "minimal
base-TCB, additive this wave" rule. **Defer B2 to EG4, maintainer-gated.** It is
the recorded "next wall," not this wave's work.

---

## 3. Architect C — a `toHOL` node in `core::Term`, forcing lazily

**Mechanism.** Add a constructor to `core::Term` (e.g. `TermKind::ToHol(v)`)
understood as a *defined-constant family*: `ToHol(n)` denotes `Succ^n(Zero)` via
the admitted unfolding equations, exactly as `Succ`/`Zero` are constants. Props
stay `App<IsThm, (Val<Ctx>, Val<Term>)>` **unchanged** — so `Thm`'s API, `eq_mp`,
`trans`, the sequent floor: all unchanged, homogeneous type, heterogeneous
values, and `Val<Term>` is `Eq` so transport is free.

**"Not a symbolic leaf" argument.** `ToHol` is a constant former (a family of
`Const`-like nodes), not a computational literal carrying kernel-privileged
arithmetic; its meaning is pinned only by admitted unfolding rules, so writing it
is inert — HOL-Light-shaped.

**Why it loses.**
1. **Directly contradicts decision (4)** ("NO symbolic leaf type; toHOL maps to a
   REGULAR Term lazily") and (3) (the value lives as a *base Expr*, not a Term
   node). Architect C's own framing ("defined-constant family") is exactly the
   dressing decision (4) anticipates and rules out — it is a new `Term` variant
   holding a native value.
2. **Only solves nat.** A `TermKind::ToHol(Int)` / `(Bytes)` re-imports
   `Int`/`Bytes` into `core::Term` — re-coupling the very types `defs-out` is
   removing. Restricting the node to `Nat` leaves int/bytes/u8/f32 with no way to
   sit symbolically in a prop, so the general literal endgame is unsolved.
3. Its *only* advantage over B1 (homogeneous `Val<Term>` type) is precisely what
   B2 recovers when actually needed, without a permanent `Term` leaf.

**Verdict.** Cheapest migration, but fights the maintainer decisions and doesn't
generalize past nat. **Reject as the mechanism; graft one idea:** keep
`Val<Term>` as B1's *default* `C`, so the concrete kernel is untouched — C's real
contribution is "don't disturb the concrete path," which B1 honors via the
defaulted parameter.

---

## 4. Judge — scoring and synthesis

Scores 1–5 (higher better). Dimensions per the mission.

| Proposal | Soundness | Base-TCB Δ min. | Reversibility | Fits decisions | Perf | Migration | Total |
|---|---|---|---|---|---|---|---|
| **A** Tree sort | 4 | 1 | 2 | 2 | 4 | 1 | 14 |
| **B1** generalized `C` | 5 | **5** | **5** | **5** | 5 | 4 | **29** |
| B2 Dyn + base method | 3 | 2 | 3 | 4 | 4 | 3 | 19 |
| **C** Term node | 5 | 5 | 4 | 2 | 5 | 5 | 26 |

**Winner: B1**, the generalized-conclusion `Thm<L, C = Val<Term>>`, grafting:

- **from A**: the load-bearing insight — a *homogeneous carrier type whose
  values vary* keeps the base calculus intact; B1 realizes it with the existing
  monomorphic `App`/`Val` shapes instead of a new sort.
- **from C**: keep `Val<Term>` as the **default** `C`, so the entire concrete
  kernel (rules, accessors, `from_pure`, all downstream) is *literally
  unchanged*. C's genuine contribution is "don't disturb the concrete path."
- **B2 (`Dyn` + new base transport method)** is the *deferred, maintainer-gated*
  escape hatch for heterogeneous symbolic collections — the honest next wall
  (EG4), explicitly **not** built this wave.

**Why B1 is clearly sound and additive (no fork).** It adds **zero** to
`base/trusted`; the base calculus already transports these shapes (existing
`nat_add_thm` is the standing proof). The new surface is a defaulted type
parameter + a symbolic landing constructor in `core`, both additive — the
default recovers today's `Thm` byte-for-byte. Soundness still rests on
`admits()` alone: the only mint of an `IsThm`-headed symbolic prop is an admitted
cert rule that derives (never accepts) its conclusion and self-floors. There is
**no genuine maintainer-decision fork** for the additive mechanism, so this wave
proceeds; the fork (the `Dyn` base method) lives strictly at EG4 and is deferred.

### Integration with the binding maintainer decisions

- **(1) `bool` + `nat` builtin, `Zero`+`Succ` in the term enum, `nat_induct`
  axiom.** EG1 does not need `Zero` (it works over `toHOL nat` base exprs, whose
  leaves are `Val<Nat>` bignums — no `Nat(0)` literal involved). Adding `Zero`
  (replacing the `Nat(0)` literal) and keeping `nat_induct` are a later additive
  stage (EG3). `Succ` already exists (`term.rs:648`).
- **(2) int/u8/bytes defined-in-eval.** Unchanged. Their symbolic props reuse
  B1 verbatim via `ToHolInt`/`ToHolBytes`/`ToHolF32/64` — **no `int`/`bytes` node
  ever enters `core::Term`** (the decisive advantage over Architect C).
- **(3) values symbolic by default (`App<ToHol_v, Val(v)>` base Expr).** B1 *is*
  this: the conclusion operand is that base Expr, transported lazily by the
  existing algebra.
- **(4) no symbolic leaf type.** Honored — B1 adds **no** `Term` leaf (this is
  why it beats C).
- **(5) `T`/`F` become defined constants.** Orthogonal to the symbolic-prop
  mechanism, but required for the *pure-tier* connective derivations to drop off
  the eval tier (see `handoff/tohol-purge.md` "LOGIC-OUT" §1). Sequenced in EG3
  alongside `Zero`, coordinated with logic-out; not a dependency of EG1.
- **(6) ε/rep/abs parameterization.** Deferred (unchanged); not this wave.

---

## 5. EG1 — the first-slice spec (minimal, additive, end-to-end on nat)

**Goal:** a `core::Thm` mentioning a large `toHOL` nat value whose succ-tower is
*never* materialized — deleting nothing. Reuses the already-admitted, already
sound `NatAddCert`; simply **omits the reification** that today forces the tower.

**Changes (all additive):**

1. **`crates/kernel/hol/core/src/thm/` — generalize `Thm`.**
   - Add `pub type IsThmProp<C> = App<IsThm, (Val<Ctx>, C)>` and redefine
     `CoreProp = IsThmProp<Val<Term>>` (same value).
   - `pub struct Thm<L: HolTier = CoreLang, C = Val<Term>>(pure::Thm<L,
     IsThmProp<C>>) where C: Expr<Ty = Term>`. Confirm `impl<L: HolTier>
     Thm<L>` blocks resolve to `Thm<L, Val<Term>>` via the default (they do —
     defaults apply in impl headers), so the 39-rule catalogue and every
     accessor compile unchanged.

2. **`core` — the symbolic landing constructor.**
   `impl<L: HolTier, C> Thm<L, C> where C: Expr<Ty = Term> + Eq + 'static`:
   `pub fn from_pure_sym(t: pure::Thm<L, IsThmProp<C>>) -> Result<Self>`. Runs
   the **non-forcing** sequent floor: a `hol_type_sym` helper that assigns each
   `App<ToHol*, Val>` its declared sort (`ToHolNat → nat`, …) without expanding,
   and types the rest structurally, confirming the concl is HOL-`bool`. (EG1
   fallback if the decode slips schedule: trust the cert floor, documented as
   above — but land the decode for audit-cleanliness.)

3. **`crates/kernel/hol/eval/src/tohol.rs` — the symbolic mint (next to
   `nat_add_thm`, which stays).**
   `pub fn nat_add_thm_symbolic(a: Nat, b: Nat) -> Result<Thm<CoreEval,
   NatAddEqE>>`: mint `NatAddCert` (existing), land via `from_pure_sym`. **No
   `ToHolNatVal`, no `reify_app`, no `eq_mp` reification** — the `ToHolNat`
   leaves stay symbolic.

4. **`crates/kernel/hol/eval/tests/` — the proof-of-mechanism test.**
   `nat_add_symbolic_never_materializes`: pick `a = b` a large `Nat` (e.g.
   magnitude `10^9`+). Call `nat_add_thm_symbolic(a, b)`; assert `Ok`. Then:
   - assert the concl operand's three `ToHolNat` leaves hold the native `Nat`s
     `a`, `b`, `a+b` (peek the `App`/`Val` structure);
   - **assert no succ-tower exists**: a helper walks the prop `Expr` and counts
     materialized `core::Term` nodes — it is **O(1)** (a handful of
     const/`HolApp` nodes for `nat.add`/`=`), *independent of `a`*. This is the
     never-materialize guarantee, machine-checked.

**Delete nothing.** `nat_add_thm` (reifying), the `Lit` facade, and all literal
leaves stay. EG1 is fully revertible: remove the two functions + the defaulted
parameter and the tree is identical.

---

## 6. Staged reversible plan (additive first, deletion last)

- **EG1** (this design's slice): generalized `Thm<L, C>` + `from_pure_sym` +
  `nat_add_thm_symbolic` + the never-materialize test. Additive. *Committed
  mechanism.*
- **EG2** (DONE — int/bytes; float blocked): symbolic landers for **int**
  (`int_add_thm_symbolic` / `int_mul` / `int_neg`) and **bytes**
  (`bytes_cat_thm_symbolic` / `bytes_len`) in `covalence-hol-eval::tohol`,
  reusing B1. Additive; **zero base delta; zero new admitted rule** (`CoreEval`
  manifest unchanged at 14 rules; `TermKind` unchanged at 18). See the EG2
  outcome note below.
- **EG3**: add `Zero` to the term enum (replacing reliance on the `Nat(0)`
  literal for the pure nat theory); make `T`/`F` defined constants (coordinate
  with logic-out, `handoff/tohol-purge.md`); `nat_induct` unchanged. Additive
  (`Zero` added while `Nat(0)` still present).
- **EG4** (maintainer-gated, base-TCB Δ): *only if* a real consumer needs
  heterogeneous symbolic collections — implement B2 (`Dyn<Term>` operand + a new,
  audited structural-`eq_mp`-for-`Dyn` base method). This is the recorded next
  wall; do **not** improvise the base method.
- **EG5** (the irreversible bulk deletion, maintainer-gated, **not** this wave):
  delete `TermKind::{Nat, Int, SmallInt, Blob, Bool}`; flip the `Lit` facade to
  the symbolic/defined forms; `core::Term` = textbook HOL Light + `Zero`/`Succ`.
  Everything downstream already routes through `toHOL`/the facade, so this is the
  celebrate-the-shrink change.

**One-way-door note.** EG1–EG3 are additive and revertible. EG4 touches the
innermost TCB and EG5 is irreversible — both are explicitly maintainer-gated and
out of this wave.

---

## 7. EG2 outcome — int / bytes landed, float walled

**Landed** (`covalence-hol-eval::tohol`, additive, zero base delta, zero new
admitted rule): `int_add_thm_symbolic` / `int_mul_thm_symbolic` /
`int_neg_thm_symbolic` (shapes `IntBinEqE` / `IntUnEqE`) and
`bytes_cat_thm_symbolic` / `bytes_len_thm_symbolic` (shapes `BytesCatEqE` /
`BytesLenEqE`, the latter a mixed-sort `ToHolBytes` operand + `ToHolNat`
result). Tests: `tests/int_bytes_symbolic.rs` — a megabyte `bytes.cat` operand
lands with an **O(1)** materialized-`Term` footprint (2 nodes) held natively
under `ToHolBytes`, and every symbolic lander is pinned to a floored concrete
sibling (`int_arith_thm` / `bytes_thm` → `from_pure` → `check_sequent`) as its
well-typedness witness.

**The realization that shaped the implementation.** Unlike `NatAddCert` (which
already concludes the *symbolic* `NatAddEqE`, so `nat_add_thm_symbolic` is a
one-step mint-and-land), the int/bytes **family** certificates
(`IntArithCert` / `BytesCert`) conclude the *concrete* `CoreProp` (`Val<Term>`
with kernel-literal leaves) — they take `(TermSpec, Vec<Lit>)` and produce
heterogeneous per-op results, so they cannot carry a single symbolic `Concl`
type. The symbolic landers therefore mint the existing sound family
certificate and **transport it backwards** along a proven
`⊢ symbolicE = Val(concrete)` reification equation (built with the existing
`ToHolIntVal` / `ToHolBytesVal` / `ToHolNatVal` reify rules + the shared
`reify_app` HolApp-spine driver, then flipped with `sym`), landing a
`Thm<CoreEval, symbolicE>` via `from_pure_sym`. The transport is **only** the
existing base `eq_mp` / `cong_pair` / `cong_app` / `sym` calculus — B1's "the
laziness *is* the existing algebra," now exercised in the concrete→symbolic
direction. No new admitted rule, no base-TCB change.

**The wall — float.** `f32`/`f64` cannot be landed symbolically under EG2's
zero-new-rule contract. `FloatCert` also concludes concrete `CoreProp` (with
`small_int` bit-pattern leaves), but the backward transport needs a proven
`⊢ toHOL_f64(bits) = Val(⌜bits⌝)` reify equation to relate a `ToHolF64` leaf to
the certificate's operand — and **no `ToHolF32Val` / `ToHolF64Val` reify rule
is admitted** (only `ToHolNatVal` / `ToHolIntVal` / `ToHolBytesVal` exist). So
a float symbolic lander requires a **new admitted rule** — either a
`ToHolFloatVal` reify rule (mirroring the transitional int/bytes ones) or a
dedicated symbolic `FloatAddCert` (mirroring `NatAddCert`). This is a distinct
wall from the EG4 `Dyn`-transport wall (that one is about *heterogeneous
collections* of symbolic theorems; this one is a *missing per-family reify
rule*). Both add to the eval-tier TCB, so both are deferred to a
maintainer-gated stage. Recorded in `crates/kernel/hol/core/src/thm/SKELETONS.md`.

+++
id = "N000Z"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# `covalence-fol` — typed representations over `covalence-pure`

> **Design sketch, not built.** A crate one level above `covalence-pure` providing
> a first-order-logic-with-equality / typed-representation framework. It does not
> mint metatheorems — it *is* (or provides) a context whose `Rule` impls derive the
> predicates below. Companion to [`pure-design.md`](./pure-design.md); the HOL port
> is `hol-kernel-plan.md`. Note: much of the ToHOL / `IsOp`/`IsImpl` role here is now
> subsumed by the relation calculus + `TyRep`-in-base
> ([`base-relcalc-holomega-design.md`](./base-relcalc-holomega-design.md)); the
> `HolCtx<K>` foothold below is the still-live part.

## Simpler first move (preferred): `HolCtx<K>` instead of a FOL layer

The full FOL/typed-representation framework may be too much, too early. A simpler
HOL-native alternative — start here, generalize later:

**`HolCtx<K>`** — HOL parameterized by a context `K` supplying *constants*:

- a constant type `Const`, with `Const → Ty` (each constant's type),
- definitions `Const → Tm<Const2>` (a constant unfolds to a term over other
  constants; **default `Const = Empty` ⇒ plain vanilla HOL**, no constant table),
- reductions `Const → Const2`.

Then **operations are reductions on expression types**: `AddExpr<L, R>` (with `L`,
`R` `Nat` constants) *reduces* to the sum constant — computation falls out of the
reduction relation, no separate `IsOp`/`IsImpl` machinery. `Tm` stays the dumb
locally-nameless enum; `K` says exactly which constants / definitions / reductions
are trusted. HOL-only, smaller, tight TCB. **Recommendation: do `HolCtx<K>` first.**

## The (more general, later) FOL approach

A context `K` assigns **multiple representations** of some abstract type `T` (which
may be just a marker). A representation wrapper — provisional `NatR<T>(T)`, generic
name TBD (`As<Nat, T>` / `Repr<Nat, T>`) — means "interpret this `T` as a natural
number". Predicates are covalence-pure *props* `P` certified in context `K`:

- **`K ⊢ HasTy<NatR<T>, Nat>`** — this `NatR<T>` is a valid natural (for `NatR<i64>`,
  holds only for non-negative values).
- **`K ⊢ EqAt<A, B, Nat>`** — `A`, `B` are equal *as naturals* (equality is
  per-type, not structural — the FOL-with-equality layer).
- **`K ⊢ IsOp<Add, (Nat, Nat), Nat>`** — `Add` is an operation `(Nat,Nat) → Nat`.
- **`K ⊢ IsImpl<Add, F>`** — `F` (a Rust impl) implements `Add`.
- … rules to **deduce applications** — apply an op to typed arguments, getting the
  result with its `HasTy` / `EqAt` facts.

So `K` is "what representations, typings, equalities, operations, and
implementations we trust." The accelerator/observer story becomes trusted
*operations + implementations*, recorded as these predicates.

## Replaces HOL's observers — and eventually HOL constants

The goal is to delete built-in constants and run **pure vanilla HOL**, where `Tm`
is the trivial locally-nameless HOL enum (no constant table). An axiomatized
operation bridges: **`ToHOL(Nat, Tm)`** maps `2 ⟹ S(S(Z))`, **`ToHOL(Bytes, Tm)`**,
etc. The context tells us exactly what we trust (which `ToHOL` axioms, which ops);
`Tm` stays the dumb enum. HOL theoremhood is then a prop over that enum.

## Why a layer above `covalence-pure` (not in it)

- It does **not** mint raw `MThm`s — `FirstOrder` is an ordinary context with
  `Rule` impls; keeps the floor TCB minimal (no speculative generality).
- The pattern (representations + typing + equality + ops + impls) is general, reused
  beyond HOL (e.g. a capability/security context can reuse typed reps).

## Reading the TCB off the context (future)

**Read the TCB off the context type** to *assert it matches a short config script*.
Add a trait (on `K`, or on `MThm`'s `K`) yielding a **serializable `TcbSpec`** — the
trusted capabilities it carries (keys, accelerators, executors, constant-providers)
— diffed against a parsed config file. The `serde` support on `Stmt` (and a future
`TcbSpec`) is a step toward this; the security context especially wants "does this
proof's TCB equal what my deployment trusts?".

## Open naming / shape questions

- Better name for `NatR<T>` — generic `As<τ, T>` vs per-type `NatR<T>`/`BytesR<T>`.
- Whether `HasTy`/`EqAt`/`IsOp`/`IsImpl` are one prop enum or separate prop types.
- How `F` (implementation functor) is represented and how application composes.

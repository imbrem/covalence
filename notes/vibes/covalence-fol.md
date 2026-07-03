# `covalence-fol` — typed representations & operations over `covalence-pure`

> **STATUS: DESIGN SKETCH** for the HOL fan-out (and a reusable general pattern).
> *Not built.* A crate **one level above `covalence-pure`** providing a
> first-order-logic-with-equality / typed-representation framework. It does **not**
> need the raw ability to mint metatheorems — it *is* (or provides) a context,
> e.g. `FirstOrder`, whose `Rule` impls derive the predicates below. Companion to
> [`pure-design.md`](./pure-design.md) and [`hol-kernel-plan.md`] (HOL port).

## Simpler first move (likely preferred): `HolCtx<K>` instead of a FOL layer

The full FOL/typed-representation framework below may be **too much, too early**.
A simpler, HOL-native alternative — start here, generalize later if needed:

**`HolCtx<K>`** — HOL parameterized by a context `K` that supplies *constants*:

- a constant type `Const`, with `Const → Ty` (each constant's type),
- definitions `Const → Tm<Const2>` (a constant unfolds to a term over other
  constants; **default `Const = Empty` ⇒ plain vanilla HOL**, no constant table),
- reductions `Const → Const2`.

Then **operations are reductions on expression types**: e.g. `AddExpr<L, R>`
(with `L`, `R` `Nat` constants) *reduces* to the sum constant — computation falls
out of the reduction relation, with no separate `IsOp`/`IsImpl` machinery. `Tm`
stays the dumb locally-nameless enum; `K` says exactly which constants /
definitions / reductions are trusted.

This is HOL-only, smaller, and keeps the TCB tight. The FOL layer below can be
built *later* (and `HolCtx` re-expressed over it), or skipped entirely if HOL
constants-via-`K` suffice. **Recommendation: do `HolCtx<K>` first.**

## The (more general, later) FOL approach

The core idea: a context assigns *many representations* to an abstract type

A context `K` can assign **multiple representations** of some abstract type `T`
(which may be just a marker). A representation wrapper — provisional name
`NatR<T>(T)`, better generic name TBD (`As<Nat, T>` / `Repr<Nat, T>` / `View<…>`)
— means "interpret this `T` as a natural number".

Predicates (these are covalence-pure *props* `P`, certified in context `K`):

- **`K ⊢ HasTy<NatR<T>, Nat>`** — "this particular `NatR<T>` instance is a valid
  natural number." E.g. for `NatR<i64>` this holds only for non-negative values.
- **`K ⊢ EqAt<A, B, Nat>`** — `A`, `B` (things "trying to be" naturals) are equal
  *as naturals*. (Equality is per-type, not structural — this is the FOL-with-
  equality layer.)
- **`K ⊢ IsOp<Add, (Nat, Nat), Nat>`** — `Add` is an operation `(Nat, Nat) → Nat`.
- **`K ⊢ IsImpl<Add, F>`** — `F` (a functor / Rust impl) implements `Add`.
- … and rules to **deduce applications** — apply an op to typed arguments and get
  the result together with its `HasTy` / `EqAt` facts.

So `K` is exactly "what representations, typings, equalities, operations, and
implementations we trust." The accelerator / observer story becomes: trusted
*operations + implementations*, recorded as these predicates.

## Replaces HOL's observers — and eventually HOL constants

This **replaces the observer mechanism in HOL**, and *eventually* **HOL
constants**: the goal is to delete built-in constants and run **pure vanilla
HOL**, where `Tm` is just the trivial locally-nameless HOL enum (no constant
table baked in). Instead, an appropriately axiomatized operation bridges:

- **`ToHOL(Nat, Tm)`** — maps e.g. `2 ⟹ S(S(Z))`,
- **`ToHOL(Bytes, Tm)`**, etc.

The **context tells us exactly what we trust** (which `ToHOL` axioms, which ops);
`Tm` stays the dumb enum. HOL theoremhood is then a prop over that enum, and the
typed-representation layer feeds it via `ToHOL`.

## Why a layer above `covalence-pure` (not in it)

- It does **not** mint raw `MThm`s — `FirstOrder` is an ordinary context with
  `Rule` impls; it sits on the floor like any other kernel. Keeps the floor TCB
  minimal (no speculative generality added to `covalence-pure`).
- The pattern (representations + typing + equality + ops + impls) is **general**,
  reused beyond HOL (e.g. the capability/security context can reuse typed reps).

## Reading the TCB off the context (future, both apps)

A separate, broadly-useful need: **read the TCB off the context type** so you can
*assert it matches a short config script*. Eventually add a trait (on the context
`K`, or on `MThm`'s `K`) yielding a **serializable `TcbSpec`** — the trusted
capabilities it carries (keys, accelerators, executors, constant-providers, …) —
which you diff against a parsed config file. The `serde` support now on `Stmt`
(and a future `TcbSpec`) is a step toward this; it's the verification the security
context especially wants ("does this proof's TCB equal what my deployment trusts?").
Not built — note the shape.

## Open naming / shape questions (decide on the fan-out)

- Better name for `NatR<T>` — generic `As<τ, T>` vs per-type `NatR<T>`/`BytesR<T>`.
- Whether `HasTy`/`EqAt`/`IsOp`/`IsImpl` are one prop enum or separate prop types.
- How `F` (implementation functor) is represented and how application composes.

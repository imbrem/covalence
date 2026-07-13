# Type hierarchy sketch

> Design sketch for the `defs/` catalogue and equality levels. See
> [`kernel-design.md`](./kernel-design.md) for the kernel rules over these types,
> and the authoring-layer sketches [`../surface/surface-syntax.md`](../surface/surface-syntax.md)
> (declaring/defining types — "spec" there is a *logical* spec, distinct from the
> `TypeSpec`/`TermSpec` handles here) and [`../logics/metatheory.md`](../logics/metatheory.md)
> (theories that introduce new types).

## Equality

Four levels:

- **Pointer equality** — preserved by `.clone()`.
- **Structural equality** — preserved by immutability; the Rust `==` operator
  (checks pointer equality first as an optimization).
- **Checked equality** — `checked_eq(lhs, rhs, strat: Strategy) -> bool`, where
  `Strategy` is an *untrusted* trait users may implement (structural equality =
  the null strategy `()`). Today `Strategy` only enables reductions/unfoldings via
  a flag; later it grows callbacks/hooks. Includes kernel *constant* reductions
  (`1 + 1 = 2`, but *not* `0 + x = x`) and unfolding of `DEFINE` definitions.
- **Derived equality** — our propositional equality; need not be universally true.

Checked equality is *sort of like* defeq — but not necessarily decidable, just
*universally* true or false: it can't hold under an assumption, it must always be
true or false (like `1 + 1 = 2`), on pain of inconsistency. A thesis of this
project: **decidability and universality are separate axes** that systems confuse.
Types have derived equality == checked equality.

## Term/type formers: `TypeSpec` and `TermSpec`

- **TypeSpec** `(name, ty, tm)` — a type former `(def, args)`, "definition `def`
  at `args`". `tm : ty -> bool`. Always valid: represents
  `{x : ty | tm x ∨ x = ε tm}`, i.e. `tm x` when `∃x. tm x`, else opaque garbage.
- **TermSpec** `(name, ty, tm)` — a term former. `tm : ty -> bool`, unfolds to
  `ε tm` (`ε` is a separate, anonymous term former).

Both are templates over a symbol `S : Symbol` (a trait anyone can implement,
provided for `SmolStr` and friends):

```rust
struct TypeSpec<S> { symbol: S, ty: Option<Type>, tm: Option<Term> }
struct TermSpec<S> { symbol: S, ty: Option<Type>, tm: Option<Term> }
```

A symbol has an **opacity** — a *constant* at the Rust level (don't trust the impl):

- **Transparent** — unfoldable in structural equality; two specs are equal if they
  have equal definitions, *ignoring* the symbol (we don't trust symbol `==` to be
  non-flaky, and want term `==` to obey the Rust rules). A future sealed
  "trusted-equality" trait (`String` etc.) could short-circuit without pointer eq.
- **Opaque** — unfoldable only in checked equality; a checked-equality function
  compares symbols (per the `Symbol` trait) and definitions. Opaque symbols are
  structurally equal only when pointer-equal.

**Erased** typespec/termspec — `ty`, or both `ty` and `tm`, deleted — can only be
compared by pointer equality (throw away the `Thm` about `abs`/`rep` and you can't
re-derive anything). Complex; leave out of MVP but don't foreclose them. This is
separate from the observer mechanism (which creates opaque types *sans* definition).

Type arguments need more thought — follow existing codebase + Isabelle/HOL
conventions when in doubt.

## Types

### Primitive type formers

- Pure stuff
- `unit` (singleton)
- `bool` (HOL boolean)
- `fn 'a 'b` (function type)
- `nat` (primitive 0/succ + induction, not the `ind` dance)

### Derived core types (semi-trusted)

Needed in *core* to specify primitive operations (e.g. `intAdd a b` reduces for
`int` literals). Semi-trusted: in a separate module (can't forge proofs) but must
be **correct** — connected to computation, so a wrong definition is unsound. Each
is a canonical lazy-static TypeSpec, in English notation:

- `def name args := ty` for `tm = λ. true` (write `any := λ. true`)
- `def name args := ty where pred` for `tm = pred`
- `def name args := { car } close pred` (opaque): `pred : rel car car`,
  `ty = car -> bool`,
  `tm = λS. forall (λx y. pred x y -> S x -> S y) ∧ exists (λx. S x)`
- `def name args := car quot pred` ⟹ `{ car } close (λx y. pred x y ∨ pred y x)`

Write `let` instead of `def` when non-opaque. The symbol is a non-exhaustive enum
`Canonical` implementing `Symbol` (display "name"), separating it from the user
namespace. If no args, also make a canonical lazy-static `Type` constant.
`def factory[template] args := …` means a kernel function returning a `TypeSpec`
with symbol `factory`. Different definitions may share symbols (we check `ty`/`tm`
too). `length`, `map`, etc. are the obvious definitions.

The catalogue:

- `set 'a := 'a -> bool`
- `rel 'a 'b := 'a -> 'b -> bool`
- `preord 'a := rel 'a 'a where (transitivity, reflexivity)`
- `pord 'a := … (transitivity, reflexivity, antisymmetry)`
- `per 'a := … (transitivity, symmetry)`; `part 'a := … (…, reflexivity)`
- `coprod 'a 'b := rel 'a 'b where (λR. (∃a. R = λx _. x = a) ∨ (∃b. R = λ_ y. y = b))`
- `prod 'a 'b := rel 'a 'b where (λR. ∃a b. R = λx y. x = a ∧ y = b)`
- `unit := prod` (empty product)
- `u1 := coprod unit unit` (bit); `u2 := coprod bit bit`; … `u{2N} := coprod uN uN`
  up through 2^64 bits (lazy-static array, variant `Bits(u64)`)
- `f2 := u1`, `f{N+1} := coprod f{N} unit` for 3..256 (variant `Fin(u64)`)
- `option 'a := coprod 'a unit`
- `stream 'a := (nat -> 'a)`
- `list 'a := stream (option 'a) where (…finite-prefix predicate…)`
- `result 'a 'b := coprod 'a 'b` (fills out the WASM component model)
- `bits := list bool`; `blob := list u8`
- `signed1 'a := prod bit 'a` (a or -a); `signed2 'a := prod bit 'a` (a or -(a+1))
- `int := quot (nat × nat)` — Grothendieck: `(a,b)` is `a − b`,
  `(a,b) ~ (c,d) ⟺ a + d = c + b`. (Chosen over `signed2 nat` so every integer op
  is a clean equational definition on representatives; `signed1`/`signed2` stay as
  general two's-complement wrappers.)
- `fieldOfFractions[mul, zero] 'a := prod 'a 'a quot (standard quotient)`
- `rat := fieldOfFractions[mul, zero] int` — `quot (int × int)` by
  cross-multiplication (with a nonzero-denominator carve)
- `real := { rat } close (ratLe)` — Dedekind cuts
- `f32 := u32`; `f64 := u64`

## Primitive term formers

Literals + the standard HOL formers + the observer mechanism. Constants like
`natAdd` are *not* primitive term formers — they are lazy statics (the usual
definitions) that the reduction mechanism recognizes by pointer equality.

- `Nat(Nat)`, `Int(Int)`, `Blob(Bytes)` literals
- `List(TermList, Ty)`, `Set(TermSet, Ty)` — opaque wrappers around
  `Arc<Vec<Term>>` / `Arc<BTreeSet<Term>>`, replaceable later
- `U8…U512` — store U256+ behind an `Arc` (encapsulated via a private
  `InternalTerm` → public `TermKind` mapping so the representation can change)
- `F32`, `F64` — a `u32`/`u64`, bitwise; only casts to/from `u32`/`u64` for now
  (later: float ops axiomatized with `real`)

Builtin computation wanted for:

- `natAdd`/`natMul`/`natLe`/`natLt`/`natPow`/`shl`/`shr`/`and`/`or`/`xor`,
  LE/BE bytes conversions, `abs`, `sgn`, nat→int casts — likewise `int`. *Not*
  `rat` yet (no representation).
- `cat`/`length`/`map`/`filter`/`foldl`/`foldr`/`index`/`take`/`skip`/`repeat n`
  for lists and blobs. (Future: untrusted `stream 'a` / `future 'a` as primitives,
  inspected by consuming *once* — value + "ashes" via a monotonic opaque counter.)
- `union`/`intersection`/`difference`/`subset`/`card` for sets, `toSet` for lists
  (but *not* `toList` — no canonical order). Sets = the infinite type, so `card`
  needs an infinite-set convention via ε (`card 0` or unspecified).

Each is a submodule adding an API to `thm`:

```
crates/kernel/hol/core/src/
    defs/   (semi-trusted)   mod.rs, nat.rs, int.rs, …
    thm/    (trusted)        mod.rs, nat.rs (imports defs, implements reduction), …
```

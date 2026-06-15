# Type Hierarchy Sketch

> See also [`kernel-design.md`](./kernel-design.md) for the kernel rules
> operating on these types, and the authoring-layer sketches:
> [`surface-syntax.md`](./surface-syntax.md) (how types are declared and
> defined — note "spec" there is a *logical* spec, distinct from the
> `TypeSpec`/`TermSpec` handles here) and [`metatheory.md`](./metatheory.md)
> (theories that introduce new types).

## Equality Concept


_Four_ levels of equality:

- Pointer equality, ==>

- Structural equality, ==>

- Checked equality, ==>

- Derived equality

Checked equality looks like:

- `checked_eq(lhs, rhs, strat : Strategy) -> bool`
    where `Strategy` is an _untrusted_ trait which can be implemented by the user
    -- structural equality is just checked equality for the null strategy `()`.

    Right now strategy doesn't do anything except enable reductions and unfoldings via a boolean flag
    -- later it will provide callbacks / hooks / etc.

It's _sort of like defeq_ -- except not necessarily decidable _either_, just _universally_ true or false
-- i.e. it can't be under an assumption, it has to _always_ be true or false, like 1 + 1 = 2, 
on pain of the system being inconsistent.

Whereas derived equality is then our version of propositional equality
--
this one doesn't have to be univerally true.

One of the theses of this project is that decidability and universality are _separate_ axes that systems confuse
--
mixing the former with the latter!

_Types_ have derived equality == checked equality

Preservation:

- Pointer equality is preserved by `.clone()`

- Structural equality is preserved by immutability -- this is the "==" operator in Rust.

  Can check pointer equality first as an optimization -- usually do automatically in "==" impls!

- Checked equality is more fallible; includes:

    - Kernel _constant_ reductions like `1 + 1 = 2` (but *not* `0 + x = x`)

    - _Unfolding_ of definitions like `(DEFINE )`

_Term formers_ and _type formers_ extended with:

- TypeSpec: (name, ty, tm) -- type former of form (def, args), meaning "definition `def` instantiated w/ args `args`"

  Here `tm : ty -> bool`
  --
  this is *always* valid, since it represents
  `{x : ty | tm x \lor x = \epsilon tm}`
  which is true iff:

  - `\exists x : ty . tm x` and `tm x` _or_

  - `\lnot \exists x : ty . tm x` and `x` is some particular, opaque garbage value

- TermSpec: (name, ty, tm) -- term former of form (def, args), meaning "definition `def` instantiated at type `ty`"

  Here `tm : ty -> bool`
  --
  this can be _unfolded_ to `\epsilon tm`,
  which is a separate term former: `\epsilon` is *anonymous*.

We want this to be a _template_

```rust
struct TypeSpec<S> {
    symbol : S,
    ty : Option<Type>,
    tm : Option<Term>
}
```

```rust
struct TermSpec<S> {
    symbol : S,
    ty : Option<Type>,
    tm : Option<Term>
}
```

which implements a sealed trait whenever `S : Symbol` 
-- where `S : Symbol` is some trait anyone can implement which is implemented for `SmolStr` and friends.

A symbol should have an _opacity_, which should be a _constant_ (at the Rust level -- again, don't trust the impl!)

- transparent symbols can be unfolded in structural equality
  -- so two typespecs/termspecs are equal if they have equal definitions

  in particular, we _ignore_ the symbol
  --
  that's because we don't trust the `==` implementation for symbols to not be flaky,
  and we want `==` for terms to always satisfy the Rust rules.

  Maybe later we can have a sealed trait for things with trusted equality like `String`
  so we can use that to short-circuit structural checks without needing pointer equality?

- opaque symbols can only be unfolded in checked equality
    -- so we have a checked equality function to check:

  - symbols (according to checked equality from the Symbol trait)

  - definitions

  opaque symbols are hence only structurally equal when they're pointer equal.

Then we have _erased_ typespec / termspec
--
where `ty` -- or both `ty` and `tm` -- have been deleted
--
for soundness these can only be compared by pointer equality!

Here, if you throw away your `Thm` about `abs/rep`, 
you can't re-derive anything about that type
-- since you've forgotten the definition!

We need to think a bit harder about how we're going to do type arguments and friends
--
follow the existing codebase conventions and Isabelle/HOL conventions when in doubt, and document,
while we work this out together!

Erased types / terms in particular are complex -- so for MVP we can leave them out,
just don't paint yourself into a corner where you can't add them at all.

This is _separate_ to the observer mechanism
-- which just creates opaque types _sans_ a particular definition.

## Type Concept

We have a very small number of builtin _primitive types_
--
we have a lot more primitive _term formers_, but many of these
-- e.g. nat and int literals
-- are primitive _representations_ for particular derived types

### Primitive Type Formers

The typical Isabelle/HOL primitives:

- Pure stuff

- `unit` (singleton type)

- `bool` (HOL boolean)

- `fn 'a 'b` (function type)

- `nat` (the natural numbers as primitive with 0/succ + the induction principle, rather than doing the `ind` dance)

## Derived Core Types 

We need some derived types in the _core_ 
-- because we'll use these types to _specify_ some of our primitive operations, e.g. `intAdd a b` 
    (which _reduces_ -- checked equality -- for a, b int literals)

These are _semi-trusted_ -- we:

- put them in a separate module, so they can't forge proofs

- but they need to be _correct_, since we're going to connect them to computation, so if they define the wrong thing, we become unsound!

Each is a _canonical_ lazy static TypeSpec written (in English notation -- this just gets translated to the definition):

- `def name args := ty` for `tm  = \lambda . true` -- we write `any := \lambda . true`

- `def name args := ty where pred` for `tm = pred`

- `def name args := { car } close pred` for opaque with: 
    
    - `pred : rel car car`

    - `ty = car -> bool`

    - `tm = \lambda S . forall (\lambda x y . pred x y -> S x -> S y) \and exists (\lambda x . S x)`

    Maybe think of better / more standard notation for this?

- `def name args := car quot pred` ==> `def name args := { car } close (\lambda x y . pred x y \or pred y x)`

The symbol is a non-exhaustive enum `Canonical` implementing `Symbol` with display "name"
--
to separate it from the user namespace.

We write `let` instead of `def` if the definition is *not* opaque.

If no args, we also make a canonical lazy static Type constant

Feel free to adjust the definitions below to be more canonical / elegant / etc 
-- they just need to be the correct things, mostly, unless noted otherwise.

Also -- make sure to correct any typos / errors -- these might be wrong!

Functions like length, map, etc, are the obvious definitions!

If we write `def factory[template] args := ...` 
what this means is a _function_ exposed by the kernel which:

- takes in arguments, and

- returns a `TypeSpec` with the symbol `factory`

Note in particular that _different_ definitions can share symbols
--
this is fine, that's why we check `ty` and `tm` too!

- `def set 'a := 'a -> bool`

- `def rel 'a 'b := 'a -> 'b -> bool`

- `def preord 'a := rel 'a 'a where (transitivity, reflexivity)`

- `def pord 'a := rel 'a 'a where (transitivity, reflexivity, antisymmetry)`

- `def per 'a := rel 'a 'a where (transitivity, symmetry)`

- `def part 'a := rel 'a 'a where (transitivity, symmetry, reflexivity)`

- `def coprod 'a 'b := rel 'a 'b where (\lambda R . (exists a . R = \lambda x _ . x = a) \or (exists b . R = \lambda _ y . y = b))`

- `def prod 'a 'b := rel 'a 'b where (\lambda R . (exists a b . R = \lambda x y . x = a \and y = b))`

- `def unit := prod` (empty product)

- `def u1 := coprod unit unit` -- bit

- `def u2 := coprod bit bit` -- crumb

- `def u4 := coprod crumb crumb` -- nybble

- `def u8 := coprod nybble nybble` -- byte

- `def u16 := coprod u8 u8`

- `def u32 := coprod u16 u16` -- word

- `def u64 := coprod u32 u32` -- dword

- `def u128 := coprod u64 u64` -- qword

- `def u256 := coprod u128 u128` -- yword

- `def u512 := coprod u256 u256` -- zword

- Fill out the rest of the array (going up powers of 2) up to 2^64 bits as a single lazy static
  -- represent as variant `Bits(u64)`

- `def f2 := u1`, `def f{N + 1} := coprod f{N} unit` for 3..256 for an array -- stick unit at the front 2 elements
  -- represent as variant `Fin(u64)`

- `def option 'a := coprod 'a unit`

- `def stream 'a := (nat -> 'a)`

- `def list 'a := stream (option 'a) where (\lambda x . \exists n . \forall i . (i < n -> \exists a . x i = some a) \and (n <= i -> x i  = none))`

- `def result 'a 'b := coprod 'a 'b` -- this fills out the WASM component model!

- `def bits := list bool`

- `def blob := list u8`

- `def signed1 'a := prod bit 'a` (interpret as: a or -a)

- `def signed2 'a := prod bit 'a` (interpret as: a or -(a + 1))

- `def int := quot (nat × nat)` — the Grothendieck construction, where
  `(a, b)` represents `a − b` and `(a, b) ~ (c, d) ⟺ a + d = c + b`.
  (Chosen over `signed2 nat` so every integer op is a clean equational
  definition on representatives — see `docs/roadmap.md`. `signed1`/
  `signed2` remain in the catalogue as general two's-complement-style
  wrappers.)

- `def fieldOfFractions[mul, zero] 'a := prod 'a 'a quot (ye olde standard quotient)`

- `def rat := fieldOfFractions[mul, zero] int` — concretely
  `quot (int × int)` by cross-multiplication `(a, b) ~ (c, d) ⟺
  a·d = c·b` (with the nonzero-denominator carve as a tracked refinement).

- `def real := { rat } close (ratLe)` -- Dedekind cuts

- `def f32 := u32`

- `def f64 := u64`

## Primitive Term Formers

We've now got some primitive term formers -- i.e. literals, along with the standard HOL ones + our "observer" mechanism.

Note we no longer have primitive term formers for constants like `natAdd`, etc
--
instead, they become lazy statics (of the usual definitions!) 
which the reduction mechanism _recognizes_ (by pointer equality!)

- `Nat(Nat)` literals of type `nat`

- `Int(Int)` literals of type `int`

- `Blob(Bytes)` literals of type `blob`

- `List(TermList, Ty)` literals of type `list 'a` for some `'a` (provided)

  -- `TermList` is an opaque wrapper around `Arc<Vec<Term>>` which we can later replace with a more optimal immutable data structure

- `Set(TermSet, Ty)` literals of type `set 'a` for some `'a` (provided)

  -- `TermSet` is an opaque wrapper around `Arc<BTreeSet<Term>>` which we can later replace with a more optimal immutable data structure

- `U8/U16/U32/U64/U128/U256/U512` literals of the appropriate type
  -- 
  we should store U256+ behind an `Arc` to avoid blowing up the enum size,
  but this should be encapsulated
  --
  we should have a private `InternalTerm` enum which maps to the public `TermKind` enum,
  so later we can optimize the representation

- `F32, F64` containing a `u32` and a `u64` in Rust -- these are bitwise.

  _Later_ we'll add floating point ops and axiomatize them with `real`
  --
  now just have the types with only (bitwise) casts to/from u32, u64

Then we want builtin computation for:

- `natAdd`, `natMul`, `natLe`, `natLt`, etc -- likewise for `int`. *Not* `rat` for now -- as we don't have a representation for it!

  We also want `natPow`, `shl`, `shr`, `and`, `or`, `xor`, etc...

  Also: to/from for LE bytes and BE bytes, and `abs`, `sgn`, casts nat -> int, ... 

- `cat`, `length`, `map`, `filter`, `foldl`, `foldr`, `index`, `take`, `skip`, etc. for lists and blobs (as appropriate for the latter)
 
  -- also operations like `repeat n`, etc.

  In the future, we'll want untrusted stream 'a as a primitive
  --
  which we can inspect by consuming *once*, getting the value and leaving behind "ashes" for soundness (given by a monotonic opaque integer counter);
  likewise for untrusted future 'a

- `union`, `intersection`, `difference`, `subset`, `card` for sets -- also toSet for lists (but *not* toList for sets -- no canonical order!)
  -- note sets are the same as the infinite type, so for `card` you need to have a convention for infinite sets via epsilon
  -- say card 0 or card unspecified

So each one of these should be a submodule, adding an extra API to thm.

So we have

covalence-core/ (all TCB)

    src/

        defs/ semi-trusted

            mod.rs
            nat.rs
            int.rs
            ...

        thm/ trusted

            mod.rs
            nat.rs // imports defs, implements reduction
            int.rs // imports defs, implements reduction
            ...

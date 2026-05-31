# Primitive Operations Catalog

This is the source of truth for the kernel's primitive operations
(`PrimOp1`, `PrimOp2`, `Ite`, `Iter`) and their minimal
axiomatization. The architecture spec (§3.4) summarises the
categories; here we list each op with:

- its **type signature** (HOL types),
- the **host-side reduction** semantics the kernel applies when all
  arguments are literals,
- the **minimal axioms** the kernel prelude ships, characterizing the
  op without needing reduction.

The kernel's rewrite/equality machinery has three layers:

- **Axioms (§9).** Irreducible postulates. Reviewed for semantic
  soundness; nothing else justifies them.
- **Reduction rules (§10).** Auto-applied by `kernel.reduce(t)` in a
  fixed, ordered, confluent, terminating list. Justified by
  derivability from the axioms. Includes literal-arg evaluation,
  numeral normalization, identity/zero simplifications, and the
  Ite-on-literal-cond rules.
- **Manual rules (§11).** User-invoked rewrites — recursive
  unfoldings, canonicalisations, cast equations. Same justification
  as reductions but applied only on demand (typically because they'd
  loop otherwise).

The trust surface is exactly the three lists. Reviewing them is the
entire kernel-soundness audit.

> **Conventions.** `α`, `β` are type variables. `→` is the HOL
> function arrow. We use `n`, `m` for `nat` and `i`, `j` for `int`.
> `b` is `bool`. `bs` is `bytes`; `bits` is the type and we name
> values of it `w`. uN/iN range over fixed-width integers.
> `reduce(t)` (§3.4) is the LCF call that triggers host-side
> evaluation of a primop applied to literals.
>
> "Minimal" means *just enough* axioms to uniquely characterize the
> operation up to provable equality. Higher-level theorems
> (commutativity, distributivity, monotonicity) are *derived* in
> user space from the equations below.

---

## 1. Booleans

The kernel ships `True`, `False`, and `Eq` as TermKind cases, plus
the following logical primitives. All have type `bool → bool` (Op1)
or `bool → bool → bool` (Op2).

| Op | Sig | Reduction (on literals) |
|---|---|---|
| `LogicalNot` | `bool → bool` | `Not True → False`; `Not False → True` |
| `LogicalAnd` | `bool → bool → bool` | full 2×2 table |
| `LogicalOr` | `bool → bool → bool` | full 2×2 table |
| `LogicalXor` | `bool → bool → bool` | full 2×2 table |
| `LogicalNand` | `bool → bool → bool` | full 2×2 table |
| `LogicalNor` | `bool → bool → bool` | full 2×2 table |
| `LogicalImp` | `bool → bool → bool` | full 2×2 table |

**No defining axioms.** The domain `bool` has exactly two values, so
each logical op is fully characterised by its (finite) truth table.
The kernel handles those via the reduction rules of §10 — there is
nothing to postulate. Identity simplifications like `And x True →
x` are similarly reduction rules, not axioms.

---

## 2. Ite

`Ite(branch_ty, cond, then, else) : branch_ty`

| Sig | Reduction (on literal cond) |
|---|---|
| `bool → α → α → α` (here `α = branch_ty`) | `Ite ty True a b → a`; `Ite ty False a b → b` |

The `branch_ty` field is carried explicitly so the term is
self-describing for typechecking; without it we'd have to recompute
the type of `then`/`else` every time we look at an `Ite`.

**One axiom:** `Ite ty (Not b) x y = Ite ty b y x` — negating the
condition flips the branches. This is the only Ite fact that isn't
a reduction rule (it doesn't fire on a literal condition; it's used
to canonicalise nested Ites). All other Ite equalities collapse to
reduction-rule applications once `cond` becomes a literal.

---

## 3. Naturals (`nat`)

`nat` is axiomatized by **full Peano** — `peano_distinct` (`0 ≠
succ n`), `peano_inj` (`succ m = succ n → m = n`), and `induct_nat`
(the induction schema). All three are first-class axioms in the
prelude (see §9 for the canonical list). The literal normal form
for `nat` is a numeral: `NatInline 5` (not `succ (succ (succ (succ
(succ 0))))`).

### PrimOp1

| Op | Sig | Reduction |
|---|---|---|
| `NatSucc` | `nat → nat` | `succ (NatInline n) → NatInline (n+1)` (numeral normalization) |
| `NatPred` | `nat → nat` | `pred (NatInline 0) → NatInline 0`; `pred (NatInline n+1) → NatInline n` |

### PrimOp2

All comparisons return `bool`. All arithmetic on `nat` is total
(`NatSub` saturates to `0`; `NatDiv`/`NatMod` by `0` are total but
unspecified — `n div 0 = 0`, `n mod 0 = 0` for definiteness; any
provable property *requires* the divisor to be nonzero).

| Op | Sig | Reduction (on literals) | Identity / zero reductions |
|---|---|---|---|
| `NatAdd` | `nat → nat → nat` | host `+` | `add a 0 → a`; `add 0 a → a` |
| `NatSub` | `nat → nat → nat` | saturating | `sub a 0 → a` |
| `NatMul` | `nat → nat → nat` | host `*` | `mul a 0 → 0`; `mul 0 a → 0`; `mul a 1 → a`; `mul 1 a → a` |
| `NatDiv` | `nat → nat → nat` | host `/` | `div a 1 → a`; `div 0 a → 0` |
| `NatMod` | `nat → nat → nat` | host `%` | `mod a 1 → 0`; `mod 0 a → 0` |
| `NatEq` | `nat → nat → bool` | host `==` | `eq a a → True` |
| `NatLt` | `nat → nat → bool` | host `<` | `lt a 0 → False` |
| `NatLe` | `nat → nat → bool` | host `<=` | `le 0 a → True` |

Recursion equations like `add a (succ b) = succ (add a b)` are
**manual rules** (§11), not reduction rules: applying them
automatically would loop with numeral normalization (`succ N → N+1`
for literal `N` would conflict with `add a (succ b) → succ (add a
b)` which introduces `succ`s).

---

## 4. Integers (`int`)

`int` is characterised as the ordered commutative ring obtained from
`nat × nat` (positive/negative parts mod equality). The prelude
contains:

- `int_of_nat : nat → int` (an injective ring homomorphism).
- Ring axioms (associativity, commutativity, distributivity,
  identities, `IntNeg` as additive inverse).
- An order axiom `IntLt` matches `NatLt` on non-negative values.

### PrimOp1

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `IntNeg` | `int → int` | host `-i` | `neg (neg i) = i`; `neg 0 = 0`; `add i (neg i) = 0` |

### PrimOp2

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `IntAdd` | `int → int → int` | host `+` | ring laws |
| `IntSub` | `int → int → int` | host `-` | `sub i j = add i (neg j)` |
| `IntMul` | `int → int → int` | host `*` | ring laws |
| `IntDiv` | `int → int → int` | host `div` (truncating toward zero) | `div_mod_spec` analogous to `nat`; sign convention pinned by the host implementation |
| `IntMod` | `int → int → int` | host `mod` (sign of dividend) | same |
| `IntEq` | `int → int → bool` | host `==` | reflexive/symmetric/transitive |
| `IntLt` | `int → int → bool` | host `<` | total order axioms; agrees with `NatLt` on `int_of_nat`-images |
| `IntLe` | `int → int → bool` | host `<=` | `le i j = Or (lt i j) (eq i j)` |

---

## 5. Fixed-width integers (`u8`…`u64`, `i8`…`i64`)

Each fixed-width type `T` of bit-width `N` is characterised by an
abstract bijection with `nat` modulo `2^N` (for unsigned) or `int`
modulo `2^N` with two's-complement sign-bit interpretation (for
signed). Concretely the prelude declares for each `T`:

- A pair of casts `T_of_nat : nat → T`, `nat_of_T : T → nat`
  (analogous for `int`), with `T_of_nat (nat_of_T x) = x` and
  `nat_of_T (T_of_nat n) = n mod 2^N`.
- All arithmetic ops on `T` are defined as the composition
  *cast-to-nat-or-int → host-op → cast-back* — which is exactly the
  wrapping semantics the kernel evaluates.

This means **users don't axiomatize each `T_Add` independently** —
they prove properties through the cast equations. The kernel still
*reduces* via the host's native ops for speed; the axioms ensure the
reduction is consistent.

### PrimOp1 (per fixed-width T)

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `T_Not` (unsigned only) | `T → T` | host `!x` (bitwise) | `T_Not x = T_of_nat ((2^N - 1) sub (nat_of_T x))` |
| `T_Of_<S>` (cast from S to T) | `S → T` | host cast | cast-equation determines value uniquely |

### PrimOp2 (per fixed-width T)

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `T_Add` | `T → T → T` | host wrapping `+` | `T_Add x y = T_of_nat ((nat_of_T x) add (nat_of_T y))` |
| `T_Sub` | `T → T → T` | host wrapping `-` | analogous |
| `T_Mul` | `T → T → T` | host wrapping `*` | analogous |
| `T_Div` | `T → T → T` | host `/` (defined on `y ≠ 0`) | via cast-spec |
| `T_Mod` | `T → T → T` | host `%` | via cast-spec |
| `T_Eq`/`T_Lt`/`T_Le` | `T → T → bool` | host comparisons | agree with `nat`/`int` analogs through the casts |
| `T_And`/`T_Or`/`T_Xor` | `T → T → T` | bitwise | defined via `bits` representation: `T_And x y = T_of_bits (BitsAnd (bits_of_T x) (bits_of_T y))` (likewise Or/Xor) |
| `T_Shl`/`T_Shr` | `T → T → T` | wrapping shift | defined via `nat` multiplication / division by `2^k` modulo `2^N` |

---

## 6. Bits (`bits`)

`bits` is the free monoid over `bool`. The prelude axiomatizes it via
its length and cons equations: any `bits` value is either empty or
the result of prepending a `bool` to a shorter `bits`.

### PrimOp1

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `BitsLen` | `bits → nat` | host length | `len empty = 0`; `len (cons b w) = succ (len w)` |
| `BitsIsEmpty` | `bits → bool` | host `is_empty` | `is_empty empty = True`; `is_empty (cons _ _) = False` |
| `BitsToBytes` | `bits → bytes` | host pack (only when `len mod 8 = 0`) | requires `len bs mod 8 = 0`; defined as packing 8 bits per byte little-endian |

### PrimOp2

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `BitsConcat` | `bits → bits → bits` | host `++` | `concat empty w = w`; `concat (cons b w) v = cons b (concat w v)` |
| `BitsCons` | `bool → bits → bits` | host prepend | `cons` is the constructor — no further equations |
| `BitsIndex` | `bits → nat → bool` | host index (out-of-range pinned to `False`) | `index (cons b w) 0 = b`; `index (cons _ w) (succ i) = index w i`; `index empty _ = False` |
| `BitsEq` | `bits → bits → bool` | host `==` | extensional: `eq w v = True ↔ len w = len v ∧ ∀ i, index w i = index v i` |

---

## 7. Bytes (`bytes`)

`bytes` is the free monoid over `u8` with a bijection to a packed
`bits` representation (8 bits per byte, little-endian inside each
byte).

### PrimOp1

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `BytesLen` | `bytes → nat` | host length | `len empty = 0`; `len (cons b bs) = succ (len bs)` |
| `BytesIsEmpty` | `bytes → bool` | host `is_empty` | `is_empty empty = True`; `is_empty (cons _ _) = False` |
| `BytesHead` | `bytes → u8` | host head (undefined on empty) | `head (cons b _) = b` |
| `BytesTail` | `bytes → bytes` | host tail | `tail (cons _ bs) = bs`; `tail empty = empty` (pinned) |
| `BytesToBits` | `bytes → bits` | host expand | `BytesToBits bs` is the unique `w` of length `8 * len bs` such that for each `i`, `index w i = bit_i_of_byte_(bs[i / 8])` |

### PrimOp2

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `BytesConcat` | `bytes → bytes → bytes` | host `++` | `concat empty bs = bs`; `concat (cons b a) c = cons b (concat a c)` |
| `BytesCons` | `u8 → bytes → bytes` | host prepend | constructor — no further axioms |
| `BytesIndex` | `bytes → nat → u8` | host index (out-of-range pinned to `0`) | `index (cons b _) 0 = b`; `index (cons _ bs) (succ i) = index bs i`; `index empty _ = 0` |
| `BytesEq` | `bytes → bytes → bool` | host `==` | extensional, like `BitsEq` |

---

## 8. Casts (overview)

Casts live in `PrimOp1`. Each is characterized by its underlying
mathematical function:

| Family | Examples | Defining axiom shape |
|---|---|---|
| **Width ↔ width (unsigned)** | `U8_Of_U16`, `U32_Of_U64`, etc. | truncate-mod-2^N or zero-extend |
| **Width ↔ width (signed)** | `I8_Of_I16`, `I64_Of_I32` | truncate or sign-extend |
| **Signed ↔ unsigned** | `U32_Of_I32`, `I32_Of_U32` | two's-complement reinterpretation |
| **Nat ↔ Int** | `NatToInt`, `IntToNat` | `IntToNat i = if 0 ≤ i then …unique nat… else 0` |
| **uN ↔ Nat** | `Nat_Of_U64`, `U64_Of_Nat` | `U64_Of_Nat n = n mod 2^64` |
| **iN ↔ Int** | `Int_Of_I64`, `I64_Of_Int` | `I64_Of_Int i = i mod 2^64` (two's-complement reinterpretation) |
| **Bits ↔ Bytes** | `BytesToBits`, `BitsToBytes` | listed in §6/§7 |

For each cast, the prelude declares the equation and (where the cast
is bijective on its image) the inverse. Defining via *equations*
rather than algorithms means user-space proofs about casts don't
have to walk the host implementation.

---

## 8.5. Epsilon (Hilbert choice)

The kernel ships Hilbert's choice operator as a first-class
primitive. Given any predicate, ε picks *some* element satisfying
it — and if none exists, picks an arbitrary element of the type.

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `Eps(α, P)` | `(α → bool) → α` | none | `select_ax`: `∀ P x. P x → P (Eps α P)` |

### Storage shape

`Eps(α, P)` carries a `TypeRef` + a `TermRef` = 8 bytes payload —
fits inline in the 3-u32 invariant.

### Role in the bootstrap

`Eps` is the bottom of the foundational stack. It's the only
primitive whose definition cannot be reduced to anything more
elementary — it's a postulated choice function, and `select_ax` is
the only axiom characterising it. Everything else uses `Eps` as a
building block:

- **Induction over `nat`** is derived from Peano's `(0 ≠ succ,
  succ-injective)` + `select_ax`: given a predicate failing
  somewhere, `Eps` picks a counterexample; minimality follows from
  well-foundedness. (Derived in the prelude, used once, never
  re-derived.)
- **Definite description**: `the_one P` is `Eps α P` when `P`
  uniquely determines its element. Used to derive partial functions.
- **Existence elimination**: from `∃x. P x`, take `w = Eps α P` and
  use `select_ax` to conclude `P w`.

## 8.6. Combinators: `Id`, `Comp`, `Iter`

The kernel ships three polymorphic combinators for **pointless**
(point-free) programming. Their utility is twofold: they let us
state primop axioms equationally without dragging around bound
variables, and they let the kernel pattern-match common shapes (e.g.
`Comp(f, g)` applied to literal data) for cheap reduction.

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `Id(α)` | `α → α` | none — `Id` is a value, not an evaluator | `Comb(Id(α), x) = x` |
| `Comp(f, g)` | `(β → γ) → (α → β) → (α → γ)` | none on `Comp` itself; `Comb(Comp(f, g), x)` reduces to `Comb(f, Comb(g, x))` | the previous equation; equivalently `Comp(f, g) = λx. f (g x)` |
| `Iter(α, n, f)` | `nat → (α → α) → (α → α)` | none on `Iter`; equality to `Id`/`Comp` chains via the axioms below | see below |

### Storage shape

- `Id(α)` carries a single `TypeRef` — 4 bytes payload, fits in the
  3-u32 invariant.
- `Comp(f, g)` carries two `TermRef`s — 8 bytes, fits inline.
- `Iter(α, n, f)` has a `TypeRef` + two `TermRef`s = 12 bytes
  payload — doesn't fit. Side-tabled in `arena.iters: Vec<(TypeRef,
  TermRef, TermRef)>` with a single-u32 `IterId` in TermDef.

### `Iter` axioms (via `Comp`/`Id`)

`Iter` is characterised by two equations that **both** hold (they
are provably equal given the equational theory of `Comp`):

```
Iter(α, 0,        f) = Id(α)
Iter(α, succ(n),  f) = Comp(f, Iter(α, n, f))      -- outer-first
Iter(α, succ(n),  f) = Comp(Iter(α, n, f), f)      -- inner-first
```

Combined with the nat-induction axiom (§8.6), these uniquely
characterise `Iter`. The two `succ`-cases together with induction
also prove `Iter`'s key shift-invariance lemma —
`Comp(f, Iter(α, n, f)) = Comp(Iter(α, n, f), f)` — without further
axioms.

### Arithmetic derived from `Iter`

With `Iter` in hand, the standard arithmetic ops are *derived*
(not axiomatized independently — though we *also* expose them as
primops for efficient host-side reduction; see §3 above):

- `add n m = Comb(Iter(nat, m, NatSucc), n)` — `m` successors
  applied to `n`.
- `mul n m = Comb(Iter(nat, m, NatAdd n), 0)`.
- `pow n m = Comb(Iter(nat, m, NatMul n), 1)`.

The defining axiom of `add`'s primop (`add n 0 = n`; `add n (succ
m) = succ (add n m)`) is then *redundant* with the `Iter` characterization
plus the host's reduction — but we keep the equation around because
(a) it's the natural way to symbolically rewrite `add(?a, 0)` to `?a`
without unfolding to `Iter`, and (b) it's the spec the host
implementation is audited against. Same story for `mul`, `pow`, etc.

### Trust note

`Id`, `Comp`, and `Iter` collectively add three kernel-trusted
combinators. Their soundness is one-paragraph: `Id` is the identity
function (by its single equation); `Comp` is the lambda above (by
unfolding); `Iter` is the function-power-iteration combinator
defined by recursion on `nat` (by the two cases + induction).
Auditable mechanically.

## 8.7. Induction principles

The prelude ships a first-class induction axiom for each kernel
primitive inductive type. These are HOL theorems (Props in the root
Context), not primops — they appear in TermDef only as `Const(name,
ty)` referring to the prelude.

### `nat`

```
induct_nat
  : ∀ P : nat → bool.
      P 0 →
      (∀ n : nat. P n → P (succ n)) →
      ∀ n : nat. P n
```

This is the *only* nat axiom needed beyond the Peano pair (`0 ≠
succ n`, `succ-injective`); everything else — uniqueness of `Iter`,
strong induction, well-foundedness — is derived.

### `bits`

```
induct_bits
  : ∀ P : bits → bool.
      P empty →
      (∀ b : bool. ∀ w : bits. P w → P (cons b w)) →
      ∀ w : bits. P w
```

### `bytes`

```
induct_bytes
  : ∀ P : bytes → bool.
      P empty →
      (∀ b : u8. ∀ bs : bytes. P bs → P (cons b bs)) →
      ∀ bs : bytes. P bs
```

### `int`

`int` is induction-free in the prelude — it's specified as the
ordered commutative ring obtained from `nat × nat`, with the lift
`int_of_nat`. Induction over `int` is *derived* (split on sign,
induct over magnitude in `nat`). The prelude exposes the standard
ring + order axioms instead of an induction axiom directly.

### Fixed-width

`uN`/`iN` types are induction-free likewise — they're characterised
by their bijection with `nat / 2^N` (or `int / 2^N`). Any
case-splitting on a `u8` is derived by the user enumerating its
256 values via `induct_nat` on the magnitude.

### Why first-class?

We could in principle *axiomatize each iter rule* and derive
induction from it (the standard HOL approach), or *axiomatize
induction* and characterise iter as the unique function satisfying
the two equations of §8.5. We do the latter because:

- The induction principle is the natural "audit unit" — it's the
  thing mathematicians recognize and that other systems (Coq, HOL
  Light, Isabelle) export.
- It's the thing soundness translations care about — lifting `nat`
  into an object logic means lifting `induct_nat`.
- It's strictly more expressive than the iter rules alone; once you
  have induction you can re-derive iter-uniqueness, well-foundedness,
  primitive recursion, etc.

The two iter rules are still in the prelude (§8.5) — but their role
is *specifying iter's behavior*, not *generating it*. The
generator is `induct_nat`.

---

## 9. Complete axiom list

This section is the **canonical list** of every axiom shipped in the
kernel prelude. Each entry names the axiom, gives its statement, and
links back to the section that motivates it. Audit cost is exactly
"review this list" — there is nothing else in the kernel's trusted
axiom set.

What's *not* here: equational defining rules like `add a 0 = a` or
`Not True = False`. Those collapse to reduction (§10) or manual
(§11) rules; their soundness is part of the rule-list audit, not
the axiom-list audit.

### 9.1. Equality, functions, and bool

| Name | Statement | Source |
|---|---|---|
| `eq_refl` | `∀ x : α. x = x` | builtin Eq |
| `eq_subst` | `x = y → P x → P y` (Leibniz) | builtin Eq |
| `eq_ext` (functional ext) | `(∀ x. f x = g x) → f = g` | builtin Eq |
| `eta_ax` | `(λ x. f x) = f` when `x ∉ FV(f)` | binder primitive |
| `bool_distinct` | `True ≠ False` | Boolean primitive |
| `bool_cases` | `∀ b : bool. b = True ∨ b = False` | Boolean primitive |

Logical ops (`Not`, `And`, `Or`, `Xor`, `Nand`, `Nor`, `Imp`) have
**no defining axioms** — they're fully characterised by their finite
truth tables, which live in the reduction rules of §10. Equivalences
like `xor_def` etc. are reduction rules (left-to-right normal form).

### 9.2. Ite

| Name | Statement | Source |
|---|---|---|
| `ite_negate` | `Ite ty (Not b) x y = Ite ty b y x` | §2 |

Reduction on literal cond (`Ite ty True a b → a`, etc.) is in §10 —
it's a fact of `bool`'s finite structure plus the typing of `Ite`,
not a separate postulate.

### 9.3. Epsilon (Hilbert choice)

| Name | Statement | Source |
|---|---|---|
| `select_ax` | `∀ P x. P x → P (Eps α P)` | §8.5 |

The *only* axiom about `Eps`. Everything else (definite description,
existence elimination) derives from it.

### 9.4. Combinators

| Name | Statement | Source |
|---|---|---|
| `id_ax` | `Comb (Id α) x = x` | §8.6 |
| `comp_def` | `Comb (Comp f g) x = Comb f (Comb g x)` | §8.6 |
| `iter_zero` | `Iter α 0 f = Id α` | §8.6 |
| `iter_succ_outer` | `Iter α (succ n) f = Comp f (Iter α n f)` | §8.6 |
| `iter_succ_inner` | `Iter α (succ n) f = Comp (Iter α n f) f` | §8.6 |

The last two are equivalent given `induct_nat` (§9.5); both are
listed because each is the natural symbolic rule to apply depending
on which side has the literal `succ`. In practice these fire as
**manual rules** (§11), not reductions.

### 9.5. Inductive types: constructors, distinctness, induction

The primitive inductive types ship a constructor pair plus an
induction schema. Arithmetic and comparison primops on these types
are characterised via reduction rules + manual rules — not as
axioms.

**Naturals** (§3):

| Name | Statement |
|---|---|
| `peano_distinct` | `0 ≠ succ n` |
| `peano_inj` | `succ m = succ n → m = n` |
| `induct_nat` | `P 0 → (∀ n. P n → P (succ n)) → ∀ n. P n` |

**Bits** (§6):

| Name | Statement |
|---|---|
| `bits_distinct` | `empty ≠ cons b w` |
| `bits_inj` | `cons b w = cons c v → b = c ∧ w = v` |
| `induct_bits` | `P empty → (∀ b w. P w → P (cons b w)) → ∀ w. P w` |

**Bytes** (§7):

| Name | Statement |
|---|---|
| `bytes_distinct` | `empty ≠ cons b bs` |
| `bytes_inj` | `cons b bs = cons c cs → b = c ∧ bs = cs` |
| `induct_bytes` | `P empty → (∀ b bs. P bs → P (cons b bs)) → ∀ bs. P bs` |

Extensionality lemmas (e.g. `bits_ext`: equal-by-length-and-index)
are derivable from these three plus `eq_ext` — not axiomatised.

### 9.6. Integers (`int`)

`int` is the ordered commutative ring obtained from `nat × nat`;
this is captured by the ring/order axioms together with the
embedding `int_of_nat`. Induction over `int` is **derived** (split
on sign, induct on magnitude in `nat`).

| Name | Statement |
|---|---|
| `int_of_nat_inj` | `int_of_nat n = int_of_nat m → n = m` |
| `int_add_assoc` | `(i + j) + k = i + (j + k)` |
| `int_add_comm` | `i + j = j + i` |
| `int_add_zero` | `i + 0 = i` |
| `int_neg_inv` | `i + (neg i) = 0` |
| `int_mul_assoc` | `(i * j) * k = i * (j * k)` |
| `int_mul_comm` | `i * j = j * i` |
| `int_mul_one` | `i * 1 = i` |
| `int_distrib` | `i * (j + k) = i * j + i * k` |
| `int_lt_trichotomy` | `lt i j ∨ eq i j ∨ lt j i` |
| `int_lt_trans` | `lt i j → lt j k → lt i k` |
| `int_lt_add` | `lt i j → lt (i + k) (j + k)` |
| `int_lt_mul_pos` | `lt 0 k → (lt i j → lt (i * k) (j * k))` |

`sub`/`div`/`mod` are reduction-rule-only: `sub i j → i + (neg j)`
(§10.3), and `div`/`mod` are pinned by the host's Euclidean
division — see §10.1 (literal-arg evaluation) and the manual cast-
equation rules of §11.

### 9.7. Fixed-width integers

Each fixed-width type `T` of width `N` is axiomatized by its
bijection with `nat / 2^N` (unsigned) or `int / 2^N` with
two's-complement reading (signed). Per type:

| Name | Statement |
|---|---|
| `T_of_nat_of_T` | `T_of_nat (nat_of_T x) = x` (round-trip) |
| `nat_of_T_of_nat` | `nat_of_T (T_of_nat n) = n mod 2^N` |
| `T_eq_via_nat` | `T_Eq x y = NatEq (nat_of_T x) (nat_of_T y)` |
| `T_lt_via_nat` | `T_Lt x y = NatLt (nat_of_T x) (nat_of_T y)` |

For signed types, substitute `int_of_T`/`T_of_int` and use the
matching axioms over `int`. Arithmetic ops (`T_Add`, …) and the
bitwise ops are all reduction-rule-only — there is no
`T_Add_via_cast` axiom, just a reduction rule deriving the result
from the host implementation. This keeps the axiom list short and
trusts the cast bijection + host arithmetic.

### 9.8. Summary

The kernel's trusted axiom set is exactly the axioms above:

- 7 logic/equality/bool axioms
- 1 Ite axiom
- 1 epsilon axiom
- 5 combinator axioms
- 3 × 3 = 9 axioms for inductive types (nat / bits / bytes:
  constructors-distinct + injective + induction)
- 13 integer ring/order axioms
- 4 × 16 = 64 fixed-width-bijection axioms (4 axioms × 16 types
  u8..u64,i8..i64; can be a single quantified schema)

**Total: ~100 axiom schemata.** Far less than the previous draft —
the reduction- and manual-rule lists carry the rest. This is a
one-time audit; new primops add to the rule lists, not to this
list, unless they introduce a new postulate.

## 10. Reduction rules (auto-applied by `reduce`)

The kernel's `reduce(t)` primitive walks a **fixed, ordered** list of
directed rewrite rules and applies the first match. The list is
required to be **confluent and terminating** so `reduce` is
deterministic — running it always reaches the same normal form
regardless of where it starts in a term.

A rule like `add a 0 → a` is justified by the prelude axioms (here,
the `iter_zero` + `id_ax` chain proves `add a 0 = a`), but the
rule itself is a kernel facility, not an axiom. The audit unit is
"each rule's LHS = RHS is derivable in the axiom list."

### Order of application

Within a term, `reduce` applies rules bottom-up. Within the rule
list, rules are tried in the order listed below; the first match
wins.

### 10.1. Literal-arg evaluation (highest priority)

For every primop, when **all** value arguments are literals of the
right type, evaluate via the host implementation and emit the
literal result.

- All `Op1`/`Op2` arithmetic: `Op2(NatAdd, NatInline 5, NatInline 3)
  → NatInline 8`, etc.
- Boolean truth tables: `LogicalAnd(True, True) → True`,
  `LogicalNot(False) → True`, all 14 cases for the 7 logical ops.
- Comparisons: `NatLt(NatInline 2, NatInline 3) → True`, etc.
- Casts: `U8_Of_U16(U16 256) → U8 0` (truncation), etc.
- Bytes/bits ops on literal arguments: `BytesLen(BytesStored id) →
  NatInline (host_len(id))`, etc.

### 10.2. Numeral normalization

`nat`, `int`, fixed-width literals all have a canonical
representation (`NatInline n`, `IntInline i`, `U32 n`, etc.).

| Rule | Description |
|---|---|
| `succ(NatInline n) → NatInline (n+1)` | absorb succ into literal |
| `pred(NatInline 0) → NatInline 0` | saturate |
| `pred(NatInline (n+1)) → NatInline n` | absorb pred |
| `IntNeg(IntInline i) → IntInline (-i)` | absorb negation |

### 10.3. Identity / zero / one simplifications

| Rule | Source |
|---|---|
| `add a 0 → a`, `add 0 a → a` | §3 |
| `sub a 0 → a` | §3 |
| `mul a 0 → 0`, `mul 0 a → 0` | §3 |
| `mul a 1 → a`, `mul 1 a → a` | §3 |
| `div a 1 → a`, `div 0 a → 0` | §3 |
| `mod a 1 → 0`, `mod 0 a → 0` | §3 |
| `IntAdd a 0 → a` etc. | §4 |
| `IntMul a 1 → a`, `IntMul a 0 → 0` etc. | §4 |
| Same family for each uN/iN | §5 |

### 10.4. Logical-op identity simplifications

| Rule | Source |
|---|---|
| `And a True → a`, `And True a → a` | §1 |
| `And a False → False`, `And False a → False` | §1 |
| `Or a True → True`, `Or True a → True` | §1 |
| `Or a False → a`, `Or False a → a` | §1 |
| `Not (Not a) → a` (involution) | §1 |
| `Imp a True → True`, `Imp True a → a` | §1 |
| `Imp False a → True` | §1 |
| `Xor a False → a`, `Xor a True → Not a` | §1 |
| Same family for `Nand`, `Nor` (as `Not (And ...)` etc.) | §1 |

### 10.5. Ite on literal cond

| Rule | Source |
|---|---|
| `Ite ty True a b → a` | §2 |
| `Ite ty False a b → b` | §2 |

(The `ite_negate` axiom of §9.2 is *not* a reduction rule — it'd
loop with itself. It's available as a manual rule, §11.)

### 10.6. Combinator reductions

| Rule | Source |
|---|---|
| `Comb (Id α) x → x` | §8.6 |
| `Comb (Comp f g) x → Comb f (Comb g x)` | §8.6 |
| `Iter α (NatInline 0) f → Id α` | §8.6 |

The `succ` cases of `iter_succ_outer`/`iter_succ_inner` are *not*
reductions — they'd unfold indefinitely on a symbolic `n`. Manual
rules only.

### 10.7. Termination + confluence

Each block above is independently terminating. Across blocks, the
ordering (literal-eval → numeral-normalize → identity → logical-
identity → ite → combinator) plus the bottom-up walk gives
confluence. Property test: random terms reach the same normal form
regardless of traversal order.

---

## 11. Manual rules (user-invoked rewrites)

Unlike §10 reductions, **manual rules** are applied only on explicit
user invocation: `kernel.try_rewrite_manual(rule_id, t)`. They are
not required to be terminating or confluent — that's the user's
responsibility to manage.

Manual rules are how the user unfolds recursive definitions one
layer at a time, applies canonicalisations the reduce engine
won't auto-apply, and accesses the equational consequences of
axioms in directed form.

### Examples

```
;; recursion equations (would loop with numeral normalization)
add(?a, succ(?b))  → succ(add(?a, ?b))
mul(?a, succ(?b))  → add(mul(?a, ?b), ?a)
pow(?a, succ(?b))  → mul(pow(?a, ?b), ?a)

;; iter unfolding (would loop on symbolic n)
Iter(?ty, succ(?n), ?f) → Comp ?f (Iter(?ty, ?n, ?f))    ;; outer
Iter(?ty, succ(?n), ?f) → Comp (Iter(?ty, ?n, ?f)) ?f    ;; inner

;; canonicalisations
ite_negate:  Ite(?ty, Not(?b), ?x, ?y) → Ite(?ty, ?b, ?y, ?x)

;; cast equations (when reduction doesn't fire)
T_of_nat(nat_of_T(?x)) → ?x        ;; via cast round-trip
nat_of_T(T_of_nat(?n)) → ?n mod 2^N

;; int reductions defined-via-other-ops
IntSub(?i, ?j) → IntAdd(?i, IntNeg(?j))
```

The full list lives in `crates/covalence-kernel/src/rewrite_manual.rs`
(once Phase 3b lands). Each rule is named for cross-reference from
proof scripts.

### Trust unit

A manual rule is **sound** iff `LHS = RHS` is derivable in the
prelude axioms. The pattern-match/substitute machinery is shared
with `reduce` (§10); only the firing policy differs. Audit cost:
review each rule individually for axiomatic justification.

---

## 12. The Reduce Primitive

`kernel.reduce(t)` recognises a `TermKind` that is either:

- `Op1(op, x)` with `x` a literal of the right type, or
- `Op2(op, x, y)` with both literals, or
- `Ite(_, True, a, _)` / `Ite(_, False, _, b)`.

It computes the result via the host implementation listed above,
allocates the literal result term, and either rewrites `t` in place
to that literal (§4.4) or unions `t`'s canonical with the result's
canonical (§4.3), at the caller's choice. The two paths are
indistinguishable up to UF state — `rewrite` is the in-place form,
`union` allocates a sibling. The kernel may fuse the two when the
allocation is short-lived (§4.4).

If `t` is shaped wrong (non-literal arg, or wrong-type literal),
`reduce` returns an error and the UF is untouched.

---

## 13. Trust Surface Summary

The trust surface added by this primop catalog is:

1. **Each entry in the table is consistent with its axioms.** That
   is, the host implementation of `NatAdd` really does match the
   recursion equations, the wrapping semantics of `U32_Add` really
   does match the modular axiom, etc. This is the kernel's "trusted
   compute" layer; bugs here can produce wrong `Thm`s.

2. **The axiom set is consistent.** All axioms above are derivable
   from a model in `nat × bool` (with `bits` = list of bool, `bytes`
   = list of u8, uN / iN as quotients of `nat` / `int` mod `2^N`,
   etc.). The axioms are small enough to inspect by hand.

3. **Types are static.** The kernel rejects `Op2(NatAdd, x, y)` if
   `x` or `y` doesn't have type `nat`. No ad-hoc polymorphism in the
   primop variants.

Bug-finding strategy:

- Diff each `PrimOpN` variant in `crates/covalence-kernel/src/term.rs`
  against this catalog.
- Property-test `reduce` against the axioms using random literals.
- Cross-check fixed-width op semantics against WASM's `iN` for the
  ops they share (helpful for FFI correctness).

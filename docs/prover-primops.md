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

The kernel's rewrite/equality machinery is split into two layers:

- **Computational rewrites (§11).** When all arguments to a primop
  are literals, the kernel evaluates via host code and emits the
  literal result as an equality. Fast path for concrete arithmetic.
- **Canonical symbolic rewrites (§10).** A small list of macro-defined
  directed rules — these *are* the axioms / characterizations of
  this catalog, just turned into rewrites. Used when an argument
  isn't a literal (`add a 0 = a` for arbitrary `a`), or when the
  caller wants symbolic simplification rather than evaluation.

Together they cover both ends of the spectrum: full host evaluation
on literals, and just-enough symbolic reasoning to unfold a
definition by one layer at a time. The trust surface is exactly:
"the axiom catalog below" + "the macro list."

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

| Op | Sig | Reduction (on literals) | Defining axioms |
|---|---|---|---|
| `LogicalNot` | `bool → bool` | `Not True = False`; `Not False = True` | `Not True = False`, `Not False = True` |
| `LogicalAnd` | `bool → bool → bool` | full table | `And x True = x`, `And x False = False` |
| `LogicalOr` | `bool → bool → bool` | full table | `Or x True = True`, `Or x False = x` |
| `LogicalXor` | `bool → bool → bool` | full table | `Xor x True = Not x`, `Xor x False = x` |
| `LogicalNand` | `bool → bool → bool` | full table | `Nand x y = Not (And x y)` |
| `LogicalNor` | `bool → bool → bool` | full table | `Nor x y = Not (Or x y)` |
| `LogicalImp` | `bool → bool → bool` | full table | `Imp x y = Or (Not x) y` |

The "defining axiom" rows for `And`/`Or` are equational because the
second-argument table is enough together with `True`/`False`
distinctness; `Nand`/`Nor`/`Imp`/`Xor` are derived in terms of
`And`/`Or`/`Not`, so user-space proofs of properties go through the
two base operators.

---

## 2. Ite

`Ite(branch_ty, cond, then, else) : branch_ty`

| Sig | Reduction | Axioms |
|---|---|---|
| `bool → α → α → α` (here `α = branch_ty`) | `Ite ty True a b = a`; `Ite ty False a b = b` | the two reduction rules, plus a typing rule that `cond : bool` and `then, else : branch_ty` |

The `branch_ty` field is carried explicitly so the term is
self-describing for typechecking; without it we'd have to recompute
the type of `then`/`else` every time we look at an `Ite`.

---

## 3. Naturals (`nat`)

`nat` is characterised in the prelude by Peano-minus-induction:
**(P1)** `0 ≠ succ n`, **(P2)** `succ m = succ n → m = n`. Induction
is derived once from these plus Hilbert choice.

### PrimOp1

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `NatSucc` | `nat → nat` | `succ n = n + 1` | introduced via (P2) |
| `NatPred` | `nat → nat` | `pred 0 = 0`; `pred (succ n) = n` | the two equations |

### PrimOp2

All comparisons return `bool`. All arithmetic on `nat` is total
(`NatSub` saturates to `0`; `NatDiv`/`NatMod` by `0` are total but
unspecified — `0 div 0 = 0`, `0 mod 0 = 0` for definiteness; any
provable property *requires* the divisor to be nonzero).

| Op | Sig | Reduction | Recursion / defining axioms |
|---|---|---|---|
| `NatAdd` | `nat → nat → nat` | host `+` | `add n 0 = n`; `add n (succ m) = succ (add n m)` |
| `NatSub` | `nat → nat → nat` | saturating | `sub n 0 = n`; `sub 0 m = 0`; `sub (succ n) (succ m) = sub n m` |
| `NatMul` | `nat → nat → nat` | host `*` | `mul n 0 = 0`; `mul n (succ m) = add (mul n m) n` |
| `NatDiv` | `nat → nat → nat` | host `/` (zero-divisor returns 0) | (characterised via div_mod_spec, below) |
| `NatMod` | `nat → nat → nat` | host `%` (zero-divisor returns 0) | `div_mod_spec`: `n = add (mul (div n d) d) (mod n d)`, with `lt (mod n d) d` for `d ≠ 0` |
| `NatEq` | `nat → nat → bool` | host `==` | `eq n n = True`; `eq 0 (succ _) = False`; `eq (succ n) (succ m) = eq n m` |
| `NatLt` | `nat → nat → bool` | host `<` | `lt n 0 = False`; `lt 0 (succ _) = True`; `lt (succ n) (succ m) = lt n m` |
| `NatLe` | `nat → nat → bool` | host `<=` | `le n m = Or (lt n m) (eq n m)` |

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
kernel prelude. Each entry names the axiom, gives its statement,
and links back to the section that motivates it. Audit cost is
exactly "review this list" — there is nothing else in the kernel's
trusted axiom set.

### 9.1. Logic & equality

| Name | Statement | Source |
|---|---|---|
| `eq_refl` | `∀ x : α. x = x` | builtin Eq |
| `eq_subst` | `x = y → P x → P y` (Leibniz) | builtin Eq |
| `eq_ext` (functional ext) | `(∀ x. f x = g x) → f = g` | builtin Eq |
| `eta_ax` | `(λ x. f x) = f` when `f` doesn't depend on `x` | binder primitive |
| `bool_distinct` | `True ≠ False` | Boolean primitive |
| `bool_cases` | `∀ b : bool. b = True ∨ b = False` | Boolean primitive |
| `not_true` | `Not True = False` | §1 Booleans |
| `not_false` | `Not False = True` | §1 Booleans |
| `and_true` | `And b True = b` | §1 |
| `and_false` | `And b False = False` | §1 |
| `or_true` | `Or b True = True` | §1 |
| `or_false` | `Or b False = b` | §1 |
| `xor_def` | `Xor x y = Not (Eq x y)` | §1 (derived) |
| `nand_def` | `Nand x y = Not (And x y)` | §1 (derived) |
| `nor_def` | `Nor x y = Not (Or x y)` | §1 (derived) |
| `imp_def` | `Imp x y = Or (Not x) y` | §1 (derived) |

### 9.2. Ite

| Name | Statement | Source |
|---|---|---|
| `ite_true` | `Ite ty True a b = a` | §2 |
| `ite_false` | `Ite ty False a b = b` | §2 |

### 9.3. Epsilon (Hilbert choice)

| Name | Statement | Source |
|---|---|---|
| `select_ax` | `∀ P x. P x → P (Eps α P)` | §8.5 |

This is the only axiom about `Eps`.

### 9.4. Combinators

| Name | Statement | Source |
|---|---|---|
| `id_ax` | `Comb (Id α) x = x` | §8.6 |
| `comp_def` | `Comb (Comp f g) x = Comb f (Comb g x)` | §8.6 |
| `iter_zero` | `Iter α 0 f = Id α` | §8.6 |
| `iter_succ_outer` | `Iter α (succ n) f = Comp f (Iter α n f)` | §8.6 |
| `iter_succ_inner` | `Iter α (succ n) f = Comp (Iter α n f) f` | §8.6 |

The last two are equivalent given `induct_nat` (§9.6); both are
shipped because either is the natural symbolic rewrite to apply
depending on which side has the literal `succ`.

### 9.5. Equational definitions of arithmetic primops

These are the "behavior axioms" for the arithmetic primops — the
specs the host implementation is audited against and the rewrites
the macro engine ships (§10 macros).

**Naturals** (§3):

| Name | Statement |
|---|---|
| `nat_pred_zero` | `pred 0 = 0` |
| `nat_pred_succ` | `pred (succ n) = n` |
| `nat_add_zero` | `add n 0 = n` |
| `nat_add_succ` | `add n (succ m) = succ (add n m)` |
| `nat_sub_zero_r` | `sub n 0 = n` |
| `nat_sub_zero_l` | `sub 0 m = 0` |
| `nat_sub_succ` | `sub (succ n) (succ m) = sub n m` |
| `nat_mul_zero` | `mul n 0 = 0` |
| `nat_mul_succ` | `mul n (succ m) = add (mul n m) n` |
| `nat_div_mod_spec` | `n = add (mul (div n d) d) (mod n d) ∧ (d ≠ 0 → lt (mod n d) d)` |
| `nat_eq_refl` | `eq n n = True` |
| `nat_eq_zero_succ` | `eq 0 (succ _) = False` |
| `nat_eq_succ_succ` | `eq (succ n) (succ m) = eq n m` |
| `nat_lt_zero_r` | `lt n 0 = False` |
| `nat_lt_zero_l_succ` | `lt 0 (succ _) = True` |
| `nat_lt_succ_succ` | `lt (succ n) (succ m) = lt n m` |
| `nat_le_def` | `le n m = Or (lt n m) (eq n m)` |

**Integers** (§4):

| Name | Statement |
|---|---|
| `int_of_nat_inj` | `int_of_nat n = int_of_nat m → n = m` |
| `int_add_assoc` | `add (add i j) k = add i (add j k)` |
| `int_add_comm` | `add i j = add j i` |
| `int_add_zero` | `add i 0 = i` |
| `int_neg_add` | `add i (neg i) = 0` |
| `int_mul_assoc` | `mul (mul i j) k = mul i (mul j k)` |
| `int_mul_comm` | `mul i j = mul j i` |
| `int_mul_one` | `mul i 1 = i` |
| `int_distrib` | `mul i (add j k) = add (mul i j) (mul i k)` |
| `int_sub_def` | `sub i j = add i (neg j)` |
| `int_div_mod_spec` | analogous to nat, with sign convention pinned |
| `int_lt_trichotomy` | `lt i j ∨ eq i j ∨ lt j i` |
| `int_lt_trans` | `lt i j → lt j k → lt i k` |
| `int_le_def` | `le i j = Or (lt i j) (eq i j)` |

**Fixed-width** (§5): for each `T ∈ {u8…u64, i8…i64}` and each
op `O ∈ {Add, Sub, Mul, Div, Mod, Lt, Le, Eq, And, Or, Xor, Shl,
Shr}`, an axiom `T_O_via_cast` of the form

```
T_O x y = T_of_nat ( (nat_of_T x) O' (nat_of_T y) )
```

where `O'` is the corresponding `nat`/`int` op modulo `2^N`. (Signed
variants substitute `int_of_T`/`T_of_int`.) Plus the cast round-trips:

| Name | Statement |
|---|---|
| `T_of_nat_of_T` | `T_of_nat (nat_of_T x) = x` |
| `nat_of_T_of_nat` | `nat_of_T (T_of_nat n) = n mod 2^N` |

**Bits** (§6):

| Name | Statement |
|---|---|
| `bits_len_empty` | `len empty = 0` |
| `bits_len_cons` | `len (cons b w) = succ (len w)` |
| `bits_is_empty_empty` | `is_empty empty = True` |
| `bits_is_empty_cons` | `is_empty (cons _ _) = False` |
| `bits_concat_empty` | `concat empty w = w` |
| `bits_concat_cons` | `concat (cons b w) v = cons b (concat w v)` |
| `bits_index_cons_zero` | `index (cons b w) 0 = b` |
| `bits_index_cons_succ` | `index (cons _ w) (succ i) = index w i` |
| `bits_index_empty` | `index empty _ = False` (pinned) |
| `bits_ext` | `(∀ i. lt i (len w) → index w i = index v i) ∧ len w = len v → w = v` |

**Bytes** (§7): analogous to bits, with `cons : u8 → bytes → bytes`
and `head`/`tail`/`index` returning `u8`.

### 9.6. Induction principles

| Name | Statement | Source |
|---|---|---|
| `peano_distinct` | `0 ≠ succ n` | §3 |
| `peano_inj` | `succ m = succ n → m = n` | §3 |
| `induct_nat` | `P 0 → (∀ n. P n → P (succ n)) → ∀ n. P n` | §8.7 |
| `induct_bits` | `P empty → (∀ b w. P w → P (cons b w)) → ∀ w. P w` | §8.7 |
| `induct_bytes` | analogous to bits, over `u8` cons | §8.7 |

### 9.7. Cast definitions

Per §8, every cast `f : S → T` ships its defining equation, e.g.
`U64_of_Nat n = n mod 2^64`, `Nat_of_U64 x = nat_of_T x`,
`BytesToBits bs = …packed bits…` (with `len = 8 * len bs`),
`BitsToBytes w` defined iff `len w mod 8 = 0`. The full list of
casts is mechanical from the type catalog (§3.2 of the architecture
doc).

### 9.8. Summary

The kernel's trusted axiom set is exactly the axioms above. Concrete
count (approximate): ~50 boolean/equality/control axioms +
~25 nat/int axioms + ~15 × (uN/iN) = ~225 fixed-width axioms (or a
single quantified schema per op) + ~12 bits + ~12 bytes + 5 induction
+ ~40 casts ≈ **350 axiom schemata**. This is a one-time audit;
the kernel grows only when a new primop is added, and each
addition is mechanical against the rules in this document.

## 10. Macro-defined symbolic rewrites

The kernel ships a fixed list of **symbolic rewrite macros** that
generate kernel-trusted equalities the user can apply without
host-side computation. These exist alongside the `reduce` machinery
(§11) for two reasons:

1. **Non-literal arguments.** `add a 0 = a` for an arbitrary `a` is a
   *theorem* the kernel can dispatch without an evaluator;
   host-side reduction is only available on literals.
2. **Defining-equations as rewrite rules.** A macro like
   `add(a, succ(b)) → succ(add(a, b))` *is* the recursion equation
   from the axiom list — just turned into a directed rule the kernel
   can apply.

Concretely the kernel exposes:

```rust
fn try_rewrite_macro(arena, term_ref) -> Result<Option<TermRef>, ...>
```

It walks the macro list, attempting to pattern-match the term's
shape against each rule's LHS. If a rule matches, the kernel
constructs the RHS substitution and emits a UF union (or in-place
rewrite, caller's choice — same options as `reduce`).

### Trust surface

The macro list is the **only** thing the user has to audit to trust
the kernel's symbolic rewriter:

- Each macro is a pair `(LHS pattern, RHS template)` where the LHS
  and RHS are HOL term shapes (built from kernel primitives,
  schematic metavariables, and side conditions).
- A macro is **sound** iff its LHS = RHS is derivable in the
  prelude axioms. This is a property of the macro alone, not of the
  rest of the kernel — auditable independently.
- The kernel's macro engine is small (pattern matcher + substitution)
  and shared across all macros.

So instead of axiomatizing each of `add`, `mul`, `pow`, …, the
prelude declares **one** set of soundness-justified macros and the
kernel mechanically applies them on demand. The trust surface
becomes "review the macro list," not "review every axiom."

### Examples

```
;; recursion equations as rewrites
add(?a, 0)         → ?a
add(?a, succ(?b))  → succ(add(?a, ?b))

mul(?a, 0)         → 0
mul(?a, succ(?b))  → add(mul(?a, ?b), ?a)

;; logical identities
Or(?a, False)      → ?a
Or(?a, True)       → True
And(?a, True)      → ?a
And(?a, False)     → False
Not(Not(?a))       → ?a

;; ite reductions on literal conditions
Ite(?ty, True,  ?t, ?e) → ?t
Ite(?ty, False, ?t, ?e) → ?e

;; iter unfolding
Iter(?ty, 0,        ?f, ?x) → ?x
Iter(?ty, succ(?n), ?f, ?x) → ?f (Iter(?ty, ?n, ?f, ?x))
```

(Notation: `?x` is a schematic metavariable; concrete kernel-side
rules use a fixed binder convention.)

### Generation strategy

The macro list is **generated** from the axiom catalog in §1–§7 via
a small build-time procedure:

1. For each defining equation (`add n 0 = n`, etc.) emit the
   left-to-right directed rule.
2. For each "extensional axiom" (e.g. `eq w v = True ↔ structural`)
   skip — those don't shape-direct.
3. For each derived identity the prelude exposes (e.g. logical
   identities), emit if and only if it's derivable from the base
   equations *and* the audit cost is low (one or two steps to
   verify).

Today this is a hand-maintained list. Later it can be generated by
a verifier that takes the axiom catalog as input and emits the
rewrite list as output — eliminating even the manual audit.

---

## 11. The Reduce Primitive

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

## 12. Trust Surface Summary

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

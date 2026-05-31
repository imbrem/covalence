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

- **Computational rewrites (§10).** When all arguments to a primop
  are literals, the kernel evaluates via host code and emits the
  literal result as an equality. Fast path for concrete arithmetic.
- **Canonical symbolic rewrites (§9).** A small list of macro-defined
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

## 8.5. `iter` and the recursion combinator

In addition to the per-type ops above, the kernel ships a single
polymorphic primitive:

| Op | Sig | Reduction | Axioms |
|---|---|---|---|
| `Iter` | `nat → (α → α) → α → α` | `iter ty 0 f x = x`; `iter ty (succ n) f x = f (iter ty n f x)` | the two equations |

This is the bounded fixed-point combinator: `iter n f x` applies `f`
to `x` exactly `n` times. (As a `PrimOpN`, `iter` has 3 children
plus a type argument, so it'd violate the 3-u32 invariant if stored
inline; like `Ite` it lives in a side table — `arena.iters` — with a
single-u32 `IterId` payload in `TermDef`.)

Why it earns a slot: `iter` is the building block from which the
kernel's recursive arithmetic axiomatization is derived. With `iter`
in hand:

- `add n m = iter nat m succ n` — `m` successors applied to `n`.
- `mul n m = iter nat m (add n) 0`.
- `pow n m = iter nat m (mul n) 1`.

Concretely, the **prelude** ships `iter` plus a single Peano-pair
`(zero ≠ succ, succ-injective)` plus Hilbert choice; everything
else — induction, `add`'s commutativity, `mul`'s associativity, etc.
— is derived in user space.

---

## 9. Macro-defined symbolic rewrites

The kernel ships a fixed list of **symbolic rewrite macros** that
generate kernel-trusted equalities the user can apply without
host-side computation. These exist alongside the `reduce` machinery
(§10) for two reasons:

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

## 10. The Reduce Primitive

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

## 10. Trust Surface Summary

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

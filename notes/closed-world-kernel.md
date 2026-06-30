# Closed-world kernel: first-order theories in the type system

**Status:** design sketch (2026-06). Supersedes the opaque-context / `IsThm`
direction in [`pure-design.md`](./pure-design.md) for the kernel layer — and the
unforgeable-certificate idea survives, now as an **equality** certificate
`Eqn<A,B,L>` rather than a generic `MThm`. The *trust surface* is reworked so the
TCB is a **closed, enumerable set of rules** rather than "trust each context's
crate". **Build plan:** rip out `covalence-pure` in place and replace it with this
framework (nothing depends on `covalence-pure` yet, so we have a free hand): the
TCB in `covalence-pure/trusted`, the `language!` macro in `covalence-pure-derive`,
ergonomics in the `covalence-pure` facade.

## Why

The earlier design made soundness rest on **context opacity** (a context value
must be unconstructible outside its crate) — but contexts are *not* meant to be
opaque (they carry public data: hypotheses, axioms, trusted keys). We want a
trust story that:

1. does **not** require opaque contexts;
2. is **closed-world**: the complete set of inferences a theory admits is fixed
   statically and can be **enumerated and diffed against a checked-in manifest**;
3. cleanly **modularizes** the logic — HOL is a theory; Nat/Int/Bytes/Text are
   theories layered on top; WASM/x86 later — each adding *only* its own rules to
   the TCB, and provable-in-HOL stays provable-without-the-extra-TCB.

The structural insight: **key the TCB on a parameter-free trait whose associated
types are coherence-unique.** Then orphan + coherence reserve the impl to the
theory's own crate *and* make it unique, so the rule set is a deterministic
function of the type. No opacity, no orphan tricks on parameterized traits.

## The framework (the trusted meta-kernel)

A typed first-order signature + an equational rewriting calculus. Everything is
values; sorts/typing are tracked at the type level.

### Sorts, ops, expressions

```rust
/// A first-order sort — the "types" the object theory ranges over. Open: any
/// Rust type may name a sort. Asserting `Sort` claims nothing about provability,
/// so free implementation is harmless.
pub trait Sort {}

impl Sort for bool {}                       // propositions are bool-sorted exprs
impl Sort for () {}                          // nullary tuple
impl<A: Sort> Sort for (A,) {}
impl<A: Sort, B: Sort> Sort for (A, B) {}    // … up to a fixed arity
// later: Either, Option, fixed-size arrays, …

/// An operation symbol `In → Out`. May carry data (the impl type's fields).
/// Open: users declare ops. Relations are ops with `Out = bool` (we merge them —
/// see "Props = Expr<bool>").
pub trait Op {
    type In: Sort;
    type Out: Sort;
}
```

Expressions are **type-level**: each shape is a distinct Rust type carrying its
leaf values, with the sort tracked by a **sealed** `Expr<S>` trait. You extend the
*vocabulary* by declaring new `Op`s and using `App` — never by implementing `Expr`
for a new type.

```rust
mod sealed { pub trait Sealed {} }
/// A well-typed expression of sort `S`. SEALED — the only forms are below.
pub trait Expr<S: Sort>: sealed::Sealed {}

/// A Rust value as a leaf expression — the type *is* the sort. (Name TBD: `Val`
/// vs `Const` vs `Lit`.) This is how a raw value *becomes* an expression — the
/// reason a bare `&A` blanket isn't enough on its own.
pub struct Val<C>(pub C);              impl<C: Sort> Expr<C> for Val<C> {}
/// A borrowed *raw value* leaf: same sort, no clone — and the home of pointer-
/// equality (`Eqn` via `TrustedDeref` / address identity) for shared subterms.
pub struct Ref<'a, C>(pub &'a C);      impl<'a, C: Sort> Expr<C> for Ref<'a, C> {}
/// Apply op `F: In → Out` to an argument expression of sort `In`.
pub struct App<F: Op, A>(pub F, pub A); impl<F: Op, A: Expr<F::In>> Expr<F::Out> for App<F, A> {}

// a borrowed *expression* is an expression of the same sort (no move / clone):
impl<'a, S: Sort, A: Expr<S> + ?Sized> Expr<S> for &'a A {}
// dynamic expression: `Expr` is object-safe, and SEALED — so `Box<dyn Expr<S>>`
// (and `&dyn Expr<S>` via the blanket) gives runtime-shaped expressions that are
// still guaranteed genuine, WITHOUT any new trusted surface:
impl<S: Sort> Expr<S> for Box<dyn Expr<S>> {}

// products: tuples / arrays / slices of exprs are exprs of the product sort
impl<X: Sort, Y: Sort, A: Expr<X>, B: Expr<Y>> Expr<(X, Y)> for (A, B) {}
// … n-ary tuples, [A; N], &[A] similarly (sealed impls alongside).
```

Notes:
- The four leaf/ref forms cover the cases cleanly: **`Val`** injects an owned value,
  **`Ref`** borrows a raw value, **`&A`** borrows an existing expression, and
  **`Box<dyn Expr<S>>`** is a dynamic (runtime-shaped) expression. The `dyn` form is
  the escape hatch from heavy monomorphization — and because `Expr` is sealed it
  adds **zero** TCB.
- `Ref`/`&A`/`&[A]`/`dyn` are **non-`'static`, and that's fine** — *expressions* are
  never keyed by `TypeId` (only *rules* are), so borrowing/dynamism in expressions
  costs nothing. We could fold `Ref` into a `Deref` op, but it's a worthwhile base
  case (and carries pointer-equality).
- For `dyn` and `Eqn::trans` to work, `Expr` carries one object-safe, framework-TCB
  operation: a **trusted structural equality** (`Val` via `TrustedEq`, `App` via
  op-identity + recursive arg-eq, products componentwise, `Ref` via pointer-or-deref).
  Audited once in the framework; it is what lets `trans` check two middle terms
  really match. No variables at this layer — HOL adds them below.

**Props = `Expr<bool>`** (relations are just `Op<Out = bool>`); connectives
`and/or/not/imp` are ops `Op<In=(bool,bool), Out=bool>`. Matches HOL (a prop *is* a
`bool` term). "`P` holds" is then an *equality* — see `Eqn`/`Thm` below.

### Trusted equality — the leaf, and how native values enter

```rust
/// Trusted, SOUND-but-partial equality at sort `C`: `teq(a,b) == true` ⟹ `a` and
/// `b` are genuinely equal (so `Eqn<Val(a), Val(b), L>` holds in *any* `L`); it
/// MAY return false for equal values (incompleteness is fine). DISTINCT from
/// `PartialEq` — that one is untrusted (could be semantically wrong); implementing
/// `TrustedEq` is a deliberate TCB claim. This is the seam by which native Rust
/// (or, later, WASM) computation enters: compute in Rust, certify the result equal.
pub trait TrustedEq { fn teq(&self, other: &Self) -> bool; }
```

Same shape as the `admits` contract (`true ⟹ really-equal`, false free) — a sound,
possibly-incomplete decision procedure, audited per type.

### Rules: structure is free, computation is gated

The deep insight that falls out: **the equality calculus is universal and lives in
the framework TCB (ungated); only *computation* is gated by `admits` and appears in
the manifest.**

- **Ungated, framework-level** (sound in *every* language): `refl`, `sym`, `trans`,
  and **congruence** — including `cong_app` under *any* op `F` (`a = b ⟹ F a = F b`
  holds because ops denote functions, whether or not `F`'s evaluation is trusted).
  You can always reason about structure; you just can't *evaluate*.
- **Gated, per-language** (`admits`, in `MANIFEST`): turning an op into its value,
  or applying an axiom. Two kinds of gated rule type (keyed by `TypeId`):
  - a general `Rule<L>` carrying premises/data, concluding an `Eqn`;
  - an **op that is also its own canonical rule** — see below.

There is deliberately **no way to equate ops** (`Eqn<F, G>` does not exist):
congruence rewrites *arguments* only, operators are fixed symbols.

#### Ops that are also rules (`Fv`, `Bv`, `nat.add`, …)

An op can ship a *canonical evaluation*, so the same type is both a symbol you may
write and a computation you may (if admitted) run:

```rust
/// `App<Self, arg>` canonically equals `eval(arg)`. Using it is GATED: the `Eqn`
/// mints only where `L::admits(TypeId::of::<Self>())`. So you may always *write*
/// `App<Fv, tm>` (uninterpreted ⇒ sound by vacuity); you may only *reduce* it to
/// the actual free-variable set where `Fv` is in the TCB.
pub trait CanonRule: Op + 'static {
    fn eval(&self, arg: &impl Expr<Self::In>) -> Val<Self::Out>;
}
```

For HOL this is exactly how the locally-nameless machinery is exposed:
`Fv: Op<In = HolTm, Out = VarSet>` (free variables), `Bv: Op<In = HolTm, Out = Nat>`
(max bound index; *locally closed* ⟺ `Bv(tm) = 0`), `subst`, β, `nat.add`, … —
each a single type that is an `Op` (write it anywhere, free) **and** a `CanonRule`
(evaluate it, only with the op's `TypeId` in your manifest).

### Languages (= theories = rulesets): membership as a function, not a trait

Type-level tuple membership is a coherence dead-end on stable Rust:
`(A1,A2): Contains<A1>` and `Contains<A2>` overlap with no way to disambiguate
(short of a frunk-style index witness we don't want). So **membership is a plain
function over `TypeId`, not a trait** — which is also more honest to the
value-directed kernel (it already checks at runtime), and lets compile times stay
flat regardless of tree size.

```rust
/// A language / theory / ruleset. PARAMETER-FREE on purpose: the only type in
/// `impl Language for Foo` is `Foo` itself, so orphan reserves the impl to
/// `Foo`'s crate and coherence makes it unique ⇒ the admissible-rule set is a
/// fixed function of the type. The VALUE may carry data (hypotheses, axioms,
/// keys). `&self` is for object-safety (`&dyn Language` walks); the rule set is
/// type-determined (impls ignore `self`'s data in `admits`/`extends`).
pub trait Language: 'static {
    /// Membership gate for rule `rule`. **Contract** (3 parts):
    /// - MUST be `true` for every DIRECT rule (so it can be applied here);
    /// - MUST be `false` for any rule NOT in `tree(self)` (soundness floor —
    ///   `admits(r) == true` ⟹ `r ∈ tree(self)`);
    /// - UNSPECIFIED for inherited (indirect) rules — implementor's choice.
    ///   Returning `true` is sound (still in-tree) and lets you apply an
    ///   inherited rule *directly* here; returning `false` requires the
    ///   apply-in-home + `lift` composition.
    /// Usually a flat `match` on `TypeId`s; with a constant `TypeId::of::<Rho>()`
    /// argument, LLVM folds the branch at `-O`.
    fn admits(&self, rule: TypeId) -> bool;

    /// Parent gate. Same 3-part contract: `true` for DIRECT parents, `false` for
    /// non-ancestors (`extends(p) == true` ⟹ `tree(p) ⊆ tree(self)`), free for
    /// indirect ancestors (where `true` enables a direct multi-layer `lift`).
    fn extends(&self, parent: TypeId) -> bool;

    /// **Static** TCB manifest, when the whole subtree is statically known —
    /// `Some` iff every parent is also `Some` (macro-built bottom-up). `None` for
    /// a future dynamic/wrapper language. **Canonical when present**: `tree(L)` is
    /// *defined* by it, and it is the source of truth `admits`/`extends` must not
    /// exceed. Identity is the `TypeId`; **no names** (those are a separate trait).
    const MANIFEST: Option<&'static Manifest>;
}

/// The TCB as raw type identities — `&'static` children so it lives in a `const`.
pub struct Manifest {
    pub ty: TypeId,
    pub extends: &'static [Manifest],     // direct parents' manifests
    pub admits:  &'static [RuleRecord],   // direct rules
    pub metadata: LangMeta,               // extension seam (minimal today)
}

/// A direct-rule entry. `metadata` is the seam for polymorphic rules / `rule@type`
/// (e.g. record the sort a generic rule is instantiated at) — minimal today.
pub struct RuleRecord { pub ty: TypeId, pub metadata: RuleMeta }
```

The trait is *that small*: two gates + one const. **Names and any other
descriptive metadata are a separate, untrusted trait** keyed off `TypeId` (e.g.
`Named { fn name(id: TypeId) -> Option<&'static str> }`), never in the kernel
surface — different consumers can name the same tree differently. A future
`fn manifest(&self) -> OwnedManifest` (object-safe, owned children) is the seam
for *dynamic* languages whose `MANIFEST` is `None`; for those the invariant is
`manifest() ≤ MANIFEST` is vacuous, and `tree(L)` falls back to the runtime walk.
A dynamic *restricting* wrapper (admits a subset of what it wraps) is then a
`MANIFEST = None`, `manifest() = Some(subset)` language — out of MVP scope, but
the shape is reserved.

So `tree(L)` is defined canonically by `MANIFEST` (or the runtime walk when it is
`None`); `admits`/`extends` are a **sound, direct-complete approximation** of
tree-membership with freedom in the middle. The default `language!` expansion
makes them direct-only flat matches (fast, DCE-friendly, false for indirect) and
builds `MANIFEST` from the *same* direct lists, so they can't drift —
multi-layer reach is then **composing one-layer lifts** (value level — see
minting), and the lift chain *is* the theorem's real dependency set. A language
that wants O(1) cross-layer casts may opt its `admits`/`extends` into the
transitive answer; still sound, just a bigger match. Either way each layer's
declaration stays **thin** (a 4-way × 4-deep tree reaches 256 rules with every
node naming ~4 rules + ~4 parents) — linear compile time, no arity wall.

The **macro is pure convenience**: `language! { Hol { rules: [Beta, Eta, …],
inherits: [Eq] } }` expands to the obvious `impl Language for Hol` (a `match` in
`admits`, a `match` in `extends`, and a `const MANIFEST = Some(&Manifest { ty:
TypeId::of::<Hol>(), extends: &[*Eq::MANIFEST.unwrap()...], admits: &[...] })`,
`None` if any parent is dynamic). The nested static tree leans on const-`match` +
promotion — a const-eval wrinkle to get right, but a contained one. Hand-writing
the impl is a short, eyeball-auditable function — no trait machinery, no sealing.

**Non-`'static` rules (future).** `TypeId::of` needs `'static`, which blocks rules
that borrow their arguments. The escape hatch: give `Rule` an associated
identity tag `type Id: 'static` (a marker, e.g. `PhantomData`-style), and key
`admits` on `TypeId::of::<Rho::Id>()`. Then a borrowing `Rho<'a>` shares the
`'static` tag `Rho::Id` and still participates. Deferred, but the `Id`-tag seam
should exist from the start so we don't have to thread it in later.

### The certificate: `Eqn<A, B, L>`

Equality is the *primitive* judgement (HOL-Light style). The certificate is:

```rust
/// `lhs` and `rhs` (expressions of the SAME sort) are equal in language value
/// `lang`. Private fields, no public constructor ⇒ unforgeable; minted only by
/// the equality calculus + admitted rules. The `L` value carries the hypotheses /
/// axioms in scope (so `trans` requires equal `lang`s — same context).
pub struct Eqn<A, B, L> { lhs: A, rhs: B, lang: L, _seal: Private }

/// A propositional theorem `⊢ P` is just equality with `⊤` (P holds ⟺ P = true):
pub type Thm<P, L> = Eqn<P, Val<bool>, L>;   // rhs value is `Val(true)`
```

The gating line is sharp: **pure logical structure is ungated framework TCB; any
step that injects *external* trust (a native equality, an op's evaluation, an
axiom) is gated by `admits` and shows up in the `MANIFEST`.**

**Ungated — the equality calculus** (sound in *every* `L`; `?Sized` so `dyn`/`&`
work). `eq_mp` (from `P` and `P=Q` get `Q`) is *derived* = `sym` + `trans`, so it's
not primitive — there is no separate "`Eq` language":

```rust
impl<S, A: Expr<S>, L> Eqn<A, A, L> { pub fn refl(e: A, lang: L) -> Self; }
impl<A, B, L>          Eqn<A, B, L> { pub fn sym(self) -> Eqn<B, A, L>; }
impl<A, B, L: PartialEq> Eqn<A, B, L> {
    /// Needs the two middle terms to really match (trusted structural eq) AND the
    /// two `lang`s equal.
    pub fn trans<C>(self, rhs: Eqn<B, C, L>) -> Result<Eqn<A, C, L>, Error>;
}
impl<A, A2, L> Eqn<A, A2, L> {
    /// Congruence in the ARGUMENT, under any op `F` (ops denote functions). No
    /// congruence in the operator — you cannot equate ops.
    pub fn cong_app<F: Op>(self, f: F) -> Eqn<App<F, A>, App<F, A2>, L>
        where A: Expr<F::In>, A2: Expr<F::In>;
    // cong_pair / cong_tuple / cong_slice: componentwise, similarly.
}
```

**Gated — anything that injects external trust** (runtime `admits`, in `MANIFEST`):

```rust
impl<L: Language> Eqn</* assoc-fn home */> {
    /// `Val(a) = Val(b)` via the type's TRUSTED equality — the native-computation
    /// seam, so it is GATED on `TrustedEqAt::<C>` being admitted (you choose which
    /// types' native equality you trust). `None` if `teq` can't decide.
    pub fn of_teq<C: Sort + TrustedEq>(a: C, b: C, lang: L) -> Option<Eqn<Val<C>, Val<C>, L>>;
    /// Apply a general rule (premises ride inside `rho`). Gated on `Rho`'s `TypeId`.
    pub fn apply<Rho: Rule<L> + 'static>(lang: L, rho: Rho)
        -> Result<Eqn<Rho::Lhs, Rho::Rhs, L>, Error>;
    /// Evaluate an op to its canonical value `App<F, arg> = F.eval(arg)`. Gated on
    /// `F`'s `TypeId` (the op-as-rule).
    pub fn canon<F: CanonRule, A: Expr<F::In>>(f: F, arg: A, lang: L)
        -> Result<Eqn<App<F, A>, Val<F::Out>, L>, Error>;
}
```

**Lift — weaken the language, one layer** (sound: `tree(L2) ⊆ tree(L)`):

```rust
impl<A, B, L2> Eqn<A, B, L2> {
    pub fn lift<L: Language>(self, into: L) -> Result<Eqn<A, B, L>, Error>
        where L2: 'static
    { /* check into.extends(TypeId::of::<L2>()) + value-level embed */ }
}
```

The structural calculus is always available; `apply`/`canon` are the only gated
gates, and `lift` weakens. To use a parent's *computation*, evaluate it in its home
language (freely construct that language value — non-opacity!) and `lift` up;
multi-layer reach is composing `lift`s, and the facade can offer a `cov.canon(…)`
convenience that projects-applies-lifts. Each gated step fires only where admitted;
each `lift` is a sound one-layer weakening.

### TCB manifest (enumerate the trust)

`L::MANIFEST` is the TCB as a compile-time tree of raw **`TypeId`s** (+ metadata)
— exact, unforgeable identity, *no* names in the framework. Naming lives in a
**separate, untrusted trait** keyed off `TypeId`. Two consequences:

- **Pinning is on the named projection.** Raw `TypeId`s are unstable across
  compiler versions, so the golden file is the *name-projected* tree
  `{ "eq.refl": …, "hol.beta": … }`; the `Named` overlay is what makes it stable
  and readable. The map should be injective (a test checks it) — a bad map only
  hurts legibility, never soundness (what fires is `admits`, on `TypeId`).
- **The TCB identity is exact.** No trusted `NAME` const to collide or mislabel;
  different consumers may present the same tree under different namespaces.

Because `impl Language for L` is unique (coherence) and the macro builds `admits`,
`extends`, and `MANIFEST` from the *same* declaration, they cannot drift; a rule
added/removed re-shapes `MANIFEST` and fails the golden-file diff. Bonus: since
`MANIFEST` is a `const`, the TCB is auditable *without running anything* — a tool
can read it straight out of the binary's rodata.

## Soundness

The trusted claim: *every `Eqn<_,_,L>` is derivable using only the universal
equality calculus + rules in `tree(L)`; hence if every rule in `tree(L)` is sound,
`L` is sound.*

1. **Unique, crate-reserved admit-set.** `Language` is parameter-free, so
   `impl Language for Foo` is allowed only in `Foo`'s crate (orphan: Self is the
   sole type) and is unique (coherence). Thus `Foo::admits`/`extends`/`MANIFEST`
   — and `tree(Foo)` — are fixed by the program, settable only by `Foo`'s author.
   *This is the load-bearing property: soundness by uniqueness of implementation,
   not by the orphan rule on parameterized traits, and not by opacity.*
2. **No rule injection.** A third party cannot override `Foo::admits` (the impl is
   unique and crate-reserved), and minting is gated on the runtime
   `lang.admits(TypeId::of::<Rho>())` check, so only `tree(L)` rules ever fire. A
   third party *can* define their own `EvilLang` whose `admits` is permissive —
   but that mints only `Eqn<_,_,EvilLang>`, honestly labelled, with `EvilLang`'s
   unsoundness visible in *its* manifest; it never contaminates `Hol`/`Cov`.
   Trust assumptions added by going through `TypeId`: (a) `TypeId` is injective
   (the whole ecosystem relies on this; ~2⁻¹²⁸ collision), and (b) rules are
   `'static` (lifted later via the `Rule::Id` tag).
3. **Per-rule TCB, enumerable.** What remains to trust is the soundness of each
   rule's `conclude` — a finite, per-rule audit, and the manifest enumerates
   exactly which (so adding Nat can't silently enlarge HOL's TCB).
4. **Uninterpreted ⇒ sound.** An op with no rule touching it is inert: nothing
   nontrivial is derivable about it, so opaque ops never threaten soundness. This
   is *why* the closed world is safe — `tree(L)` is the complete set of things
   `L` can do; everything else is vacuous.
5. **No opacity needed.** Nowhere did we require `L` values to be unconstructible.
   A third party may build an `L` value, but to mint they must apply `tree(L)`
   rules (sound) and cannot inject rules. Forging is impossible regardless of
   constructibility — the original objection is dissolved.
6. **Child ⊆ parent, one layer at a time.** `lift` runtime-checks *direct*
   `into.extends(L2)` and is a sound weakening; composing lifts threads up,
   and the composition is still sound weakening. A theorem proved with only HOL
   rules remains valid in `Cov` *and demonstrably used none of the Builtins TCB*
   — the chain of homes it passed through is exactly its real dependency set.

## The one knob: per-instance vs uniform rules

> Should a rule fix a single sort, or range over many with the TCB fixing both
> the rule and its sorts? (Store `Text@String, Text@char`, or `Text` over
> `{String, char}`?)

**Criterion: a rule may cover many sorts/ops exactly when its soundness argument
is uniform across them — one audit covers all instances.** Otherwise make it
per-instance so each instance gets its own audit line in the manifest.

- *Uniform* → one leaf. Congruence is sound for every op by one argument ⇒ a
  single `Eq::Cong` rule, not one-per-op.
- *Per-instance* → one leaf per instantiation. "Text equality decides" rests on a
  different argument for `String` vs `char` ⇒ `TextEq<String>`, `TextEq<char>` as
  two named leaves.

Mechanically: rules may be generic (`Rule<S>`); the **tree always holds
monomorphic leaves** (each used instantiation is its own named entry), so the
manifest stays a flat, exhaustively-auditable set — generic code reuse without
losing per-instance auditability.

## HOL as an instance

- **Sorts.** `HolTy` (HOL types), `HolTm<V>` (HOL terms over free-variable type
  `V`). Bound variables are de-Bruijn (machine naturals in the representation —
  distinct from the object-level `Nat` builtin).
- **Type-former ops.** `Fun: Op<In=(HolTy,HolTy), Out=HolTy>`, `Bool`, `Ind`, and
  **subtype** formers from `new_type_definition` (each a declared op).
- **Term-former ops** (`Out = HolTm<V>`): `App`, `Abs`, `Const`, `Eq`, `Select`,
  and `Var: Op<In=(V, HolTy), Out=HolTm<V>>` (constructor is `(var, ty)`). A
  variable-retag op `V → V'` is always sound (variables are typed).
- **Locally-nameless machinery as ops-that-are-rules.** `Fv: Op<In=HolTm, Out=VarSet>`
  (free variables), `Bv: Op<In=HolTm, Out=Nat>` (max bound index; *locally closed*
  ⟺ `Bv(tm) = 0`), `subst`, β, … — each a single type that is an `Op` (write it
  freely, uninterpreted) **and** a `CanonRule` (evaluate it only with the op's
  `TypeId` admitted). So you can *state* `Fv(tm) = ∅` anywhere; you can *prove* it
  by computation only where `Fv` is in your TCB.
- **Rules.** `Hol` declares beta, eta, the connective definitions, type-def
  abs/rep bijections, and admits the locally-nameless ops + the `TrustedEq` leaves
  it needs (e.g. `bool`/`Nat`). The equality calculus is framework-level (ungated),
  so there is no `Eq` language to inherit — `Hol` may inherit a tiny `Prim` base
  that just collects the common `TrustedEq` leaves, or declare them directly.
- **Builtins as layered languages.** `Nat` declares: reduce a `Nat` literal to
  `S(S(…0))`, reduce `Add`/`Mul`, commute them past the relevant HOL ops, …; and
  inherits `Hol`. Likewise `Int`, `Bytes`, `Text` (String+char),
  `FixedWidth` (u8..u128, later f32/f64). Each adds *only* its rules to the TCB.
- **Top.** `Builtins` inherits `(Nat, Int, Bytes, Text, FixedWidth)`; `Cov`
  inherits `(Hol, Builtins)`. `Cov` admits `Hol` as a (transitive, via lift) parent
  ⇒ free HOL→Cov cast; later `Wasm`, `X86`, … join `Builtins`.

## Hard parts / risks (be honest)

- **`admits`/`extends`/`MANIFEST`** are now plain hand-writable items — no trait
  coherence, no sealing. The `language!` macro is pure convenience; the
  remaining trust is "the three agree with each other", which the macro
  guarantees by deriving them from one declaration (and the golden-manifest test
  cross-checks). The runtime membership branch DCEs at `-O` for static `Rho`.
- **Trusted structural equality on `Expr`** (the `trans` middle-term check + `dyn`
  support) is a small framework-TCB operation — standard HOL-Light term-comparison
  machinery, audited once.
- **`'static` on rules/ops** (for `TypeId::of`) blocks borrowing them; lift later
  via the `Rule::Id` identity tag (seam in place from day one). *Expressions*
  borrow freely (never `TypeId`-keyed).
- **Naming `Val`** (vs `Const`/`Lit`) and whether `Ref` survives or folds into a
  `Deref` op — bikeshed, decide at first use.

## Implementation stages

0. **Framework core**: `Sort`/`Op`; `Expr` (`Val`/`Ref`/`App`/`&A`/`dyn`/products,
   sealed) + trusted structural equality; `TrustedEq`; `Eqn<A,B,L>` + the ungated
   calculus (`refl`/`sym`/`trans`/`cong`) and gated `of_teq`/`apply`/`canon`/`lift`;
   `Language` (`admits`/`extends`/`const MANIFEST`) + `Rule`/`CanonRule` (with the
   `Id`-tag seam); the `language!` macro; the name-projected golden-`MANIFEST` test.
   *Milestone: prove a toy equational theorem (e.g. `nat.add 2 3 = 5` via `canon`,
   or a `cong`/`trans` chain) and diff its manifest.*
1. **HOL**: `HolTy`/`HolTm<V>` ops + `Hol` rules over `Eq`. *Milestone: a handful
   of real HOL theorems; HOL manifest pinned.*
2. **First builtin**: `Nat` (literals + `Add`) over `Hol`, discharged against the
   HOL definition; exercise the `Hol → Nat`/`Cov` cast.
3. **Remaining builtins** (Int/Bytes/Text/FixedWidth), then the catalogue port.
4. **Later**: `Wasm`/`X86` languages; fold into `Builtins`.
```

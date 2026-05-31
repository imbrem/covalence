# Prover Architecture

This document describes the architecture of the Covalence prover kernel — a
HOL-based metalogic intended to glue together object logics, evaluators, and
cryptographic trust schemes without baking any of them into the kernel itself.

It is the canonical reference for the kernel's design. Implementation details
that live in code (file layout, exact function signatures) are out of scope
here.

For the staged build-out, see [`prover-mvp-plan.md`](./prover-mvp-plan.md).
For the exhaustive list of kernel primitive operations, their type
signatures, host-side reduction semantics, minimal axioms, and the
macro-defined symbolic rewrite layer, see
[`prover-primops.md`](./prover-primops.md).

---

## 1. Vision

The kernel is **a foundation-agnostic metalogic**. It does not commit to a
particular object logic (ZF, GT, type theory, …), to a particular evaluator
(WASM, future native runtimes), or to a particular cryptographic trust scheme
(EdDSA, ZKP, …). Each of these enters as user-supplied **assumptions** about
plain HOL terms; the kernel itself only ever applies HOL inference rules.

The intended workflow is **reverse-mathematics-style**: prove a statement
`φ` in the *weakest* logic that admits it, then lift `φ` to richer settings
via soundness translations expressed *inside* HOL. The same `φ` can have
multiple soundness interpretations — for instance, an equational result
proved in pure HOL can be lifted to any Cartesian-closed category by a
single semantics axiom, separate from the lift into ZF.

The kernel's role is to:

1. Maintain a canonical pool of terms, types, and equalities.
2. Enforce HOL's inference rules.
3. Provide a single extension mechanism — **concepts** — through which
   *anyone* can introduce new untrusted facts while preserving soundness.
4. Make assumptions first-class: oracles, content-addressed storage, and
   cryptographic trust all enter as concept theories the user opts into.

The kernel has **no built-in notion of**: content addressing, hashing,
signatures, WASM, oracles, axioms (the user's "axioms" are just assumptions
in the root [Context](#26-context)), tactics, proof terms, automatic
equality reasoning beyond what the inference rules do explicitly, or
automatic search/lookup of facts beyond explicit API calls.

---

## 2. Core Data Model

### 2.1 Namespaces

The kernel keeps **distinct ID spaces** rather than one shared `NameId`:

| Namespace | What it indexes | Owner |
|---|---|---|
| **Builtin** | Hard-coded kernel constants and types (see §3.2) | Kernel |
| **TypeName** | User-declared type constructors | User |
| **ConstName** | User-declared HOL constants | User |
| **VarName** | Free variable names (for printing and INST) | User |
| **ConceptId** | Concept handles (see §6) | Kernel-assigned |

Builtins live in a sealed enum baked into the kernel — they're not
declared via the same path as user names. The other namespaces are
separate maps in the relevant tables; a `ConstName` and a `VarName` with
the same string content are distinct.

Inside the arena, builtins don't go through the name tables at all —
they're TermDef/TypeDef variants directly (§3.2).

### 2.2 Arena

An **Arena** is a pool of types, terms, bitvectors, and union-find
state. Its structural tables (types, terms, bitvectors) are append-only
at the user level; the kernel may **mutate a term's structural form in
place to replace it with a provably-equal one** (see §4.4 "Rewrite").
Union-find state is mutable throughout.

```
Arena {
  types: Vec<TypeDef>,               // indexed by TypeId, append-only
  terms: Vec<TermDef>,               // indexed by TermId; mutable via kernel rewrite
  uf_terms: Vec<TermUfEntry>,        // one per term, mutable
  uf_types: Vec<TypeUfEntry>,        // one per type, mutable (see §4.6)
  imports: Vec<Arc<Arena>>,          // frozen arenas this one references

  // -- interning tables: variable-sized payloads pulled out of TermDef
  //    so the enum itself stays Copy (see §3.1) --
  strings:    IndexSet<SmolStr>,     // names: VarName, ConstName, TypeName, TypeVarId
  bytes:      Vec<Vec<u8>>,          // byte-string literals (and bits >> 64 bits)
  bits:       Vec<Bits>,             // bit-string literals with explicit bit-length
  ints:       Vec<Int>,              // arbitrary-precision int literals
  nats:       Vec<Nat>,              // arbitrary-precision nat literals
  tyargs:     Vec<Vec<TypeRef>>,     // arg lists for Tyapp
}

TermUfEntry {
  canonical: TermRef,                // arena-aware (§4.1); Local or Foreign(import, id)
  bound_depth: u32, has_free: bool,  // closed() = bound_depth == 0 && !has_free
}

TypeUfEntry {
  canonical: TypeRef,                // same shape
}
```

The **interning tables** are how the kernel keeps `TermDef` (and the
`TermRef`/`TypeRef` it embeds) `Copy`. Anything bigger than a few `u32`s
goes through a table:

- A free-variable's name is a `StrId` (index into `strings`), not a
  `SmolStr` carried inline.
- A long bit-string is a `BitsId` (index into `bits`); a short one is
  inline as `BitsInline { len, data }` directly in the `TermDef`
  variant (see §3.2).
- Arbitrary-precision int/nat literals are `IntId` / `NatId` when
  large, inline as `i64` / `u64` when they fit.
- Bytes literals are always `BytesId`.
- A `Tyapp(name, args)`'s arg list is a `TyArgsId`.

Foreign-arena refs are `Foreign(ImportId, id)` where `ImportId` is an
index into `arena.imports`, not an `Arc<Arena>` carried inline (the
Arc lives in the imports table). Both `TermRef` and `TypeRef` are
therefore plain `(enum_tag, u32, u32)` — `Copy`.

**Arena identity is by pointer**: there is no kernel-assigned arena
identifier. Two canonical IDs `(arena_a, id_a)` and `(arena_b, id_b)`
are equal iff `arena_a` and `arena_b` point at the *same allocation*
and `id_a == id_b`. There is no "arena number" table; identity is the
arena itself.

The kernel uses two flavours of arena reference and treats them as
identity-equivalent:

- **`Arc<Arena>`** — the default, used wherever an arena reference
  needs to be **stored** (UF entries' canonical pointers,
  `Foreign(_, _)` term references inside another arena's TermDef,
  `Prop`/`Thm` fields that outlive their constructor). Identity via
  `Arc::ptr_eq`.
- **`&'a Arena`** — used wherever an arena reference is purely
  **borrowed for the duration of a call**: hot read paths, in-place
  congruence checks, building a new term whose source arenas already
  outlive the borrow. Avoids the Arc refcount bump. Identity via
  `std::ptr::eq` on the underlying `*const Arena`.

Identity comparisons **work across the boundary**:
`Arc::as_ptr(arc)` gives the same `*const Arena` as
`r as *const Arena` for `r: &Arena` referring to the same allocation,
so an `Arc<Arena>` stored in a UF entry can be compared by pointer
against a `&Arena` passed into a query.

When an API needs to be polymorphic over "I want either form here,"
an explicit enum

```rust
enum ArenaRef<'a> {
    Arc(Arc<Arena>),
    Borrowed(&'a Arena),
}
```

is a reasonable shape; for most read paths a plain `&Arena` argument
is enough.

This matters in subtle ways:

- Cloning a frozen arena's `Arc` and storing it in two places leaves
  identity unchanged — both are still the same arena.
- Two structurally-identical arenas that happen to share content but
  live at different allocations are **not** the same arena; their
  contents are compared structurally, never canonically.
- A `&Arena` obtained by dereferencing an `Arc<Arena>` has the same
  pointer identity as that Arc — passing the borrow into a query and
  later coming back with the Arc keeps the identity intact.

The type UF parallels the term UF. The kernel provides **no rule to
introduce arbitrary type unions** — there's no analog of `union(a, b)`
that takes a "proof" of `a = b` at the type level, because we
deliberately don't have a type-level equality predicate in the logic.
What the type UF *does* support is **caching derived type equalities
via congruence** (same shape as the term side: structural decomp,
foreign-import propagation, level-k equality predicates). The reason
to maintain it is that types imported across the diamond import case
need the same arena-aware canonical treatment as terms, and downstream
tooling sometimes wants to ask "are these two types the same?"
without re-walking the structural form each time.

For introducing genuine isomorphisms between types — the
content-addressed-types use case — the user declares an opaque type
and an asserted bijection axiom (§7.4); the bijection lives at the
*term* level, so the type UF doesn't get unsoundly populated.

Key properties:

- **Structural tables are append-only from the user's view.** Terms
  and types are added; user-level code never sees a slot removed.
- **The kernel may mutate `terms[id]` to an equal `TermDef`.** This is
  the [rewrite primitive](#44-rewrite); it's not the user's privilege
  but the kernel's, and only along an existing UF equivalence.
- **Canonical IDs are arena-aware tuples `(Arc<Arena>, TermId)`** and
  `(Arc<Arena>, TypeId)`. Identity is by `Arc::ptr_eq`. A bare ID is
  *not* a canonical name across arenas — see §4 for why.
- **Imports** are `Arc`'d frozen arenas this arena may reference. Terms
  can reach across via `Comb`/`Abs` children pointing at imported
  terms; equalities cannot, except by manual user-driven unions inside
  this arena.
- **Closed flag** is computed once at term insertion. Cheaper than
  walking the term every time we need to know.
- **Bitvector side table.** Short bit-string literals are stored
  inline inside `TermDef` (see §3.2); long ones live in `bitvectors`
  and the term holds an index. This is purely an arena representation
  choice — it isn't visible to the logic, and it has no relation to
  hashes or content addressing.

#### Foreign imports

Arenas can **freeze**, becoming `Arc<Arena>` and read-only. Other
arenas hold these as `Arc`'d entries in `imports`. To reference a term
in a frozen arena, the local arena either:

- Allocates a `Comb`/`Abs` whose child is a `Foreign(arena, term_id)`
  handle holding an `Arc<Arena>` to the source (see TermDef in §3.2), or
- Re-allocates the term structurally in the local arena, importing
  only the part it needs.

Unfreezing clones the arena into a fresh mutable one with the same
indices.

#### Fresh variables

Both arenas and theorems can mint fresh free-variable names guaranteed
not to clash with anything in the local arena or its imports. This is
the substitute for ad-hoc gensyms.

### 2.3 Prop

A **Prop** is `(arena, context)`:

```
Prop {
  arena: Arena,         // owned
  context: Arc<Context>, // the assumptions and their lookup API
  concl: TermId,        // distinguished conclusion in `arena`
}
```

Crucially, the Prop's assumptions live **inside the Context** — not
directly on the Prop. This encapsulates the assumption API: anything
the user wants to do with assumptions (look them up, find equalities
inside them, check their own assumptions) goes through Context's
methods rather than directly touching a `Vec<Arc<Prop>>`.

A Prop is **not** by itself a theorem — it's just a structured
proposition with a context. The conclusion is whatever its `concl: TermId`
points at, and may be any HOL term (typically of type `bool`).

Prop is `Clone` (cheap via `Arc` sharing of the Context; the owning
arena is per-Prop).

**SMT-language analogy.** A `Context` plays the role of an SMT
**Formula** (a conjunction of asserted constraints — here, of
assumption Props). An `Arena` plays the role of an SMT **Clause**
(a self-contained line of reasoning with its own equality state). A
`Prop` is then literally a `(Formula, Clause)` pair: "given these
assumptions, here is the chunk of reasoning establishing the
conclusion." The analogy is structural, not exact — clauses in
DPLL-style SAT are disjunctions of literals — but the
Formula-vs-Clause split is the same separation between *global
assertions* and *local derivation state*.

### 2.4 Thm

A **Thm** is a compile-time-tagged Prop the kernel has stamped *true*.
Construction is kernel-only. There is no runtime "is_this_a_thm" flag:
the type system guarantees a `Thm` came out of an inference rule.

Choose between newtype (`struct Thm(Prop)`, private fields) and phantom
tag (`Prop<Verified>` vs `Prop<Untrusted>`) at implementation time. Both
give equivalent guarantees; the phantom form integrates more cleanly
with deserialization (§8).

Thm is `Clone`. A Thm can be used non-linearly (passed to multiple
rules) or consumed and mutated (rules that grow the arena take
`&mut Thm`).

`Goal` — a runtime "partially-proved Prop" — is **not** part of the
trusted kernel. Goals live in an untrusted convenience library on top.

### 2.5 Context

A **Context** is the kernel's encapsulated assumption store, plus the
API for inspecting it. Structurally:

```
Context {
  assumptions: Vec<Arc<Prop>>,
  parent: Option<Arc<Context>>,
}
```

It's a recursive linked list of assumption layers; pushing a context is
cheap. The root Context contains the user's chosen trust base — anything
the kernel would have called an "axiom" in classical HOL is just a Prop
in the root Context here. The kernel itself adds nothing to any Context.

What makes Context more than a `Vec<Arc<Prop>>` is its **inspection
API** — paralleling the no-auto-congruence rule. Just as the kernel
won't search for equalities across UF classes for you, it won't search
the Context for relevant facts either. You walk it.

Sketch of the inspection API:

| Method | Returns |
|---|---|
| `len()` | number of assumptions in the current layer |
| `assumption(i)` | `Arc<Prop>` — the i-th assumption |
| `assumption_context(i)` | `Arc<Context>` — the i-th assumption's *own* context |
| `find_equality(i, lhs, rhs)` | whether assumption `i` proves `lhs = rhs` |
| `parent()` | `Option<Arc<Context>>` for walking up the stack |

The key constraint these reflect: **you can't import a fact from an
assumption Prop until you've satisfied that Prop's own assumptions.**
The Context API lets the user inspect what an assumption depends on
(`assumption_context(i)`) so they can discharge those assumptions in
their current context before importing.

This makes "I want to use the equality `a = b` that this assumption
provides" an explicit kernel call rather than an implicit search. The
kernel doesn't search; it answers questions the user knows enough to
ask.

#### Importing a Context as a boolean term

The kernel provides an operation `import_context_as_bool(ctx) -> TermId`
that takes a Context and produces a HOL bool term in the current arena
representing "every assumption in `ctx` holds." Concretely, if the
context's assumptions are `[A₁, …, Aₙ]`, the resulting term is the
conjunction (or some canonical n-ary AND) of each `Aᵢ`'s conclusion
form.

Similarly `import_prop_as_bool(p) -> TermId` produces a bool term for
a whole Prop — i.e. "the Prop is true," materialised as `context_bool
⇒ concl`.

These two operations are how we **talk about contexts and props at the
meta level inside HOL**. It looks strange — a prop manipulating
references to other props — but it's exactly what lets us state things
like "this context implies that context" or "these two props are
extensionally equal as boolean statements" inside the kernel's own
logic.

These operations are kernel primitives because they have to weave
foreign-arena references into the target arena correctly; doing so by
hand outside the kernel is error-prone.

### 2.6 Summary

| Object | Owns | References |
|---|---|---|
| `Arena` | types/terms/bitvectors + UF state | frozen `Arc<Arena>`s as imports |
| `Prop` | one `Arena`, a `concl: TermId` | `Arc<Context>` |
| `Thm` | a `Prop` that the kernel has validated | (same as Prop) |
| `Context` | `Vec<Arc<Prop>>` | `Option<Arc<Context>>` parent |

---

## 3. Term Language

### 3.1 Locally nameless

Terms use **de Bruijn indices for bound variables + named free
variables**. The kernel's internal `TermDef` enum is private; users
interact through the public `TermKind` enum and fallible getters.
This decouples the public API from the storage layout and lets us
swap the internal representation without churning callers.

#### Internal layout invariant: 3 × u32

`TermDef` is `Copy` and every variant fits in **(tag, lhs, rhs)** —
12 bytes total. Variable-sized payloads (names, byte strings,
big-ints, type-arg lists) live in per-arena tables (§2.2); foreign-
arena refs live in a side table (below); and *display hints* (the
human-readable name of an `Abs`) live in an optional side table
because they never affect correctness. Concretely:

```rust
// Public view — kernel consumers pattern-match on this. Stable.
pub enum TermKind {
    Bound(u32),
    Free(StrId, TypeRef),
    Const(StrId, TypeRef),
    Comb(TermRef, TermRef),
    Abs(TypeRef, TermRef),            // no name; see arena.abs_hints
    Eq(TermRef, TermRef),
    True, False,
    // primitives
    Op1(PrimOp1, TermRef),            // unary primitive
    Op2(PrimOp2, TermRef, TermRef),   // binary primitive
    Ite(TypeRef, TermRef, TermRef, TermRef),  // if-then-else, branch type carried
    // literals
    U8(u8) | U16(u16) | U32(u32) | U64(u64),
    I8(i8) | I16(i16) | I32(i32) | I64(i64),
    IntInline(i64) | IntStored(IntId),
    NatInline(u64) | NatStored(NatId),
    BitsStored(BitsId),
    BytesStored(BytesId),
}

// Private internal representation. May change. Most variants are
// 1-2 u32s of payload; primops are per-op variants so the (op, lhs,
// rhs) shape fits 3 u32s without an extra tag byte. Op1/Op2 in
// TermKind reconstruct the grouping.
pub(crate) enum TermDef {
    // structural
    True, False,
    Bound(u32),
    Free(StrId, TypeRef),
    Const(StrId, TypeRef),
    Comb(TermRef, TermRef),
    Abs(TypeRef, TermRef),
    Eq(TermRef, TermRef),
    // partially-applied: just branch type + bool cond; branches via Comb
    Ite(TypeRef, TermRef),
    // partially-applied: just element type + nat count; f via Comb
    Iter(TypeRef, TermRef),
    Eps(TypeRef, TermRef),    // Hilbert choice
    Forall(TermRef),          // ∀ over predicate of inferred domain
    Exists(TermRef),          // ∃ likewise
    Ne(TermRef, TermRef),     // ≠
    Id(TypeRef),
    Comp(TermRef, TermRef),
    // literals as above; storage may be inline or via *Id into a table
    ...
    // one variant per primop kind, so the (variant, child, child) shape
    // is exactly (tag, lhs, rhs) — no embedded PrimOp byte
    NatSucc(TermRef),     NatPred(TermRef),    IntNeg(TermRef),
    NatAdd(TermRef, TermRef), NatSub(TermRef, TermRef), ...
    LogicalNot(TermRef),
    LogicalAnd(TermRef, TermRef), LogicalOr(TermRef, TermRef),
    LogicalXor(TermRef, TermRef), LogicalNand(TermRef, TermRef),
    LogicalNor(TermRef, TermRef), LogicalImp(TermRef, TermRef),
    BytesLen(TermRef), BytesHead(TermRef), BytesTail(TermRef),
    BytesConcat(TermRef, TermRef), BytesCons(TermRef, TermRef),
    BytesIndex(TermRef, TermRef), BytesEq(TermRef, TermRef),
    BitsLen(TermRef),
    BitsToBytes(TermRef), BytesToBits(TermRef),
    NatToInt(TermRef), IntToNat(TermRef),
    // ...full list in §3.4 and docs/prover-primops.md
}

// TermRef / TypeRef are packed u32 — bit 31 is the local/foreign
// flag, bits 0-30 are an index. Local: index into arena.terms /
// arena.types. Foreign: index into arena.foreign_terms /
// arena.foreign_types — side tables of (ImportId, id) pairs.
pub struct TermRef(u32);
pub struct TypeRef(u32);
```

Two consequences worth calling out:

- **`Abs` has no name field.** Display hints (the original parameter
  name a user wrote) are pinned to `TermId`s in
  `arena.abs_hints: HashMap<TermId, StrId>` (or similar). The kernel
  ignores them; only printers consult them. Dropping them keeps the
  variant within the 8-byte payload budget *and* makes the equality-
  by-structure check trivially α-equivalent.
- **`Ite` and `Iter` use type inference, not an explicit `TypeRef`.**
  `Ite(cond, then)` infers the branch type α from `type_of(then)`
  in one step; the else-branch is supplied via `Comb` and checked
  against α. `Iter(n, f)` infers α from `dom(f)` and *is* the
  iterated function directly (type `α → α`). Both store two
  `TermRef`s — 8 bytes inline, no side table.

`TypeDef` follows the same Copy + 3-u32 invariant; it's public
because the variant set is small enough that pattern-matching is
ergonomic. `TyArgsId` is the indirection for variadic `Tyapp`
arguments.

Bound-var substitution doesn't need any alpha-renaming dance;
structural equality of `TermDef`s already gives α-equivalence —
display hints stripped, de Bruijn indices intact.

A `TermRef`/`TypeRef` is the type used for child links. Local refs
point to the current arena's table; foreign refs resolve through
`arena.foreign_terms[i]` (or `_types`) → `(ImportId, id)` →
`arena.imports[ImportId]` → an `Arc<Arena>` → that arena's table.
Arena identity (§2.2) is still by pointer:
`Arc::ptr_eq(a.imports[i], b.imports[j])`.

### 3.2 Builtins

Builtins are **TermDef/TypeDef enum variants** — not entries in user
namespaces, not magic constants in a side table, not sentinel name
IDs. They appear in the same enum as everything else; an inference
rule that pattern-matches on `TermDef` sees them right next to
`Bound`, `Comb`, etc.

We accept a relatively rich set of builtins (more than HOL Light's
`= : α → α → bool` alone) in exchange for shorter time-to-MVP and
efficient FFI. The trade-off is documented in §3.4: each builtin
function-value has a minimal HOL axiomatization, and the kernel's
trust surface grows by the size of the `Prim` enum plus its
reduction machinery. If we later want to reclaim the ultra-minimalism,
we can move pieces out of the kernel into untrusted extension traits
without touching the logic.

**TypeDef variants in full** (all `Copy`):

| Variant | Logical type | Notes |
|---|---|---|
| `Bool` | `bool` | builtin |
| `Bits` | `bits` | primitive infinite type — bit strings of arbitrary length |
| `Bytes` | `bytes` | byte strings; the kernel ships this as a primitive but the user-side trust assumption `bytes ≅ list u8` connects it to a list theory |
| `Int` | `int` | arbitrary-precision signed integer |
| `Nat` | `nat` | arbitrary-precision unsigned integer (≥ 0) |
| `U8`,`U16`,`U32`,`U64` | fixed-width unsigned | matches WASM `iN` for FFI |
| `I8`,`I16`,`I32`,`I64` | fixed-width signed | same, signed |
| `Fun(TypeRef, TypeRef)` | `α → β` | builtin |
| `TVar(StrId)` | polymorphic type variable | name interned in `arena.strings` |
| `Tyapp(StrId, TyArgsId)` | user-declared type constructor instance | arg list via `arena.tyargs` |

**TermKind variants in full** — the public view. The private
`TermDef` may have a different (typically more granular) layout for
storage efficiency.

| Variant | What it represents | Source |
|---|---|---|
| `Bound(u32)` | de Bruijn index | structural |
| `Free(StrId, TypeRef)` | free variable, named, typed | user/kernel-fresh |
| `Const(StrId, TypeRef)` | user-declared HOL constant at an instance | user |
| `Comb(TermRef, TermRef)` | application | structural |
| `Abs(TypeRef, TermRef)` | binder; display hint via side table | structural |
| `Eq(TermRef, TermRef)` | polymorphic equality | **builtin** |
| `Ne(TermRef, TermRef)` | polymorphic inequality (sugar for `Not (Eq …)`) | **builtin** |
| `Forall(TermRef)` | universal quantifier over `P : α → bool` | **builtin** |
| `Exists(TermRef)` | existential quantifier over `P : α → bool` | **builtin** |
| `True`, `False` | boolean literals | **builtin** |
| `Op1(PrimOp1, TermRef)` | unary primitive op (logic, arithmetic, casts) | **builtin** (§3.4) |
| `Op2(PrimOp2, TermRef, TermRef)` | binary primitive op | **builtin** (§3.4) |
| `Ite(TermRef, TermRef)` | if-then-else: `Ite(cond, then) : α → α`, else via `Comb`; α inferred from `then` | **builtin** (§3.4) |
| `Eps(TypeRef, TermRef)` | Hilbert choice: `(α → bool) → α` | **builtin** (§3.4) |
| `Id(TypeRef)` | identity combinator: `α → α` | **builtin** (§3.4) |
| `Comp(TermRef, TermRef)` | function composition: `(β → γ) → (α → β) → (α → γ)` | **builtin** (§3.4) |
| `Iter(TermRef, TermRef)` | iter-n-times: `Iter(n, f) : α → α`; α inferred from `f`'s domain | **builtin** (§3.4) |
| `U8(u8)` … `U64(u64)` | unsigned fixed-width literal | **builtin** |
| `I8(i8)` … `I64(i64)` | signed fixed-width literal | **builtin** |
| `IntInline(i64)` / `IntStored(IntId)` | arbitrary-precision integer literal | **builtin** |
| `NatInline(u64)` / `NatStored(NatId)` | arbitrary-precision natural literal | **builtin** |
| `BitsStored(BitsId)` | bit string literal | **builtin** |
| `BytesStored(BytesId)` | byte string literal | **builtin** |

`True`/`False` and `Eq` are baked in. The goal is simpler *code*,
not minimal typing rules — a baked-in `True` skips threading Hilbert
choice through the bootstrap.

**Logical operators** (`Op1(LogicalNot, _)` and `Op2(LogicalAnd, ...)`
etc.) are first-class primops rather than user-space definitions.
Listing them in §3.4 with their reduction tables lets the kernel
reduce concrete Boolean expressions cheaply — important for
discharging hypothesis sets in tactics.

**`Ite`** is first-class for the same reason. A naive
encoding via `Comb` and a polymorphic `ite : bool → α → α → α`
constant would require traversing two `Comb`s to recognize the
shape; here the kernel can pattern-match `TermKind::Ite` directly,
reduce on a literal `True`/`False` condition, and emit equality
between the term and the matching branch via §4.4 rewrite.

User-defined constants (`Const(name, ty)`) and user-defined type
constructors (`Tyapp(name, args)`) are the only TermKind/TypeDef
variants that read from the user-side namespaces (§2.1). Every other
variant is either structural or a builtin enum case.

### 3.3 Closed vs open terms

The kernel distinguishes **closed** (no `Free(_)` reachable, no dangling
`Bound(i)`) from **open** terms. Both can live in the arena. The
restriction is on **non-congruence unions** (§4):

- **Closed terms** can be unioned with anything they're proved equal to.
- **Open terms** can only acquire equalities via congruence — the user
  has to wrap them in a binder first to do nontrivial equality
  reasoning.

The closed flag is stored on each `TermUfEntry` and set once at
insertion.

### 3.4 Computational primitives

The kernel ships two small enums `PrimOp1` (unary) and `PrimOp2`
(binary) listing every built-in function — Boolean logic, arithmetic
over `nat`/`int`/uN/iN, comparisons, length/index, casts, and the
`bits`/`bytes` accessors. They appear in TermKind as `Op1(PrimOp1,
_)` / `Op2(PrimOp2, _, _)`, plus the dedicated `Ite(_, _, _, _)`
form for if-then-else.

The rationale is shorter time-to-MVP: rather than axiomatize every
primitive type from scratch over `bits` (HOL-Light minimalism), the
kernel ships concrete operational behavior on its primitive types,
plus a **minimal axiomatization** that characterizes each operation
abstractly. Higher-level theorems (commutativity, distributivity, …)
are derived in user space.

The complete `PrimOp1`/`PrimOp2` catalog — with type signatures,
host-side reduction semantics, and minimal axioms — lives in
**[docs/prover-primops.md](./prover-primops.md)**. That document is
the source of truth; this section names the categories.

#### PrimOp1 (unary) categories

- **Booleans** — `LogicalNot`.
- **Naturals** — `NatSucc`, `NatPred` (pred 0 = 0).
- **Integers** — `IntNeg`.
- **Bytes** — `BytesLen`, `BytesHead`, `BytesTail`, `BytesIsEmpty`.
- **Bits** — `BitsLen`, `BitsIsEmpty`.
- **Casts** — `NatToInt`, `IntToNat` (clamped at 0), `BytesToBits`,
  `BitsToBytes` (defined iff bit length % 8 = 0), and the matrix of
  uN↔iN/Nat/Int sign-extensions and truncations.

#### PrimOp2 (binary) categories

- **Booleans** — `LogicalAnd`, `LogicalOr`, `LogicalXor`,
  `LogicalNand`, `LogicalNor`, `LogicalImp`.
- **Naturals** — `NatAdd`, `NatSub` (saturating), `NatMul`,
  `NatDiv`, `NatMod`, `NatEq`, `NatLt`, `NatLe`.
- **Integers** — `IntAdd`, `IntSub`, `IntMul`, `IntDiv`, `IntMod`,
  `IntEq`, `IntLt`, `IntLe`.
- **Fixed-width** — for each `T ∈ {u8…u64, i8…i64}`: `T_Add`,
  `T_Sub`, `T_Mul`, `T_Div`, `T_Mod`, `T_Eq`, `T_Lt`, `T_Le`, plus
  bitwise `T_And`, `T_Or`, `T_Xor`, `T_Shl`, `T_Shr` (no `T_Not` —
  that's a unary, see `PrimOp1`).
- **Bytes** — `BytesConcat`, `BytesCons`, `BytesIndex`, `BytesEq`.
- **Bits** — `BitsConcat`, `BitsCons`, `BitsIndex`, `BitsEq`.

#### Combinators, choice, and control flow

The kernel exposes a small set of polymorphic combinators in
addition to the per-type primops:

- `Ite(α, cond) : α → α → α` — if-then-else. Carries the branch
  type and the boolean inline (8 bytes payload); both branches
  supplied through `Comb`. Reduces to the matching branch on a
  literal condition.
- `Eps(α, P) : α` — Hilbert choice; returns *some* element of `α`
  satisfying `P`, governed by `select_ax: P x → P (Eps α P)`. The
  *only* nontrivial existence axiom in the prelude.
- `Id(α) : α → α` — identity; `Comb (Id α) x = x`. The constant
  function `λ_:β. a` is just `Abs(β, a)` — no separate `Constant`
  primitive.
- `Forall(P)` and `Exists(P)` over `P : α → bool` — quantifiers
  defined by `forall_def: Forall P = (P = Abs α True)` and
  `exists_def: Exists P = Ne P (Abs α False)`. First-class so
  axioms read like `Forall (Abs nat (λn. …))` rather than
  unfolded `Eq … (Abs …)`.
- `Ne(a, b) : bool` — sugar for `Not (Eq a b)`, defined by
  `ne_def`. Same legibility win.
- `Comp(f, g) : (β → γ) → (α → β) → (α → γ)` — function composition;
  `Comb (Comp f g) x = Comb f (Comb g x)`. Equivalent to
  `λx. f (g x)`.
- `Iter(α, n) : (α → α) → (α → α)` — bounded iteration. Carries
  the element type and the count inline (8 bytes payload); the
  function-to-iterate supplied via `Comb`. Characterised by
  `Comb (Iter α 0) f = Id α` and
  `Comb (Iter α (succ n)) f = Comp f (Comb (Iter α n) f)`
  (and the inner-first variant). Combined with `induct_nat`, these
  axioms uniquely determine `Iter`. Arithmetic ops then derive as
  `add n m = Comb (Comb (Iter nat m) NatSucc) n`, etc.

All five combinators (plus `Forall`/`Exists`/`Ne`) preserve the
(tag, lhs, rhs) 3-u32 inline invariant — none use side tables.

See [prover-primops.md](./prover-primops.md) §8.5–8.6 for full
axioms and motivation.

#### Three rewriting layers

The kernel's rewrite/equality machinery splits into three lists,
all bottoming out at kernel-trusted primitives:

1. **Axioms (prover-primops.md §9).** Irreducible postulates: Peano
   + induction (nat, bits, bytes), the ring/order axioms (int), the
   uN/iN bijection axioms, `select_ax` (epsilon), `eta_ax`, `eq_ext`,
   `bool_cases`/`bool_distinct`, the combinator equations
   (`id_ax`, `comp_def`, `iter_zero`/`iter_succ_*`), and the
   `ite_negate` axiom. ~100 schemata; one-time audit.
2. **Reduction rules (§10).** Auto-applied by `kernel.reduce(t)` in
   a fixed, confluent, terminating, ordered list. Covers literal-
   arg evaluation, numeral normalization (`succ N → N+1` for
   literal `N`), identity/zero simplifications (`add a 0 → a`,
   `And a True → a`), and `Ite` on a literal condition. Each rule
   has `LHS = RHS` derivable in the axioms.
3. **Manual rules (§11).** User-invoked rewrites that don't fit
   reduction's discipline — typically recursive unfoldings
   (`add a (succ b) → succ (add a b)`, `Iter α (succ n) f → Comp f
   (Iter α n f)`) and canonicalisations (`Ite ty (Not b) x y →
   Ite ty b y x`). Each rule has `LHS = RHS` derivable in the
   axioms, but the kernel does not enforce termination — that's the
   caller's problem.

Audit cost is exactly the three lists. New primops add to the rule
lists; the axiom list grows only when a primitive introduces a new
postulate.

**Locally-closed precondition (all three layers).** Every rewrite —
axiom instantiation, reduction-rule firing, manual-rule firing —
requires the term being rewritten *and* every metavariable
substitution to be **locally closed**: zero dangling `Bound(_)`
indices. Free variables are fine. Open de Bruijn indices are not,
because syntactic rewrites that rearrange shape (composition
unfolding, primop reduction, induction-schema instantiation, …)
can change the binding distance of a `Bound(_)` and silently break
semantics. The arena tracks `bound_depth` in O(1) (§2.2), so the
check is one comparison per rewrite.

#### Reduce: basic ops as LCF calls

The kernel exposes a primitive

```rust
fn reduce(arena, term_ref) -> Result<(), KernelError>
```

When `term_ref` resolves to an application of a `Prim(op)` to
literal arguments (e.g. `Comb(Comb(Prim(NatAdd), NatInline(5)),
NatInline(3))`), the kernel computes the result (`NatInline(8)`)
using the host's arithmetic and adds the equality to the UF —
either by **rewriting** the term in place to the result's def
(§4.4) or by **unioning** with a freshly-allocated result term
(§4.3), at the caller's choice. Both are kernel-controlled, so the
operation is sound.

Equivalently: `reduce` is composable from the lower-level §4
primitives. A user-space implementation of the same operation looks
like

1. `t' = kernel.copy_term(t)` — fresh TermId in `t`'s UF class.
2. Compute the literal result outside the kernel.
3. `kernel.rewrite(t', result_def)` with a proof — and the only
   proof the kernel will accept for this rewrite *is* the
   computation itself.

So either path bottoms out at the same trust unit (the kernel's
host-arithmetic implementation). `reduce` is the convenience
primitive; the §4 ones are the building blocks. The kernel is free
to fuse the copy + rewrite into one allocation.

This is an explicit LCF-style call: the kernel never reduces on its
own. Users invoke `reduce` exactly where they want the cost. The
kernel never reduces with a non-literal argument either — `add x 0
= x` is a *theorem*, derived from the axioms below, not a reduction.

#### Minimal axiomatization

Each primitive comes with a minimal HOL axiomatization in the kernel
prelude — *just enough* to characterize it. Anything else is derived
in user space.

- **`nat`** is characterized by Peano-minus-induction:
  - `0 ≠ succ n`
  - `succ m = succ n → m = n`
  - Induction is *derived* from these plus Hilbert choice (`ε`):
    given a predicate, `ε` picks a counterexample if one exists;
    `succ`-injectivity + zero-distinct means there can't be one for
    a P satisfying the induction premises. Used once in the
    standard library; never re-derived.
- **`nat` arithmetic** is characterized by its recursion equations:
  `add n 0 = n`, `add n (succ m) = succ (add n m)`; similarly for
  `sub` (saturating: `sub n 0 = n`, `sub 0 m = 0`, `sub (succ n)
  (succ m) = sub n m`), `mul`, `div`, `mod`.
- **`int`** is characterized as the ordered commutative ring obtained
  by quotienting `nat × nat` (or equivalently axiomatized directly:
  zero, neg, add with the ring laws). The kernel's prelude contains
  the bijection with `nat × nat` and the ring axioms; everything
  else derives.
- **Fixed-width `uN` / `iN`** are characterized by their bijection
  with `nat / 2^N` (resp. `int / 2^N` with sign-bit interpretation),
  i.e. the standard wrapping arithmetic. Each op's recursion
  equations follow from the bijection.
- **`bits` and `bytes`** are characterized via their length / cons /
  index equations (essentially: they're free monoids over `bool`
  and `u8` respectively).

The kernel ships these axioms as a small *prelude Prop* every other
Prop has access to (architecturally: the prelude sits in the root
Context, see §2.5). The prelude is the kernel's only contribution
to the user's axiom set; everything else is the user's choice.

#### Trust surface

The trust surface added by the primitive system is:

1. **The `Prim` enum is complete and well-typed.** Each variant has
   a fixed HOL type the kernel knows, and the kernel rejects
   applications that don't match.
2. **`reduce` computes correctly.** The host's `i64::wrapping_add`
   implementation must match the abstract semantics in the
   `IntAdd` axiom, etc. This is the kernel's "trusted compute"
   layer.
3. **The prelude axioms are consistent.** Standard ring/order
   axioms; the kernel doesn't validate consistency, but the
   axiomatization is small enough to inspect by hand.

These are bounded — `Prim` has on the order of 100 variants and
each is mechanically traceable to its axiom and its reduce
implementation. Bugs here can produce wrong Thms (unlike bugs in
untrusted code), so the prelude + reduce machinery need careful
review.

### 3.5 Library types

Types that *aren't* kernel primitives (lists, options, pairs,
records, …) are defined in user-space via the usual HOL
type-defining-theorem mechanism. There is no kernel knowledge of
them. The kernel primitives of §3.2 (`int`, `nat`, `bits`, `bytes`,
the fixed-width integers) cover the cases where efficient FFI
matters; everything else goes through user-defined types.

`blob` in particular is a useful alias for `bytes` in the standard
library; it's not a kernel concept.

---

## 4. Union-Find: Equality without Closure or Search

The UF is the equality engine, but it does **not perform automatic
congruence closure**. Every union is explicit. The kernel's job is to
record and look up equalities the user has proved; *strategy* for how
to propagate congruences lives in untrusted code.

The same "no automatic work" discipline applies to assumption lookup
(§2.5 Context inspection API) — the kernel doesn't search for relevant
facts on the user's behalf.

### 4.1 Canonical IDs are arena-tagged

Each `TermUfEntry` stores `canonical: (Arc<Arena>, TermId)`. Same for
`TypeUfEntry`. To check "are `a` and `b` known equal in this arena's
view?", you walk both canonical chains and compare the final tuples
— pointer equality on the `Arc<Arena>` (via `Arc::ptr_eq`) plus
equality on the local ID.

This matters for the **diamond import** case:

```
       D
      / \
     B   C
      \ /
       A
```

Arena `A` imports both `B` and `C`, which both import `D`. If both
`B` and `C` import a term `x ∈ D`, then in `A`'s view both copies
have `canonical = (Arc<D>, x_id)` — and because both copies use the
*same* `Arc<D>` allocation, pointer equality holds and they regain
UF identity through their shared ancestor. But terms that
*originated* in `B` and `C` separately can only ever be compared
**structurally** in `A`, since `A` is not in a position to assume any
equality not explicitly proved.

This is what makes "(arena, index)" the correct canonical identity.
Using a bare ID would silently collapse the diamond and unsound unions
could leak across.

### 4.2 Equality predicates with explicit congruence levels

The kernel offers a small family of equality builtins, parameterised by
how much congruence reasoning to apply:

- **`eq_at_level(a, b, 0)`** — same arena-tagged canonical: walk both
  canonical chains; tuples must coincide.
- **`eq_at_level(a, b, k)`** for `k > 0` — succeeds if level-0 succeeds,
  *or* if both terms decompose into the same shape and their
  corresponding sub-children are `eq_at_level(_, _, k-1)`.
- **`eq_at_level(a, b, ∞)`** — exhaustive structural recursion.

The kernel doesn't pick a level; callers do.

The analogous family exists for types (`type_eq_at_level`) once the
type UF infrastructure is in place. At MVP these predicates exist but
only ever return non-trivial answers from structural identity, since
the kernel provides no rules to *introduce* type unions yet (§4.6).

### 4.3 Union primitives

Two writes:

- **`union(a, b)`** — caller has a proof (i.e. a `Thm`) that `a = b`.
  Merge `a` and `b`'s classes. Caller is responsible for closedness
  when this is a non-congruence equality.
- **`union_if_congruent_step(a, b)`** — LCF helper. If `a` and `b`
  decompose into the same shape and their corresponding children are
  *already* `eq_at_level(_, _, 0)`, performs the union. Otherwise
  returns failure.

`union_if_congruent_step` is the kernel's analog of HOL Light's
`MK_COMB`: it lets the user "ratchet up" one level of congruence
explicitly, given that the children are already known equal.

**No congruence closure** is automatic. There is no use-list maintained
by the kernel; the kernel doesn't track which `Comb`s point at which
children for the purposes of fanout. If you union `a` with `b` and
later want `f(a) = f(b)`, you call `union_if_congruent_step(f(a),
f(b))` explicitly.

### 4.4 Rewrite and copy

In addition to UF unions, the kernel exposes two **structural
manipulation** primitives:

- **`rewrite(t, new_def)`** — caller has either a proof of, or a UF
  witness for, `t = (the term defined by new_def)`. The kernel
  replaces `terms[t].definition` with `new_def`. After rewrite, any
  other term holding a child `TermRef::Local(t)` will see the new
  structural form.
- **`copy_term(t) -> TermId`** — allocate a fresh `TermId` with the
  *same* `TermDef` as `t` and place it in `t`'s UF class
  (`canonical = canonical_term(t)`, plus the inherited
  `bound_depth` and `has_free`). No new equality is introduced; this
  is just a new handle to the same class. Always sound — the kernel
  is doing an internal-only union of `t` with a freshly-allocated
  copy.

Why `rewrite`? Pure UF is enough for soundness but not always for
efficiency. If `Comb(f, x)` is known to equal `body`, every
traversal of the larger term will still hit `Comb(f, x)`
structurally; `union` only redirects the canonical, not the shape.
Rewriting `Comb(f, x)` to `body` outright makes subsequent
structural operations skip the application.

Why `copy_term`? It gives untrusted code (tactics, the user-space
`reduce` wrapper of §3.4) a way to set up a rewrite *target* without
disturbing the original handle: copy `t`, then rewrite the copy.
The kernel can recognise this idiom and fuse the two operations
into a single allocation. It is also useful for "naming" a
subterm — handing different bits of tactical code a unique `TermId`
they can mutate without contention.

Soundness for `rewrite` is preserved because:

- The kernel only accepts a rewrite when the new definition is in the
  same UF class as the old one (or comes with a Thm proving the
  equality).
- The UF state is updated accordingly so canonical lookups remain
  consistent.

Both primitives are expected to be used sparingly — most proof code
should just `union`. They are for hot paths and for explicit
canonicalisation by tactics.

### 4.5 Why no closure or search?

Three reasons:

1. **Performance is the user's call.** Congruence closure and fact
   search are sometimes exactly what you want and sometimes ruinously
   expensive. Putting them in the kernel commits everyone to one
   policy.
2. **The trust surface is smaller.** No use-lists, no propagation
   queues, no invariants for "if X changes the canonical of Y, the
   use-list must be visited." `union(a, b)` is a single write.
3. **Diamond-import correctness is easier.** With explicit unions, the
   kernel never has to ask "should I propagate this fact across an
   arena boundary?" — the answer is always *no, unless the user
   explicitly does so*.

Library code on top of the kernel can implement closure strategies
and fact-search strategies as untrusted utilities.

### 4.6 Type union-find as derived-equality cache

The arena's `uf_types` mirrors `uf_terms` structurally. The kernel
exposes `type_eq_at_level(a, b, k)` predicates analogous to the term
side.

It is **purely a cache for derived equalities** that fall out of
structural reasoning:

- **Foreign-import propagation.** Importing the *same* type from a
  shared ancestor arena makes both copies share a canonical
  (`(Arc<Arena>, TypeId)` of the source; pointer-equal because they
  hold the same `Arc` allocation).
- **Congruence steps.** If `Tyapp(f, [a₁, …, aₙ])` and `Tyapp(f, [b₁,
  …, bₙ])` have all `aᵢ` known canonically equal, the kernel can
  union the two applications via the type analog of
  `union_if_congruent_step`.

There is **no kernel rule** to introduce arbitrary type unions — no
analog of `union(a, b)` taking a "proof" of `a = b` at the type
level, because we deliberately do not have a type-equality proposition
in the logic. Type equalities at this level are only ever structural
or congruential, never propositional. This avoids the typing-rule
complications of user-driven type isomorphisms (a term well-typed
under one set of type equalities is generally ill-typed under
another).

Isomorphisms between *types* — what you actually want for
content-addressed types and for importing object-logic theorems —
happen at the **term level**, via bijection axioms on opaque types
declared through the concept system (§6.4 and §7.4). The type UF
stays purely structural.

---

## 5. Inference Rules

The kernel provides:

### 5.1 HOL primitive rules

All ten HOL Light rules, adapted to mutate an owned `Thm`:

| Rule | Operates on |
|---|---|
| REFL | `&mut Thm` (add a fresh `tm = tm`) |
| TRANS | `&mut Thm`, takes another `&Thm` |
| MK_COMB | `&mut Thm`, takes another `&Thm` — implemented in terms of `union_if_congruent_step` |
| ABS | `&mut Thm`, fresh-var name |
| BETA | `&mut Thm` |
| ASSUME | constructs a new Thm |
| EQ_MP | `&mut Thm`, takes another `&Thm` |
| DEDUCT_ANTISYM | `&mut Thm`, takes another `&Thm` |
| INST | `&mut Thm` |
| INST_TYPE | `&mut Thm` |

Each rule grows the arena (appending new terms/types) and calls
`union` on the UF when it produces a new equality. Where a rule needs
to combine two theorems' arenas, it does so via the foreign-import
mechanism.

### 5.2 Assumption-manipulation rules

The two non-HOL inferences this kernel adds:

- **add-assumption** — produce a Thm whose conclusion is conditional
  on a new assumption.
- **assumption-eliminates-false** — if an assumption `A` (a Prop) can
  derive `false = true` via the kernel's rules, then `not A` becomes
  a `Thm`.

### 5.3 Definitions

Standard `new_basic_definition` and `new_basic_type_definition` from
HOL Light, with the twist that the resulting Thm goes into the
*Context*, not into a kernel-global axiom list. The kernel keeps no
axiom list at all.

---

## 6. Concepts

A **concept** is a polymorphic constant family

```
c[α₁, …, αₙ] : α₁ → ⋯ → αₙ → bool
```

Each type-instantiation `c[α]` is a distinct HOL constant. From the
logic's point of view, concepts are just ordinary HOL constants — no
side table, no special term constructor, no special equality logic.
What makes them concepts is the **API for setting their theory**.

### 6.1 The root concept and anonymous concepts

The kernel ships **exactly one named concept: the root concept**. Its
handle is the kernel's authority root — it's how the kernel decides
who may write to which sub-namespaces.

Everyone else gets **anonymous** concepts:

- `kernel.declare_anonymous_concept(kind) -> ConceptHandle` — returns a
  capability for a fresh, unnamed concept.
- Anonymous concepts **cannot be serialised** — there's nothing to
  name them by.

For **serialisable / cross-process** concepts, the user goes through
the root concept's naming protocol. We start with anonymous concepts
only; the naming protocol lands in a later phase. The expected shape:

> There is one root concept. Every other 'named' concept is just a
> partial application of the root: `rootConcept(name, args)` where
> `name` is a `bits` value. Whoever holds the capability for a
> particular `name` prefix can write theory axioms within that
> sub-namespace.

For MVP, only anonymous concepts exist. Naming is deferred.

### 6.2 Theory axioms

A theory axiom is a `Prop` whose conclusion has the shape

```
P₁(…) ∧ ⋯ ∧ Pₖ(…)  ⇒  c[α](t₁, …, tₙ) = true
```

The premises and `tᵢ`s are arbitrary HOL terms; premises may reference
*other* concepts, equalities, free variables — anything the kernel can
express.

`handle.add_theory_axiom(prop)` checks the conclusion shape and
accepts `prop` as a member of `c`'s theory.

Soundness is preserved because for *any* theory of this shape, the
trivial model `c[α] = (λx₁…xₙ. true)` satisfies every axiom. The owner
is therefore choosing the strongest possible theory (everything is
`true`), restricted only by the premises they attach. Users of `c`
get exactly what the owner has declared and what they assume about it.

Notable cases:

- **`attest()`** is the degenerate nullary axiom `c[] = true`.
- **Point observations** (`c[α](a, b) = true`) are axioms with no
  premises.
- **Universal regions** (`∀x. c[α](x) = true`) are axioms with bound
  variables in the conclusion.

The `enter()` sub-capability (give me a handle to write only to
`c[α, β]` for fixed `β`) is **not** part of the trusted core. It lives
in an untrusted library.

### 6.3 Observations as UF unions

Once a theory axiom of the form `c[α](t₁, …, tₙ) = true` enters scope,
the kernel can immediately `union(c[α](t₁, …, tₙ), True)` in the UF.
From then on, equality queries on that term are O(1) at level 0.

Observations are structurally indistinguishable from "normal"
equalities like `(1 + 1) = 2`. The UF doesn't track which unions came
from concept theory.

### 6.4 Concept-owned type hierarchy

In addition to the constant family `c[α₁, …, αₙ]`, every concept `c`
implicitly owns an **infinite hierarchy of opaque types**:

```
conceptType[c, s₁, …, sₙ]
```

where `s₁, …, sₙ` are bit-string labels. For each label sequence,
this is a fresh opaque type constructor whose **declaration** is
owned by `c` — only the holder of `c`'s ConceptHandle can declare
that a particular `conceptType[c, s₁, …, sₙ]` is in scope. (For
implementation purposes the type lives in the user-side TypeName
namespace, but its identity and ownership flow through the concept.)

`conceptType` is **literally just opaque type declarations**. The
kernel attaches no built-in semantics: declared conceptTypes have no
inhabitants the kernel knows about, no relation to any other type,
and no relation to hashing, content addressing, or any external
naming scheme. The labels `s₁, …, sₙ` are just bit strings as far as
the kernel cares.

**The owner cannot assert anything about a `conceptType`** — owner
authority is restricted to declaring that the type exists (and
declaring concept *constant* family theory via §6.2). Any
*claim* about a conceptType — that it's nonempty, that it's in
bijection with some other type, that it's a subtype, anything —
enters as a **user-side assumption in the Context**, no different
from any other trust assumption.

This is the same shape as concepts themselves: just as the owner of
`c` doesn't make `c` *true* (they declare axioms saying when it's
true; everyone else assumes whatever they want), the owner of `c`
doesn't give `conceptType[c, …]` any structure — they just say it
exists, and the user assumes whatever they want about it.

Why have owner-declared types at all, then, rather than letting
anyone declare any opaque type? Because ownership is what makes the
type **named** in a non-conflicting way: two parties working
independently won't accidentally pick the same labels under
different concepts. The hierarchy is essentially a namespace
mechanism for opaque types.

Downstream uses of this primitive include content addressing (§7.4),
but those are uses built on top of the mechanism, not the
mechanism's purpose.

---

## 7. Definitions and the Outside-the-Kernel Store

### 7.1 Definitions are just (arena, index)

A HOL definition `c = body` is structurally just a Thm of the form
`Const(c, ty) = body` whose `body` lives in some arena. To "use" the
definition without expanding it, you reference the constant by name. To
"unfold" it, you produce a Thm `c = body` from your kernel's
definitional theorem store and apply EQ_MP / TRANS / etc.

This means the foreign-import mechanism doubles as the import-a-
definition mechanism. If arena `D` declares constant `c` and its
definition theorem `|- c = body`, then arena `A` importing `D` gets
both `c` and the option to unfold it on demand. If `A` doesn't need
the body, it never has to materialise `body`'s structural form — `A`
just references `(D, c_id)`.

### 7.2 Content addressing is entirely outside the kernel

The kernel has **no knowledge** of hashing, of any content-addressable
store, of `O256`, or of any specific naming scheme for arenas. From
the kernel's view, foreign imports are `Arc<Arena>` values that
arrived from somewhere — that "somewhere" is the runtime's
responsibility.

The runtime around the kernel may:

- Hash a frozen arena's bytes and store it in a CAS.
- Look up arenas by hash.
- Materialise a `BitsHashed`-equivalent reference as actual bytes by
  consulting the store.

But these are *runtime* actions on opaque byte buffers. They never
enter the kernel's type theory. If you want to **talk about** a hash
inside HOL, you build a `bits` term holding the hash bytes, and let
user-written concept theory (e.g. `storeContains`) relate that `bits`
value to the bytes it names. The kernel sees only the bits.

### 7.3 The "definition plus facts, without the body" pattern

Recipe for "I want to refer to `c` and use a few of its theorems
without loading its body":

1. Arena `D₀` declares constant `c`, gives its type, and proves a
   handful of headline theorems about it.
2. Arena `D₁` extends `D₀` with the actual definition theorem
   `|- c = body` plus everything that depends on the body.
3. A consumer imports `D₀` only; `c` is in scope, its headline
   theorems are in scope, but `body` is never materialised.
4. If the consumer later needs the body, it imports `D₁` (which
   foreign-imports `D₀`, so identities line up).

The kernel doesn't enforce this split — it's just a pattern enabled
by the foreign-import / canonical-arena-id machinery.

### 7.4 Content-addressed types via concept-owned bijections

Content addressing of types reuses the concept-owned type hierarchy
(§6.4): a "content-addressed type" is a `conceptType[c, hash]`
declared under some concept `c`, together with a **user-side
trust assumption** in the Context that asserts `conceptType[c,
hash] ≅ <spec>` for some HOL type expression `<spec>`.

The kernel itself does not endorse the bijection — declaring
`conceptType[c, hash]` and assuming `conceptType[c, hash] ≅ <spec>`
are two distinct operations: the owner of `c` does the first; the
user does the second by adding the bijection to their root Context.

To unfold a content-addressed type to its target, the user applies
the bijection assumption (an ordinary HOL `∃` statement; elimination
via Skolemisation gives `abs` and `rep` functions). To re-fold,
apply `abs`. No kernel knowledge of hashing or content addressing is
involved — the `hash` value is just a `bits` label chosen by the
user.

For complex type expressions, the user chains bijections:
`conceptType[c, parentHash] ≅ Tyapp(F, [conceptType[c, child1Hash],
conceptType[c, child2Hash]])`, then unfolds children separately as
needed. Each step is an explicit `∃`-elimination — there is no
automatic unfolding.

This is **extremely explicit**, and we accept that, because complex
meta-level proofs aren't the kernel's job: they belong in object
logics (Isabelle/HOL, etc.). The kernel's content-addressed types
exist primarily to support importing *batches of object-logic
theorems* under an assumption like "object logic `L` is sound" —
the import surface uses a uniform translation pattern, not ad-hoc
proofs.

### 7.5 Content-addressed function values (future direction)

For content-addressable *function values*, the eventual design
direction is to combine §7.4 with Hilbert choice:

- Declare a `conceptType[c, hash]`.
- Assert that it's a singleton subtype of `A → B` carved out by some
  spec `P` — i.e., bijection with `{ x : A → B | spec(x) }`.
- The function value is `f = ε x. x ∈ conceptType[c, hash]`.

A "content-addressed function" is then a `(spec_hash, type, f)`
triple. Consumers verify `spec_hash` matches the spec they expect
without sharing any structural representation of the function term.
This is not MVP work.

### 7.6 Standard-library concept: the store

The content-addressed store is a *standard-library concept*, not a
kernel feature.

```
storeContains : bits → bits → bool
```

`storeContains(name, blob)` is a concept owned by the store's
implementer. Its theory (axioms with conclusion `storeContains(…) =
true`) is whatever the store's owner declares. Users add trust
assumptions like:

- `∀ b. storeContains(hash(b), b) = true` — every blob is named by its
  content hash.
- `∀ h b₁ b₂. storeContains(h, b₁) ∧ storeContains(h, b₂) ⇒ b₁ = b₂`
  — no collisions.

The `hash` function above is itself a HOL constant whose properties
live in further user assumptions. The kernel doesn't know BLAKE3, or
any hash function, at all.

---

## 8. Serialisation

Each `Prop` has a flat byte serialisation. Deserialisation yields an
**untrusted** Prop — concretely, in the phantom-tag scheme, a
`Prop<Untrusted>`.

An untrusted Prop is always safely **embeddable as a HOL `bool` term**
(just structural decomposition; no soundness risk). Lifting an
untrusted Prop to a Thm requires either:

- A concept observation firing (the runtime asserts truth via a
  concept), or
- An explicit user trust assumption discharged by the user.

The deserialisation path itself never produces a `Thm` directly.

Anonymous concepts are **not serialisable** — they have no name. The
root-concept / named-concept design (§6.1) is the road to serialisable
cross-process facts.

The Context-as-bool and Prop-as-bool operations (§2.5) interact with
serialisation in an interesting way: a deserialised Prop's
*conclusion-as-bool* form can be talked about even before the Prop
itself is reified into a Thm. This is what lets the
`isValidSignature(key, sig, serialise(pred))` pattern work — we can
state the signature relation in HOL terms without first trusting the
deserialised Prop.

---

## 9. Soundness Story

The kernel's soundness reduces to seven invariants:

1. **Thm construction is kernel-only.** All inference rules are sound
   in plain HOL.
2. **No automatic congruence closure.** Every UF union either comes
   from a Thm or from explicit `union_if_congruent_step` calls.
3. **No automatic search.** The Context API exposes what's there for
   inspection but never volunteers a fact. Users discharge nested
   assumption Props' contexts explicitly before importing facts from
   them.
4. **Canonical identity is arena-aware.** Two terms (or types) in
   different arenas with the same `TermId` (or `TypeId`) are not
   assumed equal; the canonical tuple `(arena-ref, TermId)` (or
   `(arena-ref, TypeId)`) is what matters — identity is by pointer
   (`Arc::ptr_eq` for stored `Arc<Arena>`, `std::ptr::eq` for
   borrowed `&Arena`, equivalent across both), never by content.
5. **Concept theory axioms have the shape `… ⇒ c[α](…) = true`.**
   This applies only to the constant family side; the kernel checks
   the conclusion shape and accepts the axiom. The trivial model
   (`c` is always true) satisfies every such theory. The kernel does
   *not* accept any owner-asserted axiom about a `conceptType` —
   conceptTypes are pure opaque declarations, and any claim about
   them enters as a normal user-side assumption in the Context.
6. **No type-equality propositions.** The type UF caches derived
   equalities (foreign-import propagation, congruence) only. Type
   isomorphisms enter at the term level via bijection axioms — they
   never become silent type-level identifications.
7. **Trust enters only via the root Context.** Anything the user
   wants to believe is an explicit `Prop` they added to the Context.
   The kernel never silently trusts a runtime, a key, or a signature.

Anything outside these invariants — tactics, decision procedures, WASM
modules, the convenience `Goal` type, the `enter()` sub-capability,
content-addressed extraction, signed import, congruence-closure
strategies, assumption-search strategies — is **untrusted**. Bugs in
untrusted code can produce wrong answers but cannot produce wrong
Thms.

---

## 10. Glossary

- **Arena** — pool of types, terms, bitvectors, plus term UF and type
  UF state. SMT-analogously, a *clause*: a self-contained line of
  local reasoning.
- **Arena identity** — by pointer: two arena references are the same
  arena iff they point to the same allocation. Stored references are
  `Arc<Arena>` (identity via `Arc::ptr_eq`); ephemeral read paths use
  `&'a Arena` (identity via `std::ptr::eq`); the two forms are
  identity-equivalent. No kernel-issued arena number; the arena *is*
  its allocation.
- **Builtin** — TermDef/TypeDef enum variant supplied by the kernel
  (`Bool`, `Bits`, `Fun`, `True`, `False`, `Eq`, `Bits(_)`). Not in
  any user namespace. Pattern-matched alongside the structural
  variants — no separate well-known-name table.
- **Concept** — polymorphic constant family whose theory is set by a
  capability holder; the kernel's only extension point.
- **Context** — kernel-encapsulated assumption store with an
  inspection API; attached to every Prop. SMT-analogously, a
  *formula*: the global conjunction of assertions.
- **Observation** — a particular point-fact `c[α](t₁, …, tₙ) = true`,
  represented as a theory axiom or directly as a UF union.
- **Owner** — holder of a `ConceptHandle`. The capability granting
  authority to write to a concept's theory.
- **Prop** — structured proposition: `(arena, context, concl)`. Not
  necessarily true. SMT-analogously, a (formula, clause) pair: the
  Context is the formula (global assertions), the Arena is the
  clause (local reasoning).
- **Rewrite** — kernel primitive that mutates a term's structural form
  in place to a provably-equal one. Optimisation, not soundness.
- **Root concept** — the kernel's one built-in concept; the authority
  root for naming sub-concepts.
- **Theory axiom** — a Prop with conclusion `… ⇒ c[α](…) = true`,
  contributed by the owner of `c`.
- **Thm** — a Prop the kernel has validated. Compile-time-only
  distinction from Prop.
- **Trust assumption** — a Prop in the root Context relating concepts
  to facts the kernel itself can't observe.
- **Type UF** — union-find on types; purely a cache for derived
  equalities (foreign-import propagation, congruence). No primitives
  to introduce arbitrary type unions; isomorphisms happen at the
  term level via bijection axioms on opaque types (§6.4, §7.4).
- **conceptType** — opaque type constructor owned by a concept. The
  concept's owner can declare instances `conceptType[c, s₁, …, sₙ]`
  and assert bijection-existence axioms about them.
- **`union_if_congruent_step`** — the LCF-style helper that performs
  one level of congruence-based union explicitly. The kernel's
  substitute for automatic closure.

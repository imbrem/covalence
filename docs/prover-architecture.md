# Prover Architecture

This document describes the architecture of the Covalence prover kernel — a
HOL-based metalogic intended to glue together object logics, evaluators, and
cryptographic trust schemes without baking any of them into the kernel itself.

It is the canonical reference for the kernel's design. Implementation details
that live in code (file layout, exact function signatures) are out of scope
here.

For the staged build-out, see [`prover-mvp-plan.md`](./prover-mvp-plan.md).

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
  bitvectors: Vec<Bits>,             // side table for bit strings too large to inline
  uf_terms: Vec<TermUfEntry>,        // one per term, mutable
  uf_types: Vec<TypeUfEntry>,        // one per type, mutable (see §4.6)
  imports: Vec<Arc<Arena>>,          // frozen arenas this one references
  // ...
}

TermUfEntry {
  canonical: (Arc<Arena>, TermId),   // arena-aware canonical pointer (see §4.1)
  closed: bool,                      // no Free vars or dangling Bound reachable
}

TypeUfEntry {
  canonical: (Arc<Arena>, TypeId),   // arena-aware canonical pointer
}
```

**Arena identity is by pointer**: there is no kernel-assigned arena
identifier. Two canonical IDs `(arena_a, id_a)` and `(arena_b, id_b)`
are equal iff `arena_a` and `arena_b` point at the *same allocation*
(pointer equality via `Arc::ptr_eq`) and `id_a == id_b`. There is no
"arena number" table; identity is the arena itself.

This matters in subtle ways:

- Cloning a frozen arena's `Arc` and storing it in two places leaves
  identity unchanged — both are still the same arena.
- Two structurally-identical arenas that happen to share content but
  live at different allocations are **not** the same arena; their
  contents are compared structurally, never canonically.

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

There is **one** `TermDef` enum, with one variant per kind of term —
no out-of-band tables of "well-known" terms, no magic name IDs, no
sentinel constants. Terms use **de Bruijn indices for bound variables
+ named free variables**:

```rust
TermDef =
  // -- general shapes --
  | Bound(u32)                       // de Bruijn index
  | Free(VarName, TypeRef)           // named free variable, typed
  | Const(ConstName, TypeRef)        // user-declared constant at an instance
  | Comb(TermRef, TermRef)           // application
  | Abs(VarName, TypeRef, TermRef)   // binder; VarName is a hint only
  // -- builtin variants (see §3.2 for the rationale) --
  | True                             // the boolean true
  | False                            // the boolean false
  | Eq(TermRef, TermRef)             // primitive polymorphic equality
  | Bits(BitsValue)                  // primitive bit string

BitsValue =
  | Inline([u8; N])                  // short literal stored in-line
  | Indirect(BitsId)                 // index into arena.bitvectors

TermRef = Local(TermId) | Foreign(Arc<Arena>, TermId)
TypeRef = Local(TypeId) | Foreign(Arc<Arena>, TypeId)
```

Likewise, `TypeDef` is one enum whose variants are listed in §3.2.
There is no separate "builtin type table" alongside it — `Bool`,
`Bits`, `Fun`, `TVar`, `Tyapp` are all just `TypeDef` variants.

Bound-var substitution doesn't need any alpha-renaming dance; structural
equality of `TermDef`s already gives α-equivalence.

A `TermRef`/`TypeRef` is the type used for child links. `Local(_)`
points to this arena's table; `Foreign(arena, _)` points into the
arena handed in via the `Arc<Arena>`. Equality checks transparently
follow either.

### 3.2 Builtins

Builtins are **TermDef/TypeDef enum variants** — not entries in user
namespaces, not magic constants in a side table, not sentinel name
IDs. They appear in the same enum as everything else; an inference
rule that pattern-matches on `TermDef` sees them right next to
`Bound`, `Comb`, etc.

This keeps the kernel code simple (no "is this name the well-known
`bool_id`?" lookups), and keeps the logic minimal at the same time
(builtins are exactly those things the kernel needs to *construct*
intrinsically — `bool` as a type, `True`/`False`/`Eq` because the
logic is built on equality, and `bits` because the arena needs a
primitive infinite type for bit strings).

**TypeDef variants in full:**

| Variant | Logical type |
|---|---|
| `Bool` | `bool` (builtin) |
| `Bits` | `bits` (builtin — replaces HOL Light's `ind` as the primitive infinite type) |
| `Fun(TypeRef, TypeRef)` | `α → β` (builtin) |
| `TVar(TypeVarId)` | polymorphic type variable |
| `Tyapp(TypeName, Vec<TypeRef>)` | user-declared type constructor instance (the only path through the user-side TypeName namespace) |

**TermDef variants in full** (combining §3.1's list with the builtins,
since they all live in the one enum):

| Variant | What it represents | Source |
|---|---|---|
| `Bound(u32)` | de Bruijn index | structural |
| `Free(VarName, TypeRef)` | free variable | user VarName |
| `Const(ConstName, TypeRef)` | constant at an instance | user ConstName |
| `Comb(TermRef, TermRef)` | application | structural |
| `Abs(VarName, TypeRef, TermRef)` | binder | structural |
| `True`, `False` | the booleans | **builtin** |
| `Eq(TermRef, TermRef)` | polymorphic equality | **builtin** |
| `Bits(BitsValue)` | bit string literal | **builtin** |

We keep `True`/`False` baked in even though HOL Light defines them —
the goal is to simplify the *code*, not the typing rules. A baked-in
`True` lets the bootstrap not have to thread Hilbert choice into the
very first definitions.

**`Bits` representation.** `BitsValue` has two cases chosen at
insertion time, both producing the same logical value:

- **`Inline(bytes)`** — the bit string is stored directly inside the
  TermDef. Cheap, no extra indirection. Used for short literals
  (cut-off is an implementation knob; e.g. 256 bits).
- **`Indirect(BitsId)`** — the bit string lives in the arena's
  `bitvectors` table at `BitsId`. Used for longer literals so we
  don't inflate every TermDef-sized object.

Both representations are kernel-internal and equivalent at every
level of the equality predicates (§4). The kernel never talks to a
content store about them — `Indirect` is just an internal arena
index.

User-defined constants (`Const(name, ty)`) and user-defined type
constructors (`Tyapp(name, args)`) are the only TermDef/TypeDef
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

### 3.4 Library types

Standard-library types (`blob`, `i32`, `i64`, `nat`, `nat list`, …) are
defined on top of `bits` via the usual HOL type-defining-theorem
mechanism. There is no special-case kernel knowledge of them.

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

### 4.4 Rewrite

In addition to UF unions, the kernel exposes a **rewrite** primitive
that mutates a term's structural form in place:

- **`rewrite(t, new_def)`** — caller has either a proof of, or a UF
  witness for, `t = (the term defined by new_def)`. The kernel
  replaces `terms[t].definition` with `new_def`. After rewrite, any
  other term holding a child `TermRef::Local(t)` will see the new
  structural form.

Why have this in addition to `union`? Pure UF is enough for soundness
but not always for efficiency. If `Comb(f, x)` is known to equal
`body`, every traversal of the larger term will still hit `Comb(f,
x)` structurally; `union` only redirects the canonical, not the
shape. Rewriting `Comb(f, x)` to `body` outright makes subsequent
structural operations skip the application.

Soundness is preserved because:

- The kernel only accepts a rewrite when the new definition is in the
  same UF class as the old one (or comes with a Thm proving the
  equality).
- The UF state is updated accordingly so canonical lookups remain
  consistent.

Rewrite is a kernel primitive but expected to be used sparingly — most
proof code should just `union`. Rewrite is for hot paths and for
explicit canonicalisation by tactics.

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
   assumed equal; the canonical tuple `(Arc<Arena>, TermId)` (or
   `(Arc<Arena>, TypeId)`) is what matters — identity is by
   `Arc::ptr_eq`, never by content.
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
- **Arena identity** — by pointer: two `Arc<Arena>` are the same
  arena iff `Arc::ptr_eq` holds. No kernel-issued arena number; the
  arena *is* its allocation.
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

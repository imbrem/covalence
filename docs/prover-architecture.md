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
in the root [Context](#26-context-stack)), tactics, proof terms, or
automatic equality reasoning beyond what the inference rules do explicitly.

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
they're TermDef/TypeDef variants directly (§3.2). This makes the most
common terms (equality, true/false, bits literals, function types)
allocation-cheap and gives the kernel a precise list of what it admits
without consulting any table.

### 2.2 Arena

An **Arena** is an immutable, append-only pool of types and terms, plus
*mutable* union-find state stored alongside.

```
Arena {
  id: ArenaId,                    // kernel-assigned, unique
  types: Vec<TypeDef>,            // immutable, indexed by TypeId
  terms: Vec<TermDef>,            // immutable, indexed by TermId
  uf: Vec<UfEntry>,               // one per term, mutable
  imports: Vec<Arc<Arena>>,       // frozen arenas this one references
  // ...
}

UfEntry {
  canonical: (ArenaId, TermId),   // arena-aware canonical pointer
  closed: bool,                   // no Free vars or dangling Bound reachable
}
```

Key properties:

- **TermDef and TypeDef are immutable** once allocated. The arena is
  append-only at the structural level. Equalities live entirely in the
  UF state.
- **Canonical IDs are arena-aware tuples `(ArenaId, TermId)`.** A
  `TermId` alone is *not* a canonical name across arenas — see §4 for
  why.
- **Imports** are `Arc`'d frozen arenas this arena may reference (foreign
  imports). Terms can reach across via `Comb`/`Abs` children pointing at
  imported terms; equalities cannot, except by manual user-driven
  unions inside this arena.
- **Closed flag** is computed once at term insertion. Cheaper than
  walking the term every time we need to know.

#### Foreign imports

Arenas can **freeze**, becoming `Arc<Arena>` and read-only. Other arenas
hold these as `Arc`'d entries in `imports`. To reference a term in a
frozen arena, the local arena either:

- Allocates a `Comb`/`Abs` whose child is a `Foreign(arena_id, term_id)`
  handle (see TermDef in §3.2), or
- Re-allocates the term structurally in the local arena, importing only
  the part it needs.

Unfreezing clones the arena into a fresh mutable one with the same
indices.

#### Fresh variables

Both arenas and theorems can mint fresh free-variable names that are
guaranteed not to clash with anything in the local arena or its
imports. This is the substitute for ad-hoc gensyms.

### 2.3 Prop

A **Prop** is a `(arena, assumptions)` pair, where:

- `arena` is the Arena above.
- `assumptions: Vec<Arc<Prop>>` lists other Props this one depends on.

A Prop is **not** by itself a theorem — it's just a structured
proposition. The "conclusion" is whatever the arena's distinguished
`concl: TermId` points at, and may be any HOL term (typically of type
`bool`).

Prop is `Clone` (cheap via `Arc` sharing of assumptions; the owning
arena is per-Prop).

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

### 2.5 Context Stack

A **Context** is `{ assumptions: Vec<Arc<Prop>>, parent: Option<Arc<Context>> }`.
It's a recursive linked list of assumption layers; pushing a context is
cheap. Looking up "is `p` an active assumption?" walks the chain.

Thms hold `Arc<Context>`. The **root** Context contains the user's
chosen trust base — anything the kernel would have called an "axiom"
in classical HOL is just a Prop in the root Context here. The kernel
itself adds nothing to any Context.

### 2.6 Summary

| Object | Owns | References |
|---|---|---|
| `Arena` | immutable types/terms + mutable UF state | frozen `Arc<Arena>`s as imports |
| `Prop` | one `Arena` | `Vec<Arc<Prop>>` assumptions |
| `Thm` | a `Prop` that the kernel has validated | `Arc<Context>` |
| `Context` | `Vec<Arc<Prop>>` | `Option<Arc<Context>>` parent |

---

## 3. Term Language

### 3.1 Locally nameless

Terms use **de Bruijn indices for bound variables + named free
variables**:

```rust
TermDef =
  | Bound(u32)                       // de Bruijn index
  | Free(VarNameId, TypeId)          // named free variable, typed
  | Const(ConstName, TypeId)         // user-declared constant at an instance
  | Comb(TermRef, TermRef)           // application
  | Abs(VarNameId, TypeId, TermRef)  // binder; VarNameId is a hint only
  // -- builtins (see §3.2) --
  | Eq(TermRef, TermRef)             // primitive equality
  | True                             // primitive
  | False                            // primitive
  | BitsLit(SmallBits)               // short bits literal, inline
  | BitsHashed(O256)                 // long bits, by content hash

TermRef = Local(TermId) | Foreign(ArenaId, TermId)
```

Bound-var substitution doesn't need any alpha-renaming dance; structural
equality of `TermDef`s already gives α-equivalence.

A `TermRef` is the type used for child links inside `Comb`, `Abs`, etc.
`Local(TermId)` points to this arena's `terms[id]`; `Foreign(a, id)`
points to `imports.find(a).terms[id]`. The two are interchangeable
operationally; equality checks transparently follow either.

### 3.2 Builtins

Builtins are **kernel-supplied** TermDef/TypeDef variants — not entries
in the user namespace.

**TypeDef builtins:**

| Variant | Logical type |
|---|---|
| `Bool` | `bool` |
| `Bits` | `bits` (replaces HOL Light's `ind` as the primitive infinite type) |
| `Fun(TypeRef, TypeRef)` | `α → β` |
| `TVar(TypeVarId)` | polymorphic type variable |
| `Tyapp(TypeName, Vec<TypeRef>)` | user-declared type constructor instance |

(TypeRef is the type analog of TermRef.)

**TermDef builtins:**

| Variant | What it represents |
|---|---|
| `Eq(a, b)` | `a = b` (polymorphic) |
| `True`, `False` | the booleans |
| `BitsLit(bits)` | bit string literal stored inline (≲ a few hundred bits) |
| `BitsHashed(O256)` | bit string stored by its content hash; the bytes live elsewhere |

`Eq`, `True`, `False` are baked in because (a) `=` is the only primitive
constant in HOL Light, and we keep that minimalism, (b) `True`/`False`
are constants of `Bool` that the kernel constructs natively — defining
them via Hilbert choice as HOL Light does would be a circular setup
problem when `Eq` is also a variant.

`BitsLit` vs `BitsHashed` is a **transparent representation
optimization**. Logically both denote a `bits` value; the kernel auto-
chooses based on length. `BitsHashed` lets us treat large blobs without
loading them — the bytes are fetched from outside the kernel when
actually needed (e.g. printing, equality up to the contents). Two
`BitsHashed(h)` with the same hash compare equal at level 1 (§4)
without loading anything. `BitsHashed` is also the only place the
kernel knowingly produces an `O256` — and even here, it's just a
referent, not a trust-bearing identity. The hash function itself
remains outside the kernel; the runtime decides how `BitsHashed(h)`
gets materialised.

User-defined constants (`Const(name, ty)`) and user-defined type
constructors (`Tyapp(name, args)`) are the only paths from the user-
side namespaces (§2.1) into TermDef/TypeDef. Everything else is either
a builtin variant or a structural form (`Comb`/`Abs`/`Bound`/`Free`).

### 3.3 Closed vs open terms

The kernel distinguishes **closed** (no `Free(_)` reachable, no dangling
`Bound(i)`) from **open** terms. Both can live in the arena. The
restriction is on **non-congruence unions** (§4):

- **Closed terms** can be unioned with anything they're proved equal to.
- **Open terms** can only acquire equalities via congruence — the user
  has to wrap them in a binder first to do nontrivial equality
  reasoning.

This is the kernel's way of refusing to commit to a "free variable
theory" (à la Isabelle/Pure's `vars` machinery). Open terms are kept
around for structural purposes (so you can build `Abs(_, _, body)` over
them); nontrivial equalities between them must be wrapped inside a
binder first.

The closed flag is stored on each `UfEntry` and set once at insertion
(constant time, since the constructor knows the children).

### 3.4 Library types

Standard-library types (`blob`, `i32`, `i64`, `nat`, `nat list`, …) are
defined on top of `bits` via the usual HOL type-defining-theorem
mechanism (see §7.4 for the content-addressed flavour). There is no
special-case kernel knowledge of them.

---

## 4. Union-Find: Equality without Closure

The UF is the equality engine, but it does **not perform automatic
congruence closure**. Every union is explicit. The kernel's job is to
record and look up equalities the user has proved; *strategy* for how
to propagate congruences lives in untrusted code.

### 4.1 Canonical IDs are arena-tagged

Each `UfEntry` stores `canonical: (ArenaId, TermId)`. To check
"are `a` and `b` known equal in this arena's view?", you walk both
canonical chains and compare the final tuples — including the arena
tag.

This matters for the **diamond import** case:

```
       D
      / \
     B   C
      \ /
       A
```

Arena `A` imports both `B` and `C`, which both import `D`. If both `B`
and `C` import a term `x ∈ D`, then in `A`'s view both copies have
`canonical = (D, x_id)` — they regain UF identity through their shared
ancestor. But terms that *originated* in `B` and `C` separately can
only ever be compared **structurally** in `A`, since `A` is not in a
position to assume any equality not explicitly proved.

This is what makes "(arena, index)" the correct canonical identity.
Using a bare `TermId` would silently collapse the diamond and unsound
unions could leak across.

### 4.2 Equality predicates with explicit congruence levels

The kernel offers a small family of equality builtins, parameterised by
how much congruence reasoning to apply:

- **`eq_at_level(a, b, 0)`** — same arena-tagged canonical: walk both
  canonical chains; tuples must coincide.
- **`eq_at_level(a, b, k)`** for `k > 0` — succeeds if level-0 succeeds,
  *or* if both terms decompose into the same shape and their
  corresponding sub-children are `eq_at_level(_, _, k-1)`.
- **`eq_at_level(a, b, ∞)`** — exhaustive structural recursion.

This subsumes both pure UF equality (level 0) and full structural
α-equivalence (level ∞), with intermediate levels useful as bounded
"how much congruence to try" budgets in user-written tactics.

The kernel doesn't pick a level; callers do.

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
`MK_COMB` rule: it lets the user "ratchet up" one level of congruence
explicitly, given that the children are already known equal.

**No congruence closure** is automatic. There is no use-list maintained
by the kernel; the kernel doesn't track which `Comb`s point at which
children for the purposes of fanout. If you union `a` with `b` and
later want `f(a) = f(b)`, you call `union_if_congruent_step(f(a),
f(b))` explicitly.

### 4.4 Why no closure?

Three reasons:

1. **Performance is the user's call.** Congruence closure is sometimes
   exactly what you want and sometimes ruinously expensive. Putting it
   in the kernel commits everyone to one policy.
2. **The trust surface is smaller.** No use-lists, no propagation
   queues, no invariants for "if X changes the canonical of Y, the
   use-list must be visited." `union(a, b)` is a single write.
3. **Diamond-import correctness is easier.** With explicit unions, the
   kernel never has to ask "should I propagate this fact across an
   arena boundary?" — the answer is always *no, unless the user
   explicitly does so*.

Library code on top of the kernel can implement closure strategies
(e.g. a `cogit-style` saturating loop) as an untrusted utility.

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

Each rule grows the arena (immutably appending new terms/types) and
calls `union` on the UF when it produces a new equality. Where a rule
needs to combine two theorems' arenas, it does so via the foreign-import
mechanism: the smaller of the two arenas is frozen and imported into the
larger one.

### 5.2 Assumption-manipulation rules

The two non-HOL inferences this kernel adds:

- **add-assumption** — produce a Thm whose conclusion is conditional
  on a new assumption.
- **assumption-eliminates-false** — if an assumption `A` (a Prop) can
  derive `false = true` via the kernel's rules, then `not A` becomes a
  `Thm`.

These are the assumption-stack counterparts of HOL's discharge/eliminate
patterns.

### 5.3 Definitions

Standard `new_basic_definition` and `new_basic_type_definition` from
HOL Light, with two twists:

- The resulting Thm goes into the *Context*, not into a kernel-global
  axiom list. The kernel keeps no axiom list at all.
- Type definitions can be content-addressed (§7.4 and §8) so that the
  same definition imported from two places is the same constant.

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
  capability for a fresh, unnamed concept. The handle is the only way
  to identify it.
- Anonymous concepts **cannot be serialised** — there's nothing to
  name them by. Their theory is in-memory only and dies with the
  process.
- They're the right primitive for short-lived facts (e.g. "the WASM
  module currently executing observed this tuple").

For **serialisable / cross-process** concepts, the user goes through
the root concept's naming protocol. We start with anonymous concepts
only; the naming protocol lands in a later phase. The expected shape:

> "There is one root concept. Every other 'named' concept is just a
> partial application of the root: `rootConcept(name, args)` where
> `name` is a `bits` value (typically a content hash of the
> sub-concept's declaration). Whoever holds the capability for a
> particular `name` prefix can write theory axioms within that
> sub-namespace."

This unifies "anyone can define a concept" with "the kernel decides
who writes where": there isn't a separate namespace system — there's
the one root concept, and naming is just type-parameter instantiation
in the right argument slot.

For MVP, only anonymous concepts exist. Naming is deferred.

### 6.2 Theory axioms

A theory axiom is a `Prop` whose conclusion has the shape

```
P₁(…) ∧ ⋯ ∧ Pₖ(…)  ⇒  c[α](t₁, …, tₙ) = true
```

The premises and `tᵢ`s are arbitrary HOL terms; premises may reference
*other* concepts, equalities, free variables — anything the kernel can
express.

`handle.add_theory_axiom(prop)` checks the conclusion shape (the
positive `c[α](…) = true` form, possibly under arbitrary premises) and
accepts `prop` as a member of `c`'s theory — that is, the Prop becomes
an assumption in the relevant Context.

Soundness is preserved because, for *any* theory of this shape, the
trivial model `c[α] = (λx₁…xₙ. true)` satisfies every axiom. The owner
is therefore choosing the strongest possible theory (everything is
`true`), restricted only by the premises they attach. Users of `c` get
exactly what the owner has declared and what they assume about it.

Notable cases:

- **`attest()`** is the degenerate nullary axiom `c[] = true`.
- **Point observations** (`c[α](a, b) = true`) are axioms with no
  premises.
- **Universal regions** (`∀x. c[α](x) = true`) are axioms with bound
  variables in the conclusion.

There is no separate side table of observations, no `attest_all`
primitive in the trusted kernel. Painting whole regions of a concept
*efficiently* (e.g. "for all `x : nat`, `c(x, 0) = true`") is supported
by adding a universally-quantified theory axiom — once it's in the
Context, the UF can resolve `c[nat](?, 0)`-shaped queries against it
trivially.

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

---

## 7. Definitions and Content Addressing

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

### 7.2 Content-addressed definitions

The kernel itself has no knowledge of hashing or the content store.
But we *do* want to be able to import a definition and some facts
about it without loading the entire defining arena. The mechanism:

- The defining arena, once frozen, can be content-addressed
  externally (the runtime hashes its bytes and stores it).
- Other arenas hold the source arena as `Arc<Arena>` plus the
  source's hash (which they treat as opaque, via the `BitsHashed`
  builtin if they want to manipulate it as a term).
- The runtime — *not* the kernel — knows how to fetch an arena by
  hash and materialise it as an `Arc<Arena>`.

This **does slightly break** the "content addressing is not special"
principle: the *runtime around the kernel* has to know how to fetch
arenas from a store. But the *kernel itself* still doesn't — it
receives `Arc<Arena>`s already loaded. From the kernel's view, an
imported arena is just an imported arena.

The `BitsHashed(O256)` builtin (§3.2) is what lets the kernel *talk
about* content hashes as `bits` values inside HOL terms, without
endorsing any particular hash function. The relationship between
`BitsHashed(h)` and the actual bytes it refers to is established
entirely by user-written theory axioms on the `storeContains` concept
(§7.5).

### 7.3 The mechanism for "definition plus facts, without the body"

Recipe for "I want to refer to `c` and use a few of its theorems
without loading its body":

1. Arena `D₀` declares constant `c`, gives its type, and proves a
   handful of headline theorems about it.
2. Arena `D₁` extends `D₀` with the actual definition theorem
   `|- c = body` plus everything that depends on the body.
3. A consumer imports `D₀` only; `c` is in scope, its headline
   theorems are in scope, but no `body` ever gets materialised.
4. If the consumer later needs the body, it imports `D₁` (which
   foreign-imports `D₀`, so identities line up).

The kernel doesn't enforce this split — it's just a pattern enabled
by the foreign-import / canonical-arena-id machinery.

### 7.4 Type definitions via subtype + spec

For content-addressable *functions*, the design direction is:

- Define a type `T = { x : A → B | spec(x) }` where `spec` uniquely
  determines a function.
- The spec is a closed `bool` term, hence content-addressable.
- Recover the function as `f = ε x. x ∈ T` (Hilbert choice). Since `T`
  is a singleton, `ε` picks the unique inhabitant.

A "content-addressed function" is then a `(spec_hash, T, f)` triple,
where the consumer can verify `spec_hash` matches the spec they expect
without having to know the function's HOL term form. Two consumers
referring to the same `spec_hash` agree on `f` extensionally without
sharing any structural representation.

This is **not in MVP**; it's the design direction for after we can
serialise theorems at all. The MVP uses the standard HOL definition
mechanism (no content-addressing of function values).

### 7.5 Standard-library concept: the store

The content-addressed store is a *standard-library concept*, not a
kernel feature.

```
storeContains : bits → bits → bool
```

`storeContains(name, blob)` is a concept owned by the store's
implementer. Its theory includes:

- `∀ b. storeContains(hash(b), b) = true` — every blob in the store
  is named by its content hash. (`hash` is itself a HOL constant
  whose properties live in further concept theory or user
  assumptions.)
- `∀ h b₁ b₂. storeContains(h, b₁) ∧ storeContains(h, b₂) ⇒ b₁ = b₂`
  — no collisions.

The kernel doesn't know what BLAKE3 is, or that `BitsHashed(h)` and
`storeContains(h, _)` ought to agree. That agreement is exactly the
theory the store owner declares.

---

## 8. Serialisation

Each `Prop` has a flat byte serialisation. Deserialisation yields an
**untrusted** Prop — concretely, in the phantom-tag scheme, a
`Prop<Untrusted>`.

An untrusted Prop is always safely **embeddable as a HOL `bool` term**
(just a structural decomposition; no soundness risk). Lifting an
untrusted Prop to a Thm requires either:

- A concept observation firing (the runtime asserts truth via a
  concept), or
- An explicit user trust assumption discharged by the user.

The deserialisation path itself never produces a `Thm` directly.

Anonymous concepts are **not serialisable** — they have no name. The
root-concept / named-concept design (§6.1) is the road to
serialisable cross-process facts.

---

## 9. Soundness Story

The kernel's soundness reduces to five invariants:

1. **Thm construction is kernel-only.** All inference rules are sound
   in plain HOL.
2. **No automatic congruence closure.** Every UF union either comes
   from a Thm or from explicit `union_if_congruent_step` calls that
   the user authored. The kernel never propagates equalities on its
   own.
3. **Canonical identity is arena-aware.** Two terms in different
   arenas with the same `TermId` are not assumed equal; the canonical
   tuple `(ArenaId, TermId)` is what matters. Diamond imports
   correctly regain identity only through shared ancestors.
4. **Concept theory axioms have the shape `… ⇒ c[α](…) = true`.**
   Every such theory is satisfied by the trivial model where `c` is
   always true.
5. **Trust enters only via the root Context.** Anything the user
   wants to believe is an explicit `Prop` they added to the Context.
   The kernel never silently trusts a runtime, a key, or a signature.

Anything outside these invariants — tactics, decision procedures, WASM
modules, the convenience `Goal` type, the `enter()` sub-capability,
content-addressed extraction, signed import, congruence-closure
strategies — is **untrusted**. Bugs in untrusted code can produce
wrong answers but cannot produce wrong Thms.

---

## 10. Glossary

- **Arena** — pool of types and terms (immutable) plus union-find
  state (mutable).
- **ArenaId** — unique identifier of an arena; part of every
  canonical-ID tuple.
- **Builtin** — kernel-supplied TermDef/TypeDef variant (e.g. `Eq`,
  `True`, `Bool`, `Bits`). Not in any user namespace.
- **Concept** — polymorphic constant family whose theory is set by a
  capability holder; the kernel's only extension point.
- **Context** — recursive stack of assumption Props attached to a Thm.
- **Observation** — a particular point-fact `c[α](t₁, …, tₙ) = true`,
  represented as a theory axiom or directly as a UF union.
- **Owner** — holder of a `ConceptHandle`. The capability granting
  authority to write to a concept's theory.
- **Prop** — structured proposition: arena + assumption vector. Not
  necessarily true.
- **Root concept** — the kernel's one built-in concept; the authority
  root for naming sub-concepts.
- **Theory axiom** — a Prop with conclusion `… ⇒ c[α](…) = true`,
  contributed by the owner of `c`.
- **Thm** — a Prop the kernel has validated. Compile-time-only
  distinction from Prop.
- **Trust assumption** — a Prop in the root Context relating concepts
  to facts the kernel itself can't observe (e.g. "this signature
  scheme is unforgeable").
- **`union_if_congruent_step`** — the LCF-style helper that performs
  one level of congruence-based union explicitly. The kernel's
  substitute for automatic closure.

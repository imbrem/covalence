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
in the root [Context](#context-stack)), tactics, or proof terms.

---

## 2. Core Data Model

### 2.1 Arena

An **Arena** is a pool of types, terms, and theorems indexed by `Copy` u32
handles (`TypeId`, `TermId`, `ThmId`). Each term has two pieces of state:

```
term_id → { canonical: TermId, definition: TermDef }
```

- `canonical` is the union-find representative for this term's equivalence
  class.
- `definition` is the structural decomposition (`Var`, `Const`, `Comb`,
  `Abs`). `definition` is **not required to be canonical** — that is, the
  child handles inside a `Comb(f, x)` may point at non-canonical terms.
  This lets us soundly *rewrite* terms in place by replacing a definition
  with a structurally-different but provably-equal one.

See [§3 Term Language](#3-term-language) and [§4 Union-Find](#4-union-find)
for what's stored and how.

#### Foreign imports

Arenas can **freeze**, after which they're shareable read-only via `Arc`.
Other arenas can hold immutable references to frozen arenas and import
terms from them via **tagged handles**:

```
TermRef = Local(TermId) | Foreign(ArenaId, TermId)
```

A `Thm` always lives over one *owning* arena plus zero or more frozen
imported arenas it references. Standard libraries live in well-known
frozen arenas and are imported by hash. Unfreezing an arena clones it
into a fresh mutable arena with the same indices.

#### Fresh variables

Both arenas and theorems can mint fresh free-variable names that are
guaranteed not to clash with anything in their imports. This is the
substitute for ad-hoc gensyms.

### 2.2 Prop

A **Prop** is a `(arena, assumptions)` pair, where:

- `arena` is the Arena above.
- `assumptions: Vec<Arc<Prop>>` lists other Props this one depends on.

A Prop is **not** by itself a theorem — it's just a structured proposition.
The "conclusion" is whatever the arena's distinguished `concl: TermId`
points at, and may be any HOL term (typically of type `bool`).

Prop is `Clone` (cheap, via `Arc` sharing of the assumption vec — the
arena itself is owned per Prop, with frozen imports shared).

### 2.3 Thm

A **Thm** is a compile-time-tagged Prop the kernel has stamped *true*.
Construction is kernel-only. There is no runtime "is_this_a_thm" flag:
the type system guarantees a `Thm` came out of an inference rule.

Choose between newtype (`struct Thm(Prop)`, private fields, `Deref` to
`&Prop`) and phantom-tag (`Prop<Verified>` vs `Prop<Untrusted>`) at
implementation time. Both give equivalent guarantees; the phantom-tag
form is more uniform when we need an "untrusted Prop" type for
deserialization.

Thm is `Clone`. A Thm can be used non-linearly (e.g. passed to multiple
rules that each derive from it) or consumed and mutated (rules that grow
the arena take `&mut Thm`).

`Goal` — a runtime "partially-proved Prop" — is **not** part of the
trusted kernel. Goals live in an untrusted convenience library on top.

### 2.4 Context Stack

A **Context** is `{ assumptions: Vec<Arc<Prop>>, parent: Option<Arc<Context>> }`.
It's a recursive linked list of assumption layers; pushing a context is
cheap. Looking up "is `p` an active assumption?" walks the chain.

Thms hold `Arc<Context>`. The **root** Context contains the user's chosen
trust base — anything the kernel would have called an "axiom" in classical
HOL is just a Prop in the root Context here. The kernel itself adds
nothing to any Context.

### 2.5 Summary

| Object | Owns | References |
|---|---|---|
| `Arena` | a Vec of types/terms/thms + UF state | frozen `Arc<Arena>`s as imports |
| `Prop` | one `Arena` | `Vec<Arc<Prop>>` assumptions |
| `Thm` | a `Prop` that the kernel has validated | `Arc<Context>` |
| `Context` | `Vec<Arc<Prop>>` | `Option<Arc<Context>>` parent |

---

## 3. Term Language

### 3.1 Locally nameless

Terms use **de Bruijn indices + named free variables** (the same shape
`covalence-isabelle` used before it was retired):

```
TermDef =
  | Bound(u32)              // de Bruijn index
  | Free(NameId, TypeId)    // named free variable, typed
  | Const(NameId, TypeId)   // constant at an instantiated type
  | Comb(TermId, TermId)    // application
  | Abs(NameId, TypeId, TermId)  // binder; NameId is a hint, not significant
```

Bound-var substitution doesn't need any alpha-renaming dance; α-equivalence
is structural equality of `TermDef`s.

### 3.2 Closed vs open terms

The kernel distinguishes **closed** (no `Free(_)` reachable, no dangling
`Bound(i)`) from **open** terms. Both can live in the arena. The
restriction is on equality:

- **Closed terms** can be unioned with anything they're proved equal to.
- **Open terms** can only acquire equalities via **congruence**: if
  `Comb(f, x)` and `Comb(g, y)` have `f = g` and `x = y` already, the two
  apps are unioned.

This is the kernel's way of refusing to commit to a "free variable theory"
(à la Isabelle/Pure's `vars` machinery). Open terms are kept around for
structural purposes (so you can build `Abs(_, _, body)` over them), but
nontrivial equalities between them must be wrapped inside a binder first.
The end-user experience is the HOL/HOL style: substitution is for binders,
equalities are for closed terms.

### 3.3 Primitive types

The kernel ships exactly two primitive types beyond function-type and
`bool`:

- `bits` — an infinite type representing arbitrary-length bit strings.
  Logical constructors are `nil : bits`, `cons : bool → bits → bits`, plus
  `eq`, `len`, `append`, `head`, `tail`. **`bits` replaces `ind`** as the
  primitive infinite type.

  At the *arena representation* level, short bit strings (say ≤256 bits)
  are stored inline; longer ones are content-addressed and stored by
  reference. This is invisible to the logic — `nil`/`cons`/`eq` are still
  the canonical surface.

- `bool` — as in HOL Light.

Standard-library types (`blob`, `i32`, `i64`, `nat`, `nat list`, …) are
defined on top of `bits` via the usual HOL type-defining-theorem
mechanism. There is no special-case kernel knowledge of them.

---

## 4. Union-Find

The UF is *the* equality engine. Each term entry carries a `canonical:
TermId` pointing to its class representative. Two terms are α-equal iff
they have the same canonical id.

The kernel supports two write operations on the UF:

- **union(a, b)** — proved `a = b`. Merge their classes. Caller is
  responsible for closedness when this is a nontrivial (non-congruence)
  equality.
- **rewrite(t, t')** — replace `t`'s `definition` with `t'` (which must be
  in the same class). Useful for canonicalising the structural form of `t`
  without changing its class.

The UF is **deliberately minimal**: no automatic e-graph extraction, no
saturation. Higher-level rewriting strategies live in untrusted libraries.
The two primitives above plus congruence are enough to implement HOL's
equality reasoning.

### 4.1 Congruence

Whenever the UF unions `a` and `b`, it walks the use-list of `a` and `b`
and propagates congruence: any `Comb(f, x)` whose `f`-canonical or
`x`-canonical changed gets re-canonicalised. This is the only "automatic"
behaviour in the UF.

---

## 5. Inference Rules

The kernel provides:

### 5.1 HOL primitive rules

All ten HOL Light rules, adapted to mutate an owned `Thm` rather than
allocate a fresh one:

| Rule | Operates on |
|---|---|
| REFL | `&mut Thm` (add a fresh `tm = tm`) |
| TRANS | `&mut Thm`, takes another `&Thm` |
| MK_COMB | `&mut Thm`, takes another `&Thm` |
| ABS | `&mut Thm`, fresh-var name |
| BETA | `&mut Thm` |
| ASSUME | constructs a new Thm |
| EQ_MP | `&mut Thm`, takes another `&Thm` |
| DEDUCT_ANTISYM | `&mut Thm`, takes another `&Thm` |
| INST | `&mut Thm` |
| INST_TYPE | `&mut Thm` |

Each rule grows the arena and updates the UF. Where a rule needs to
*combine* two theorems' arenas, it does so via the foreign-import
mechanism (the smaller of the two is frozen and imported into the larger).

### 5.2 Assumption-manipulation rules

The two non-HOL inferences this kernel adds:

- **add-assumption** — wrap a `Thm` so that its conclusion is now a
  conditional on a new assumption.
- **assumption-eliminates-false** — if an assumption `A` can be used to
  derive `false = true`, then `not A` is a `Thm`.

These are the assumption-stack counterparts of HOL's discharge/eliminate
patterns.

### 5.3 Definitions

Standard `new_basic_definition` and `new_basic_type_definition` from HOL
Light, but the resulting Thm's "axiom-like" content is added to the
*Context* rather than to a kernel-global axiom set. The kernel doesn't
keep an axiom list at all.

---

## 6. Concepts

A **concept** is a polymorphic constant family

```
c[α₁, …, αₙ] : α₁ → ⋯ → αₙ → bool
```

Each type-instantiation `c[α]` is a distinct HOL constant. From the logic's
point of view, concepts are just ordinary HOL constants — there is no
side table, no special term constructor, no special equality logic. What
makes them concepts is the **API for setting their theory**.

### 6.1 Owner capability

`kernel.declare_concept(name, kind)` returns a `ConceptHandle`. The name
reserves a constant family; the `kind` declares the arity pattern (how
many type parameters and what arity-shape) for the family.

Only code holding the `ConceptHandle` can add to the concept's theory.
Sharing the handle = sharing the capability. The WASM bridge gives a
handle out to a hosted component as part of instantiation.

### 6.2 Theory axioms

A theory axiom is a `Prop` whose conclusion has the shape

```
P₁(…) ∧ ⋯ ∧ Pₖ(…)  ⇒  c[α](t₁, …, tₙ) = true
```

(Premises and `tᵢ`s are arbitrary HOL terms; premises may reference *other*
concepts, equalities, free variables, anything.)

The kernel checks the conclusion shape and accepts the Prop as a member
of `c`'s theory — that is, the Prop becomes an assumption in the relevant
Context.

Soundness is preserved because for *any* concept's theory the trivial
model `c[α] = (λx₁…xₙ. true)` satisfies every axiom of this shape. The
owner is therefore choosing the strongest possible theory (everything is
`true`), constrained from below by the premises they attach. Users of `c`
get only what the owner has declared and what they assume about it.

Notably:

- **`attest()` is a degenerate case**: the nullary axiom `c[] = true`.
- **Point observations** (`c[α](a, b) = true`) are just axioms with no
  premises.
- **Universal regions** (`∀x. c[α](x) = true`) are axioms with bound
  variables in the conclusion.

There is no separate side table of observations and no `attest_all`
primitive in the trusted kernel. Painting whole regions of a concept
*efficiently* (e.g. "for all `x : nat`, `c(x, 0) = true`") is supported
by adding a universally-quantified theory axiom — once it's in the
Context, the UF can canonicalise `c[nat](?, 0)` queries against it
trivially.

The `enter()` / sub-capability story — "give me a capability to write
only to `c[α, β]` for a *fixed* `β`" — is a useful affordance but is
not part of the trusted core. It lives in an untrusted library.

### 6.3 Observations as UF unions

Once a theory axiom of the form `c[α](t₁, …, tₙ) = true` enters scope,
the kernel can immediately **union** `c[α](t₁, …, tₙ)` with `true` in
the UF. From then on, any equality query on that term is O(1).

This means observations are structurally indistinguishable from
"normal" equalities like `(1 + 1) = 2`. The UF doesn't know which
unions came from concept theory and which came from inference rules.

---

## 7. Standard-Library Concepts

The kernel ships no concepts. The standard library defines the ones we
care about:

### 7.1 Content-addressed store

```
storeContains : name → blob → bool
```

owned by the store implementation. Its theory includes axioms like:

- `∀ b. storeContains(hash(b), b) = true` — every blob the store admits
  is named by its content hash.
- `∀ h b₁ b₂. storeContains(h, b₁) ∧ storeContains(h, b₂) ⇒ b₁ = b₂`
  — no collisions within this store.

The kernel doesn't know what BLAKE3 is. The `hash` function is itself
another HOL constant whose properties are supplied via concept theory
or trust assumptions.

### 7.2 Cryptographic signatures

```
isValidSignature : key → sig → blob → bool
```

Theory: a particular signature scheme's verifier defines when this is
true. Users add a trust assumption

```
∀ key sig pred.
  isTrustedKey(key) ∧
  storeContains(_, sig) ∧
  isValidSignature(key, sig, serialize(pred))
  ⇒  pred = true
```

to import facts from elsewhere. The kernel sees only HOL implication.

### 7.3 Execution facts

```
executed : wasm-component → blob → blob → bool
```

owned by the WASM runtime. Theory: the runtime can observe
`executed(w, in, out)` whenever it has actually run `w` on `in` and got
`out`. Trust assumption tying executed to an object-logic statement
about `w`'s semantics lives in user code (the **WASM spec axiom** — see
[`prover-mvp-plan.md`](./prover-mvp-plan.md) for why this is deferred
past MVP).

### 7.4 Future schemes

ZKP-based imports look exactly the same as signatures: `isValidZKP(zkp,
pred)` is a concept, and the trust assumption is "the store has no valid
ZKPs for false statements" because forging one is computationally
infeasible. Other cryptographic schemes plug in the same way.

---

## 8. Serialization

Each `Prop` has a flat byte serialization. Deserialization yields an
**untrusted** Prop — concretely, in the phantom-tag scheme, a
`Prop<Untrusted>`.

An untrusted Prop is always safely **embeddable as a HOL `bool` term**.
Lifting an untrusted Prop to a Thm requires either:

- A concept observation firing (e.g. a runtime relation marks it true).
- An explicit trust assumption discharged by the user.

The deserialization path itself never produces a `Thm` directly.

---

## 9. Soundness Story

The kernel's soundness reduces to four invariants:

1. **Thm construction is kernel-only.** All inference rules are sound in
   plain HOL.
2. **Concept theory axioms have the shape `… ⇒ c[α](…) = true`.** Every
   such theory is satisfied by the trivial model where `c` is always
   true.
3. **Trust enters only via the root Context.** Anything the user wants
   to believe is an explicit `Prop` they added to the Context. The
   kernel never silently trusts a runtime, a key, or a signature.
4. **Foreign-imported Thms are still valid.** Imported arenas are
   immutable; their canonical/definition state cannot be perturbed by
   the importer. The importer's view is consistent with the source's.

Anything outside these invariants — tactics, decision procedures, WASM
modules, the convenience `Goal` type, the `enter()` sub-capability,
content-addressed extraction, signed import — is **untrusted**. Bugs in
untrusted code can produce wrong answers but cannot produce wrong Thms.

---

## 10. Glossary

- **Arena** — pool of types/terms/thms with union-find state.
- **Concept** — polymorphic constant family whose theory is set by a
  capability holder; the kernel's only extension point.
- **Context** — recursive stack of assumption Props attached to a Thm.
- **Observation** — a particular point-fact `c[α](t₁, …, tₙ) = true`,
  represented as a theory axiom or directly as a UF union.
- **Owner** — holder of a `ConceptHandle`. The capability granting
  authority to write to a concept's theory.
- **Prop** — structured proposition: arena + assumption vector. Not
  necessarily true.
- **Theory axiom** — a Prop with conclusion `… ⇒ c[α](…) = true`,
  contributed by the owner of `c`.
- **Thm** — a Prop the kernel has validated. Compile-time-only
  distinction from Prop.
- **Trust assumption** — a Prop in the root Context relating concepts
  to facts the kernel itself can't observe (e.g. "this signature scheme
  is unforgeable").

# Prover Architecture (implementation notes)

> **The canonical design doc is now [`ARCHITECTURE.md`](../ARCHITECTURE.md)** at
> the repo root, with operational guidance for AI agents in
> [`AGENTS.md`](../AGENTS.md). This file is kept as a reference for the kernel's
> current Rust-level details (arena fields, MVP status, refactor notes) — it
> elaborates on, and may temporarily diverge from, the canonical doc where MVP
> shortcuts apply.

This document describes the architecture of the Covalence prover kernel — a
HOL-based metalogic intended to glue together object logics, evaluators, and
cryptographic trust schemes without baking any of them into the kernel itself.

For the staged build-out, see [`prover-mvp-plan.md`](./prover-mvp-plan.md).
For the exhaustive list of kernel primitive operations, their type
signatures, host-side reduction semantics, minimal axioms, and the
macro-defined symbolic rewrite layer, see
[`prover-primops.md`](./prover-primops.md).
For the S-expression debug syntax (used by the REPL and printer),
see [`prover-sexpr.md`](./prover-sexpr.md).

---

## What this is

This is a system for building mathematical certainty out of parts you
don't individually have to trust, and for storing the result like a
version-controlled filesystem. It works like a hall of mirrors: many
independent ways of checking the same claim, where confidence comes
from their agreement rather than from any one of them being
authoritative. It refuses convenient lies — never "this is universally
true," only "this is true within this specific, named collection of
things I can point at" — and tracks honestly what it assumes at every
step. The trusted core is kept deliberately tiny (a small proof
checker whose rules are purely mechanical, never depending on what's
already been proved), and everything clever — fast formats, decision
procedures, foreign systems — sits outside that core where a mistake
gets caught rather than believed. You can always add another mirror
if you're not yet satisfied; there's no fixed ceiling on certainty,
you stop when you're sure enough. The whole thing mounts as an
ordinary folder tree so a person (or an AI agent) can `ls`, `cat`,
and `mount` it, while underneath it's a content-addressed store where
the only thing you ultimately trust is a human looking at the
simplest possible statement.

---

## At a glance

A content-addressed store plus a WASM-component evaluator carry
everything. The trusted core is an LCF kernel for a variant of HOL
with one overriding invariant — **well-formedness is purely
syntactic, never provability-dependent** (§1.1) — which is what lets
the empty context stop being privileged: there is no
axiom/oracle/assumption distinction. An oracle is just an authority
that may add Horn clauses whose heads are its own opaque relations
(conservative, since an uninterpreted head always has a model). Terms
are arena indices; theorems live in a union-find over them; frozen
arenas are content-addressed, giving a theory DAG.

The kernel's target shape is roughly 8–10 primitives by **deriving,
not trusting**: `pair` / `unit` / `DOWHILE` (Elgot iteration) plus
`bits` / `blob` carriers stay primitive; `sum`, `option`, sexpr cells,
`ITER`, `num` and so on are derived with a native `(tag, a, b)`
representation, so derivation costs no runtime speed. Type-operator
identity is `(normalised predicate, declared tyvar order)`, not the
name. (MVP is more permissive — see §3.2.)

Above the kernel you work **metalogically**: define internal logics
as HOL theories, prove `provable_L(P)`, connect logics by
embedding / equiconsistency edges so adequacy is reachability from a
human-inspected silvered node; verify sound-not-complete decision
procedures against an assumed WASM spec; borrow strength by assuming
consistency only when forced. The same mirror-and-edge pattern
recurs on the **execution plane** (executors emulate each other;
trust by consensus, not by any one engine) and the **content plane**
(stores compose and degrade under *scoped* no-collision / no-forgery
assumptions, never the global lie; SHAttered is handled by "this
repo is collision-free" staying true while "SHA-1 is secure" is
refuted). Cryptographic assumptions become "a global store lacks
$BAD, and my local store maps into it." Confidence is quantitative
via a probabilistic internal logic, with independence modelled as a
correlation term. Because every logic is data, a functor
HOL → NewBase transports the whole development; the base is just
another node.

**Storage is the VCS.** Git-like trees for paths plus Dolt-style
prolly-tree tables for data, both content-addressed and in the TCB
(a false read asserts a false fact). Reads carry Merkle witnesses;
merges produced by untrusted code emit a checkable certificate. It
mounts as a real filesystem: a path `R[fn, fn, fn | A, B, C, D]` is
directories for the left columns and a `.self` table for the right
tuple. "Mount Q at P" is literally the clause `∀x. Q(x) ⇒ P(x)`,
sound for free because the body is an oracle. Symbolic values are
symlinks (dangling is normal), materialised values are files, and
`st_mode` is the discriminator. Formats are themselves a plane:
`valid(format, data)` is an oracle fact; a typed value is the
keyed-BLAKE3 identity `keyed(format_id, payload)`; format IDs are
256-bit (infinite formats by nesting); `Name256` is just `blob`
refined to length 32 — carrier plus refinement, the universal
answer to "dedicated type or raw blob."

### The philosophical spine

A non-collapsed **computational trinity** — computation, proof, and
evidence kept deliberately distinct. Running a program yields a
**fact**, not a proof; this is the same conservativity that keeps
oracles from lying. Trinitarianism plus a first-class epistemology
of evidence.

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

### 1.1 The core invariant: well-formedness is syntactic

> **The empty context is never privileged.** Axioms are assumptions
> in the root context; oracles enter the same way. Therefore:
> well-formedness of a type or a term — whether it can be *formed*
> at all — must be decidable **purely by syntactic inspection**,
> never by consulting what is provable.

Anything else couples the type system to a particular set of axioms
and silently changes when assumptions are added or removed. Every
primitive in the kernel that classically *would* inspect provability
(HOL Light's `new_type_definition`, `new_specification`, …) has to
be reworked so the proof obligation lands at the **use site** as an
ordinary hypothesis, never at the formation site as a side condition.
This is the principle behind the subset-type modification of §3.6
and the syntactic side conditions on type operators.

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

An **Arena** is a pool of types and terms plus per-arena interning
tables and a list of imports. Its structural tables are append-only
at the user level; the kernel may **mutate a term's structural form
in place to replace it with a provably-equal one** (see §4.4
"Rewrite"). Union-find on terms (§4) is a separate structure that
references arenas — the arena itself carries no equality state.

```
Arena {
  types: Vec<TypeDef>,         // indexed by TypeId, append-only
  terms: Vec<TermDef>,         // indexed by TermId; mutable via kernel rewrite
  imports: Vec<Import>,        // foreign arenas + their substitutions

  // Interning tables for variable-sized payloads referenced by
  // TermDef / TypeDef sealed-id handles.
  strings:      IndexSet<SmolStr>,
  bytes:        Vec<Vec<u8>>,
  ints:         Vec<Int>,
  nats:         Vec<Nat>,
  tyargs:       Vec<Vec<TypeRef>>,
  term_substs:  Vec<TermSubst>,         // interned, addressed by TermSubstId
  type_substs:  Vec<TypeSubst>,         // interned, addressed by TypeSubstId
}

Import {
  source:     Arc<Arena>,
  term_subst: TermSubstId,              // index into term_substs
  type_subst: TypeSubstId,              // index into type_substs
}

TermSubst { map: HashMap<StrId, TermId> }   // source-name → term in importing arena
TypeSubst { map: HashMap<StrId, TypeId> }   // source-tyvar → type in importing arena
```

Putting the substitutions behind a sealed `TermSubstId` /
`TypeSubstId` gives them the same treatment as every other
variable-sized payload — the representation is private to the
kernel and free to change (e.g., to a more compact `Vec` of
pairs, or to a small-int variable scheme once we make that move).

The **interning tables** keep `TermDef` (and the `TermRef` / `TypeRef`
it embeds) `Copy`. Anything bigger than a few `u32`s goes through a
table:

- A free-variable's name is a `StrId` (index into `strings`), not a
  `SmolStr` carried inline.
- Arbitrary-precision int/nat literals are `IntId` / `NatId` when
  large, inline when they fit.
- Bytes literals are always `BytesId`.
- A `Tyapp(name, args)`'s arg list is a `TyArgsId`.

Foreign-arena references are **structural** in this kernel: a
`TermDef::Foreign(ImportId, TermId)` is a regular allocated term in
the importing arena that resolves to a term in the imported arena via
`arena.imports[i].source`. The same shape applies for
`TypeDef::Foreign(ImportId, TypeId)`. There are no side tables of
foreign IDs.

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

Types have **no union-find**. The kernel offers no proposition for
"these two types are equal" — types are compared structurally only.
Genuine isomorphisms between types (the content-addressed-types use
case) are reflected at the **term** level via bijection axioms on
opaque types declared through the concept system (§6.4 / §7.4).

Key properties:

- **Structural tables are append-only from the user's view.** Terms
  and types are added; user-level code never sees a slot removed.
- **The kernel may mutate `terms[id]` to an equal `TermDef`.** This is
  the [rewrite primitive](#44-rewrite); it's not the user's privilege
  but the kernel's, and only along an existing UF equivalence.
- **Canonical IDs are arena-aware tuples `(Arc<Arena>, TermId)`.**
  Identity is by `Arc::ptr_eq`. A bare `TermId` is *not* a canonical
  name across arenas — see §4 for why.
- **Imports carry substitutions** (see "Foreign imports" below).
  Terms in this arena can name a foreign term via
  `TermDef::Foreign(import_id, source_id)`.
- **Closed flag** is computed once at term insertion. Cheaper than
  walking the term every time we need to know.

#### Foreign imports

Arenas can **freeze**, becoming `Arc<Arena>` and read-only. Other
arenas import them by calling `add_import(source, term_subst,
type_subst)`. The result is an `ImportId` pointing at the new entry
in `arena.imports`.

The **substitution** maps source-arena names (the imported arena's
free variables / type variables, identified by `StrId`) to terms /
types in the *importing* arena. When a
`TermDef::Foreign(import_id, source_id)` is interpreted:

- For every `Free(name, ty)` in the source term whose name is
  mapped by the import's `TermSubst`, the result substitutes the
  mapped term.
- For every `TVar(name)` in source types whose name is mapped by
  the import's `TypeSubst`, the result substitutes the mapped type.
- **Anything not mapped** — free variables and type variables
  alike — resolves to `epsilon(λ_. true) : α`, a definite but
  unconstrained inhabitant of the relevant type.

> **Future direction (variable IDs).** Today free-variable and
> type-variable names are `StrId` handles into the arena's string
> table. The plan is to switch to small-integer variable IDs (a
> dedicated `VarId` / `TyVarId` rather than reused `StrId`s). That
> makes substitution maps cheaper (dense arrays keyed by integer)
> and enables importing **ranges** of variables — e.g. "shift all
> free-variable IDs ≥ N in the source by k" — which is the
> efficient analog of α-renaming during composition of imports.
> This change is forward-compatible with the substitution-table
> model above: the IDs become a different sealed type, and the
> `TermSubst` representation switches.

Imported terms must be **locally closed** (no dangling de Bruijn
indices) before the substitution is applied. Any imported `Bound(i)`
that survives import is interpreted as `epsilon(λ_. true) : α` of
the appropriate type. This is forward-compatible with adding a real
de-Bruijn substitution on imports later — indices beyond the
substitution's reach simply default to epsilon.

The substitution model reifies the theory DAG inside imports:
re-exporting a theorem from arena `A` through arena `B` to arena `C`
just composes the substitutions. There is no separate "theory" or
"signature" object; the import edge *is* the theory translation.

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
variables**. The kernel's internal `TermDef` and `TypeDef` enums
are **private** to the crate; users interact through the public
`TermKind` view (and fallible getters) for terms, and through
opaque `TypeRef` accessors for types. The internal representation
is free to change without churning callers — including which
primitive types and operators the kernel ships.

The public `TermKind` lists every term shape the kernel currently
distinguishes (binders, application, equality, the primops, the
literal flavours). `TermDef` may store these more compactly — for
instance, arbitrary-precision literals may have separate "inline"
and "interned" representations — but `TermKind` collapses storage
details and presents the logical value.

A `TermRef` is an opaque reference to a term in the current arena.
Foreign-arena terms appear as a `TermDef::Foreign(ImportId, TermId)`
allocation in the importing arena, so they're regular local terms
with a structural marker telling the kernel which substitution to
apply. The same shape applies to `TypeDef::Foreign(ImportId,
TypeId)`. There is **no separate side-table or packed-flag
machinery** distinguishing "local vs foreign" refs.

Bound-var substitution doesn't need any alpha-renaming dance;
structural equality of `TermDef`s already gives α-equivalence —
display hints stripped, de Bruijn indices intact. (Display hints —
the original parameter name a user wrote — live at the
pretty-printer layer; the kernel never reads them.)

### 3.2 Builtins

The kernel reserves a small set of **builtin** type and term
constructors that pattern-match alongside the structural ones in the
private `TermDef` / `TypeDef`. Exactly which primops and primitive
types are baked in is a kernel-private detail and may change between
revisions; the canonical list lives in [`prover-primops.md`].

The kernel's long-term goal is **vanilla HOL plus our builtins and
the existential operators** — nothing else. Convenience
constructors like `Id`, `Comp`, `Iter`, `Ite`, `LiftOp1`, `LiftOp2`
that exist in today's `TermDef` will move out into user-level
constants with their own axioms; only the structural HOL shapes
(`Bound`, `Free`, `Const`, `Comb`, `Abs`, `Eq`), the existentials
(`Forall`, `Exists`, `Eps`), and the primop families
(`Op1` / `Op2` and their literals) will remain in the core term
language.

We accept a richer-than-HOL-Light set of builtins in exchange for
shorter time-to-MVP and efficient FFI. The trade-off is that each
builtin function-value has a minimal HOL axiomatization (§3.4) and
the kernel's trust surface grows by the size of the primop enums
plus their reduction machinery. Pieces can move out of the kernel
into untrusted extension traits later without touching the logic.

The general principle is **derive, don't trust** — primitive status
should only buy you something derivation can't. For *most*
structural types (sums, options, sexpr-style cons cells, …) a
typedef-plus-representation-hint gives the same runtime layout as a
hard-coded primitive while keeping the trusted core small. The
kernel today still ships `pair` / `unit` / `sum` and a few related
shapes as primitives **for now** — they make MVP implementation
easier — but the long-term direction is to push them through the
untrusted API on top of a smaller trusted core (e.g. a 2-pointer
cell that all of `pair`, `sum`, `option`, sexpr cells can compile
into). This is exactly why the kernel's term and type
representations are kept opaque (§3.1).

#### Logically present today (MVP)

- **Types**: `bool`, `bytes`, `int` (arbitrary precision signed),
  `nat` (arbitrary precision unsigned). Type formers: `α → β`,
  `TVar`, user-declared `Tyapp`.
- **Terms**: the structural shapes (`Bound`, `Free`, `Const`,
  `Comb`, `Abs`), polymorphic equality / inequality, the
  quantifiers `∀` / `∃`, the Hilbert choice operator `ε`, the
  combinators `Id` / `Comp` / `Iter` / `Ite`, the boolean
  literals, arbitrary-precision integer literals, and byte
  string literals.
- **Primops**: the boolean truth-table operators, the basic
  arithmetic on `nat` and `int`, and a handful of bytes
  operations.

Fixed-width integers (`u8` … `u64`, `i8` … `i64`) and bit-string
literals (`Bits`) were intentionally postponed for MVP — they'll
return with the same shape once the rest of the kernel API has
settled.

**`Ite`** is first-class so the kernel can pattern-match on it
directly and reduce on a literal `True`/`False` condition. A naïve
encoding via `Comb` and a polymorphic `ite : bool → α → α → α`
constant would require traversing two `Comb`s to recognize the
shape.

User-defined constants (`Const(name, ty)`) and user-defined type
constructors (`Tyapp(name, args)`) are the only `TermKind`/`TypeDef`
shapes that read from the user-side namespaces (§2.1). Every other
variant is either structural or a builtin.

[`prover-primops.md`]: ./prover-primops.md

### 3.3 Closed vs open terms

The kernel distinguishes **closed** (no `Free(_)` reachable, no dangling
`Bound(i)`) from **open** terms. Both can live in the arena. The
restriction is on **non-congruence unions** (§4):

- **Closed terms** can be unioned with anything they're proved equal to.
- **Open terms** can only acquire equalities via congruence — the user
  has to wrap them in a binder first to do nontrivial equality
  reasoning.

The closed flag is stored on each `TermProps` entry and set once at
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
- `LiftOp1(op)` / `LiftOp2(op)` — η-expansion of a primop into a
  function value. `Comb (LiftOp1 op) x → Op1(op, x)` and analogously
  for binary, so applied forms collapse back to the compact primop.
  These exist so primops are usable in higher-order positions (e.g.
  `Comp (LiftOp1 Not) f` for "negate after f"). Storage: 4 bytes
  (just the PrimOpN discriminant).
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

All seven combinators (plus `Forall`/`Exists`/`Ne`) preserve the
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
   a fixed, confluent, terminating, ordered list. **Only
   fully-constant inputs fire.** Concretely: a primop applied to
   literal arguments returns its computed literal result; nothing
   else reduces. Algebraic identities (`add a 0 = a`), short-circuit
   shortcuts (`And False x = False`), definitional unfoldings
   (`Comb (Id α) x = x`, `Ite True x y = x`), and recursive
   simplifications all become **theorems** proved against the
   axioms — they are not kernel reductions.
3. **Manual rules (§11).** User-invoked rewrites that don't fit
   reduction's discipline — typically recursive unfoldings
   (`add a (succ b) = succ (add a b)`) and canonicalisations. Each
   rule has `LHS = RHS` derivable in the axioms, but the kernel
   does not enforce termination — that's the caller's problem.

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
Even short-circuit cases like `And False x = False` and `Or True x
= True` are theorems, not reductions: the kernel's reducer fires
only when **every** input is a literal.

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

### 3.6 Subset types and type-operator formation

Per the core invariant (§1.1), every well-formedness check on a
type expression has to be **purely syntactic**. This subsection
spells out how the classical HOL Light primitives are reworked to
keep that promise.

#### Subset types are unconditionally well-formed

HOL Light's `new_type_definition` introduces an opaque type `t` from
a predicate `P : α → bool` **and requires a proof** `∃x. P x` that
the carrier is inhabited. The introduction axiom is then
`(∀a:t. P (rep a)) ∧ (∀x:α. P x ⇔ rep (abs x) = x)` (or equivalent),
with `abs : α → t` and `rep : t → α` as the bijection. The
inhabitation requirement is exactly the kind of side condition the
core invariant forbids: it inspects what is provable to decide
whether the type can be formed.

Covalence drops the inhabitation side-condition. The introduction
axiom is instead:

```
abs (rep a) = a                       — unconditional
rep (abs x) = x  ⇔  P x ∨ ¬∃y. P y    — modified
```

When `P` is inhabited (`∃y. P y` holds) the right-hand side
collapses to `P x`, recovering HOL Light's behaviour: `rep` is an
injection whose image is exactly `{x | P x}`. When `P` is **not**
inhabited, the disjunct `¬∃y. P y` becomes `true` and the second
equation degenerates to `rep (abs x) = x` for *every* `x` — making
`abs` and `rep` mutual inverses on the whole carrier. The subset
type is then iso to its carrier (a consistent reading: the empty
`{x | P x}` doesn't constrain anything).

`rep (abs (ε P)) = ε P` holds unconditionally — the same
Hilbert-epsilon bargain we already pay for term-level existentials,
lifted to type formation. The nonemptiness obligation moves from
a meta-level side condition to an object-level disjunct that
propagates to use sites, where an assumption `P a` discharges
`∃y. P y` and collapses the disjunct to ordinary behaviour. The
cost lands exactly where the user hasn't established inhabitation
— which is correct.

#### Other existence obligations follow the same pattern

The disjunct trick handles the typedef nonemptiness case; the
remaining classical existence side conditions get the same
treatment:

- **`new_specification`** is already `ε`-derived; stop discharging
  the existence side condition, expose the same disjunct at use
  sites.
- **`new_definition`** has trivial existence (the witness is the
  body); only syntactic conditions remain — closedness,
  type-variable scoping.
- **`new_type`** (opaque-type introduction) and the standard
  **infinity axiom**: the kernel ships no inhabitation built-in.
  If the user wants `t` inhabited they assume `∃x : t. True`; the
  assumption sits in the context, never in the formation rule.

None of these consults the assumption set, so all are consistent
with the core invariant.

#### Syntactic side conditions on `subset P`

To form the subset type `subset P` the kernel checks, by structural
recursion on `P`, that:

- **`P` is locally closed.** No escaping de Bruijn indices.
- **`fv(P) = ∅`.** No free term variables. (A free term variable
  in `P` would make the *type* depend on a term context — the
  real hazard. Free type variables are fine; see below.)
- **Free type variables in `P` are permitted** — they make
  `subset P` a polymorphic type operator parameterised by those
  variables.

All three are decidable by structural inspection — none touches the
assumption set or the UF.

#### Type-variable ordering: user-provided

The order of a type operator's parameters is part of its
**interface**, not an artifact of how its defining predicate is
written. The user declares the order at definition time (the
Isabelle convention), and the kernel checks that the declared list
is a permutation of `tyvars(P)`. Occurrence order would couple the
operator's interface to the internal shape of `P` — innocuous
refactors of `P` would silently permute the operator's arguments.

There are two regimes for tyvar ordering across the kernel:

- **Declared order** wherever a user-facing interface exists —
  type operators, polymorphic constants.
- **Canonical order** (occurrence over a normal form) for purely
  internal machinery — serialisation, auto-generalisation,
  content-addressing of operators with no user-declared list.

#### Content-addressed identity for type operators

A type operator's identity is `(normalised P, declared tyvar
order)`. The user-facing name is a **namespace binding** pointing
at that address — it is not the identity. Two operators with the
same `P` but different declared orders are *genuinely different*
operators (different interfaces), so they hash differently.

The canonical tyvar ordering used by the normaliser must be the
same one used by constant polymorphism and by serialisation, or
the same logical object hashes differently along different paths.
Threading one canonical order through all three is part of the
content-addressing contract.

#### Why this matters operationally

**Every well-formed type expression is decidably well-formed by
structural inspection alone.** The kernel does not need to admit a
witness theorem to typecheck `t = subset α P`. Untrusted code can
run a type-checker that traverses `TypeDef` / `Tyapp` shapes
without round-tripping through the proof engine — the kernel is
needed only for deciding *equalities*.

---

## 4. Union-Find: Equality without Closure or Search

The UF is the equality engine, but it does **not perform automatic
congruence closure**. Every union is explicit. The kernel's job is to
record and look up equalities the user has proved; *strategy* for how
to propagate congruences lives in untrusted code.

The same "no automatic work" discipline applies to assumption lookup
(§2.5 Context inspection API) — the kernel doesn't search for relevant
facts on the user's behalf.

**Types have no UF.** The kernel offers no propositional equality
on types, so there is nothing to canonicalise. Two types are equal
iff they are structurally equal modulo their imports' substitutions
(§2.2).

**The term UF is external to the arena.** A separate `TermUf` data
structure holds one entry per allocated term, indexed by
`(Arc<Arena>, TermId)`. Arenas can be queried, frozen, and imported
without touching equality state; UFs reference arenas but arenas do
not reference UFs.

### 4.1 Canonical IDs are arena-tagged

Each UF entry stores `canonical: (Arc<Arena>, TermId)`. To check
"are `a` and `b` known equal in this UF's view?", walk both canonical
chains and compare the final tuples — pointer equality on the
`Arc<Arena>` (via `Arc::ptr_eq`) plus equality on the local ID.

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

There is no analogous family for types: types compare structurally
modulo their imports' substitutions, with no kernel-mediated
canonicalisation.

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
  other term holding a `TermRef` to `t` will see the new structural
  form.
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

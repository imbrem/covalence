# Arena and union-find: the syntax / semantics split

> **STATUS: WORKING NOTE — extracted from session conversation.**
> Refines [`modified-hol.md` §3](./modified-hol.md#3-the-layered-structure):
> the bottom layer factors into a **substrate** (arena = syntax + UF
> = semantics; pure LF rules; no content-addressing; no first-class
> substitutions) and a **framework** (substrate + the four
> modifications + content-addressing primitives + observations). The
> corelib becomes a particular arena+UF value, not a mountable
> namespace. Significant simplification: Phase H (`Arena::hash`) and
> Phase E (substitution-imports) leave the substrate, becoming
> framework-layer machinery if needed at all.

The user's framing, verbatim:

> *Corelib can just be an arena with a union-find on it as the
> theorems in the corelib. The only question is whether we should
> explicitly disallow content-addressing for this design — while it
> fits content addressing well, we can always require content-addressing
> to be in the nested inner HOL only. Which could probably simplify a
> lot of our logic — e.g. we can get rid of the substitution-import
> stuff since that's mainly so we can do a content addressed import
> safely. The interesting part is that Arena only holds well-typed
> HOL syntax (or perhaps, just well-typed* **generic** *lambda
> syntax — an interesting direction!) and only becomes actual HOL
> terms when you stick the union-find on top.* + *Arena only being
> the native representation of syntax we can get out of this — by
> representing content-addressed syntax in the higher language and
> flat syntax in the lower language in the same data structure.*

---

## Contents

1. [The core idea](#1-the-core-idea)
2. [The arena: syntax carrier](#2-the-arena-syntax-carrier)
3. [The union-find: semantic content](#3-the-union-find-semantic-content)
4. [The substrate's inference rules](#4-the-substrates-inference-rules)
5. [Why no content addressing in the substrate](#5-why-no-content-addressing-in-the-substrate)
6. [Why no first-class substitution-imports](#6-why-no-first-class-substitution-imports)
7. [Generic lambda vs HOL-specific syntax](#7-generic-lambda-vs-hol-specific-syntax)
8. [How the corelib fits](#8-how-the-corelib-fits)
9. [Revised layering](#9-revised-layering)
10. [What this dissolves](#10-what-this-dissolves)
11. [Open questions](#11-open-questions)
12. [Cross-references](#12-cross-references)

---

## 1. The core idea

> **Arena holds syntax. Union-find holds theorems.**

The substrate's data is one (`Arena`, `Union-find`) pair, where:

- The **Arena** is a typed-lambda-syntax carrier. It stores types
  (`TVar`, `TyApp`), terms (`Var`, `Const`, `App`, `Abs`, `Eq`),
  and a definition table mapping declared constants to defining
  terms. **No content-addressing primitives.** No semantics beyond
  well-typedness.
- The **Union-find** layers semantic content on top. It's an
  equivalence relation over arena terms. "T proves `a = b`" iff
  `find(a) == find(b)` in T's UF. "T proves `p`" iff `find(p) ==
  find(true_term)` for some designated truth witness.

A "Thm" is a value-level proof that "the kernel performed certain
union operations." That value is opaque (only the kernel's inference
rules construct it), and queryable via `uf.find(a) == uf.find(b)`.

This is the [Phase P](../../../../prop-egraph-design.md) shape, but
*explicitly* with the arena and UF as the substrate's only data,
nothing else.

---

## 2. The arena: syntax carrier

```rust
// Substrate-level Arena. Tiny, auditable, fast.

pub struct Arena {
    // Type-level
    types: Vec<TypeDef>,
    // Term-level
    terms: Vec<TermDef>,
    // Definitions: constant_name → defining_term
    definitions: HashMap<StrId, TermId>,
    // Interning tables for compact representation
    strings: Vec<SmolStr>,
    // ... no hash, no CA, no substitution tables
}

pub enum TypeDef {
    TVar(StrId),
    TyApp(StrId, Vec<TypeId>),
}

pub enum TermDef {
    Var(StrId, TypeId),       // free variable, named
    Const(StrId, TypeId),     // declared constant (must be in definitions)
    App(TermId, TermId),      // application
    Abs(TypeId, TermId),      // λ binder, locally nameless
    Bound(u32),               // de Bruijn index
    Eq(TermId, TermId),       // meta-equality
    // Possibly: a small set of well-known constants (true_term, false_term)
    //           if treating those as primitive simplifies the UF discipline.
}
```

**No content-addressing in the arena.** No `Arena::hash()`. No
canonical-form computation. The arena is a flat allocation table that
the kernel grows monotonically.

**No first-class substitution-imports.** No `(source_arena,
term_subst, type_subst)` triples. An "import" at the substrate level
is just an `Arc<Arena>` reference; if you want to specialize an
imported theorem, use `INST` or `INST_TYPE` rules to produce a new
Thm with substituted form, the standard HOL Light way.

**No observation primitive in the arena.** Observations are how
authorities write facts; they're a *framework* concept, not a
substrate one. The substrate sees only typed lambda terms.

The arena is generic over CA scheme because there isn't one. Higher
layers can content-address arena terms by walking them and hashing,
but the arena itself doesn't know or care.

---

## 3. The union-find: semantic content

```rust
pub struct UnionFind {
    // Equivalence classes over arena TermIds (and TypeIds, if
    // type-level equalities are first-class).
    parent: Vec<TermId>,
    rank: Vec<u32>,
    // ... possibly an egraph hash-cons for efficient congruence
}
```

Operations:

- `union(a, b)` — merge the classes of `a` and `b`.
- `find(a)` — canonical representative of `a`'s class.
- `union_if_congruent(a, b)` — merge if their decompositions match
  via prior unions (the egraph rebuild step).

A **Thm** is a value-level proof that some specific sequence of these
unions happened, performed by the kernel's rules. It's not a separate
data structure — it's the (Arena, UF) state at the moment the rule
returned.

**The LCF trust boundary** is: only the kernel's rule functions
call `UnionFind::union`. Everything else queries via `find`. A bug
elsewhere can't produce a false Thm because nothing else can union.

---

## 4. The substrate's inference rules

Small, conventional:

- **`assume(t)`**: introduce `t` as a hypothesis. Produces a Thm
  whose hypothesis set is `{t}` and whose UF asserts `t` is true.
- **`imp_intro(t, thm)`**: from `Γ, t ⊢ φ` derive `Γ ⊢ t ⟹ φ`.
- **`imp_elim(imp_thm, hyp_thm)`**: from `Γ ⊢ t ⟹ φ` and `Δ ⊢ t`
  derive `Γ ∪ Δ ⊢ φ`.
- **`all_intro(x, thm)`**: from `Γ ⊢ φ(x)` (with `x ∉ FV(Γ)`)
  derive `Γ ⊢ ⋀x. φ(x)`.
- **`all_elim(all_thm, witness)`**: from `Γ ⊢ ⋀x. φ(x)` derive
  `Γ ⊢ φ(witness)`.
- **`refl(t)`**: `Γ ⊢ t ≡ t`.
- **`sym(thm)`**, **`trans(ab, bc)`**, **`cong_app(eq, s)`**,
  **`cong_abs(eq)`**.
- **`beta(t)`**: `Γ ⊢ (λx. M) N ≡ M[N/x]`.
- **`eta(t)`**: `Γ ⊢ λx. f x ≡ f` when `x ∉ FV(f)`.
- **`define(c, d)`**: introduce a fresh constant `c` with definition
  `d`. Returns `c ≡ d`.

That's the whole substrate API. ~15 rules; each is a small Rust
function that reads the arena, validates side conditions, performs a
UF union, and returns a `Thm`. Audit by inspection.

**What's *not* in the substrate:**

- HOL Light's `new_basic_type_definition` (subset typedef) — that's
  a *framework* primitive because it relies on the disjunct trick,
  which is one of the four modifications. Live in the next layer up.
- Observations under authorities — framework primitive.
- Content addressing — framework or higher.
- Stores, signatures, oracles — outer-framework / userspace.

---

## 5. Why no content addressing in the substrate

Three arguments:

1. **Smaller TCB.** Phase H ([`Arena::hash()`](../../../../refactor-plan.md))
   is hundreds of lines of canonicalization in the trust core. With
   CA out of the substrate, that code leaves the TCB. The substrate
   stays as small as it can be.
2. **Multiple CA schemes possible.** BLAKE3 today, a quantum-resistant
   hash tomorrow, Git-SHA-1 for compatibility, a learned content
   hash for a particular community. All are framework-layer choices.
   The substrate doesn't commit.
3. **CA is itself a scoped assumption.** Per the
   [oracle-everything stratification](../../shared-backbone/00-overview.md#3-oracle-everything-stratification),
   crypto schemes are oracles. CA *uses* a crypto scheme. So CA is a
   shell-layer concern that consumes the substrate, not a substrate
   primitive.

**The "too tempting" tension resolved.** The user noted: arenas
naturally support CA because their flat-table structure hashes
cleanly. The resolution is that **the same arena data structure
supports both modes**:

- In the substrate: an arena is just a flat allocation table, no CA
  metadata.
- In the framework / higher: the *same* arena structure can be
  hashed (by a framework-layer function), serialized, content-addressed,
  imported across kernels.

The data structure is shared; the operations on it stratify. Lower
layers see less; higher layers see more.

---

## 6. Why no first-class substitution-imports

[Phase E](../../../../refactor-plan.md) added substitution to import
edges — an `(source_arena, term_subst, type_subst)` triple lets you
import a Thm from another arena under a renaming, which is essential
for content-addressed imports (same logical content, different
variable names ⇒ same hash if substitution is applied during the
import).

**Without CA in the substrate, this disappears.** Imports become
bare `Arc<Arena>` references; specialization happens via the
existing `INST` / `INST_TYPE` rules at the using site. Those rules
already produce new Thms with substituted forms — the substrate's
import edge doesn't need to.

**Does substitution itself go away?** No — `INST` and `INST_TYPE`
are essential HOL rules; they stay. What goes is the *first-class
substitution attached to an import edge*. The rules' substitutions
are local operations on the consumer's arena, not edge-carrying
machinery.

**Is first-class substitution a good idea in general?** Probably
not at the substrate. The argument for first-class subst is mostly
"CA imports need it." Without that driver, the substrate stays
simpler. Frameworks can add subst-imports back if a specific use
case justifies it (e.g., a framework-level theory-translation
machinery), but they're not bottom-layer primitives.

---

## 7. Generic lambda vs HOL-specific syntax

The user's question: arena holds well-typed HOL syntax, or
well-typed *generic lambda* syntax?

**Argument for generic.** If the arena is just typed lambda — `App`,
`Abs`, `Var`, `Const`, `Eq`, types — then the same substrate
supports any logic over typed lambda terms:

- HOL = substrate + HOL connectives + choice + subset typedef
  (framework).
- ZFC = substrate + set theory's primitives + replacement
  (framework or shell library).
- Future intuitionistic logic, HoTT, etc.

The HOL-specific bits (the disjunct-trick subset typedef, the
boolean connectives' axioms, ε-choice) live in the framework as a
*configuration* of the substrate. Other logics get other
configurations.

**Argument for HOL-specific.** Some efficiency gains might come from
the substrate knowing about `Bool`, the propositional connectives,
the standard quantifiers — fewer indirections, less framework
machinery to wire up HOL.

**Synthesis.** The substrate holds **generic typed lambda syntax**.
Specific theories add their constants via the `define` rule and
their axioms via the trust set. HOL's connectives are *defined
constants* with axioms; they're not built into the substrate.

This costs maybe 5–10% in implementation complexity at the framework
layer vs baking HOL into the substrate, and buys reusability for ZFC
and any future foundation. Worth it.

There's one nuance: the substrate probably needs to know about
`Eq` (because `refl`, `sym`, `trans`, `cong` are equality rules).
The boolean connectives don't need to be primitive — they're
definitions via lambda calculus.

---

## 8. How the corelib fits

The corelib is **a particular value of (Arena, UF) plus the trust
set under which its UF unions are justified**.

In paranoid mode:

```rust
fn init_corelib(kernel: &mut Kernel) -> CoreLib {
    let mut k = kernel.fresh_substrate();
    // Run the derivation script — a sequence of inference rule
    // applications. Each rule mutates k's arena and UF.
    run_script(include_bytes!("../corelib-script.bin"), &mut k)
        .expect("corelib derivation failed");
    CoreLib { arena: k.arena, uf: k.uf }
}
```

In default mode:

```rust
fn init_corelib(kernel: &mut Kernel) -> CoreLib {
    let blob = include_bytes!("../corelib-prebuilt.sigblob");
    verify_signature(blob, COREL_LIB_AUTHORITY_KEY)
        .expect("corelib signature verification failed");
    let (arena, uf) = deserialize_arena_uf(&blob.payload);
    CoreLib { arena, uf }
}
```

Either way, the corelib is just an (Arena, UF) the kernel uses. No
mountable namespace at the substrate level. The
[Kernel-as-OS layer](../../shared-backbone/notes/kernel-as-os.md) can
expose it under `/auth/corelib/` paths, but that's a framework /
shell concern; the substrate doesn't care.

**This simplifies the corelib design significantly.** No content
addressing of corelib entries (the corelib is just bytes signed by
the corelib authority). No mount machinery in the substrate. No
namespace conflicts. The corelib is *a value*, identified by the
hash of its serialized form.

---

## 9. Revised layering

This refines [`modified-hol.md` §3](./modified-hol.md#3-the-layered-structure):

```
┌────────────────────────────────────────────────────┐
│  Theories + morphisms + interpretations            │
│    LOTS, CHANGING, untrusted                       │
├────────────────────────────────────────────────────┤
│  Framework                                         │
│    UNCHANGING, content-addressing, observations    │
│                                                    │
│   - The four modifications (observations,         │
│     oracle naming, no-root-privilege,             │
│     disjunct-trick subset types)                  │
│   - Content addressing primitives (hash arena,    │
│     serialize, deserialize, sign, verify)         │
│   - Authorities + observations                    │
│   - Possibly first-class subst-imports if needed  │
├────────────────────────────────────────────────────┤
│  Substrate                                         │
│    UNCHANGING, TINY, auditable by inspection       │
│                                                    │
│   - Arena: typed lambda syntax (Var, Const,       │
│     App, Abs, Eq, definitions)                    │
│   - Union-find: equivalence classes              │
│   - ~15 LF inference rules                        │
│   - No CA, no observations, no first-class       │
│     subst-imports                                 │
└────────────────────────────────────────────────────┘
```

**Mapping from modified-hol.md's bottom-inner / bottom-outer / top:**

- `modified-hol.md` *bottom-inner* (pure meta-meta-reasoning) ≈
  this doc's **substrate**.
- `modified-hol.md` *bottom-outer* (with content-addressing) ≈
  this doc's **framework**.
- `modified-hol.md` *top* (theories + morphisms) = this doc's
  **theories**.

The new naming is sharper: "substrate" and "framework" are distinct
levels rather than "inner" and "outer" of the same thing. The
substrate is logically minimal; the framework adds the HOL flavor
plus content-addressing. Theories ride both.

---

## 10. What this dissolves

- **Phase H ([`Arena::hash()`](../../../../refactor-plan.md)) leaves
  the TCB.** Arena hashing becomes a framework function that
  operates on a passed-in arena; no kernel impact, no canonicalization
  primitive in the substrate. Per `phase-h-no-normalization` auto-memory,
  the no-canonicalization bet is preserved — but the hashing
  operation itself moves out.
- **Phase E (substitution-imports) leaves the TCB.** Bare arena
  imports work; specialization via `INST` / `INST_TYPE`. Phase E
  machinery is at most a framework-layer concern.
- **`Arc<Arena>` references replace the elaborate import substitution
  triples.** Imports become a much simpler operation.
- **The substrate fits in ~700 LoC** (substrate + arena + UF +
  inference rules + de Bruijn machinery). The framework adds another
  500–1000 lines for content addressing, observations, authority
  bookkeeping, the four modifications.
- **The corelib design simplifies.** No mountable-at-substrate
  namespace; just a value loaded under an authority.
- **The format graph still works.** `HolLightKernel` is implemented
  by drivers (`HolPrim`, etc.) that route through the substrate +
  framework. The trait stays generic; backends vary in what framework
  features they expose.

---

## 11. Open questions

- **Egraph or simple UF?** The current
  [Phase P](../../../../prop-egraph-design.md) prototype uses an egraph
  shape (UF + hash-cons + congruence rebuild). Egraph is faster for
  many queries; simple UF is smaller code. Recommend egraph — the
  efficiency matters at corelib-load time, and the rebuild logic is
  bounded.
- **Truth witness — primitive or convention?** Two options:
  (a) substrate has a primitive `True : Bool` term that the UF
  designates as "the truth witness"; (b) userspace allocates whatever
  `Bool(true)` ref it wants and threads it through rules. Per memory
  `prop-egraph-user-truth`, (b) is the current bet. Keep (b) at the
  substrate; (a) only if a performance reason emerges.
- **What types does the substrate know about?** Minimum: `Bool`
  (for the truth witness, if needed), function types `α → β` (for
  `App`/`Abs` typing), `Var(StrId)` for type variables. Possibly
  nothing else — even `Bool` could be a framework definition.
- **Definitions: substrate primitive or framework?** Definitions
  are conservative extensions, doable purely with substrate rules
  if we have `assume` + `imp_intro` + `imp_elim`. But making them
  a primitive simplifies the API. Lean to primitive.
- **Serialization without CA in the substrate.** If the substrate
  doesn't hash arenas, how do we serialize? Answer: the framework
  provides arena serialization (a function `Arena → Bytes`).
  Deserialization checks well-formedness but doesn't depend on a
  canonical-form hash.
- **Cross-arena equality.** Two arenas might allocate "the same"
  logical term under different `TermId`s. The substrate doesn't
  resolve this (no CA). The framework can, if it wants, via a
  walk-and-compare or via hashing.
- **Performance of the bottom.** Per user emphasis, the substrate
  *must not constrain performance of layers above*. Egraph + flat
  arenas + de Bruijn binders is the right shape for this. Benchmarks
  to follow.

---

## 12. Cross-references

- [`modified-hol.md`](./modified-hol.md) — the previous layered
  structure; this note refines §3 (bottom-inner / bottom-outer
  becomes substrate / framework).
- [`facts-not-proofs.md`](./facts-not-proofs.md) — the LCF
  discipline this design realizes. Arena+UF is the canonical
  "fact storage, not justification storage" data shape.
- [`../../shared-backbone/notes/core-lib.md`](../../shared-backbone/notes/core-lib.md)
  — corelib design; this note simplifies it (corelib is a value, not
  a mountable namespace at the substrate level).
- [`../../shared-backbone/notes/kernel-as-os.md`](../../shared-backbone/notes/kernel-as-os.md)
  — the system kernel framing; corelib mounts at `/auth/corelib/`
  via framework machinery, not substrate.
- [`../../../../prop-egraph-design.md`](../../../../prop-egraph-design.md)
  — Phase P prototype; this note generalizes it (substrate is
  egraph-shaped; the design is no longer "indefinite Phase P
  coexistence" but "substrate is Phase P's shape").
- [`../../../../refactor-plan.md`](../../../../refactor-plan.md) Phase H,
  Phase E — both leave the TCB under this design.
- [`../02-framework.md`](../02-framework.md) — the framework layer
  design; this note clarifies what stays in the framework vs what
  drops down to the substrate.
- [`../../../../../AGENTS.md`](../../../../../AGENTS.md) TCB list —
  this design narrows it further (CA + subst-imports leave).
- HOL Light's own kernel structure (arena of typed lambda + 10
  primitive rules) — the design template.

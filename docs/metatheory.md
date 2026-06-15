# Covalence — Metatheory: Theories, Derivations, and Models

> **STATUS: WORKING DRAFT / DESIGN SKETCH.** Fleshes out the original
> scratch sketch (`docs/sketches/MAPS.md`). Describes how object
> theories (PA, ZFC, …) and their *derivations* become first-class
> objects **inside our HOL metatheory**, how soundness theorems let us
> "get rid of the oracles," and the metavariable **layering** decisions
> — including why we start with **two layers + HOL Light** and treat the
> third (schematic) layer / HOL-ω as *future*.
>
> See also: [`VISION.md`](./VISION.md) (metatheory-as-default, symbolic
> vs. computational), [`observers.md`](./observers.md) (the computational
> half), [`surface-syntax.md`](./surface-syntax.md) (how theories are
> written), [`kernel-design.md`](./kernel-design.md) (the HOL kernel
> these object theories are built inside).

---

## 1. The core idea: theories *inside* HOL

Our kernel is an HOL-Light-style metatheory. The plan is **not** to make
PA, ZFC, etc. new trusted logics — it is to **define each of them as an
ordinary datatype inside HOL**:

- a type of **formulas** of the object theory,
- an inductive **derivability** predicate `Derivable_X : formula → bool`,
- a **denotation** `⟦·⟧` mapping object formulas into HOL propositions
  under a chosen model.

Then the headline judgement of the sketch —

```
   HOL(A);   PA(A);   ZFC(A)
```

— is read as `X(A) ≜ ⊢_HOL Derivable_X ⌜A⌝`: "*A* is a theorem of theory
*X*" is itself an ordinary HOL theorem about the reified object theory.
This is the reflective core of "metatheory is the default mode."

Concretely, the sketch's two layers for one theory:

```
   ( theory of peano arithmetic )      ;; the formulas + axioms of PA
   ( theory of PA _derivations_ )      ;; the inductive proof trees over them
```

---

## 2. Soundness: proving instead of trusting

> *Prove PA is sound under standard denotation: if ∃ derivation, then
> true.*

The key theorem schema:

```
   ⊢_HOL   Derivable_PA ⌜A⌝   ⟹   ⟦A⟧      (under the standard model)
```

"If there exists a PA derivation of *A*, then *A* holds." This is the
mechanism behind the OBSERVERS program of *getting rid of the oracles*
(`docs/observers.md`): instead of a validator *trusting* a backend, we
prove its outputs sound under a formal semantics, and the trusted
validator collapses into an untrusted checker.

Its computational counterpart (the sketch's `WASM(P, D, A)` line):

```
   WASM(P, D, A)   ⟹   ∃ D'. ZFC(D', A)
```

"A WASM program *P* run on data *D* witnessing *A*" yields the existence
of a ZFC derivation *D'* of *A*. The WASM run produces a *checkable
certificate* (Alethe / DRAT / a reified derivation), and the kernel
checks the certificate — it never trusts the program. This is exactly
the "complex software enters by producing checkable certificates, not by
being formalized" claim of [`VISION.md`](./VISION.md).

---

## 3. Theory morphisms and transport

> `PA(A) ⟹ HOL(A) ⟹ ZFC(A)` &nbsp;&nbsp; `Isabelle[THRY](A) ⟹ THRY(A)`

Interpretations between theories are **proved theorems**, not trusted
glue:

- `PA(A) ⟹ HOL(A)` — every PA theorem is a HOL theorem (interpret PA's
  `nat` as HOL's `nat`); `HOL(A) ⟹ ZFC(A)` — interpret HOL inside ZFC.
  Chaining gives transport *up* the strength hierarchy.
- This realizes the **reverse-math** discipline of the VISION doc: prove
  in the *simplest sufficient* theory, then transport to wherever you
  want the statement-of-record. The morphism layer is MVP-scope there;
  it is the `(spec a |- spec b)` entailment question of
  [`surface-syntax.md`](./surface-syntax.md) §6.
- `Isabelle[THRY](A) ⟹ THRY(A)` — *importing* from an external prover.
  An imported article is **not** trusted blindly (cf. the project's
  "no trust articles" stance); it is replayed/checked against our reified
  `THRY`, so an Isabelle theorem in theory `THRY` becomes one of ours
  only once `Derivable_THRY ⌜A⌝` is re-established here.
- `GT3(A)` / locale & context machinery, and model embeddings like
  `Nat → ZFSet`, are the longer-horizon items: first-class *contexts*
  and *locales* over the reified theories.

---

## 4. The LCF-style derivation API

> *Expose an LCF-style API for building derivations in some system `Thry`
> in our HOL.*

For each reified object theory we expose **smart constructors** over its
derivation datatype — the LCF discipline, one level up:

- The *abstract type* is "a value of type `Derivation_X`"; the only way
  to make one is via the inference-rule constructors of `X`.
- Building a derivation and checking `Derivable_X ⌜A⌝` are the *same
  act*, just as `Thm` in the kernel can only be built by the kernel
  rules.
- These constructors are written in the [surface syntax](./surface-syntax.md)
  `(by …)` proof vocabulary — they bottom out in ordinary HOL proofs
  about the reified `Derivable_X`, so **defining a new object logic adds
  no kernel TCB**: it is a definition + an induction principle, checked
  by the existing kernel.

This is the symbolic-metatheory analogue of the observer/validator
pipeline: there, *computational* facts enter via checked certificates;
here, *symbolic* facts enter via checked derivations.

---

## 5. The metavariable layering

The sketch lists three candidate layers of variables (the OBSERVERS
sketch, "how do we get rid of the oracles"):

```
   - Schemavars / Schematypes   (Isabelle-style, schematic)
   - Metavars   / Metatypes     (HOL — our metatheory)
   - Vars       / Types         (the current/object logic)
```

with metatype variables `α` *distinct from* HOL object types, over which
we form first-order derivation trees `{a1,…,an} ⊢ conc`.

The purpose of that bottom schematic layer is specific and worth stating
plainly: **replace the kernel's complex, hand-written rules for
well-typedness, locally-nameless invariants, and unification with a
single, simple first-order logic.** In that FOL:

- **individuals are reified HOL syntax** — a variable is schematic of a
  fixed *meta-sort* like `HOLTm` (a HOL term) or `HOLTy` (a HOL type),
  **not** of any particular HOL type;
- **predicates are the syntactic judgements** that today live as Rust
  code: `IsThm t`, `HasTy t τ`, `IsLocallyClosed t`, and friends.

So "this term is well-typed at τ", "this locally-nameless term has no
dangling de-Bruijn indices", "this is a theorem" stop being properties
enforced by bespoke kernel code and become **predicates with FOL
inference rules** — derivations, not Rust. Unification likewise becomes
ordinary first-order reasoning over `HOLTm`/`HOLTy` rather than a special
algorithm in the TCB.

> **The crucial difference from Isabelle/HOL: we do *not* conflate
> meta-types with object types.** Isabelle/Pure is itself a typed
> metalogic whose type discipline does double duty for the object logic.
> Here the framework's *only* "types" are the fixed, finite meta-sorts
> (`HOLTm`, `HOLTy`, `HOLThm`, …); HOL's own rich type system is just
> *data* of sort `HOLTy` together with the `HasTy` predicate — it is not
> baked into the framework at all. The framework stays a dead-simple
> FOL; all the richness lives in ordinary predicates over reified
> syntax.

### 5.1 Decision: **start with two layers + HOL Light**

We **start with two layers**:

1. **Meta** — HOL Light, our metatheory (where reified theories,
   derivability predicates, and soundness theorems live).
2. **Object** — the current logic / theory being reasoned about (PA,
   ZFC, a user theory).

The **schematic FOL framework** described above is recorded as a
**potential future plan, not a commitment**. Its payoff is real —
collapsing the kernel's bespoke well-typedness / locally-closed /
unification machinery into one small first-order logic over reified
syntax, shrinking the TCB to "a FOL checker + the predicate rules." But
the cost is real too, and the kernel's current Rust rules work today.
Two layers are very likely enough for the MVP and quite possibly long
after; we adopt the framework only once the simplification clearly pays
for itself (e.g. when typing or unification rules start to sprawl).

### 5.2 Decision: **HOL Light now, HOL-ω maybe later**

The metatheory is **HOL Light** to begin with — rank-1 polymorphism,
the kernel we already have. A later move to **HOL-ω** (HOL with
type-constructor variables / higher kinds, à la `HOL_omega`) is a
*possible*, **independent** future — it is about the *object* logic's
type system, orthogonal to the schematic FOL framework of §5.1 (which is
about *describing* HOL's syntax in a simpler logic). We are explicitly
**not** building for HOL-ω now; the surface and metatheory designs
should avoid baking in assumptions that would make that migration
impossible, but should not pay for it up front either.

The *pull* toward HOL-ω is the north star of
[`surface-syntax.md`](./surface-syntax.md) §1.1: we want the surface
layer to be a genuinely **Haskell-like language**, and a Haskell-like
language wants higher-kinded type constructors (functors, monads,
container types abstracted over their element constructor) as
first-class citizens. Rank-1 HOL Light models those one ground instance
at a time; HOL-ω lets us quantify over the type *constructor* itself.
That is a want, not yet a need — we adopt it only when a concrete theory
we care about is unstatable without it.

> **Why these are two independent bets, both deferred.** The schematic
> FOL framework (§5.1) simplifies *how we describe HOL itself*; HOL-ω
> enriches *the object logic's type system*. They are orthogonal — adopt
> either, both, or neither. The two-layer / HOL-Light path already proves
> PA/ZFC soundness, transport, and the WASM-certificate story without
> either. Per the project's "defer-as-guardrails" discipline, both are
> notes constraining today's design, not phases of their own: don't
> preclude them, don't pay for them.

---

## 6. Summary of judgement forms

| Form | Meaning | Status |
|---|---|---|
| `X(A)` | `⊢_HOL Derivable_X ⌜A⌝` — *A* is a theorem of *X* | core |
| `Derivable_X ⌜A⌝ ⟹ ⟦A⟧` | soundness of *X* under a model | core goal |
| `PA(A) ⟹ HOL(A) ⟹ ZFC(A)` | proved theory transport | MVP-scope |
| `WASM(P,D,A) ⟹ ∃D'. ZFC(D',A)` | computational certificate | post-MVP |
| `Isabelle[THRY](A) ⟹ THRY(A)` | checked external import | post-MVP |
| `GT3(A)`, `Nat → ZFSet` | locales/contexts, model embeddings | future |

Throughout, the metatheory stays **HOL Light over two variable layers**,
and every object theory is admitted by *definition + checked proof* — the
kernel TCB never grows to accommodate a new logic.

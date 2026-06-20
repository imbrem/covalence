# Theories, models, and logics — the signature/theory/model architecture

> **STATUS: DESIGN DISCUSSION (record).** Captures the design conversation that
> refined `surface-compiler.md`'s "many models" idea into a precise
> **signature → theory → model** architecture, centred on **multiple models of
> one theory *within a single logic***, with a **two-axis consumability** story
> and the **analysis-in-second-order-arithmetic** program as the driving
> example. Builds on: `surface-compiler.md` (the dispatch/effect machinery,
> hol-in-hol, lifting), `metatheory.md` (reified object logics, soundness,
> transport, the HOL-ω deferral §5.2), `covalence-pure.md` (the assumption /
> meta-assumption sets, the accelerator discharge).

---

## 1. Signature → Theory → Model

The three first-class objects, made precise:

```
   Signature   type constants + TYPE FAMILIES (with KINDS: ty, ty→ty, ty→ty→ty, …)
               + operation symbols, typed over that type part
   Specification   the laws / axioms over the signature
   Theory      = Signature + Specification
   Model       = a Logic L + objects in L (concrete types / families / ops)
               + a proof those objects satisfy the spec WHEN TRANSLATED into L
```

The decisive feature: **the signature is higher-kinded.** A signature *opens*
with its type part — type constants of kind `ty`, and **type families** of kind
`ty → ty`, `ty → ty → ty`, … — and only then gives the operations typed over it.

- **Group / Monoid / Ordered field**: type part is a *carrier* of kind `ty`
  (`α : ty`), then `op : α→α→α`, `e : α`, …
- **Monad**: type part opens with a *family* `m : ty → ty`, then
  `return : a → m a`, `bind : m a → (a → m b) → m b`.
- **Profunctor**: `p : ty → ty → ty`, then `dimap`.

A **theory** adds the spec (associativity/identities for monoid; the monad laws;
Spivak's 13 axioms for a complete ordered field). A **model** is a *host logic*
plus concrete objects in it plus the proof that, *translated into that logic*,
the objects satisfy the spec. The translation is part of the model — and not
every signature/spec translates into every logic (§3).

This is the **ML module system / typeclass** concept, made first-class *with
proved morphisms*: signature ≈ a *signature*/*class*, model ≈ a
*structure*/*instance*, a definition or proof written against the theory ≈ a
*functor* (parametric in the model).

---

## 2. Many models of one theory **within one logic** (the primary concept)

The point is **not** merely "different logics give different models." It is that
**one theory has many genuinely different *implementations* inside a *single*
logic** — and that within-logic multiplicity is first-class.

Within HOL *alone*:

- **`Nat`** — the kernel `nat`; `list unit` (unary); a `bool`-stream coding; the
  `nat` obtained by interpreting SOA's number sort.
- **`CompleteOrderedField`** — Dedekind cuts; Cauchy sequences of rationals; the
  SOA-coded reals interpreted into HOL.
- **`Monoid`** — `(nat,+,0)`, `(nat,×,1)`, `(α→α, ∘, id)` — *already built*, three
  models of one interface inside HOL.

So a theory's unit of organization is **theory (interface) + {models} +
{morphisms between models}**, where each model is a *distinct implementation*
(carrier + ops + axiom-satisfaction proof). Library content (definitions, proofs)
is written **against the theory** and **instantiated at any model**.

### 2.1 The morphisms — and reaching for isomorphic models

Models of a theory are related by **proved morphisms**; the strongest is an
**isomorphism**, which transports facts losslessly both ways. The dispatcher
keeps a *family* of in-logic models and **routes each operation to the cheapest
isomorphic representative** (`surface-compiler.md §4`): prove a fact in whichever
of `nat ≅ list unit` is easier, transport over the iso, it holds in both.

### 2.2 The unification: acceleration *is* an in-logic iso

The **efficient `nat`** (the kernel accelerator) and the **defined `nat`** are
*two models of `Nat` within HOL*, and the proof they are isomorphic **is**
`discharge(NatAccel)` from `covalence-pure.md §4.2`. So three things we designed
separately collapse into one mechanism:

> within-logic model multiplicity ≡ isomorphic-model dispatch ≡
> accelerator-soundness (the accelerator and the definition are two models + a
> proved iso).

"The accelerator coincides with its definition" is literally "here are two
models of `Nat` in one logic and an iso between them."

---

## 3. Consumability — when can a logic host a theory?

A logic `L` hosts a theory `(Σ, Φ)` only if it clears **two independent axes.**

### 3.1 Statability — can `L` *express* `Σ`'s kinds and `Φ`'s order?

| Logic | Type part it can express | Spec order |
|---|---|---|
| **FOL** | type *constants* only (kind `ty`) | first-order |
| **HOL (rank-1)** | + kind-`ty` type *variables* (polymorphism) | + higher-order |
| **HOL-ω** | + higher-kinded type *families* (`ty→ty`, …) | + higher-order |

### 3.2 Provability — is `L` *strong enough* to prove a model satisfies `Φ`?

This is the reverse-math / subsystem axis: `RCA₀ ⊂ WKL₀ ⊂ ACA₀ ⊂ … ⊂ HOL`. A
theory can be *statable* in a weak logic yet a model's satisfaction *unprovable*
there — which is exactly the analysis-in-SOA content (§5).

**The two axes are independent.** HOL-ω is about axis 1 (kinds); the
SOA-subsystem ladder is about axis 2 (strength). A logic "can't consume" a theory
either because it can't *state* it (wrong kinds/order) or can't *prove* a model
into it (too weak).

### 3.3 The polymorphism boundary (the rank-1 HOL nuance)

"HOL can host some higher-kinded cases via polymorphism" — the precise line:

- **Rank-1 HOL hosts a *generic* theory exactly when the type part is kind-`ty`
  (a carrier variable).** Monoid's `(α:ty, op, e)` → `∀'a. …` is a genuine HOL
  theorem. Models are instantiations at concrete `'a` + ops. No HOL-ω needed —
  Monoid/Group/Ring/OrderedField/vector-space-over-a-fixed-field all qualify.
- **Rank-1 HOL *cannot* host a generic theory with a kind-`ty→ty` family**
  (Monad's `m`, Functor's `f`): you can't write `∀m:ty→ty. …`. Fallbacks:
  - **per-instance** — fix `m := option`; the monad laws *for option* are a fine
    rank-1 development (each monad separate — "one ground instance at a time");
  - **meta-level** — do the genericity in Rust (our `Monoid` value carrying the
    laws), quantifying at the meta-level and sidestepping the object logic.
- **The line is "must you quantify over the constructor?"** If constructors are
  *concrete* and only the *element* type varies, rank-1 suffices —
  `∀'a. F 'a → G 'a` (a natural transformation between *fixed* `F`, `G`) is a
  good rank-1 type. You need HOL-ω precisely when the constructor itself is a
  *variable you bind*.

**Consequence.** Monad / functor / profunctor *genericity in the object logic* is
the thing genuinely blocked on HOL-ω — the concrete "theory we care about that is
unstatable in rank-1" that `metatheory.md §5.2` named as the adoption trigger.
Everything on the *current* roadmap (Monoid, Ring, the 13 axioms / analysis, the
SOA program) is kind-`ty`, so rank-1 hosts it generically; HOL-ω earns its place
when a generic Monad development becomes load-bearing.

---

## 4. The `.thy` / `.cov` shape

Splitting a theory's authoring along this architecture:

```
   real.thy            the SIGNATURE + SPEC (surface syntax) — the interface.
                       For `real`: Spivak's 13 complete-ordered-field axioms.
   real/cuts.cov       a MODEL in HOL: Dedekind cuts + the 13-axiom proof.
   real/cauchy.cov     a MODEL in HOL: Cauchy sequences + the 13-axiom proof.
   real/soa.cov        a MODEL via SOA-coded reals + the 13-axiom proof.
   analysis/…          library content written AGAINST real.thy, INSTANTIABLE
                       at any model above.
```

- The **header** (`.thy`) is surface syntax (`surface-syntax.md`); it needs the
  surface elaborator (not yet built — agent-landed inline `#def`/`#newtype`/
  `#subtype`/`#quot` in the `.cov` language is the precursor). **Don't block the
  content on the header ergonomics**: today the **givens-env** (`*_env()`
  exposing operators + axioms as givens) *is* the interface object; the `.thy`
  surface header is sugar over it, layered on later.
- "Share proofs across models" = proofs are *functors* over the theory; each
  model supplies its implementation + satisfaction proof; the library replays
  against any model. The replay *failures* (a proof that won't go through in a
  weaker model) are as informative as the successes — that's the reverse-math
  signal.

---

## 5. The driving program: how much of Spivak in second-order arithmetic

The concrete first library. Goal: develop (a useful fragment of) Spivak's
*Calculus* and see **how much replays in second-order arithmetic (Z₂)** — i.e.
reverse mathematics, with model-dispatch as the mechanism.

### 5.1 The interface — Spivak's 13 axioms

`real.thy` = the **13 axioms** (P1–P9 field; P10–P12 ordered field via the
positive cone; P13 completeness/LUB). Analysis is developed *against this
interface* — Spivak's own method ("assume P1–P13, derive the rest"), which is the
spec-vs-model structure of `surface-syntax.md §2`. Status of the 13 over the
Dedekind model: P1–P5,P8,P9 proved; P6 (`1≠0`); **P7 (`mul_inv`)** and the order
axioms being discharged now (the rat-postulate work); **P13** is the genuinely
ℝ-specific one (P1–P12 hold of `rat` too).

### 5.2 The tree (a DAG of `.cov` files — the first `compile_project` target)

```
analysis/
  field.cov        P1–P9   field consequences          ← ring/AC normalizer (built)
  order.cov        P10–P12 inequalities, |·|, sgn       ← order / SMT (Farkas seed)
  complete.cov     P13     sup/inf, Archimedean, density
  sequences.cov    Cauchy, monotone convergence
  limits.cov       ε–δ limits, limit laws
  continuity.cov   IVT / EVT / boundedness (needs P13)
  derivative.cov   rules, chain rule, MVT              ← symbolic differentiator (phase 2)
  integral.cov     Riemann integral, FTC               ← symbolic integrator (phase 2)
  elementary.cov   exp / log / trig
```

This is a DAG of mutually-aware `.cov` files — exactly what the landed
`compile_project` (`docs/cov-project.md`) builds, replacing the hand-written
`library_env` wiring. **First milestone: chapters 1–8** (axioms → completeness →
continuity → the three hard theorems); derivatives/integrals are **phase 2**.

### 5.3 Three automation layers (handlers, in the effect-system sense)

1. **Algebraic identities** → the **ring/AC normalizer** (`ac.rs`,
   `ring/normalize.rs` — built).
2. **Inequalities** → **order / SMT**. The Alethe **Farkas/`la_generic`**
   prototype is the seed; generalize to n-literal QF_LRA over `rat`/`real`.
3. **Calculus** → a **proof-producing symbolic differentiator** (a rewriter
   `f ↦ ⊢ deriv f = f'` over the proved rules), later an integrator.

### 5.4 SOA as an internal theory + the transport showpiece

The metatheory core, scaling the proved `init/prop.rs` recipe (reify → derive →
denote → prove-sound-internally):

- **Phase 1 — reify Z₂ in HOL, prove sound.** Multi-sorted (number + set vars),
  atomic `t=s`/`t<s`/`t∈X`, the formula datatype, `Derivable_SOA` (PA⁻ +
  second-order induction + comprehension), denotation `⟦·⟧` (numbers→`nat`,
  sets→`nat→bool`), and `⊢ Derivable_SOA ⌜A⌝ ⟹ ⟦A⟧`. **HOL models Z₂ cleanly**
  (full comprehension = HOL λ-abstraction), so soundness is direct *and* the
  denotation `⟦·⟧` **is** the transport interpretation — Phase 1 and Phase 4
  share their core.
- **Phase 2 — tracer bullet**: one theorem proved in SOA, transported to HOL.
- **Phase 3 — replay across models**: build `nat` (+ a subset of inductive
  types) *as a model in SOA* exposing the *same* `.cov` interface as HOL's `nat`,
  and replay the proof scripts (needs the `#model`/`#in` dispatch). This is "many
  models of one theory" with one model in HOL and one in SOA, side by side.
- **Phase 4 — internal HOL + `SOA(A) ⟹ HOL(A)` as objects**: reify HOL in HOL
  (hol-in-hol), prove the morphism between the two *reified* theories, and
  **transport** an SOA theorem to internal-HOL rather than re-prove it. First-
  class metatheory made visible.
- **Phase 5 — analysis-in-SOA**: code reals as sets-of-naturals, instantiate the
  analysis functors at the SOA model, measure what replays (the reverse-math
  payoff). Long-horizon, research-grade.

Recommended near-term commitment: **Phases 1 + 2** (SOA sound + one transported
theorem); 3–5 as the roadmap. Reify **full Z₂ first** (clean soundness/transport;
HOL models it); the RCA₀/ACA₀ *subsystem* stratification — where the real
reverse-math content lives — is a *refinement* (restrict which comprehension
instances `Derivable_SOA` admits) layered on after.

---

## 6. What's already built that feeds this

- `compile_project` (`docs/cov-project.md`) — the multi-file `.cov` DAG builder
  (`analysis/`'s build path).
- Inline `.cov` definitions (`#def`/`#newtype`/`#subtype`/`#quot`) + the
  equivalence test vs core's parser — the precursor to `.thy` headers.
- `sexp` (tree-based, polymorphic Lisp cons-cell) — the recommended substrate for
  reifying object-language syntax (over the list-based `sexpr`).
- `ring/normalize.rs` + `ac.rs` (algebra) and the Alethe Farkas prototype (SMT) —
  two of the three automation layers, seeded.
- `init/prop.rs` — propositional logic reified + **proved sound internally**: the
  working prototype the SOA reification scales up.
- The ≥2-rec-arg inductive engine + `tree`/`sexp` — substrate for reified syntax.
- The `order`/`preorder` and `monoid` model-generic developments — the first
  in-logic "theory + several models" instances.

---

## 7. Open forks (decisions pending)

1. **Fix the waist — and at HOL Light (rank-1) or HOL-ω?** **RESOLVED:** the
   *final* waist is **HOL-ω** (to program the middle language like Haskell — the
   endgame is a self-bootstrapping HOL-ω→WASM compiler with translation-validated
   soundness); the path is **HOL Light → HOL Light over `covalence-pure` → HOL-ω
   over `covalence-pure`** (HOL-ω is easier to state over the simple Pure base,
   and its API is a superset of HOL Light's so the migration is additive *if*
   `covalence-hol` keeps direct rank-1-polymorphism use concentrated). See
   [`kernel-design.md §11.6`](./kernel-design.md).
2. **Model granularity** — is "acceleration" an *attribute of* a model, or a
   *separate iso-related model*? (Lean: separate model + iso, keeping each model
   clean — consistent with §2.2.)
3. **`real`: fixed-at-the-concrete-type vs parametric `CompleteOrderedField`** —
   lean fixed-at-`real` first (decoupling benefit now), abstract when the surface
   `#theory`/`#model` machinery lands.
4. **SOA: full Z₂ first vs subsystem-stratified from the start** — lean full Z₂
   first; subsystems as a refinement.
5. **First analysis milestone: chapters 1–8 vs pulling derivatives/integrals
   early** (the latter prioritizes the symbolic differentiator sooner).

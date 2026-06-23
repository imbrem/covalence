# Theories, models, and logics — the signature/theory/model architecture

> **DESIGN RECORD.** Refines [`surface-compiler.md`](./surface-compiler.md)'s
> "many models" idea into a precise **signature → theory → model** architecture,
> centred on **multiple models of one theory within a single logic**, with a
> **two-axis consumability** story, the **analysis-in-SOA** driving example, and
> **Metamath as the shared logic-definition substrate** (§5.6). Builds on
> [`metatheory.md`](./metatheory.md) (reified object logics, transport) and
> [`covalence-pure.md`](./covalence-pure.md) (the assumption / meta-assumption
> sets).

---

## 1. Signature → Theory → Model

The three first-class objects, made precise:

```
   Logic       a LANGUAGE (typed grammar / type theory — what can be STATED) PLUS
               derivability rules (what can be PROVED), BUNDLED as one object
               (e.g. classical FOL, intuitionistic FOL — two logics over the SAME
                language, related by a language-ISO, not a shared-identity syntax)
   Signature   type constants + TYPE FAMILIES (with KINDS: ty, ty→ty, ty→ty→ty, …)
               + operation symbols, typed over that type part — in a logic's language
   Specification   the laws / axioms over the signature (formulas in the language)
   Theory      = Signature + Specification
   Model       interprets the SIGNATURE's symbols as objects — an interpretation of
               the language (pure semantics; no axioms); models related by ISO-TRANSPORT
   M ⊨ T       "M is a model of theory T": a PROOF, in a LOGIC, that M's
               interpretation satisfies T's spec
```

**A logic bundles its language and its rules — kept as *internal aspects of one
object*, deliberately *not* two separately-shared ones.** Conceptually a logic
has two parts: a *language* (the typed grammar — terms/formulas/kinds — what can
be *stated*; logicians' "language", `admits` below is its well-typedness
judgment) and a *derivability relation* (the rules — what can be *proved*).
Intuitionistic and classical FOL share a language and differ only in `⊢`. **But
we do *not* reify the language as a separate object that logics reference by
identity** — "do `L₁` and `L₂` have *the same* language?" asked as an *equality*
distinguishes isomorphic languages and is **evil** (non-invariant), cutting
against this doc's own "always reach for isomorphic models". So: language + rules
**bundle into the `Logic` object**, and "these two logics share a language" is a
*language-isomorphism* (a morphism up to iso — for int/classical FOL, the identity
translation plus the `LEM` extension), never an identity. **A model interprets a
logic's language** (semantics, indifferent to the rules) and models relate by
**iso-transport**; **`M ⊨ T` is proved in a logic** (which logic is part of the
claim — a Heyting-valued `M` satisfies the intuitionistic `T`, a Boolean one the
classical `T`). This is still the Isabelle/Pure shape — a substrate logic (HOL-ω,
Pure's typed λ-calculus with `≡`) carrying object logics (FOL/PA/…) that add `⊢` —
just without an evil shared-syntax identity between them.

> **A refinement to revisit (user — note for later).** Reifying a syntax object is
> *not* evil after all, **if** we view it as the concrete object **constructed by a
> `#thy`** (its reified formulas/syntax), equipped with *several separate, partial*
> **projections** into target logics — `⟦·⟧_HOL`, `⟦·⟧_ZF`, … — which are
> themselves things we reason about (the `peano/` deep embedding's `denote` is one
> such projection). The earlier "evil" worry was about asserting an *identity*
> between two logics' languages; a `#thy`-constructed syntax object with reasoned-about
> *partial projection maps* is legitimate (and is exactly the deep-embedding +
> multiple-target-logics picture). Hold this for when `#thy` reification + the
> projection maps are built out.

The decisive feature: **the signature is higher-kinded.** A signature *opens*
with its type part — type constants of kind `ty`, and **type families** of kind
`ty → ty`, `ty → ty → ty`, … — and only then gives the operations typed over it.

- **Group / Monoid / Ordered field**: type part is a *carrier* of kind `ty`
  (`α : ty`), then `op : α→α→α`, `e : α`, …
- **Monad**: type part opens with a *family* `m : ty → ty`, then
  `return : a → m a`, `bind : m a → (a → m b) → m b`.
- **Profunctor**: `p : ty → ty → ty`, then `dimap`.

A **theory** adds the spec (associativity/identities for monoid; the monad laws;
Spivak's 13 axioms for a complete ordered field). A **model** realizes the
signature's vocabulary as concrete objects in a host — that realization is an
interpretation of the *syntax*, and is pure semantics (it does not yet mention
the spec). The claim that those objects *satisfy the spec* is then a separate
proof, `M ⊨ T`, carried out in a *logic* over the syntax (§1.1). Not every
signature is statable in every syntax, and not every spec is provable in every
logic over it (§3 — the two-axis consumability).

This is the **ML module system / typeclass** concept, made first-class *with
proved morphisms*: signature ≈ a *signature*/*class*, model ≈ a
*structure*/*instance*, a definition or proof written against the theory ≈ a
*functor* (parametric in the model).

### 1.1 Two seams: `Logic` (language + rules, bundled) and `Model` (interpretation)

The single `Logic` object bundles its language and its derivability rules (§1 —
splitting them into a separately-*shared* syntax object would be evil). A `Model`
is separate, because a model is a genuinely different kind of thing — a structure,
related to logics by `⊨` and to other models by iso-transport, never quotiented
by identity. So **two** seams, not three:

- **`Logic` = language + rules.** `admits` is the *language* aspect (statability,
  §3.1 — does its grammar's kinds reach this signature? FOL *refuses* a `ty→ty`
  family). `handlers` is the *rules* aspect (the proof-side dispatch — rewriting,
  induction, reduction, LEM-or-not — genuinely *varied per logic*). These are two
  *aspects of one object*; "same language" across logics is a morphism up to iso,
  not a field they share.
- **`Model` = meaning.** An interpretation of a logic's *language*: it realizes
  each signature symbol as a concrete object and lowers surface literals into its
  carrier. Pure semantics — says nothing about axioms.

```rust
/// LOGIC — bundles a LANGUAGE (a type theory: what can be STATED) and DERIVABILITY
/// rules (what can be PROVED) as ONE object. Language + rules are internal aspects,
/// NOT two shared objects — "same language?" by identity would be evil.
trait Logic {
    fn admits(&self, sig: &Signature) -> Result<(), Unstatable>;   // language aspect (§3.1)
    fn handlers(&self) -> HandlerSet;                              // rules aspect (per logic)
    /// Literal POLICY (not realization): which literal kinds this logic admits
    /// and at what target sort. `None` = this logic has no such literal. The
    /// model (below) realizes an admitted literal into its carrier. (`nat`
    /// literal = a non-negative `int` literal — one entry.)
    fn literal_sort(&self, kind: LiteralKind) -> Option<Sort>;     // language aspect
}

/// MODEL — interprets a signature's symbols as objects (semantics; no axioms);
/// models relate to each other by ISO-TRANSPORT. Literal-lifting is the model
/// realizing surface literals into its carrier.
trait Model {
    fn interpret(&self, sig: &Signature) -> Result<Interpretation, …>;
    /// --- LITERAL LIFTING (model-relative; each may FAIL) ---
    /// A surface literal is lowered into THIS model's carrier — and a model may
    /// legitimately reject a kind (Err). A Nat literal is a non-negative Int one.
    fn lift_int(&self, n: &Int)    -> Result<Term, NoLiteral>;
    fn lift_string(&self, s: &str) -> Result<Term, NoLiteral>;
    fn lift_bytes(&self, b: &[u8]) -> Result<Term, NoLiteral>;
}
```

A **model** is `(a Model interpretation over a Logic's language)` alone — *not*
the satisfaction proof. **`M ⊨ T`** is a separate object: a proof, **in a
`Logic`**, that `M`'s interpretation satisfies `T`'s spec (`surface-compiler.md
§3.0.2`; it is a `.thm`, and which logic it's proved in is part of the claim). So
the seams collaborate as: `Logic` gates *statability* and supplies *proof power*,
`Model` supplies *meaning*, and `M ⊨ T` is the theorem that ties a model to a
theory. (This is what Track 1 built: its `Logic` bundles `nat_model()` =
interpret + handlers, with no separate syntax object.)

**Literal lifting is a `Model` method — model-relative and fallible.** The
surface literal `3` is not one fixed kernel term; the *model* decides how to lower
it into its carrier (`surface-compiler.md §5`). The *logic* only fixes the
**policy** — whether the literal is admitted and at what target *sort*
(`literal_sort` above) — while the **model** fixes the *value* (the carrier term);
two models of one theory in one logic lower `3` differently
(`surface-compiler.md §3.0.5`). For `nat/self` (kernel `nat`)
`lift_int(3)` is the built-in literal; for **`nat/unary`** (`list unit`) it runs a
model-supplied **builtin-nat → unary conversion** (`3 ↦ cons unit.nil (cons
unit.nil (cons unit.nil nil))`); for a reified-SOA model it is the object numeral
`S(S(S 0))`. A model with no sensible lift returns `Err(NoLiteral)` — a
diagnostic, not a silent coercion. (A **Nat** literal is exactly a non-negative
**Int** literal, so there is a single `lift_int`; string/byte are the same shape.)
This is the `covalence-pure` literal-as-lifted-observation mechanism
(`covalence-pure.md §3`) surfaced as a `Model` responsibility. This
`Logic`+`Model` two-seam split is the Rust-level realization of the
logic/theory/model architecture, and the substrate the HOL-ω migration slots into
(HOL-ω is a new `Logic` whose bundled language has a richer `admits`, *reusing*
the existing `Model` seam).

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

## 5. The driving programs: the analysis library + the reified-theory ladder

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
`compile_project` (`notes/cov-project.md`) builds, replacing the hand-written
`library_env` wiring. **First milestone: chapters 1–8** (axioms → completeness →
continuity → the three hard theorems); derivatives/integrals are **phase 2**.

### 5.3 Three automation layers (handlers, in the effect-system sense)

1. **Algebraic identities** → the **ring/AC normalizer** (`ac.rs`,
   `ring/normalize.rs` — built).
2. **Inequalities** → **order / SMT**. The Alethe **Farkas/`la_generic`**
   prototype is the seed; generalize to n-literal QF_LRA over `rat`/`real`.
3. **Calculus** → a **proof-producing symbolic differentiator** (a rewriter
   `f ↦ ⊢ deriv f = f'` over the proved rules), later an integrator.

### 5.4 The reified-object-theory ladder (prop → PA → SOA, and beyond)

> **Revised sequencing (user):** don't jump straight to SOA. Climb the ladder —
> **propositional logic → Peano arithmetic → second-order arithmetic** — building
> reusable *first-order-logic and theory* tooling at each rung. Each rung is the
> same recipe (`init/prop.rs`): reify the syntax as a datatype → an inductive
> `Derivable_X` predicate → a denotation `⟦·⟧` into HOL → **soundness proved
> internally** → the transport morphism. **Induction on derivations** (rule
> induction, the impredicative `inst d := P`) is the through-line skill.

**Rung 1 — propositional logic.** Already reified + proved sound (`init/prop.rs`);
the near-term work is `prop.cov` exposing it in the script language, with
**induction-on-derivations packaged as a first-class principle** — and a
deliberate *stress test* of the `.cov` language over reified syntax (the surface
gaps it surfaces drive the next language features). This is the cheapest place to
nail the metatheory loop end-to-end.

**Rung 2 — Peano arithmetic, and FOL tooling in general.** PA = first-order logic
(terms, formulas, capture-avoiding substitution, ∀/∃) + the arithmetic signature +
the **induction schema**; soundness via HOL `nat`. This is the big reusable
investment: a generic **first-order-theory framework** (the syntax of FOL, a
`Derivable` engine parameterized by a signature + axioms, the denotation
machinery) that *every* later theory reuses. **Knowing a result is PA-provable is
itself a useful certificate** — a large fraction of mathematics lives in PA, and
PA-provability bounds a theorem's logical strength. The FOL framework is what
rung 1's stress-test gaps tell us to build.

**Rung 3 — second-order arithmetic (Z₂).** Multi-sorted (number + set vars),
`Derivable_SOA` (PA⁻ + second-order induction + comprehension), denotation
(numbers→`nat`, sets→`nat→bool`). **HOL models Z₂ cleanly** (full comprehension =
HOL λ-abstraction), so soundness is direct *and* the denotation **is** the
SOA→HOL transport interpretation. Then the showpiece: reify HOL in HOL
(hol-in-hol), prove `SOA(A) ⟹ HOL(A)` between the two *reified* theories, and
**transport** an SOA theorem to internal-HOL rather than re-prove it — first-class
metatheory made visible. Reify **full Z₂ first**; the RCA₀/ACA₀ subsystem
stratification (the real reverse-math content, and the home of analysis-in-SOA,
§5.2/Phase 5) is a *refinement* layered on after.

**Other first-order theories worth building** (each a `Derivable_X` + soundness +
transport over the FOL framework from rung 2):

| Theory | What it is | Why |
|---|---|---|
| **Robinson Q** | PA minus induction (finitely axiomatized) | the base of essential undecidability / Gödel; the weakest "arithmetic" |
| **Presburger** | FO theory of `(ℕ, +)` | **decidable** (a real decision procedure to build — a handler) |
| **Tarski RCF** | real-closed fields (FO theory of `(ℝ, +, ·, <)`) | **decidable** by quantifier elimination — the decision procedure behind real-algebra automation; pairs with the analysis/SMT layer (§5.3) |
| **ZF / ZFC / Tarski-Grothendieck** | first-order set theory of `∈` (ZFC = ZF + choice; **TG** = ZFC + universes/inaccessibles) | the long-horizon big goal. ZF/ZFC/TG differ *only in axioms* — all ride the same FOL framework, so reifying their **syntax + derivability is essentially free** |

The decidable ones (Presburger, RCF) are doubly valuable: they're object theories
*and* they yield **decision-procedure handlers** the surface can dispatch to
(`surface-compiler.md` effect dispatch) — the same way the Farkas/Alethe work
yields a linear-arithmetic handler.

**Near-term commitment:** rung 1 (`prop.cov` + induction-on-derivations, in
progress), then the FOL framework + PA (rung 2). SOA, the FO-theory catalogue, and
analysis-in-SOA follow once the FOL tooling is solid.

### 5.5 Two pillars of metatheory, and the PA→SOA→ZF chain

Doing metatheory *here* rests on two pillars, both living in `init/prop.rs`'s
proven, TCB-free reify-syntax-as-HOL-data lane (the substrate PA's `peano/fol.rs`
already established):

1. **Induction on derivations → interpretation.** `PA ⟹ SOA ⟹ ZF` are *relative
   interpretations*, proved **by induction on derivations** (translate each axiom,
   show its translation is provable in the target, check each rule is preserved).
   Two grades: the **constructive / per-derivation** form (a Rust recursion over
   how derivations are built — what PA's `Derivation` does today for `PA⟹HOL`) and
   the **internalized** single HOL metatheorem (`⊢ Derivable_X ⌜A⌝ ⟹ …`, via the
   impredicative rule-induction — `prop_induction` is the proven template).
   **Interpretation is *syntactic*: it does NOT require the target theory to have a
   HOL model.** So the whole chain is provable from reified syntax + the
   rule-induction engine.

   > **The proper-deep-embedding test (user).** The internalized form is not just
   > "nicer" — it is what a *proper* deep embedding **requires**. `Derivable_PA`
   > must be **pure syntactic data** (a derivation carries *no* HOL `Thm`), and the
   > projection to HOL is **one step**: apply the soundness theorem to a finished PA
   > derivation. The acceptance test: *you derive in PA without ever building the
   > HOL theorem, then project in a single move.* PA's current `Derivation` (a
   > formula paired with its `Thm`, built lock-step) is the *shallow hybrid* that
   > **fails** this test — it proves the HOL theorem *while* deriving. Fixing this
   > (pure `Derivable_PA` + the one-step soundness projection) is the priority for
   > the PA thread; it is exactly the deferred `prop.rs`-style internalized
   > soundness theorem, promoted from afterthought to primary structure.

2. **Representation equivalence → syntactic metatheory.** A metatheorem *in HOL*
   that two syntax/substitution representations agree (de Bruijn ↔
   metavariable/Metamath ↔ named ↔ HOAS). This is how you change representation
   soundly, transport substitution lemmas, and — load-bearing — **admit WASM
   decision procedures**: an untrusted fast oracle works on an *efficient*
   representation, and proving *that representation ≅ kernel-syntax* in HOL lets its
   results transport soundly (the observer substrate at the *syntactic* level).

**We are not in the business of proving ZF/ZFC *sound* (scoped truths, user).**
The standard theorem here is "**φ holds in ZFC**", *not* "φ holds" — truths are
**scoped to a theory** (`notes/VISION.md`, metatheory-as-default). The outer HOL is
not there to certify an absolute model of ZF; it is there to reason about
**transport between scopes** — "what holds in ZF holds in HOL" (under the relevant
interpretation), "what holds in PA holds in ZF", and so on. Those transports are
the `Derivable_X ⟹ …` interpretation theorems of pillar 1, and (per pillar 1) they
are **syntactic — they need no model of the source or target.** So the working mode
is: derive within a scope, and transport between scopes; *absolute* soundness is
not the goal.

**The PA/SOA-vs-ZF asymmetry, in that light.** PA denotes into HOL `nat` and SOA
into HOL `nat → bool`, so they *happen* to have unconditional HOL models (SOA cheap:
HOL has the sets) — handy, but still just one scope (`HOL`) among the targets. **ZF
has no HOL model without added strength** (Gödel: HOL ⊬ `Con(ZF)`), but this rarely
bites, because we want scoped ZF truths + transport, not a HOL model of ZF. *If* one
ever wants an absolute model, it is **gated on a universe** —
`⊢ (∃ inaccessible) ⟹ Model(ZFC)` — which is exactly what **Tarski-Grothendieck**
supplies (the Mizar move), making TG the natural *top*. But that is the exception,
not the program.

**Metamath import** is where both pillars meet: `set.mm` is FOL + ZFC, so the
reified FOL+ZFC framework is its object substrate, and a Metamath proof is replayed
as an **untrusted frontend → kernel re-derivation** (the Alethe pattern). Metamath's
metalogic is a trivial *metavariable-substitution + distinct-variable* engine;
encoding it and proving `mm_subst ≅ locally-nameless` (pillar 2) is the sound
import bridge — and doubles as the first, cleanest instance of the WASM-decision-
procedure admission protocol. (Replay/verification is proof-theoretic, so it needs
no ZF model; only *transporting* a `set.mm` theorem into a HOL fact hits the
universe wall.)

**Recommended build order:** internalized rule-induction for PA (small: template +
two-sorted Church fold) → generalize to the FOL `Derivable` engine (interpretations
become first-class) → SOA (cheap denotation) → reify ZF/ZFC/TG (axioms only) +
`SOA⟹ZF` → the Metamath substitution engine + its `≅ locally-nameless` metatheorem.

### 5.6 Metamath as the shared logic-definition substrate (user reframe)

A sharpening that ties the pillars together and elevates `covalence-metamath`
from "an import target" to **the substrate**: a **logic *is* a Metamath
database** — symbols, typed variables, and its axioms/inference rules as
substitution schemas. The pure metavariable-substitution metalogic is universal
and theory-agnostic, so prop calc, FOL, ZFC, PA, modal logics all become
databases in *one shared syntax everyone writes their logic in*. (This is why the
crate's medium is `SExpr` and the encoding is faithful flat sequences — it's the
shared substrate; the HOL kernel, structured-tree encodings, and set.mm scale are
all **optimizations over it**.)

**The grounding — one primitive, one existential, proof-irrelevant (user).** The
*primitive* is the **decidable valid-proof relation** `ValidProof(P, S, A)` — "`P`
is a valid Metamath proof of statement `S` under axioms `A`" — exactly what
`metamath::verify` *checks* (a concrete proof object, mechanically validated). The
*one* derived notion is the **existential** `Derivable_A(S) := ∃P. ValidProof(P, S,
A)` — "*there exists* a (possibly astronomically long) valid proof". **Proof-
irrelevance is the name of the game:** we care only that a proof *exists*, never
which one — two proofs of `S` are interchangeable and we never manipulate the giant
`P` (HOL makes this automatic: `Derivable_A(S)` is a mere proposition). This is the
**thin waist at the *inner-logic* level**: every inner/object logic maps *into*
Metamath as an axiom-set `A`, and the metatheory is **proving equivalences between
Metamath variants** — conservative extensions, interpretations, `A₁ ⊑ A₂` — as
relations between databases. (Distinct from the *outer* waist: HOL-ω over Pure is
the metalogic we reason *in*; Metamath is the inner waist object logics reduce
*to* — cf. [[pure-narrow-waist-direction]].) Four locking pieces:

1. **The standard theorem's *meaning* is that existential.** Asserting `S` in a
   Metamath-defined logic `A` means **`Derivable_A(S) = ∃P. ValidProof(P, S, A)`**.
   We never exhibit `P`, only certify it exists — the rigorous form of the scoped
   truth "`S` holds in `A`" (§5.5): a HOL-kernel proof, a WASM oracle, a replayed
   set.mm proof are each just a *more practical certificate of the same existence
   claim* (proof-irrelevance is what makes them interchangeable).
2. **Metatheorems = existence-transport via a rewriting function `S`.** The shape
   is `Derivable_ZF(A) ⟹ Derivable_GT(S(A))`, where `S` is a computable rewrite on
   Metamath `SExpr` terms, proved **by induction on the source derivation** (each
   rule instance → an image derivation under `S`) — so the giant target derivation
   is *certified to exist without being built*. This is pillar 1's interpretation,
   now **native in the substrate**; PA→SOA→ZF→GT and model↔model become `S`-functions
   over databases.
3. **The correspondence `Metamath-L ≅ native-L` is one theorem, two directions.**
   *Down / validation:* `Metamath-PA ≅ our PA` anchors that the `.mm` *definition*
   of PA means what we expect (without it a database is just symbols + schemas).
   *Up / acceleration:* the same `≅` lets native PA, the HOL kernel, and WASM
   decision procedures **optimize** `Derivable_{mmL}` goals — run fast natively,
   transport the result across the correspondence. This is the
   `≡ iso-dispatch ≡ accelerator-discharge` identity (§2), now anchored on the
   Metamath substrate, and the same admission protocol as pillar 2.
4. **Convergence with `.logic` (§3.0.5 of `surface-compiler.md`) — the unifying
   answer for `#logic`.** A `.logic` — the *data* parameterizing a generic `Logic`
   impl for a family — **is a Metamath database**: axioms + rules as substitution
   schemas. So "define a logic" and "write a Metamath database" are the same act,
   and the HOL bridge is `S`-into-`IsThm` (the shallow-embed-future target).

**A HOL type for databases, and the relation lattice (user).** To do the
metatheory *inside* HOL we need databases to be **first-class HOL data** — a HOL
type `Database` reifying (constants, typed variables, axiom/rule schemas, DV
conditions), so HOL can quantify over databases and state `Derivable_A(S) :=
∃P. ValidProof(P, S, A)` with `A` a HOL value. On that type, define the **relations
between databases** (the "equivalences between variants" made precise) — climbing
in strength:
- **Extension** `A ⊑ B` — `B` has all of `A`'s constants + axioms. The basic
  theorem is **monotonicity**: `A ⊑ B ⟹ Derivable_A(S) ⟹ Derivable_B(S)` (more
  axioms ⟹ more derivable).
- **Interpretation under a renaming/substitution** `A ⟹_σ B` — a translation `σ`
  maps `A`'s vocabulary to `B`-expressions with `σ`(every `A`-axiom) `B`-derivable.
  Its theorem is **transport**: `Derivable_A(S) ⟹ Derivable_B(σ(S))` — this *is*
  the `S`-rewrite of point 2, now a *relation on the database type* (`σ` = the `S`).
- **Conservative extension** — `A ⊑ B` and, restricted to `A`'s language,
  `Derivable_B(S) ⟹ Derivable_A(S)` (`B` proves nothing new about `A`'s language).
- **Equivalence** `A ≅ B` — mutual interpretation.

These compose into a category of databases (objects = databases, morphisms =
interpretations), and PA→SOA→ZF→GT, conservative-extension chains, and
`Metamath-L ≅ native-L` all live in it. Building the `Database` HOL type + `⊑`
(monotonicity) + `⟹_σ` (transport) is the foundational first cut; conservative
extension and `≅` layer on.

**Crate boundary (user, important).** Because Metamath *is* the logic-definition
substrate, **the engine belongs first-class in `covalence-hol`** — the `SExpr`
expression model, substitution, frame/DV, the verifier, `Derivable_L`, the
`S`-rewrite transport, and the `Metamath-L ≅ native-L` correspondence. That is core
to defining logics and doing metatheory, so it must not live off in a side crate.
**`covalence-metamath` is demoted to the format/IO reader**: compressed-proof
decoding, `.mm` file parsing, `$[ $]` file inclusion, and set.mm-scale ingestion —
the messy format concerns we *don't* want cluttering `covalence-hol`. So the move
is: relocate the engine (`expr`/`subst`/`database`-model/`verify`) into
`covalence-hol/src/metamath/`, and slim `covalence-metamath` to a frontend that
depends on `covalence-hol` and produces its databases. **Near-term value** then
sits in `covalence-hol`: *define logics* (FOL, a real ZFC fragment, modal logics as
databases) and study `Derivable_L` / `S` / the correspondence — *not* racing to
set.mm-scale ingestion (one consumer's optimization, and the reader crate's job).

### 5.7 The stack, the elevated `covalence-metamath`, and why nothing is wasted

This whole substrate is the **top layer of the three-layer stack**
(`VISION.md` §1): bottom = executors + content-addressing (disk + CPU, the root of
trust); middle = HOL (HOL Light → HOL-ω, the metalogic, "generalized Haskell" with
proven-WASM compilation and lazy-by-default evaluation); **top = *internal*
Metamath, the thin waist** — `∃D. ValidProof(D, P, Ax)`. Every internal logic
(FOL/HOL/ZFC/GT/MLTT/LF/Dedukti) passes through it, which is what gives a *uniform*
notion of conservative extension, syntax translation, and "proving what we think we
prove" (soundness w.r.t. the Metamath base). Efficient encodings (de Bruijn, …) are
HOL data structures proven sound against that base — Metamath both pins the meaning
and lets us swap encodings freely behind proven equivalences; and since we **never
look at the proofs** (only assert one exists), the databases stay dead-simple
(ZFC/CTL/… are *just their axiom sets*).

**`covalence-metamath` is therefore *not* merely a demoted reader — it is the
independent oracle.** Its load-bearing job is to hold **independent elaborators of
Metamath databases into HOL**, so we can **sanity-check that the output of `#logic`
is at least equivalent to — preferably syntactically *equal* to — the canonical
Metamath database** for that logic. For databases like Grothendieck-Tarski (or
ZFC) the canonical database can be **fetched from the Internet** and diffed against
what `#logic` produces. It is also where **set.mm ingestion** lives — a *one-and-done*
import, **symbolic at first** (trust the imported database as an axiom set we then
relate to ours); **later**, once we have a *verified Metamath checker compiled to
WASM*, we can ingest via the verified checker + its verification proof (this adds
the **WASM executor to the base trust set**, versus pure in-HOL interpretation — a
deliberate trust-vs-throughput trade).

**Nothing we have already built is wasted.** Our native `peano::pa` / HOL
developments are not superseded by internal Metamath — they are **proven equivalent
to `Metamath-PA`** (`§5.6` (3), the `≅`). That equivalence cuts both ways: the
native development is often **more convenient for direct use**, *and* it is exactly
what lets us **prove `Metamath-PA` (and eventually `Metamath-SOA`) sound**. The
HOL-database relation lattice (`§5.6`, `metalogic::{database,relations}`) is the
machinery these equivalences and conservative extensions are stated in.

---

## 6. What's already built that feeds this

- `compile_project` (`notes/cov-project.md`) — the multi-file `.cov` DAG builder
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

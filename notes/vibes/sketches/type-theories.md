+++
id = "N0032"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-03T21:05:38+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Type theories as object logics — MLTT, book HoTT, NuPRL, and IZF→MLTT

> **STATUS: DESIGN SKETCH.** How dependent type theories enter Covalence as
> object logics over the Metamath thin waist, and how set-theory→type-theory
> translation works. Part of the [`logic-frontends.md`](../logics/logic-frontends.md)
> umbrella; see it for the four-artifact pattern and the difficulty axes. The
> binding-representation `≅` here is pillar-2 of
> [`metatheory.md`](../logics/metatheory.md) §5.5; the transport `S` is pillar-1.

---

## 1. Shared shape: a type theory is a database of judgment rules

A dependent type theory `L` is, in the waist, a database `D_L` over four
**judgment forms**, each a typecode in the grammar:

```
   Γ ⊢ A type            A is a type in context Γ
   Γ ⊢ a : A             a inhabits A
   Γ ⊢ A ≡ B             definitional type equality
   Γ ⊢ a ≡ b : A         definitional term equality
```

Each rule of `L` (formation / introduction / elimination / computation, plus the
congruences and the conversion rule) becomes a Metamath axiom: a substitution
schema over these typecodes. `Derivable_L(J)` = "a derivation of judgment `J`
exists." As always (umbrella §1) this is pure existence — we replay `L`'s proof
trees into the engine's constructors and never inspect the witness.

The whole family — LF, MLTT, book HoTT, NuPRL, CIC — shares this skeleton. They
differ in (a) how binding is represented, (b) which type formers the database
has, and (c) the computation/equality discipline. (a) is written once and reused;
(b) is bulk; (c) is where NuPRL diverges sharply.

## 2. The binding decision (write once, reuse for all)

Metamath has no native binders. Two honest routes; we recommend the first as the
*abstract* base and the second as a *model*:

- **(a) Algebraic / CwF presentation — binder-free.** Present `L` as a *category
  with families*: contexts, substitutions-as-morphisms, `Ty Γ`, `Tm Γ A`,
  comprehension `Γ.A`, type formers as algebraic operations with naturality
  (Beck–Chevalley) equations `Π(A,B)[σ] = Π(A[σ], B[σ↑])`. **No object-level
  variable binding** — it is a first-order equational theory, which is *exactly*
  what the waist's substitution handles natively. Cost: the substitution-law
  bureaucracy (every former needs its naturality equation; the weakening/`↑` laws
  are the coherence-hell). This is the canonical `D_L`.

- **(b) Raw de Bruijn syntax + a typing relation.** `Tm`/`Ty` as encoded SExpr
  terms (never unfolded — the `Derivable_… ⌜S⌝` discipline), capture-avoiding
  substitution as a syntax function, rules over `Derivable_L`. de Bruijn (not
  named) so α-equivalence is definitional and needs no quotient.

"Relate it to a locally-nameless impl, a de Bruijn impl, etc." is served by
making (a) the representation-independent interface and (b) (and
locally-nameless, and HOAS) concrete models of it. Each model proves the CwF
axioms; "two implementations agree" is an equivalence of CwFs. This is pillar-2
representation equivalence, written once for the family — every type-theory
frontend reuses it.

## 3. MLTT (predicative) — the base

Difficulty: **moderate, mostly mechanical bulk** (no hard theorems for the
axiom base itself; umbrella §4 row "MLTT").

- **Infrastructure first:** the four judgment forms + the binding discipline (§2).
- **Type formers:** Π, Σ, Id, +, ℕ, ⊤/⊥, plus the conversion rule
  (`Γ ⊢ a : A`, `Γ ⊢ A ≡ B` ⟹ `Γ ⊢ a : B`).
- **Two sub-decisions that carry weight:** universes — use **Tarski** (`El`/decode,
  an ℕ-indexed cumulative hierarchy); cleaner to state in a binder-weak substrate
  than Russell. And how the **equality congruences** are bundled — they are the
  single biggest source of axiom count (one per former).
- **`+model`:** predicative MLTT has an *in-HOL* model (interpret types as HOL
  sets / setoids over a universe), so the semantic bridge is available without
  added strength. Crib the *content* from the Agda/Coq CwF formalizations (the
  "type theory in type theory" line, Abel–Öhman–Vezzosi); note that **no Metamath
  MLTT exists off the shelf** (set.mm is ZFC; iset.mm is IZF — still set theory).

## 4. Book HoTT = MLTT + univalence + HITs

Difficulty: **MLTT + a little + one fiddly bucket.**

- **Univalence: cheap.** Given `Id`, the universe, and the definables
  `isEquiv`/`≃`/`idtoeqv` (the last via J), univalence is *one axiom*: an
  inhabitant of `isEquiv(idtoeqv)`. The only work is the page of definitions to
  state it. The algebraic presentation (§2a) absorbs it cleanly.
- **HITs: the fiddly part, but bounded.** No settled general HIT schema exists,
  and we do **not** want one in the database. Pick a **finite menu** (S¹,
  suspension, propositional/set truncation, pushout, quotient — whatever is
  needed) and postulate each as a small cluster: point constructors, *path*
  constructors, the dependent eliminator, and β-rules. Two hazards: the
  path-constructor computation rules hold only **propositionally** (inhabitants of
  an identity type, not judgmental) — state them that way; and the dependent
  eliminator's path-β needs `transport`/`apd` defined first — the bookkeeping is
  the fussiest part. Each HIT is a handful of axioms; bounded, *not* open research
  as long as the menu is fixed.
- **Precedent:** the HoTT book §10.5 already builds the cumulative hierarchy `V`
  as a HIT and verifies a constructive set theory — directly relevant to §5.
- **`+model`:** needs univalent universes ⇒ added strength (the simplicial model
  uses inaccessibles as a *sufficient* model; the syntax's tight strength is more
  modest but still above predicative MLTT). So `+model` is "universes," not free.

## 5. Translating set theory into type theory — CZF clean, IZF walled

The user's question: *how hard to translate IZF theorems into MLTT?* This is a
transport `S` (artifact #4), and the answer is dominated by a **proof-theoretic
strength wall**, not formalization tedium.

**Canonical machinery — sets as well-founded trees (Aczel).** A type of iterative
sets as a W-type:

```
   V := W (A : U). (A → V)        a set = an index type A + an A-family of sets
```

with `=ᵥ` / `∈ᵥ` defined by mutual recursion (bisimulation; membership =
subtree-up-to-`=ᵥ`), propositionally truncated for extensionality. Each
set-theory axiom is then a *theorem about V*; an IZF/CZF *proof* translates
mechanically once `V` and the per-axiom lemmas exist (intuitionistic logic's
rules map one-to-one onto MLTT's — pillar-1, fold the derivation against the
lemmas). **The entire cost is building `V` and validating the axioms; individual
theorem translation is then free.**

The split:

| | Strength | Into MLTT |
|---|---|---|
| **CZF** (predicative) | ≈ ML-TT w/ W-types + 1 universe (Bachmann–Howard) | **clean & charted** — the `V` model; fiddly lemmas are Subset-Collection / "fullness" (needs type-theoretic choice on the index setoids, which holds for trees) |
| **IZF** (impredicative) | **equiconsistent with full ZF** (Friedman) | **no total interpretation into plain MLTT** — IZF ⋙ MLTT |

**Why IZF is walled.** IZF has full (impredicative) Separation + Power Set, and
ZF-strength Collection. Two breakages:

1. *Impredicative powerset / full Separation* need a genuine **universe of
   propositions `Ω`** that is impredicative. Predicative MLTT cannot form `𝒫(x)`
   in the same universe. An impredicative `Ω` (Coq's `Prop`, or propositional
   resizing in HoTT) fixes this — but alone buys only ~higher-order-arithmetic
   strength, still far below ZF.
2. *Collection/Replacement at ZF strength* needs the **universe structure itself**
   tall enough — the type-theoretic analogue of an inaccessible (Mahlo /
   super-universe). This is exactly the [`metatheory.md`](../logics/metatheory.md) §5.5
   "**ZF needs a universe (TG)**" phenomenon, in type-theoretic clothing.

So a *total sound* IZF→MLTT interpretation is **impossible on strength grounds**.
What is possible:

- Translate **CZF**, not IZF, for a clean total result (recommended if the goal
  is "set theory in type theory" without strength games).
- Translate **IZF into MLTT *extended* with (i) an impredicative `Ω` and (ii) a
  sufficiently tall universe**, declared as an explicit added axiom — then the
  pipeline is identical; you have paid for the strength honestly. Without (ii)
  you get a *bounded fragment* of IZF (no unrestricted Collection/Power).

**One-line version:** *CZF → MLTT is a formalization exercise; IZF → MLTT is
impossible until MLTT is made as strong as ZF, after which it is the same
exercise on top of an admitted large-universe axiom.* The deliverable in our
system is the same shape as PA ⟹ SOA ⟹ ZF: a `V`-construction + per-axiom
validation lemmas, with proof-transport as the cheap mechanical part.

## 6. NuPRL / Computational Type Theory — the distinctive one

NuPRL is a dependent type theory like the others *in shape* but radically
different *in foundation*, so it gets its own treatment. Difficulty: **high but
well-charted** — the Rahli et al. Coq formalization of NuPRL's metatheory is the
template to crib.

What makes it different (and how each piece maps in):

- **Untyped computation system underneath.** Terms are untyped; there is a fixed
  evaluation (lazy reduction to canonical form) on *closed* terms. → This is an
  **executor** in the bottom layer (umbrella §3 "untyped reduction"): a native
  reducer / WASM evaluator for the computation system. Direct-computation rules
  discharge to it.
- **Types as PERs.** A type is a *partial equivalence relation* over closed
  terms; `a ∈ A` and `a =ₐ b` are defined by the PER. → The semantic bridge is a
  **PER model built in HOL** (Allen's semantics; what Rahli mechanized in Coq):
  `D_NuPRL`'s rules are validated against the HOL PER model. This is a genuine
  *model construction*, not just replay — and its cumulative universe hierarchy
  pushes `+model` into the "needs universes" strength bracket.
- **Extensional equality / equality reflection.** `Γ ⊢ a = b ∈ A` reflects into
  the judgment, making typechecking **undecidable**. → There is *no* cheap
  syntactic checker; you **replay proof trees** (sequent derivations) into
  `Derivable_NuPRL`. That is fine — the waist only ever certifies *existence* of
  a derivation, and the proof tree is the witness.

So NuPRL slots into the same four-artifact frame, but its accelerator is split
into "an evaluator for the computation system" + "a HOL PER model," and its
faithfulness `≅` is the Allen/Rahli adequacy result. It is the right *last* member
of the type-theory family: most infrastructure (binding, judgment forms) is
shared, but the PER semantics + untyped evaluator are net-new.

## 7. Reuse map

What is written once and shared across the family, vs. per-system:

| Component | Shared (write once) | Per-system |
|---|---|---|
| Judgment forms (§1) | ✓ | — |
| Binding `≅` / CwF interface (§2) | ✓ (pillar-2, whole family) | the concrete model |
| Conversion / executor | the *mechanism* | each system's reduction rules |
| Type formers | the schema-replay engine | the actual former axioms (bulk) |
| `+model` strength | the universe ladder | which rung each system needs |

This is why the recommended order (umbrella §5) builds **LF first** (smallest:
Π only, §2 machinery, conversion) → **MLTT** (adds formers + universes) →
**HoTT** (adds univalence + HITs) → **NuPRL** (adds untyped eval + PER): each
step reuses the prior infrastructure and adds one new axis.

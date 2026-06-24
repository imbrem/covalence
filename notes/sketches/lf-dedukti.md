# LF, λΠ, and Dedukti — the encoding framework and a second universal substrate

> **STATUS: DESIGN SKETCH.** The Edinburgh Logical Framework (λΠ), Twelf-style
> judgments-as-types encodings, and **Dedukti** (λΠ-modulo-rewriting) — the one
> external system that is *itself* a universal logic substrate, a direct cousin
> of our Metamath thin waist. Part of the
> [`logic-frontends.md`](../logic-frontends.md) umbrella. Shares the dependent-TT
> binding machinery of [`sketches/type-theories.md`](./sketches/type-theories.md)
> §2.

---

## 1. Why LF is sequenced before MLTT

LF is the **smallest dependent type theory**: the λΠ-calculus, with dependent
function types `Πx:A. B` and nothing else — no universes, no large eliminations,
no Σ/Id/inductive families. That makes it the ideal place to *first* build the
type-theory infrastructure:

- the four judgment forms and the binding discipline
  ([`sketches/type-theories.md`](./sketches/type-theories.md) §2) — written here,
  reused by MLTT / HoTT / NuPRL / CIC;
- conversion (βη) as the only computation — the simplest executor on the
  conversion axis;
- and it immediately unlocks the **Dedukti/Logipedia** ecosystem (§4), a second
  large corpus of machine-checked proofs to consume.

So `D_LF` is high-leverage scaffolding, not a niche target. Difficulty:
**moderate** for Derivable; **moderate** for `+model` (λΠ has an in-HOL model — it
is weak).

## 2. LF's actual job: judgments-as-types (it encodes *other* logics)

LF is not used to *do* mathematics directly; its purpose is to be a
**meta-framework for encoding object logics**. The recipe (Harper–Honsell–Plotkin):

- object **syntax** → LF types and term constants;
- object **binding** → LF's own λ (higher-order abstract syntax — HOAS);
- object **judgments** → LF type families;
- object **rules** → LF constants whose types are the rule's premises → conclusion.

A derivation in the object logic ≅ a well-typed LF term — the **adequacy
theorem**. This means: to bring in "logic X via its LF encoding," you have a
choice that is itself illuminating for Covalence:

- **(i) Replay the LF encoding directly** — `Derivable_LF(⌜well-typed term⌝)` over
  `D_LF` with X's signature loaded. The object-level theorem of X is *witnessed*
  by an LF term; we certify that term typechecks.
- **(ii) Relate the LF encoding to our native X** — the LF **adequacy** theorem
  ("LF-encoding-of-X ≅ object X") is *exactly* pillar-2 representation
  equivalence: HOAS ↔ de Bruijn ↔ Metamath-metavariable. So adequacy is the same
  artifact we already build for the type-theory family, instantiated at "HOAS vs.
  our representation."

The HOAS point is worth stating sharply: **LF's binding-via-λ is one more
representation in the pillar-2 `≅` web.** Bringing LF in extends that web with the
HOAS node; nothing conceptually new beyond the type-theory binding work.

## 3. `D_LF` — the database

Artifacts (umbrella §2):

**Definition.** `D_LF` = the λΠ typing judgment as a Metamath database: kinds
(`Type`, `Πx:A. K`), families, objects, the Π-formation/intro/elim rules, and βη
**conversion** as the equality judgment. Because λΠ is "MLTT with only Π," this is
a *strict sub-case* of the MLTT plan
([`sketches/type-theories.md`](./sketches/type-theories.md) §3) — drop universes,
Σ, Id, ℕ, the HIT/equality-congruence bulk. The CwF/explicit-substitution
presentation (§2 there) applies and keeps it binder-free.

**Accelerator = a λΠ typechecker.** Bidirectional type checking with βη
conversion — a small, standard algorithm (Twelf's core). Run as an untrusted
frontend that constructs `Derivable_LF`.

**Faithfulness.** `Metamath-LF ≅ HOL-LF`: λΠ has a straightforward HOL model
(it is weak), so the semantic bridge is available; adequacy of object encodings
rides on top per-encoding.

**Transport `S`.** Per object logic encoded in LF — "LF-encoding-of-X ⟹ native X"
is the adequacy `S`. And the headline one: **LF ⟷ Metamath** (§5).

## 4. Dedukti — λΠ modulo rewriting, and the import corpus

**Dedukti** = λΠ extended with a confluent user-supplied **rewrite system** on
types/terms (λΠ/≡_R): conversion is βη *plus* the rewrite rules, so far more
definitional equalities hold. Its purpose is to be a **universal proof checker
and interchange format** — Coq, HOL, Isabelle, Matita, PVS, FoCaLiZe and others
export proofs into Dedukti (the **Logipedia** project assembles them into one
library). Dedukti is, in other words, *a second "thin waist for proofs"* already
in the world.

Two things to do with it:

- **Consume it (artifact #2, replay).** Ingest `.dk` / Logipedia proofs the way
  set.mm is ingested: parse, typecheck modulo the rewrite system, and construct
  `Derivable_Dedukti ⌜φ⌝`. The new work vs. the set.mm RPN checker is the
  **rewriting / conversion-modulo-`R`** engine (confluence is assumed of the
  supplied `R`; we check, not prove, well-typedness). This is moderate–high but
  bounded, and the payoff is *the entire multi-prover Logipedia corpus* through
  one frontend. The "construct, don't trust" principle holds: we re-derive, never
  trust Dedukti's checker.
- **Relate the encodings (artifact #4).** Each Dedukti theory comes with a
  declared encoding of its source logic (e.g. "HOL in λΠ/≡"); the transport `S`
  from `Derivable_Dedukti`-under-that-encoding to our native HOL/etc. is the
  semantic payoff, gated per encoding on the usual strength axis.

## 5. The deep point — Metamath ⟷ LF, waist to waist

This is the most ambitious and most interesting artifact in the whole frontend
program. **Dedukti/LF and our Metamath waist are both universal logic
substrates, with opposite design choices:**

| | Metamath waist (ours) | LF / Dedukti |
|---|---|---|
| metalogic | first-order, substitution + DV only | dependently typed (λΠ) |
| binding | metavariables + DV side-conditions | native (HOAS via λ) |
| proofs | proof-**irrelevant** (existence only) | proof-**relevant** (proofs are λ-terms) |
| computation | none (pure deduction) | βη (+ rewriting, in Dedukti) |
| checker | tiny RPN verifier | bidirectional λΠ(-mod-`R`) typechecker |

Because each is "just a logic," each can be *defined inside the other*:

- **LF as a Metamath database** — `D_LF` (§3) already *is* λΠ written in our
  waist. So Covalence can state and reason about LF/Dedukti typing *as object
  logic*.
- **Metamath as an LF/Dedukti signature** — Metamath's metavariable-substitution
  metalogic is itself encodable in λΠ (it is a very small logic).

The **waist-to-waist `≅`** relates them: a proof-relevant λΠ derivation maps to
the existence of a Metamath derivation and back (the proof-irrelevant direction
is a forgetful collapse; the other direction reconstructs a witness). Establishing
this positions Covalence to **consume the entire Dedukti/Logipedia interchange
ecosystem through the substrate it already has** — every system that exports to
Dedukti reaches Covalence's waist for free. It is the sharpest possible statement
of "Metamath is the substrate the systems relate *through*, not an interchange
format": we relate to the *other* universal substrate by a single metatheorem,
and inherit its whole import surface.

## 6. Difficulty summary

- **`D_LF` (Derivable): moderate.** A restricted MLTT (Π + βη only); reuses the
  type-theory binding/conversion machinery, which is *why* it is built first.
- **LF `+model`: moderate.** In-HOL (weak); per-encoding adequacy on top.
- **Dedukti import: moderate–high.** The conversion-modulo-rewriting engine is the
  new cost; payoff is the Logipedia multi-prover corpus.
- **Metamath ⟷ LF `≅`: research-flavored, high-value.** Optional, but the strategic
  prize — it federates the two universal substrates.

# Peano Arithmetic — the build plan (rung 2 of prop → PA → SOA)

> **AGENT BRIEF.** A concrete, handoff-ready plan to build Peano Arithmetic as a
> reified object theory inside HOL, scaling the proved `init/prop.rs` recipe.
> This is **rung 2** of the metatheory ladder (`theories-models-and-logics.md
> §5.4`): propositional logic (done) → **PA + a reusable first-order-logic
> framework** → second-order arithmetic. The big payoff is the FOL framework,
> which Robinson Q / Presburger / Tarski RCF / ZFC all reuse.

---

## 0. Non-negotiables (read first)

- **TEST-GATE.** `cargo test -p covalence-hol --lib` (~120s on a green base) must
  pass before every commit. NEVER gate on `cargo build` alone — re-entrant
  `LazyLock` / `cov_theory!` cycles only manifest at *runtime*, and that
  anti-pattern caused multiple broken merges. If the suite *hangs*, that is a
  re-entrant `LazyLock` **you** introduced — fix it, don't work around it.
  (See `crates/covalence-core/SKELETONS.md` + the auto-memory deadlock note.)
- **Genuine theorems only.** Every theorem hypothesis- and oracle-free; no
  postulates beyond clearly-definitional ones. Soundness must be *proved*, not
  asserted.
- **Commit incrementally**; pull `proof-thoughts` first and periodically.

## 1. The recipe (the same one `prop.rs` proved)

A reified object theory `X` is five pieces, each scaling what `init/prop.rs` did:
1. **Syntax** reified as data (`prop`: `PropForm`; `PA`: terms + formulas).
2. **`Derivable_X`** — an impredicative derivability predicate (`prop`:
   `Derivable_Prop A := ∀d. Closed d ⟹ d A`).
3. **Denotation** `⟦·⟧` into HOL (`prop`: `⟦A⟧ v : bool`).
4. **Soundness** `⊢ Derivable_X ⌜A⌝ ⟹ ⟦A⟧`, by **rule induction** (the
   impredicative `inst d := ⟦·⟧`; `prop_induction` packages it).
5. **Transport** `X(A) ⟹ HOL(A)` — for PA this *is* the soundness denotation
   (PA's `nat` ↦ HOL `nat`).

What PA adds over prop: **a term layer, quantifiers (binders), and substitution.**

## 2. The two genuinely-new pieces (where the work is)

### 2.1 First-order syntax with binders — reify LOCALLY-NAMELESS

PA has **terms** (over the signature `0`, `S`, `+`, `·`) and **formulas** (atomic
`t = s`, connectives `∧∨¬⟹`, and **quantifiers `∀x. φ`, `∃x. φ`**). The new thing
vs prop is binders.

**Recommendation: reify the syntax LOCALLY-NAMELESS (de Bruijn indices for bound
variables), mirroring the kernel's own `Term` representation.** This makes
substitution *shifting* and eliminates capture-avoidance entirely — the single
biggest simplification. The kernel's `subst.rs` (`open`/`close`/`shift_by`/
`subst_free`) is the exact pattern to mirror, now *on the reified datatype*.

How to reify the datatype — pick by tractability, justify in your report:
- **(a) A dedicated `Term`/`Formula` inductive type** via the now-working
  inductive engine (`init/inductive/` handles ≥2 recursive args). Gives a real
  recursor + structural induction for defining substitution/denotation.
- **(b) The `sexp` carrier** (`init/sexp.rs`, tree-based, the recommended
  internal-language substrate) — reify FOL terms/formulas as `sexp`. More
  uniform with future internal languages, but you build the FOL-specific views.
- **(c) Church/impredicative encoding** (what `prop.rs` did) — works, but
  substitution over a Church encoding is awkward; prefer (a) or (b) here since PA
  *needs* substitution.

Lean **(a) a dedicated locally-nameless `Formula` datatype** (cleanest recursor
for substitution + denotation), with `(b)` as the alternative if you want the
`sexp` unification. (The prop agent's note: wire reified `var` to carry an atom
payload — locally-nameless makes the *bound* vars indices and only *free* vars
carry atoms.)

### 2.2 Substitution + the induction schema

- **Substitution** `⌜φ[t/x]⌝` on the reified syntax — the locally-nameless
  `open`/`subst` on `Formula`. Prove its basic equations + the substitution lemma
  (`⟦φ[t/x]⟧ = ⟦φ⟧` under the updated environment) — the lemma soundness needs.
- **The induction schema** is one more **closure clause** of `Derivable_PA`
  (the prop agent's insight): for a reified open `P(x)`,
  `d ⌜P(0)⌝ ⟹ (∀n. d ⌜P(n)⌝ ⟹ d ⌜P(Sn)⌝) ⟹ d ⌜∀n. P(n)⌝`.
  So `pa_induction(pred, axiom_cases, rule_cases)` is the *same* single
  `inst d := pred` + discharge `Closed_PA pred` as `prop_induction` — reuse that
  packaging directly.

## 3. Phasing (the recommended order)

**Phase A — the reusable FOL framework** (the real investment; everything below
reuses it):
- A1. The reified locally-nameless **FOL syntax** generic over a *signature*
  (function + relation symbols with arities): `Term`, `Formula` (atomic,
  `∧∨¬⟹`, `∀`/`∃`).
- A2. **Substitution** (`open`/`close`/`subst`) + its equations.
- A3. A **generic `Derivable` engine** parameterized by (signature, axioms,
  rules) — the FOL natural-deduction/Hilbert rules as closure clauses, with the
  impredicative `Derivable := ∀d. Closed d ⟹ d A` shape and a packaged
  `fol_induction`/rule-induction principle (generalize `prop_induction`).
- A4. The **denotation framework**: a signature *interpretation* (carrier +
  symbol meanings) → `⟦Term⟧ : env → carrier`, `⟦Formula⟧ : env → bool`, + the
  substitution lemma.

**Phase B — PA specifically** (instantiate the framework):
- B1. The arithmetic signature (`0`,`S`,`+`,`·`) + the PA axioms + the **induction
  schema** as a `Derivable_PA` closure clause.
- B2. The standard interpretation (carrier = HOL `nat`, `S`↦`succ`, `+`↦`nat.add`,
  …) and `⟦·⟧` into HOL.
- B3. **Soundness** `⊢ Derivable_PA ⌜A⌝ ⟹ ⟦A⟧` via `pa_induction` (each axiom +
  rule + the induction schema discharged — the schema case uses HOL `nat`
  induction). This is also the **`PA(A) ⟹ HOL(A)` transport**.

**Phase C — `pa.cov` + a worked theorem** (the demonstration):
- C1. Expose PA in `.cov` (`pa_env`, `pa.cov`); prove a small PA theorem (e.g.
  `∀x. x + 0 = x` or commutativity of `+`) *by PA induction-on-derivations*, and
  show it transports to a native HOL `nat` fact.
- C2. Push as much into the `.cov` script language as possible (a stress test,
  like `prop.cov`); record surface gaps.

**Minimal viable first cut if scope is tight:** A1+A2 (syntax + substitution) are
the critical path — start there. Then a *small* `Derivable_PA` (a few axioms, no
schema yet) + soundness for the schema-free fragment, before the full induction
schema. Don't try to land all of A–C at once; land A green, then B, then C.

## 4. Prerequisites / surface gaps this will hit

The `prop.cov` stress test already surfaced the `.cov`-language gaps PA needs
(recorded in `init/SKELETONS.md`); closing them is part of Phase C (or a
precursor):
1. **`(pa-induct …)` / impredicative rule-induction tactic** — the `inst d := P`
   + `Closed P` discharge has no `.cov` surface (it's Rust-only today). The
   generalization of the missing `(prop-induct …)` tactic.
2. **β/η-aware `#concl` matching** — statements over a *bound* variable
   (pervasive in FOL: every `∀x. …`) can't be re-stated through the current
   first-order, no-β `#concl` matcher. Needed to express PA metatheorems in
   `.cov` at all.
3. Reified `var` carrying atoms / the term layer — handled by the locally-nameless
   choice (§2.1).

If these block the `.cov` demonstration (Phase C), do the Rust development
(Phases A–B) fully first — it stands alone — and record the `.cov` gaps as the
next elaborator features (they're wanted regardless).

## 5. What to reuse (don't rebuild)

- `init/prop.rs` — the *exact* template: `Derivable` shape, `Closed`, the
  impredicative `prop_induction`, the denotation + soundness structure.
- `init/sexp.rs` / `init/sexpr.rs` — the reified-syntax carriers (and the
  recommendation to prefer `sexp`).
- `init/inductive/` — the ≥2-rec-arg inductive engine, if reifying `Formula` as a
  datatype (option (a)).
- `covalence-core/src/subst.rs` — the locally-nameless `open`/`close`/`shift`/
  `subst` algorithms to mirror on the reified syntax.
- `init/nat.rs` — the HOL `nat` theory the standard interpretation lands in
  (induction, `add`/`mul`, order) for the soundness schema case.

## 6. Deliverable checklist

- [ ] Reified locally-nameless FOL `Term`/`Formula` (generic signature) + tests.
- [ ] Substitution + equations + the substitution lemma.
- [ ] Generic `Derivable` engine + packaged rule-induction principle.
- [ ] Denotation framework + signature interpretation.
- [ ] PA signature + axioms + the induction-schema closure clause.
- [ ] The standard `nat` interpretation + `⟦·⟧`.
- [ ] **Soundness `⊢ Derivable_PA ⌜A⌝ ⟹ ⟦A⟧`** (= the `PA(A) ⟹ HOL(A)` transport).
- [ ] `pa.cov` + one worked PA theorem proved by induction-on-derivations,
      transported to HOL.
- [ ] Surface-gap notes for the `.cov` features PA wants next.
- [ ] **Full `cargo test -p covalence-hol --lib` green at every commit.**

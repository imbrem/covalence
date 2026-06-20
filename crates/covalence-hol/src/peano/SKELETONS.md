# Skeletons — `covalence-hol/src/peano`

Intentional placeholders in the Peano-arithmetic deep embedding. See
`CLAUDE.md` § Skeletons and the [crate index](../SKELETONS.md). Build plan:
[`docs/peano-arithmetic-plan.md`](../../../../docs/peano-arithmetic-plan.md).

## Status (what is done)

The deep PA-in-HOL embedding is built **Phases A–B** of the plan:

- `fol.rs` — reified locally-nameless FOL syntax (Church carrier + `Fol`
  AST) and substitution (`open`/`close`/`shift`/`subst_fvar`), with the
  substitution laws as tests. **Done, proven.**
- `deep.rs` — the standard interpretation `⟦·⟧` into HOL `nat`/`bool`
  (terms → `nat`, formulas → `bool`, quantifiers → real HOL `∀`/`∃`, free
  atoms → named HOL free vars). **Done, proven.**
- `pa.rs` — the PA axioms (PA1–PA6) each paired with its proven `nat`
  denotation; the inference rules (`specialize`, `mp`); the **induction
  schema** discharged to `Thm::nat_induct`; and the worked theorem
  `∀x. x + 0 = x` proved **by PA induction-on-derivations** and transported
  to HOL `nat` (matching `init::nat::add_zero`). The soundness/transport
  `PA(A) ⟹ HOL(A)` is realised **constructively, per-derivation**: a
  `Derivation` is a reified `Fol` paired with a genuine `⊢ ⟦A⟧`, built in
  lock-step (LCF discipline one level up). **Done, proven, oracle-free.**

## Deferred

### The ∀-closed impredicative soundness theorem (`⊢ ∀A. Derivable_PA A ⟹ ⟦A⟧`)

`pa.rs` proves soundness **constructively per derivation** (every
`Derivation.thm` is `⊢ ⟦formula⟧`). The single ∀-quantified HOL statement
`⊢ Derivable_PA ⌜A⌝ ⟹ ⟦A⟧` — the impredicative form `init/prop.rs` proves for
propositional logic via `inst d := ⟦·⟧` — is **not** yet stated as one HOL
theorem here.

Why deferred: that form needs the denotation to be an **HOL fold of the
Church carrier** so the predicate variable `d` can be `inst`'d with it.
`prop.rs` denotes into the single semantic type `bool`; PA is **two-sorted**
(terms → `nat`, formulas → `bool`), so the fold needs either (a) a two-type-
variable carrier `Φ⟨'t,'r⟩` with `eq : 't→'t→'r` and HOAS quantifier handlers
`all : ('t→'r)→'r`, denoted at `'t:=nat, 'r:=bool`; or (b) a uniform
`'r := (nat→nat)→nat` coding (0/1 truth) à la `init/regex.rs`. The de Bruijn
`Fol` AST + the proven substitution already provide everything the *syntax*
side needs; what remains is re-stating denotation as that fold and running the
prop-style rule induction (`fol_induction`) over the PA closure clauses
(PA1–PA6, FOL natural-deduction rules, the induction schema). The constructive
soundness here makes that a re-packaging, not new mathematics.

### `.cov` surface (Phase C)

PA is **not** exposed through the `.cov` script language. The two `.cov`
elaborator features the plan §4 calls for are still missing (they block
expressing PA metatheorems in `.cov`, and `prop.cov` already recorded them):

- a `(pa-induct …)` / impredicative rule-induction tactic — the `inst d := P`
  + `Closed P` discharge has no `.cov` surface;
- **β/η-aware `#concl` matching** — statements over a *bound* variable
  (pervasive in FOL: every `∀x. …`) cannot be re-stated through the current
  first-order, no-β `#concl` matcher.

Phases A–B stand alone in Rust (above), so this is recorded as the next
elaborator work rather than blocking the development.

# Full ACL2: soundness + import into base HOL — the plan

**Goal.** Prove soundness of (a staged, eventually full) ACL2 logic inside Covalence and
transport imported book theorems into **base HOL** as genuine kernel theorems. Priority
directive (2026-07-16): this plan outranks the other Lisp-toolkit north stars
(determinism/ε-eval/type-system) unless something is trivially adjacent.

**Shape.** The reified-theory ladder (as prop→PA→SOA): deep-embed ACL2 terms, reify
`Derivable_ACL2` as a clause set on `metalogic::binary::RuleSet2`, interpret into a HOL
*model* of the ACL2 universe, prove each rule truth-preserving, conclude soundness by
`rule_induction2`. Book import = untrusted Rust front end producing `Derivable_ACL2`
certificates; the soundness metatheorem transports each into `⊢ ⟦φ⟧`.

**Why this is tractable.** ACL2's logic is **quantifier-free** first-order — theorems
mean `∀σ. ⟦φ⟧σ ≠ nil`, with the ∀ at the meta level. This sidesteps the known
β-capture wall that blocked quantifier derivation constructors in the SOA ladder.
Precedent: the HOL4 "ACL2 in HOL" embedding (Gordon–Hunt–Kaufmann–Reynolds) proved
this shape works; we differ by making the derivability relation itself a reified,
rule-inducted object. In-repo prior art to reuse: the binary engine + rule induction,
`metalogic/discharge.rs` helpers, `init/` recursion theorem + subtype machinery +
int-quotient recipe, the λ_iter deep-embedding patterns (`code.rs`, `lambda_ty.rs`),
the existing sexpr HOL theory the Lisp dialects target.

**Discipline.** Each stage has a hard gate (kernel-checked tests), an honest fragment
boundary (import tally: *transported to HOL* / *in-dialect only* / *rejected*), a
SKELETONS entry for anything left open, and a commit. No new admitted kernel rules;
`crates/kernel/**` untouched; aggressive but revertible (commit per stage).

## Stages

- **S0 — Object universe (model carrier).** HOL datatype
  `A = Int ⊕ Sym ⊕ Cons A A` (integers first; rationals at S8; chars/strings slotted
  when books need them) via existing subtype + recursion machinery. Deliver: induction,
  case analysis, constructor injectivity/distinctness. Gate: cons-injectivity +
  an induction instance as kernel theorems.
- **S1 — Primitives in the model.** Total `car/cdr/cons/consp/equal/if/atom` +
  integer arithmetic ops; ACL2's *completion axioms* (e.g. `car` of an atom is `nil`)
  **proved** as model theorems, not postulated. Gate: every ground ACL2 axiom instance
  we state is a kernel theorem.
- **S2 — Deep-embedded terms + semantics.** ACL2 (pseudo-)terms as data (vars,
  `quote`, application, `lambda`), substitution, valuations, `⟦t⟧σ : A`;
  theorem-ness `:= ∀σ. ⟦φ⟧σ ≠ nil`. Gate: evaluation of sample terms computes via
  kernel reduction.
- **S3 — Ground/equational `Derivable_ACL2` + SOUNDNESS.** Clause set: propositional
  calculus (if-form), equality + congruence, instantiation (QF substitution),
  primitive axioms. Prove `Derivable_ACL2(φ) ⟹ ⊢ ⟦φ⟧` by rule induction. Gate:
  `(defthm four (equal (+ 2 2) 4))` imports as a **base-HOL theorem via transport**
  (not by direct kernel arithmetic).
- **S4 — Definitional principle, conservative tier.** Non-recursive `defun`
  (unfolding) + structural recursion on cons-size (nat measure), justified by the
  model recursion theorem; defining equations enter `Derivable_ACL2` only with an
  admissibility certificate. Gate: `app`/`len`/`rev` admitted; ground theorems about
  them transport.
- **S5 — Ordinals below ε₀.** Ordinal notations (CNF) as a HOL datatype, `o<`,
  **well-foundedness proved** (the classic nested structural induction). Gate: wf
  theorem + ACL2's ordinal axioms as model theorems. (Parallel-safe with S4.)
- **S6 — Induction rule.** Reify ACL2's induction schema; soundness via well-founded
  induction in the model. Start with cons-structural measures (unlocks most list
  books), then ordinal measures. Gate: associativity-of-`app` defthm imports into
  base HOL.
- **S7 — Full definitional principle.** Arbitrary measures into ordinals, mutual
  recursion, via a well-founded recursion theorem over `o<` in the model. Gate: a
  non-structural defun (e.g. merge-sort by length, or ackermann) admitted + used.
- **S8 — Rationals (then complex rationals).** `rat` as quotient over `int × posnat`
  (the int-quotient-lifting recipe); upgrade the carrier's numeric fragment; re-prove
  S1 arithmetic axioms. (Parallelizable with S5–S7; required for "full".)
- **S9 — `defchoose` / `defun-sk`.** ε in the model; conservativity of the choice
  axioms. After S6.
- **S10 — Encapsulation + functional instantiation.** Conservativity via model
  witnesses; the functional-instantiation rule reified and proved sound. Hardest
  conceptual piece after ε₀.
- **S11 — Book front end.** `defmacro` (logic-invisible: macroexpansion is untrusted
  Rust translation), `include-book`/`local`/portcullis, certification-style tally
  report. Gate: a real community book (e.g. a small list/arithmetic book) imports
  end-to-end with theorems landing in base HOL and an honest tally.
- **S12 — Guards.** `verify-guards` etc. are logic-irrelevant: accept + record.

## Cross-cutting

- **Reusable APIs first** (standing directive): the reify/soundness/transport triple
  becomes a mid-level "theory ladder" API shared with prop/PA/SOA (and later K/SpecTec);
  the dialect trait gets `reify`/`transport` hooks; book import goes through the trait.
- **Performance seam:** deep-embedded evaluation of big terms should ride
  computation-backed certificates (`TermExt::reduce`), never unfolded object numerals.
- **Risks accepted:** ε₀ wf proof size (S5), functional instantiation (S10), carrier
  churn at S8. Mitigation = stage isolation: S0–S4+S6-structural already yield a
  demo-grade importer with real HOL transport before any hard stage lands.

## Order of attack

S0 → S1 → S2 → S3 (first transported theorem) → S4 + S6-structural (list books) →
S5 → S7 → S8 ∥ S9 → S10 → S11 (real book) → S12. Ship the tally UI into the /lisp
demo as soon as S3 lands.

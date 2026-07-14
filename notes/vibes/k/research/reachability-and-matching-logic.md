# Reachability logic and matching logic: what a Covalence embedding actually needs

> **STATUS: RESEARCH SURVEY (AI-drafted, web-sourced).** Researched 2026-07-13
> via live fetches of primary sources; claims individually marked with
> certainty. Cross-checked by an independent verification pass; corrections
> applied.

Scope: the two layers of "matching logic", the AML proof system, one-path and
all-path reachability logic (semantics, proof systems, the *inductive*
soundness of Circularity), how K rules/claims map onto RL, total-correctness
moves, and prior mechanizations worth cribbing.

## Two layers of "matching logic"

The name covers two very different things, and the distinction is
load-bearing for an embedding:

- **Topmost matching logic** — what the reachability-logic papers (LICS'13
  one-path, RTA'14/[LMCS'19 all-path](https://ar5iv.labs.arxiv.org/html/1810.10826))
  actually use. A pattern is just a **FOL formula** over a many-sorted
  signature Σ with a distinguished sort `Cfg`, extended with "basic patterns"
  (Cfg-sorted terms used as predicates); (γ,ρ)⊨π iff γ=ρ(π). A mechanical
  □-translation (replace each basic pattern π with □=π) reduces pattern
  validity to plain FOL validity in the configuration model T — verbatim,
  *"matching logic is a methodological fragment of the FOL theory of T"*
  **[high]**. Consequence: **an RL embedding does not require full AML** — any
  FOL-with-a-configuration-model substrate suffices for the pattern layer
  **[high]**.
- **Full AML / matching μ-logic** — the later foundational layer (Chen–Roşu
  [LICS 2019](https://fsl.cs.illinois.edu/publications/chen-rosu-2019-lics.pdf);
  the applicative core in the
  [July 2019 TR](https://fsl.cs.illinois.edu/publications/chen-rosu-2019-trb.html)).
  Patterns φ ::= x | X | σ | φφ | φ→φ | ∃x.φ | μX.φ, interpreted as **sets**
  of elements of a structure (A, _⋆_ : A×A→2^A, σ^A ⊆ A); application is
  pointwise-unioned (B⋆C = ⋃ b⋆c) **[high]**. Note on positivity: the
  classical LICS'19/TR convention puts "φ positive in X" in the μ syntax; the
  recent [Notes on AML](https://ar5iv.labs.arxiv.org/html/2506.10088)
  (arXiv:2506.10088) explicitly drops syntactic positivity and carries it as a
  side condition on the Pre-Fixpoint axiom instead (the researcher pass
  initially conflated the two conventions; verified against the PDF) **[high]**.

## The AML proof system (~13 rules)

The Hilbert system — exactly what the CAV'21 Metamath checker implements — is
**8 axiom schemas + 5 inference rules** **[high]**, in four groups:

- **Propositional/FOL**: (Tautology); (∃-Quantifier) φ[y/x]→∃x.φ; Modus
  Ponens; ∃-generalization (φ→ψ ⊢ ∃x.φ→ψ, x∉FV(ψ)).
- **Frame reasoning**: (Propagation⊥) φ·⊥→⊥, (Propagation∨)
  (φ∨ψ)·χ → φ·χ ∨ ψ·χ, (Propagation∃) (∃x.φ)·ψ → ∃x.(φ·ψ) if x∉FV(ψ) — each
  in both left/right application forms; Framing (φ→ψ ⊢ φ·χ→ψ·χ, both sides).
- **Fixpoint reasoning**: Set Variable Substitution (φ ⊢ φ[ψ/X]);
  (Pre-Fixpoint) φ[μX.φ/X]→μX.φ; Knaster–Tarski (φ[ψ/X]→ψ ⊢ μX.φ→ψ).
- **Technical**: (Existence) ∃x.x; (Singleton Variable)
  ¬(C₁[x∧φ] ∧ C₂[x∧¬φ]).

The many-sorted LICS'19 system H/H^μ is the same shape with sorted application
contexts C_σ **[high]**.

## Sorts, definedness, equality: theories, not primitives

Nothing beyond the 13 rules is built in **[high]**:

- A **sort** s is an ordinary symbol; its inhabitant set is the pattern
  ⟦s⟧ — sugar for applying a distinguished inhabitant symbol ⟦_⟧ to s
  (verified verbatim in [CAV21](https://trinhmt.github.io/home/Proof/CAV21.pdf)).
  "succ is a sorted function Nat→Nat" is an axiom quantifying over
  inhabitants; sorted quantification is ∀x:s.φ ≡ ∀x.(x∈⟦s⟧)→φ.
- **Definedness/equality/membership** are one theory over one symbol:
  ⌈φ⌉ := DEF·φ, ⌊φ⌋ := ¬⌈¬φ⌉, φ=ψ := ⌊φ↔ψ⌋, x∈φ := ⌈x∧φ⌉.

K/Kore's sort system compiles to exactly this. Kore itself is *"not the same
as the syntax of matching logic, but an axiomatic extension with equality,
sorts, and rewriting"* (CAV21, verbatim) — so a frontend consuming Kore sees
AML plus the definedness/sort/rewriting theories already reified as axioms
**[high]** (Kore format drifts with the K toolchain; description is 2021's).

## Transition systems in μ-logic: one symbol

K's transition relation is one extra symbol **•** ("one-path next": •φ matches
configurations with SOME successor matching φ) **[high]**. Then, verbatim from
LICS'19 §IX:

- eventually ⋄φ ≡ μX.φ∨•X; well-foundedness WF ≡ μX.◦X ("no infinite paths",
  ◦ = all-path next, dual of •); weak-eventually ⋄w φ ≡ νX.φ∨•X = ¬WF ∨ ⋄φ;
- reaching-star φ₁⇒\*φ₂ ≡ φ₁→⋄wφ₂ and reaching-plus φ₁⇒⁺φ₂ ≡ φ₁→•⋄wφ₂
  (progress: at least one step) **[high]**.

RL sequents translate wholesale (LICS'19 Def. 38): RL2MmL⟦A ⊢_C φ₁⇒φ₂⟧ =
(∀ Â) ∧ (∀◦ Č) → (φ₁ ⇒? φ₂), where the rule translation is
**□(φ₁⇒⁺φ₂)** with □φ ≡ νX.φ∧◦X — the *always* operator, **not** totality
⌊φ₁⇒⁺φ₂⌋ (the researcher pass initially misread the glyph; verified by
glyph-forensics against the LICS'19 PDF — if load-bearing, eyeball Def. 38 in
the typeset PDF once) — ? is \* if C=∅ else +, and circularities are guarded
by a leading all-path next ◦ so they only hold after one step **[high]**.
**Theorem 39** then makes the entire RL proof system a derived artifact:
S ⊢_RL φ₁⇒φ₂ iff the corresponding pattern is derivable from Γ_RL (the
FOL-oracle patterns of the configuration model) **[high]**.

## Reachability logic: semantics

RL rules φ⇒φ' between patterns generalize both semantics steps and Hoare
triples. S (a set of one-path rules l∧b ⇒∃ r — the operational semantics)
induces γ ⇒_S^T γ' (∃ rule and valuation ρ with (γ,ρ)⊨φ_l, (γ',ρ)⊨φ_r)
**[high]**.

- **One-path** ([LICS'13](https://fsl.cs.illinois.edu/publications/rosu-stefanescu-ciobaca-moore-2013-lics.pdf),
  Defs. 6–7, verbatim): S⊨φ⇒∃φ' iff for every ρ and every γ with (γ,ρ)⊨φ, *if
  γ terminates* then ∃γ' with γ⇒\*_S γ' and (γ',ρ)⊨φ' — partial correctness;
  divergence discharges the obligation **[high]**.
- **All-path** ([LMCS'19](https://ar5iv.labs.arxiv.org/html/1810.10826), §3,
  verbatim): S⊨φ⇒∀φ' iff on every **complete** path (a finite path that is not
  a strict prefix of another — i.e. ending stuck/final) from every γ⊨φ, some
  state on the path matches φ' — with the matching valuation ρ **shared**
  between LHS and RHS, which is how logical variables link pre/post states
  **[high]**. This is AF over complete paths, and φ' may match an intermediate
  configuration (strictly generalizing Hoare triples).

## The all-path proof system (8 rules, verbatim)

Sequents S,A ⊢_C φ⇒∀φ' with axioms A and circularities C (LMCS'19 Fig. 1)
**[high]**:

1. **Step**: from ⊨ φ → ⋁_{φl⇒∃φr ∈ S} ∃FreeVars(φl).φl and, for each rule
   φl⇒∃φr ∈ S, ⊨ ∃c.(φ[c/□] ∧ φl[c/□]) ∧ φr → φ' (both plain FOL validities
   in T), conclude S,A ⊢_C φ⇒∀φ'. One premise per semantics rule even with
   unbounded branching.
2. **Axiom**: φ⇒∀φ' ∈ A.
3. **Reflexivity**: S,A ⊢ φ⇒∀φ — **requires C = ∅**.
4. **Transitivity**: S,A ⊢_C φ₁⇒∀φ₂ and S,A∪C ⊢ φ₂⇒∀φ₃ give
   S,A ⊢_C φ₁⇒∀φ₃ — the second premise gets A∪C: circularities are *flushed*
   into the axioms after one step of progress.
5. **Consequence**: ⊨φ₁→φ₁', ⊢_C φ₁'⇒∀φ₂', ⊨φ₂'→φ₂ give ⊢_C φ₁⇒∀φ₂.
6. **Case Analysis**: φ₁⇒∀φ and φ₂⇒∀φ give φ₁∨φ₂⇒∀φ.
7. **Abstraction**: φ⇒∀φ' with X∩FreeVars(φ')=∅ gives ∃X.φ⇒∀φ'.
8. **Circularity**: S,A ⊢_{C∪{φ⇒∀φ'}} φ⇒∀φ' gives S,A ⊢_C φ⇒∀φ'.

Reflexivity's C=∅ restriction ensures anything derived under circularities
takes ≥1 step; Circularity's assumptions become usable only via Transitivity's
flushed second premise **[high]**. The one-path system (LICS'13 Fig. 2) is the
7-rule sibling: no Step rule — its Axiom applies conditional semantics rules
directly, with conditions discharged as A∪C ⊢_∅ φᵢ∧ψ ⇒ φ'ᵢ and a structureless
frame pattern ψ conjoined; derived rules include set circularity, the core of
the MatchC prover **[high]**.

## Circularity is inductive, not coinductive

**The single most important fact for a Covalence embedding** **[high]** (the
theorem text is verbatim; the embedding-suitability reading is our inference
**[medium]**): Circularity is coinductive *in flavor* but its soundness proof
is **step-indexed induction**, no coinduction anywhere. LMCS'19 §7:

- Define S ⊨ₙ^δ φ⇒∀φ': restrict to complete paths of length ≤ n; δ=+
  additionally requires the target be reached after ≥1 step. Then S⊨φ⇒∀φ' iff
  S⊨ₙ^\* for all n.
- **Lemma 2**: if S,A ⊢_C φ⇒∀φ' then for all n, S⊨ₙ^+ A and S⊨ₙ₋₁^+ C imply
  S⊨ₙ^{Δ_C} φ⇒∀φ' (Δ_C = + iff C≠∅). Proof: induction on the proof tree with
  the IH kept universally quantified over n, plus an inner induction on n in
  the Circularity case. Soundness follows with A=C=∅.
- The paper's intuition, verbatim: *"requiring progress (taking at least one
  step) before circularities can be used ensures that only diverging
  executions can correspond to endless invocation of a circularity."*
  Circularity generalizes the Hoare while-invariant rule (derived in the
  paper).

Likewise the relative-completeness proof (Thm 3 — complete relative to a FOL
oracle for T, assuming S finite, ℕ in Σ, and a Gödel-β encoding of paths)
pivots on **coreach(φ')** — "every complete path from c includes a
configuration satisfying φ'" — a **least fixpoint** over the transition
relation **[high]**. So both the soundness and completeness arguments live
entirely in inductive/least-fixpoint land: a fuel-indexed satisfaction
predicate over an inductively defined one-step relation is all that's needed —
which lands squarely on Covalence's existing impredicative `Derivable_R`
machinery (the SpecTec/metalogic engine), with no coinduction facility
required **[medium]** (design inference). The FSL soundness proofs are
mechanized in Coq, parametric in the operational semantics S **[high]**.

## K rules and claims → RL

From the [live K user manual](https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md)
(fetched 2026-07-13; wording can drift but the semantics is foundational)
**[high]**:

- `rule LHS => RHS requires REQ ensures ENS` denotes the transition from state
  `LHS #And REQ` to `RHS #And ENS` — i.e. the one-path rule
  (LHS∧REQ) ⇒∃ ∃?X.(RHS∧ENS). `?X` variables appear only in the RHS and are
  existentially quantified at its top; ordinary variables are universally
  quantified over the whole rule.
- `claim` sentences have the same shape but are *proved* by kprove against
  the semantics; the Haskell backend supports both `one-path` and `all-path`
  claim attributes (module-level defaults, `--default-claim-type`; all-path is
  the default), and `trusted` claims are added directly to the
  proven-circularities set. Set variables exist in K for partiality (`3/0`)
  and non-determinism (`3 #Or 5`).

## Total correctness

RL is partial-correctness by design (both semantics above). Standard moves
**[high]**:

- **Buruiană–Ciobâcă** (["Reducing Total Correctness to Partial Correctness…"](https://arxiv.org/abs/1902.08419),
  WPTE 2018 / EPTCS 289): a language-parametric transformation of the
  semantics given an expression decreasing in a well-founded order at each
  step (prototyped on RMT).
- **Matching μ-logic directly**: WF ≡ μX.◦X and strong-eventually ⋄ make
  total-correctness claims *statable* as μ-patterns (finite-trace LTL via
  axioms (Fin) WF and (Lin) •X→◦X), even though the K RL prover doesn't
  discharge them. Whether current K backends grew total-correctness support
  since is unverified.

## Prior embeddings to crib

1. **FSL Coq mechanizations** of one-path (LICS'13) and all-path (LMCS'19)
   soundness — parametric in the operational semantics, designed so RL
   derivations act as proof certificates **[high]**.
2. **Rusu–Nowak**, ["(Co)inductive Proof Systems for Compositional Proofs in Reachability Logic"](https://arxiv.org/abs/1909.01744)
   (FROM 2019 / EPTCS 303; [journal JLAMP 2020](https://www.sciencedirect.com/science/article/pii/S2352220820301048)):
   three sound-and-complete proof systems over plain transition systems (not
   K-specific), trading coinduction against induction/compositionality,
   mechanized in Coq (partially Isabelle). The cleanest template for RL over
   an inductively-defined transition relation + RTC in a prover **[high]**
   (Coq artifact location not re-verified).
3. **[harp-project/AML-Formalization](https://github.com/harp-project/AML-Formalization)**
   (Rocq, **LGPL-2.1** — copyleft: fine to study/interoperate, importing code
   carries LGPL obligations): locally-nameless AML with soundness, an
   interactive proof mode (ICTAC 2023), Metamath proof extraction, and
   `kore`/`koreimport` directories. Actively maintained — v1.1.3 released
   2026-02-27 **[high]** (active repo; state will move).
4. **[kframework/matching-logic-proof-checker](https://github.com/kframework/matching-logic-proof-checker)**
   (**NCSA**, permissive; archived read-only 2024-02-15): the CAV'21
   Metamath formalization of the 13-rule AML system + Kore-in-ML + concrete
   rewriting proof generation — the closest existing analogue of Covalence's
   Metamath-substrate plan **[high]**. (Details in the proof-generation doc.)
5. **["K Definitions as Matching Logic Theories, Formally"](https://link.springer.com/chapter/10.1007/978-3-032-22730-0_10)**
   (Chen, Cheval, Lucanu, Roşu, FoSSaCS 2026) formalizes the K→ML-theory
   correspondence itself; **Minuska** ([SEFM 2024](https://dl.acm.org/doi/10.1007/978-3-031-77382-2_12))
   is an independent Coq-verified K-style framework **[medium]** (both from
   listings/snippets, not fetched PDFs).

## What this means for Covalence

Suggested embedding shape (our synthesis, **[low]** — design inference, not a
published claim): (1) represent a K/Kore definition as a set of one-path rules
(lᵢ∧bᵢ ⇒∃ rᵢ) over a configuration type; (2) define the one-step relation
γ ⇒_S γ' inductively — one constructor per rule + valuation, exactly the
impredicative `Derivable_R` pattern already used for SpecTec; (3) define
all-path validity via the least-fixpoint coreach predicate (or step-indexed
⊨ₙ^δ) and one-path validity via RTC + a divergence disjunct; (4) prove the 8
all-path rules — Circularity via the Lemma 2 double-induction recipe — as
derived theorems *once*, parametric in S; (5) optionally, later, embed AML
itself (13 rules) to consume Kore theories and CAV'21-style Metamath
certificates natively on the Metamath substrate.

Key comforts: the RL pattern layer is just FOL-over-a-model (no AML needed to
start); Circularity needs no coinduction; Step's premises are FOL side
conditions dischargeable by existing HOL machinery; and Consequence's ⊨
premises are exactly where SMT/oracle obligations enter (relative completeness
assumes precisely that oracle) — the same hole the proof-generation papers
left open, so plan its discharge story deliberately.

## Sources consulted

- https://ar5iv.labs.arxiv.org/html/1810.10826 (All-Path Reachability Logic, LMCS'19) ; https://arxiv.org/abs/1810.10826 ; https://lmcs.episciences.org/5408
- https://fsl.cs.illinois.edu/publications/rosu-stefanescu-ciobaca-moore-2013-lics.pdf ; https://dl.acm.org/doi/10.1109/LICS.2013.42
- https://fsl.cs.illinois.edu/publications/chen-rosu-2019-lics.pdf ; https://fsl.cs.illinois.edu/publications/chen-rosu-2019-lics.html
- https://ar5iv.labs.arxiv.org/html/2506.10088 ; https://arxiv.org/pdf/2506.10088
- https://fsl.cs.illinois.edu/publications/chen-rosu-2019-trb.html
- https://trinhmt.github.io/home/Proof/CAV21.pdf ; https://link.springer.com/chapter/10.1007/978-3-030-81688-9_23
- https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md
- https://github.com/kframework/matching-logic-proof-checker
- https://github.com/harp-project/AML-Formalization ; https://arxiv.org/abs/2201.05716 ; https://dl.acm.org/doi/10.1007/978-3-031-47963-2_10
- https://arxiv.org/abs/1909.01744 ; https://www.sciencedirect.com/science/article/pii/S2352220820301048
- https://arxiv.org/abs/1902.08419 ; https://link.springer.com/chapter/10.1007/978-3-319-94205-6_20
- https://link.springer.com/chapter/10.1007/978-3-032-22730-0_10 ; https://dl.acm.org/doi/10.1007/978-3-031-77382-2_12

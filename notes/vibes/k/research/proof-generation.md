+++
id = "N000S"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T19:57:49+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# K proof generation: the Metamath pipeline, its fate, and the opening

> **STATUS: RESEARCH SURVEY (AI-drafted, web-sourced).** Researched 2026-07-13
> via live fetches of primary sources; claims individually marked with
> certainty. Cross-checked by an independent verification pass; corrections
> applied.

Scope: K's trust story for proof generation — the CAV 2021 execution-certifying
pipeline, the OOPSLA 2023 reachability certificates, what happened to the
implementations (spoiler: archived), what's still maintained, and where a
Covalence K frontend can attach.

## The CAV 2021 pipeline: K executions → Metamath proof objects

The foundational paper is
["Towards a Trustworthy Semantics-Based Language Framework via Proof Generation"](https://trinhmt.github.io/home/Proof/CAV21.pdf)
(Chen, Lin, Trinh, Roşu, CAV 2021). Its architecture has four components
**[high]**: (1) a logical foundation for K — matching logic; (2) **proof
parameters** emitted by K; (3) a proof-object generator; (4) a trustworthy
third-party checker (Metamath). K itself is deliberately a black box — the
paper's own words: *"we hide such complexity by letting K generate proof
parameters that include enough information for proof object generation."*

Concretely **[high]**: `kompile` compiles a K definition to Kore; the pipeline
translates that into an applicative matching logic (AML) theory Γ^L; each
concrete execution (`krun --depth N`) yields proof parameters — the complete
snapshot trace τ₀…τₙ plus, per step, which rewrite rule fired and its
substitution θ; a Python generator then emits a complete Metamath proof of
Γ^L ⊢ φ_init ⇒ φ_final. Proof objects are deliberately layered so components
are reused: the logic formalization (once and for all) → the per-language
semantics theory (reused across programs) → the per-execution proof **[high]**.

**The 245-line trust base.** The trusted Metamath formalization of matching
logic is *245 lines* (CAV21 verbatim: *"The resulting formalization has only
245 lines of code… This formalization of matching logic is the main trust base
of our proof objects"*; the OOPSLA 2023 follow-up cites it as 240 lines)
**[high]**. It covers AML pattern syntax, the proof system, metalevel
operations (free variables, capture-free substitution), and a `#Notation`
mechanism for sugaring/desugaring congruence **[high]**. The rationale for
Metamath: checkers are *"often hundreds lines of code and can proof-check
thousands of theorems in a second."* The contrast with Coq's ≥18,000-line
trusted OCaml codebase is drawn in the [OOPSLA 2023 paper](https://fsl.cs.illinois.edu/publications/lin-chen-trinh-wang-rosu-2023-oopsla.pdf),
*not* CAV21 (the researcher pass initially placed it in CAV21; verified against
both PDFs' full text) **[high]**.

## Sizes and timings (CAV21 Table 1)

Proof objects are huge but check fast; generation is the bottleneck **[high]**
(2021 hardware — modern checkers/hardware would be faster):

- 100-step `two-counters`: proof object **1,635.6 kLOC / 130 MB**, generated in
  **184.3 s**, checked in **5.6 s** total (~3.5 s of which is the reusable
  logic-foundation part, 2.1 s the task part) **[high]**.
- Worst case `tautologyhard`: 6,884.7 kLOC / 550 MB, generation 406 s, checking
  18.0 s **[high]**.
- Benchmarks: `two-counters` at depths 10/20/50/100 plus the REC rewriting
  suite (add8, factorial, fibonacci, benchexpr, benchsym, benchtree, langton,
  mul8, revelt, revnat, tautologyhard) **[high]**. Semantics-theory generation
  is ~4–12 s per language; per-step rewrite proof generation is linear in steps
  **[high]**.

## The honest trust gaps

CAV21 states three limitations explicitly, verbatim from the paper **[high]**:

1. **Trust kompile/Kore** — the K frontend → Kore compilation *"lacks a formal
   specification"*; it is trusted, unverified. (Being addressed on paper in
   2026 — see FoSSaCS below.)
2. **Trust domain reasoning** — integer arithmetic etc. are *"assumed lemmas"*;
   SMT proof-object generation was left to future work. The same hole persists
   in OOPSLA 2023: constraint implications are sent to Z3, *"resulting in a gap
   in our proof certificates"* **[high]**.
3. **Core K only** — no built-in collection datatypes (lists/sets/maps);
   supporting them needs unification modulo those theories **[high]**.

## OOPSLA 2023: certifying the reachability verifier

["Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier"](https://fsl.cs.illinois.edu/publications/lin-chen-trinh-wang-rosu-2023-oopsla.pdf)
(Lin, Chen, Trinh, Wang, Roşu; PACMPL 7(OOPSLA1) Article 23,
[DOI 10.1145/3586029](https://dl.acm.org/doi/10.1145/3586029)) extends the
pipeline from concrete execution to K's **one-path reachability verifier**
(`kprove`) **[high]**: each successful verification run — symbolic execution
plus coinductive discharge of loop circularities — yields a matching-logic
certificate for Γ^L ⊢ φ_pre ⇒reach φ_post, checked in Metamath.

Evaluated on three K-defined languages — IMP (imperative), REG (register
machine), PCF (functional) — over sum/exp/collatz/product plus SV-COMP
`loop-new` tasks **[high]**. Representative row (`sum.imp`): 42 symbolic steps,
0.58 MB hints, proof **37 MB raw / 1.6 MB xz**, K verifier alone 4.2 s,
certificate generation **105 s**, checking **1.8 s** with smetamath (or 9.6 s
with their Rust checker) **[high]**. Trust framing: K is ~550 kLOC of
unverified Haskell/Java/C++; certification eliminates the ~120 kLOC internal
verification algorithm from the trust base **[high]**.

## Repo reality: the whole certificate stack is frozen

- **[runtimeverification/proof-generation](https://github.com/runtimeverification/proof-generation)**
  (the CAV21/OOPSLA23 implementation; `kframework/matching-logic-proof-checker`
  redirects to it): Metamath formulation of matching logic, Kore formalized in
  ML, an interactive matching-logic theorem prover (at
  `src/proof_generation/itp/` in the final tree — the researcher pass initially
  cited an older `ml/itp` layout), and the automated proof generator. **Archived
  read-only 2024-02-15**, **NCSA-licensed** (permissive, import-friendly), ~540
  commits, mostly Python, pinned to old tooling (Python 3.10+, Z3 4.8.10, a
  customized K) **[high]**. No successor repo is pointed to.
- **[Formal-Systems-Laboratory/matching-logic-mm0](https://github.com/Formal-Systems-Laboratory/matching-logic-mm0)**
  (**BSD-3-Clause**): a parallel Metamath Zero track — AML in MM0
  (`00-matching-logic.mm0`, definedness and words/regex theories, mm1 proofs)
  plus a Maude-based generator producing MM0 proofs of regex totality via
  Brzozowski derivatives; published as "A Logical Treatment of Finite Automata"
  (Rodrigues, Sebe, Chen, Roşu, TACAS 2024). Demonstrates mechanized fixpoint
  (μ) reasoning — relevant to reachability — but dormant: last pushed
  2024-09-25 **[high]**.
- **Pi Squared → fast.xyz.** Roşu's spin-out ($12.5M raise) built "Proof of
  Proof" — Metamath/AML proof checking inside zkVMs, plus a custom
  parallelizable "block model" proof format for ZK; public code
  ([Pi-Squared-Inc/proof-checker-public](https://github.com/Pi-Squared-Inc/proof-checker-public),
  C++/Cairo/Rust checkers + zk-backend benchmarks) was **archived 2025-03-31**
  **[medium]** (archive status verified on GitHub; block-model/zkVM details come
  from now-dead pi2 docs). The company has since pivoted hard **[high]**: the
  GitHub org is renamed `fastxyz`, [pi2.network → pi2labs.org](https://pi2labs.org/),
  docs → [docs.fast.xyz](https://docs.fast.xyz/), and the current product is
  "Fast", a payments/settlement network for the agentic economy — with **no
  public mention of Proof of Proof, matching logic, or K** in current docs.
  Xiaohong Chen is CTO of fast.xyz; Zhengyao Lin went to CMU **[high]**.
  (Fast-moving startup — verified live 2026-07-13, could change again.)

Bottom line **[medium]** (the "nobody ships" conclusion is an inference from
public repos; private work at RV or fastxyz could exist): the science is
validated, the artifacts are permissively licensed (NCSA / BSD-3), but **nobody
currently ships a maintained K-execution-to-checkable-proof pipeline** — the
archived code is pinned to circa-2022/2023 K and Kore versions.

## What is still maintained: proof hints in the LLVM backend

K itself is actively maintained, and specifically
[runtimeverification/llvm-backend](https://raw.githubusercontent.com/runtimeverification/llvm-backend/master/docs/proof-trace.md)
(**BSD-3-Clause**, last pushed 2026-07-07) retains first-class **proof-hint
instrumentation** **[high]**: `kompile --proof-hint-instrumentation[-slow]`
plus `krun --proof-hint` emit a binary trace of rule-application events (rule
ordinal, arity, variable substitutions), hook/function-call events,
side-condition events, and KORE configuration snapshots, with
`kore-proof-trace` / `kore-rich-header` as reference consumers. This is the
modern descendant of CAV21's "proof parameters" and is what Pi Squared's
pipeline consumed. **Nothing in the K org currently turns these hints into
checkable proofs** — that layer is the archived repo **[high]**. (Format
details can evolve with llvm-backend releases; verified against master
2026-07-13.)

## Fresh theory: closing the kompile gap

["K Definitions as Matching Logic Theories, Formally"](https://link.springer.com/chapter/10.1007/978-3-032-22730-0_10)
(Chen, Cheval, Lucanu, Roşu, FoSSaCS 2026, first online April 2026) gives a
formal denotational semantics of K definitions directly as matching-logic
theories, explicitly targeting CAV21's Limitation 1 (kompile as *"a trusted but
unverified component"*) **[high]** (fresh publication; the verification pass
notes it was not yet on the FSL publications index — worth re-checking before
formal citation). This confirms the K→Kore→ML lowering is still an active
research concern even as the proof-generation implementations sit archived.

Foundational reading **[high]**: Roşu, "Matching Logic" (LMCS 13, 2017);
Chen–Roşu, "Matching μ-Logic" (LICS 2019 — adds the least-fixpoint μ binder
that subsumes reachability/LTL/CTL); and the
["Applicative Matching Logic: Semantics of K" tech report](https://fsl.cs.illinois.edu/publications/chen-rosu-2019-trb.html)
(July 2019), which defines the minimal applicative variant the 245-line
formalization targets — per its own abstract, AML is *"much simpler… yet as
expressive as matching mu-logic"* (the researcher pass initially attributed a
"simplest variant" quote to CAV21; the CAV21 full text contains no such
sentence, nor even the word "applicative") **[high]**.

Ecosystem periphery **[medium]** (from search results, not fetched pages): a
Coq/Rocq AML mechanization (harp-project/AML-Formalization — see the
reachability doc), a Lean project (ILDS/RV 2022), a Dedukti recheck of
proof-generation objects (Ledein, EuroProofNet 2022), and a 2025 arXiv paper on
dependently-typed AML encodings.

## What this means for Covalence

- **The seam is proof hints.** The maintained attach point for a Covalence K
  frontend is the LLVM backend's binary proof-hint stream — exactly the "proof
  parameters" role from CAV21. Consume Kore + hints, lower rewrite rules to
  internally-defined relations (the `Derivable_R` machinery that already serves
  SpecTec), and certify traces internally — Covalence's Metamath substrate
  playing precisely the role the 245-line formalization played.
- **The field is open.** Everything between K's hint emission and a checked
  proof is archived (Feb 2024 / Mar 2025 / Sep 2024). That is both risk
  (bit-rot against current K/Kore) and opportunity: no one is shipping this.
- **Licenses permit import.** proof-generation is NCSA, matching-logic-mm0 and
  llvm-backend are BSD-3 — all importable with attribution.
- **Budget expectations from the papers**: certificates in the tens-of-MB /
  millions-of-lines range, generation minutes, checking seconds; and plan for
  the SMT/domain-reasoning hole — it is the one gap neither paper closed.

## Sources consulted

- https://trinhmt.github.io/home/Proof/CAV21.pdf
- https://fsl.cs.illinois.edu/publications/lin-chen-trinh-wang-rosu-2023-oopsla.pdf
- https://fsl.cs.illinois.edu/publications/lin-chen-trinh-wang-rosu-2023-oopsla.html
- https://dl.acm.org/doi/10.1145/3586029
- https://fsl.cs.illinois.edu/publications/chen-lin-trinh-rosu-2021-cav.html
- https://fsl.cs.illinois.edu/publications/ (and /chen-rosu-2019-trb.html)
- https://github.com/runtimeverification/proof-generation
- https://github.com/kframework/matching-logic-proof-checker
- https://github.com/Formal-Systems-Laboratory/matching-logic-mm0
- https://github.com/Pi-Squared-Inc/proof-checker-public
- https://raw.githubusercontent.com/runtimeverification/llvm-backend/master/docs/proof-trace.md
- https://link.springer.com/chapter/10.1007/978-3-032-22730-0_10
- https://pi2labs.org/ ; https://docs.fast.xyz/ ; https://xchen.page/
- https://blockworks.co/news/pi-squared-raises-12-5-million
- https://blog.pi2.network/zkvm-benchmarking/
- https://europroofnet.github.io/_pages/WEPN/2022/abstracts/WEPN_2022_Ledein.pdf
- https://arxiv.org/pdf/2509.13018 ; https://www.ideals.illinois.edu/items/119513

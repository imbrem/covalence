# notes/vibes/k/ — the K-framework corpus

Everything behind the K frontend: the sourced research surveys and their
synthesis. The north star lives in
[`../vision/k-framework-vision.md`](../vision/k-framework-vision.md); the
actionable decision record is
[`../../design/k-frontend.md`](../../design/k-frontend.md) (input surface =
KORE, the fragment ladder F0–F4, the sublanguage ladder). First code slice:
`crates/lang/k` (`covalence-k`).

**Resume here:** [`reduction-demo-scope.md`](./reduction-demo-scope.md) — the
detailed scope + layered-API architecture + roadmap for the medium-term north
star (*demo the basic K tutorial languages end-to-end*; K a first-class IR on
par with Metamath). Target = Lesson 1.2 `colorOf`/`contentsOfJar` + a PEANO
demo; the four missing pieces (matcher, congruence, driver, `.k` rule reader);
the `KSession`-as-`MmSession`-peer framing.

## `research/` — sourced surveys (researched 2026-07-13)

Web-researched from primary sources with an independent verification pass;
every claim carries a certainty tag and rot-prone facts carry staleness notes.

| Doc | What it covers |
|---|---|
| [`research/k-framework-today.md`](./research/k-framework-today.md) | K in 2026: repo/version/license state, anatomy of a `.k` definition, kompile, KAST vs KORE, pyk, tutorials. |
| [`research/kore-ir.md`](./research/kore-ir.md) | KORE — the kompiled matching-logic IR: grammar, axiom shapes, attributes, JSON encodings, stability; why it's our ingestion surface. |
| [`research/backends-and-smt.md`](./research/backends-and-smt.md) | LLVM + Haskell backends, the KORE-RPC protocol, exactly where Z3 sits (QF_LIA+UF side conditions), kprove/KCFG — and the absence of proof objects. |
| [`research/semantics-ecosystem.md`](./research/semantics-ecosystem.md) | The semantics to import, by tier: KEVM/Kontrol, KWasm, KMIR, RISC-V (active) · KPlutus/KAVM/IELE (dormant) · c-semantics, x86-64 (frozen, legacy-K). Licenses + K-pins. |
| [`research/proof-generation.md`](./research/proof-generation.md) | RV's proof-certificate line: CAV'21 Metamath pipeline, OOPSLA'23 reachability certificates, the Pi Squared pivot, LLVM-backend proof hints — the opening Covalence fills. |
| [`research/reachability-and-matching-logic.md`](./research/reachability-and-matching-logic.md) | The theory: AML / matching μ-logic vs the RL papers' FOL fragment, the all-path proof system, why Circularity is inductively (step-indexed) sound, prior embeddings to crib. |

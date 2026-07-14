# K frontend — KORE ingestion + the fragment ladder — design doc

- **Status:** Draft
- **Owner:** agents (drafted 2026-07-13 for maintainer review)
- **Last touched:** 2026-07-14
- **Related:** [`notes/vibes/vision/k-framework-vision.md`](../vibes/vision/k-framework-vision.md)
  (the north star), [`notes/vibes/k/`](../vibes/k/README.md) (the sourced research
  corpus behind every external claim here), [`notes/vibes/logics/wasm-spec.md`](../vibes/logics/wasm-spec.md)
  (the SpecTec frontend this mirrors), `crates/lang/k` (covalence-k, the first
  slice), `crates/kernel/hol/init/src/metalogic` (the rule-induction engine).

## Context / problem

The K framework north star ([vision note](../vibes/vision/k-framework-vision.md))
wants K definitions — WASM, x86, C, IMP/LAMBDA, eventually the SSA dialect —
hosted inside Covalence as object semantics, with theorems like *"under rule set
R, term A reduces to term B"* (B possibly open) stated and checked internally,
Metamath-style. The vision note left the input surface as an open question and
sketched the lowering only by analogy.

The research corpus (notes/vibes/k/research/) settles the facts we need:

- **KORE is the stable elaborated surface.** `kompile` desugars everything
  (strictness/heating/cooling, contexts, configuration abstraction) into
  `definition.kore` — a one-page-of-BNF matching-logic language, S-expression-
  shaped, stable since ~2019, with rewrite rules as `\rewrites` axioms and side
  conditions as `\equals(b, true)`. Consuming it keeps us out of K's Java
  frontend entirely — the exact analogue of consuming SpecTec's elaborated AST
  instead of `.watsup`.
- **K's own symbolic pipeline has no proof objects.** kprove/KCFG validity rests
  on trusting the Haskell backend + Z3. RV's proof-generation line (CAV'21 /
  OOPSLA'23) emitted *Metamath* proofs over a ~245-line AML formalization — and
  is archived since 2024-02; its commercial successor (Pi Squared) pivoted away.
  Nobody ships a maintained K-to-checkable-proof pipeline. That is Covalence's
  opening, and it lands on our existing internal-Metamath waist.
- **Reachability logic needs no coinduction.** The all-path system's Circularity
  rule is proved sound *inductively* via step-indexed satisfaction over the
  transition relation — which maps directly onto the impredicative
  `Derivable_R` least-fixpoint machinery (`metalogic::{RuleSet, derivable,
  rule_induction}`) that Metamath and SpecTec already share.
- **SMT use is shallow and fenced.** Z3 only decides side-condition
  satisfiability in ~QF_LIA + uninterpreted functions; everything else is
  abstracted or handled by K-level `simplification` lemmas. "The same SMT proofs
  as the Haskell backend" is a bounded re-certification target, not open-ended.

## Goals

- A K frontend that ingests `definition.kore` (textual), classifies its axioms
  into explicit fragments, and renders a canonical S-expression IR.
- A fragment ladder where each rung is independently useful and lowers to the
  kernel through the existing metalogic engine — reduction theorems first,
  reachability claims later, SMT parity last.
- Real semantics as milestones: tutorial-scale first, then KWasm (active,
  NCSA-licensed, K 7.1.x) toward the KWasm ⟷ SpecTec agreement metatheorem.
- Same trust story as Metamath/SpecTec: the frontend is an untrusted driver;
  bugs cost faithfulness/completeness, never soundness.

## Non-goals

- **No *general* `.k` parser.** The full K surface language (grammars,
  strictness elaboration, configuration sugar) stays upstream; kompile is the
  elaborator. (Its trust status is a known gap K itself is addressing —
  FoSSaCS 2026 formalizes the K→ML-theory map.) **Purpose-built parsers for
  specific target projects are in-scope**, though (maintainer decision
  2026-07-13): the frozen tier (x86-64, c-semantics) won't kompile on modern K,
  so the plan there is a custom frontend for exactly the `.k` subset those
  projects use — parse the project, not the language.
- **No full AML embedding up front.** Full applicative matching logic (patterns
  as sets, μ/ν, the 13-rule Hilbert system) is the *eventual* semantic anchor —
  as a Metamath database on the waist, where RV's own formalization went — but
  the ladder gets reduction/reachability theorems without it.
- **No legacy-K dialect yet.** c-semantics and x86-64 are frozen on ~2019–2021 K
  and won't kompile on 7.x; they need either a port or an old-dialect ingestion
  story. Recorded as a guardrail, not a phase (per the defer-as-guardrails rule).
- **No trusting K's backends.** LLVM-backend proof hints / KCFG output are
  oracles whose traces we certify, never certificates we admit.

## Proposal

### Input surface (decided): `definition.kore`

Textual KORE, parsed by the new **`covalence-k`** crate (`crates/lang/k`) —
kernel-free, `#![forbid(unsafe_code)]`, deps `covalence-sexp`/`smol_str`/
`thiserror` only. Slice 1 (this change): `ast` (definitions, modules, sentences,
patterns, sorts), `parse` (hand-rolled, byte-offset errors, handles K's mangled
identifiers / multiary `\and` / sort-parameter quirks), `sexpr` (the canonical
S-expr IR — the "simple S-expression based intermediate representation"),
`fragment` (axiom classifier + `RewriteRule` extraction with priority/owise,
requires/ensures, label/unique-id). KORE-JSON and KAST-JSON ingestion are
recorded skeletons; pyk's parser is the reference implementation to crib from.

### The fragment ladder

Each fragment is a *feature* (per the explicit stepping-stones requirement), not
just a milestone; `fragment::classify` makes membership checkable. Fragments are
also allowed their own **purpose-built IRs** (maintainer decision 2026-07-13):
the canonical KORE S-expr IR is the shared floor, but a rung may compile its
KORE/K fragment into a smaller custom S-expr IR when that makes the lowering or
the theorem statements simpler — one IR per job, not one universal IR.

- **F0 — ground rewriting.** Unconditional `\rewrites` axioms over constructor
  terms. Lowering: encode KORE application terms into the uninterpreted free
  term algebra over `Φ = nat` (`k$app`, `k$c$…`, metavariables `k$v$…` — the
  `wasm::encode` recipe verbatim, so HOL substitution = KORE substitution), one
  `Derivable_Step` clause per rule via `metalogic::RuleSet`. Concrete-step
  theorems `⊢ Derivable_Step ⌜cfg ↪ cfg'⌝` come from `derive`; multi-step by
  chaining. Demo: a counter/IMP-style tutorial semantics.
- **F1 — conditional rewriting + functions.** `requires`/`ensures` over hooked
  `Bool`/`Int`, and function-rule axioms (`\implies`/`\equals` shape). Needs the
  *hook theories*: a small vocabulary of hooked sorts/symbols (INT, BOOL, then
  MAP/LIST/SET/BYTES) mapped onto kernel catalogue types with computation rules —
  the K analogue of SpecTec's leg-B side conditions, and the same blocker shape
  (side conditions = decidable function predicates). Priority/`owise` is a
  backend *convention* (no negation axioms are emitted): model it explicitly as
  rule order in the lowered relation and record the caveat.
- **F2 — reachability with open targets.** `A →* B` with `B` open/existential:
  reflexive-transitive closure over the F0/F1 step relation, stated with free
  variables or `∃` in the conclusion. The metalogic engine supports free vars in
  derivation conclusions today; what's missing is a reusable RTC/`Reduces*`
  layer over `Derivable_Step` (the internal-derivability exploration's gaps 2/6)
  — build it once, K and SpecTec both consume it.
- **F3 — reachability claims (the K proof system).** One-path/all-path claims
  `φ ⇒ φ'` and the 8-rule all-path system with Circularity, embedded via
  step-indexed satisfaction over the F2 relation (inductive, per the LMCS'19
  soundness proof; Rusu–Nowak's Coq mechanization is the crib). KCFG JSON from
  pyk becomes an untrusted proof *sketch* we replay: Edges = step chains, Covers
  = implications, Splits = case analysis. LLVM-backend proof hints
  (`--proof-hint-instrumentation`, actively maintained) are the concrete-trace
  oracle for execution-as-proof.
- **F4 — SMT parity.** Re-certify what K delegates to Z3: the QF_LIA + UF
  side-condition fragment. Options, in order: internal arithmetic decision
  procedures over the catalogue types; or swap in a proof-producing solver and
  replay through `crates/proof/alethe` (cvc5 emits Alethe; Z3 does not).
  `smt-lemma`/`simplification` rules become internally proved lemmas instead of
  solver assertions.

### Sublanguage ladder (which semantics, in order)

Tutorial IMP/LAMBDA (pl-tutorial, BSD-3) → **KWasm** (active, K-pinned, NCSA;
the headline: relate its step relation to the SpecTec lowering — a *simulation*
between materially different configuration encodings: KWasm's flat cells +
explicit `<valstack>` vs SpecTec's evaluation contexts — not a syntactic match)
→ KMIR / RISC-V (active, BSD-3, small) → KEVM (active, production-grade, big)
→ frozen tier (c-semantics, x86-64) behind the legacy-K guardrail → the SSA
dialect (hand-written K definition, ours). K itself (its meta-semantics) is the
reflective capstone from the vision note.

### The `.k`-source grammar frontend (`covalence-k::kdef`)

A **second, complementary** input surface, distinct from KORE ingestion: read a
K definition's *grammar* — its `syntax` (BNF) declarations — directly from `.k`
source. This is the "custom frontend for a K fragment" the maintainer okayed
(2026-07-13): rather than depend on kompile to read a tutorial language's
grammar, parse it ourselves. Landed:

- **Parser** (`kdef::parse`) — a [winnow]-based parser (via the workspace
  wrapper `covalence_parse::winnow`, so it can grow toward a large K subset) for
  `requires`/`module`/`imports` and `syntax Sort ::= …` productions: terminals,
  non-terminals (with optional `name:` labels), `|` alternatives, `>` priority
  blocks, `left:`/`right:`/`non-assoc:` block tags, `[attr]` lists, `List{}`/
  `NeList{}` sugar. Non-`syntax` sentences (`rule`/`configuration`/…) are
  *skipped* and counted — this reads grammar, not semantics.
- **AST + S-expr IR** (`kdef::ast`, `kdef::sexpr`) — plain data + a canonical
  deterministic rendering.
- **CFG lowering** (`kdef::cfg`) — lower a module's grammar to a
  `covalence_grammar::Cfg<char>` (terminals → char-regexes, non-terminals → refs,
  `List{}` desugared, priority/brackets **flattened** — priorities are parse-time
  filters over the same context-free language). This is the neutral IR the
  **kernel CFG stratum** (`covalence-init::grammar::cfg`, `Derives_E`) already
  consumes — the bridge from "parse a K grammar" to "internally certify that a
  token string is a valid program of it".
- **Imported builtin sorts as a strategy** (`kdef::cfg::SortResolver`) — sorts a
  module references but does not define (`Id`/`Int`/`Bool` from
  `DOMAINS-SYNTAX`) resolve through a swappable trait: `NoDomains` leaves them
  empty (structural CFG only), `KDomains` injects the standard K token regexes so
  the CFG recognises real tokens; a future resolver could follow `imports`
  transitively. (Inter-token layout/whitespace is a separate scanner concern, not
  yet modelled — see `SKELETONS.md`.)

It parses the real **LAMBDA** and **IMP** tutorial grammars (vendored BSD-3 in
`crates/lang/k/examples/k-tutorial/`). This surface is independent of the KORE
pipeline: it does not (yet) read K *rules*, and does not kompile to KORE.

[winnow]: https://docs.rs/winnow

### Trust boundary

`covalence-k` and every lowering above it are untrusted drivers, exactly like
`covalence-metamath`/`covalence-spectec`: the kernel re-checks each
construction; `Derivable_*` witnesses are pure syntactic data. The TCB does
**not** move. Long-term, the AML-in-Metamath database (artifact #1 of
[`logic-frontends.md`](../vibes/logics/logic-frontends.md)) becomes the semantic
anchor `D_AML` on the waist, with the F0–F3 machinery as its native accelerator
and RV's archived formalization as the reference — that is the leg-A/leg-B
mirror from `wasm-spec.md`, replayed for K.

## Alternatives considered

- **Parse `.k` directly for the *semantics*** — no: elaborating the full `.k`
  language (strictness → heating/cooling, configuration abstraction, macro
  expansion) is a large Java system; kompile already emits the elaborated theory
  as KORE, which is what we ingest for reduction theorems (SpecTec's no-`.watsup`
  reasoning). *Parsing the `.k` grammar itself is in scope, though* — that's the
  `kdef` frontend above, a deliberately separate, smaller job that reads only the
  `syntax` declarations (and will grow toward a larger subset over time).
- **Ingest KAST JSON (`compiled.json`) instead of KORE** — pre-elaboration
  representation with meta-level `#And`/`#Equals`; less stable meaning, and the
  backends don't execute it. Kept as a skeleton for tooling interop (pyk speaks
  it), not the primary surface.
- **Full AML embedding first** — heaviest path to the first theorem; the
  RL-over-transition-relation route (F0–F3) mints useful reduction theorems
  early and the AML database can anchor it later without rework (the step
  relation is the same object).
- **Adopt RV's Metamath proof-generation artifacts wholesale** — archived,
  NCSA-licensed, tied to circa-2021 Kore; we crib the design (and eventually
  relate to it on the waist) rather than depend on it.

## Open questions

- **Hooked collections.** INT/BOOL map cleanly onto catalogue types; `MAP` (the
  configuration workhorse) needs a kernel-side finite-map theory with the right
  computation rules — biggest F1 unknown.
- **`binder` attribute.** K object-language binders compile to application
  symbols + backend substitution hooks, essentially undocumented. Fine for
  WASM/IMP (no object binders); LAMBDA needs an answer.
- **Cell encoding.** Encode cells as plain constructors in the free algebra (F0
  does this) vs. structured kernel data (`covalence-inductive` / carved sexprs)
  for the F2+ layers — decide when the RTC layer lands.
- **Priority soundness.** Modeling priority/owise as ordered rule choice is a
  *convention* imported from the backends; is there a cheap way to state what it
  assumes (rule-condition disjointness) internally?
- **Version pinning.** K releases per-merge (7.1.x); active semantics pin via
  `deps/k_release`. Pin one K version per imported semantics and record it, or
  chase latest?

## Status / next steps

- **Landed (slice 1):** `covalence-k` (parse + S-expr IR + fragment classifier +
  tests), the research corpus (`notes/vibes/k/`), this doc.
- **Landed (F0 lowering):** `covalence-init::k` (`crates/kernel/hol/init/src/k/`)
  — the K analogue of `wasm/`. `encode` reifies KORE configuration patterns into
  the free term algebra over `Φ = nat` (evar → metavariable, app → tagged node,
  `\dv`/string → literal constant); `reduce` lowers unconditional `RewriteRule`s
  to a `Derivable_KStep` `RuleSet` (one `∀x…. d ⌜Step(LHS,RHS)⌝` clause per rule,
  conditional rules skipped + reported) and `reduce::step` mints a concrete
  `⊢ Derivable_KStep ⌜Step(cfg, cfg')⌝` via `metalogic::apply` — hypothesis-free,
  kernel-checked, TCB unchanged. End-to-end test parses textual KORE →
  `Step(count(0), done)`. Skeletons in `src/k/SKELETONS.md`.
- **Landed (`.k` grammar frontend):** `covalence-k::kdef` — a winnow-based
  parser for K's `.k` `syntax` declarations + S-expr IR + `covalence_grammar::Cfg`
  lowering with the swappable `SortResolver` strategy for imported builtin sorts.
  Parses the real **LAMBDA and IMP** tutorial grammars (vendored BSD-3). See the
  `.k`-source subsection above.
- **Landed (F2 — multi-step reduction):** `covalence-init::k::relation` — K
  reduction as a *genuine relation* on the binary inductive engine
  (`metalogic::binary::RuleSet2`, the same engine the CFG stratum and the merged
  Lisp `Reduces` relation use). `kstep_rule_set` builds `KStep : Φ → Φ → bool`
  (one base clause per unconditional rewrite rule); `kreduces_rule_set` builds
  `KReduces = KStep*` (`refl` + `step` clauses). `prove_step` mints
  `⊢ KStep a b`, `prove_reduces` folds a step chain into `⊢ KReduces a b` — so
  `A →* B` with `B` open is directly statable. Headline test:
  `⊢ KReduces ⌜count(0)⌝ ⌜done⌝` from two steps, hypothesis-free. This supersedes
  `reduce`'s single-step unary encoding for multi-step work.
- **Next:** (1) an **untrusted redex matcher + reduction driver** (find the
  firing rule + substitution at a concrete configuration, drive
  leftmost-innermost to normal form building the `KReduces` chain — cf. the Lisp
  `prove_reduces` fuel driver) + **congruence/context clauses** for `KStep` (so a
  redex buried in a cell can step) + a `/k` REPL over the merged `repl-core`
  stack; (2) **hook theories** (F1 — hooked `Bool`/`Int`/`Map` → catalogue types)
  to admit conditional rules; then a tutorial IMP semantics as the first
  whole-definition demo, en route to KWasm↔SpecTec.
- **Longer term (matching-logic ↔ Metamath):** relate the `Derivable_KStep`
  world to the Metamath substrate now that `mm-metatheory` landed
  (`metalogic::{apply, mm_session, mm_compose}`): KORE axioms are an
  applicative-matching-logic theory, and RV's own trust story renders K proofs
  *as Metamath* over a ~245-line AML formalization (see
  `notes/vibes/k/research/proof-generation.md`). The `S`-transport /
  `Derivable_L₁(A) ⟹ Derivable_L₂(S A)` machinery in `metalogic` is the bridge —
  an AML-in-Metamath database `D_AML` as the semantic anchor, with F0–F3 as its
  native accelerator.

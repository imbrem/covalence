+++
id = "N002W"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Thoughts on the separation plan (discussion draft, agent-authored)

Reactions to `notes/plans/sketch-separation.md`. Opinionated on purpose; for us to
argue with. Not committed.

## The core move: sketch → clean `covalence` — I think this is right, with nuance

The instinct ("this is a vibe-coded sketch; copy it over already-in-final-form, each
piece reviewed as we go") is the correct quality bar and I'd commit to it. Two
refinements:

- **Prefer the branch/reset over a new repo — for now.** You already named the reason:
  no external deps, one checkout, so aggressive history ops are free *only right now*.
  `main → initial-sketch`, reset `main` to empty, cherry-pick clean. A second repo buys
  you almost nothing today and costs you the cross-links (SKELETONS, notes, the
  worklog trail) that are currently the map. Keep it one repo until there's an actual
  external consumer.
- **The `develop`(green) / `main`(sound-with-high-confidence) invariant is the best idea
  in the doc.** It's the thing that makes "sketch on top of a solid core" actually
  work: sketches live as branches off `develop`; promotion to `main` is the point where
  the adversarial-audit discipline we've been using becomes the *gate*, not a habit.
  I'd write that invariant down as the first entry in the new repo's CONTRIBUTING.

**But** — the doc's own caveat is the real constraint: don't copy over until the shapes
are stable, or you'll re-copy. Which is exactly why "fix the high-level APIs first" is
load-bearing. So the sequencing question dominates everything else.

## "Fix the high-level APIs first" — where each one actually stands

My read of readiness (this is the thing to calibrate together):

| API to fix | State | Note |
|---|---|---|
| **Core kernel API** | **Closest.** | `covalence-hol-api` (Hol/Nat/HolOmega traits) + `covalence_pure::api` + `CertificateAlgebra` + `InductiveBackend<L>` are exactly "fix the kernel API." The `SExprRep` carving (see the Lisp answers) is the next chunk. This is the one to *finish and freeze* first. |
| **Content addressing** | **Not started; the real gate.** | You said it yourself: a product needs this. Right now it's design-only (`store/`, `CertificateAlgebra`'s `execute`/hash story, the relations vision). Nothing to freeze yet. **This is the critical path.** |
| **WASM compile + interp** | **Partial.** | `covalence-web-kernel` + the wasm-build/store lore exist; SpecTec/WASM front ends exist; but "compile + interpret + *accelerate the kernel*" as a fixed API is not there. |
| **WASM acceleration of the kernel** | **Not started.** | The `term-arena-vs-wasm` note flags it; it's the perf endgame, and it's downstream of the kernel API being stable. |
| **Server/client (HTTP + WS)** | **Exists, unfrozen.** | `cov serve`, the web kernel, the article path. The API isn't *fixed* (async ArticleSource still stubbed) but it's the least risky. |

**So the honest ordering I'd argue for:** (1) finish + freeze the **kernel API**
(incl. `SExprRep` and the inductive/backend surface — we're ~1–2 focused passes away);
(2) **content-addressing** as its own real build, because it gates "a product" and
everything persistent (SQLite, proof import, federation) hangs off it; (3) the **WASM
compile/interp/accelerate** API; (4) server/client last (cheap to stabilize once the
kernel + store APIs are fixed). The extension features (§ below) ride on those four.

The tell that we're ready to start copying: the kernel + store APIs stop churning
across two consecutive sketches.

## The "API vs application" split per extension — yes, and we've been doing it

This is the right discipline and it's already the pattern of the last several sessions
(trait API + a consumer that runs unchanged: `covalence-hol-api` + the migrated
consumer; the `Realize`/`SExprRep` producer + `HolBackend`; the proof-format *linker*
API + the web checker *application*). I'd make it explicit: **every extension gets an
`*-api` crate (or module) and a separate application, and the application must compile
against the API with the backend swapped.** That's the single best forcing function
for the "runs unchanged when we change the backend" property the whole plan is about.

## Naming base/eval/top — the top layer is a *family*, and the names should say so

You're right that "top" is wrong because there's more than one, and the list
(Metamath@{ZFC,GT,HOL,IZFC}, ACL2/Lisp, K, SpecTec, SMT-LIB, PA/SOA, Dedukti/STLC/F,
GT3, WASM-as-strange-loop) makes clear the top isn't a *layer*, it's a *plane of object
logics*. Some naming thoughts (bikeshed freely):

- The three tiers are really **trust/computation tiers**, not a fixed count:
  - **base** = the untrusted-relations substrate (computation as `execute`; content
    addressing; system interop). Suggest: **`substrate`** (or `machine`) — it's where
    "this bash command ran here" lives, and it's the SQLite-dumpable trust floor.
  - **eval/middle** = the trusted metalogic — HOL-ω, the certificate algebra. Suggest:
    **`metalogic`** or **`kernel`** (the LCF core). This is the one that must be *sound*.
  - **top** = **object logics** (a family, not a layer). Suggest: **`logics/`** as a
    directory of instantiations, each an *object logic* hosted in the metalogic.
- Then the families you list are naturally **`logics/{metamath, acl2, k, spectec,
  smtlib, pa, soa, dedukti, systemf, gt3, wasm}`**, and "Metamath@ZFC" etc. are
  *models/instantiations* within the metamath logic — which matches how you already
  treat PA/SOA as a subset of Metamath. This directory-of-object-logics framing might
  itself be worth a design doc; it dissolves the "what do we call the top layer"
  problem by saying there isn't one top, there's a plane.
- WASM-as-top ("strange loop") is the interesting one: it's *both* a base executor
  (untrusted relation) *and* an object logic (its own spec). I'd keep both roles and let
  the strange loop be an explicit, documented bridge rather than a naming compromise.

## The HOL-ω / System F consistency question (line 65) — my belief, flagged for checking

I would *not* assert this without checking, but my strong prior: **plain HOL is already
enough to prove System F's consistency (strong normalization).** Girard's
reducibility-candidates proof is impredicative but lives comfortably in
higher-order arithmetic, and HOL (higher-order logic with infinity + choice) is
considerably stronger than that. So HOL-ω is likely *not required for the consistency
proof.* Where HOL-ω earns its keep is different: it's the natural *home* for embedding
F-ω-style **type-operator polymorphism natively** (the `HolOmega` trait, rank
stratification) — i.e. hosting System F / F-ω as an object logic ergonomically, not
proving its consistency. Worth a literature check before we write it down (this is
exactly the kind of claim the deep-research skill is for). The "Categories for Types"
machinery you want is the same story: it's about *hosting* the type theory, and the
consistency proofs are a separate, likely-cheaper-than-expected obligation.

## The Python-API-per-layer idea — strong, and it's a good test of the abstractions

Two reasons I like it beyond "helps agents": (1) a clean Python binding per layer is a
*proof that the layer's API is actually an API* (if it doesn't bind cleanly, it wasn't
factored right) — so it doubles as an API-quality ratchet; (2) it forces first-class
dynamic support, which the relations substrate wants anyway (system interop, "ran here"
predicates). I'd sequence it *after* each layer's Rust API is frozen (bind the frozen
thing), not before — otherwise the bindings churn with the API.

## What I'd actually do next (concrete)

1. **Finish the kernel-API freeze**: land `SExprRep` + the deparse/observe pair (the
   Lisp answers doc), port a *second* `InductiveBackend`, and migrate one more real
   consumer off `TermKind`. When two sketches don't move these, call it frozen.
2. **Start content-addressing for real** — it's the product gate and the substrate for
   SQLite/proof-import/federation. This is the biggest genuinely-unstarted piece.
3. **Write two design docs** (using the new `notes/design/` framework): the
   *object-logics plane* (the naming + the family taxonomy above) and the
   *content-addressing / relations substrate* (you already have a stub) — these are the
   two conceptual forks that, once settled, make the "copy over cleanly" transition
   tractable.
4. Only then start the `develop`/`main` split + the careful copy-over.

## One risk to name

The plan's success depends on *stopping the sketch sprawl* long enough to freeze APIs.
The recent cleanup (project-map, design-doc framework, `what-is-the-tcb`, the trait
APIs, the demo pages) was the right first move against exactly that. The failure mode
is starting the copy-over before content-addressing exists, discovering it forces a
kernel/store API change, and re-copying. So: **content-addressing before copy-over**,
even though it's tempting to freeze the parts that already look clean.

# TCB-simplification / HOL-ω program — decision & history log

A chronological, append-only record of decisions, rationale, audit verdicts, and
commits for the program that drives the kernel toward **textbook HOL-ω** (most code
written Haskell-style), a **relation-calculus base** (all computation = untrusted
relation evaluation), and — long-term — **`Expr<Ctx>` schema variables** with
`Computation ⟹ Relation` (the WASM story). Companion to the design roadmap
[`tcb-holomega-roadmap.md`](./tcb-holomega-roadmap.md) (the plan) and the memory
note `base-relcalc-holomega-vision` (the standing directives). This file is the
*history* (why each choice was made, what the audit said); the roadmap is the
*plan*; git commits are the *what*.

Convention: newest entries at the bottom. Each entry = date · what · why · verdict ·
commit(s).

---

## 2026-07-08 — session foundations (before this program)

- **Integer parsing solidified** (gating benchmark) — full radix-generic
  `parse_nat_correct`/`parse_int_correct`, all radices, hypothesis-free. Audited
  SOUND (3/3 dims). Merged. *Why:* the user's "make integer parsing really solid"
  first-priority; gates JSON.
- **Float / S-expr / JSON parsing** — S-expr reader → carved `sexpr`, exact decimal
  float parser, JSON reader + `same_json` PER (sym/trans/refl-on-domain). Merged.
  Then **strict JSON integer-subset** (faithfulness + subset), and the string-level
  `same_json` PER + the ∀ whole-value integer subset (closed **without** the
  induction wall — `parse_json_int` is non-recursive, so `atom_span` coincides
  syntactically). All HOL-only, zero-TCB, genuine.
- **relcalc base Phase 0 + positive calculus** — `rel.rs` (`UntrustedFn`/`Rel`/
  `execute` minting positive membership over zero-copy `Ref<Arc<_>>`, `transpose`,
  `compose`/`join`/`meet`) + generic `tyrep.rs` (`TyFn`/`TyApp`). Design doc through
  2 audit-verified revision rounds. **Two adversarial TCB audits, both SOUND.**
  *Why:* the user's "give it a go" on the audited base redesign.

## 2026-07-08 — leaf elimination: float unwall (EG2 residue)

- **Decision:** unwall float — add the two new admitted `CoreEval` reify rules
  `ToHolF32Val`/`ToHolF64Val` + f32/f64 add/mul symbolic landers. *Why:* float was
  the one literal family blocked from symbolic landing (EG1 nat + EG2 int/bytes
  done); maintainer explicitly approved the +2-rule TCB delta over the
  alternatives (EG3 architectural / design-only).
- **Audit verdict: SOUND** (no holes, no must-fixes). The reify rules are
  pure/total/injective `bits → u32/u64_lit` maps carrying **zero float semantics**
  (all float meaning stays in `FloatCert`); no canonicalization gap (the wave-2
  `LitEqCert` bug class does not recur); gating correct; **base/core manifests
  byte-unchanged** (only `evalManifest` 14→16). Commit `1ab7aefe`; merged.
- Remaining float ops (sub/div/min/max/cmp/convert) recorded in SKELETONS — none
  need a new admitted rule.

## 2026-07-08 — merge everything to (local) main

- **Decision:** merge all session work into `main` locally (maintainer: "just merge
  everything into main; I'll push it up later"). `main` FF'd to the parsing/float/
  JSON line, then `--no-ff` merged the relcalc base Phase 0. HEAD `8b5b76e3`;
  combined build green (base/trusted 51, eval float-symbolic all pass).
- **Constraint recorded:** pushes are blocked — a pre-push hook allows only `main`,
  and the auto-mode classifier blocks direct `main` pushes (PR review). So origin is
  behind; local `main`/`pure-impl-1` are the rollback points until the maintainer
  pushes. *Decision:* do NOT disable the hook or force-push — maintainer's policy.

## 2026-07-08 — program kickoff: design roadmap workflow

- **Decision:** before implementing any of the (architectural, TCB-gated)
  continuation, run a 5-architect design workflow → synthesis → adversarial review,
  producing `tcb-holomega-roadmap.md`. *Why:* "don't improvise the walls" — the
  leaf-removal symbolic-prop wall, HOL-ω rank stratification, defs-without-global-
  state, and especially `Expr<Ctx>` + pattern-matching in the sealed mint-gated
  grammar all carry real soundness risk; design + adversarial check first.
- Fronts: A leaf-removal+defs-out · B HOL-ω middle + Ty/kind base constructors ·
  C Haskell-in-HOL-ω · D relation-calculus-as-computation · E `Expr<Ctx>` schema
  variables + `Computation⟹Relation` + WASM. Workflow `wsx6mbbnv`.
- **Next:** on completion — record the review's verdicts + the chosen safe-first
  stage here, commit the roadmap, then implement that stage (additive, audited,
  reversible) and log the audit verdict.

## 2026-07-08 — roadmap workflow landed; safe-first stage chosen

- **Workflow `wsx6mbbnv` done** (5 architects + synth + adversarial review) →
  [`tcb-holomega-roadmap.md`](./tcb-holomega-roadmap.md). Near-term ordering:
  **B-K1** (reflected Kind sort, base, zero TCB) → **B-K2** (higher-rank Ty ctors,
  base, zero TCB) → **B-K3** (KindOf/RankOf/RankLe CanonRules, 3 gated mints) →
  EG3a (`TermKind::Zero`) → EG3b (T/F defined, connectives→CoreLang) → DEFS-OUT
  sequent-reshape → close float-op gap → **EG5** (delete 5 literal leaves,
  IRREVERSIBLE, wasm32-adversarial-audit-gated) → residual defs/. Steps 1–4
  additive-first + independently mergeable; EG5 the single irreversible door.
- **Review verdicts:** (a) leaf-removal symbolic-prop wall = SOUND-PLAN near-term
  (zero new base method for the statically-shaped case; Dyn/heterogeneous case =
  EG4, deferred); EG5 must be one atomic commit (the `rules.rs:797`
  `tohol_unfolding_rules_are_exclusive` guard: co-admitting *Val reify + structural
  unfolding mints ⊢False) + wasm32 audit. (b) HOL-ω rank = SOUND-PLAN-as-gated /
  proof NEEDS-WORK (align rank formula to **Homeier's HOL-Omega** stratification;
  audit vs SelectAx/bool; `TyInst` must structurally bind the rank premise; B-K3
  KindOf must return None on ill-kinded, never a wrong kind). (c)
  defs-without-global-state = SOUND (Def-as-value, `Arc::ptr_eq` identity, fresh Arc
  per `define`, no global registry) but re-entrancy liveness NEEDS-WORK (the
  LazyLock incident class). (d) persisted RelEdge ≠ free Thm (needs re-execution or
  an admitted attestation axiom, else ⊢False). (e) shape-erased general matcher
  (Dyn, no derive(Eq)) = deferred-hard wall; shaped Inst/Match is contained.
- **Decision:** implement **B-K1 first** — zero-TCB inert base ops (no `Thm::new`,
  no CanonRule), the pattern already audited via `tyrep.rs`. Additive + trivially
  reversible. No irreversible/gated door touched.

## 2026-07-08 — B-K1 landed: reflected Kind sort (zero-TCB)

- **B-K1 done** (commit `c65b3f28`). New `crates/kernel/base/trusted/src/kind.rs`:
  `KStar<K>` (`()→K`, the kind ⋆) + `KArrow<K>` (`(K,K)→K`, function kind) as inert
  ops mirroring `tyrep.rs` (hand-written `Copy/Clone/Eq/Debug`, never derive). Helper
  `star::<K>()` = `App(KStar, Val(()))` (⋆ as a term; `()` isn't an `Expr`, so the
  arg is `Val(())`). Test `kind_sort_in_base_transports`.
- **Zero-TCB verified:** no `Thm::new`, no `CanonRule`, no `Rule` (the 3 grep hits
  in kind.rs are docstring mentions) ⇒ uninterpreted ⇒ inert ⇒ sound by vacuity;
  base manifest + 18 mint sites unchanged; core builds; clippy clean. Pattern
  pre-audited via `tyrep`, so no separate audit agent for an inert-op addition
  (proportionate: an op that can mint nothing can't be a forgery vector).

## 2026-07-08 — B-K2 landed: higher-rank HOL-ω binder syntax (zero-TCB)

- **B-K2 done.** Extended `tyrep.rs` with reflected DE-BRUIJN binder syntax:
  `TyBound<T>` (`u32→T`, de-Bruijn tyvar), `TyAll<T,K>` (`(K,u32,T)→T`, rank-N ∀ —
  the `u32` is the rank), `TyAbs<T,K>` (`(K,T)→T`, type-level λ). All inert (no
  `CanonRule`); **no reduction op in the base** (β = `TyBeta` lives in the middle),
  so the base stays operationally binder-free. Test
  `tyrep_binders_are_debruijn_and_transport` (well-formed terms; structural eq =
  α-equivalence since de-Bruijn; `cong_pair`/`cong_app` transport through binders).
- **Zero-TCB** (inert ops, same reasoning as B-K1). Rank *stratification* is NOT
  enforced here — that is the middle-side `TyInst` side-condition (needs B-K3's
  kind/rank `CanonRule`s + the Homeier-aligned consistency proof; see review
  must-fixes). A malformed/ill-ranked spine is inert, not unsound.
- **Note discovered:** the base has only `cong_pair` (2-tuple congruence); a 3-tuple
  arg (`TyAll`) can't be driven component-wise by `cong_pair` (only refl+cong_app on
  the whole tuple). Not a soundness issue — the middle nests or adds a helper. `TyAbs`
  (2-tuple) shows full component-wise congruence.
- **Next: B-K3** (KindOf/RankOf/RankLe as `CanonRule`s) — the FIRST stage with a real
  TCB delta (3 gated mints), so it gets a full adversarial audit; KindOf must return
  `None` on ill-kinded input, never a wrong kind (a wrong kind → false rank premise →
  defeats the `TyInst` gate).

## 2026-07-08 — checkpoint: B-K1+B-K2 merged to main; B-K3 teed up (needs design+audit)

- **State:** local `main` = `c9fff3e8` — parsing + float + JSON + relcalc Phase 0 +
  roadmap + **B-K1** (Kind sort) + **B-K2** (higher-rank binder syntax), all merged;
  worklog current. Pushes still blocked (hook allows only main + classifier blocks
  main) — maintainer pushes later.
- **Deliberate stop before B-K3.** B-K1/B-K2 were the clean zero-TCB autonomous
  wins (inert ops, pattern pre-audited via tyrep). **B-K3 crosses into real-TCB
  territory** (3 new admitted `CanonRule`s) and is the soundness-critical hinge —
  improvising it late in a long run would violate the "don't improvise the walls"
  discipline. Teed up for a deliberate, audited pass:
  - **Design to nail first:** the in-base demo type rep `Cdemo` (a flat encoding the
    CanonRule computes over — analogous to `TyRepDemo`/`Kdemo`, but a *whole* type
    term as one `Val<Cdemo>` leaf, since a `CanonRule` evals over a `Val` leaf, not
    an App-spine); how `KindOf` recurses over it; and how the flat demo relates to
    the B-K1/B-K2 App-spine syntax (bridge deferred to the `C = core::Type` wiring).
  - **The three rules:** `KindOf : Cdemo → KindC` (**MUST return `None` on
    ill-kinded input, NEVER a wrong kind** — a wrong kind ⇒ false rank premise ⇒
    defeats the `TyInst` gate); `RankOf : Cdemo → u32` with
    `rank(∀α:κ:r.τ) = max(r+1, rank(τ))` (`InstTFree` = the rank-0 case); `RankLe :
    (u32,u32) → bool`. All gated `canon` mints; +3 lines at `lib.rs:11-33`.
  - **Mandatory:** full adversarial audit (the KindOf totality/no-wrong-kind
    contract, like the arithmetic certs) BEFORE merge; and the higher-rank *middle*
    rules (`TyBeta`/`TyGen`/`TyInst`) must NOT enter `CORE_MANIFEST` until the rank
    stratification is proven against the FULL rule set incl. `SelectAx`/`bool`
    (Homeier-aligned) — the `rules.rs:812` `manifest_matches_golden` tripwire.
- **Then:** EG3a (`TermKind::Zero`) → EG3b (T/F defined, connectives→CoreLang) →
  DEFS-OUT sequent-reshape → close float-op gap → EG5 (irreversible, gated).

## 2026-07-08 — B-K3 landed + audited SOUND: kind/rank synthesis CanonRules

- **B-K3 done** (commits `1950f091` impl, `3621e689` overflow hardening). New
  `crates/kernel/base/trusted/src/kindcheck.rs`: flat de-Bruijn demo rep `TyC`/
  `KindC` + three `CanonRule`s — `KindOf` (standard simply-kinded synthesis; None on
  ill-kinded, never a wrong kind), `RankOf` (gated on well-kindedness;
  `rank(∀α:κ:r.τ)=max(r+1,rank τ)`, `saturating_add` so a `u32::MAX` rank never wraps
  down — the conservative direction), `RankLe` (decides `≤`). Tests
  `kindof_synthesises_and_refuses` (all ill-kinded shapes refuse via `Err(NoMatch)`)
  + `rankof_and_rankle`. TCB delta = 3 new `eval` functions; **no new mint site**
  (canon unchanged, 18 mint sites, base manifest untouched).
- **Adversarial audit verdict: SOUND to merge** (no HOLE, no must-fix). Verified:
  de-Bruijn `lookup` correct + push/pop balanced on all `?`-paths (no capture/
  off-by-one → no wrong `Some(kind)`); all `eval`s deterministic+pure (the property
  canon needs — a nondeterministic eval would be unsound like `execute` vs canon);
  gating on own `TypeId`; RankOf's `kind_of` gate ⇒ `rank_of` never hits its own None
  path; saturating over-approx only makes a future `rank≤r` check stricter. Scope
  honesty confirmed: computes/certifies but does NOT enforce stratification.
- **Robustness follow-up (non-blocking, recorded):** `kind_of`/`rank_of` are
  unbounded structural recursion — an adversarially deep `TyC` could stack-overflow
  `canon(KindOf,…)` (DoS, NOT a false theorem). Add a depth guard (returns None past
  a limit = conservative refusal, sound) before this eval sees untrusted network
  input. Deliberately NOT added now (avoids a premature magic constant + a
  completeness caveat on legit deep types while it's a demo). Recorded in the base
  SKELETONS.
- **Milestone:** B-K1 + B-K2 + B-K3 complete the near-term **HOL-ω base-constructor
  front** (roadmap Front B, stages 1–3): reflected Kind sort, higher-rank binder
  syntax, and the base kind/rank oracle. Next stages (EG3a `TermKind::Zero` → EG3b
  T/F-as-defs → DEFS-OUT → EG5) move into the **core** crate / leaf-removal, where
  EG3b removes a CoreLang primitive (maintainer-gated) and EG5 is the irreversible
  door.

## 2026-07-09 — end-to-end prototype chain (types → monads → Haskell surface → HOL data)

Maintainer: "keep going … finish a working prototype end-to-end … we can always roll
back" + "a general theory of monads instantiating theorems for list + option" + "work
towards our Haskell-like syntax … parse a subset of Haskell and write init/ in our
dialect … a trait to handle numeric literals etc. so different implementations lower
different subsets." Delivered four composing prototype layers (all merged to main):

- **HOL-ω type instantiation prototype** (`base/trusted/src/holomega_proto.rs`, commit
  `8cd4a6ec`, test-only/untrusted). Rank-stratified `∀`-instantiation driven by the
  B-K3 oracle: instantiate `∀(α:κ:r).τ` at σ ONLY when the base certifies
  `kindof(σ)=κ` ∧ `rankof(σ)≤r`. 5 tests incl. the **Girard-blocking** demo (rank-0 `∀`
  REJECTS a rank-1 polymorphic arg; a rank-1 binder admits it). Substitution is
  untrusted; trust = the 3 base certs. Trusted-CoreLang `TyInst` stays gated on the
  consistency proof.
- **General monad theory → list + option** (`init/src/init/monad.rs`, merged
  `c1568cb3`, zero-TCB). `monad_map_ret`: `{left-id law} ⊢ map f (ret a) = ret (f a)`
  (general, one hypothesis) INSTANTIATED + discharged to hyps-free `option_map_ret`
  and `list_map_ret` (list needed append-nil via `list_induct`). The "prove once,
  instantiate for free" payoff, genuine. (Single-carrier plain-HOL rendering; a
  two-type-param version wants HOL-ω type-operator vars — noted.)
- **`covalence-haskell` surface crate** (`crates/lang/haskell`, merged, zero-dep,
  kernel-agnostic). AST + hand-written recursive-descent parser (lambda/app/let/binops/
  literals/top-level defs) + the **`Lower` trait** — per-construct methods DEFAULTING to
  an "unsupported" error, so a backend lowers only its subset (the maintainer's ask).
  Demo backends `SExprLower`/`PeanoLower` (differ on numeric-literal lowering)/`NoLitLower`
  (proves subset-support). 15 tests.
- **HOL backend** (`crates/lang/haskell/src/hol.rs`, feature `hol`, merged). `HolLower`
  lowers the parsed Haskell → init's **carved `sexpr`** kernel Terms (untyped ⇒ no type
  inference) via the same `Lower` driver: `\x->x` ⇒ `(lambda x x)`, `compose f g x =
  f (g x)` ⇒ nested-lambda sexpr. 7 end-to-end tests. Default build stays kernel-
  agnostic (init is an optional dep). **Closes the loop: Haskell source → HOL data.**
- **Follow-ons (recorded in the haskell SKELETONS):** typed HOL-`Term` lowering with
  inference; lowering to actual `init/` definitions (the real "write init/ in the
  dialect" step); trusted-CoreLang `TyInst`/`TyGen`/`TyBeta` (gated on the Homeier
  consistency proof); EG3a→EG5 core leaf-removal.

## 2026-07-10 — ultracode: 3 parallel audited tracks merged to main (8e2e9f13)

Workflow `wijd7ts4t` (13 agents): three worktree-isolated tracks, each stage
adversarially audited (fix+re-audit loop) — **all SOUND**. Full joint-review doc:
[`tcb-review-2026-07.md`](./tcb-review-2026-07.md).
- **Track A (kernel):** EG3a (`TermKind::Zero` + transitional eval-tier `ZeroLitCert`
  bridge, dies at EG5) → EG3b (**T/F defined constants; `FalseElim` DELETED,
  coreManifest 26→25**; ⊢T at CoreLang; zero new axioms) → A3 (**5 CoreLang rules
  reshaped to `Prem<L>`**; `ZeroNeSucc` now ex-falso; connective builders out of core;
  coupling 37→29). **EG5 preflight = BLOCKED** (no structural target for SmallInt/f32/
  f64; float-lander gap; unary-numeral perf wall) → EG5 NOT executed; plan in
  `eg5-preflight.md`. Latent finding: the exclusivity guard is nat-only (extend to 5
  families before EG5).
- **Track B (haskell):** SExpr IR interchange pipeline (Haskell ⇒ S-expr ⇒ backend),
  **Nat literals = covalence Nat** (not u128), `Realize` trait at the SExpr boundary,
  HOL backend re-routed; third-party-text tests + init-dialect flagship. Also fixed a
  pre-existing RED deps gate on main (haskell purge-ratchet breach). Zero-TCB.
- **Track C (base):** `covalence_pure::api` facade + `CertificateAlgebra` trait (the
  algebra the future relations-base implements) + `covalence-tcb-db` SQLite TCB-dump
  PoC. Zero trusted-TCB delta. Notes: `base-api-surface.md`, `base-abstraction.md`.
- **Merge:** B/C haskell + docs/deps conflicts reconciled (took B's crate rewrite,
  regenerated deps deterministically). Full gate green: **193 test suites, 0 failures**,
  clippy clean, fmt clean, `deps:check` up to date. Note: the tcb-audit base jump
  (mintSites 18→24) measures ALREADY-LANDED rel.rs + B-K1..3 (earlier skipped `bun run
  deps`), not new trust.

## 2026-07-11 — EG5 unblocked + prep landed; S1 (bytes) honest-stop finding

Maintainer decisions unblock EG5: **binary `ToHolNat`** (log-sized, via `nat_binary.rs`)
kills the unary perf wall; **`SmallInt` = `toHOL` leaf** (`ToHolSmallInt`, no structural
rule → leaf-only → deletable; f32/f64 ride along). Recorded in `eg5-preflight.md`
(BLOCKED→UNBLOCKED-WITH-DECISIONS) + the review doc.
- **Prep merged (main 57ab9f48, additive, manifests byte-identical):** P1 exclusivity
  guard → per-family table (nat/int/bytes); P2 facade sweep (init literal-ctors 72→6).
- **S1 bytes swap = HONEST-STOP** (docs-only `baaf576a`, merged `cfe4f218`). Key
  finding: EG5's per-family swaps are **bigger than the preflight sketched** — each is
  all-or-nothing (guard forbids additive intermediate) and needs (1) the missing
  structural HOL theory completed (`bytesConsNat`/`bytesAt` are declaration-only;
  `Blob↔list u8` bridge + list-recursion lemmas absent), (2) the WHOLE cert family
  flipped to a structural RHS, (3) a new structural-injectivity audit obligation. Int
  (S2) is identical. This is the real remaining EG5 cost — a multi-stage per-family
  proof+cert effort, best run as a dedicated orchestrated push (ultracode) with the
  structural theories built first. NOT rushed; the tree stayed green, no TCB change.

## 2026-07-11 — cleanup/decouple/demoable push (4 tracks, all PASS, zero-TCB, main bf0cde66)

Workflow `wc3ue96f0`: 4 parallel tracks to a clear, decoupled, demoable state — each
build/test/scope-reviewed PASS, **all zero-TCB** (core/eval manifests byte-identical to
origin/main). 198 workspace suites green; web app builds.
- **A — backend decoupling:** new `covalence-hol-api` (crates/kernel/hol/api) — a
  consumer crate exposing `Hol` (promoted from init's inductive engine) + a NEW `Nat`
  trait (term builders + Peano lemmas by name), impl'd for `NativeHol` by delegation.
  Migration-proof test derives theorems entirely through `H: Hol + Nat` (no backend
  type named). Inventory: `scripts/backend-coupling.mjs` + `docs/deps/backend-coupling.json`
  (consumer TermKind::=13, Term::=59). Design note `notes/vibes/backend-decoupling.md`.
  Deferred (SKELETONS): no real external consumer migrated yet; Inductives/HolOmega/Int/
  List traits not built; Hol error type not associated.
- **B — Haskell frontend:** dialect extended (if/list/tuple/unit/comments/type-sig lines),
  `DesugarBackend`, an example-module library lowered to SExpr + (feat hol) kernel Terms.
  57 tests, both configs green.
- **C — web demo:** three new routes — `/deps` (dep-tree from graph.json/svg), `/tcb`
  (TCB-audit from manifests + tcb-audit.json), `/haskell` (pipeline + precomputed
  examples; live-WASM playground honest-stopped, recorded). Web build green.
- **D — navigation + docs:** `notes/design/` framework (TEMPLATE + README index),
  `notes/vibes/project-map.md` (crate groups + active threads), `k-framework-vision.md`
  (the new K north star: full K + all sublanguages, relate K-WASM to SpecTec),
  `relational-base-rewrite.md` STUB (signed-SQLite, maintainer to flesh out),
  `what-is-the-tcb.md`.

<!-- APPEND NEW ENTRIES BELOW -->

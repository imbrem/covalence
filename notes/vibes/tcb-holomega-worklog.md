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

<!-- APPEND NEW ENTRIES BELOW -->

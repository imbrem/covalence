+++
id = "N001I"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-19T00:00:00+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# ACL2 campaign — handoff / context dump (2026-07-17)

State dump at a token-budget wind-down, mid-campaign. Read together with
[`acl2-agent-guide.md`](./acl2-agent-guide.md) (module map, patterns, gotchas,
process), [`acl2-s7-s12-plan.md`](./acl2-s7-s12-plan.md) (stage plan),
[`acl2-fidelity.md`](./acl2-fidelity.md) (deviations ledger).

## Committed and done (branch `lisp-demo`)

- **S0–S6 + S5 (a–d): the ACL2 ladder through the full definitional-principle
  substrate.** Tip `1022c58f` "S5 COMPLETE". Every stage adversarially audited
  before commit. Highlights: soundness metatheorem + transport (S3, first
  transported theorem), structural induction (S6, app-assoc gate), full-ε₀
  well-foundedness (`ordinal.rs` `wf`/`wf_induct`), IND-ORD measured induction
  with app-assoc re-derived by measure (`gate_s5d.rs`, 95-clause env), the S5
  axiom pack (classical `cases` + ModelImplies arith rows),
  `transport_implies_open`, S11-lite book pipeline with honest tally +
  `#book`, certified ground defthms in the `/lisp` demo (`#lang acl2`).
- Web demo polish: fixed-layer hover popover (`232f5203` on origin/main).
- **origin/main is at `232f5203`; local lisp-demo is ahead — NOT pushed
  (standing directive: never push unless the user asks in that request).**

## In the tree at wind-down (uncommitted; from the stopped `acl2-s7-premise-api` workflow)

Workflow `wf_aaa27fbf-f5d` was STOPPED mid-phase-1 (token budget). Its script:
`.claude/projects/.../workflows/scripts/acl2-s7-premise-api-wf_aaa27fbf-f5d.js`
(resumable via `Workflow({scriptPath, resumeFromRunId: "wf_aaa27fbf-f5d"})` —
completed agents return cached; the two green phase-1 agents will cache-hit).

1. **S7 design — DONE** (`acl2-s7-design.md`): full definitional principle at
   skeleton precision (wf-recursion model theorem via the `recursion.rs`
   graph recipe with `wf_induct`; measured admission; mutual-recursion
   decision; gates + negative controls). Implementation NOT started.
2. **Abstract-sexpr API slice 1 — DONE, reported green** (per
   `abstract-sexpr-api.md` §4 "Slice 1"): trait in `crates/lib/sexp`
   (`abstract_sexpr.rs` + lib wiring), `crates/lang/lisp/src/carrier.rs` +
   `tests/carrier.rs` (impl + retarget demo), small `relation.rs`/
   `semantics.rs`/`lib.rs` touches, SKELETONS updated. Verify its tests before
   trusting (its agent finished; the workflow verify phase never ran).
3. **Premise-builder P0 — PARTIAL, agent killed mid-task.** Its own task
   breakdown: hilbert.rs `Script` + `KCache` + `derive_under_cached` + shared
   `s6_app_session` DONE; `simplify.rs` planner/emitter + FactCache + premise
   builders + driver IN PROGRESS (untracked file, state unknown); arith env
   rows (`with_arith_rules`, plus-zero-int), gate tests (app-assoc AUTO,
   len2-app, measured variant, negative controls), docs/SKELETONS NOT started.
   Binding design: `acl2-premise-builder.md` (P0 gate = app-assoc derived
   fully automatically, zero hand-built steps).
4. `gate_s5d.rs`/`ordinal.rs`/`mod.rs`/`carved.rs` small edits from these
   agents; `docs/deps/*` regenerated (dep graph gained the sexp→lisp edge).

## Next steps (the campaign queue, unchanged)

1. Finish premise-builder P0 (resume from the task breakdown above), then P1
   wiring (lang-side IndEngine; fixture books' app-assoc/len2-app flip to
   transported — pin new tallies).
2. S7 implementation per `acl2-s7-design.md` (crown: wf-recursion model thm).
3. S8 rationals ∥ S9 defchoose → S10 functional instantiation → S11 full books
   (real community book gate) → S12 guards. Cross-cutting: remaining API
   slices, ladder→metalogic promotion (see s7-s12 plan §consolidation).
4. Every stage: adversarial audit before commit; workflow scripts must treat
   DEAD audit/verify agents as failures (a fixed bug — keep the fix).

## Operational notes (hard-won, this session)

- A transient "Fable 5 requires usage credits" API error killed 4 subagents in
  one workflow; probe with a tiny agent before relaunching big workflows.
- The user's main checkout may sit on THEIR active branch (e.g.
  `wasm-spec-total-load`) — never merge/commit there; merge to `main` by
  checking `main` out in THIS worktree (no other worktree holds it). A
  `.git/hooks/pre-push` allows pushing only with `main` checked out.
- NEVER `git push` unprompted (memory: feedback-no-unprompted-push).
- `notes/plans/atoms.md`: maintainer's live file — never touch/commit
  (`git add -A -- ':!notes/plans/atoms.md'`).
- Full `cargo test -p covalence-init` ≈ 7 min (1029 tests); acl2 release
  filter ≈ 2 min (73+); lisp needs `--features hol`.

# ACL2 program — agent orientation guide

Read this first if you're working on the ACL2 tower. It compresses what five
workflow rounds (S0–S6, S5, books) learned. Companion docs:
[`acl2-full-plan.md`](./acl2-full-plan.md) (stages),
[`acl2-s7-s12-plan.md`](./acl2-s7-s12-plan.md) (what's next),
[`acl2-fidelity.md`](./acl2-fidelity.md) (assumptions/deviations),
per-stage designs `acl2-s0-s3-design.md` / `acl2-s4-s6-design.md` /
`acl2-s5-design.md` (each carries §-numbered *implementation reports* recording
what actually landed, including naming deviations — trust those over the design
body).

## Module map (all in `crates/kernel/hol/init/src/init/acl2/`)

| File | Contents |
|---|---|
| `carrier.rs` | S0: `acl2_carved()` = payload-parametric carve at `coprod int bytes`; `aint`/`asym`; injectivity/distinctness/induct/cases; paramorphic recursor |
| `prims.rs` | S1: `t`/recognizers/`aequal`/`aif`; `intval` seam + lifted arithmetic; completion laws; the 11-row `PrimRow` table; `<` seam (S5) |
| `term.rs` | S2: pseudo-term encoders (`sym/quote/app/mk_*`); pair-valued `ev` (eval × evlis); `subst`; **`subst_sema`** |
| `ladder.rs` | S3: reusable unary `derive_mixed` + `Premise{Side,Derivation}` + β-bridges — promotion to `metalogic/` flagged |
| `derivable.rs` | S3+S6: `Acl2Env` (AxiomRow/UserRow/PrimRow, `Discharge` enum), `ClauseKind`, `Derivable_ACL2`, membership constructors, `sound_pred`, `soundness()` by rule induction, `project_*`, `transport_equal[_open]`, IND + CongImpl |
| `defun.rs` | S4: `DefunSpec`/`admit_defun`, `model_image` single-source-of-truth, per-row discharge |
| `hilbert.rs` | S6: K/S/MP deduction compiler for in-object premise derivations |
| `ordinal.rs` | S5: `o-p`/`o<` paramorphisms + defining equations, `ord_fold` normalizer, Acc, nat↪int bridge consumers, `main_ord`/`graded_wf`/**`wf`**/**`wf_induct`** |
| `SKELETONS.md` | the open-work ledger — severe entries are the next stage's entry points |

Lang side: `crates/lang/lisp/src/acl2.rs` (dialect, `CertEngine` certificate
path for ground defthms), `src/book.rs` (+`reader::read_book`, `#book` in
`session.rs`) — the tally pipeline. Web: `/lisp` page, `#lang acl2`.

## Patterns that carried the program (reuse these)

- **Pair-valued paramorphism** (S2 `ev`, S5 `OLT`/`OP`): mutually-recursive or
  deeper-than-depth-1 recursion over the carrier dissolves into ONE recursor
  call at a product type; pointwise folding lemmas by `cases()` — no fuel, no
  `cv_exists`, no `fun_ext` induction.
- **Design-first at proof-skeleton precision.** The three crown proofs
  (`subst_sema`, IND discharge, `main_ord`) all closed essentially first-try
  because their case structures were designed to the individual `lem`-split
  before implementation. Budget the design agent; it repays.
- **Single-source-of-truth terms**: `model_image()` (defun) — the same Rust
  function generates both the model definition and the eval-dispatch image, so
  drift is a compile/kernel error, not an unsoundness.
- **Discharge enum, fail-safe**: env axioms carry their own justification
  (`Schema`/`ModelEq(Thm)`/`ModelHolds(Thm)`/`Hook`); anything unrecognized
  fails the soundness build — new clause kinds cannot silently skip discharge.
- **check() test style**: every gate test asserts `hyps().is_empty()` AND exact
  conclusion equality against an independently-built term. Negative controls
  alongside (wrong theorem/false goal/escape path must error, minting nothing).
- **Honesty ladder for hard proofs** (S5): pre-commit to graded fallbacks
  (below-ω → ω² → full ε₀) so a wall still lands a true theorem.

## Gotchas (each cost someone real time)

- `cargo test -p covalence-lisp` runs **0 tests** without `--features hol`.
- The **deps purge-ratchet** rejects new `Term::blob`/`TermKind::Blob` call
  sites: use the `covalence_hol_eval::mk_blob`/`as_blob` facade. Never bump the
  golden.
- **Per-instance recursor cache**: the carved recursor cache is a per-instance
  `OnceLock` (a process-global would serve the *wrong* recursor to a second
  carve). Preserve this if you touch `carved.rs`.
- **Products: use `fst_pair`/`snd_pair` only** — `delta_all` over-unfolds prod
  internals (the recorded init/prod gotcha).
- **Fold recursor images before `reduce`** (the `lisp.rs:301` trick) or the
  reduction diverges into the paramorphism.
- Binder-hint names in `induct` cases (`"b"/"h"/"t"`) are **load-bearing**
  (instantiated by `.inst`).
- The metalogic engine for ACL2 is the **unary** `RuleSet`
  (`metalogic/mod.rs:244/278/329`), not `binary::RuleSet2` — the full-plan's
  original claim was wrong, corrected in the S0–S3 design.
- Pre-commit hook runs `cargo fmt --all` + deps regen — do not commit while
  other agents have in-flight edits.
- `notes/plans/atoms.md` is the maintainer's live file: never touch, never
  commit (`git add -A -- ':!notes/plans/atoms.md'`).
- Workflow scripts: a **dead** audit/verify agent (null result) must be treated
  as a failure — `if (audit && !audit.ok)` alone silently passes a crashed
  auditor (the S5-round bug).

## Process (mandatory for theory stages)

1. Design note (or § extension) with gates + risk register + out-of-scope list.
2. Implement; walls become precise SKELETONS entries, deviations go in the
   design note's implementation-report section.
3. Full `cargo test -p covalence-init` (~900 tests) + `-p covalence-lisp
   --features hol` + `cargo check --workspace` + fmt + `bun run deps:check`.
4. **Adversarial audit before commit** — a separate agent with a refutation
   brief (postulate hunt, TCB diff empty, statements-match-names, certificate
   load-bearing, tally honesty). Nothing merges on the implementer's word.
5. Commit per stage (`git add -A -- ':!notes/plans/atoms.md'`); commit message
   names the gate that passed.

## Where ACL2 knowledge lives

The logic we're modeling: quantifier-free FOL with equality over a fixed
universe; theorems = terms evaluating non-nil under all valuations; induction up
to ε₀; definitional principle via measures into ordinals; defchoose/encapsulate
as conservative extensions. Primary sources used so far: the ACL2 manual's
`o-p`/`o<`/completion-axiom definitions (checked against `ordinal.rs`/`prims.rs`
during audits) and the community-books event grammar (`book.rs` design). The
HOL4 "ACL2 in HOL" project (Gordon–Hunt–Kaufmann–Reynolds) is the precedent for
the model-theoretic shape; our difference is the reified, rule-inducted
`Derivable_ACL2` (certificates as first-class objects). For fidelity questions
consult `acl2-fidelity.md` first — every known deviation is on that list.

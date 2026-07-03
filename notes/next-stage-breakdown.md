# Next-stage breakdown (companion to REFACTOR.md)

**Status:** working breakdown (2026-07) of [`../REFACTOR.md`](../REFACTOR.md),
to start once `pure-impl-1` lands in `main`. REFACTOR.md is the intent (the
user's voice); this is the execution plan — sequencing, dependencies, open
decisions.

## The dependency structure

The four workstreams are not independent:

- **Docs reorg (A)** is cheap, self-contained, and *should go first* — the crate
  re-org rewrites crate-map/SKELETONS anyway, so get the target shape in place
  before generating new content into it.
- **Tooling (B)** makes the crate re-org survivable: shared build caches across
  worktrees turn each `git mv` + rename iteration from minutes to seconds, and
  reliable CI is the safety net the migration leans on. Do the *foundations*
  before (C); the long tail (LSP, dev-containers) can run alongside.
- **Crate hierarchy (C)** is the churn-heavy one — every crate rename touches
  every consumer. It wants B's foundations, and it *creates the homes* (kernel/
  base/wasm, kernel/hol/wasm) that D fills.
- **WASM roadmap (D)** is the actual product milestone. Its kernel-theory side
  (evaluation-as-a-language, the `Evaluate` seam, `CanonRule`) continues the
  closed-world kernel roadmap and can progress *now*; its packaging side
  (shared runtime API, async) wants C's layout.

Suggested order: **A → B(foundations) → C (group-by-group) → D**, with D's
theory side and B's long tail running concurrently.

## Phase A — notes/docs/skills split (cheap, first)

1. `notes/vibes/` ← everything currently in `notes/` (the AI-generated,
   cross-referenced plans). One `git mv` + link fixups.
2. `notes/` ← new structured tree (`ideas/`, `experiments/`, …) — *aspirational*
   (what we want; may drift).
3. `docs/` ← *true* documentation only, aggressively synced (start tiny: build,
   crate map, kernel TCB inventory — things CI could even check).
4. Refresh `README.md`, `CLAUDE.md` (thin), skills to match; simplify SKELETONS
   *organizationally* now (severe-first stays), and note the future
   **skeleton database** (parse `SKELETON:`-style comments into a queryable
   index — future work, not now).

## Phase B — tooling foundations

1. **Build system decision** (the big one — needs a spike, not a doc):
   `buck2` as the eventual delegate under `bun run build:*`, with cog
   compatibility as a long-term dogfood target. *Interim option to evaluate
   honestly:* cargo + `sccache`/shared `CARGO_TARGET_DIR` per-machine gets the
   worktree-cache win this week; buck2 is a real migration (every crate gets a
   BUCK file, toolchains, wasm rules). Recommend: spike buck2 on `lib/`-tier
   crates only; adopt the cheap shared-cache interim immediately.
2. **Artifact discipline**: every `bun run` task checks its inputs exist (or
   fails with a clear error); WASM artifacts get one standard import/share path.
3. **CI reliability** before the re-org starts (it's the migration's referee).
4. **Dev-containers** (agents + "install covalence and play"), and the
   CI-uses-the-devcontainer + flake question — investigate as one item.
5. **LSP revival**: separate process speaking to a covalence server (or running
   one in-process like the client/REPL); targets the covalence language +
   `.wasm`/`.wat`/`.watsup`. Can start any time after A; grows with `lang/`.

## Phase C — crate hierarchy (incremental, group-by-group)

Target shape (REFACTOR.md §Organization): `lib/` (core, proto, data, wasm, sat,
smt, crypto, db, git, fuse) · `proof/` (hol, metamath, lean, alethe) · `store/` ·
`kernel/` (base/{trusted,derive,eval,wasm,cap,db,fed}, hol/{logic,script,init,
eval,metamath,spectec,wasm}) · `lang/` · `server/` · `vcs/` · `app/` (repl, cog,
fuse) · `ffi/` (python, later js). Naming `covalence-group-…-thing`, catchall
`lib`/`core` segments elided; group-level cycles allowed, crate DAG strict.

Migration discipline:
- **One pilot group first** (`lib/` — leaf wrappers, least coupled) to settle
  the on-disk pattern (nested dirs + explicit workspace members — the
  `covalence-pure/trusted` nesting is the precedent), the re-export "group
  crate" idiom, and the rename mechanics. Then a mechanical per-group cadence:
  `git mv` + rename + sed imports + green CI + commit, one group per PR-sized
  change.
- Order: `lib/` → `proof/` → `store/` → `kernel/` → `server/`+`vcs/` → `app/`
  → `ffi/`. (`kernel/` is where our live closed-world work sits — by then the
  pattern is boring.)
- Note `kernel/base` = today's `covalence-pure` (its planned feature crates —
  eval, wasm, cap, fed — are exactly the base-layer languages already sketched
  in the closed-world design); `kernel/hol` = today's `covalence-core`;
  `kernel/hol/init` = a *smaller* `covalence-init` (much of today's init
  redistributes).

Open placement questions to settle during the pilot (flagged in REFACTOR.md):
sexp/parse placement in `data/`; `db/` fused into `data/`?; is `proof/` part of
`lib/`?; `extensions/` naming (one VSCode ext); the fixture-dir name for
opentheory/spectec/tests; `assets/` vs `data/` split; `packages/` for the
JS+Svelte library.

## Phase D — WASM roadmap (the milestone)

1. **WASM acceleration** — kernel-theory side: the base-layer `wasm/` language
   ("facts about what WASM modules evaluate to") + `kernel/hol/wasm` built over
   `eval/` (ideally `logic/` only). Continues the closed-world kernel plan (the
   `Evaluate` seam is the hook).
2. **Shared high-level runtime API** — one API over browser / native / VSCode
   execution (builds on covalence-wasm + web-kernel decisions).
3. **Async tasks** — `spawn_blocking`-based first (and kept), WASM 3.0 async
   later; ties into the script layer's async direction.
4. **The covalence library artifact** — covalence+Rust compiled to a `.wasm`
   importing the covalence WIT; the surface language compiling to WASM is the
   long-term goal the build system (B) must anticipate.

## Immediate next actions (once merged to main)

1. Phase A wholesale (one or two sittings).
2. B1 interim cache + B3 CI reliability; start the buck2 spike.
3. C pilot on `lib/`.
4. D1 theory work continues in-kernel regardless (closed-world Stage 1+).

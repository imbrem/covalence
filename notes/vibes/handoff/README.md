# Handoff docs — per-task current status (AI-generated)

Consolidated, pick-up-here status for each active workstream, as of main @ 4d3337a5
(2026-07). These are the "where things are / what's next" snapshots; the full
plan is [`../pure-hol-and-build-plan.md`](../pure-hol-and-build-plan.md), the
design corpus is [`../`](../README.md).

| Task | Doc | One-line status |
|---|---|---|
| **defs/ out of core** (PRIORITY) | [`defs-out-of-core.md`](./defs-out-of-core.md) | THE plan: shrink the TCB by moving the `defs/` catalogue out of `kernel/hol/core` → `kernel/hol/eval`. The literal-path foundations serve this. |
| toHOL purge | [`tohol-purge.md`](./tohol-purge.md) | S0–S9 + fallibility DONE + merged; S10/S11 reframed under the defs-out plan. |
| f32/f64 + ball arithmetic | [`float-ball.md`](./float-ball.md) | F0/F1 done+merged+audited; F2a facade done; F2b+ paused behind the defs-out priority. |

Authorship: AI-generated status/plan docs (vibes tier). The kernel TCB is
`crates/kernel/base/trusted` + `crates/kernel/hol/core`.

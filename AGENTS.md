# Agent guide

Read [`CLAUDE.md`](./CLAUDE.md) for repository invariants, build commands,
documentation policy, and trusted-kernel rules. Read the applicable skill before
working in a subsystem.

## Selecting work

Open work is authored beside code with stable markers:

```rust
// TODO(cov:area.stable-id, major): Concise acceptance-oriented description.
```

Use:

```sh
bun run todos -- --list
bun run todos -- --list --severity severe
bun run todos -- --list --crate covalence-init
bun run todos -- --list --search "structural sigma"
```

After adding, moving, changing, or completing a marker, run `bun run todos`.
Never recreate `SKELETONS.md`. The generated truth is
`docs/todos/todos.json`; the query cache is
`target/covalence-todos.sqlite`.

For portfolio context and dependencies, read
[`notes/vibes/plans/workstreams-and-state-report.md`](./notes/vibes/plans/workstreams-and-state-report.md).
Claim one workstream/task boundary, keep cross-stream dependencies explicit, and
do not duplicate TODOs in multiple crates.

## Handoff

Report:

- stable TODO IDs addressed or introduced;
- files changed;
- tests and benchmarks run;
- TCB/dependency changes;
- remaining blockers and their IDs.

Trusted-code edits require `bun run deps` and a review of the generated TCB
delta. Before handoff, run at least `bun run todos:check`,
`bun run deps:check`, and the narrowest relevant tests.

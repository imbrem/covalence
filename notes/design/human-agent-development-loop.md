# Human–agent mathematical development loop

- **Status:** Draft
- **Owner:** maintainer
- **Last touched:** 2026-07-18

## Goal

The maintainer should be able to contribute primarily by writing mathematical
intent: theorem statements, examples, high-level scripts, laws, pseudocode, and
API critiques. Agents turn that intent into implementation plumbing, but the
result must come back as a small, inspectable mathematical change.

This is not a “submit theorem, receive proof” queue. Humans and agents build the
theory, representations, tests, explanations, and proof vocabulary together.
The project should progressively dogfood its own language and module system.

## Unit of work

Every API workstream should start with a **dogfood script**:

1. representative declarations and theorem statements;
2. idealized high-level pseudocode, even when it does not compile yet;
3. two or more intended backends/interpretations;
4. observable laws and expected proof ergonomics;
5. benchmark fixtures and success metrics.

For example, an inductive slice begins with something like:

```haskell
data List a = Nil | Cons a (List a)

map_id      :: Theorem (map id xs = xs)
map_compose :: Theorem (map (f . g) xs = map f (map g xs))

listChurchIso :: Iso (List a) (ChurchList a)
```

The human reviews this surface before agents build the Rust traits, backend
adapters, theorem derivations, and conformance harness. During migration the
script may be checked-in pseudocode with expected diagnostics; eventually it
becomes executable Covalence module code.

## Workstream lifecycle

```text
mathematical brief
      ↓
dogfood script + theorem statements
      ↓
API proposal and dependency DAG
      ↓
isolated branch/worktree implementation
      ↓
conformance tests + benchmark + generated audits
      ↓
local review / draft PR
      ↓
merge and update the Covalence map
```

Each workstream has one branch and worktree. Generated global artifacts are
regenerated only in the integration branch, avoiding cross-agent races.

## Review packet

A change is reviewable when it includes:

- the mathematical intent and high-level example;
- the public API diff, preferably with generated rustdoc;
- backend/conformance evidence;
- dependency graph delta;
- TODO delta from the branch base;
- TCB/mint-site delta;
- benchmark delta where relevant;
- screenshots or executable demos for user-facing behavior;
- an explicit list of shortcuts and follow-up TODO IDs.

The maintainer should be able to review the dogfood script and audit summary
first, then descend into implementation only where useful.

## Local-first, GitHub-compatible workflow

Use local Git worktrees as the execution substrate and GitHub draft pull
requests as the temporary review UI. A PR is a transport and review artifact,
not the source of truth: all intent, audit output, and measurements live in the
repository and remain usable offline.

This gives useful review mechanics now—stacked commits, inline comments,
checks, rendered Markdown, and branch comparison—while providing concrete
requirements for a future `cov cog review` experience.

Avoid one PR per tiny agent action. Prefer one workstream PR with small,
semantically named commits:

```text
spec: add dogfood script and laws
api: introduce capability vocabulary
backend: adapt native implementation
proof: add conformance and isomorphism laws
audit: regenerate maps and metrics
```

## The Covalence map

The map should combine stable and live layers:

1. **Architecture:** crates/packages and allowed dependency edges.
2. **Mathematics:** logic APIs, theory APIs, interpretations, backends, and
   proved relationships/isomorphisms.
3. **Work:** TODO/project DAG with owners, status, and acceptance conditions.
4. **Execution:** active worktrees/branches/agents, checks, commits, and PRs.
5. **Evidence:** demos, benchmark series, TCB audit, and proof coverage.

The current dependency graph and TODO database already supply layers 1 and 3.
Git worktrees/branches supply the local part of layer 4. The next map prototype
should emit one JSON graph and several filtered Mermaid/DOT views rather than
building an unrelated dashboard database.

Longer term, `cov cog` should content-address workflow events and commits, and
the web/VSCode clients should render the same graph. GitHub synchronization
then becomes one backend for reviews rather than the model itself.

## Immediate dogfood exercises

- **Inductives:** list/tree declaration, fold laws, Church/native isomorphism.
- **Naturals:** successor and binary backends, addition preservation, round
  trips, SMT term-size benchmark.
- **Relations:** paths as relation composition, reflexive-transitive closure,
  functional relations as arrows, and checked category/allegory laws.
- **Graphs:** DOT bytes to graph interpretation, topological-order certificate,
  reachability path, and weighted shortest-path optimality certificate.
- **Lisp:** syntax over the inductive API, evaluator relation, and two
  representations connected by an interpretation theorem.


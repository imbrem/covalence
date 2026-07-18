# <Title> — design doc

<!--
Copy this file to notes/design/<slug>.md and fill it in. Keep it short: a
design doc is a decision record, not a manual. Delete the guidance comments as
you go. Once a doc is accepted and the work lands, either fold its durable
content into docs/ (maintainer-authored) or mark it Superseded and link the
successor — don't let accepted docs rot in place.

Authorship: agents may draft/iterate design docs here (this is the notes/design/
scaffolding area). The maintainer owns which docs graduate to docs/.
-->

- **Status:** Draft | In review | Accepted | Superseded | Parked
  <!-- see notes/design/README.md for what each status means -->
- **Owner:** <who is driving this>
- **Last touched:** <YYYY-MM-DD>
- **Related:** <links to notes/vibes/*, TODO IDs, crates, other design docs>

## Context / problem

What is the situation today, and what hurts? Ground it in the code: point at the
crates, files, and existing scaffolding that this touches. State the problem
sharply enough that the goals below are obviously the right ones.

## Goals

- What must be true when this is done. Testable where possible.

## Non-goals

- What this explicitly does **not** try to do (so reviewers don't expand scope).
  Cross-link the doc that *does* own each deferred concern.

## Proposal

The actual design. Prefer concrete types/signatures/schemas over prose where the
shape is load-bearing. Say what changes, what stays, and — critically for this
repo — **whether the TCB moves** (which manifests / admitted rules / mint sites).
If it touches the TCB, say so loudly and link `notes/vibes/kernel/tcb/what-is-the-tcb.md`.

## Alternatives considered

- **<alternative>** — why not (or why later).

## Open questions

- Unresolved decisions, ordered by how much they block. This is the section the
  maintainer and agents iterate on turn by turn.

## Status / next steps

Where it stands and the immediate next action. When work is deferred, record a
source-local `TODO(cov:...)` marker and link its stable ID here rather than
leaving prose TODOs.

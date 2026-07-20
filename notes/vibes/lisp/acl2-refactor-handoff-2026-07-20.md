+++
id = "N0052"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:codex"
at = "2026-07-20T00:00:00+01:00"
source = "acl2-refactor-handoff"
agent = "codex"
harness = "codex"
+++

# ACL2 refactor handoff — 2026-07-20

## Synchronization baseline

Branch `parser-primitives` was synchronized with local `main` at merge commit
`5e33bfdc`. The completed checkpoint immediately before the work described
below is `2a6dfc9c` (`feat(acl2): prove universal append execution`). It added
a checked universal reachability theorem for relational APPEND and reusable
`Reduces` congruence/retargeting lemmas.

The branch already contains:

- pinned upstream corpus progress and exact-manifest gates;
- the strict source-green `std/lists/acl2-count.lisp` island (5/5 exports);
- logical-green `std/basic/{nfix,ifix}` fixer islands;
- the checked APPEND theorem frontier and law pack;
- linked book/world import with structured blockers;
- pointwise host `MayEval` transports into relational and equational HOL; and
- generic admission ordering that requires existence and uniqueness before
  totalization.

## Important semantic finding

The current first-order relation has `Step, Reduces : tau -> tau -> bool`,
where `tau` is also the exhaustive ACL2 object datatype. Operator applications
such as `rel-append x y` and terminal ACL2 values therefore inhabit the same
HOL carrier.

Host `LispRel::is_value` distinguishes Rust term syntax, but that distinction
cannot be internalized as a sound predicate on `tau`: atom/nil/cons exhaust
the datatype extensionally, including the denotation of operator terms.
Consequently raw universal endpoint uniqueness is false because `Reduces` is
reflexive: both the initial operator term and its computed result are reachable.

The theorem currently returned by `replay_acl2_append_existence` is therefore
best described as universal checked **reachability**, not the admission API's
full `MayEval` existence theorem. Do not use it alone to totalize a definition.
A whole-Lisp solution needs reified configurations with an explicit terminal
`Value(tau)` constructor, or an equivalent separation of expression/config and
value roles.

## In-flight bounded seam

The work checkpointed with this handoff introduces a sound smaller boundary using
the existing generic inductive recursion graph:

- `acl2_append_eval_prop(environment, x, y, value)` constructs a reified
  APPEND big-step graph proposition;
- `replay_acl2_append_graph_adequacy(environment)` obtains closed totality and
  determinacy theorems from generic `graph_total` and `graph_det`; and
- `reified_append_evaluation_exists_and_is_unique` is the initial smoke test.

The graph fixes `y` as a parameter and treats `x` as the recursive input and
the graph word as the explicit result. Its carrier cases are:

```text
atom payload  |-> y
nil           |-> y
cons h t      |-> cons h (eval t)
```

This compiles (`RUSTC_WRAPPER= cargo check -p covalence-lisp --features hol`)
but its new test was intentionally not run at handoff time. The API is
APPEND-specific on purpose; after the refactor, prefer extracting a generic
admitted-definition evaluation graph only if the resulting interface is
independently reusable.

## Recommended continuation after the refactor

1. Run the new `reified_append_evaluation_exists_and_is_unique` test and
   inspect the exact quantified theorem shapes, not merely hypothesis counts.
2. Prove graph/model agreement by rule induction:
   `AppendEval_y x r -> r = APPEND-model x y`.
3. Derive pairwise graph uniqueness from two model-agreement instances, or
   retain the stronger generic `graph_det` theorem if its shape is preferable.
4. Add a checked pointwise bridge from concrete APPEND `MayEval` evidence to
   `AppendEval`; do not claim unrestricted `Reduces` uniqueness.
5. Decide whether `ExecutionAdequacyReplay` should consume this specialized
   definition graph or wait for reified `CoreExpr`/machine configurations.
6. Rerun the focused ACL2, relation, fixer, ACL2-COUNT, and APPEND corpus gates,
   then `bun run todos:check` and `RUSTC_WRAPPER= bun run deps:check`.

The stable remaining marker is `cov:lisp.acl2.admission-layer`. Its wording
should be revisited after the refactor so it distinguishes raw reachability,
definition-graph adequacy, and whole-language `MayEval` adequacy.

## Trust and generated state

No trusted kernel rule or external dependency was added by the in-flight
graph seam. It composes existing checked inductive totality/determinacy proofs.
The last full audit before this seam reported unsafe=0, mint-sites=24,
CoreLang/CoreEval admitted rules=25/17, with no TCB dependency expansion.

Generated map/dependency/TODO artifacts are intentionally left modified and
must not be included in the source-only checkpoint:

- `apps/covalence-map/static/covalence-map.json`
- `docs/deps/covalence-map.json`
- `docs/deps/graph.{dot,json,mmd,svg}`
- `docs/todos/todos.json`

Two older unrelated generated-artifact stashes remain; do not drop them.

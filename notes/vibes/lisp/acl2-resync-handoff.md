+++
id = "N0043"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-19T00:00:00+01:00"
source = "resync-handoff"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# ACL2 resync handoff

This branch is the continuing ACL2 import and x86 books workstream. It is
periodically merged into `main`, tested there, and then resynchronized with
`main` so development can continue without maintaining a long-lived fork of
the surrounding APIs.

## Relevant changes from main

The reusable API stack has moved toward narrow, representation-independent
capability crates:

- `covalence-logic-api` owns logic, relation, Nat, Bytes, and Bits vocabulary.
- `covalence-inductive` owns records, variants, polynomial families, least and
  greatest fixpoint capabilities, structural family actions, and law bundles.
- `covalence-sexpr-api` and `covalence-lisp` are the intended reusable
  S-expression and Lisp layers.
- The parsing crates separate syntax, bounded host evaluation, untrusted
  witnesses, and proof-producing replay.
- JSON is an example of the target layering: an abstract value API, a reference
  host backend, an inductive-family backend, parsing, and separately tracked
  proof-bearing HOL realizations.

ACL2 should follow the same shape:

```text
text/bytes parsing
  -> abstract S-expression and Lisp APIs
  -> ACL2 events, world, books, packages, and rule capabilities
  -> host importer/search
  -> NativeHol replay and checked theorem production
  -> x86 books as downstream corpus and benchmark
```

The current implementation still crosses some of these boundaries directly.
That is accepted migration debt, not the desired final dependency structure.
Refactor it incrementally behind compatibility adapters rather than combining
the resync with a wholesale rewrite.

## Collaboration rules

- Work in the `parser-primitives` worktree and commit source-only checkpoints.
- Merge `main` at natural resync points before allowing the branch to drift.
- Keep generated dependency, TODO, and map artifacts out of intermediate
  commits; regenerate them at the integration boundary.
- Author open work beside the responsible code with stable
  `TODO(cov:..., severity)` markers.
- Treat host parsing, search, induction discovery, and book analysis as
  untrusted. Only checked replay may produce authoritative kernel theorems.
- Keep ACL2-specific concepts out of the generic Lisp API unless they are
  justified independently as reusable Lisp capabilities.
- Avoid unrelated edits in the SpecTec/WASM workstream.
- In each handoff report tests, benchmark measurements, TODO changes,
  dependency changes, and the TCB delta.

## Near-term extraction path

1. Stabilize the ACL2 world/event and book-loading behavior represented by the
   current tests.
2. Extract ACL2-facing traits for world queries, event admission, packages,
   rule classes, modes, and proof results.
3. Adapt the existing concrete importer to those traits without changing its
   observable behavior.
4. Put NativeHol theorem replay behind a distinct backend capability.
5. Make the x86 books corpus a downstream compatibility and performance
   benchmark rather than part of the generic API contract.

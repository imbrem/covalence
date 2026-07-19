+++
id = "N0046"
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

# SpecTec/WASM resync handoff

This worktree owns the SpecTec-to-Covalence/WASM semantics vertical slice. At
this resync its combined relation has grown from 2,216 to 3,766 clauses while
the explicitly censused opaque premises have fallen from 321 to 7. Preserve
that coverage and honesty ratchet while adapting to the reusable APIs now on
`main`.

## Relevant changes from main

- Parsing is now split into neutral grammar syntax, policy-explicit parser
  capabilities, bounded host evaluators, untrusted witnesses, and separately
  checked HOL replay. Regex, lexer, CFG, parser-generator, and PEG layers have
  concrete crates.
- `covalence-inductive` now exposes records, variants, polynomial datatype
  families, nested least/greatest fixpoint vocabulary, structural family
  actions, law bundles, and higher-kinded combinators.
- Logic-level Nat, Bytes, Bits, text, relations, and computation-model APIs
  have representation-independent capability seams.
- JSON demonstrates the desired stacking pattern: abstract API, reference
  backend, inductive-family backend, parser/PER layer, and separate
  proof-bearing NativeHol realization.
- Trusted-code accounting remains generated and mandatory. Host parsing,
  indexing, monomorphisation, coverage analysis, and lowering are never
  theorem authority merely because they are deterministic.

Do not mechanically rewrite the mature SpecTec lowering onto every new API.
Extract or adopt a shared primitive only when it preserves the current
coverage, clause identity/order contracts, and checked theorem endpoints.

## Target architecture

```text
SpecTec source / official AST
        |
        v
indexed, provenance-preserving SpecTec API
        |
        +----> grammar API ----> bytes/parser witnesses ----> HOL replay
        |
        +----> syntax/type families via inductive capabilities
        |
        +----> rules/Dec/evaluator relations
                           |
                           v
                 checked NativeHol relation facts
                           |
                           v
             WASM syntax, typing, and execution APIs
```

SpecTec is one semantics frontend for the first-class WASM API, not the WASM
API itself. Keep syntax, typing, execution, parsing, and representation
morphisms separable so later K-WASM and operational/denotational backends can
state comparison theorems against the same abstract objects.

## Collaboration rules

- Work only in `spectec-improvements`; commit source-only checkpoints.
- Keep generated map, TODO, and dependency artifacts out of intermediate
  commits and regenerate them at integration boundaries.
- Preserve stable source-local TODO IDs and the exact coverage census.
- Never improve a score by skipping, coarsening, erasing sorts, or silently
  treating a premise as true.
- Separate untrusted indexing/lowering/search from proof-producing replay.
- Avoid new trusted rules or theorem mint sites. Stop and report any proposed
  TCB expansion before implementing it.
- Prefer focused tests and coverage ratchets during development. Run the
  broadest expensive combined-set tests at natural checkpoints.
- Report commits, test/coverage results, TODO changes, dependency changes,
  TCB delta, remaining opaque premises, and next blockers.

## Next milestone

Drive the current nearly-total lowering into a demonstrable WASM semantics
slice:

1. Preserve the 3,766-clause combined-set load and seven-premise opacity bound.
2. Eliminate or precisely classify the remaining ordered/Else residue without
   unsound complement assumptions.
3. Finish the integer builtin frontier already supported by exact numeric
   primitives; keep the remaining float frontier explicit.
4. Expose a narrow first-class WASM syntax/typing/execution facade that does
   not mention SpecTec implementation types.
5. Select a small official WASM program family and derive checked typing and
   execution facts through the complete path.
6. Record which objects and facts would be shared by a later K-WASM
   realization, but do not block this milestone on K.

The milestone is complete when the official SpecTec source can load, the
selected WASM examples produce hypothesis-free checked relation facts, the
coverage/opacity ratchets do not regress, focused tests pass, and the TCB mint
count remains unchanged.


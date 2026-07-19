+++
id = "N0047"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:codex"
at = "2026-07-19T00:00:00+01:00"
source = "native"
agent = "codex"
harness = "codex"
+++

# First-class WebAssembly semantics facade

This note records the backend-neutral boundary introduced by the first
demonstrable WebAssembly slice.  It is deliberately smaller than either the
SpecTec model or a future K-WASM configuration.  The boundary names
WebAssembly objects and relations; it does not make one frontend's syntax tree
the interchange format for another.

## Shared objects

The public facade should grow around these concepts:

- numeric and value types;
- instructions and straight-line programs;
- exact instruction stack effects;
- validation contexts;
- machine states and execution configurations;
- stable identities for typing, one-step, and multi-step relations;
- hypothesis-free checked typing and execution facts;
- source provenance for normative rules.

The initial Rust vocabulary lives in `covalence_hol_api::wasm`.  Unsupported
instructions and states are refused rather than represented by an opaque
catch-all.  Extending the vocabulary therefore makes coverage changes visible
in types and tests.

## Backend contract

`WasmTyping` and `WasmExecution` are the narrow capability traits.  A backend
accepts the neutral objects above and returns checked facts whose neutral
statements identify exactly what was proved.  The current native adapter owns
the SpecTec-derived clause environment privately.  A future K adapter should
own K cells, rewrites, and encodings privately while implementing the same
capabilities.

Backend comparison should relate each private encoding to the same neutral
statement, not translate SpecTec AST nodes into K terms.  Useful future
correspondence objects are:

1. a parser-to-neutral-syntax correspondence;
2. a neutral-syntax-to-backend encoding relation;
3. typing preservation for each backend encoding;
4. one-step and finite-trace simulation over neutral configurations;
5. agreement of observable terminal values and traps.

These are future theorem families, not assumptions of the current facade.

## Proof authority

Parsing, indexing, monomorphisation, coverage analysis, slicing, lowering,
search, and source attribution remain untrusted.  The current adapter returns
only hypothesis-free theorems produced by NativeHol replay.  Its zero-opaque
slice is transported into the full combined rule set through checked
clause-set inclusion.

The facade adds no trusted rule and no theorem mint site.  A K frontend must
meet the same boundary: host execution can select or propose a derivation, but
only replay in the checked metalogic establishes theorem authority.

## Current milestone and deliberate gaps

The first slice covers `nop`, `i32.const`, `i32.add`, and `drop`, including
exact stack effects and concrete finite executions.  The official-rule witness
layer records pinned SpecTec source identities and official WebAssembly
specification sections for the rules used by the examples.

This milestone does not yet claim:

- complete WebAssembly syntax;
- composed whole-program validation judgments;
- stores, frames, calls, control flow, memory, references, SIMD, or GC in the
  neutral configuration vocabulary;
- a K-WASM dependency or K-specific public type;
- resolution of the explicitly censused ordered/`Else` premises;
- approximation of the remaining float, relaxed, or representation builtins.

Those gaps should be closed by extending the neutral objects and capability
traits only when a checked backend path exists.

The immediate blocker to a composed `Instrs_ok` fact is narrower than the
facade: lowering currently leaves the non-call `(SET t)*` map in
`Instrs_ok/seq` as a raw iteration spine.  At zero locals the premise asks for
`with_locals(C, [], iter.list[t](SET t, []), C)`, while the exact base graph
proves `with_locals(C, [], [], C)`.  Exact relational evaluation of that map is
required before even the non-empty `nop` program can be typed as a sequence;
stack framing and subtyping for the addition example come after it.

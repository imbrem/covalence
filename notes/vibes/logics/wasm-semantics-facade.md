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

The facade now represents all four scalar numeric values without host
floating-point interpretation and checks the complete scalar numeric
instruction-typing vocabulary: constants, tests, comparisons, unary and
binary operators, conversions, explicit numeric `select`, `nop`, and `drop`.
Operator/type mismatches are rejected before replay. Floating constants retain
their raw IEEE payload, including signed zero and NaN payloads. Concrete
execution remains the narrower checked `nop`, `i32.const; drop`, and
`i32.const; i32.const; i32.add; drop` family.

The official-rule witness layer records pinned SpecTec source identities and
official WebAssembly specification sections for every rule used by those
examples. Exact theorem and clause-forest destruction also runs on the
combined-set stack boundary; once the combined semantics exceeded nine
thousand deeply nested clauses, dropping these values on a default host thread
became as stack-sensitive as constructing them.

This milestone does not yet claim:

- non-scalar WebAssembly syntax;
- composed whole-program validation judgments;
- stores, frames, calls, control flow, memory, references, SIMD, or GC in the
  neutral configuration vocabulary;
- a K-WASM dependency or K-specific public type;
- resolution of the explicitly censused ordered/`Else` premises;
- approximation of the remaining float, relaxed, or representation builtins.

Those gaps should be closed by extending the neutral objects and capability
traits only when a checked backend path exists.

Direct mapped iterations in function arguments now evaluate through exact
`ev.map` relations.  This unlocks hypothesis-free whole-sequence `Instrs_ok`
facts for `nop` and `i32.const 5; drop`, replaying all seven `Instrs_ok/seq`
premises at every link.

The addition witness remains deliberately execution-only at whole-program
level.  Its consecutive pushes require framing an individual instruction over
the existing operand stack.  The normative relation exposes
`Instrs_ok/frame` only for an already-derived whole sequence; `Instr_ok` has no
frame rule and there is no sequence-concatenation rule.  Exact result/instruction
subtyping preserves stack-list arity, so it cannot manufacture that missing
composition.  The facade refuses a `ProgramValid` claim for this example.

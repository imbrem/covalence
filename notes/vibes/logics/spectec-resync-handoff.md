+++
id = "N0046"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "resync-handoff"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# SpecTec/WASM resync handoff

This branch is at a natural source-only stopping point for the planned major
refactor. It remains an incomplete WASM implementation, but all landed claims
below are exact and checked; unresolved work still fails closed.

## Checkpoints since main `77fec306`

- `8732dc20` — expose checked semantics facade
- `cc07b5ed` — extend exact builtin frontier
- `cee325a8` — prove whole-program typing slice
- `05d0a481` — generalize checked decision and typing APIs
- `305eb575` — close structural list and mutual type gaps
- `291ff474` — add exact structural float semantics
- `280a18fb` — prove exact float comparisons
- `ee8d4bdd` — widen exact semantic APIs
- `586b6167` — deepen exact semantics frontier
- `0eb4732b` — carve exact recursive semantics substrate
- `e52dde8d` — prove compact float multiplication and seal carriers
- one final checkpoint containing the `fdiv_`, relation, singleton-`instr`,
  facade, and handoff work described below

## Current ratchets

- Combined relation: **18,722 clauses**
  - 558 source rules
  - 184 star clauses
  - 1,258 decision clauses
  - 15,246 exact builtin clauses
  - 1,476 evaluator clauses
- Exact builtins: **87 operations**, **76/91** formerly zero-clause tags
  filled, **15 remaining**.
- Opaque-premise census: **exactly seven**:
  - five composite `Else` applicability sites for reference cast/test and
    `array.init_data`;
  - one existential ordered-applicability premise for `vcvtop__`;
  - one negated reachability premise for `NotImmutReachable`.
- Type rendering: **176/207** standalone and **204/207** at use sites.
  The remaining three are explicitly pinned as bare parametric `num_`,
  `lane_`, and `lit_` families.
- Refinements: **28/29 families**, **53/56 premises**. The remaining three are
  the `instr` refinements for `VSHUFFLE`, `VNARROW`, and `VEXTRACT_LANE`.
- Typed semantic relations: **5/125** exact (`Defaultable`,
  `Nondefaultable`, and the three notation relations); 120 remain fail-closed.
- TCB: **24 mint sites**, zero unsafe uses, no new admitted rule or dependency.

## Completed in the final waves

### Exact scalar floating-point frontier

`fmul_` and `fdiv_` are fully integrated, including F32/F64 normals,
subnormals, signed zero, infinities, quantified NaNs, invalid-operation NaNs,
overflow, and ties-to-even. Both use compact checked staging rather than an
enumerated cross product:

- `fmul_`: 1,860 clauses (20 factor + 432 product + 824 result + 584
  exceptional), replacing a rejected F32-only prototype of 1,195,024 clauses.
- `fdiv_`: 2,888 clauses (1,464 ratio + 824 result + 600 exceptional).
- Checked division examples include `3/2 = 1.5` and odd-denominator
  `1/3 = 0x3eaaaaab`, plus wrong-result refusal.

The remaining builtin TODO names 15 tags: strict add/sub/sqrt, relaxed float
operations, relaxed truncation/integer operations, and five SpecTec/environment
scaffolds. Do not count the scaffolds as IEEE coverage.

### Recursive and dependent carriers

- Exact closed `U` path-table terms exist for all 41 constructors of the
  nine-member value/type SCC.
- All ten recursive constructor shapes have fail-closed routing and Wf
  obligations; all 41 root equations are hypothesis-free.
- Eight generative members are sealed through the single existing reviewed
  typedef seam: `comptype`, `fieldtype`, `heaptype`, `rectype`, `storagetype`,
  `subtype`, `typeuse`, and `valtype`.
- `resulttype` remains exactly an alias to `list valtype`; it is not given a
  fictitious typedef.
- Finite dependent sigma lowering preserves indexed fibers exactly. In
  particular, `CONST numtype num_(numtype)` has distinct I32/I64/F32/F64
  branches; integer and float carriers are not joined or erased.
- Full recursive `instr` carrier rendering succeeds, and a singleton closed-U
  signature has typed constructors and hypothesis-free root equations.

### Typed relations and public facade

- `Defaultable` and `Nondefaultable` now replay exactly over the sealed
  `valtype` carrier. Hypothesis-free examples cover I32 and BOT respectively.
- Public `WasmCoverage` reports full imported opacity separately from the
  zero-opaque checked execution slice.
- `v128` is represented as a neutral value type for exact `drop`/`select`.
  Vector instructions are not falsely exposed because their `Instr_ok` rules
  are absent from the current checked slice.
- `numeric.const; drop` execution is generic across I32, I64, F32, and F64,
  retaining exact raw IEEE payloads.
- The three pinned normative programs remain `nop`, `i32.const 5; drop`, and
  `i32.const 2; i32.const 3; i32.add; drop`. The addition example deliberately
  has no whole-program `Instrs_ok` theorem because the source relation lacks
  the required instruction-level frame/sequence composition rule.

## In-flight design state (not claimed complete)

The singleton `instr` Wf layer is partially generalized to structural
`RecursivePayloadShape::{Direct,Product,List,Option}` metadata. Constructor
terms/root equations are green, but full Wf construction stops exactly at
constructor 111, `REF.EXTERN`: its recursive occurrence is hidden behind an
intermediate Church/function carrier that reused global `cov$self`.

The next refactor should give recursive named carriers distinct scoped self
variables and structurally normalize the intended recursive alias before
payload-shape derivation. Do not accept that function-shaped occurrence as
opaque and do not identify it with `instr`. Once singleton Wf is complete, the
three remaining `instr` refinements can be lowered and the refinement census
can move to 29/29 and 56/56.

For type coverage, generalize the finite dependent-sigma mechanism to bare
finite-index families `num_`, `lane_`, and `lit_`; this is the exact route from
204/207 to 207/207 use-site renderability.

For typed relations, the sealed carrier now makes further structural lifting
possible. Continue from 5/125 without falling back to the legacy whole-carrier
renderer or treating nested invariants as truth.

## Verification evidence

The final pre-handoff audit passed before this document-only checkpoint:

- builtin tests: **33 passed, 1 intentionally ignored**;
- syntax tests: **23 passed**;
- semantic-relation tests: **6 passed**;
- sort/refinement tests: **20 passed** in the preceding wave;
- coverage report and v1 coverage: passed at 18,722 clauses / seven opaque;
- public WASM facade tests: **3 passed** (the full run took 449 seconds after
  the checked slice grew to 6,995 clauses);
- `bun run todos:check`: passed;
- `bun run deps:check`: passed after regenerating notes/maps;
- TCB audit: 24 mint sites, zero unsafe, no dependency delta.

Per the request to stop quickly, no additional test rerun was performed solely
for this handoff text and final commit.

## Generated artifacts and integration

Intermediate commits are source-only. Generated TODO/map/dependency artifacts
were intentionally removed from the final checkpoint. At integration time run:

```sh
bun run todos
bun run notes
bun run notes
env RUSTC_WRAPPER= bun run deps:check
```

Then review and commit the generated delta separately if main expects it.

## Trust and backend boundary

Parsing, indexing, monomorphisation, coverage analysis, lowering, staging, and
search remain untrusted. Only checked NativeHol replay establishes theorem
authority. A future K-WASM backend should share the neutral WASM syntax,
typing/execution statements, coverage contract, configurations, and observable
results; it must not expose SpecTec AST nodes or gain theorem authority from
host execution.

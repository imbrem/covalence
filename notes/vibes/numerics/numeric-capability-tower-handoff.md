+++
id = "N0045"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-19T00:00:00+01:00"
source = "workmux-handoff"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Numeric capability tower: workmux handoff

## Goal

Extend the successful representation-independent Nat architecture into a
layered numeric capability tower without attempting to finish every concrete
numeric theory. The first deliverable is a small generic consumer that runs
unchanged against a proof-free value backend and a proof-bearing NativeHol
backend.

This branch is primarily about API shape and representation morphisms:

```text
Nat
 |
 v
Int ----> Rat ----> Real
 |         |
 v         v
Decimal   approximation / enclosure
 |                    |
 v                    v
IEEE rounding ----> Ball arithmetic
```

Syntax, algebraic laws, observation, decision, normalization, rounding, and
enclosure must be separate optional capabilities. A backend must not advertise
laws merely because its host representation computes successfully.

## Existing foundation

- Abstract Nat capabilities:
  `crates/kernel/hol/logic/src/nat.rs`.
- Legacy concrete Int facade:
  `crates/kernel/hol/api/src/int.rs`.
- Exact decimal traits and canonical interchange:
  `crates/lang/decimal/src/lib.rs`.
- Exact host values:
  `crates/lib/types/src/{nat,int,rat,decimal}.rs`.
- Generic numeral grammar and backend ladder:
  `crates/lang/numerals/`.
- Structural HOL decimal representation:
  `crates/kernel/hol/init/src/init/decimal.rs`.
- Concrete HOL rational and real developments:
  `crates/kernel/hol/init/src/init/{rat,real}.rs`.
- Trusted/eval IEEE operations:
  `crates/kernel/base/{trusted,eval}/src/float.rs`.
- Typed HOL floating-point layer:
  `crates/kernel/hol/eval/src/{defs/floats,typed_float}.rs`.
- Ball groundwork:
  `crates/kernel/hol/init/src/init/ball.rs`.

There are currently three important decimal representations:

```text
covalence_types::Decimal
CanonicalDecimal (A0006 and JSON)
NativeHol decimal as (int, nat)
```

The lack of explicit, checked morphisms between them is the first concrete
problem to solve.

## Required boundaries

- Put dependency-free numeric vocabulary beside the existing logic/Nat
  vocabulary, or in an equally low and neutral API crate.
- Keep host values, NativeHol terms, IEEE evaluation, and future WASM/WIT
  realizations as backends.
- Treat BigInt, BigRational, host float operations, normalization, parsing, and
  search as untrusted computation.
- Proof-bearing morphisms and laws must consume or construct checked theorem
  evidence; they may not wrap booleans or successful host comparisons in an
  evidence type.
- Do not refactor the unfinished internals of the concrete rational or real
  developments during the first milestone.
- Do not implement decimal-to-IEEE rounding or ball containment in this branch;
  design their capability seams, then leave those proof milestones for the
  follow-up `certified-decimal-f32-ball` workstream.

## First milestone

1. Define narrowly composable capability families for:
   - integers: syntax, arithmetic, order, supplied laws;
   - rationals: syntax, field operations, order, supplied laws;
   - exact decimals: refinement into rationals;
   - IEEE values: bit observation and explicit rounding capabilities;
   - balls: construction, observation, arithmetic, and enclosure laws.
2. Keep equality decision, normalization, rounding, and enclosure computation
   optional.
3. Provide proof-free reference adapters for the exact host value types.
4. Implement the `CanonicalDecimal` to exact host rational refinement.
5. Implement the smallest honest NativeHol decimal-to-rational adapter using
   the existing `(int, nat)` decimal representation and checked theorem path.
6. Write one generic consumer/conformance test that runs over the reference
   and NativeHol backends without changing its algorithm.

The relevant existing open boundary is
`TODO(cov:json.decimal-a0006-native-hol-morphism, major)`. Resolve it only if
normalization, signed exponents, and the theorem evidence are genuinely
complete; otherwise narrow it into precise source-local follow-ups.

## Acceptance conditions

- The capability traits do not mention concrete host or NativeHol carrier
  types.
- Reference and NativeHol implementations share a generic conformance test.
- Decimal-to-rational conversion handles zero, sign, normalization, positive
  exponents, and negative exponents.
- Host computation cannot mint proof evidence.
- The first milestone introduces no new trusted rule or theorem mint site.
- The dependency graph remains layered and has no web, parser evaluator, or
  WASM runtime dependency in the abstract API.
- Narrow Rust tests, `bun run todos:check`, and `bun run deps:check` pass.
- TCB mint sites remain unchanged.

## Worktree discipline

- Suggested branch: `numeric-capability-tower`.
- Prefer a small sequence of commits: API vocabulary, reference backend,
  NativeHol adapter, generic conformance.
- Avoid broad renaming or moving existing numeric theories.
- Commit source-only checkpoints; regenerate generated indexes only at the
  integration boundary.
- Stop after the cross-backend decimal-to-rational demonstration.
- Report commits, stable TODO changes, tests, dependency/TCB deltas, ergonomic
  problems found in the traits, and a proposed `certified-decimal-f32-ball`
  follow-up.


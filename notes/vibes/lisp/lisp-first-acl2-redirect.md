+++
id = "N0051"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:codex"
at = "2026-07-19T00:00:00+01:00"
source = "lisp-first-acl2-redirect"
agent = "codex"
harness = "codex"
+++

# Discussion memo: restore Lisp-first ACL2 layering

## Proposed redirect

Treat ACL2 as a logically admitted subset and event system built on a reusable
Lisp semantics. Do not give generic Lisp ACL2's totality requirements.

The intended stack is:

```text
bytes/text
  → abstract S-expressions
  → general Lisp syntax and environments
  → partial relational small-step Lisp semantics
  → ACL2 admissible worlds and logical subset
  → checked ACL2 derivations
  → sound transport to ordinary HOL theorems
  → imported libraries and x86 development
```

## Generic Lisp foundation

The Lisp layer should support:

- expressions, values, environments, closures, and application;
- a small-step relation over configurations;
- reflexive-transitive execution `s →* s'`;
- arbitrary recursion, divergence, stuck states, and optionally unspecified
  evaluation choices;
- relational evaluation:

  ```text
  MayEval(e, v) ≡ e →* value(v)
  ```

- checked finite traces as evidence for `MayEval`;
- no assumption that every expression terminates or has a unique result.

If useful, define a total projection with Hilbert choice:

```text
eval(e) = εv. MayEval(e, v)
```

For general Lisp, a trace proves `MayEval(e, v)`, not necessarily
`eval(e) = v`. Equality with the chosen evaluator additionally requires
existence and uniqueness of the result.

This foundation should be independently reusable and should not contain ACL2
books, worlds, admissibility, theorem hints, or x86-specific concepts.

## ACL2 on top

ACL2 should restrict the Lisp layer with checked evidence:

- first-order logical terms and well-formed logical worlds;
- conservative admission of nonrecursive definitions;
- termination and well-foundedness evidence for recursive definitions;
- existence and uniqueness of results for admitted functions;
- connection of admitted Lisp execution to total HOL functions;
- ordered events, packages, tables, local scopes, includes, and generated
  events;
- a checked derivation calculus for rewriting, congruence, cases, induction,
  and other ACL2 proof principles;
- a soundness theorem transporting checked ACL2 derivations into ordinary,
  hypothesis-free HOL theorems.

Host parsing, macro expansion, normalization, proof search, trace discovery,
and induction discovery remain untrusted. They may produce witnesses, but only
kernel-checked replay may produce theorem authority.

## Why redirect

The current work has drifted toward a direct ACL2-specific deep evaluator and
proof normalizer. That has produced real checked results, but it risks:

- conflating generic Lisp execution with ACL2 logical totality;
- making reusable Lisp APIs carry ACL2-specific concepts;
- solving individual theorem-normalization problems before the semantic
  boundary is stable;
- obscuring which facts follow from Lisp execution, ACL2 admission, or the
  ACL2 proof calculus.

The recent `NFIX`/`IFIX` work illustrates the issue. The four target theorems
are small, but proving them has exposed delicate interactions among evaluator
rows, recognizer normalization, case hypotheses, and theorem transport. A
Lisp-first semantics would not eliminate symbolic proof, but it would make the
responsibilities clearer:

- reduction traces justify concrete execution;
- ACL2 admission establishes totality and uniqueness;
- symbolic derivations prove open theorems;
- transport converts only checked derivations to HOL authority.

## What remains useful

This is a layering correction, not a request to discard the branch. Likely
reusable work includes:

- S-expression readers and abstract syntax;
- book linking and source provenance;
- ordered-world/event analysis;
- ACL2 term encodings;
- conservative definition machinery;
- well-founded recursion and ordinal results;
- checked derivation and transport rules;
- untrusted proof-search and corpus-analysis infrastructure;
- completeness reporting and x86 corpus measurements.

Each component should be audited and assigned to one of the explicit layers.

## Scope of “Lisp first”

Do not block ACL2 on implementing all of Common Lisp. The prerequisite should
be a small, explicit Lisp core sufficient to host ACL2 terms and event-time
computation:

1. lexical scope, variables, quotation, conditionals, and application;
2. conses, symbols, integers, strings, and primitive operations;
3. closures and recursive bindings;
4. partial small-step execution and checked traces;
5. determinism/uniqueness results for a deterministic sublanguage;
6. a clear extension seam for macros and host effects.

Features not required by upstream ACL2 or independently valuable Lisp clients
can remain out of scope.

## Suggested migration

1. Inventory the current Lisp/ACL2 implementation by semantic layer.
2. Specify the minimal Lisp configuration, value, and small-step relations.
3. Implement checked trace replay and prove its soundness.
4. Relate the current executable evaluator to the relation on their shared
   supported fragment instead of immediately deleting it.
5. Express ACL2 logical admissibility as predicates and checked world
   transitions above the Lisp layer.
6. Prove that admitted ACL2 functions have terminating, unique logical
   results and connect them to total HOL constants.
7. Rebase the existing ACL2 derivation checker and theorem transport on that
   admitted semantics.
8. Resume upstream green islands, then bitvector libraries and x86.

## Questions for review

- Should general Lisp reduction be deterministic, or should evaluation order
  remain relational with determinism proved only for selected strategies?
- What is the smallest Lisp core needed by ACL2 event computation?
- Which current deep-evaluator theorems can become derived lemmas over
  small-step execution?
- Should ACL2 admission produce total HOL constants directly, or first produce
  existence/uniqueness theorems from which those constants are defined?
- How should raw Lisp execution and `make-event` be sandboxed so they can
  propose events without theorem authority?
- What exact milestone demonstrates the layering end to end before returning
  to broad community-books work?

## Recommended first milestone

Choose a tiny recursive Lisp program and prove:

1. a checked finite small-step trace reaches a value;
2. the trace entails relational evaluation;
3. an ACL2-style termination/admission witness establishes totality and
   uniqueness for the function;
4. the admitted function receives a conservative HOL interpretation; and
5. one open theorem about it is proved by checked ACL2 derivation and
   transported to a closed HOL theorem.

This tests every intended boundary without requiring a complete Lisp or ACL2
implementation.

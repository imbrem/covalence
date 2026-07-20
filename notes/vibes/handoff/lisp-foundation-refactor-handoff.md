+++
id = "N0047"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T21:16:52+01:00"
source = "lisp-foundation-refactor-handoff"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Lisp foundation refactor handoff

## Stable boundary reached

The reusable Lisp stack now has one common core syntax and CEK machine shared
by Scheme, Sector, ACL2 expression execution, and the applicative side of the
Forsp work. The kernel API separates syntax, runtime values, closures,
environments, effects, checked traces, transition classification, admission,
and theorem-producing replay seams.

Recent checkpoints on `main` are:

- `e4275657`: stable machine-step classifications, including lexical beta and
  environment-lookup delta steps;
- `e7843d14`: concrete higher-order Lisp execution transports to HOL equality;
- `a026378d`: ACL2 concrete executions use that transport without claiming
  totality;
- `51b59574`: frontend syntax can be imported into either direct trees or
  opaque resource handles; the arena runtime now makes expressions, values,
  closures, and environments opaque.

The uncommitted final checkpoint adds `CoreExprLayer::try_map_recursive` and
`export_core`, the checked inverse-shaped projection from an arbitrary
`LispExpression` backend to the neutral `CoreExpr` tree. This should be kept:
it is the natural representation boundary for the planned refactor.

## Tests already run before the stop request

- `cargo test -p covalence-kernel-lisp`: 35 passed;
- `cargo test -p covalence-lisp --lib --all-features`: 86 passed, 3 external
  corpus tests ignored;
- focused Scheme effect, backend-conformance, and ACL2 operational/HOL bridge
  tests passed;
- TODO, dependency, notes, and TCB checks passed at the preceding checkpoints.

Per maintainer request, no further tests were run after adding the final
fallible traversal/export helper.

## Deliberately unfinished

The next implementation was going to generalize HOL transport from the direct
host runtime to any `LispRuntime`: use `export_core` for the initial expression
and `project_datum` for the terminal value, then replay the resulting neutral
program with `LispSemantics`. An arena-backed Scheme lambda should be the first
conformance test. This work has not been started and should be reconsidered in
the new crate architecture rather than patched into the current layout.

Universal ACL2 adequacy is also still open. Concrete traces and equational
definition hypotheses are now connected, but neither proves:

```text
forall inputs. exists value. MayEval(call, value)
forall inputs values. MayEval(call, value1) and MayEval(call, value2)
                      implies value1 = value2
```

Only after those facts are replayed should ACL2 totalize a definition and
transport checked derivations to closed HOL theorems. The severe marker remains
`cov:lisp.acl2.admission-layer`.

Other known HOL gaps remain source-local TODOs: strict sequencing, variadic
closures, runtime-list application, and mutually recursive lexical bindings.

## Refactor guidance

- Keep `kernel/lisp` as the low-level, WIT-shaped capability waist and put
  concrete Scheme/ACL2 frontend policy under `lang`.
- Directory dependencies may cross `kernel` and `lang` in either direction;
  only actual Cargo package cycles need an extracted interface/IR crate.
- Preserve `CoreExpr` as an interchange tree, not a mandatory runtime
  representation. Runtime code should consume `LispExpression`/`LispSyntax`.
- Preserve `RuntimeValueLayer` and `CoreExprLayer` as the one-layer functors;
  direct trees, opaque resources, and future logical inductive realizations
  should implement the same APIs.
- Do not merge the first-order `LispRel` and the equational `LispSemantics`
  merely to reduce file count. They currently make different claims. A future
  CEK-wide HOL relation can subsume them only after it represents syntax,
  environments, closures, continuations, effects, and partiality honestly.
- Keep ACL2 worlds, events, admission, books, and proof calculus above generic
  Lisp. Keep Forsp's concatenative machine separate where its semantics is
  genuinely different, while sharing data, trace, and effect vocabularies.

## Repository state caveat

`notes/chats/` is unrelated maintainer work and was not edited or staged. The
handoff commit should include only the Lisp source changes, generated map/TODO
artifacts required by the repository checks, and this note.

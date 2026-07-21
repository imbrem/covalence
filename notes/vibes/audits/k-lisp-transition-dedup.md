+++
id = "N005J"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:codex"
at = "2026-07-21T00:00:00+01:00"
source = "k-lisp-rule-dedup"
agent = "codex"
harness = "codex"
+++

# K/Lisp transition deduplication

K and Lisp share a proof-free execution shape but not a proof calculus. This
distinction should control the extraction.

## Current layers

| Layer | K | Lisp | Shared candidate |
|---|---|---|---|
| transition discovery | `KReducer` + `Matcher` | `StepRelation` / `DeterministicStep` | deterministic state transition |
| finite witness | reducer loop | `CheckedTrace`, `execute`, `explore` | states, fuel, halt/stuck outcome |
| checked replay | `RewriteRelation::prove_step` | `TraceReplay` / `MayEvalReplay` | capability shape only |
| theorem | HOL `Step` and `Reduces` | backend-specific relations/equalities | no common theorem representation |

`covalence-computation::execution` already owns a neutral deterministic
`TransitionSystem` and fuel-bounded traces. K now implements that interface, so
generic tracing and its certified reducer operate over the same next-step
function. The checked reducer remains authoritative: the generic trace is only
an untrusted witness, while `KReducer::reduce` constructs the HOL theorem.

## Smallest safe extraction

Move only these proof-free concepts into a neutral kernel package:

1. deterministic and nondeterministic one-step capabilities;
2. terminal observation;
3. finite checked traces and fuel bounds;
4. run/explore algorithms.

Then make `covalence-computation` and `covalence-kernel-lisp` compatibility
facades over that package. Keep `TraceReplay`, `MayEvalReplay`, K's
`RewriteRelation`, and all theorem types in their present proof layers.

Putting the common API in Lisp would make K depend on language-specific policy.
Putting it in `lang/computation` would make the low-level Lisp capability waist
depend on a high-level theory crate. A new small kernel package avoids both
directions and keeps a future WIT boundary free of HOL carriers.

Tracked acceptance work is `semantics.shared-transition-waist`.

## Duplication outside this extraction

K still exposes three historical proof paths in `k/reduce.rs`, `k/relation.rs`,
and the newer `k/rewrite.rs`. They encode different judgement shapes, so deleting
either older path would remove public functionality. After consumers settle on
the binary `RewriteRelation`, retain old entry points as forwarding adapters or
mark them deprecated; do not merge their theorem types by type alias without an
explicit equivalence theorem.

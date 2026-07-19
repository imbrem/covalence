+++
id = "N000I"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-18T23:51:27+01:00"
source = "codex-development-wave"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Inductive API audit

Status: agent audit of `main` at `358dc877` (2026-07-18).

This note describes what the integrated inductive APIs actually provide, where
the proof objects come from, and which parts remain interface designs rather
than working prover paths.

## Executive summary

The current code contains two related inductive interfaces:

1. A mature, membership-relativized `InductiveTheory` interface used by the HOL
   Church, carved-type, and engine backends.
2. A cleaner polynomial/fixpoint vocabulary with proof-bearing aggregate,
   Lambek-isomorphism, least-fixpoint, and greatest-fixpoint bundles.

The first interface is implemented and exercised by real prover backends. The
second establishes a good consumer-facing target, but no production backend
currently implements its proof-bearing traits. The structural conversion
between their specifications exists; the theorem-preserving adapter between
their realized bundles does not.

That distinction is the most important fact for planning. The new layer is not
unsound or an expansion of the TCB: it is an untrusted vocabulary containing
opaque theorem handles. But it is not yet evidence that the HOL kernel can
realize the advertised generic fixpoint laws.

## The layers

```text
plain structural syntax
  FunctorExpr              zero / one / parameter / variable / sum / product / composition
  PolynomialSpec           named sum of named products
  Record/Variant/EnumSpec  restricted aggregate views
  FixpointSpec             name + PolynomialSpec
        |
        v  structural validation
  Validated<Spec>
        |
        +--> opaque realization seams (representation-specific result)
        |
        +--> proof-bearing bundles (carrier/operations + theorem-producing facts)

legacy path
  InductiveSpec --> InductiveBackend --> InductiveTheory
       ^ structural conversion             |
       +---------- FixpointSpec ------------+  theorem adapter is still missing
```

### Structural functor expressions

[`FunctorExpr`](../../../crates/kernel/data/inductive/src/polynomial.rs#L32) is the
small structural algebra
`0 | 1 | P | X | F + G | F × G | F ∘ G`. Composition is represented explicitly
by [`Compose`](../../../crates/kernel/data/inductive/src/polynomial.rs#L45), and
[`expand_composition`](../../../crates/kernel/data/inductive/src/polynomial.rs#L103)
implements capture-free substitution of the inner expression for every `Var`
in the outer expression. Parameters are constants and are not substituted.
[`is_recursive`](../../../crates/kernel/data/inductive/src/polynomial.rs#L63) correctly
treats `F ∘ G` as dependent on `X` only when both `F` depends on its argument
and `G` depends on `X`.

[`StructuralPolynomial`](../../../crates/kernel/data/inductive/src/functor.rs) now
checks the bounded `0 | 1 | P | X | F + G | F × G` fragment and deliberately
rejects explicit composition. [`StructuralFunctorAction`] gives backends a
narrow seam for interpreting `F(X)` and lifting an arrow `f : X → Y` to
`F(f)`. [`StructuralFunctorLaws`] separately requests backend-native evidence
for identity, composition, and congruence. These traits do not mint evidence,
and no HOL backend implements them yet. Composition-preserving interpretation,
nested fixpoint realization, and a proof that `expand_composition` preserves
interpretation therefore remain open.

### Named polynomial and aggregate specifications

[`PolynomialSpec`](../../../crates/kernel/data/inductive/src/polynomial.rs#L301) is the
ergonomic source form

```text
F(X) = Σ constructor. Π field. (parameter | X)
```

It preserves constructor and field names and declaration order.
[`Position`](../../../crates/kernel/data/inductive/src/polynomial.rs#L149) restricts
each field to either one external parameter token or a direct recursive
occurrence. [`into_expression`](../../../crates/kernel/data/inductive/src/polynomial.rs#L375)
forgets names and translates the normal form to `FunctorExpr`.

The aggregate views deliberately narrow this common representation:

- [`RecordSpec`](../../../crates/kernel/data/inductive/src/polynomial.rs#L200) is one
  non-recursive product. The empty record is the unit product.
- [`VariantSpec`](../../../crates/kernel/data/inductive/src/polynomial.rs#L435) is a
  non-recursive sum of products.
- [`EnumSpec`](../../../crates/kernel/data/inductive/src/polynomial.rs#L455) is a
  non-empty sum of units.

Their proof-bearing realization bundles are:

- [`RecordTheory` and `RecordFacts`](../../../crates/kernel/data/inductive/src/aggregate.rs#L12):
  constructor, ordered projections, projection β, and extensionality.
- [`VariantTheory` and `VariantFacts`](../../../crates/kernel/data/inductive/src/aggregate.rs#L44):
  injections, case application/β, injectivity, and constructor distinctness.
- [`EnumTheory` and `EnumFacts`](../../../crates/kernel/data/inductive/src/aggregate.rs#L88):
  case terms, exhaustiveness, and distinctness.

Each proof-bearing backend trait receives a checked spec and must return the
operations together with theorem-producing rule methods
([`aggregate.rs`](../../../crates/kernel/data/inductive/src/aggregate.rs#L108)).
The older `RecordBackend`/`VariantBackend`/`EnumBackend` traits return opaque
backend-defined values and promise no common proof surface
([`aggregate.rs`](../../../crates/kernel/data/inductive/src/aggregate.rs#L139)).

### Validation boundary

The plain specifications are intentionally permissive Rust data so parsers can
construct invalid values and report useful errors. [`Validated<S>`](../../../crates/kernel/data/inductive/src/validated.rs#L15)
has a private field and is constructed through `TryFrom`; the backend-facing
APIs accept this wrapper.

Validation currently checks:

- non-empty type/constructor/field names;
- unique constructors and fields;
- no recursive positions in records and ordinary variants;
- a non-empty case set for enums;
- the nested polynomial's structure for fixpoints.

The conversion methods on validated values preserve only transformations that
cannot invalidate those properties, such as mapping parameter tokens
([`validated.rs`](../../../crates/kernel/data/inductive/src/validated.rs#L42)).

This boundary is useful but modest. It does not prove semantic positivity,
functoriality, inhabitation, or backend support. Positivity is obtained by the
limited grammar: `PolynomialSpec` can only place `X` directly in finite
products and sums. `FunctorExpr` composition is not accepted by
`FixpointSpec`, so its broader syntax never reaches this validation/realization
path.

### Least and greatest fixpoints

[`FixpointCore`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L25) packages:

- the exact validated specification;
- the carrier `μF` or `νF`;
- the instantiated layer type `F carrier`;
- `roll : F carrier → carrier`;
- `unroll : carrier → F carrier`;
- theorem methods proving both inverse equations.

The inverse methods in
[`FixpointIsoFacts`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L46) make the
Lambek isomorphism explicit rather than leaving it as a backend convention.

[`LeastFixpoint`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L54) adds
[`LeastFixpointFacts`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L62):
construction of `fold`, the `fold/roll` computation law, and structural
induction. [`GreatestFixpoint`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L78)
dually adds `unfold`, the `unroll/unfold` computation law, and coinduction
through [`GreatestFixpointFacts`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L86).
The capability split is good: a backend can implement least fixpoints without
pretending to support coinduction.

There are also opaque compatibility seams,
[`InductiveFixpointBackend`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L156)
and [`CoinductiveFixpointBackend`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L174),
whose associated result types have no shared theorem contract. The
proof-bearing traits are strictly stronger
([`fixpoint.rs`](../../../crates/kernel/data/inductive/src/fixpoint.rs#L101)).

At this revision these types and traits have unit tests of structural
validation, but repository search finds no implementation of
`ProofBearingLeastFixpointBackend`,
`ProofBearingGreatestFixpointBackend`, `LeastFixpointFacts`,
`GreatestFixpointFacts`, or the proof-bearing aggregate backend traits. In
particular, greatest fixpoints are an API seam only; the missing backend-neutral
conformance suite is tracked by
`cov:inductive.coinductive-conformance`
([`conformance.rs`](../../../crates/kernel/data/inductive/src/conformance.rs#L36)).

### The implemented legacy bundle

[`InductiveSpec`](../../../crates/kernel/data/inductive/src/spec.rs#L108) describes a
single, directly recursive, first-order datatype using constructor arguments
[`Rec` or `Ext(X)`](../../../crates/kernel/data/inductive/src/spec.rs#L16). It converts
structurally to and from `FixpointSpec`
([`spec.rs`](../../../crates/kernel/data/inductive/src/spec.rs#L189)).

[`InductiveBackend`](../../../crates/kernel/data/inductive/src/backend.rs#L11)
realizes that declaration as
[`InductiveTheory`](../../../crates/kernel/data/inductive/src/theory.rs#L167):
an opaque carrier, membership predicate, ordered constructors, and an
`InductiveFacts` rule object.

This contract is richer and more representation-aware than the new minimal
least-fixpoint bundle. It includes:

- iteration and constructor computation;
- constructor injectivity and distinctness;
- induction and cases;
- constructor membership and optional trivial membership;
- optional primitive recursion;
- explicit capability flags for exact membership, recursive-position
  injectivity, and primitive recursion
  ([`BackendCaps`](../../../crates/kernel/data/inductive/src/theory.rs#L75)).

Membership relativization is essential for sharing the API between exact
carved types and encodings whose carrier contains junk. The full contract and
the rank-1 Church “subtree recovery” limitation are documented at
[`theory.rs`](../../../crates/kernel/data/inductive/src/theory.rs#L1).

This path has production implementations:

- the impredicative Church backend
  ([`church.rs`](../../../crates/kernel/hol/init/src/init/inductive/church.rs#L96));
- the carved exact-type backend
  ([`carved.rs`](../../../crates/kernel/hol/init/src/init/inductive/carved.rs#L1201));
- the existing engine adapter
  ([`engine.rs`](../../../crates/kernel/hol/init/src/init/inductive/engine.rs#L65)).

The generic conformance checker actually consumes the bundle, constructs a
recursor and induction obligations through `LogicOps`, and checks theorem
shapes, membership plumbing, and distinctness
([`check_theory`](../../../crates/kernel/data/inductive/src/conformance.rs#L101)).
This is stronger evidence than type-checking a trait implementation, although
it is not yet a complete semantic conformance proof.

The missing bridge is accurately tracked by
`cov:inductive.legacy-fixpoint-adapter`
([`backend.rs`](../../../crates/kernel/data/inductive/src/backend.rs#L9)). Building it
requires realizing the new structural functor capability in the target logic
and deriving the layer, roll/unroll, and Lambek theorems. A structural spec
conversion or an implementation of `map` alone cannot manufacture those
facts.

### Logic abstraction and trust

The inductive crate is logic-independent and has only `smol_str` and
`thiserror` dependencies
([`Cargo.toml`](../../../crates/kernel/data/inductive/Cargo.toml#L1)).
Its local [`Logic`](../../../crates/kernel/data/inductive/src/logic.rs#L29) trait names
the logic's `Type`, `Term`, `Thm`, and `Error` carriers. `LogicOps` adds enough
HOL-flavoured construction and primitive rules for generic consumers and
conformance checks
([`logic.rs`](../../../crates/kernel/data/inductive/src/logic.rs#L42)).

This crate does not mint theorems and does not enlarge the TCB. A dishonest
backend can return the wrong theorem handle only if it can already forge
`L::Thm`; with an unforgeable kernel theorem type, the trait objects merely
organize checked results. Conversely, Rust's trait system does not verify that
a returned theorem has the equation described in a doc comment. Consumers must
either trust the backend adapter's implementation or inspect theorem
conclusions with logic operations. The existing conformance suite does the
latter for part of the legacy contract.

The trust story therefore depends on:

1. an unforgeable `Thm` carrier and sound primitive rules in the logic TCB;
2. backend code deriving, rather than admitting, the handles it returns;
3. conformance checks or typed statement witnesses ensuring the returned
   theorem is the advertised one.

The local logic abstraction also duplicates the extracted
`covalence-logic-api`; integration is explicitly open as
`cov:inductive.logic-api-adapter`
([`logic.rs`](../../../crates/kernel/data/inductive/src/logic.rs#L27)).

### S-expressions as a client

The S-expression crate chooses the canonical polynomial
`P + 1 + X × X`: atom, nil, and cons
([`polynomial`](../../../crates/kernel/lisp/sexpr/src/lib.rs#L27)). It provides
three distinct levels:

1. [`SExprF`](../../../crates/kernel/lisp/sexpr/src/lib.rs#L53), a concrete
   one-layer functor with an executable `map`.
2. [`SExprSyntax`, `SExprView`, and `ProperList`](../../../crates/kernel/lisp/sexpr/src/lib.rs#L74),
   representation-independent construction/observation and derived finite
   list operations. `ListSpine` preserves dotted tails rather than pretending
   every S-expression is a proper list.
3. [`SExprFixpoint`](../../../crates/kernel/lisp/sexpr/src/lib.rs#L147), a checked
   constructor-named wrapper around a generic `LeastFixpoint`. `try_new`
   compares the full spec with the canonical S-expression spec and then
   delegates the carrier, roll/unroll, fold, computation, and induction
   methods. It adds no theorem or axiom.

[`FreeSExpr`](../../../crates/kernel/lisp/sexpr/src/lib.rs#L208) is a working Rust
reference representation for the syntax/view layer. It is not a prover backend
and does not construct `SExprFixpoint`. No production code currently constructs
an `SExprFixpoint`, because no production least-fixpoint backend supplies the
required bundle.

Constructor injectivity/distinctness and proof-bearing proper-list predicates
are still open as `cov:sexpr.no-confusion-laws` and
`cov:sexpr.proper-list-proof-capability`
([`sexpr-api/src/lib.rs`](../../../crates/kernel/lisp/sexpr/src/lib.rs#L256)).

## Design assessment

### Strengths

- **Bounded width through layers.** Plain syntax, validation, opaque realization,
  proof-bearing contracts, and datatype-specific wrappers are separate.
- **Representation neutrality.** Consumers receive carrier/operation/theorem
  handles rather than learning Church or carved representations.
- **Honest partiality.** Least and greatest fixpoints and optional legacy
  capabilities are separate; unsupported operations can be refused.
- **Portable specifications.** The data is ordered, comparable, hashable, and
  free of closures, which is a good basis for serialization and content
  addressing.
- **Explicit laws.** Lambek inverses and computation rules are API values
  instead of undocumented backend expectations.
- **TCB restraint.** The API does not admit facts or add trusted mint sites.
- **Useful migration path.** Old and new specifications are structurally
  interconvertible, allowing consumers to stabilize before backend replacement.

### Costs and risks

- **Two parallel public models.** `InductiveSpec`/`InductiveTheory` and
  `FixpointSpec`/`LeastFixpoint` overlap but have different theorem surfaces.
  Until the bridge lands, consumers must choose between implemented richness
  and the cleaner target abstraction.
- **The new proof contracts are mostly nominal.** Doc comments specify theorem
  shapes, but the type system records only `L::Thm`. There is no general
  statement-indexed witness or conformance checker for the new bundles.
- **Functor composition stops before realization.** `FunctorExpr::Compose`
  cannot be retained in `PolynomialSpec` or `FixpointSpec`; expanding it erases
  names and cannot feed the named realization path. The JSON composition TODO
  therefore remains genuine
  ([`json-api`](../../../crates/lang/json-api/src/lib.rs#L639)).
- **No generic functor interpretation/action.** This blocks the honest legacy
  adapter and makes the `map` appearing in fold/unfold laws prose rather than an
  exposed operation.
- **Local logic duplication.** The compatibility `Logic`/`LogicOps` vocabulary
  risks adapter churn and prevents direct stacking on the newer logic/relation
  APIs.
- **Object safety trades precision for flexibility.** `Box<dyn ...Facts>` makes
  runtime backend swapping straightforward, but associated typed statements,
  static composition, serialization, and WIT projection will require another
  layer.
- **The first-order grammar is intentionally narrow.** There is no mutual,
  nested, indexed, higher-order, or multi-parameter recursion. Adding those
  directly to the current normal form could widen every backend; capability
  layers are preferable.
- **Conformance coverage is asymmetric.** The legacy least-inductive bundle has
  meaningful checks; proof-bearing aggregates, least fixpoints, and all
  coinductive behavior do not.

## Prioritized improvements

1. **Unify on the extracted logic carriers.** Resolve
   `cov:inductive.logic-api-adapter` first, preferably by re-exporting or
   implementing thin adapters rather than growing a third logic vocabulary.
   This sets the carrier types used by all later work.
2. **Define polynomial interpretation and functor action.** Add a narrow
   capability that interprets `0`, `1`, parameters, sums, and products and
   returns `F A`, `map F f`, identity/composition laws, and the necessary
   congruence theorems. Keep names as metadata above this structural layer.
3. **Implement one HOL `LeastFixpoint` adapter.** Start with the carved backend,
   whose exact carrier and stronger recursion/freeness capabilities make the
   Lambek package most direct. Derive every returned theorem through the
   existing kernel. Then adapt Church only for the subset it can honestly
   supply.
4. **Add conformance for the new bundles.** Check exact theorem conclusions for
   Lambek inverses and computation laws, plus malformed indices/arity. Use the
   same suite against at least two backends to demonstrate representation
   independence.
5. **Give no-confusion its own optional capability.** Least-fixpoint initiality
   alone is too weak as an ergonomic surface for S-expressions. Add
   constructor injectivity/distinctness separately so Church-like backends can
   expose precisely what they prove.
6. **Connect composition to named specs.** Either normalize composed
   expressions into generated names with a source-name mapping, or let
   `FixpointSpec` carry a structural expression plus optional presentation
   schema. Do not silently claim that the current name-erasing expansion solves
   JSON's list/object composition.
7. **Build the first coinductive reference backend.** A small stream functor is
   enough to force the shape of observation, bisimulation, productivity, and
   the conformance suite before broadening the datatype grammar.
8. **Replace prose-only theorem contracts incrementally.** Statement-indexed
   theorem wrappers or checked smart constructors can ensure that a
   `fold_roll` result is actually the requested equation without putting
   backend adapters in the trust story. This should lower to the kernel's
   ordinary theorem checks, not add TCB rules.
9. **Drive the design through vertical clients.** Finish the S-expression
   no-confusion/proper-list layer, then JSON composition, and compare at least
   two natural-number encodings. These expose practical API holes more reliably
   than expanding the datatype grammar speculatively.

## Verification performed

The audit used repository-wide implementation searches and the narrow test
suites:

```sh
cargo test -p covalence-inductive -p covalence-sexpr-api
```

No trusted crate or dependency edge was changed by this report.

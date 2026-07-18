# Logic, Nat, and inductive API extraction audit

- **Status:** Draft audit
- **Owner:** maintainer
- **Last touched:** 2026-07-18
- **Audits:** `covalence-logic-api`, `covalence-hol-api::nat`, and
  `covalence-inductive`

## Executive assessment

The extraction is a useful additive first step. It creates dependency-light
vocabulary, splits optional capabilities rather than encoding missing work as
runtime failure, preserves current consumers, and adds no theorem mint sites.
It should not yet be called the stable high-level API.

The largest remaining architectural issue is that the three surfaces are not
yet one stack:

- `covalence-logic-api` owns the new associated-error logic carrier;
- Nat capabilities still extend the legacy concrete `Hol` trait and return
  `covalence_core::Result`;
- `covalence-inductive` retains its older parallel `Logic`/`LogicOps` carrier;
- aggregate and fixpoint realizations return opaque backend bundles without a
  common proof-bearing contract.

The next iteration should connect these seams while retaining compatibility
adapters outside the dependency-light API crates.

## Logic API

### What is good

- The crate has no dependencies and no implementation authority.
- `Kind`, `Type`, `Term`, `Thm`, and `Error` are associated carriers.
- Capabilities for types, terms, equality, quantifiers, and proof rules are
  independently implementable.
- `TypeSystem` has an explicit kind arrow and type application, leaving room
  for `m a`, `r a b`, and HOL-ω rather than baking in simply typed HOL.
- Typed `Arrow<A,B>` values prevent some malformed relational composition at
  the API boundary.

### Risks and improvements

- `RelationOrder::inclusion` and `relation_equality` sound as if any requested
  judgment can be proved. Split proposition construction, supplied evidence,
  derivation laws, and optional decision procedures. A backend should not
  implement a method whose contract silently presumes arbitrary inclusion.
- `RelationProperty` is a closed enum. Prefer separate capability/law packages
  so new properties do not require editing the central crate.
- The relation API lacks products, coproducts, converse laws, residuals,
  tabulation, closures, maps/functions as functional relations, and law
  bundles. These are needed before calling it an allegory/relational algebra.
- `Arrow` contains public fields, so callers can form an ill-typed arrow. This
  is acceptable as syntax if all operations validate it, but should be made
  explicit; a checked backend handle or private constructor is safer.
- `NativeHol` currently uses `Kind = ()` and does not implement `TypeSystem`;
  this is a compatibility adapter, not yet the HOL-ω realization.
- Haskell-style monads, arrows, transformers, do-notation, and higher-level
  proof scripts should be a theory/API layer over this core, not methods added
  to the minimal `Logic` carrier.

## Nat API

### What is good

- `NatSyntax`, `NatArithmetic`, `NatOrder`, law groups, normalization, and
  equality decision are honest capabilities.
- Optional computation is represented by absence of an implementation.
- The blanket `Nat` facade preserves existing method and UFCS consumers.
- The native backend is split across the narrow traits and covered by tests.

### Risks and improvements

- The new traits still extend legacy `Hol` and return concrete
  `covalence_core::Result`; they are not backend-neutral in the same sense as
  `covalence-logic-api`.
- Syntax combines Peano structure and native `u64` literals. Literal injection
  should be its own capability, and eventually accept arbitrary natural
  values/bytes rather than imposing `u64`.
- Addition and multiplication are grouped. Separate capabilities may be useful
  for representations that cheaply support only one operation or for very
  small WIT surfaces.
- The law methods return whole closed theorem schemas with no typed statement
  witness. This preserves today's API, but future APIs should make the
  proposition shape inspectable and conformance-testable.
- There is not yet an `Iso`/interpretation API or a second backend, so the
  design goal of consilience has not been exercised.

## Inductive and aggregate API

### What was implemented

The portable syntax is a named sum of named products:

```text
F(X) = Σ constructor. Π field. (parameter | X)
```

- `RecordSpec<P>` is one named product.
- `VariantSpec<P>` is a non-recursive sum of products.
- `EnumSpec` is a non-empty sum of units.
- `PolynomialSpec<P>` permits parameter positions and direct occurrences of
  the functor variable.
- `FixpointSpec<P>` names a least or greatest fixpoint candidate.
- `InductiveFixpointBackend` and `CoinductiveFixpointBackend` are separate, so
  a backend can support `μF` without pretending to support `νF`.
- The older `InductiveSpec` converts structurally to and from `FixpointSpec`,
  keeping existing backends and consumers working.

### Why this is a good first representation

- Sum-of-products matches ordinary algebraic datatypes and the WASM component
  model's records, variants, and enums.
- Plain data is easy to compare, serialize, content-address, generate, and pass
  through WIT later.
- Direct recursive positions guarantee strict positivity by construction.
- A single description supports aggregate syntax and both fixpoint directions.
- Separating least/greatest backend traits makes partial implementations
  explicit.
- Existing sophisticated `InductiveTheory` contracts remain intact instead of
  being weakened to fit a premature universal bundle.

### Costs and current holes

- This is only a unary, first-order, direct-recursion polynomial language. It
  cannot yet express nested functors (`List (F X)`), composition, mutual
  recursion, indexed families, higher-order functors, or explicit parameter
  binders/kinds.
- Public fields and constructors permit invalid specs; validation is a
  convention. Validated newtypes/builders should make the safe path dominant.
- `FixpointSpec` has both a result name and a functor name without a stated
  identity/namespace rule.
- `RecordBackend`, `VariantBackend`, and `EnumBackend` return opaque bundles
  with no shared projections, injections, eliminators, extensionality laws, or
  round-trip proofs.
- The fixpoint backends likewise return opaque values. The API does not yet
  require `in : F X → X`, `out : X → F X`, their inverse laws, fold/unfold,
  induction/coinduction, or computation laws.
- Coinduction is therefore only a capability slot; no implementation or
  semantic conformance test exists.
- The old and new logic carrier traits coexist. This is a temporary migration
  state, not an intended permanent abstraction.
- Named field order is semantic in the plain data, but field permutation,
  structural record equivalence, and datatype isomorphism are not modeled.

### Recommended second iteration

1. Introduce validated `Polynomial`, `Record`, `Variant`, and `Fixpoint`
   wrappers; retain unchecked `*Spec` values for parsing and diagnostics.
2. Generalize positions into a small functor expression:

   ```text
   Zero | One | Param(P) | Var | Sum | Product | Compose
   ```

   Keep named sum-of-products as the ergonomic/WASM-facing normal form.
3. Define logic-generic aggregate bundles with constructors/projections or
   injections/case analysis and explicit beta/eta/extensionality laws.
4. Define `Fixpoint` bundles containing `in`, `out`, `in_out`, and `out_in`.
   Add `fold` plus induction for least fixpoints, and `unfold` plus coinduction
   for greatest fixpoints.
5. Adapt the existing `InductiveTheory` into the new least-fixpoint bundle.
   Do not replace its richer membership-relativized and paramorphism contracts.
6. Implement two representations of a small datatype and prove their
   isomorphism. Lists or binary naturals are the best first conformance target.
7. Move the shared carrier to `covalence-logic-api`; keep legacy `LogicOps` as
   an adapter until all consumers migrate.

## Review gates for the next extraction

- API crates depend only downward on vocabulary/data crates.
- Invalid specifications cannot reach a backend through the normal API.
- Every theorem-producing method documents its exact conclusion and evidence.
- Optional capabilities are traits, not flags paired with failing methods.
- At least two backends share one conformance suite.
- Compatibility code is visibly separate and carries a removal TODO.
- TODO and dependency deltas are attached to the commit or PR.
- TCB audit shows no unexplained mint-site or trusted-line increase.


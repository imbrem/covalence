# HOL Inductive Types

> **STATUS: PROPOSED — standalone implementation proposal, not committed.**
>
> This proposal designs a **datatype package for `covalence-hol`**:
> how to define recursive inductive types *inside HOL* while keeping
> `covalence-pure` as the trusted bottom layer. It is deliberately
> narrower than the repo's broader kernel/store proposals: the focus
> here is the shape of datatype introduction, recursion, induction,
> and later byte encodings.
>
> Read this with [`../stacked-pure-hol/README.md`](../stacked-pure-hol/README.md)
> and [`../stacked-pure-hol/next-stages.md`](../stacked-pure-hol/next-stages.md).
> Those documents explain the current **Pure as TCB, HOL as object
> layer** split; this proposal says how inductive types should fit
> inside that split.

## Read in this order

1. **This file** — direction, scope, and the main architectural choices.
2. **[`00-package-design.md`](./00-package-design.md)** — the concrete
   follow-on package design: accepted spec AST, elaboration pipeline,
   module placement, theorem bundle, and first milestones.

## 1. The short form

Implement inductive types in the **classic HOL package style**:

1. choose a hidden representation type inside HOL,
2. use `new_type_definition` to introduce the abstract datatype,
3. define constructors / cases / recursor by transport through `abs` / `rep`,
4. derive distinctness, injectivity, no-confusion, recursion, and induction as HOL theorems.

For this repo, that means:

- **implementation lives in `covalence-hol`, not `covalence-pure`;**
- **no new kernel primitives for datatypes;**
- **polymorphic datatypes first, bytes later.**

The first package should target generic datatypes like `option 'a` and
`list 'a` structurally. Canonical byte encodings come later, and only
for **closed concrete instantiations** such as `option bytes`,
`list bytes`, and `sexpr`.

## 2. Why this proposal exists

The current tree already has most of the kernel-side machinery a HOL
datatype package needs:

- `covalence-pure` has fresh abstract type introduction via
  [`Thm::new_type_definition`](../../../../crates/covalence-pure/src/thm.rs),
- fresh defined constants via
  [`Thm::define`](../../../../crates/covalence-pure/src/thm.rs),
- and fresh process-local type identities via
  `TypeKind::TyConObs`.

What it does **not** yet have is a design for the layer above that
machinery:

- what class of datatype specs the first package accepts,
- what hidden representation it uses,
- what theorem bundle it exports,
- and how bytes should interact with polymorphic recursive types.

This proposal fixes those choices explicitly.

## 3. The main decision

### 3.1 Polymorphic first

The first datatype package should be **polymorphic and structural**.

Examples:

- `option 'a`
- `list 'a`
- `sexpr` (monomorphic first, then possibly generalized later)

This is simpler than a bytes-first plan because a generic datatype like
`list 'a` does **not** come with a canonical byte encoding for `'a`.
If the package tries to be byte-backed from the start, it immediately
needs one of:

- per-parameter codec assumptions,
- monomorphic carve-outs,
- or a "bytes are secretly the real carrier" story that stops feeling
  honestly polymorphic.

The proposal chooses none of those for v1.

### 3.2 Bytes later

Bytes matter, but they should arrive as a **later codec layer**, not as
the hidden carrier of the generic datatype package.

The first byte-facing APIs should be added only for concrete closed
instantiations:

- `encode_option_bytes : option bytes -> bytes`
- `decode_option_bytes : bytes -> option (option bytes)`
- `encode_list_bytes : list bytes -> bytes`
- `decode_list_bytes : bytes -> option (list bytes)`
- `encode_sexpr : sexpr -> bytes`
- `decode_sexpr : bytes -> option sexpr`

That keeps the generic datatype package independent of any global
"every type has a canonical wire format" commitment.

## 4. Prior art and what we copy

The intended shape is the older HOL Light / HOL4 style, not the full
Isabelle BNF package.

### 4.1 HOL Light / HOL4 route

Use a hidden representation language, define the abstract type from it,
then derive the usual package theorems. This is the right v1 model for
Covalence because:

- it matches the existing `new_type_definition` and `define` hooks,
- it keeps the trusted surface flat,
- it yields the standard theorem bundle users expect,
- and it can be implemented as an ordinary HOL-layer elaborator.

### 4.2 Isabelle BNF route

Isabelle's modern package is more general and richer, especially for
nested recursion through registered functors. It is a useful **later**
reference point, but it is too heavy to be the first implementation
target here.

### 4.3 What we do not copy

We do **not** make datatypes kernel primitives.

That would grow the TCB for no gain: the existing Pure layer already
supports the conservative-extension story we need.

## 5. The representation strategy

The first package should elaborate datatype specs into a hidden
**structural representation universe** inside HOL.

This universe only needs enough structure to encode the accepted v1
specs:

- nullary constructors,
- constructor products,
- recursive self occurrences,
- type-parameter leaves,
- and previously-defined datatype applications at positive positions.

The package then:

1. synthesizes a hidden representation predicate `P`,
2. proves or synthesizes a witness theorem for `P x`,
3. invokes `Thm::new_type_definition`,
4. defines constructors and eliminators in terms of the returned
   `abs` / `rep`,
5. derives the theorem bundle.

For v1, the package should require at least one **non-recursive**
constructor. That keeps witness synthesis straightforward and matches
the simple route used by classic HOL packages.

## 6. Accepted and rejected spec shapes

### 6.1 Accept in v1

- single-family recursive datatypes
- strictly positive recursion
- polymorphic parameters
- constructors with zero or more fields
- fields built from products of:
  - parameters,
  - recursive occurrences,
  - previously-defined inductive families applied positively

Examples:

- `option 'a = NONE | SOME 'a`
- `list 'a = NIL | CONS 'a (list 'a)`
- `sexpr = ATOM bytes | CONS sexpr sexpr`

### 6.2 Reject in v1

- mutual recursion
- negative occurrences
- recursion under function space
- higher-order nested recursion requiring a BNF-style functor account
- quotient / codatatype / genuinely coinductive definitions

Those are later extensions, not part of the first package.

## 7. The exported theorem bundle

For each accepted datatype, the package should export a predictable
bundle of constants and theorems.

### 7.1 Constants

- the abstract type operator
- one constant per constructor
- a `case` constant
- a primitive recursor / iterator

### 7.2 Theorems

- constructor typing facts
- constructor distinctness
- constructor injectivity
- no-confusion / n-chotomy
- case-reduction equations
- recursion equations
- induction theorem

The public API is **constructor-first**. Users should reason through
this bundle, not through the hidden `abs` / `rep` representation.

## 8. Implementation placement

### 8.1 `covalence-pure`

No new datatype primitives.

The only Pure-layer requirements are the ones already present:

- `new_type_definition`
- `define`
- ordinary theorem derivation rules

### 8.2 `covalence-hol`

This is where the datatype package lives.

Responsibilities:

- parse / hold datatype specs,
- check strict positivity,
- elaborate to the hidden representation,
- generate witness terms,
- invoke Pure typedef / definition machinery,
- derive and package the theorem bundle.

### 8.3 Shell / serialization layers

No byte-level commitment in the generic datatype package. Byte codecs
are a separate layer that depends on the datatype package, not part of
its hidden representation.

## 9. Bytes as a second phase

Once the structural datatype package exists, add a second library layer
for **canonical codecs of closed datatypes**.

The first wire format should be simple and aligned with existing repo
utilities:

- constructor tag as unsigned LEB128,
- fields serialized in constructor order,
- recursive subvalues serialized recursively,
- `bytes` fields embedded as raw payload with explicit length framing.

This phase should reuse the existing unsigned LEB128 utilities in
[`crates/covalence-parse/src/leb128.rs`](../../../../crates/covalence-parse/src/leb128.rs).

Crucially, this is **not** a generic theorem of the datatype package.
It is a codec package for selected closed instantiations.

## 10. First concrete milestones

### Phase 1 — generic datatype package

Land the package itself and use it to define:

- `option 'a`
- `list 'a`
- `sexpr`

Acceptance criteria:

- constructors, cases, recursor, and induction theorem all generated,
- positivity checks reject unsupported shapes,
- users can prove simple functions like `map`, `length`, and `sexpr_size`
  from the generated recursion / induction package.

### Phase 2 — concrete byte codecs

Add codecs for:

- `option bytes`
- `list bytes`
- `sexpr`

Acceptance criteria:

- encode/decode round-trips,
- malformed encodings are rejected,
- equal values encode identically,
- unequal constructor shapes do not decode ambiguously.

## 11. Why this is the right first cut

This proposal keeps the hard parts in the right order:

- **first** get inductive types into HOL with a standard theorem package,
- **then** add bytes where the carrier story is already concrete.

That order fits the current tree better than a bytes-first route:

- `covalence-pure` already has the conservative-extension mechanisms,
- `bytes` already exists as a native carrier,
- but there is no generic per-type-parameter codec discipline yet.

The result is smaller, more honest, and easier to audit.

## 12. Open questions

- Whether `sexpr` should stay monomorphic over `bytes` permanently or
  later become parameterized over its atom carrier.
- Whether the hidden structural representation should be exposed as an
  internal library or generated ad hoc per datatype family.
- Whether nested positive uses of already-defined inductive families are
  part of v1 or deferred to v1.1.
- Whether the later codec layer should expose only `encode/decode`, or
  also a `valid_encoding_T : bytes -> bool` predicate inside HOL.

## Cross-references

- [`../stacked-pure-hol/README.md`](../stacked-pure-hol/README.md) —
  current Pure/HOL split this proposal builds on.
- [`../stacked-pure-hol/next-stages.md`](../stacked-pure-hol/next-stages.md) —
  current notes on `new_type_definition`, `TyConObs`, and follow-on work.
- [`../../../prover-architecture.md`](../../../prover-architecture.md) —
  the older kernel-facing architecture doc; useful contrast, but not the
  implementation target for this package.
- [`../../../../ARCHITECTURE.md`](../../../../ARCHITECTURE.md) and
  [`../../../../AGENTS.md`](../../../../AGENTS.md) —
  project-level constraints on TCB size, syntactic well-formedness, and
  bytes/blob usage.

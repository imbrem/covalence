# HOL Inductive Types: Package Design

> **STATUS: PROPOSED — implementation-oriented follow-on to**
> [`README.md`](./README.md).
>
> This document turns the main proposal into a concrete package shape:
> what input the first datatype package accepts, how it elaborates that
> input into HOL definitions, which modules should own each step, and
> what theorem bundle should be emitted.

## 1. Scope of this document

[`README.md`](./README.md) settles the architectural direction:

- datatypes are implemented in `covalence-hol`,
- `covalence-pure` remains unchanged as the trusted bottom layer,
- polymorphic structural datatypes come first,
- canonical byte codecs come later for closed concrete types.

This follow-on doc specifies the **first implementation cut**.

It does **not** attempt to solve:

- mutual recursion,
- full Isabelle-BNF-style nested recursion,
- quotients / codatatypes / coinduction,
- generic per-type-parameter codec abstraction.

## 2. The first user-facing surface

The package should accept a datatype specification that is explicit and
already type-checked at the syntactic level. The first surface does not
need parser sugar; a Rust data structure is enough.

Suggested shape:

```rust
pub struct DatatypeSpec {
    pub name: SmolStr,
    pub params: Vec<SmolStr>,
    pub ctors: Vec<CtorSpec>,
}

pub struct CtorSpec {
    pub name: SmolStr,
    pub fields: Vec<FieldSpec>,
}

pub enum FieldSpec {
    /// A datatype parameter, e.g. `'a`.
    Param(SmolStr),
    /// A recursive self occurrence, e.g. `list 'a` inside `list 'a`.
    Self_,
    /// A previously-defined positive type application, e.g.
    /// `option 'a` or `pair 'a bytes`.
    App { head: SmolStr, args: Vec<FieldSpec> },
    /// Binary product of fields. This is convenience syntax in the
    /// elaborator; the hidden representation can flatten it later.
    Product(Vec<FieldSpec>),
    /// Closed leaf carried by an existing HOL type, e.g. `bytes`.
    Closed(HolTypeRef),
}
```

That is intentionally narrow. The v1 package should operate on an AST
that already distinguishes:

- recursive self occurrences,
- parameter leaves,
- previously-defined positive applications,
- and closed leaves like `bytes`.

This keeps strict-positivity checking simple and local.

## 3. Admissibility checks

The package should reject unsupported shapes before generating any HOL
terms.

### 3.1 Required checks

- constructor names are distinct
- parameter names are distinct
- the datatype has at least one constructor
- at least one constructor is **non-recursive**
- every recursive occurrence is strictly positive
- no recursive occurrence appears under function space
- every referenced external type constructor is already known to the
  HOL layer

### 3.2 Deferred checks

The package should **not** attempt to infer or justify advanced
functoriality laws in v1. If a shape would require BNF-style machinery,
reject it.

That means the package can initially accept:

- `option 'a`
- `list 'a`
- `sexpr`

and reject examples like:

- `bad = K (bad -> bool)`
- mutually recursive families
- arbitrary recursion through not-yet-registered positive functors

## 4. Hidden representation strategy

The first package should elaborate each datatype into a hidden
representation expression over a small internal universe of HOL types.

The implementation does **not** need to expose this universe publicly.
It only needs enough structure to build the hidden predicate used by
`new_type_definition`.

### 4.1 Representation constructors

The internal representation language should support:

- `unit` for nullary constructors
- binary sums for constructor choice
- binary products for constructor fields
- parameter variables
- recursive knots

This is the classic HOL route: constructors are encoded by navigating a
sum-of-products representation, then transported into the abstract type
via `abs` / `rep`.

### 4.2 Witness generation

Because v1 requires at least one non-recursive constructor, the package
can synthesize a witness term directly:

- choose a non-recursive constructor,
- populate each of its non-recursive fields with canonical witnesses,
- build the corresponding representation value,
- prove the hidden predicate holds of that value.

This avoids needing the disjunct trick for datatype existence in the
first package implementation. The hidden predicate is inhabited by
construction.

## 5. Elaboration pipeline

The package should proceed in a fixed sequence.

### 5.1 Phase A: spec normalization

- flatten obvious product sugar
- resolve references to parameters vs self vs prior datatype heads
- assign constructor tags in declaration order

Output: a normalized datatype spec with explicit recursive structure.

### 5.2 Phase B: positivity and shape check

- walk every field
- ensure recursive occurrences stay in positive positions
- reject unsupported nested forms

Output: an admissible normalized spec.

### 5.3 Phase C: hidden representation synthesis

- build the sum-of-products representation type
- build the hidden predicate `P : repr -> prop`
- synthesize a witness `w : repr`
- derive a theorem `⊢ P w`

Output: representation type, predicate term, witness theorem.

### 5.4 Phase D: abstract type introduction

- call `Thm::new_type_definition` with the witness theorem
- obtain:
  - fresh type operator
  - `abs`
  - `rep`
  - the three basic typedef theorems

Output: the raw abstract datatype shell.

### 5.5 Phase E: constructor definition

For each constructor:

- define a representation-level constructor term
- transport it through `abs`
- introduce the public constructor constant with `Thm::define`

Output: one public HOL constant per constructor.

### 5.6 Phase F: eliminator and recursor definition

- define a `case` constant by analysis of the hidden representation
- define a primitive recursor / iterator from the constructor clauses
- expose both as ordinary HOL constants via `Thm::define`

Output: public eliminator and recursor.

### 5.7 Phase G: theorem derivation

Derive, package, and name:

- constructor distinctness
- constructor injectivity
- no-confusion / n-chotomy
- case reduction rules
- recursor equations
- induction theorem

Output: the public theorem bundle.

## 6. The exported Rust bundle

The elaborator should return a structured result, not a loose list of
theorems.

Suggested shape:

```rust
pub struct DatatypeBundle {
    pub spec: DatatypeSpec,
    pub ty: HolTypeRef,
    pub ctors: Vec<CtorBundle>,
    pub case_const: HolTermRef,
    pub recursor: HolTermRef,
    pub induction: HolThmRef,
    pub distinctness: Vec<HolThmRef>,
    pub injectivity: Vec<HolThmRef>,
    pub no_confusion: Vec<HolThmRef>,
    pub case_rewrites: Vec<HolThmRef>,
    pub recursor_rewrites: Vec<HolThmRef>,
}

pub struct CtorBundle {
    pub name: SmolStr,
    pub term: HolTermRef,
    pub typing: HolThmRef,
}
```

The package API should make the theorem categories explicit. Later
automation can consume these categories without re-discovering them by
name or shape.

## 7. Module placement

The implementation should stay in `covalence-hol`.

Suggested module split:

- `datatype/spec.rs`
  - `DatatypeSpec`, `CtorSpec`, `FieldSpec`
- `datatype/check.rs`
  - normalization and positivity checking
- `datatype/repr.rs`
  - hidden representation synthesis
- `datatype/build.rs`
  - typedef invocation, constructor/case/recursor definitions
- `datatype/theorems.rs`
  - distinctness, injectivity, induction, rewrite derivation
- `datatype/mod.rs`
  - public package API and `DatatypeBundle`

The important design line is:

- `covalence-pure` remains generic kernel machinery,
- `covalence-hol` owns datatype elaboration and theorem production.

## 8. The first three datatypes

### 8.1 `option 'a`

This is the smallest full package smoke test.

Requirements:

- two constructors (`NONE`, `SOME`)
- one recursive-free parameterized family
- case theorem
- recursor equations
- induction theorem

### 8.2 `list 'a`

This is the first recursive family.

Requirements:

- one nullary constructor (`NIL`)
- one recursive constructor (`CONS`)
- recursion equations sufficient to define `map`, `append`, and `length`
- induction theorem sufficient for ordinary list proofs

### 8.3 `sexpr`

This is the first monomorphic tree family tied to `bytes`.

Requirements:

- `ATOM bytes`
- `CONS sexpr sexpr`
- recursion theorem sufficient to define a size or fold function

`sexpr` is the natural bridge to the later byte-codec phase, but the
generic package should not special-case it.

## 9. Byte-codec follow-on boundary

The second phase should depend on `DatatypeBundle`, not on hidden
representation details.

That means the codec layer should:

- consume constructor order and field structure from the datatype spec,
- generate `encode_T` / `decode_T` over already-defined public
  constructors,
- prove codec theorems using the public recursion and induction bundle,
- avoid depending on the hidden `abs` / `rep` representation.

This keeps the datatype package and the codec package cleanly separate.

## 10. Test strategy

### 10.1 Package tests

- admissibility tests for accepted / rejected specs
- `option` theorem bundle smoke tests
- `list` recursion / induction smoke tests
- `sexpr` recursion smoke tests

### 10.2 Meta-properties

- generated constructors are distinct
- recursor equations specialize correctly
- induction theorem is strong enough to prove simple user functions
- public theorems do not expose raw hidden representation details

### 10.3 Codec tests later

- round-trip for `option bytes`
- round-trip for `list bytes`
- round-trip for `sexpr`
- malformed LEB128 / truncated payload rejection

## 11. Deferred extensions

Once the first package lands, the next likely extensions are:

- nested positive occurrences through a registered functor class
- mutual recursion
- a generic fold / map theorem family
- public package metadata suitable for simplifier integration
- byte codecs for more closed families

Those are follow-on projects, not blockers for the first implementation.

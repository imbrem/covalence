+++
id = "N005I"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-21T00:00:00+01:00"
source = "substrate-expression-consolidation"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Substrate expressions

This note is the focused design plan for expressions in the SQLite-backed
substrate. It refines maintainer sketches [`N0056`](../../plans/relational-design.md)
and [`N005H`](../../plans/covalence_substrate_design.md). It does not modify
those source notes.

## The boundary

An expression is syntax with a sort and a finite set of typed inputs. It does
not read SQLite, select rows, or mint a theorem. A separate environment assigns
values to its inputs; evaluation is partial and returns a value of the declared
sort.

```text
Expression E : (inputs Γ) -> sort T
Environment ρ satisfies Γ
evaluate(E, ρ) : Result<T, DecodeError>
```

Keep four objects distinct:

| Object | Responsibility |
|---|---|
| SQLite schema | Physical tables, columns, storage classes, constraints, keys. |
| expression context `Γ` | Typed slots an expression may reference. |
| representation | Partial decoding from a SQLite value or identity into a substrate value. |
| table interpretation | Binds slots to table columns and quantifies the resulting row predicate. |

Call only the first object a **schema**. Use **context** for expression inputs
and **interpretation** for the checked connection between a table and a context.
This avoids confusing the existing `Expr<Ctx>` schematic-rule idea with SQLite
schema metadata.

## Minimal semantic core

The first expression language needs only:

- `Val<T>(value)`: a closed value;
- `Slot<K, T>`: a typed input identified by a stable key;
- `App<F, A>`: application of a typed operation;
- products needed to supply multi-argument operations.

`Col` should not be an expression constructor. It belongs to a table
interpretation, which binds a `Slot` to `(column, representation)`. This keeps
the same expression usable against SQLite rows, proton values, WASM resources,
or another database representation.

The core judgements are:

```text
Γ |- E : T
ρ : Γ
eval(E, ρ) = v : T
```

Ground expressions have an empty context. Open expressions cannot become
ordinary theorem propositions until their slots are bound, instantiated, or
quantified by a checked rule.

## Two representations, one meaning

Define a small dynamic expression tree first. It has stable sort, operation,
and slot identifiers; validates itself against a dynamic context; serializes
canonically; and is suitable for SQLite and WASM boundaries. This is the audit
reference and independent replay format.

A Rust generic façade may represent the same judgement using associated types:

```rust
trait Expr {
    type Context;
    type Sort;
}
```

The façade is valuable for compile-time construction and zero-cost closed
expressions, but its type machinery must not define the persisted semantics.
Provide checked lowering from the typed façade to the dynamic tree and test
that both evaluators agree. Do not put arbitrary Rust `TypeId` values in the
durable format; use stable substrate identifiers.

The older `HasVar<V>` proposal becomes an optional analysis. The authoritative
operation is `inputs(E)`, computed from the dynamic tree. A type-level
`Contains<K>` or finite context can conservatively accelerate construction,
but correctness never depends on compiler-specific constexpr or `TypeId`
behavior.

## Representations and failure

A representation is a named partial decoder:

```text
decode : SqlValue -> Result<T, DecodeError>
```

It declares its accepted SQLite storage classes and additional predicates.
Examples include signed integer, UTF-8 text, blob bytes, `Def<T>`, and
`Use<Source,T>`. `NULL` is absence and is accepted only by an explicit optional
representation.

The initial policy is fail-closed:

- validating an interpretation checks every slot binding and required schema
  condition;
- evaluating a row that cannot decode produces no theorem;
- a trusted `All` transition rejects the batch if any relevant row fails;
- untrusted imports retain failures in a rejection report;
- epsilon totalization, if useful later, is an explicit derived representation.

This preserves the useful layering: decidable schema/decoder validation first,
general theorem reasoning second.

## From expressions to table facts

A table interpretation contains:

```text
table identity
expression context Γ
slot -> (column, representation) bindings
row predicate P : Expr<Γ, bool>
visibility/provenance scope
```

After binding a row, `P` is a ground proposition. Table-level claims are
quantifiers over those propositions:

- `All(I)`: every current row decodes and satisfies `P`;
- `Any(I)`: some row decodes and satisfies `P`, carrying a row witness;
- `NotAll(I)`: some row decodes and refutes `P`, carrying a counterexample;
- `NotAny(I)`: every current row decodes and refutes `P`.

These are facts about a particular snapshot unless accompanied by a checked
invariant preserved across mutations. They are not a four-valued truth system:
they are ordinary quantified propositions with different evidence.

For an open-world relation, stored rows establish positive membership only.
Absence becomes negative information only with explicit completeness evidence.
Do not conflate that completeness with `NotAny` for a current finite table.

## Identity-bearing representations

`Def<T>` and `Use<Source,T>` extend decoding with an identity environment:

- `Def<T>` associates a physical key with one erased substrate value of `T` in
  a declared scope;
- `Use<Source,T>` resolves a key through that source scope;
- the same physical column interpreted under different types or scopes denotes
  independent maps;
- a missing use is a decoding failure;
- a conflicting definition is a mutation error unless checked equality proves
  the denotations equal.

This identity environment is nucleus state. It should be modeled independently
of SQL uniqueness: a UNIQUE constraint can help validate a representation, but
does not itself establish semantic equality or theorem authority.

## Theorem boundary

Rows and expression evaluations are evidence, not theorem constructors. The
nucleus may issue an `MThm` only through a named checked transition that records:

1. the expression and context;
2. the environment or table interpretation;
3. decoder/schema validation;
4. the quantified claim and its evidence;
5. the language/rule authority used;
6. the neutron generation and provenance.

Schematic rules use the same open-expression mechanism, but instantiation is a
separate checked operation. Database slots are not HOL variables, binders, or
metavariables merely because all are represented by contexts.

## First executable slice

Use a tiny monomorphic model rather than the complete future API:

```text
Tm(id INTEGER PRIMARY KEY)                  -- Def<Term>
App(tm INTEGER, lhs INTEGER, rhs INTEGER)   -- Uses of Tm
HasTy(tm INTEGER, ty INTEGER)               -- candidate and trusted copies
```

Implement, in order:

1. dynamic sorts, stable slot IDs, context checking, `Val`/`Slot`/`App`;
2. SQLite values and partial representations, including explicit optionality;
3. table interpretations and row binding;
4. `All` and `Any` evidence, then their negative duals;
5. `Def`/`Use` resolution and conflict-checked insertion;
6. a typed Rust façade lowering to the dynamic expression;
7. identical evaluation in SQLite and a tiny in-memory interpreter;
8. one checked promotion from candidate `HasTy` rows into trusted state.

The slice is accepted when malformed rows are rejected deterministically,
typed and dynamic evaluation agree, a forged `Def` collision cannot be
promoted, and the same logical `HasTy` fact can be witnessed by proton and
neutron representations.

## Decisions intentionally deferred

- whether contexts are type-level lists, rows, or generated marker types in
  the ergonomic Rust façade;
- general dependent sorts or substrate polymorphism;
- generated columns, collations, floating arithmetic, and recursive SQL;
- epsilon representations;
- canonical binary encoding and content hashes;
- whether a future e-graph shares the dynamic expression encoding;
- performance-oriented interning and static input-set approximations.

None is needed to test the semantic boundary above.

# 02 — Egglog Python API

[`egglog-python`](https://github.com/egraphs-good/egglog-python) is a
typed Python wrapper over the egglog Rust crate, maintained by the
egglog team. It's also one of the most polished surface languages on
top of egglog — typed sorts via `Expr` subclasses, decorator-based
function/constructor declaration, fluent rule builders, and static
type checking via `mypy`. Reviewing it serves two purposes:

1. **It tells us what shape an "egglog-style" Python API on top of
   Covalence should take**, when we want users to author proofs in
   the egglog idiom against our kernel rather than against external
   egglog.
2. **It's the obvious ingestion path** for users already using
   `egglog-python` for program optimisation who'd like to take the
   results as theorems in Covalence.

This file documents the API; it does not yet propose a port — that
sits in [`03-integration-plan.md`](./03-integration-plan.md).

## API surface

### Sorts

A sort is a Python class subclassing `Expr`:

```python
from egglog import *

class Math(Expr):
    pass

# or, with an explicit egglog name:
class Math(Expr, egg_sort="Math2"):
    pass
```

Parameterised sorts use generic typing:

```python
MyMap = Map[i64, String]
MyMap.empty().insert(i64(1), String("one"))
```

### Constructors and functions

Decorator-based:

```python
@function
def fib(n: i64Like) -> i64: ...

@function(egg_fn="foo", cost=10, merge=lambda old, new: old.max(new))
def my_foo() -> i64: ...
```

`i64Like` is a union alias `i64 | int` so Python literals upcast.

The wrapper picks `function` vs `constructor` automatically: if the
return type is a builtin, it's a `function`; if it's an eqsort and
there's no `merge`, it's a `constructor`; if there's a `merge`, it's
always a `function`.

Datatype constructors are methods of the sort:

```python
class Math(Expr):
    @method(egg_fn="Num")
    def __init__(self, v: i64Like): ...

    @method(egg_fn="Var")
    @classmethod
    def var(cls, v: StringLike) -> Math: ...

    @method(egg_fn="Add")
    def __add__(self, other: Math) -> Math: ...

    @method(egg_fn="Mul")
    def __mul__(self, other: Math) -> Math: ...
```

Class-level `ClassVar` declarations correspond to `(declare …)`:

```python
class Boolean(Expr):
    TRUE: ClassVar[Boolean]
FALSE = constant("False", Boolean)
```

Relations are explicit:

```python
edge = relation("edge", i64, i64)
edge(i64(1), i64(2))
```

### Rules and rewrites

Pattern variables are typed up front:

```python
f0, f1, x = vars_("f0 f1 x", i64)
egraph.register(
    rule(
        eq(f0).to(fib(x)),
        eq(f1).to(fib(x + 1)),
    ).then(set_(fib(x + 2)).to(f0 + f1))
)
```

Or via the function-scoped form:

```python
@egraph.register
def _math(a: Math, b: Math):
    yield rewrite(a * b).to(b * a)
    yield rewrite(a + b).to(b + a)
```

Rewrites use a fluent builder:

```python
rewrite(a + b).to(b + a)
rewrite(a + b).to(b + a, eq(a).to(zero))   # conditional
birewrite(a + b).to(b + a)
```

Rulesets:

```python
path_rs = ruleset(rule(edge(x, y)).then(path(x, y)), name="path_rs")
egraph.run(10, ruleset=path_rs)
```

### Actions

| egglog | Python |
|---|---|
| `(let x e)` | `let("x", e)` |
| `(set (f a) v)` | `set_(f(a)).to(v)` |
| `(union a b)` | `union(a).with_(b)` |
| `(delete (f a))` | `delete(f(a))` |
| `(panic "msg")` | `panic("msg")` |

All actions are first-class values passed to `egraph.register(...)`.

### Running, checking, extracting

```python
egraph.run(5)
egraph.run(1000, fib(7))            # until fib(7) is derivable
egraph.run(10, ruleset=path_rs)
egraph.check(eq(a).to(b))           # fails if not derivable
egraph.extract(expr)                # lowest-cost representative
egraph.simplify(schedule, expr)
```

### Schedules

```python
run(limit=10, ruleset=path_rs, *until)
saturate(s)
seq(s1, s2)
repeat(n, s)
```

### Built-ins

Python classes are provided for `i64`, `f64`, `String`, `Unit`,
`Bool`, `Map`, `Vec`, `Set`, `Rational`, `BigInt`, `BigRat`, with
Python-operator overloads (`+`, `*`, `>>`, …) that round-trip to the
egglog operators.

### Proofs

The wrapper exposes the low-level `Prove`, `ProveExists`, and
`ProveExistsOutput` commands as bindings. The high-level Python
workflow for proof extraction is incomplete upstream — there's no
`egraph.prove(...)` analogue yet. The plumbing is there if we want to
drive it from Rust via the same Rust API.

## What this looks like as a Covalence frontend

The egglog-python API is essentially **a DSL for building an `Egraph`
and triggering rule fixpoints over it**. Mapping it onto Covalence:

| egglog-python construct | Covalence equivalent (sketch) |
|---|---|
| `class Math(Expr)` | A sort registered with the host `Egraph`'s arena — a fresh `SortId`. |
| `@function` / `@method` | A constructor `TermDef::App(ctor_id, args)` whose ctor is interned. |
| `vars_("a b c", T)` | Pattern variables, freshly named in a per-rule scope. |
| `rewrite(lhs).to(rhs, *when)` | A kernel rewrite: match `lhs` in the arena under σ, build `rhs` under σ, `EThm::union`. |
| `rule(*premises).then(*actions)` | A general rule: each premise is a pattern match; each action is a kernel op. |
| `egraph.register(...)` | Mutating call on a `covalence-egglog` runner that wraps an `Egraph` + scheduler. |
| `egraph.run(N)` | The runner's saturation driver, calling `EThm` rule methods for each firing. |
| `egraph.check(eq(a).to(b))` | `EThm::eq(a_ref, b_ref)`. |
| `egraph.extract(expr)` | Cost-model extractor over the arena. |

A Python wrapper that hits these endpoints would live in
`packages/` (or in `crates/covalence-python` as PyO3 bindings — see
`covalence-python` for the existing pattern). It would mirror the
egglog-python decorators verbatim where we can match semantics, and
mark unsupported features with clear `NotImplementedError`s rather
than silent divergence.

## Where the egglog-python API and our kernel disagree

* **Reflexivity.** egglog-python (like egglog) requires the term to
  be added before `t = t` holds. Our kernel agrees.
* **Mutability.** egglog-python's `EGraph` is a mutable handle; our
  `EThm` is a value type whose mutation is method-bound. This is
  surface-level — both expose the same fixpoint API.
* **Static typing.** egglog-python leans hard on Python type hints to
  catch arity / sort mismatches at edit time. We'd want the same at
  the wrapper layer; the kernel itself stays dynamically sort-checked.
* **Proofs.** egglog-python today only exposes low-level proof
  commands. Covalence's wrapper would expose `egraph.thm()` returning
  an `EThm` — *that* is the difference, and the whole point of the
  exercise.
* **Containers.** egglog-python supports `Map`, `Vec`, `Set`. Our
  Phase 1–2 wouldn't; we'd raise `NotImplementedError` on container
  ops until we either add them to the kernel or admit them as Fiat
  oracles.

## Pre-existing crates of interest

* [`covalence-python`](../../../../crates/covalence-python) —
  PyO3 0.28 bindings. Reuses the same plumbing we'd want for an
  egglog-style Python frontend.
* [`covalence-sexp`](../../../../crates/covalence-sexp) — already
  has a dialect mechanism; an egglog parser would add an
  `EgglogDialect` next to `CovalenceDialect`, `SmtLibDialect`,
  `WatDialect`.

## References

* [`egglog-python` docs index](https://github.com/egraphs-good/egglog-python/blob/main/docs/index.md)
* [`egglog-python` translation reference](https://github.com/egraphs-good/egglog-python/blob/main/docs/reference/egglog-translation.md) — the source for most of this file
* [`egglog-python` GitHub](https://github.com/egraphs-good/egglog-python)

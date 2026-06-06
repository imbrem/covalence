# 00 — Egglog foundations

What an egglog program *is* semantically, in enough detail to design
ingestion and a native frontend on top of Covalence's kernel.

## The slogan

> **Egglog = e-graphs + Datalog.**
>
> An e-graph is a database whose rows can be unioned. Egglog is the
> Datalog-style rule engine that drives that database to a fixpoint.

If you only know `egg`: the e-graph is the same congruence-closed
union-find over a term language. What changes is that the *driver* —
the thing that decides which rewrites to fire — is now a relational
fixpoint over the e-graph's function tables, not a hand-rolled
scheduler. This buys faster pattern matching, e-class analyses as
first-class rules, and uniform incremental ("seminaive") evaluation.

If you only know Datalog: egglog programs are Datalog programs whose
*values* are e-class identifiers, and whose function tables are
quotiented by an equality relation that the engine maintains
automatically via congruence closure. The merge step at the end of
each iteration is congruence rebuild.

## The three data structures

An egglog state is a triple **(sorts, tables, UF)**:

1. **Sorts.** Either an *eqsort* (a user datatype whose values are
   e-classes), or a *primitive sort* (`i64`, `f64`, `String`, `Bool`,
   `Unit`, plus containers `Map`, `Vec`, `Set`, and big-number sorts
   `BigInt`, `BigRat`). Primitive-sort values are not e-class IDs;
   they are themselves.
2. **Tables.** Each declared function `f : A₁ × … × Aₙ → R` is a
   table whose rows are `(a₁, …, aₙ) ↦ r`. The arity tuple is the
   key. For an eqsort `R`, `r` is an e-class ID. For a primitive
   `R`, `r` is a primitive value.
3. **Union-find.** A union-find over e-class IDs. Two terms are
   equal iff their root e-class IDs are equal.

Three flavours of function correspond to three table shapes:

| egglog form | shape | what the table stores |
|---|---|---|
| `(constructor f (A …) R)` where `R` is an eqsort | rows have an e-class ID on the right | each invocation `(f a …)` adds a row mapping the arg-tuple to a fresh e-class ID (subject to congruence collapse) |
| `(function f (A …) R [:merge expr])` | rows have a primitive (or eqsort) on the right with a **merge** policy | inserting a conflicting row triggers the `merge` expression to combine old and new |
| `(relation f (A …))` | desugars to `(function f (A …) Unit)` | a Datalog-style predicate |

A `(datatype Math (Num i64) (Add Math Math))` block is sugar that
declares the sort `Math` and two constructors whose return type is
`Math`.

## Congruence closure, restated

When `(f a b) = c` and `(f a' b') = c'` are both rows of `f`'s table,
and `a = a'` and `b = b'` hold in the union-find, the engine unions
`c` with `c'` and rebuilds. This is the same congruence rebuild as
`egg`, but expressed as a join over `f`'s table — which makes it the
same shape as any Datalog rule.

### Reflexivity is NOT free

A subtle but load-bearing detail: **egglog does not assume
reflexivity**. A proof of `t = t` only exists if `t` was added at
the top level (or built up via congruence from such terms). This
mirrors a chase: only ground terms that the program actually mentions
exist in the database. Our Covalence kernel takes the same line —
`refl` is a rule that builds `Eq(t,t)` in the arena and unions it
with `truth` only after the caller has decided `t` is interesting
([`eprop.rs:117`](../../../../crates/covalence-kernel/src/eprop.rs#L117)).

## Rules and actions

A rule has the form

```
(rule (premise₁ premise₂ …) (action₁ action₂ …) :ruleset R :name N)
```

* A **premise** is a *fact*: either an equality `(= pat₁ pat₂)`, or a
  pattern call `(f arg₁ …)` that asserts there is *some* row of `f`
  matching that shape. Pattern variables are local to the rule.
* An **action** is any of the top-level state-mutating operations:
  `let`, `set`, `union`, `delete`, `subsume`, `panic`, or a bare
  expression (which forces the constructor evaluation).

When the engine fires the rule, it finds every substitution `σ` that
satisfies all premises in the current database, then executes the
actions under `σ`.

### Rewrites are sugar for rules

`(rewrite lhs rhs)` desugars to roughly

```
(rule ((= x lhs)) ((union x rhs)))
```

where `x` is a fresh variable. `(rewrite lhs rhs :when (guard…))`
adds the guards as additional premises. `(birewrite lhs rhs)` emits
two rewrites, one each direction.

This sugar is the key bridge to our kernel: a kernel-checkable rewrite
is exactly an `EThm` method that, given a substitution, matches
`lhs` in the egraph and unions it with `rhs`. The egglog "fire all
rules to fixpoint" loop becomes "iterate rule firings until no new
unions appear".

## Saturation semantics

A `(run N)` step performs *N* iterations of:

1. **Match.** For each rule, find every new substitution since the
   last iteration (this is the **seminaive** trick: only join against
   rows added since the previous round, which collapses an O(n²) scan
   to O(Δn · n)).
2. **Stage actions.** Buffer the unions, sets, and inserts. Crucially,
   the rule body runs against the *old* database — staged effects
   are not visible to other rule firings in the same iteration.
3. **Rebuild.** Apply staged effects, run congruence closure to
   fixpoint, recompute canonical e-class IDs for every table.

If iteration *k+1* produces no changes, the database is *saturated*
for that ruleset. The `saturate` schedule combinator runs until
saturation; `(repeat n s)` runs `s` *n* times; `(seq s₁ s₂ …)` runs
in sequence; `(run R)` runs ruleset `R` once.

`(run N :until P)` adds an early-exit check: stop as soon as the
fact `P` is provable.

## Merge functions

For a `(function f (…) R :merge (combine old new))`, when a new row
collides with an existing one, the engine inserts
`(combine old new)` instead of either. This is how egglog encodes
*lattice-valued* e-class analyses inside the same machinery as
equality saturation — the classic example is interval analysis where
`combine` is the lattice meet.

For an eqsort `R`, a constructor row collision is resolved by
unioning the two e-class IDs (rather than by a merge function). For
a relation (`R = Unit`), there's nothing to merge.

## What egglog *isn't*

* **Not a theorem prover.** It can saturate equalities and report
  what holds, but the saturation may not terminate, and there's no
  "I tried everything and it doesn't hold" answer in finite time.
  `check` answers "does this hold in the current database?", not
  "is this a consequence of the rules?".
* **Not a confluent rewriter.** The `merge` and `union` actions can
  collapse e-classes in any order; the saturation result depends on
  the choice of rules, not on a normal form.
* **Not a higher-order rewriter.** All binders must be encoded as
  explicit terms (de Bruijn or named with a side-table). This is
  exactly what HOL Light proofs that target an e-graph do, and it's
  why our kernel keeps lambda an explicit `TermDef` variant.

## The 2.0 proof system

Egglog 2.0 ships a proof module
([`src/proofs/`](https://github.com/egraphs-good/egglog/tree/main/src/proofs))
that, when the program belongs to the proof-encodable fragment, can
reconstruct an explicit justification DAG for any equality the engine
established. The shape of a proof:

```rust
// from egglog 2.0 src/proofs/proof_format.rs
pub struct Proposition { pub lhs: TermId, pub rhs: TermId }

pub struct Proof {
    proposition: Proposition,
    justification: Justification,
}

pub enum Justification {
    Fiat,                                   // top-level `let` / `union` / primitive `2 = 2`
    Rule { name, premise_proofs, substitution },
    MergeFn { function, old_proof, new_proof },
    Trans(ProofId, ProofId),
    Sym(ProofId),
    Congr { proof, child_index, child_proof },
}
```

A `ProofStore` is a hash-consed arena of `Proof` nodes, indexed by
`ProofId`. Proofs are extracted via the low-level commands `prove`
and `prove-exists`, which materialise a proof term in a special
table and let the host walk it.

Whether a program is proof-encodable is checked statically with
`program_supports_proofs` / `command_supports_proof_encoding`. The
egglog 2.0 docs describe the proof API as "read-only proof
reconstruction"; not every feature (notably some scheduler and
container operations) is in the supported fragment.

### Why this matters for us

Our kernel already has the matching axioms:

| egglog `Justification` | Covalence kernel rule |
|---|---|
| `Fiat` | seed assumption — caller built `t` and either declared `union(t, t')` or `set` |
| `Rule { name, premise_proofs, substitution }` | a kernel-checked rule (rewrite, congruence, theory) instantiated at `substitution`, with the premise sub-proofs as inputs |
| `MergeFn { function, old, new }` | a user-supplied rewrite `(combine old new)` on the merge-function's body, applied via `cong` + `subst` |
| `Trans` | `EThm::trans` (Phase P4) |
| `Sym` | `EThm::sym` (Phase P3 list) |
| `Congr { proof, i, child_proof }` | `EThm::cong` with the i-th subterm substitution |

So Layer A — replaying egglog proofs through `EThm` — reduces to:
parse the `ProofStore`, walk the DAG, dispatch each `Justification`
variant to the matching `EThm` method. The whole egglog runtime
becomes an untrusted oracle.

## References

* [egglog repo](https://github.com/egraphs-good/egglog) — README, source
* [egglog tutorial](https://egraphs-good.github.io/egglog-tutorial) — basics, rewrites, Datalog
* [`src/proofs/proof_format.rs`](https://github.com/egraphs-good/egglog/blob/main/src/proofs/proof_format.rs) — the canonical proof shape
* [Zhang, Wang, Willsey, Tatlock — PLDI 2023](https://mwillsey.com/papers/egglog) — the paper
* `docs/prop-egraph-design.md` — Covalence's matching e-graph kernel
* `crates/covalence-kernel/src/eprop.rs` — the `EThm` API our integration targets

# 01 — Egglog command language

The full surface syntax of egglog 2.0, grouped by purpose, with a
column for **how each construct lands in Covalence**:

* **K** = *kernel-mappable*. Layer B (native frontend) can compile
  this to one or more `EThm` rule calls without an external oracle.
* **P** = *proof-supportable*. Layer A (oracle replay) can ingest
  egglog's `Justification` for this construct via the 2.0 proof API.
* **O** = *oracle-only*. We can run it through external egglog, but
  there is currently no proof encoding; ingestion either drops the
  result or admits it.
* **—** = *not applicable* (I/O, debug, control flow).

The command list is taken from
[`egglog/src/ast/parse.rs`](https://github.com/egraphs-good/egglog/blob/main/src/ast/parse.rs)
at 2.0, which is the authoritative source.

## A. Declarations — sorts, functions, datatypes

| Command | Syntax | Status | Notes |
|---|---|---|---|
| `sort` | `(sort Name)` or `(sort Name (Container T₁ …))` | **K** | An eqsort name. Container variant declares a parameterised sort (`(sort M (Map i64 String))`). Layer B: maps to a kernel `Sort` registry per `Egraph`. |
| `datatype` | `(datatype Name (Ctor₁ A …) (Ctor₂ B …) …)` | **K** | Sugar: declares the sort and one constructor per variant. |
| `datatype*` | `(datatype* (Name₁ Ctors₁) (Name₂ Ctors₂) …)` | **K** | Same, but with mutually recursive sorts. |
| `function` | `(function f (A …) R :merge expr)` or `(function f (A …) R :no-merge)` | **K** if `:no-merge` and pure congruence; **P+O** if `:merge` non-trivial | The `:merge` form gates the `MergeFn` justification — supported in egglog's proof encoding. Layer B requires the merge expression to itself be a kernel-checkable rewrite. |
| `constructor` | `(constructor f (A …) R)` or with `:cost N` or `:unextractable` | **K** | The common case. `:cost` only affects extraction, not soundness. `:unextractable` marks the constructor as a non-extractable target. |
| `relation` | `(relation p (A …))` | **K** | Sugar for `(function p (…) Unit)`. Datalog-style predicate. |
| `declare` | (sugar in `datatype` block, no top-level command) | **K** | Nullary function — a named constant of some sort. |

**Where Layer B touches the kernel.** Today's `Arena` knows about the
HOL term language, not arbitrary user sorts. To accept user `(sort
…)` declarations, the egraph needs a thin **schema layer** on top:
either (a) a separate `RelationStore` parallel to `Arena` that holds
relation rows keyed by argument tuples and pointing to `TermRef`s
(for eqsorts) or primitive values, or (b) encode every user-defined
constructor as a fresh `TermDef::App(ctor_id, args)` and let the
existing union-find do the work.

Option (b) is simpler and stays within the existing TCB if `ctor_id`
is just a name interned into the arena. The relation-store option
(a) is needed once we start joining over arbitrary predicates rather
than just rewriting equalities. Phase 3 picks this up.

## B. Rules

| Command | Syntax | Status | Notes |
|---|---|---|---|
| `rule` | `(rule (premise …) (action …) :ruleset R :name N)` | **K** for kernel-checkable premise/action pairs; **P** when egglog encodes the rule's firing | A premise is a pattern fact; an action is a state mutation. Layer A: each rule firing becomes a `Justification::Rule { name, premise_proofs, substitution }`. |
| `rewrite` | `(rewrite lhs rhs :when (g …) :ruleset R)` | **K**, **P** | Desugars to a `rule` with `(= x lhs)` premise and `(union x rhs)` action. The base case for our integration. |
| `birewrite` | `(birewrite lhs rhs :when (…))` | **K**, **P** | Two rewrites. |
| `ruleset` | `(ruleset R)` | **—** (scheduling sugar) | Declares a ruleset name. |
| `unstable-combined-ruleset` | `(unstable-combined-ruleset R R₁ R₂ …)` | **O** | Combines rulesets; not load-bearing for correctness. |

**Layer A trust model for `Rule`.** A `Justification::Rule { name,
premise_proofs, substitution }` only proves anything *given* that
the rule body is sound. Our replay path must therefore have a
catalog mapping `name -> RuleHandler`, where the handler is either:

1. a built-in kernel rule (refl, sym, trans, cong, …) — replay
   directly, trusted;
2. a user-declared rewrite that desugars to "build LHS under σ,
   build RHS under σ, union them" — replay via `EThm` build + union,
   trusted;
3. a user-declared `rule` with an arbitrary action body — the
   handler needs to encode each action as a kernel step; if it can't,
   replay fails and we either drop the equality or admit it.

Most real egglog programs stick to (1)+(2). Programs that use
non-trivial `set`/`delete`/`subsume` actions are outside the Layer A
fragment and become Layer B targets.

## C. Actions (top-level and inside rule bodies)

| Action | Syntax | Status | Kernel mapping |
|---|---|---|---|
| `let` | `(let x expr)` | **K**, **P** (`Justification::Fiat`) | Allocate `expr` in the arena, bind the e-class as a named term. |
| `set` | `(set (f a …) v)` | **K** for primitive sorts via merge; **P** | Insert / overwrite a row of `f`. For eqsort `R`, semantically equivalent to `(union (f a …) v)`. |
| `union` | `(union a b)` | **K**, **P** (`Fiat` at top level; from `Rule` inside a body) | Direct `Egraph::uf.union(a, b)` in Layer B; in Layer A this is the conclusion of a `Rule`-justified step. |
| `delete` | `(delete (f a …))` | **O** | Drops a row. Has no `Justification` — proof-encoding programs cannot delete. Layer B can support it but the resulting state is no longer monotonically growing, breaking the egraph-as-conclusion view. |
| `subsume` | `(subsume (f a …))` | **O** | Marks a row as no-longer-extractable. Affects extraction only; soundness-irrelevant. |
| `panic` | `(panic "msg")` | **—** | Aborts. Treat as a kernel `Result::Err`. |
| bare expr | `(f a …)` | **K**, **P** (`Fiat`) | Evaluates the expression, forcing its row into the table. |

**`delete` and `subsume` are why egglog and HOL are not the same
object.** In our kernel, a `Thm` is *monotone* — once a union holds
in the UF, no rule can take it back, and that monotonicity is what
makes `eq` queries sound. Egglog drops this guarantee in favour of
program-optimisation use cases. For our purposes the proof-encodable
fragment is exactly the monotone fragment, which is fine.

## D. Execution

| Command | Syntax | Status | Notes |
|---|---|---|---|
| `run` | `(run N)` or `(run R N)` or `(run R N :until (fact …))` | **K**, **P** | Layer B: iterate match-then-apply until *N* steps or no change. Layer A: not transmitted as a justification — proofs are extracted *after* a run. |
| `run-schedule` | `(run-schedule s)` | **K**, **P** | Top-level schedule runner. |
| `saturate` | `(saturate s)` | **K** | Schedule combinator: run `s` until fixpoint. |
| `seq` | `(seq s₁ s₂ …)` | **K** | Sequential composition. |
| `repeat` | `(repeat n s)` | **K** | Iterated. |

Schedules are pure control flow over rule firings; they have no
direct proof content. The proof DAG just contains whichever
`Justification::Rule` nodes fired.

## E. Querying

| Command | Syntax | Status | Notes |
|---|---|---|---|
| `extract` | `(extract expr)` or `(extract expr N)` | **K** for kernel-cost extraction; **O** otherwise | Returns the lowest-cost term in the e-class of `expr`. Layer B: an extractor over `Egraph`. Has no proof content (extraction is "compute the best representative", not "prove an equality"). |
| `check` | `(check (fact …))` | **K**, **P** when proof-supportable | Asserts that all facts hold in the current database. Layer A: `(check (= a b))` triggers a proof extraction for `a = b`. |
| `simplify` | `(simplify schedule expr)` | **K** | Sugar: `run` the schedule, then `extract expr`. |
| `query-extract` | covered by `check` + `extract` | **K** | (Removed in 2.0 as a separate command; was sugar.) |

## F. Proofs (2.0)

| Command | Syntax | Status | Notes |
|---|---|---|---|
| `prove` | `(prove (= a b))` | **P** | Materialise a proof DAG for the equality `a = b` if one exists. The host then walks the `ProofStore` via the `Justification` API. |
| `prove-exists` | `(prove-exists Ctor)` | **P** | Materialise a proof that an e-class of constructor `Ctor` exists. |

These are the entry points for Layer A. The proof DAG is the
`ProofStore` documented in
[`src/proofs/proof_format.rs`](https://github.com/egraphs-good/egglog/blob/main/src/proofs/proof_format.rs).

**Eligibility.** Not every program supports proof extraction. egglog
exposes `program_supports_proofs(prog) -> Result<(), Reason>` to
check ahead of time. Programs that use `delete`, certain container
operations, or unsupported scheduler features fall outside the
encodable fragment. Layer A's first job after parsing is to call
this checker and reject (with a diagnostic) anything we can't replay.

## G. Stack and modularity

| Command | Syntax | Status | Notes |
|---|---|---|---|
| `push` | `(push)` or `(push n)` | **K** | Save the current state. Maps to cloning the `Egraph` (cheap-ish; arena + UF are owned). |
| `pop` | `(pop)` or `(pop n)` | **K** | Restore. |
| `include` | `(include "file.egg")` | **—** | File inclusion. Belongs in the parser. |

## H. I/O and debug

| Command | Status | Notes |
|---|---|---|
| `print-function`, `print-size`, `print-stats` | **—** | Diagnostic; emit to stdout / a file. Layer B should pass these through to our REPL/logger. |
| `input` / `output` | **—** | CSV row import/export. Belongs in a thin I/O wrapper, not the kernel. |
| `fail` | **—** | `(fail cmd)` asserts that `cmd` errors. Test harness only. |

## I. Built-in sorts

The primitive sorts shipped by egglog:

| Sort | Notes for Covalence |
|---|---|
| `i64`, `f64` | Layer A: opaque values that appear as `TermDef::Lit` in the arena. Layer B: need an `Arena` literal variant per sort. We already have `i64` literals in some form. |
| `String` | Same — an interned string literal. |
| `Unit` | Trivial; `relation` desugars through this. |
| `Bool` | We already use `Bool(true)` as the user-truth ref. |
| `Map[K,V]`, `Vec[T]`, `Set[T]` | **O** for now. Containers have their own merge semantics and are typically not in the proof-encodable fragment. |
| `Rational`, `BigInt`, `BigRat` | **O** initially. Translatable via `covalence-types::Nat`/`Int` once we extend the term language. |

Each primitive sort comes with a battery of primitive operations
(`+`, `*`, `to-string`, `min`, `max`, `bitvec-and`, …). Layer A
treats them as opaque external functions whose Fiat justification is
"egglog computed it". Layer B has to implement each operation we
care about as a kernel-checked function (or admit them as `Fiat`
oracles, with appropriate trust markers).

## What's missing from this table

* The `:cost` annotation on constructors — irrelevant to soundness;
  matters for the extractor.
* The `:unextractable` flag — same.
* The `:when` clause on rewrites — desugars to extra premises.
* The container-specific helpers (`map-insert`, `vec-push`, …) — too
  many to enumerate; live in the `O` bucket until containers are in
  the proof fragment upstream.
* The experimental `set-cost`/`get-cost` from egglog-experimental and
  egglog-python — not in core egglog, not in scope here.

## How the K/P/O split steers the plan

* **Layer A MVP** = the **P** rows of A, B, C-without-delete, D, E,
  F. That is enough to ingest any kernel-checkable equality saturation
  proof from a vanilla egglog program.
* **Layer B MVP** = the **K** rows of A, B (rewrite + birewrite only),
  C-without-delete-or-subsume, D, E. That is enough to run a pure
  equality-saturation egglog program against our `Egraph` and finish
  with a kernel-checked `EThm`.
* Everything **O** waits until either egglog grows proof support for
  it, or we decide to admit it as an oracle with explicit trust.

[`03-integration-plan.md`](./03-integration-plan.md) sequences these
phases concretely.

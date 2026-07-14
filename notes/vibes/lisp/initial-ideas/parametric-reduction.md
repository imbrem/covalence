# Parametric reduction: representation × semantics × strategy (discussion draft)

Response to: we want a **reduction relation ASAP** (recursive functions may not
terminate!), and the API should be **parametric in all three of** representation,
semantics/relation, and reduction strategy, with a high-level API on top. Not committed.
This supersedes the single `ReductionStrategy` seam in the minimal-spec — that was one axis
of three.

## Why the relation is non-negotiable (the non-termination argument)

The equational shape `⊢ input = output` forces reduction to be a **function**: it demands
an `output` to equate to. A recursive Lisp function that diverges — `(define (loop x) (loop
x))` — has **no value**, so there is no `output`, so the equational theorem *cannot be
stated*. The moment we have user-defined recursion (Little Schemer ch2+), some programs
don't terminate, and the equation is the wrong object.

The right object is a **step relation** and its reflexive-transitive closure:

```
Step    ⊆ (State × Term) × (State × Term)      -- one reduction step
Reduces = Step*                                 -- zero-or-more steps
```

A term relates to *each* of its reducts. Termination = reaching a normal form (a value)
is a **theorem about** a particular run, not a precondition for stating it. Divergence =
an infinite `Step` chain (no normal form) — expressible, honest, non-hanging. `amb` =
`Step` has several successors. This is the `Eval_L`/`Reduces` relation from
[`reduction-relations-and-state.md`](./reduction-relations-and-state.md) and
[`lisp-dialects-and-order.md`](./lisp-dialects-and-order.md), and it's why we need it now.

## The three orthogonal axes

| Axis | What varies | Trait | Instances |
|---|---|---|---|
| **Representation** `R` | how a term/value is encoded | `Repr { type Term; … }` | untyped `SExpr` tree · kernel `sexpr` `Term` · internal Rust `Val` · (later) a WASM value |
| **Semantics** `S` | *what* the reduction relation IS | `Semantics<R> { … Step/Reduces …}` | McCarthy small-step · big-step eval · a dialect's `Eval_L` · ACL2 applicative |
| **Strategy** `Str` | *how* a reduction is found + certified | `Strategy<R,S> { … }` | symbolic (chain kernel laws) · **proven-WASM-interpreter oracle** · normal-order · applicative-order |

They are genuinely independent:

- One **semantics** (`Reduces`) can be explored by many **strategies** (normal vs
  applicative order; a slow symbolic prover vs a fast proven-WASM oracle) — all producing
  witnesses of the *same* relation.
- One **strategy** (symbolic congruence-chaining) works over many **representations**
  (kernel S-expression term today; a different term encoding later).
- **Representation** is orthogonal to both: it's the data the other two operate on.

The current build's `ReductionStrategy` producing `⊢ input = output` is exactly **one
corner**: `R` = kernel S-expression term, `S` = *terminating deterministic* fragment, `Str` = symbolic.
The generalization keeps that corner working and opens the other three.

## The API on top

The high-level surface is generic over the three, and returns a **certified reduction**,
not a value:

```rust
// Representation: the term encoding.
trait Repr { type Term; type Value; /* is_value, embed/project */ }

// Semantics: THE relation. A step is certified — each `step` returns a kernel proof that
// `from` reduces to `to` under this relation (⊢ Step (s,from) (s',to)), or None if `from`
// is a normal form / stuck.
trait Semantics<R: Repr> {
    type StepCert;                    // a kernel Thm: ⊢ Step (s, from) (s', to)
    fn successors(&self, s: &State, t: &R::Term) -> Successors<R>;   // 0, 1, or many (amb)
}

// Strategy: choose which successor(s) to pursue and how far — the search policy.
trait Strategy<R: Repr, S: Semantics<R>> {
    // Advance the reduction by (up to) `fuel` steps, accumulating a certified chain.
    fn drive(&self, s: &S, red: &mut Reduction<R, S>, fuel: Fuel) -> Progress;
}

// The result object: a lazy, certified reduction sequence. Handles NON-TERMINATION by
// being a stream — you pull steps; it ends in a Value or streams forever.
struct Reduction<R: Repr, S: Semantics<R>> {
    cur: R::Term,
    cert: S::CompositeCert,   // ⊢ Reduces (s, input) (s', cur) — the chain so far (trans-composed)
    // status: Value(v) | Reducible | Stuck | Diverging(step_count)
}
```

Key properties:

- **Non-termination is a first-class status**, not a hang: `reduce` returns a `Reduction`
  you *pull* (`next`/`drive fuel`). The REPL shows the current head + step count; a
  diverging program streams `…` instead of freezing. Bounded (`fuel`) and run-to-value are
  both just drive policies.
- **Every prefix is certified**: `cert` is `⊢ Reduces (s,input) (s',cur)` — the
  transitivity-composed chain of the per-step certs. The printed value (when a normal form
  is reached) is read off `cur` with `cert` witnessing it. Still: **print only after a
  kernel Thm** — now the Thm is a (possibly partial) reduction certificate, not an
  equation.
- **`next` unifies two features**: the nondeterminism resume (`amb`, pull another
  successor) and the non-termination resume (pull another step) are the same operation on
  the `Reduction` stream.

## Today's honest first cut (buildable now, genuinely a relation)

A full inductive `Reduces` HOL predicate (least fixpoint in the kernel) is a real lift
(recon flagged it as not-built). But we get the relation's *behavior* immediately with the
equational theorems we already have:

- **`Step` cert = a kernel equation** `⊢ from = to` for one computation law
  (`proj_scons`, a δ-unfold of a user `define`, a β-step). We can prove these today.
- **`Reduces` cert = the trans-composition** `⊢ input = cur` of the steps so far. Also
  today (`Thm::trans`).
- **The stream** makes it a relation in behavior: a diverging recursion produces an
  unbounded certified step stream (each step a real Thm) instead of a single impossible
  equation. Run it with fuel; it never claims a value it can't reach.

So the "reduction relation ASAP" ships as a **lazy stream of certified equational steps**
now, and upgrades to a **genuine inductive `Reduces` HOL relation** later (the `StepCert`
type changes from an equation to a relation-membership Thm; nothing above it moves — that's
the point of the semantics axis). The proven-WASM-interpreter strategy is a
`Strategy`-axis drop-in: it runs a verified WASM evaluator and certifies its trace as the
step chain — the end-to-end test the user wants.

## What this changes in the build

1. `ReductionStrategy` (the one seam) splits into **`Repr` / `Semantics` / `Strategy`**,
   with the high-level `Repl::reduce` returning a `Reduction` stream.
2. The current equational reduce becomes `SymbolicStrategy` over the *terminating* corner —
   keep it; make it the `fuel = ∞, run-to-value` policy of the streaming API.
3. Add the **`Step`/`Reduces` semantics** (equational-step cut) + `fuel`/`next` so
   non-terminating user recursion is demoable (shows steps, doesn't hang).
4. Recursion (`define`) + the step relation together give Little Schemer ch2 (`lat?`,
   `member?`, recursive descent) — the north-star tests.

## Open questions

- **`Step` granularity** — one computation law per step (fine-grained, many certs) vs
  weak-head-normal per step. Fine-grained is simpler to certify and to display; start there.
- **Divergence certificate** — is "diverges" ever a *theorem* (coinductive / a proof no
  normal form exists), or just an observed unbounded stream? Observed for now; the
  coinductive non-termination proof is a later, separate object.
- **Where the inductive `Reduces` lives** — proved in `covalence-init` (like `init/lisp.rs`)
  as an impredicative least fixpoint, or assembled in the untrusted REPL from step certs?
  The step-cert stream needs *no* kernel relation; the monolithic `Reduces` predicate is
  only needed to state ∀-theorems *about* reduction (e.g. determinism, `member?` totality).
  So: stream now, inductive predicate when we prove metatheorems.
- **Fuel vs true laziness** in the browser — a `drive(fuel)` button vs an async pull loop.
  Fuel-per-cell is the minimal demo; async streaming is the async-prover `Env`.

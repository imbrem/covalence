# covalence-lisp — SKELETONS

See [`notes/vibes/lisp/STATUS.md`](../../../notes/vibes/lisp/STATUS.md) for the
full picture.

## Severe

- **The full metacircular interpreter does not run yet.** The ground fragment
  (`quote`/`car`/`cdr`/`cons` dispatched by `eq?` on the operator symbol) runs
  and is certified (`tests/little_schemer_ch2.rs::metacircular_*`). Two gaps
  block the complete `metacircular.lisp`
  (`notes/vibes/lisp/minimal-spec/implementation-plan.md` §metacircular):
  1. **Truthy-data `cond` conditions.** Lisp `cond`/`if` test any non-`nil`
     value as true; the kernel `cond α c x y` needs a **`bool`** condition. So a
     clause like `evcon`'s `((eval (car (car c)) a) …)`, whose test is *data*,
     fails to type. Needs a data→bool coercion (a `truthy`/`null?`-style fold)
     applied to non-bool `cond` tests, or a Lisp-native `cond` over `sexpr`.
  2. **Polymorphic `eval` return + `assoc`/env + lambda-in-`eval`.** The plan's
     `eval` returns *data* on most branches but *bool* on the `atom`/`eq`
     branches, so it has no single HOL type; `assoc`/`pair`/`evlis` and the
     `((lambda …) …)` application path inside `eval` inherit that. Needs the
     data-as-boolean bridge above plus a uniform `sexpr` representation of
     `t`/`nil` (Lisp-level constants via the carved recursor) so predicates
     return data.
- **The REPL bypasses the `ReductionStrategy` seam** (legacy `hol.rs`).
  `Session`/`semantics.rs` now drive the parametric `Semantics<LispRepr>` +
  `RunToValue` seam directly, but the older one-shot `SymbolicStrategy`
  (`ReductionStrategy` in `hol.rs`) is unused except by `LispHol::eval` and its
  own tests. Fold it into the `Semantics` seam or retire it.

## Minor

- **`relation.rs` reduction relation — next-phase clauses.** The `Step`/`Reduces`
  relations (on the binary engine, `src/relation.rs`) land the primitive fragment
  (car/cdr/cons, atom?/consp/null?, eq? on *equal* atoms, cond truthy/falsy
  select, unary-elimination congruence). Deferred: **β/λ** (`Step ((λx.b) a) b[a/x]`)
  and **δ/`defun`** (`Step (f args) body[args]`, via the defun-as-hypothesis
  `Premise::Side`); **integer literals** (`Step (+ (int a)(int b)) (int a+b)`, the
  `sector+int` dialect); **`eq?` on distinct atoms** (needs the blob-disequality
  clause) and congruence *into* `eq?` operands; **congruence into `cond` tests**
  (so a predicate result can drive a `cond`); and the metatheorems (`Step`
  determinism, `Reduces` = `Step*`) via `rule_induction2`. No `RelationalSemantics`
  `Semantics<LispRepr>` wrapper / `#semantics` toggle yet (driver is standalone
  `prove_step`/`prove_reduces`).

- **`defun` return type is a 2-way guess.** `Session::install` tries `bool`
  then `sexpr` for a recursive function's head (predicates vs data functions).
  Functions that are neither purely-bool nor purely-`sexpr`-valued (mixed, or
  higher-order) are not installable; there is no real Lisp type inference.
- **Forward references default to `sexpr… → sexpr`.** A call to a not-yet-defined
  function compiles a `sexpr`-returning free-variable head
  (`semantics.rs::forward_head_ty`), so mutual recursion only closes when the
  later `defun` also has a `sexpr` return of the same arity. A forward-referenced
  *predicate* (bool return) would not unify.
- **`carved → sexpr` rename pending.** The code still uses the `carved` jargon
  (`CarvedSExpr`, `carved()`); the plan is to rename to an `SExpr`-family that
  does not clash with `covalence_sexp::SExpr`, coordinated with the kernel.
- **`null?` is the `consp` complement** (`⊢ ¬ consp v`), correct on lists;
  `null?` of a non-nil *atom* answers `nil` rather than erroring as a strict
  list-only `null?` would.
- **`eq?` is atoms-only.** Both operands must reduce to `atom b` values; the
  step decides the closed blob (dis)equality via `atom` injectivity
  (`CarvedSExpr::inj_atom`) + congruence. `eq?` on lists (structural `sexpr`
  equality) is `Stuck` / future work.
- **Predicate/`eq?` values are `bool` literals, data values are `sexpr`.** See
  the metacircular gap (2): a uniform `sexpr`-valued `t`/`nil` (so predicates
  compose as data) would need Lisp-level `t`/`nil` constants.
- The aspirational `Reduces (state,input) (state',output)` *relation* (with
  `amb` nondeterminism + threaded state, streaming for non-terminating fns) is
  future work; today's `⊢ input = output` is its deterministic special case.
  Non-termination IS handled (fuel-bounded `drive_fueled` → `Status::Diverging`,
  never a hang), but only as the equational fragment.
- `resolve_number`/`resolve_string` numeral-vs-symbol split is cosmetic (both
  lower to raw-byte atoms); strings with whitespace/parens do not round-trip.
- The `#`-directive table has only `#help` / `#show`; extensible
  (`session::Directive`) but no `#defun` / `#load` / `#type`.

# covalence-repl-core — SKELETONS

See [`notes/vibes/lisp/STATUS.md`](../../../notes/vibes/lisp/STATUS.md).

## Severe

- **The `ReductionStrategy` seam is not yet load-bearing.** The only consumer
  (`covalence-lisp`'s `Session`/`Evaluator`) composes kernel rules directly and
  bypasses `reduce`, so the abstraction does not currently mediate any REPL
  reduction. Route the Lisp REPL through it so the seam earns its keep (and a
  proven-WASM-interpreter strategy can drop in).
- `ReductionStrategy::reduce` returns only the equational `⊢ term = value`
  shape (the deterministic special case). The aspirational relational shape
  `⊢ Reduces (state,input) (state',output)` (nondeterminism/`amb`, threaded
  state, streaming for non-terminating recursive fns) is not yet a kernel
  object; the trait signature will widen when it is. See
  `notes/vibes/lisp/initial-ideas/parametric-reduction.md` and
  `reduction-relations-and-state.md`.

## Minor
- No `SExprRepl` event-driven refinement (fold S-expr events straight to
  `Term`, no intermediate tree). `Repl` + `ReductionStrategy` only for now.
- No concrete `Repl` impl lives here (by design); the worked instance is
  `covalence-lisp::session::Session` (start/parse/eval/show + `#`-directives).

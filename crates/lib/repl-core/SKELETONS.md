# covalence-repl-core — SKELETONS

## Minor

- `ReductionStrategy::reduce` returns only the equational `⊢ term = value`
  shape (the deterministic special case). The aspirational relational shape
  `⊢ Reduces (state,input) (state',output)` (nondeterminism/`amb`, threaded
  state) is not yet a kernel object; the trait signature will widen when it is.
  See `notes/vibes/lisp/initial-ideas/reduction-relations-and-state.md`.
- No `SExprRepl` event-driven refinement (fold S-expr events straight to
  `Term`, no intermediate tree). `Repl` + `ReductionStrategy` only for now.
- No concrete `Repl` impl lives here (by design); the worked instance is
  `covalence-lisp::session::Session` (start/parse/eval/show + `#`-directives).

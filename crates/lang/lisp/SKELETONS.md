# covalence-lisp — SKELETONS

See [`notes/vibes/lisp/STATUS.md`](../../../notes/vibes/lisp/STATUS.md) for the
full picture.

## Severe

- **The REPL bypasses the `ReductionStrategy` seam.** `Evaluator` (`eval.rs`)
  composes kernel rules **directly**; `SymbolicStrategy` (`hol.rs`, the
  `ReductionStrategy` instance) is only reached by `LispHol::eval` + its own
  de-risking tests, not by `Session`/`eval_cell`. Route every reduction through
  the seam so the abstraction is load-bearing — the precondition for a drop-in
  proven-WASM-interpreter strategy.
- **No chapter-2 recursion / `defun`.** The evaluator (`eval.rs`) has no
  user definitions, no environment/dictionary, and no recursion, so the ch2
  recursive predicates (`lat?`, `member?`, `rember`, …) — and the metacircular
  `eval`/`apply` interpreter — cannot be run. `Lisp`'s `resolve_symbol` still
  treats every symbol as a bare atom (no dictionary lookup), and `session::State`
  is a unit. Needs: a `defun` special form, a binding environment threaded
  through `Evaluator::eval`, and a recursion principle (the carved carrier's
  `induct`/recursor, currently `pub(crate)` in `covalence-init`) to produce
  `⊢ f args = value` for recursive `f`.
- **`eval` is symbolic-only.** No conditionals (`cond`/`if`), no `lambda`, no
  arithmetic (ch1 needs none, but the surface will). Any operator outside
  `quote`/`car`/`cdr`/`cons`/`atom?`/`consp`/`null?`/`eq?` is `Stuck`.
- **`carved → sexpr` rename pending.** The code still uses the `carved` jargon
  (`CarvedSExpr`, `carved()`, `carved.rs`); the plan is to rename to an
  `SExpr`-family that does not clash with `covalence_sexp::SExpr`, test-gated and
  coordinated with the kernel bundle name. See `notes/vibes/lisp/README.md`.

## Minor

- **`null?` is the `consp` complement** (`⊢ ¬ consp v` folded via boolean
  `simp`), correct on lists (`snil`/`scons`) — which is all ch1 uses — but
  `null?` of a non-nil *atom* answers `nil` rather than erroring the way a
  strict Little-Schemer `null?` (list-only) would.
- **`eq?` is atoms-only** (Little Schemer ch1 semantics): both operands must
  evaluate to `atom b` values; the result is the closed literal (dis)equality
  of the blob payloads. `eq?` on lists is `Stuck` (structural sexpr equality is
  future work).
- **Predicate/`eq?` values are `bool` literals, data values are `sexpr`.** The
  printed `t`/`nil` for a predicate is read off a `⊢ … = T/F` theorem (kind
  `Bool`); data results are carved `sexpr` terms (kind `Data`). A uniform
  sexpr-valued `t`/`nil` (so predicates compose as data) would need Lisp-level
  `t`/`nil` constants defined via the carved recursor (`pub(crate)`-gated).
- `SymbolicStrategy` (in `hol.rs`) still only matches single-step `car`/`cdr
  (cons h t)`; it needs to grow to cover what `Evaluator` does once the REPL is
  routed through it (see the Severe seam entry).
- The aspirational `Reduces (state,input) (state',output)` *relation* (with
  `amb` nondeterminism + threaded state, and streaming for NON-TERMINATING
  recursive fns) is future work; today's `⊢ input = output` is its deterministic
  special case. See
  `notes/vibes/lisp/initial-ideas/parametric-reduction.md` and
  `reduction-relations-and-state.md`.
- `resolve_number` only classifies all-ASCII-digit tokens, and numerals lower
  to the same raw-byte atom as symbols — the numeral/symbol split is cosmetic.
  `resolve_string` collapses strings into symbol-style atoms (raw bytes, no
  quoting/escaping); strings with whitespace/parens do not round-trip.
- Reader materializes the full `SExpr` tree; no event-driven fold-to-`Term`
  fast path (`SExpBuilder`/`TreeBuilder`).
- The `#`-directive table has only `#help` / `#show`; it is extensible
  (`session::Directive`) but has no `#defun` / `#load` / `#type` etc.

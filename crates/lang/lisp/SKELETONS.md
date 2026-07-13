# covalence-lisp — SKELETONS

## Severe

- **No chapter-2 recursion / `defun`.** The evaluator (`eval.rs`) has no
  user definitions, no environment/dictionary, and no recursion, so the ch2
  recursive predicates (`lat?`, `member?`, `rember`, …) cannot be run. `Lisp`'s
  `resolve_symbol` still treats every symbol as a bare atom (no dictionary
  lookup), and `session::State` is a unit. Needs: a `defun` special form, a
  binding environment threaded through `Evaluator::eval`, and a recursion
  principle (the carved carrier's `induct`/recursor, currently `pub(crate)` in
  `covalence-init`) to produce `⊢ f args = value` for recursive `f`.
- **`eval` is symbolic-only.** No conditionals (`cond`/`if`), no `lambda`, no
  arithmetic (ch1 needs none, but the surface will). Any operator outside
  `quote`/`car`/`cdr`/`cons`/`atom?`/`consp`/`null?`/`eq?` is `Stuck`.

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
- `SymbolicStrategy` (in `hol.rs`) is now superseded by `Evaluator` for the
  REPL, but retained as the single-step `ReductionStrategy` seam. It still only
  matches `car`/`cdr (cons h t)`; the `ReductionStrategy` trait is the intended
  plug for a future proven-WASM-interpreter strategy.
- The aspirational `Reduces (state,input) (state',output)` *relation* (with
  `amb` nondeterminism + threaded state) is future work; today's `⊢ input =
  output` is its deterministic special case. See
  `notes/vibes/lisp/initial-ideas/reduction-relations-and-state.md`.
- `resolve_number` only classifies all-ASCII-digit tokens, and numerals lower
  to the same raw-byte atom as symbols — the numeral/symbol split is cosmetic.
  `resolve_string` collapses strings into symbol-style atoms (raw bytes, no
  quoting/escaping); strings with whitespace/parens do not round-trip.
- Reader materializes the full `SExpr` tree; no event-driven fold-to-`Term`
  fast path (`SExpBuilder`/`TreeBuilder`).
- The `#`-directive table has only `#help` / `#show`; it is extensible
  (`session::Directive`) but has no `#defun` / `#load` / `#type` etc.

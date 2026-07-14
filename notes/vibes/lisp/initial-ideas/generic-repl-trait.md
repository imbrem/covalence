# A generic `Repl` trait + an event-driven S-expr extension (discussion draft, agent-authored)

Response to: make the REPL a **generic trait** with associated `State`/`Term`/`Eval`/
error types and lifecycle methods (`start(&mut self) -> Result<Self::State,
Self::Error>`, …); then an **extension** for S-expressions where `Term` is *parsed from a
sexpr* — and, naturally, via the **event-based API** (`covalence_sexp::SExpVisitor` /
`SExpBuilder`) rather than taking a materialized `SExpr`, which also saves allocations;
perhaps with **multiple error types**. Not committed. Refines the minimal-spec's §3 API
(the concrete `Session` becomes an *impl* of this trait).

## 0. The shape

Two layers:

1. **`Repl`** — the paradigm-neutral core: a session (`State`) in which you turn source
   into a `Term`, evaluate it to an `Eval`, and render it back. Nothing here is
   S-expr-specific — a Forth REPL, a Haskell REPL, an SMT REPL all implement it.
2. **`SExprRepl: Repl`** — the refinement where `Term` is built from S-expression
   *events*: the streaming parser (`parse_with`) drives an `SExpBuilder` whose `Output`
   is (a fragment of) `Self::Term`, so **no intermediate `SExpr` tree is allocated** and
   the Forth-style atom resolution happens *at the event*.

## 1. The generic `Repl` trait

```rust
pub trait Repl {
    type State;                 // the session world: defs, kv, log, dialect (reduction-relations-and-state.md)
    type Term;                  // an evaluable form
    type Eval;                  // the RESULT of evaluating a Term — our reduction Thm `⊢ (s,i) ~~> (s',o)`

    // --- multiple error types (one per phase; collapse via `Error` below if you like) ---
    type StartError;            // failed to initialize a session
    type ParseError;            // source/events -> Term
    type EvalError;             // Term -> Eval

    // --- lifecycle ---
    /// Begin a session: a fresh State (load prelude defs, pick the dialect, empty world).
    fn start(&mut self) -> Result<Self::State, Self::StartError>;

    /// text -> Term, against the current State (reader macros / abbreviations, §S-expr).
    fn parse(&mut self, state: &Self::State, src: &str) -> Result<Self::Term, Self::ParseError>;

    /// Term -> Eval, stepping the State (defs extended, log appended, kv mutated).
    fn eval(&mut self, state: &mut Self::State, term: Self::Term) -> Result<Self::Eval, Self::EvalError>;

    /// Resume a NONDETERMINISTIC evaluation for the next witness (`amb`), if any.
    fn next(&mut self, _state: &mut Self::State, _prev: &Self::Eval) -> Option<Self::Eval> { None }

    /// Eval -> text, against the State (may abbreviate — a section of the parse relation).
    fn show(&self, state: &Self::State, eval: &Self::Eval) -> String;
}
```

Notes:

- **`start` returns the `State`** (not stored in `self`), so one `Repl` value can drive
  many independent sessions, and `State` is snapshot/clone/serialize-able (checkpointing,
  the content-address store, undo). `self` holds the *dialect machinery* (dictionaries,
  builders); `State` holds the *session data*. Clean split.
- **`Eval` is the reduction theorem**, not a bare value — that's the whole
  "evaluate-as-a-theorem" contract (`reduction-relations-and-state.md`). `next` makes the
  relation's multiple witnesses (nondeterminism / `amb`) first-class without changing the
  return type.
- **`show`/`parse` take `&State`** so both consult session state — enabling stateful
  reader macros and stateful pretty-printing (macro abbreviation), and keeping Thm 1 / Thm
  3 (`Parses`) sharing one relation so reader and printer can't drift.

### Multiple error types + the optional collapse

Per-phase errors are the honest default (a parse failure and a divergence are different
things, with different recovery). For the convenience `step`, add an *optional* unified
error and `From` glue:

```rust
pub trait ReplStep: Repl
where
    Self::ParseError: Into<Self::Error>,
    Self::EvalError:  Into<Self::Error>,
{
    type Error;                                     // the unified line error
    /// parse ; eval ; show — the whole REPL cell.
    fn step(&mut self, state: &mut Self::State, src: &str) -> Result<String, Self::Error> {
        let t = self.parse(state, src).map_err(Into::into)?;
        let e = self.eval(state, t).map_err(Into::into)?;
        Ok(self.show(state, &e))
    }
}
```

So you get *both*: granular `ParseError`/`EvalError`/`StartError` when you want to
discriminate, and one `Error` at the cell boundary (what the web `CellResult` carries).
(`thiserror` per library crate; the unified `Error` is a `#[from]`-enum — matches the repo
convention.)

## 2. How the associated types instantiate for our Lisp

| assoc type | minimal Lisp instance |
|---|---|
| `State` | `{ defs, kv:(), log:() }` — the extensible world (`reduction-relations-and-state.md` §3) |
| `Term` | a lowered `sexpr` HOL `Term` (built straight from events, §3) — or a light AST |
| `Eval` | `Thm` of `⊢ Reduces (state,input) (state',output)` |
| `StartError` | prelude/dialect load failure |
| `ParseError` | reader error (bad delimiters, ill-formed event stream, unknown reader macro) |
| `EvalError` | unbound head, arity mismatch, stuck (no reduction witness) |

`Session` (minimal-spec §3) is then `impl Repl for Session` + `impl SExprRepl` — and the
free-standing `parse`/`reduce`/`prettyprint`/`show`/`next` methods become the trait
methods verbatim (so the WIT/Python bindings bind the *trait surface*).

## 3. The S-expr extension — Term from events, no `SExpr` allocation

The repo already has the exact pattern: `SExpBuilder` (bottom-up node construction) +
`TreeBuilder<B, D>` (adapter implementing `SExpVisitor`) + `parse_with(src, &mut visitor)`
(`crates/lib/sexp`). The default `DefaultBuilder` builds an `SExpr` tree; **we supply a
builder whose `Output` is `Self::Term`, so the parser folds events directly into terms and
the `SExpr` Vec-tree is never built.**

```rust
pub trait SExprRepl: Repl {
    /// Builds Term fragments from SAX events. Reuse covalence_sexp::{SExpBuilder, TreeBuilder}.
    type TermBuilder: SExpBuilder;

    /// A fresh builder carrying the state's dialect + dictionary + numeral policy.
    fn term_builder(&self, state: &Self::State) -> (Self::TermBuilder, impl Dialect);

    /// Assemble the top-level built fragments into one Term (one form per REPL cell).
    fn assemble(&self, out: Vec<<Self::TermBuilder as SExpBuilder>::Output>)
        -> Result<Self::Term, Self::ParseError>;

    /// Default `Repl::parse` via the streaming event parser — zero intermediate `SExpr`.
    fn parse_events(&mut self, state: &Self::State, src: &str)
        -> Result<Self::Term, Self::ParseError>
    {
        let (b, dialect) = self.term_builder(state);
        let mut tb = TreeBuilder::new(b, dialect);
        covalence_sexp::parse_with(src, &mut tb).map_err(Self::parse_err)?;
        self.assemble(tb.into_results())
    }
}
```

A concrete `Session` sets `Repl::parse = SExprRepl::parse_events`. The builder's `Output`
can be the `sexpr` HOL `Term` itself (fold-to-kernel-term while parsing) or a small
resolved AST; either way the separate `SExpr` materialization + re-walk-to-lower of the
tree path is gone. That's the allocation win the ask names, and it's *streaming* (parse
and build interleave).

### The Forth split lives in `build_atom` — where numerals are decided

The event `atom(text)` is exactly the Forth "just-read-a-token" moment, so the
dictionary→numeral→symbol resolution (minimal-spec §4) is the builder's `build_atom`:

```rust
impl SExpBuilder for LispTermBuilder {
    type Output = Term;                    // fold straight to a kernel term fragment

    fn build_atom(&mut self, text: &str) -> Term {
        if let Some(w) = self.dict.lookup(text)        { w.to_term() }          // 1. dictionary
        else if let Some(l) = self.nums.read_numeral(text) { l.to_term() }      // 2. numeral (THE policy)
        else                                           { Term::sym(text) }      // 3. bare symbol
    }
    fn build_list(&mut self, kids: Vec<Term>) -> Term { Term::app_spine(kids) } // application
    fn build_string(&mut self, fmt: &str, bytes: &[u8]) -> Term { Term::str(fmt, bytes) }
    fn build_quoted_symbol(&mut self, c: &str) -> Term { Term::sym(c) }
}
```

So **the numeral decision is one method on one builder**, chosen per dialect via
`term_builder` — and it happens at the source event, no `SExpr` in between. Swapping
bin/oct/hex/LEB128 (`atoms.md`) = swapping `self.nums`, nothing else moves. (Optionally,
`build_atom` can *defer* resolution — emit an unresolved `Term::sym` and resolve at
`eval` — if you want parse/eval cleanly separated; the streaming/Forth mode resolves
eagerly. Both are one-line variants of the same builder.)

## 4. Why event-based is the right default (beyond allocations)

- **No `SExpr` tree** — parse folds straight to `Term` (the stated saving), and it's
  *streaming* (constant extra space beyond the term itself).
- **Resolution at the source** — the Forth dictionary/numeral split is literally the
  `build_atom` event; you can't put it in a more natural place.
- **Dialect reuse for free** — `parse_with` + `Dialect` already give per-dialect trivia,
  delimiters, quoting (`CovalenceDialect`/`WatDialect`/`SmtLibDialect`/…), so
  `#dialect` switches the reader by swapping the `Dialect` fed to `TreeBuilder`.
- **One visitor, many consumers** — the same event stream can feed the term-builder, a
  content-hasher (`#hash` over events, no tree), a pretty-reprinter, or a linter. The
  event API is the shared spine (parsing-relations.md's "one grammar, many forms").

## 5. Fit with the minimal-spec

- `Session` becomes `impl Repl + SExprRepl`; `Session::{parse, reduce→eval, prettyprint,
  show, next}` are the trait methods. The WIT (`lisp.wit`) and Python shim bind the trait
  surface, so "one API, three faces" (§9) is now literally *the trait*.
- `start()` replaces the ad-hoc `Session::new()` and returns a fresh `State` — enabling
  per-session state on the web (`session` resource) and checkpoint/undo.
- `eval_cell` (the web entrypoint) = `ReplStep::step` + the `#`-directive pre-check.
- Minimal instances: `TermBuilder = LispTermBuilder` (folds to `sexpr` `Term`),
  `Dialect = CovalenceDialect` (reuse), errors as the table in §2.

## 6. Open questions

- **Fold-to-kernel-`Term` at parse, or a resolved AST between?** Folding straight to the
  HOL term is maximally allocation-lean but couples the reader to the kernel; a tiny
  resolved AST (`Word | Lit | App | Sym`) as `Output` keeps the reader kernel-agnostic and
  lowers in `eval`. I lean: AST `Output` for the reader crate, fold-to-`Term` as an
  optional fast path in the `hol` feature.
- **Eager vs deferred atom resolution** (§3) — resolve in `build_atom` (Forth-eager,
  streaming interpreter feel) or emit bare symbols and resolve in `eval` (clean
  parse/eval separation, needed anyway for `quote`/macros where atoms *aren't* evaluated).
  Probably **deferred by default** (so `(quote foo)` doesn't resolve `foo`), with an
  eager streaming mode for a true Forth loop.
- **How many error types?** `StartError`/`ParseError`/`EvalError` is a good minimum; do we
  want a separate `DirectiveError`, or are directives just a `Term` variant whose `eval`
  yields `EvalError`? (I lean: directives are parsed to a `Term::Directive`, so they reuse
  `EvalError` — one fewer type.)
- **`next` shape** — `fn next(&mut self, state, prev) -> Option<Eval>` (pull one more
  witness) vs `Eval` being an iterator/stream of derivations. Pull-based `next` matches the
  async-prover `Env` and the web `:next` button; the stream is a thin wrapper over it.
- **Does `TreeBuilder`'s per-list `Vec<Output>` matter?** It's O(children) transient
  allocation per list — far less than a full `SExpr` tree, but not zero. A push/pop arena
  on the builder could remove it if profiling says so; out of scope for minimal.

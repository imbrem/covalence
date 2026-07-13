//! A paradigm-neutral REPL trait stack.
//!
//! Two independent pieces:
//!
//! - [`Repl`] — the lifecycle core. A session ([`Repl::State`]) in which
//!   source becomes a [`Repl::Term`], a term evaluates to a [`Repl::Eval`],
//!   and an eval renders back to text. Per-phase error types
//!   ([`Repl::StartError`] / [`Repl::ParseError`] / [`Repl::EvalError`]),
//!   plus a default [`Repl::step`] that runs the whole cell. Nothing here is
//!   S-expr- or kernel-specific — a Forth, Haskell, or SMT REPL implements
//!   the same trait.
//!
//! - [`ReductionStrategy`] — **the abstraction for how a reduction is
//!   proved**. Its [`reduce`](ReductionStrategy::reduce) takes a kernel term
//!   and returns a kernel theorem `⊢ term = value`. This is the seam where a
//!   symbolic strategy (compose the carrier's computation laws) and a future
//!   proven-WASM-interpreter strategy plug in interchangeably. It is generic
//!   over the kernel term/thm types so this crate stays kernel-agnostic; the
//!   Lisp crate instantiates it under its `hol` feature.
//!
//! The design intent lives in
//! `notes/vibes/lisp/initial-ideas/generic-repl-trait.md` and
//! `reduction-relations-and-state.md`. The aspirational
//! `Reduces (state,input) (state',output)` *relation* is not yet a kernel
//! object; this crate ships the **equational special case** `⊢ input =
//! output` that that note flags as the deterministic corollary. See
//! `SKELETONS.md`.

#![forbid(unsafe_code)]

/// The paradigm-neutral REPL core.
///
/// One `Repl` value carries the *dialect machinery* (dictionaries,
/// builders); each [`start`](Repl::start) hands back a fresh, independent
/// [`State`](Repl::State), so a single `Repl` can drive many sessions and a
/// `State` is snapshot/clone/serialize-able for checkpointing.
pub trait Repl {
    /// The session world: definitions, kv, log, dialect.
    type State;
    /// An evaluable form (e.g. a lowered kernel term or a small AST).
    type Term;
    /// The result of evaluating a term — for the kernel REPL, a reduction
    /// theorem, never a bare value.
    type Eval;

    /// Failed to initialize a session.
    type StartError;
    /// Source/events -> [`Term`](Repl::Term).
    type ParseError;
    /// [`Term`](Repl::Term) -> [`Eval`](Repl::Eval).
    type EvalError;

    /// Begin a session: a fresh [`State`](Repl::State).
    fn start(&mut self) -> Result<Self::State, Self::StartError>;

    /// `text -> Term`, against the current state.
    fn parse(&mut self, state: &Self::State, src: &str) -> Result<Self::Term, Self::ParseError>;

    /// `Term -> Eval`, possibly stepping the state.
    fn eval(
        &mut self,
        state: &mut Self::State,
        term: Self::Term,
    ) -> Result<Self::Eval, Self::EvalError>;

    /// Resume a nondeterministic evaluation for the next witness (`amb`), if
    /// any. Defaults to none.
    fn next(&mut self, _state: &mut Self::State, _prev: &Self::Eval) -> Option<Self::Eval> {
        None
    }

    /// `Eval -> text`, against the state (may abbreviate).
    fn show(&self, state: &Self::State, eval: &Self::Eval) -> String;

    /// parse ; eval ; show — the whole REPL cell. Errors are surfaced
    /// per-phase via [`StepError`].
    fn step(&mut self, state: &mut Self::State, src: &str) -> Result<String, StepError<Self>> {
        let t = self.parse(state, src).map_err(StepError::Parse)?;
        let e = self.eval(state, t).map_err(StepError::Eval)?;
        Ok(self.show(state, &e))
    }
}

/// The unified error at the [`Repl::step`] cell boundary — a parse or an
/// eval failure, kept discriminable.
#[derive(Debug)]
pub enum StepError<R: Repl + ?Sized> {
    /// A [`Repl::parse`] failure.
    Parse(R::ParseError),
    /// A [`Repl::eval`] failure.
    Eval(R::EvalError),
}

/// **The abstraction for how a reduction is proved.**
///
/// A `ReductionStrategy` turns a kernel term into a kernel theorem
/// `⊢ term = value`. It is the single swappable seam between *what* the REPL
/// reduces and *how* the reduction is justified:
///
/// - `SymbolicStrategy` (in `covalence-lisp`, `hol` feature) composes the
///   carved `sexpr` carrier's computation laws (`car (cons a b) = a`, …).
/// - A future `WasmInterpreterStrategy` would run a proven WASM interpreter
///   and certify its trace — returning a theorem of the *same* shape, so the
///   REPL above it is unchanged.
///
/// Generic over the term (`Term`) and theorem (`Thm`) types so this crate
/// carries no kernel dependency; downstream crates pin them to the kernel's
/// `Term` / `Thm`.
pub trait ReductionStrategy {
    /// The kernel term type reduced.
    type Term;
    /// The kernel theorem type returned — its conclusion is `term = value`.
    type Thm;
    /// A failure to prove a reduction (stuck term, kernel error, …).
    type Error;

    /// Prove `⊢ term = value`, returning the kernel theorem. The REPL reads
    /// the printed value off this theorem's conclusion — there is **no path
    /// that yields a value without a theorem**.
    fn reduce(&self, term: &Self::Term) -> Result<Self::Thm, Self::Error>;
}

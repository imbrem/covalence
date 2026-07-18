//! A paradigm-neutral REPL trait stack.
//!
//! Two layers:
//!
//! - [`Repl`] — the lifecycle core. A session ([`Repl::State`]) in which
//!   source becomes a [`Repl::Term`], a term evaluates to a [`Repl::Eval`],
//!   and an eval renders back to text. Per-phase error types
//!   ([`Repl::StartError`] / [`Repl::ParseError`] / [`Repl::EvalError`]),
//!   plus a default [`Repl::step`] that runs the whole cell. Nothing here is
//!   S-expr- or kernel-specific — a Forth, Haskell, or SMT REPL implements
//!   the same trait.
//!
//! - **The parametric reduction API** — three orthogonal axes, generic and
//!   kernel-agnostic (design intent:
//!   `notes/vibes/lisp/initial-ideas/parametric-reduction.md`):
//!   - [`Repr`] — the term/value **encoding**.
//!   - [`Semantics`] — *what the reduction relation IS*: a certified single
//!     [`step`](Semantics::step) returning a [`StepCert`] carrying a kernel
//!     `⊢ from = to`, or `None` at a normal form / stuck term.
//!   - [`Strategy`] — *how* a reduction is driven: a [`drive`](Strategy::drive)
//!     search policy that pulls (up to) `fuel` steps.
//!   - [`Reduction`] — the result object: a **lazy, certified sequence**
//!     `{ cur, composite ⊢ input = cur, status }`. Non-termination is a
//!     first-class [`Status::Diverging`] status you *pull* (`fuel`-bounded),
//!     not a hang; `amb`/nondeterminism resumes through the same seam.
//!
//! [`ReductionStrategy`] is the original one-axis seam (`⊢ term = value`), kept
//! as the run-to-value convenience: it is exactly the `Strategy`-drives-`Semantics`
//! corner where the relation is deterministic and terminating.
//!
//! The aspirational `Reduces (state,input) (state',output)` *relation* is not
//! yet a kernel object; the [`StepCert`] shipped here is the equational special
//! case `⊢ from = to` that the note flags as the deterministic corollary — and
//! the composite is the [`Thm::trans`]-chain `⊢ input = cur`. When the
//! inductive `Reduces` HOL relation lands, the `StepCert`/`Composite`
//! associated types change and nothing above them moves. See the generated open-work index.

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

// ============================================================================
// The parametric reduction API (three orthogonal axes)
// ============================================================================

/// **Axis 1 — representation.** How a term/value is encoded.
///
/// The kernel S-expression `Term` is one `Repr`; an internal Rust `Val`, or a
/// WASM value, would be others. [`Semantics`] and [`Strategy`] operate over a
/// `Repr` without caring which encoding it is.
pub trait Repr {
    /// The reducible term encoding.
    type Term: Clone;
    /// Is this term a value (a normal form to stop at)? Advisory — the ground
    /// truth for "no step" is [`Semantics::step`] returning `None`.
    fn is_value(&self, _term: &Self::Term) -> bool {
        false
    }
}

/// **Axis 2 — semantics: THE relation.** A single certified reduction step.
///
/// [`step`](Semantics::step) returns `Some(cert)` with a kernel proof that
/// `from` reduces to `to` under this relation (today: an equation
/// `⊢ from = to`), or `None` when `from` is a normal form / stuck. The cert
/// carries both the proof ([`StepCert::thm`]) and the reduced term
/// ([`StepCert::to`]) so a [`Strategy`] can continue from it.
///
/// This is the axis that upgrades: replacing the equational `StepCert` with a
/// `⊢ Reduces (s,from) (s',to)` membership Thm changes nothing above.
pub trait Semantics<R: Repr> {
    /// A single-step certificate: a kernel `⊢ from = to` plus the reduct `to`.
    type StepCert: StepCert<R, Thm = Self::Thm>;
    /// The kernel theorem type (its conclusion is `from = to`). Also the
    /// composite `⊢ input = cur` type — a chain of steps is still one theorem.
    type Thm: Clone;
    /// A failure to *attempt* a step (a kernel/theory error — distinct from a
    /// clean normal form, which is `Ok(None)`).
    type Error;

    /// One reduction step from `term`, or `Ok(None)` if `term` is a normal
    /// form / stuck under this relation.
    fn step(&self, term: &R::Term) -> Result<Option<Self::StepCert>, Self::Error>;

    /// **Transitivity** — compose a running composite `⊢ input = from` with a
    /// step `⊢ from = to`, yielding `⊢ input = to`. `prev` is `None` for the
    /// very first step (then `step_thm` *is* the composite). This is the one
    /// kernel-touching operation the generic driver needs; keeping it on the
    /// semantics keeps repl-core kernel-agnostic.
    fn compose(
        &self,
        prev: Option<Self::Thm>,
        step_thm: Self::Thm,
    ) -> Result<Self::Thm, Self::Error>;
}

/// A single certified reduction step: the reduct term plus a kernel theorem
/// witnessing `⊢ from = to`.
///
/// Generic over the theorem type so the crate stays kernel-agnostic; the Lisp
/// instance pins it to the kernel `Thm`. Composition (transitivity) of steps
/// onto a running composite `⊢ input = from` lives on
/// [`Semantics::compose`].
pub trait StepCert<R: Repr>: Sized {
    /// The kernel theorem type (its conclusion is `from = to`).
    type Thm;

    /// The reduct — the RHS of this step's `⊢ from = to`.
    fn to(&self) -> &R::Term;

    /// The step theorem `⊢ from = to`.
    fn thm(&self) -> &Self::Thm;

    /// Consume the step, yielding its `to` term and its theorem.
    fn into_parts(self) -> (R::Term, Self::Thm);
}

/// **Axis 3 — strategy.** Drives [`Semantics`] steps: a search policy.
///
/// [`drive`](Strategy::drive) advances a [`Reduction`] by up to `fuel` steps,
/// accumulating the certified chain, and reports [`Progress`]. Run-to-value is
/// `drive(Fuel::UNBOUNDED)`; a bounded button-press is `drive(Fuel::steps(n))`.
///
/// A semantics/theory error during a pull is surfaced as `Err`; a clean normal
/// form is `Ok(Progress::Value)`, and a fuel bound with steps remaining is
/// `Ok(Progress::Reducible)`.
pub trait Strategy<R: Repr, S: Semantics<R>> {
    /// Advance `red` by up to `fuel` steps under semantics `sem`.
    fn drive(&self, sem: &S, red: &mut Reduction<R, S>, fuel: Fuel) -> Result<Progress, S::Error>;
}

/// **The linear run-to-value strategy.** Pull single [`Semantics::step`]s in
/// order until a normal form is reached or `fuel` runs out. This is the
/// deterministic corner: the same behaviour as the legacy
/// [`ReductionStrategy`], now streaming and fuel-bounded. Nondeterministic
/// (`amb`) search would be a different `Strategy` selecting among successors.
#[derive(Clone, Copy, Debug, Default)]
pub struct RunToValue;

impl<R: Repr, S: Semantics<R>> Strategy<R, S> for RunToValue {
    fn drive(
        &self,
        sem: &S,
        red: &mut Reduction<R, S>,
        mut fuel: Fuel,
    ) -> Result<Progress, S::Error> {
        while !fuel.is_empty() {
            match red.pull(sem)? {
                Progress::Value => return Ok(Progress::Value),
                Progress::Stuck => return Ok(Progress::Stuck),
                Progress::Reducible => fuel = fuel.spend(),
            }
        }
        // Fuel exhausted with the head still reducible — a bound, not a hang.
        red.set_diverging();
        Ok(Progress::Reducible)
    }
}

/// A step budget for [`Strategy::drive`]. `UNBOUNDED` runs to a normal form (or
/// forever, for a genuinely diverging program — hence *pull* it with a bound in
/// interactive contexts).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fuel(pub u64);

impl Fuel {
    /// Run until a normal form is reached (no step budget).
    pub const UNBOUNDED: Fuel = Fuel(u64::MAX);
    /// A budget of exactly `n` steps.
    pub const fn steps(n: u64) -> Fuel {
        Fuel(n)
    }
    /// Is the budget exhausted?
    fn is_empty(self) -> bool {
        self.0 == 0
    }
    /// Consume one step.
    fn spend(self) -> Fuel {
        Fuel(self.0.saturating_sub(1))
    }
}

/// What a [`Strategy::drive`] call accomplished.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Progress {
    /// The reduction reached a normal form (a [`Status::Value`]).
    Value,
    /// `fuel` ran out with more steps available — the reduction is
    /// [`Status::Reducible`]; pull again with more fuel.
    Reducible,
    /// The reduction is [`Status::Stuck`] — a term with no step that is not a
    /// value.
    Stuck,
}

/// The status of a [`Reduction`]'s current head.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    /// A normal form: the head is a value (no further step).
    Value,
    /// Reducible: `drive` stopped on a fuel bound; more steps remain.
    Reducible,
    /// Stuck: the head is not a value and has no step (a semantics error /
    /// dead end).
    Stuck,
    /// Observed non-termination: `steps` certified steps taken, still
    /// reducible. (A diverging program under `UNBOUNDED` fuel never reaches
    /// this — pull with a bound instead.)
    Diverging(u64),
}

/// **The result object — a lazy, certified reduction sequence.**
///
/// Carries the current head `cur`, the composite certificate `⊢ input = cur`
/// (the transitivity-chain of the per-step certs so far), the running step
/// count, and a [`Status`]. You `pull` it forward with a [`Strategy`]; the
/// printed value (at a normal form) is read off `cur` with `composite`
/// witnessing it. Handles non-termination by being a stream, never a hang.
pub struct Reduction<R: Repr, S: Semantics<R>> {
    /// The current head term.
    cur: R::Term,
    /// `⊢ input = cur` — the trans-composed chain so far, or `None` before any
    /// step (the identity reduction; `cur == input`, use `⊢ input = input`).
    composite: Option<S::Thm>,
    /// How many certified steps have been taken.
    steps: u64,
    /// The current status.
    status: Status,
}

impl<R: Repr, S: Semantics<R>> Reduction<R, S> {
    /// Begin a reduction from `input`. Status starts [`Status::Reducible`]
    /// (nothing tried yet); `composite` is `None` (the identity `input = input`).
    pub fn start(input: R::Term) -> Self {
        Reduction {
            cur: input,
            composite: None,
            steps: 0,
            status: Status::Reducible,
        }
    }

    /// The current head term.
    pub fn cur(&self) -> &R::Term {
        &self.cur
    }

    /// The current status.
    pub fn status(&self) -> Status {
        self.status
    }

    /// How many certified steps have been taken.
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// The composite certificate `⊢ input = cur`, if any step has been taken.
    /// `None` means the reduction is still at `input` (the identity reduction);
    /// a caller wanting a theorem there mints `⊢ input = input` itself.
    pub fn composite(&self) -> Option<&S::Thm> {
        self.composite.as_ref()
    }

    /// Consume the reduction, yielding the final head and composite.
    pub fn into_parts(self) -> (R::Term, Option<S::Thm>) {
        (self.cur, self.composite)
    }

    /// Pull **one** step under `sem`, composing it (via [`Semantics::compose`])
    /// onto the running certificate `⊢ input = cur`. Returns the [`Progress`]
    /// of that single pull and updates [`status`](Reduction::status).
    ///
    /// Returns [`Progress::Value`] (and sets [`Status::Value`]) when `sem.step`
    /// reports a normal form — the composite is then the final `⊢ input =
    /// value`.
    pub fn pull(&mut self, sem: &S) -> Result<Progress, S::Error> {
        match sem.step(&self.cur)? {
            None => {
                self.status = Status::Value;
                Ok(Progress::Value)
            }
            Some(cert) => {
                let (to, step_thm) = cert.into_parts();
                let composite = sem.compose(self.composite.take(), step_thm)?;
                self.composite = Some(composite);
                self.cur = to;
                self.steps += 1;
                self.status = Status::Reducible;
                Ok(Progress::Reducible)
            }
        }
    }

    /// Mark the reduction as having hit a step bound while still reducible —
    /// records the observed step count as [`Status::Diverging`].
    pub fn set_diverging(&mut self) {
        self.status = Status::Diverging(self.steps);
    }
}

// ============================================================================
// The legacy one-axis seam
// ============================================================================

/// **The original single-axis reduction seam** — `⊢ term = value` in one shot.
///
/// This is the deterministic-terminating corner of the three-axis API: a
/// [`Strategy`] driving a [`Semantics`] to a normal form, collapsed to a single
/// call. Kept as a convenience for callers that want the value directly and a
/// drop-in point for a proven-WASM-interpreter oracle. Generic over the term
/// and theorem types so this crate carries no kernel dependency.
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

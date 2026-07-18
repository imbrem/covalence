//! The Forsp **reduction relation as a [`Semantics`]** — the parametric-reduction
//! wiring that lets `/forsp` render a program as a step sequence, mirroring the
//! Lisp [`LispSemantics`](../../lisp/src/semantics.rs).
//!
//! Three axes, exactly as `covalence-repl-core` prescribes:
//!
//! - [`ForspRepr`] — the term/state **encoding**. A Forsp "term" is a
//!   [`Snapshot`] of the small-step [`Machine`](crate::machine::Machine): its
//!   reified continuation, plus the stack and environment. Reduction is over
//!   *machine states*, not self-contained syntax, because Forsp is a stack
//!   machine with a shared heap.
//! - [`ForspSemantics`] — *what the relation IS*: one [`step`](Semantics::step)
//!   advances the machine by a single instruction and produces a
//!   [`ForspStep`] carrying the before/after [`Snapshot`].
//! - The [`RunToValue`](covalence_repl_core::RunToValue) strategy drives it to a
//!   halted state (or a fuel bound → [`Status::Diverging`]), so a genuinely
//!   non-terminating Forsp program is a *stream you pull*, never a hang.
//!
//! # Untrusted witness, kernel-ready seam
//!
//! Forsp has **no kernel theory yet**, so a [`ForspStep`] is a *lightweight
//! witness* — the before/after machine [`Snapshot`] — **not** a kernel `Thm`.
//! [`Semantics::Thm`] is therefore a plain [`StepTrace`] (the chain of snapshots
//! visited). The traits are nonetheless wired so a future kernel-backed forsp
//! theory drops in as a `Semantics` *swap*: replace [`ForspSemantics`] with one
//! whose `StepCert` carries `⊢ state → state'` and whose `Thm` is the composite
//! reduction theorem — nothing above the `Semantics` boundary moves. See
//! the generated open-work index for the kernel-proof skeleton.

use std::cell::RefCell;

use covalence_repl_core::{Repr, Semantics, StepCert};

use crate::machine::{Machine, MachineState};
use crate::{FError, ForeignPrims, Forsp, ValRef};

/// A cloneable snapshot of the small-step machine: the reified continuation
/// (as `(ip, saved_env)` pairs) plus the stack and environment.
///
/// This is the Forsp analogue of the Lisp reduction's kernel `Term`: the whole
/// "state of the computation" a step transforms. The heap the [`ValRef`]s point
/// into is *shared, monotically-growing* and lives outside the snapshot (in the
/// [`ForspSemantics`]' [`Forsp`] runtime), so a `Snapshot` is cheap to clone.
#[derive(Clone, Debug)]
pub struct Snapshot {
    /// Value stack (cons-list; top is car).
    pub stack: ValRef,
    /// Current environment (cons-list of `(name . val)` pairs).
    pub env: ValRef,
    /// Reified continuation as `(ip, saved_env)` frames; last is active.
    pub control: Vec<(ValRef, ValRef)>,
}

impl Snapshot {
    /// The observable machine state (stack, env, continuation depth).
    pub fn observe(&self) -> MachineState {
        MachineState {
            stack: self.stack,
            env: self.env,
            control_depth: self.control.len(),
        }
    }

    /// Has the machine halted (no remaining continuation)?
    pub fn is_halted(&self) -> bool {
        self.control.is_empty()
    }
}

/// **Axis 1 — representation.** A Forsp reducible is a machine [`Snapshot`].
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspRepr;

impl Repr for ForspRepr {
    type Term = Snapshot;

    fn is_value(&self, term: &Snapshot) -> bool {
        term.is_halted()
    }
}

/// The lightweight "theorem" carried by a Forsp reduction: the ordered trace of
/// machine snapshots the reduction has passed through (a witness, not a kernel
/// certificate). `states[0]` is the input; `states.last()` is the current head.
///
/// This is the `Semantics::Thm` composite — [`compose`](Semantics::compose)
/// appends. A kernel-backed forsp theory would replace this with a real
/// `⊢ input →* cur` reduction theorem.
#[derive(Clone, Debug)]
pub struct StepTrace {
    /// The snapshots visited, oldest first. Non-empty.
    pub states: Vec<Snapshot>,
}

impl StepTrace {
    /// The number of steps witnessed (transitions = snapshots − 1).
    pub fn len(&self) -> usize {
        self.states.len().saturating_sub(1)
    }

    /// Is this the empty (single-state) trace?
    pub fn is_empty(&self) -> bool {
        self.states.len() <= 1
    }
}

/// A single certified Forsp step: the reduct [`Snapshot`] plus the before/after
/// witness [`StepTrace`] `[before, after]`.
#[derive(Clone, Debug)]
pub struct ForspStep {
    to: Snapshot,
    /// The two-state witness `[before, after]` for this one step.
    trace: StepTrace,
}

impl ForspStep {
    /// The `before` snapshot of this step.
    pub fn before(&self) -> &Snapshot {
        &self.trace.states[0]
    }
    /// The `after` snapshot of this step (`== self.to()`).
    pub fn after(&self) -> &Snapshot {
        self.trace.states.last().expect("two-state trace")
    }
}

impl StepCert<ForspRepr> for ForspStep {
    type Thm = StepTrace;
    fn to(&self) -> &Snapshot {
        &self.to
    }
    fn thm(&self) -> &StepTrace {
        &self.trace
    }
    fn into_parts(self) -> (Snapshot, StepTrace) {
        (self.to, self.trace)
    }
}

/// **Axis 2 — semantics: THE relation.** The Forsp small-step relation over a
/// shared [`Forsp`] runtime.
///
/// Holds the runtime in a [`RefCell`] because the heap is a monotonically
/// growing arena every step allocates into, while [`Semantics::step`] takes
/// `&self`. This is the untrusted analogue of `LispSemantics`' process-global
/// kernel theories.
pub struct ForspSemantics<F: ForeignPrims = ()> {
    rt: RefCell<Forsp<F>>,
}

impl<F: ForeignPrims> ForspSemantics<F> {
    /// Wrap a runtime as the reduction relation.
    pub fn new(rt: Forsp<F>) -> Self {
        ForspSemantics {
            rt: RefCell::new(rt),
        }
    }

    /// Consume the semantics, recovering the underlying runtime (for rendering
    /// the final stack).
    pub fn into_runtime(self) -> Forsp<F> {
        self.rt.into_inner()
    }

    /// Borrow the runtime (for rendering).
    pub fn with_runtime<R>(&self, g: impl FnOnce(&mut Forsp<F>) -> R) -> R {
        g(&mut self.rt.borrow_mut())
    }

    /// Build the initial [`Snapshot`] for `program` in the runtime's current
    /// environment: one control frame `(program, current_env)`, current stack.
    pub fn initial(&self, program: ValRef) -> Snapshot {
        let rt = self.rt.borrow();
        Snapshot {
            stack: rt.stack,
            env: rt.env,
            control: vec![(program, rt.env)],
        }
    }

    /// Restore the runtime + machine to `snap`, take one step, and read back the
    /// resulting snapshot. Returns `Ok(None)` if `snap` is already halted.
    fn step_from(&self, snap: &Snapshot) -> Result<Option<Snapshot>, FError> {
        if snap.is_halted() {
            return Ok(None);
        }
        let mut rt = self.rt.borrow_mut();
        // Restore the observable runtime state, then rebuild the machine's
        // reified continuation from the snapshot and step it once.
        rt.stack = snap.stack;
        rt.env = snap.env;
        let mut m = Machine::load(&mut rt, ValRef::NIL);
        m.restore(&snap.control);
        if !m.step()? {
            return Ok(None); // was halted after all
        }
        let control = m.control_pairs();
        let stack = m.forsp().stack;
        let env = m.forsp().env;
        Ok(Some(Snapshot {
            stack,
            env,
            control,
        }))
    }
}

impl<F: ForeignPrims> Semantics<ForspRepr> for ForspSemantics<F> {
    type StepCert = ForspStep;
    type Thm = StepTrace;
    type Error = FError;

    fn step(&self, term: &Snapshot) -> Result<Option<ForspStep>, FError> {
        match self.step_from(term)? {
            None => Ok(None),
            Some(after) => Ok(Some(ForspStep {
                to: after.clone(),
                trace: StepTrace {
                    states: vec![term.clone(), after],
                },
            })),
        }
    }

    fn compose(&self, prev: Option<StepTrace>, step_thm: StepTrace) -> Result<StepTrace, FError> {
        match prev {
            // First step: the two-state witness *is* the composite.
            None => Ok(step_thm),
            Some(mut acc) => {
                // Append the step's `after` (its `before` == acc's last).
                acc.states.extend(step_thm.states.into_iter().skip(1));
                Ok(acc)
            }
        }
    }
}

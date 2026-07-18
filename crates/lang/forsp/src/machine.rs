//! A **small-step machine** for Forsp — the reduction relation `/forsp` shows
//! step-by-step, mirroring the Lisp small-step semantics.
//!
//! The big-step [`eval::compute`](crate::eval) recurses through closure bodies
//! (a Rust call stack). To make evaluation an *inspectable, fuel-bounded step
//! sequence*, this module **reifies the continuation**: a [`Machine`] carries an
//! explicit control stack of [`Frame`]s (each an instruction-list cursor plus
//! the environment to restore when the frame completes). Each [`Machine::step`]
//! advances exactly **one** instruction — push a literal, resolve a name, fire a
//! primitive, or enter/leave a closure — so a program becomes a sequence of
//! machine states you can pull one at a time.
//!
//! The machine is defined against the *same* heap primitives and the *same*
//! `eval_one`/`exec_prim` semantics as the big-step engine — the differential
//! tests in `tests.rs` assert small-step and big-step agree on the final value.
//!
//! Forsp is **untrusted** eval (no kernel theory yet), so a step is witnessed by
//! a lightweight [`before`/`after` snapshot](crate::semantics::ForspStep), not a
//! kernel `Thm`. The trait wiring in [`crate::semantics`] is arranged so a
//! kernel-backed forsp theory can later drop in as a `Semantics` swap without
//! disturbing the driver. See the generated open-work index.

use super::{Cell, FError, ForeignPrims, Forsp, Heap, Prim, Tag, ValRef};

/// A frame of the reified continuation: an instruction-list cursor plus the
/// environment to restore to when this frame is exhausted.
///
/// The bottom frame's `saved_env` is the ambient environment; a frame pushed by
/// applying a closure carries the *caller's* environment, restored on exit — the
/// lexical-scope discipline the big-step engine gets from Rust's call stack.
#[derive(Clone, Copy, Debug)]
pub struct Frame {
    /// Remaining instructions in this frame (a cons-list cursor; NIL = done).
    pub ip: ValRef,
    /// Environment to restore when this frame is exhausted.
    pub saved_env: ValRef,
}

/// A snapshot of the machine's observable state: stack, environment, and the
/// depth of the reified continuation. Used as the lightweight before/after
/// witness of a [`Machine::step`].
#[derive(Clone, Copy, Debug)]
pub struct MachineState {
    /// The value stack (a cons-list; top is the car).
    pub stack: ValRef,
    /// The current environment (a cons-list of `(name . val)` pairs).
    pub env: ValRef,
    /// Continuation depth (number of active frames). `0` means halted.
    pub control_depth: usize,
}

/// The small-step Forsp machine over a [`Forsp`] runtime.
///
/// Owns a `&mut Forsp` (heap + stack + env + foreign) and a reified control
/// stack. [`step`](Machine::step) advances one instruction; [`state`] snapshots
/// the observable state.
pub struct Machine<'f, F: ForeignPrims = ()> {
    f: &'f mut Forsp<F>,
    /// The reified continuation. `control[len-1]` is the active frame.
    control: Vec<Frame>,
}

impl<'f, F: ForeignPrims> Machine<'f, F> {
    /// Load `program` (a parsed instruction list) into a fresh machine over `f`.
    /// The program runs in `f`'s current environment.
    pub fn load(f: &'f mut Forsp<F>, program: ValRef) -> Self {
        let saved_env = f.env;
        Machine {
            f,
            control: vec![Frame {
                ip: program,
                saved_env,
            }],
        }
    }

    /// Replace this machine's reified continuation with `frames` (as
    /// `(ip, saved_env)` pairs, active frame last). Used to restore a machine
    /// from a [`Snapshot`](crate::semantics::Snapshot) before taking a step.
    pub fn restore(&mut self, frames: &[(ValRef, ValRef)]) {
        self.control.clear();
        self.control.extend(
            frames
                .iter()
                .map(|&(ip, saved_env)| Frame { ip, saved_env }),
        );
    }

    /// Read the reified continuation back out as `(ip, saved_env)` pairs.
    pub fn control_pairs(&self) -> Vec<(ValRef, ValRef)> {
        self.control.iter().map(|f| (f.ip, f.saved_env)).collect()
    }

    /// Snapshot the observable machine state.
    pub fn state(&self) -> MachineState {
        MachineState {
            stack: self.f.stack,
            env: self.f.env,
            control_depth: self.control.len(),
        }
    }

    /// Has the machine halted (control stack empty)?
    pub fn is_halted(&self) -> bool {
        self.control.is_empty()
    }

    /// Borrow the underlying runtime (for rendering the final stack).
    pub fn forsp(&mut self) -> &mut Forsp<F> {
        self.f
    }

    /// Pop exhausted frames from the top of the control stack, restoring each
    /// frame's `saved_env` — this is the "return from a closure" transition.
    /// Returns `true` if a frame was popped (i.e. this counts as a step).
    fn unwind_done(&mut self) -> bool {
        let mut popped = false;
        while let Some(top) = self.control.last() {
            if top.ip.is_nil() {
                let frame = self.control.pop().expect("checked non-empty");
                self.f.env = frame.saved_env;
                popped = true;
            } else {
                break;
            }
        }
        popped
    }

    /// Advance the machine by **one** instruction.
    ///
    /// Returns `Ok(true)` if a step was taken (state may have changed),
    /// `Ok(false)` if the machine was already halted, or `Err` on a runtime
    /// fault. A step is one of: unwind an exhausted frame (closure return),
    /// `quote` a literal, or evaluate a single instruction (which may itself
    /// push a new frame when it applies a closure).
    pub fn step(&mut self) -> Result<bool, FError> {
        // First, retire any exhausted frames (a closure return is a step).
        if self.unwind_done() {
            return Ok(true);
        }
        let Some(&Frame { ip, .. }) = self.control.last() else {
            return Ok(false); // halted
        };
        debug_assert!(!ip.is_nil(), "unwind_done left an exhausted frame");

        let instr = self.f.heap.car(ip);
        let rest = self.f.heap.cdr(ip);

        // `quote` is the only special form: push the *next* value literally.
        if self.f.heap.tag(instr) == Tag::Atom && self.f.heap.as_atom(instr) == "quote" {
            if rest.is_nil() {
                return Err(FError::DanglingQuote);
            }
            let val = self.f.heap.car(rest);
            let rest2 = self.f.heap.cdr(rest);
            self.control.last_mut().unwrap().ip = rest2;
            self.f.push(val);
            return Ok(true);
        }

        // Ordinary instruction: consume it from the active frame, then evaluate.
        self.control.last_mut().unwrap().ip = rest;
        self.eval_one(instr)?;
        Ok(true)
    }

    /// Evaluate a single instruction. Mirrors [`eval::eval_one`](crate::eval),
    /// except applying a closure **pushes a control frame** instead of recursing.
    fn eval_one(&mut self, expr: ValRef) -> Result<(), FError> {
        match self.f.heap.tag(expr) {
            Tag::Int | Tag::Hash | Tag::Blob => self.f.push(expr),
            Tag::Nil | Tag::Cons => {
                let env = self.f.env;
                let clos = self.f.heap.closure(expr, env);
                self.f.push(clos);
            }
            Tag::Atom => {
                let name = expr;
                match env_find(&self.f.heap, self.f.env, name) {
                    Ok(val) => self.apply(val)?,
                    Err(FError::Unbound(nm)) => {
                        let Forsp {
                            ref mut foreign,
                            ref mut heap,
                            ref mut stack,
                            ..
                        } = *self.f;
                        let mut ctx = super::FCtx { heap, stack };
                        if !foreign.call(&nm, &mut ctx)? {
                            return Err(FError::Unbound(nm));
                        }
                    }
                    Err(e) => return Err(e),
                }
            }
            Tag::Closure | Tag::Prim => self.f.push(expr),
        }
        Ok(())
    }

    /// Apply a value: enter a closure (push a frame), fire a primitive, or push.
    /// Unlike the big-step [`apply`](crate::eval), entering a closure does *not*
    /// recurse — it pushes a [`Frame`] carrying the closure body and the
    /// environment to restore, so the next `step` begins the body.
    fn apply(&mut self, val: ValRef) -> Result<(), FError> {
        match self.f.heap.tag(val) {
            Tag::Closure => {
                let (body, cenv) = match self.f.heap.get(val) {
                    Cell::Closure { body, env } => (*body, *env),
                    _ => unreachable!(),
                };
                let saved = self.f.env;
                self.f.env = cenv;
                self.control.push(Frame {
                    ip: body,
                    saved_env: saved,
                });
            }
            Tag::Prim => {
                let p = match self.f.heap.get(val) {
                    Cell::Prim(p) => *p,
                    _ => unreachable!(),
                };
                self.exec_prim(p)?;
            }
            _ => self.f.push(val),
        }
        Ok(())
    }

    /// Fire a primitive. Delegates to the runtime; `force` re-enters
    /// [`apply`](Self::apply) so forcing a closure pushes a frame (small-step).
    fn exec_prim(&mut self, p: Prim) -> Result<(), FError> {
        if let Prim::Force = p {
            let val = self.f.try_pop()?;
            return self.apply(val);
        }
        // All other primitives are single-shot stack/heap effects with no
        // control-flow: run them through the shared implementation.
        crate::eval::exec_prim_pub(self.f, p)
    }
}

/// Look up `name` (an Atom ValRef) in the environment. Duplicated from
/// `eval` (private there) to keep the machine self-contained.
fn env_find(heap: &Heap, env: ValRef, name: ValRef) -> Result<ValRef, FError> {
    let target = heap.as_atom(name);
    let mut cur = env;
    while !cur.is_nil() {
        let pair = heap.car(cur);
        let key = heap.car(pair);
        if heap.tag(key) == Tag::Atom && heap.as_atom(key) == target {
            return Ok(heap.cdr(pair));
        }
        cur = heap.cdr(cur);
    }
    Err(FError::Unbound(target.to_string()))
}

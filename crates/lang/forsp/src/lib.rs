#![forbid(unsafe_code)]

pub(crate) mod eval;
mod hash;
pub mod machine;
mod print;
mod read;
pub mod semantics;

use std::collections::HashMap;
use std::fmt;

use covalence_hash::O256;
pub use covalence_sexp::SExpr;

use covalence_repl_core::{Fuel, Reduction, RunToValue, Status, Strategy};

pub use machine::{Frame, Machine, MachineState};
pub use semantics::{ForspRepr, ForspSemantics, ForspStep, Snapshot, StepTrace};

/// Forsp runtime error.
#[derive(Debug, thiserror::Error)]
pub enum FError {
    #[error("stack underflow")]
    StackUnderflow,
    #[error("{op}: expected {expected}, got {got}")]
    Type {
        op: &'static str,
        expected: &'static str,
        got: Tag,
    },
    #[error("unbound variable: {0}")]
    Unbound(String),
    #[error("quote at end of instruction list")]
    DanglingQuote,
    #[error("parse error: {0}")]
    Parse(String),
}

/// Context passed to foreign primitives for stack/heap manipulation.
pub struct FCtx<'a> {
    pub heap: &'a mut Heap,
    pub stack: &'a mut ValRef,
}

impl FCtx<'_> {
    pub fn push(&mut self, v: ValRef) {
        *self.stack = self.heap.cons(v, *self.stack);
    }

    pub fn try_pop(&mut self) -> Result<ValRef, FError> {
        if self.stack.is_nil() {
            return Err(FError::StackUnderflow);
        }
        let top = self.heap.car(*self.stack);
        *self.stack = self.heap.cdr(*self.stack);
        Ok(top)
    }

    /// Pop a value and extract it as a hash.
    pub fn try_pop_hash(&mut self) -> Result<O256, FError> {
        let v = self.try_pop()?;
        self.heap.try_as_hash(v)
    }

    /// Pop a value and extract it as a blob.
    pub fn try_pop_blob(&mut self) -> Result<Vec<u8>, FError> {
        let v = self.try_pop()?;
        self.heap.try_as_blob(v).map(|b| b.to_vec())
    }

    /// Push a hash onto the stack.
    pub fn push_hash(&mut self, h: O256) {
        let v = self.heap.hash(h);
        self.push(v);
    }

    /// Push a blob onto the stack.
    pub fn push_blob(&mut self, b: Vec<u8>) {
        let v = self.heap.blob(b);
        self.push(v);
    }

    /// Format a heap value as a Forsp S-expression string. Closures register
    /// their content hash on the heap as a side effect, so the result can be
    /// read back via the `!HEX` syntax.
    pub fn show(&mut self, v: ValRef) -> String {
        print::show(self.heap, v)
    }

    /// Compute the content hash of `v` (and register it for `!HEX` lookup).
    pub fn content_hash(&mut self, v: ValRef) -> O256 {
        self.heap.content_hash(v)
    }
}

/// External primitives for interacting with the environment.
/// Called when a name is not found in the Forsp environment
/// (i.e. symbol definitions take precedence).
pub trait ForeignPrims {
    /// Try to handle `name` as a primitive operation.
    /// Returns `Ok(true)` if handled, `Ok(false)` if unknown.
    fn call(&mut self, name: &str, ctx: &mut FCtx<'_>) -> Result<bool, FError>;
}

impl ForeignPrims for () {
    fn call(&mut self, _name: &str, _ctx: &mut FCtx<'_>) -> Result<bool, FError> {
        Ok(false)
    }
}

/// Index into the Forsp heap. NIL is always index 0.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ValRef(pub i32);

impl ValRef {
    pub const NIL: ValRef = ValRef(0);

    pub fn is_nil(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Debug for ValRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_nil() {
            write!(f, "NIL")
        } else {
            write!(f, "V({})", self.0)
        }
    }
}

/// Built-in primitive operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Prim {
    Push,
    Pop,
    Eq,
    Cons,
    Car,
    Cdr,
    Cswap,
    Tag,
    Force,
    Add,
    Sub,
    Mul,
    Nand,
    Lsh,
    Rsh,
    Stack,
    Env,
}

/// A cell in the Forsp heap.
#[derive(Clone, Debug)]
pub enum Cell {
    Nil,
    Atom(String),
    Int(i32),
    Hash(O256),
    Blob(Vec<u8>),
    Cons { car: ValRef, cdr: ValRef },
    Closure { body: ValRef, env: ValRef },
    Prim(Prim),
}

/// Value type tag (cheap discriminant without borrowing contents).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Tag {
    Nil,
    Atom,
    Int,
    Hash,
    Blob,
    Cons,
    Closure,
    Prim,
}

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Tag::Nil => "nil",
            Tag::Atom => "atom",
            Tag::Int => "int",
            Tag::Hash => "hash",
            Tag::Blob => "blob",
            Tag::Cons => "cons",
            Tag::Closure => "closure",
            Tag::Prim => "prim",
        })
    }
}

/// Arena of Forsp values. Index 0 is always NIL.
pub struct Heap {
    pub(crate) cells: Vec<Cell>,
    /// Memoised content hash per cell, populated lazily by [`Heap::content_hash`].
    pub(crate) hash_cache: Vec<Option<O256>>,
    /// Reverse index: content hash → most recent ValRef hashed to it.
    pub(crate) by_hash: HashMap<O256, ValRef>,
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

impl Heap {
    pub fn new() -> Self {
        Heap {
            cells: vec![Cell::Nil],
            hash_cache: vec![None],
            by_hash: HashMap::new(),
        }
    }

    pub fn alloc(&mut self, cell: Cell) -> ValRef {
        let idx = self.cells.len() as i32;
        self.cells.push(cell);
        self.hash_cache.push(None);
        ValRef(idx)
    }

    pub fn get(&self, r: ValRef) -> &Cell {
        &self.cells[r.0 as usize]
    }

    /// Compute (and cache) the content hash of `v`. Recursively hashes
    /// reachable subvalues. After this call, `v` (and every cell it
    /// transitively contains) can be recovered via [`Heap::value_at`].
    pub fn content_hash(&mut self, v: ValRef) -> O256 {
        hash::hash_of(self, v)
    }

    /// Look up a value previously hashed in this heap. Returns `None` if no
    /// cell with this hash has been registered (via [`Heap::content_hash`]
    /// or by printing a closure).
    pub fn value_at(&self, h: O256) -> Option<ValRef> {
        self.by_hash.get(&h).copied()
    }

    pub fn tag(&self, r: ValRef) -> Tag {
        match self.get(r) {
            Cell::Nil => Tag::Nil,
            Cell::Atom(_) => Tag::Atom,
            Cell::Int(_) => Tag::Int,
            Cell::Hash(_) => Tag::Hash,
            Cell::Blob(_) => Tag::Blob,
            Cell::Cons { .. } => Tag::Cons,
            Cell::Closure { .. } => Tag::Closure,
            Cell::Prim(_) => Tag::Prim,
        }
    }

    // --- constructors ---

    pub fn atom(&mut self, s: &str) -> ValRef {
        self.alloc(Cell::Atom(s.to_string()))
    }

    pub fn int(&mut self, n: i32) -> ValRef {
        self.alloc(Cell::Int(n))
    }

    pub fn hash(&mut self, h: O256) -> ValRef {
        self.alloc(Cell::Hash(h))
    }

    pub fn blob(&mut self, b: Vec<u8>) -> ValRef {
        self.alloc(Cell::Blob(b))
    }

    pub fn cons(&mut self, car: ValRef, cdr: ValRef) -> ValRef {
        self.alloc(Cell::Cons { car, cdr })
    }

    pub fn closure(&mut self, body: ValRef, env: ValRef) -> ValRef {
        self.alloc(Cell::Closure { body, env })
    }

    pub fn prim(&mut self, p: Prim) -> ValRef {
        self.alloc(Cell::Prim(p))
    }

    // --- fallible accessors ---

    pub fn try_car(&self, r: ValRef) -> Result<ValRef, FError> {
        match self.get(r) {
            Cell::Cons { car, .. } => Ok(*car),
            _ => Err(FError::Type {
                op: "car",
                expected: "cons",
                got: self.tag(r),
            }),
        }
    }

    pub fn try_cdr(&self, r: ValRef) -> Result<ValRef, FError> {
        match self.get(r) {
            Cell::Cons { cdr, .. } => Ok(*cdr),
            _ => Err(FError::Type {
                op: "cdr",
                expected: "cons",
                got: self.tag(r),
            }),
        }
    }

    pub fn try_as_atom(&self, r: ValRef) -> Result<&str, FError> {
        match self.get(r) {
            Cell::Atom(s) => Ok(s),
            _ => Err(FError::Type {
                op: "as_atom",
                expected: "atom",
                got: self.tag(r),
            }),
        }
    }

    pub fn try_as_int(&self, r: ValRef) -> Result<i32, FError> {
        match self.get(r) {
            Cell::Int(n) => Ok(*n),
            _ => Err(FError::Type {
                op: "as_int",
                expected: "int",
                got: self.tag(r),
            }),
        }
    }

    pub fn try_as_hash(&self, r: ValRef) -> Result<O256, FError> {
        match self.get(r) {
            Cell::Hash(h) => Ok(*h),
            _ => Err(FError::Type {
                op: "as_hash",
                expected: "hash",
                got: self.tag(r),
            }),
        }
    }

    pub fn try_as_blob(&self, r: ValRef) -> Result<&[u8], FError> {
        match self.get(r) {
            Cell::Blob(b) => Ok(b),
            _ => Err(FError::Type {
                op: "as_blob",
                expected: "blob",
                got: self.tag(r),
            }),
        }
    }

    // --- panicking accessors (for printer / known-good contexts) ---

    pub fn car(&self, r: ValRef) -> ValRef {
        self.try_car(r).unwrap()
    }

    pub fn cdr(&self, r: ValRef) -> ValRef {
        self.try_cdr(r).unwrap()
    }

    pub fn as_atom(&self, r: ValRef) -> &str {
        self.try_as_atom(r).unwrap()
    }

    pub fn as_int(&self, r: ValRef) -> i32 {
        self.try_as_int(r).unwrap()
    }

    pub fn as_hash(&self, r: ValRef) -> O256 {
        self.try_as_hash(r).unwrap()
    }

    pub fn as_blob(&self, r: ValRef) -> &[u8] {
        self.try_as_blob(r).unwrap()
    }
}

/// Forsp runtime: heap + stack + environment + foreign primitives.
pub struct Forsp<F: ForeignPrims = ()> {
    pub heap: Heap,
    pub stack: ValRef,
    pub env: ValRef,
    pub foreign: F,
}

impl Default for Forsp<()> {
    fn default() -> Self {
        Self::new()
    }
}

impl Forsp<()> {
    pub fn new() -> Self {
        Self::new_with(())
    }
}

impl<F: ForeignPrims> Forsp<F> {
    pub fn new_with(foreign: F) -> Self {
        let mut f = Forsp {
            heap: Heap::new(),
            stack: ValRef::NIL,
            env: ValRef::NIL,
            foreign,
        };
        f.init_env();
        f
    }

    fn init_env(&mut self) {
        let prims: &[(&str, Prim)] = &[
            ("push", Prim::Push),
            ("pop", Prim::Pop),
            ("eq", Prim::Eq),
            ("cons", Prim::Cons),
            ("car", Prim::Car),
            ("cdr", Prim::Cdr),
            ("cswap", Prim::Cswap),
            ("tag", Prim::Tag),
            ("force", Prim::Force),
            ("+", Prim::Add),
            ("-", Prim::Sub),
            ("*", Prim::Mul),
            ("nand", Prim::Nand),
            ("<<", Prim::Lsh),
            (">>", Prim::Rsh),
            ("stack", Prim::Stack),
            ("env", Prim::Env),
        ];
        for &(name, prim) in prims {
            let name_ref = self.heap.atom(name);
            let prim_ref = self.heap.prim(prim);
            let pair = self.heap.cons(name_ref, prim_ref);
            self.env = self.heap.cons(pair, self.env);
        }
    }

    /// Parse a Forsp source string into a cons-list of instructions.
    /// Sugar (`'x`, `$x`, `^x`) is expanded inline (spliced).
    pub fn read(&mut self, source: &str) -> Result<ValRef, FError> {
        read::read(&mut self.heap, source)
    }

    /// Read a single S-expression value from a source string.
    pub fn read_one(&mut self, source: &str) -> Result<ValRef, FError> {
        read::read_one(&mut self.heap, source)
    }

    /// Convert a heap value to an [`SExpr`] for external consumption.
    /// Closures are rendered as `!<hash>` and registered on the heap as a
    /// side effect, so the resulting sexp can be read back through `read`.
    pub fn to_sexp(&mut self, v: ValRef) -> SExpr {
        print::to_sexp(&mut self.heap, v)
    }

    /// Format a heap value as a Forsp S-expression string. See [`to_sexp`](Self::to_sexp).
    pub fn show(&mut self, v: ValRef) -> String {
        print::show(&mut self.heap, v)
    }

    /// Compute the content hash of `v` (and register it for `!HEX` lookup).
    pub fn content_hash(&mut self, v: ValRef) -> O256 {
        self.heap.content_hash(v)
    }

    /// Execute a parsed instruction list (the result of [`read`](Self::read)).
    pub fn exec(&mut self, program: ValRef) -> Result<(), FError> {
        eval::compute(self, program)
    }

    /// Convenience: read + exec.
    pub fn run(&mut self, source: &str) -> Result<(), FError> {
        let program = self.read(source)?;
        self.exec(program)
    }

    // -- stack helpers --

    pub(crate) fn push(&mut self, v: ValRef) {
        self.stack = self.heap.cons(v, self.stack);
    }

    pub(crate) fn try_pop(&mut self) -> Result<ValRef, FError> {
        if self.stack.is_nil() {
            return Err(FError::StackUnderflow);
        }
        let top = self.heap.car(self.stack);
        self.stack = self.heap.cdr(self.stack);
        Ok(top)
    }

    pub fn try_peek(&self) -> Result<ValRef, FError> {
        if self.stack.is_nil() {
            return Err(FError::StackUnderflow);
        }
        Ok(self.heap.car(self.stack))
    }

    // -- panicking convenience (tests) --

    /// Pop a value (panics on underflow).
    pub fn pop(&mut self) -> ValRef {
        self.try_pop().unwrap()
    }

    /// Pop and extract an integer.
    pub fn pop_int(&mut self) -> i32 {
        let v = self.pop();
        self.heap.as_int(v)
    }

    /// Pop and extract an atom string.
    pub fn pop_atom(&mut self) -> String {
        let v = self.pop();
        self.heap.as_atom(v).to_string()
    }

    /// Pop and extract a hash.
    pub fn pop_hash(&mut self) -> O256 {
        let v = self.pop();
        self.heap.as_hash(v)
    }

    /// Pop and extract a blob.
    pub fn pop_blob(&mut self) -> Vec<u8> {
        let v = self.pop();
        self.heap.as_blob(v).to_vec()
    }
}

/// The result of a small-step Forsp reduction: the full step trace (a sequence
/// of machine [`Snapshot`]s), the final stack, the step count, and the streaming
/// [`Status`]. The `/forsp` endpoint renders the trace as reduction steps.
///
/// `status` is [`Status::Value`] when the machine halted, or
/// [`Status::Diverging`] when a fuel bound stopped it with work remaining
/// (pull again with more fuel — never a hang).
pub struct ForspReduction {
    /// The ordered machine snapshots visited (input first, current head last).
    pub trace: StepTrace,
    /// The final value stack (a cons-list; top is car).
    pub final_stack: ValRef,
    /// How many small steps were taken.
    pub steps: u64,
    /// Streaming status of the head snapshot.
    pub status: Status,
}

impl<F: ForeignPrims> Forsp<F> {
    /// Reduce `program` (a parsed instruction list) **step by step**, returning
    /// the [`ForspReduction`] — the trace of machine states plus the final
    /// stack. `fuel` bounds the number of steps: use [`Fuel::UNBOUNDED`] to run
    /// to a halt, or [`Fuel::steps(n)`](Fuel::steps) for an inspectable prefix
    /// (a diverging program then reports [`Status::Diverging`] rather than
    /// hanging).
    ///
    /// This is the differential twin of [`exec`](Self::exec): for a terminating
    /// program the final stack matches what `exec` leaves behind. The `/forsp`
    /// endpoint calls this to render reduction steps.
    ///
    /// Consumes `self` (the semantics needs to own the runtime + heap); the
    /// runtime is recoverable via [`ForspReduction`] state if needed later.
    pub fn forsp_reduce(self, program: ValRef, fuel: Fuel) -> Result<ForspReduction, FError> {
        let sem = ForspSemantics::new(self);
        let input = sem.initial(program);
        let mut red: Reduction<ForspRepr, ForspSemantics<F>> = Reduction::start(input);
        RunToValue.drive(&sem, &mut red, fuel)?;

        let status = red.status();
        let steps = red.steps();
        let (head, composite) = red.into_parts();
        // The composite trace is `None` iff no step was taken (program was
        // already halted / empty); then the trace is just the single input.
        let trace = composite.unwrap_or_else(|| StepTrace {
            states: vec![head.clone()],
        });
        let final_stack = head.stack;
        Ok(ForspReduction {
            trace,
            final_stack,
            steps,
            status,
        })
    }

    /// Read + small-step reduce, running to a halt. Convenience over
    /// [`read`](Self::read) + [`forsp_reduce`](Self::forsp_reduce).
    pub fn reduce_source(self, source: &str) -> Result<ForspReduction, FError> {
        let mut this = self;
        let program = this.read(source)?;
        this.forsp_reduce(program, Fuel::UNBOUNDED)
    }
}

/// Build a proper cons-list from a slice of ValRefs.
fn vec_to_list(heap: &mut Heap, elems: &[ValRef]) -> ValRef {
    let mut list = ValRef::NIL;
    for &e in elems.iter().rev() {
        list = heap.cons(e, list);
    }
    list
}

#[cfg(test)]
mod tests;

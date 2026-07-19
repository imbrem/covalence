//! Concatenative/stack-machine capabilities for Forth–Lisp hybrids.
//!
//! Forsp shares S-expression data, lexical environments, closures, and the
//! generic execution relation with applicative Lisps, but it does not lower
//! naturally to function-position application. This module keeps the common
//! API tower wide enough for both styles without pretending they are the same
//! operational semantics.
//!
//! @covalence-api {"id":"A0023","title":"Concatenative Lisp stack machines","status":"experimental","dependsOn":["A0022"]}

/// A suspended caller for a lexical stack-machine closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackContinuation<C, E> {
    pub code: C,
    pub cursor: usize,
    pub environment: E,
}

/// A stack-machine configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackConfiguration<C, V, E> {
    pub code: C,
    pub cursor: usize,
    pub operands: Vec<V>,
    pub environment: E,
    pub continuations: Vec<StackContinuation<C, E>>,
}

impl<C, V, E> StackConfiguration<C, V, E> {
    pub fn new(code: C, environment: E) -> Self {
        Self {
            code,
            cursor: 0,
            operands: Vec::new(),
            environment,
            continuations: Vec::new(),
        }
    }
}

/// WIT-shaped constructors for concatenative instructions.
///
/// `Code`, `Value`, and `Instruction` can become opaque component resources.
/// The interface does not expose Rust callbacks or a concrete representation.
pub trait StackInstructionSyntax {
    type Symbol: Clone;
    type Datum: Clone;
    type Primitive: Clone;
    type Code: Clone;
    type Instruction: Clone;
    type Error;

    fn literal(&self, datum: Self::Datum) -> Result<Self::Instruction, Self::Error>;
    fn quote(&self, datum: Self::Datum) -> Result<Self::Instruction, Self::Error>;
    fn closure(&self, code: Self::Code) -> Result<Self::Instruction, Self::Error>;
    fn bind(&self, name: Self::Symbol) -> Result<Self::Instruction, Self::Error>;
    fn push_binding(&self, name: Self::Symbol) -> Result<Self::Instruction, Self::Error>;
    fn resolve(&self, name: Self::Symbol) -> Result<Self::Instruction, Self::Error>;
    fn primitive(&self, primitive: Self::Primitive) -> Result<Self::Instruction, Self::Error>;
}

/// Construction and observation of instruction sequences.
pub trait StackProgramSyntax: StackInstructionSyntax {
    fn program(&self, instructions: Vec<Self::Instruction>) -> Result<Self::Code, Self::Error>;
    fn instructions(&self, code: &Self::Code) -> Result<Vec<Self::Instruction>, Self::Error>;
}

//! Concatenative/stack-machine capabilities for Forth–Lisp hybrids.
//!
//! Forsp shares S-expression data, lexical environments, closures, and the
//! generic execution relation with applicative Lisps, but it does not lower
//! naturally to function-position application. This module keeps the common
//! API tower wide enough for both styles without pretending they are the same
//! operational semantics.
//!
//! @covalence-api {"id":"A0023","title":"Concatenative Lisp stack machines","status":"experimental","dependsOn":["A0022"]}

use covalence_sexpr_api::SExprView;

use crate::runtime::LispEnvironment;

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

/// Public observation of a concatenative Lisp value.
///
/// Closure contents remain opaque to ordinary clients; only the evaluator's
/// [`StackMachineValue`] capability can recover them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackValueView<D> {
    Datum(D),
    Closure,
}

/// Privileged machine-facing layer of a concatenative Lisp value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackValueLayer<D, C> {
    Datum(D),
    Closure(C),
}

/// Construction and public observation of stack-machine values.
pub trait StackValue {
    type Datum: Clone;
    type Value: Clone;
    type Error;

    fn datum(&self, datum: Self::Datum) -> Result<Self::Value, Self::Error>;
    fn view(&self, value: &Self::Value) -> Result<StackValueView<Self::Datum>, Self::Error>;
    fn equivalent(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error>;
}

/// Privileged closure roll/unroll operations for a stack evaluator.
pub trait StackMachineValue: StackValue {
    type Closure: Clone;

    fn roll(
        &self,
        layer: StackValueLayer<Self::Datum, Self::Closure>,
    ) -> Result<Self::Value, Self::Error>;
    fn unroll(
        &self,
        value: &Self::Value,
    ) -> Result<StackValueLayer<Self::Datum, Self::Closure>, Self::Error>;
}

/// Contents of an opaque lexical stack closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackClosureRecord<C, E> {
    pub code: C,
    pub environment: E,
}

/// Construction and observation of lexical stack-closure resources.
pub trait StackClosure {
    type Code: Clone;
    type Environment: Clone;
    type Closure: Clone;
    type Error;

    fn close(
        &self,
        record: StackClosureRecord<Self::Code, Self::Environment>,
    ) -> Result<Self::Closure, Self::Error>;
    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<StackClosureRecord<Self::Code, Self::Environment>, Self::Error>;
}

/// Coherent representation bundle for a concatenative Lisp machine.
///
/// This is a sibling of [`crate::LispRuntime`], not a subtype of it:
/// applicative Lisps close over expressions, whereas Forsp-style languages
/// close over instruction sequences. Both bundles reuse the same inductive
/// data and lexical-environment capabilities.
pub trait StackRuntime {
    type Symbol: Clone;
    type Atom: Clone;
    type Datum: Clone;
    type Primitive: Clone;
    type Instruction: Clone;
    type Code: Clone;
    type Value: Clone;
    type Closure: Clone;
    type Environment: Clone;
    type Error;

    type Data: SExprView<Payload = Self::Atom, Value = Self::Datum>;
    type Syntax: StackProgramSyntax<
            Symbol = Self::Symbol,
            Datum = Self::Datum,
            Primitive = Self::Primitive,
            Instruction = Self::Instruction,
            Code = Self::Code,
        >;
    type Values: StackMachineValue<Datum = Self::Datum, Value = Self::Value, Closure = Self::Closure>;
    type Closures: StackClosure<Code = Self::Code, Environment = Self::Environment, Closure = Self::Closure>;
    type Environments: LispEnvironment<Symbol = Self::Symbol, Value = Self::Value, Environment = Self::Environment>;

    fn data(&self) -> &Self::Data;
    fn syntax(&self) -> &Self::Syntax;
    fn values(&self) -> &Self::Values;
    fn closures(&self) -> &Self::Closures;
    fn environments(&self) -> &Self::Environments;

    fn data_error(
        &self,
        error: <Self::Data as covalence_sexpr_api::SExprSyntax>::Error,
    ) -> Self::Error;
    fn syntax_error(&self, error: <Self::Syntax as StackInstructionSyntax>::Error) -> Self::Error;
    fn value_error(&self, error: <Self::Values as StackValue>::Error) -> Self::Error;
    fn closure_error(&self, error: <Self::Closures as StackClosure>::Error) -> Self::Error;
    fn environment_error(
        &self,
        error: <Self::Environments as LispEnvironment>::Error,
    ) -> Self::Error;
}

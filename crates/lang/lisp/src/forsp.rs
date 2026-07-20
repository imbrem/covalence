//! Proof-free Forsp frontend over the common Lisp stack-machine capabilities.
//!
//! Forsp is a Forth–Lisp hybrid: lists in computation position form lexical
//! closures, values flow through an operand stack, `$name` pops and binds,
//! `^name` pushes without calling, and a bare bound closure is invoked. This
//! implementation deliberately excludes I/O and unsafe pointer primitives;
//! those are effects above the pure operational core.

use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use std::str::FromStr;
use std::sync::Arc;

use covalence_kernel_lisp::sexpr::{Free, ProperList, SExprF, SExprSyntax, SExprView};
use covalence_kernel_lisp::{
    Datum, DeterministicStep, EffectHandler, EffectResume, EffectState, EffectSuspension,
    HostEnvironment, HostEnvironments, LispEnvironment, RuntimeBinding, StackClosure,
    StackClosureRecord, StackConfiguration, StackContinuation, StackInstructionSyntax,
    StackMachineValue, StackProgramSyntax, StackRuntime, StackValue, StackValueLayer,
    StackValueView, StepRelation, TerminalValue,
};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use crate::frontend::CoreAtom;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ForspPrimitive {
    Eq,
    Cons,
    Car,
    Cdr,
    Cswap,
    Add,
    Subtract,
    Multiply,
    Stack,
}

/// Effects in the reference Forsp implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ForspEffect {
    Read,
    Print,
    PointerState,
    PointerRead,
    PointerWrite,
    PointerToObject,
    PointerFromObject,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspInstruction {
    Literal(Datum<CoreAtom>),
    Quote(Datum<CoreAtom>),
    Closure(ForspCode),
    Bind(String),
    PushBinding(String),
    Resolve(String),
    Primitive(ForspPrimitive),
    Effect(ForspEffect),
}

pub type ForspCode = Arc<[ForspInstruction]>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForspClosure {
    pub code: ForspCode,
    pub environment: ForspEnvironment,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspValue {
    Datum(Datum<CoreAtom>),
    Closure(Arc<ForspClosure>),
}

pub type ForspEnvironment = HostEnvironment<String, ForspValue>;
pub type ForspConfiguration = StackConfiguration<ForspCode, ForspValue, ForspEnvironment>;

#[derive(Clone, Copy, Debug, Default)]
pub struct ForspValues;

impl StackValue for ForspValues {
    type Datum = Datum<CoreAtom>;
    type Value = ForspValue;
    type Error = Infallible;

    fn datum(&self, datum: Self::Datum) -> Result<Self::Value, Self::Error> {
        Ok(ForspValue::Datum(datum))
    }

    fn view(&self, value: &Self::Value) -> Result<StackValueView<Self::Datum>, Self::Error> {
        Ok(match value {
            ForspValue::Datum(datum) => StackValueView::Datum(datum.clone()),
            ForspValue::Closure(_) => StackValueView::Closure,
        })
    }

    fn equivalent(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        Ok(left == right)
    }
}

impl StackMachineValue for ForspValues {
    type Closure = Arc<ForspClosure>;

    fn roll(
        &self,
        layer: StackValueLayer<Self::Datum, Self::Closure>,
    ) -> Result<Self::Value, Self::Error> {
        Ok(match layer {
            StackValueLayer::Datum(datum) => ForspValue::Datum(datum),
            StackValueLayer::Closure(closure) => ForspValue::Closure(closure),
        })
    }

    fn unroll(
        &self,
        value: &Self::Value,
    ) -> Result<StackValueLayer<Self::Datum, Self::Closure>, Self::Error> {
        Ok(match value {
            ForspValue::Datum(datum) => StackValueLayer::Datum(datum.clone()),
            ForspValue::Closure(closure) => StackValueLayer::Closure(Arc::clone(closure)),
        })
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ForspClosures;

impl StackClosure for ForspClosures {
    type Code = ForspCode;
    type Environment = ForspEnvironment;
    type Closure = Arc<ForspClosure>;
    type Error = Infallible;

    fn close(
        &self,
        record: StackClosureRecord<Self::Code, Self::Environment>,
    ) -> Result<Self::Closure, Self::Error> {
        Ok(Arc::new(ForspClosure {
            code: record.code,
            environment: record.environment,
        }))
    }

    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<StackClosureRecord<Self::Code, Self::Environment>, Self::Error> {
        Ok(StackClosureRecord {
            code: closure.code.clone(),
            environment: closure.environment.clone(),
        })
    }
}

/// Direct Rust realization of the abstract concatenative runtime.
#[derive(Clone, Debug)]
pub struct ForspRuntime {
    data: Free<CoreAtom>,
    syntax: ForspSyntax,
    values: ForspValues,
    closures: ForspClosures,
    environments: HostEnvironments<String, ForspValue>,
}

impl Default for ForspRuntime {
    fn default() -> Self {
        Self {
            data: Free::new(),
            syntax: ForspSyntax,
            values: ForspValues,
            closures: ForspClosures,
            environments: HostEnvironments::default(),
        }
    }
}

impl StackRuntime for ForspRuntime {
    type Symbol = String;
    type Atom = CoreAtom;
    type Datum = Datum<CoreAtom>;
    type Primitive = ForspPrimitive;
    type Instruction = ForspInstruction;
    type Code = ForspCode;
    type Value = ForspValue;
    type Closure = Arc<ForspClosure>;
    type Environment = ForspEnvironment;
    type Error = Infallible;
    type Data = Free<CoreAtom>;
    type Syntax = ForspSyntax;
    type Values = ForspValues;
    type Closures = ForspClosures;
    type Environments = HostEnvironments<String, ForspValue>;

    fn data(&self) -> &Self::Data {
        &self.data
    }

    fn syntax(&self) -> &Self::Syntax {
        &self.syntax
    }

    fn values(&self) -> &Self::Values {
        &self.values
    }

    fn closures(&self) -> &Self::Closures {
        &self.closures
    }

    fn environments(&self) -> &Self::Environments {
        &self.environments
    }

    fn data_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn syntax_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn value_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn closure_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }

    fn environment_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspRequest {
    Read,
    Print(ForspValue),
    PointerState,
    PointerRead(ForspValue),
    PointerWrite {
        address: ForspValue,
        value: ForspValue,
    },
    PointerToObject(ForspValue),
    PointerFromObject(ForspValue),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspResponse {
    Value(ForspValue),
    Unit,
}

pub type ForspEffectState = EffectState<ForspConfiguration, ForspRequest>;

/// Host I/O capability for the safe reference effects.
pub trait ForspIo {
    type Error;

    fn read(&mut self) -> Result<ForspValue, Self::Error>;
    fn print(&mut self, value: &ForspValue) -> Result<(), Self::Error>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspIoHandlerError<E> {
    Io(E),
    UnsafeRequest,
}

/// Proof-free adapter from safe Forsp requests to a host I/O capability.
pub struct ForspIoHandler<H> {
    pub host: H,
}

impl<H: ForspIo> EffectHandler<ForspRequest, ForspResponse> for ForspIoHandler<H> {
    type Error = ForspIoHandlerError<H::Error>;

    fn handle(&mut self, request: &ForspRequest) -> Result<ForspResponse, Self::Error> {
        match request {
            ForspRequest::Read => self
                .host
                .read()
                .map(ForspResponse::Value)
                .map_err(ForspIoHandlerError::Io),
            ForspRequest::Print(value) => self
                .host
                .print(value)
                .map(|()| ForspResponse::Unit)
                .map_err(ForspIoHandlerError::Io),
            ForspRequest::PointerState
            | ForspRequest::PointerRead(_)
            | ForspRequest::PointerWrite { .. }
            | ForspRequest::PointerToObject(_)
            | ForspRequest::PointerFromObject(_) => Err(ForspIoHandlerError::UnsafeRequest),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspError {
    EmptyStack,
    Unbound(String),
    ExpectedDatum,
    ExpectedCons,
    ExpectedInteger,
    MalformedQuote,
    UnhandledEffect(ForspEffect),
    InvalidEffectResponse,
}

impl Display for ForspError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyStack => f.write_str("Forsp operand stack is empty"),
            Self::Unbound(name) => write!(f, "unbound Forsp name `{name}`"),
            Self::ExpectedDatum => f.write_str("Forsp primitive expected data, not a closure"),
            Self::ExpectedCons => f.write_str("Forsp projection expected a cons cell"),
            Self::ExpectedInteger => f.write_str("Forsp arithmetic expected exact integers"),
            Self::MalformedQuote => f.write_str("Forsp `quote` has no following datum"),
            Self::UnhandledEffect(effect) => {
                write!(f, "Forsp effect `{effect:?}` requires an explicit handler")
            }
            Self::InvalidEffectResponse => {
                f.write_str("Forsp handler returned a response of the wrong shape")
            }
        }
    }
}

impl core::error::Error for ForspError {}

#[derive(Clone, Copy, Debug, Default)]
pub struct ForspSyntax;

impl StackInstructionSyntax for ForspSyntax {
    type Symbol = String;
    type Datum = Datum<CoreAtom>;
    type Primitive = ForspPrimitive;
    type Code = ForspCode;
    type Instruction = ForspInstruction;
    type Error = core::convert::Infallible;

    fn literal(&self, datum: Self::Datum) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::Literal(datum))
    }

    fn quote(&self, datum: Self::Datum) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::Quote(datum))
    }

    fn closure(&self, code: Self::Code) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::Closure(code))
    }

    fn bind(&self, name: Self::Symbol) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::Bind(name))
    }

    fn push_binding(&self, name: Self::Symbol) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::PushBinding(name))
    }

    fn resolve(&self, name: Self::Symbol) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::Resolve(name))
    }

    fn primitive(&self, primitive: Self::Primitive) -> Result<Self::Instruction, Self::Error> {
        Ok(ForspInstruction::Primitive(primitive))
    }
}

impl StackProgramSyntax for ForspSyntax {
    fn program(&self, instructions: Vec<ForspInstruction>) -> Result<ForspCode, Self::Error> {
        Ok(instructions.into())
    }

    fn instructions(&self, code: &ForspCode) -> Result<Vec<ForspInstruction>, Self::Error> {
        Ok(code.to_vec())
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ForspFrontend;

impl ForspFrontend {
    pub fn lower(&self, form: &SExpr) -> Result<ForspCode, ForspError> {
        let items = form
            .as_list()
            .map_or_else(|| core::slice::from_ref(form), |items| items);
        self.lower_sequence(items)
    }

    pub fn quote(&self, form: &SExpr) -> Datum<CoreAtom> {
        match form {
            SExpr::Atom(Atom::Symbol(text)) => Int::from_str(text).map_or_else(
                |_| Datum::Atom(CoreAtom::symbol(text.as_bytes())),
                |integer| Datum::Atom(CoreAtom::Integer(integer)),
            ),
            SExpr::Atom(Atom::Str { format, bytes }) => Datum::Atom(CoreAtom::String {
                format: format.to_string(),
                bytes: bytes.to_vec(),
            }),
            SExpr::List(items) => Datum::list(items.iter().map(|item| self.quote(item))),
        }
    }

    fn lower_sequence(&self, items: &[SExpr]) -> Result<ForspCode, ForspError> {
        let mut instructions = Vec::new();
        let mut cursor = 0;
        while cursor < items.len() {
            if items[cursor].as_symbol() == Some("quote") {
                let datum = items.get(cursor + 1).ok_or(ForspError::MalformedQuote)?;
                instructions.push(ForspInstruction::Quote(self.quote(datum)));
                cursor += 2;
                continue;
            }
            instructions.push(self.lower_item(&items[cursor])?);
            cursor += 1;
        }
        Ok(instructions.into())
    }

    fn lower_item(&self, form: &SExpr) -> Result<ForspInstruction, ForspError> {
        Ok(match form {
            SExpr::List(items) if items.len() == 2 && items[0].as_symbol() == Some("quote") => {
                ForspInstruction::Quote(self.quote(&items[1]))
            }
            SExpr::List(items) => ForspInstruction::Closure(self.lower_sequence(items)?),
            SExpr::Atom(Atom::Str { .. }) => ForspInstruction::Literal(self.quote(form)),
            SExpr::Atom(Atom::Symbol(text)) => {
                if let Some(name) = text.strip_prefix('$') {
                    ForspInstruction::Bind(name.to_owned())
                } else if let Some(name) = text.strip_prefix('^') {
                    ForspInstruction::PushBinding(name.to_owned())
                } else if Int::from_str(text).is_ok() {
                    ForspInstruction::Literal(self.quote(form))
                } else if let Some(primitive) = primitive(text) {
                    ForspInstruction::Primitive(primitive)
                } else if let Some(effect) = effect(text) {
                    ForspInstruction::Effect(effect)
                } else {
                    ForspInstruction::Resolve(text.to_string())
                }
            }
        })
    }
}

/// Read Forsp source, expanding apostrophe quote sugar and accepting its
/// single-semicolon line comments.
pub fn read(source: &str) -> Result<Vec<SExpr>, covalence_sexp::ParseError> {
    let normalized = ForspSurface::new(source).normalize()?;
    covalence_sexp::parse_smt(&normalized)
}

struct ForspSurface<'a> {
    source: &'a str,
    cursor: usize,
    output: String,
}

impl<'a> ForspSurface<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            cursor: 0,
            output: String::with_capacity(source.len()),
        }
    }

    fn normalize(mut self) -> Result<String, covalence_sexp::ParseError> {
        self.trivia();
        while self.cursor < self.source.len() {
            self.form()?;
            self.trivia();
        }
        Ok(self.output)
    }

    fn form(&mut self) -> Result<(), covalence_sexp::ParseError> {
        match self
            .peek()
            .ok_or_else(|| self.error("expected Forsp form"))?
        {
            b'\'' => {
                self.cursor += 1;
                self.output.push_str("(quote ");
                self.trivia();
                self.form()?;
                self.output.push(')');
            }
            b'(' => {
                self.cursor += 1;
                self.output.push('(');
                self.trivia();
                while self.peek() != Some(b')') {
                    if self.cursor == self.source.len() {
                        return Err(self.error("unclosed Forsp list"));
                    }
                    self.form()?;
                    self.trivia();
                }
                self.cursor += 1;
                self.output.push(')');
            }
            b')' => return Err(self.error("unexpected ')'")),
            b'"' => self.string()?,
            _ => self.atom(),
        }
        Ok(())
    }

    fn trivia(&mut self) {
        loop {
            while self.peek().is_some_and(|byte| byte.is_ascii_whitespace()) {
                self.output
                    .push(self.source.as_bytes()[self.cursor] as char);
                self.cursor += 1;
            }
            if self.peek() != Some(b';') {
                return;
            }
            while let Some(byte) = self.peek() {
                self.cursor += 1;
                if byte == b'\n' {
                    self.output.push('\n');
                    break;
                }
            }
        }
    }

    fn string(&mut self) -> Result<(), covalence_sexp::ParseError> {
        let start = self.cursor;
        self.output.push('"');
        self.cursor += 1;
        while let Some(byte) = self.peek() {
            self.output.push(byte as char);
            self.cursor += 1;
            match byte {
                b'\\' => {
                    let escaped = self
                        .peek()
                        .ok_or_else(|| self.error_at(start, "unterminated Forsp string escape"))?;
                    self.output.push(escaped as char);
                    self.cursor += 1;
                }
                b'"' => return Ok(()),
                _ => {}
            }
        }
        Err(self.error_at(start, "unterminated Forsp string"))
    }

    fn atom(&mut self) {
        while let Some(byte) = self.peek() {
            if byte.is_ascii_whitespace() || matches!(byte, b'(' | b')' | b';' | b'\'') {
                break;
            }
            let ch = self.source[self.cursor..]
                .chars()
                .next()
                .expect("not at eof");
            self.output.push(ch);
            self.cursor += ch.len_utf8();
        }
    }

    fn peek(&self) -> Option<u8> {
        self.source.as_bytes().get(self.cursor).copied()
    }

    fn error(&self, message: impl Into<String>) -> covalence_sexp::ParseError {
        self.error_at(self.cursor, message)
    }

    fn error_at(&self, offset: usize, message: impl Into<String>) -> covalence_sexp::ParseError {
        covalence_sexp::ParseError {
            offset,
            message: message.into(),
        }
    }
}

fn primitive(name: &str) -> Option<ForspPrimitive> {
    Some(match name {
        "eq" => ForspPrimitive::Eq,
        "cons" => ForspPrimitive::Cons,
        "car" => ForspPrimitive::Car,
        "cdr" => ForspPrimitive::Cdr,
        "cswap" => ForspPrimitive::Cswap,
        "+" => ForspPrimitive::Add,
        "-" => ForspPrimitive::Subtract,
        "*" => ForspPrimitive::Multiply,
        "stack" => ForspPrimitive::Stack,
        _ => return None,
    })
}

fn effect(name: &str) -> Option<ForspEffect> {
    Some(match name {
        "read" => ForspEffect::Read,
        "print" => ForspEffect::Print,
        "ptr-state" => ForspEffect::PointerState,
        "ptr-read" => ForspEffect::PointerRead,
        "ptr-write" => ForspEffect::PointerWrite,
        "ptr-to-obj" => ForspEffect::PointerToObject,
        "ptr-from-obj" => ForspEffect::PointerFromObject,
        _ => return None,
    })
}

type StackConfigurationOf<R> = StackConfiguration<
    <R as StackRuntime>::Code,
    <R as StackRuntime>::Value,
    <R as StackRuntime>::Environment,
>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeForspError<E> {
    Language(ForspError),
    Runtime(E),
}

impl<E: Display> Display for RuntimeForspError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Language(error) => Display::fmt(error, f),
            Self::Runtime(error) => write!(f, "Forsp runtime failed: {error}"),
        }
    }
}

impl<E: Debug + Display> core::error::Error for RuntimeForspError<E> {}

impl<E> From<ForspError> for RuntimeForspError<E> {
    fn from(error: ForspError) -> Self {
        Self::Language(error)
    }
}

/// Concatenative evaluator over an abstract stack runtime.
#[derive(Clone, Debug)]
pub struct RuntimeForspMachine<R> {
    runtime: R,
}

impl<R> RuntimeForspMachine<R> {
    pub fn new(runtime: R) -> Self {
        Self { runtime }
    }

    pub fn runtime(&self) -> &R {
        &self.runtime
    }
}

impl<R> RuntimeForspMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
        >,
{
    pub fn initial(&self, code: R::Code) -> StackConfigurationOf<R> {
        StackConfiguration::new(code, self.runtime.environments().empty())
    }

    fn pop(
        configuration: &mut StackConfigurationOf<R>,
    ) -> Result<R::Value, RuntimeForspError<R::Error>> {
        configuration
            .operands
            .pop()
            .ok_or_else(|| ForspError::EmptyStack.into())
    }

    fn pop_datum(
        &self,
        configuration: &mut StackConfigurationOf<R>,
    ) -> Result<R::Datum, RuntimeForspError<R::Error>> {
        match self
            .runtime
            .values()
            .unroll(&Self::pop(configuration)?)
            .map_err(|error| RuntimeForspError::Runtime(self.runtime.value_error(error)))?
        {
            StackValueLayer::Datum(datum) => Ok(datum),
            StackValueLayer::Closure(_) => Err(ForspError::ExpectedDatum.into()),
        }
    }

    fn pop_integer(
        &self,
        configuration: &mut StackConfigurationOf<R>,
    ) -> Result<Int, RuntimeForspError<R::Error>> {
        let datum = self.pop_datum(configuration)?;
        match self
            .runtime
            .data()
            .view(&datum)
            .map_err(|error| RuntimeForspError::Runtime(self.runtime.data_error(error)))?
        {
            SExprF::Atom(CoreAtom::Integer(integer)) => Ok(integer),
            _ => Err(ForspError::ExpectedInteger.into()),
        }
    }

    fn datum_value(&self, datum: R::Datum) -> Result<R::Value, RuntimeForspError<R::Error>> {
        self.runtime
            .values()
            .datum(datum)
            .map_err(|error| RuntimeForspError::Runtime(self.runtime.value_error(error)))
    }

    fn truth(&self, value: bool) -> Result<R::Value, RuntimeForspError<R::Error>> {
        let datum = if value {
            self.runtime
                .data()
                .atom(CoreAtom::symbol("t"))
                .map_err(|error| RuntimeForspError::Runtime(self.runtime.data_error(error)))?
        } else {
            self.runtime.data().nil()
        };
        self.datum_value(datum)
    }

    fn invoke(
        &self,
        configuration: &mut StackConfigurationOf<R>,
        closure: R::Closure,
    ) -> Result<(), RuntimeForspError<R::Error>> {
        let closure = self
            .runtime
            .closures()
            .open(&closure)
            .map_err(|error| RuntimeForspError::Runtime(self.runtime.closure_error(error)))?;
        configuration.continuations.push(StackContinuation {
            code: configuration.code.clone(),
            cursor: configuration.cursor,
            environment: configuration.environment.clone(),
        });
        configuration.code = closure.code;
        configuration.cursor = 0;
        configuration.environment = closure.environment;
        Ok(())
    }

    fn apply(
        &self,
        primitive: ForspPrimitive,
        configuration: &mut StackConfigurationOf<R>,
    ) -> Result<(), RuntimeForspError<R::Error>> {
        match primitive {
            ForspPrimitive::Eq => {
                let right = self.pop_datum(configuration)?;
                let left = self.pop_datum(configuration)?;
                let equal = self
                    .runtime
                    .data()
                    .equivalent(&left, &right)
                    .map_err(|error| RuntimeForspError::Runtime(self.runtime.data_error(error)))?;
                configuration.operands.push(self.truth(equal)?);
            }
            ForspPrimitive::Cons => {
                let head = self.pop_datum(configuration)?;
                let tail = self.pop_datum(configuration)?;
                let datum =
                    self.runtime.data().cons(head, tail).map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.data_error(error))
                    })?;
                configuration.operands.push(self.datum_value(datum)?);
            }
            ForspPrimitive::Car | ForspPrimitive::Cdr => {
                let value = self.pop_datum(configuration)?;
                let SExprF::Cons { head, tail } =
                    self.runtime.data().view(&value).map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.data_error(error))
                    })?
                else {
                    return Err(ForspError::ExpectedCons.into());
                };
                configuration.operands.push(self.datum_value(
                    if primitive == ForspPrimitive::Car {
                        head
                    } else {
                        tail
                    },
                )?);
            }
            ForspPrimitive::Cswap => {
                let condition = self.pop_datum(configuration)?;
                let false_value = matches!(
                    self.runtime.data().view(&condition).map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.data_error(error))
                    })?,
                    SExprF::Nil
                );
                if !false_value {
                    let right = Self::pop(configuration)?;
                    let left = Self::pop(configuration)?;
                    configuration.operands.push(right);
                    configuration.operands.push(left);
                }
            }
            ForspPrimitive::Add | ForspPrimitive::Subtract | ForspPrimitive::Multiply => {
                let right = self.pop_integer(configuration)?;
                let left = self.pop_integer(configuration)?;
                let result = match primitive {
                    ForspPrimitive::Add => left + right,
                    ForspPrimitive::Subtract => left - right,
                    ForspPrimitive::Multiply => left * right,
                    _ => unreachable!(),
                };
                let datum = self
                    .runtime
                    .data()
                    .atom(CoreAtom::Integer(result))
                    .map_err(|error| RuntimeForspError::Runtime(self.runtime.data_error(error)))?;
                configuration.operands.push(self.datum_value(datum)?);
            }
            ForspPrimitive::Stack => {
                let mut datums = Vec::with_capacity(configuration.operands.len());
                for value in configuration.operands.iter().rev() {
                    datums.push(
                        match self.runtime.values().view(value).map_err(|error| {
                            RuntimeForspError::Runtime(self.runtime.value_error(error))
                        })? {
                            StackValueView::Datum(datum) => datum,
                            StackValueView::Closure => self
                                .runtime
                                .data()
                                .atom(CoreAtom::symbol("<closure>"))
                                .map_err(|error| {
                                    RuntimeForspError::Runtime(self.runtime.data_error(error))
                                })?,
                        },
                    );
                }
                let stack =
                    self.runtime.data().list(datums).map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.data_error(error))
                    })?;
                configuration.operands.push(self.datum_value(stack)?);
            }
        }
        Ok(())
    }

    fn next_configuration(
        &self,
        configuration: &StackConfigurationOf<R>,
    ) -> Result<Option<StackConfigurationOf<R>>, RuntimeForspError<R::Error>> {
        let mut next = configuration.clone();
        let instructions = self
            .runtime
            .syntax()
            .instructions(&next.code)
            .map_err(|error| RuntimeForspError::Runtime(self.runtime.syntax_error(error)))?;
        if next.cursor == instructions.len() {
            let Some(caller) = next.continuations.pop() else {
                return Ok(None);
            };
            next.code = caller.code;
            next.cursor = caller.cursor;
            next.environment = caller.environment;
            return Ok(Some(next));
        }
        let instruction = instructions[next.cursor].clone();
        next.cursor += 1;
        match instruction {
            ForspInstruction::Literal(datum) | ForspInstruction::Quote(datum) => {
                next.operands.push(self.datum_value(datum)?);
            }
            ForspInstruction::Closure(code) => {
                let closure = self
                    .runtime
                    .closures()
                    .close(StackClosureRecord {
                        code,
                        environment: next.environment.clone(),
                    })
                    .map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.closure_error(error))
                    })?;
                let value = self
                    .runtime
                    .values()
                    .roll(StackValueLayer::Closure(closure))
                    .map_err(|error| RuntimeForspError::Runtime(self.runtime.value_error(error)))?;
                next.operands.push(value);
            }
            ForspInstruction::Bind(name) => {
                let value = Self::pop(&mut next)?;
                next.environment = self
                    .runtime
                    .environments()
                    .extend(&next.environment, vec![RuntimeBinding::new(name, value)])
                    .map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.environment_error(error))
                    })?;
            }
            ForspInstruction::PushBinding(name) => {
                let value = self
                    .runtime
                    .environments()
                    .lookup(&next.environment, &name)
                    .map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.environment_error(error))
                    })?
                    .ok_or_else(|| {
                        RuntimeForspError::Language(ForspError::Unbound(name.clone()))
                    })?;
                next.operands.push(value);
            }
            ForspInstruction::Resolve(name) => {
                let value = self
                    .runtime
                    .environments()
                    .lookup(&next.environment, &name)
                    .map_err(|error| {
                        RuntimeForspError::Runtime(self.runtime.environment_error(error))
                    })?
                    .ok_or_else(|| {
                        RuntimeForspError::Language(ForspError::Unbound(name.clone()))
                    })?;
                match self
                    .runtime
                    .values()
                    .unroll(&value)
                    .map_err(|error| RuntimeForspError::Runtime(self.runtime.value_error(error)))?
                {
                    StackValueLayer::Closure(closure) => self.invoke(&mut next, closure)?,
                    StackValueLayer::Datum(_) => next.operands.push(value),
                }
            }
            ForspInstruction::Primitive(primitive) => self.apply(primitive, &mut next)?,
            ForspInstruction::Effect(effect) => {
                return Err(ForspError::UnhandledEffect(effect).into());
            }
        }
        Ok(Some(next))
    }
}

impl<R> StepRelation for RuntimeForspMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    type Configuration = StackConfigurationOf<R>;
    type Error = RuntimeForspError<R::Error>;

    fn successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        Ok(self
            .next_configuration(configuration)?
            .into_iter()
            .collect())
    }
}

impl<R> DeterministicStep for RuntimeForspMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    fn next(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        self.next_configuration(configuration)
    }
}

/// Compatibility façade for the direct Forsp runtime.
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspMachine;

impl ForspMachine {
    pub fn initial(code: ForspCode) -> ForspConfiguration {
        RuntimeForspMachine::new(ForspRuntime::default()).initial(code)
    }

    fn pop(configuration: &mut ForspConfiguration) -> Result<ForspValue, ForspError> {
        configuration.operands.pop().ok_or(ForspError::EmptyStack)
    }
}

impl StepRelation for ForspMachine {
    type Configuration = ForspConfiguration;
    type Error = ForspError;

    fn successors(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        self.next(configuration)
            .map(|next| next.into_iter().collect())
    }
}

impl DeterministicStep for ForspMachine {
    fn next(
        &self,
        configuration: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        RuntimeForspMachine::new(ForspRuntime::default())
            .next(configuration)
            .map_err(|error| match error {
                RuntimeForspError::Language(error) => error,
                RuntimeForspError::Runtime(never) => match never {},
            })
    }
}

/// Forsp reduction with explicit effect suspension.
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspEffectMachine;

impl ForspEffectMachine {
    pub fn initial(code: ForspCode) -> ForspEffectState {
        EffectState::Running(ForspMachine::initial(code))
    }

    fn request(
        effect: ForspEffect,
        continuation: &mut ForspConfiguration,
    ) -> Result<ForspRequest, ForspError> {
        Ok(match effect {
            ForspEffect::Read => ForspRequest::Read,
            ForspEffect::Print => ForspRequest::Print(ForspMachine::pop(continuation)?),
            ForspEffect::PointerState => ForspRequest::PointerState,
            ForspEffect::PointerRead => ForspRequest::PointerRead(ForspMachine::pop(continuation)?),
            ForspEffect::PointerWrite => {
                let value = ForspMachine::pop(continuation)?;
                let address = ForspMachine::pop(continuation)?;
                ForspRequest::PointerWrite { address, value }
            }
            ForspEffect::PointerToObject => {
                ForspRequest::PointerToObject(ForspMachine::pop(continuation)?)
            }
            ForspEffect::PointerFromObject => {
                ForspRequest::PointerFromObject(ForspMachine::pop(continuation)?)
            }
        })
    }
}

impl DeterministicStep for ForspEffectMachine {
    fn next(&self, state: &ForspEffectState) -> Result<Option<ForspEffectState>, ForspError> {
        match state {
            EffectState::Suspended(_) | EffectState::Returned(_) => Ok(None),
            EffectState::Running(configuration) => {
                if let Some(ForspInstruction::Effect(effect)) =
                    configuration.code.get(configuration.cursor)
                {
                    let mut continuation = configuration.clone();
                    continuation.cursor += 1;
                    let request = Self::request(*effect, &mut continuation)?;
                    return Ok(Some(EffectState::Suspended(EffectSuspension {
                        continuation,
                        request,
                    })));
                }
                Ok(Some(match ForspMachine.next(configuration)? {
                    Some(next) => EffectState::Running(next),
                    None => EffectState::Returned(configuration.clone()),
                }))
            }
        }
    }
}

impl StepRelation for ForspEffectMachine {
    type Configuration = ForspEffectState;
    type Error = ForspError;

    fn successors(&self, state: &ForspEffectState) -> Result<Vec<ForspEffectState>, ForspError> {
        Ok(self.next(state)?.into_iter().collect())
    }
}

impl TerminalValue for ForspEffectMachine {
    type Value = ForspConfiguration;

    fn terminal_value(&self, state: &ForspEffectState) -> Option<Self::Value> {
        match state {
            EffectState::Returned(configuration) => Some(configuration.clone()),
            EffectState::Running(_) | EffectState::Suspended(_) => None,
        }
    }
}

impl EffectResume for ForspEffectMachine {
    type Configuration = ForspConfiguration;
    type Request = ForspRequest;
    type Response = ForspResponse;
    type Error = ForspError;

    fn resume(
        &self,
        suspension: EffectSuspension<ForspConfiguration, ForspRequest>,
        response: ForspResponse,
    ) -> Result<ForspConfiguration, ForspError> {
        let mut continuation = suspension.continuation;
        match (suspension.request, response) {
            (ForspRequest::Read, ForspResponse::Value(value))
            | (ForspRequest::PointerState, ForspResponse::Value(value))
            | (ForspRequest::PointerRead(_), ForspResponse::Value(value))
            | (ForspRequest::PointerToObject(_), ForspResponse::Value(value))
            | (ForspRequest::PointerFromObject(_), ForspResponse::Value(value)) => {
                continuation.operands.push(value);
            }
            (ForspRequest::Print(_), ForspResponse::Unit)
            | (ForspRequest::PointerWrite { .. }, ForspResponse::Unit) => {}
            _ => return Err(ForspError::InvalidEffectResponse),
        }
        Ok(continuation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_kernel_lisp::{execute, handle_to_completion};

    fn program(source: &str) -> ForspCode {
        let form = read(source).unwrap().pop().unwrap();
        ForspFrontend.lower(&form).unwrap()
    }

    fn run(source: &str) -> ForspConfiguration {
        let machine = RuntimeForspMachine::new(ForspRuntime::default());
        let trace = execute(&machine, machine.initial(program(source)), 128).unwrap();
        trace.end().clone()
    }

    #[test]
    fn bind_push_and_arithmetic_follow_forsp_stack_order() {
        let result = run("(5 $x ^x ^x *)");
        assert_eq!(
            result.operands,
            vec![ForspValue::Datum(Datum::Atom(CoreAtom::Integer(
                Int::from(25)
            )))]
        );
    }

    #[test]
    fn list_forms_are_lexical_closures_and_bare_names_call() {
        let result = run("(($x ^x ^x *) $square 6 square)");
        assert_eq!(
            result.operands,
            vec![ForspValue::Datum(Datum::Atom(CoreAtom::Integer(
                Int::from(36)
            )))]
        );
    }

    #[test]
    fn verbose_quote_reuses_inductive_lisp_data() {
        let result = run("(quote (1 2 3) car)");
        assert_eq!(
            result.operands,
            vec![ForspValue::Datum(Datum::Atom(CoreAtom::Integer(
                Int::from(1)
            )))]
        );
    }

    #[test]
    fn reference_quote_sugar_and_comments_are_accepted() {
        let result = run("(
               ; reference Forsp syntax
               '(1 2 3) car
             )");
        assert_eq!(
            result.operands,
            vec![ForspValue::Datum(Datum::Atom(CoreAtom::Integer(
                Int::from(1)
            )))]
        );
    }

    #[derive(Default)]
    struct RecordingIo {
        input: Vec<ForspValue>,
        printed: Vec<ForspValue>,
    }

    impl ForspIo for RecordingIo {
        type Error = &'static str;

        fn read(&mut self) -> Result<ForspValue, Self::Error> {
            if self.input.is_empty() {
                Err("end of input")
            } else {
                Ok(self.input.remove(0))
            }
        }

        fn print(&mut self, value: &ForspValue) -> Result<(), Self::Error> {
            self.printed.push(value.clone());
            Ok(())
        }
    }

    #[test]
    fn pure_machine_rejects_effects_instead_of_performing_host_io() {
        let error =
            execute(&ForspMachine, ForspMachine::initial(program("(read)")), 4).unwrap_err();
        assert!(matches!(
            error,
            covalence_kernel_lisp::ExecutionError::Relation(ForspError::UnhandledEffect(
                ForspEffect::Read
            ))
        ));
    }

    #[test]
    fn safe_io_suspends_resumes_and_retains_a_transcript() {
        let machine = ForspEffectMachine;
        let mut handler = ForspIoHandler {
            host: RecordingIo {
                input: vec![ForspValue::Datum(Datum::Atom(CoreAtom::Integer(
                    Int::from(41),
                )))],
                printed: Vec::new(),
            },
        };
        let run = handle_to_completion(
            &machine,
            ForspEffectMachine::initial(program("(read 1 + print)")),
            &mut handler,
            32,
        )
        .unwrap();

        assert!(run.returned.operands.is_empty());
        assert_eq!(run.transcript.len(), 2);
        assert!(matches!(run.transcript[0].request, ForspRequest::Read));
        assert!(matches!(run.transcript[1].request, ForspRequest::Print(_)));
        assert_eq!(
            handler.host.printed,
            vec![ForspValue::Datum(Datum::Atom(CoreAtom::Integer(
                Int::from(42)
            )))]
        );
    }

    #[test]
    fn safe_handler_refuses_low_level_pointer_requests() {
        let mut handler = ForspIoHandler {
            host: RecordingIo::default(),
        };
        assert!(matches!(
            handler.handle(&ForspRequest::PointerState),
            Err(ForspIoHandlerError::UnsafeRequest)
        ));
    }
}

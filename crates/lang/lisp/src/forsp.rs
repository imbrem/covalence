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
    HostEnvironment, HostEnvironments, LispEnvironment, LispIoRequest, LispIoResponse,
    StackClosure, StackClosureRecord, StackConfiguration, StackEffectMachine,
    StackEffectMachineError, StackEffectSemantics, StackInstructionLayer, StackInstructionSyntax,
    StackInstructionView, StackMachine, StackMachineError, StackMachineValue,
    StackPrimitiveSemantics, StackProgramSyntax, StackRuntime, StackValue, StackValueLayer,
    StackValueView, StepRelation, TerminalValue,
};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use crate::frontend::CoreAtom;

pub use covalence_kernel_lisp::LispIo as ForspIo;

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

pub enum ForspHandleValueKind {}
pub enum ForspHandleClosureKind {}

pub type ForspHandleValue = covalence_kernel_lisp::Resource<ForspHandleValueKind>;
pub type ForspHandleClosure = covalence_kernel_lisp::Resource<ForspHandleClosureKind>;
pub type ForspHandleError = covalence_kernel_lisp::ResourceError;

pub type ForspHandleEnvironment = HostEnvironment<String, ForspHandleValue>;

#[derive(Clone, Debug)]
pub struct ForspHandleValues {
    values: covalence_kernel_lisp::ResourceTable<
        ForspHandleValueKind,
        StackValueLayer<Datum<CoreAtom>, ForspHandleClosure>,
    >,
    closures: covalence_kernel_lisp::ResourceTable<
        ForspHandleClosureKind,
        StackClosureRecord<ForspCode, ForspHandleEnvironment>,
    >,
}

impl ForspHandleValues {
    fn layer(
        &self,
        value: &ForspHandleValue,
    ) -> Result<StackValueLayer<Datum<CoreAtom>, ForspHandleClosure>, ForspHandleError> {
        self.values.get_cloned(*value)
    }

    fn allocate(
        &self,
        layer: StackValueLayer<Datum<CoreAtom>, ForspHandleClosure>,
    ) -> ForspHandleValue {
        self.values.insert(layer)
    }
}

impl StackValue for ForspHandleValues {
    type Datum = Datum<CoreAtom>;
    type Value = ForspHandleValue;
    type Error = ForspHandleError;

    fn datum(&self, datum: Self::Datum) -> Result<Self::Value, Self::Error> {
        Ok(self.allocate(StackValueLayer::Datum(datum)))
    }

    fn view(&self, value: &Self::Value) -> Result<StackValueView<Self::Datum>, Self::Error> {
        Ok(match self.layer(value)? {
            StackValueLayer::Datum(datum) => StackValueView::Datum(datum),
            StackValueLayer::Closure(_) => StackValueView::Closure,
        })
    }

    fn equivalent(&self, left: &Self::Value, right: &Self::Value) -> Result<bool, Self::Error> {
        if left == right {
            return Ok(true);
        }
        Ok(match (self.layer(left)?, self.layer(right)?) {
            (StackValueLayer::Datum(left), StackValueLayer::Datum(right)) => left == right,
            (StackValueLayer::Closure(left), StackValueLayer::Closure(right)) => left == right,
            _ => false,
        })
    }
}

impl StackMachineValue for ForspHandleValues {
    type Closure = ForspHandleClosure;

    fn roll(
        &self,
        layer: StackValueLayer<Self::Datum, Self::Closure>,
    ) -> Result<Self::Value, Self::Error> {
        if let StackValueLayer::Closure(closure) = layer {
            self.closures.contains(closure)?;
            Ok(self.allocate(StackValueLayer::Closure(closure)))
        } else {
            Ok(self.allocate(layer))
        }
    }

    fn unroll(
        &self,
        value: &Self::Value,
    ) -> Result<StackValueLayer<Self::Datum, Self::Closure>, Self::Error> {
        self.layer(value)
    }
}

#[derive(Clone, Debug)]
pub struct ForspHandleClosures {
    closures: covalence_kernel_lisp::ResourceTable<
        ForspHandleClosureKind,
        StackClosureRecord<ForspCode, ForspHandleEnvironment>,
    >,
}

impl StackClosure for ForspHandleClosures {
    type Code = ForspCode;
    type Environment = ForspHandleEnvironment;
    type Closure = ForspHandleClosure;
    type Error = ForspHandleError;

    fn close(
        &self,
        record: StackClosureRecord<Self::Code, Self::Environment>,
    ) -> Result<Self::Closure, Self::Error> {
        Ok(self.closures.insert(record))
    }

    fn open(
        &self,
        closure: &Self::Closure,
    ) -> Result<StackClosureRecord<Self::Code, Self::Environment>, Self::Error> {
        self.closures.get_cloned(*closure)
    }
}

/// Opaque value/closure backend for the same Forsp machine.
#[derive(Clone, Debug)]
pub struct ForspHandleRuntime {
    data: Free<CoreAtom>,
    syntax: ForspSyntax,
    values: ForspHandleValues,
    closures: ForspHandleClosures,
    environments: HostEnvironments<String, ForspHandleValue>,
}

impl Default for ForspHandleRuntime {
    fn default() -> Self {
        let arena = covalence_kernel_lisp::ResourceArena::new();
        let values = arena.table("Forsp value");
        let closures = arena.table("Forsp closure");
        Self {
            data: Free::new(),
            syntax: ForspSyntax,
            values: ForspHandleValues {
                values,
                closures: closures.clone(),
            },
            closures: ForspHandleClosures { closures },
            environments: HostEnvironments::default(),
        }
    }
}

impl StackRuntime for ForspHandleRuntime {
    type Symbol = String;
    type Atom = CoreAtom;
    type Datum = Datum<CoreAtom>;
    type Primitive = ForspPrimitive;
    type Instruction = ForspInstruction;
    type Code = ForspCode;
    type Value = ForspHandleValue;
    type Closure = ForspHandleClosure;
    type Environment = ForspHandleEnvironment;
    type Error = ForspHandleError;
    type Data = Free<CoreAtom>;
    type Syntax = ForspSyntax;
    type Values = ForspHandleValues;
    type Closures = ForspHandleClosures;
    type Environments = HostEnvironments<String, ForspHandleValue>;

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

    fn value_error(&self, error: ForspHandleError) -> Self::Error {
        error
    }

    fn closure_error(&self, error: ForspHandleError) -> Self::Error {
        error
    }

    fn environment_error(&self, error: Infallible) -> Self::Error {
        match error {}
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeForspRequest<V> {
    Io(LispIoRequest<V>),
    PointerState,
    PointerRead(V),
    PointerWrite { address: V, value: V },
    PointerToObject(V),
    PointerFromObject(V),
}

pub type ForspRequest = RuntimeForspRequest<ForspValue>;
pub type RuntimeForspResponse<V> = LispIoResponse<V>;
pub type ForspResponse = LispIoResponse<ForspValue>;
pub type ForspEffectState = EffectState<ForspConfiguration, ForspRequest>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForspIoHandlerError<E> {
    Io(E),
    UnsafeRequest,
}

/// Proof-free adapter from safe Forsp requests to a host I/O capability.
pub struct ForspIoHandler<H> {
    pub host: H,
}

impl<H, V> EffectHandler<RuntimeForspRequest<V>, RuntimeForspResponse<V>> for ForspIoHandler<H>
where
    H: ForspIo<V>,
{
    type Error = ForspIoHandlerError<H::Error>;

    fn handle(
        &mut self,
        request: &RuntimeForspRequest<V>,
    ) -> Result<RuntimeForspResponse<V>, Self::Error> {
        match request {
            RuntimeForspRequest::Io(LispIoRequest::Read) => self
                .host
                .read()
                .map(LispIoResponse::Value)
                .map_err(ForspIoHandlerError::Io),
            RuntimeForspRequest::Io(LispIoRequest::Write(value)) => self
                .host
                .write(value)
                .map(|()| LispIoResponse::Unit)
                .map_err(ForspIoHandlerError::Io),
            RuntimeForspRequest::PointerState
            | RuntimeForspRequest::PointerRead(_)
            | RuntimeForspRequest::PointerWrite { .. }
            | RuntimeForspRequest::PointerToObject(_)
            | RuntimeForspRequest::PointerFromObject(_) => Err(ForspIoHandlerError::UnsafeRequest),
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
    InvalidCursor { cursor: usize, length: usize },
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
            Self::InvalidCursor { cursor, length } => {
                write!(
                    f,
                    "Forsp instruction cursor {cursor} exceeds program length {length}"
                )
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

impl StackInstructionView for ForspSyntax {
    type Effect = ForspEffect;

    fn view_instruction(
        &self,
        instruction: &Self::Instruction,
    ) -> Result<
        StackInstructionLayer<Self::Symbol, Self::Datum, Self::Primitive, Self::Code, Self::Effect>,
        Self::Error,
    > {
        Ok(match instruction {
            ForspInstruction::Literal(datum) => StackInstructionLayer::Literal(datum.clone()),
            ForspInstruction::Quote(datum) => StackInstructionLayer::Quote(datum.clone()),
            ForspInstruction::Closure(code) => StackInstructionLayer::Closure(code.clone()),
            ForspInstruction::Bind(symbol) => StackInstructionLayer::Bind(symbol.clone()),
            ForspInstruction::PushBinding(symbol) => {
                StackInstructionLayer::PushBinding(symbol.clone())
            }
            ForspInstruction::Resolve(symbol) => StackInstructionLayer::Resolve(symbol.clone()),
            ForspInstruction::Primitive(primitive) => StackInstructionLayer::Primitive(*primitive),
            ForspInstruction::Effect(effect) => StackInstructionLayer::Effect(*effect),
        })
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

pub type StackConfigurationOf<R> = StackConfiguration<
    <R as StackRuntime>::Code,
    <R as StackRuntime>::Value,
    <R as StackRuntime>::Environment,
>;

/// A checked pure Forsp execution over a selected stack runtime.
///
/// The terminal configuration is retained as both the trace endpoint and the
/// result because a concatenative program returns an operand stack rather than
/// one distinguished value. Direct and resource-handle backends therefore
/// expose the same evidence shape.
pub type ForspEvaluation<R> =
    covalence_kernel_lisp::MayEval<StackConfigurationOf<R>, StackConfigurationOf<R>>;

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

fn forsp_stack_error<E>(
    error: StackMachineError<String, ForspEffect, RuntimeForspError<E>, E>,
) -> RuntimeForspError<E> {
    match error {
        StackMachineError::EmptyStack => RuntimeForspError::Language(ForspError::EmptyStack),
        StackMachineError::Unbound(symbol) => {
            RuntimeForspError::Language(ForspError::Unbound(symbol))
        }
        StackMachineError::UnhandledEffect(effect) => {
            RuntimeForspError::Language(ForspError::UnhandledEffect(effect))
        }
        StackMachineError::InvalidCursor { cursor, length } => {
            RuntimeForspError::Language(ForspError::InvalidCursor { cursor, length })
        }
        StackMachineError::Primitive(error) => error,
        StackMachineError::Runtime(error) => RuntimeForspError::Runtime(error),
    }
}

/// Forsp's language-specific primitive dictionary.
///
/// The generic [`StackMachine`] owns closure invocation, binding, name
/// resolution, and continuation behavior. This dictionary owns only the
/// meanings of Forsp's data and arithmetic words.
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspPrimitives;

impl ForspPrimitives {
    fn pop<R: StackRuntime>(
        operands: &mut Vec<R::Value>,
    ) -> Result<R::Value, RuntimeForspError<R::Error>> {
        operands.pop().ok_or_else(|| ForspError::EmptyStack.into())
    }

    fn pop_datum<R>(
        runtime: &R,
        operands: &mut Vec<R::Value>,
    ) -> Result<R::Datum, RuntimeForspError<R::Error>>
    where
        R: StackRuntime,
    {
        match runtime
            .values()
            .unroll(&Self::pop::<R>(operands)?)
            .map_err(|error| RuntimeForspError::Runtime(runtime.value_error(error)))?
        {
            StackValueLayer::Datum(datum) => Ok(datum),
            StackValueLayer::Closure(_) => Err(ForspError::ExpectedDatum.into()),
        }
    }

    fn datum_value<R>(runtime: &R, datum: R::Datum) -> Result<R::Value, RuntimeForspError<R::Error>>
    where
        R: StackRuntime,
    {
        runtime
            .values()
            .datum(datum)
            .map_err(|error| RuntimeForspError::Runtime(runtime.value_error(error)))
    }

    fn truth<R>(runtime: &R, value: bool) -> Result<R::Value, RuntimeForspError<R::Error>>
    where
        R: StackRuntime<Atom = CoreAtom>,
    {
        let datum = if value {
            runtime
                .data()
                .atom(CoreAtom::symbol("t"))
                .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?
        } else {
            runtime.data().nil()
        };
        Self::datum_value(runtime, datum)
    }
}

impl<R> StackPrimitiveSemantics<R> for ForspPrimitives
where
    R: StackRuntime<Atom = CoreAtom, Datum = Datum<CoreAtom>, Primitive = ForspPrimitive>,
{
    type Error = RuntimeForspError<R::Error>;

    fn apply(
        &self,
        runtime: &R,
        primitive: &ForspPrimitive,
        mut operands: Vec<R::Value>,
    ) -> Result<Vec<R::Value>, Self::Error> {
        match primitive {
            ForspPrimitive::Eq => {
                let right = Self::pop_datum(runtime, &mut operands)?;
                let left = Self::pop_datum(runtime, &mut operands)?;
                let equal = runtime
                    .data()
                    .equivalent(&left, &right)
                    .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?;
                operands.push(Self::truth(runtime, equal)?);
            }
            ForspPrimitive::Cons => {
                let head = Self::pop_datum(runtime, &mut operands)?;
                let tail = Self::pop_datum(runtime, &mut operands)?;
                let datum = runtime
                    .data()
                    .cons(head, tail)
                    .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?;
                operands.push(Self::datum_value(runtime, datum)?);
            }
            ForspPrimitive::Car | ForspPrimitive::Cdr => {
                let value = Self::pop_datum(runtime, &mut operands)?;
                let SExprF::Cons { head, tail } = runtime
                    .data()
                    .view(&value)
                    .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?
                else {
                    return Err(ForspError::ExpectedCons.into());
                };
                operands.push(Self::datum_value(
                    runtime,
                    if *primitive == ForspPrimitive::Car {
                        head
                    } else {
                        tail
                    },
                )?);
            }
            ForspPrimitive::Cswap => {
                let condition = Self::pop_datum(runtime, &mut operands)?;
                let false_value = matches!(
                    runtime
                        .data()
                        .view(&condition)
                        .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?,
                    SExprF::Nil
                );
                if !false_value {
                    let right = Self::pop::<R>(&mut operands)?;
                    let left = Self::pop::<R>(&mut operands)?;
                    operands.push(right);
                    operands.push(left);
                }
            }
            ForspPrimitive::Add | ForspPrimitive::Subtract | ForspPrimitive::Multiply => {
                let pop_integer =
                    |operands: &mut Vec<R::Value>| -> Result<Int, RuntimeForspError<R::Error>> {
                        let datum = Self::pop_datum(runtime, operands)?;
                        match runtime.data().view(&datum).map_err(|error| {
                            RuntimeForspError::Runtime(runtime.data_error(error))
                        })? {
                            SExprF::Atom(CoreAtom::Integer(integer)) => Ok(integer),
                            _ => Err(ForspError::ExpectedInteger.into()),
                        }
                    };
                let right = pop_integer(&mut operands)?;
                let left = pop_integer(&mut operands)?;
                let result = match primitive {
                    ForspPrimitive::Add => left + right,
                    ForspPrimitive::Subtract => left - right,
                    ForspPrimitive::Multiply => left * right,
                    _ => unreachable!(),
                };
                let datum = runtime
                    .data()
                    .atom(CoreAtom::Integer(result))
                    .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?;
                operands.push(Self::datum_value(runtime, datum)?);
            }
            ForspPrimitive::Stack => {
                let mut datums = Vec::with_capacity(operands.len());
                for value in operands.iter().rev() {
                    datums.push(
                        match runtime.values().view(value).map_err(|error| {
                            RuntimeForspError::Runtime(runtime.value_error(error))
                        })? {
                            StackValueView::Datum(datum) => datum,
                            StackValueView::Closure => {
                                runtime.data().atom(CoreAtom::symbol("<closure>")).map_err(
                                    |error| RuntimeForspError::Runtime(runtime.data_error(error)),
                                )?
                            }
                        },
                    );
                }
                let stack = runtime
                    .data()
                    .list(datums)
                    .map_err(|error| RuntimeForspError::Runtime(runtime.data_error(error)))?;
                operands.push(Self::datum_value(runtime, stack)?);
            }
        }
        Ok(operands)
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
            Syntax = ForspSyntax,
        >,
{
    pub fn initial(&self, code: R::Code) -> StackConfigurationOf<R> {
        StackConfiguration::new(code, self.runtime.environments().empty())
    }

    fn next_configuration(
        &self,
        configuration: &StackConfigurationOf<R>,
    ) -> Result<Option<StackConfigurationOf<R>>, RuntimeForspError<R::Error>> {
        StackMachine::new(&self.runtime, ForspPrimitives)
            .next_configuration(configuration)
            .map_err(forsp_stack_error)
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
            Syntax = ForspSyntax,
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
            Syntax = ForspSyntax,
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

impl<R> TerminalValue for RuntimeForspMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
            Syntax = ForspSyntax,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    type Value = StackConfigurationOf<R>;

    fn terminal_value(&self, configuration: &Self::Configuration) -> Option<Self::Value> {
        (configuration.continuations.is_empty() && configuration.cursor == configuration.code.len())
            .then(|| configuration.clone())
    }
}

/// Compatibility façade for the direct Forsp runtime.
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspMachine;

impl ForspMachine {
    pub fn initial(code: ForspCode) -> ForspConfiguration {
        RuntimeForspMachine::new(ForspRuntime::default()).initial(code)
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

impl TerminalValue for ForspMachine {
    type Value = ForspConfiguration;

    fn terminal_value(&self, configuration: &Self::Configuration) -> Option<Self::Value> {
        (configuration.continuations.is_empty() && configuration.cursor == configuration.code.len())
            .then(|| configuration.clone())
    }
}

/// Forsp's policy for converting effect words into requests and responses.
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspEffects;

impl<R> StackEffectSemantics<R> for ForspEffects
where
    R: StackRuntime<Primitive = ForspPrimitive>,
    R::Syntax: StackInstructionView<Effect = ForspEffect>,
{
    type Request = RuntimeForspRequest<R::Value>;
    type Response = RuntimeForspResponse<R::Value>;
    type Error = RuntimeForspError<R::Error>;

    fn suspend(
        &self,
        _runtime: &R,
        effect: &ForspEffect,
        mut operands: Vec<R::Value>,
    ) -> Result<(Vec<R::Value>, Self::Request), Self::Error> {
        let mut pop = || {
            operands
                .pop()
                .ok_or(RuntimeForspError::Language(ForspError::EmptyStack))
        };
        let request = match effect {
            ForspEffect::Read => RuntimeForspRequest::Io(LispIoRequest::Read),
            ForspEffect::Print => RuntimeForspRequest::Io(LispIoRequest::Write(pop()?)),
            ForspEffect::PointerState => RuntimeForspRequest::PointerState,
            ForspEffect::PointerRead => RuntimeForspRequest::PointerRead(pop()?),
            ForspEffect::PointerWrite => {
                let value = pop()?;
                let address = pop()?;
                RuntimeForspRequest::PointerWrite { address, value }
            }
            ForspEffect::PointerToObject => RuntimeForspRequest::PointerToObject(pop()?),
            ForspEffect::PointerFromObject => RuntimeForspRequest::PointerFromObject(pop()?),
        };
        Ok((operands, request))
    }

    fn resume(
        &self,
        _runtime: &R,
        request: &Self::Request,
        response: Self::Response,
        mut operands: Vec<R::Value>,
    ) -> Result<Vec<R::Value>, Self::Error> {
        match (request, response) {
            (RuntimeForspRequest::Io(LispIoRequest::Read), LispIoResponse::Value(value))
            | (RuntimeForspRequest::PointerState, LispIoResponse::Value(value))
            | (RuntimeForspRequest::PointerRead(_), LispIoResponse::Value(value))
            | (RuntimeForspRequest::PointerToObject(_), LispIoResponse::Value(value))
            | (RuntimeForspRequest::PointerFromObject(_), LispIoResponse::Value(value)) => {
                operands.push(value);
            }
            (RuntimeForspRequest::Io(LispIoRequest::Write(_)), LispIoResponse::Unit)
            | (RuntimeForspRequest::PointerWrite { .. }, LispIoResponse::Unit) => {}
            _ => return Err(ForspError::InvalidEffectResponse.into()),
        }
        Ok(operands)
    }
}

fn forsp_effect_error<E>(
    error: StackEffectMachineError<
        StackMachineError<String, ForspEffect, RuntimeForspError<E>, E>,
        RuntimeForspError<E>,
    >,
) -> RuntimeForspError<E> {
    match error {
        StackEffectMachineError::Stack(error) => forsp_stack_error(error),
        StackEffectMachineError::Effect(error) => error,
    }
}

pub type RuntimeForspEffectState<R> = covalence_kernel_lisp::StackEffectState<R, ForspEffects>;

/// Forsp effect suspension over a selected stack runtime.
#[derive(Clone, Debug)]
pub struct RuntimeForspEffectMachine<R> {
    runtime: R,
}

impl<R> RuntimeForspEffectMachine<R> {
    pub fn new(runtime: R) -> Self {
        Self { runtime }
    }

    pub fn runtime(&self) -> &R {
        &self.runtime
    }
}

impl<R> RuntimeForspEffectMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
            Syntax = ForspSyntax,
        >,
{
    pub fn initial(&self, code: R::Code) -> RuntimeForspEffectState<R> {
        StackEffectMachine::new(&self.runtime, ForspPrimitives, ForspEffects).initial(code)
    }

    fn next_effect(
        &self,
        state: &RuntimeForspEffectState<R>,
    ) -> Result<Option<RuntimeForspEffectState<R>>, RuntimeForspError<R::Error>> {
        StackEffectMachine::new(&self.runtime, ForspPrimitives, ForspEffects)
            .next_effect(state)
            .map_err(forsp_effect_error)
    }
}

impl<R> StepRelation for RuntimeForspEffectMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
            Syntax = ForspSyntax,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    type Configuration = RuntimeForspEffectState<R>;
    type Error = RuntimeForspError<R::Error>;

    fn successors(
        &self,
        state: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        Ok(self.next_effect(state)?.into_iter().collect())
    }
}

impl<R> DeterministicStep for RuntimeForspEffectMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
            Syntax = ForspSyntax,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    fn next(
        &self,
        state: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        self.next_effect(state)
    }
}

impl<R> TerminalValue for RuntimeForspEffectMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
            Syntax = ForspSyntax,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    type Value = StackConfigurationOf<R>;

    fn terminal_value(&self, state: &Self::Configuration) -> Option<Self::Value> {
        match state {
            EffectState::Returned(configuration) => Some(configuration.clone()),
            EffectState::Running(_) | EffectState::Suspended(_) => None,
        }
    }
}

impl<R> EffectResume for RuntimeForspEffectMachine<R>
where
    R: StackRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = ForspPrimitive,
            Instruction = ForspInstruction,
            Code = ForspCode,
            Syntax = ForspSyntax,
        >,
    R::Code: Debug + PartialEq,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    type Configuration = StackConfigurationOf<R>;
    type Request = RuntimeForspRequest<R::Value>;
    type Response = RuntimeForspResponse<R::Value>;
    type Error = RuntimeForspError<R::Error>;

    fn resume(
        &self,
        suspension: EffectSuspension<Self::Configuration, Self::Request>,
        response: Self::Response,
    ) -> Result<Self::Configuration, Self::Error> {
        StackEffectMachine::new(&self.runtime, ForspPrimitives, ForspEffects)
            .resume(suspension, response)
            .map_err(forsp_effect_error)
    }
}

/// Compatibility façade for direct-runtime Forsp effects.
#[derive(Clone, Copy, Debug, Default)]
pub struct ForspEffectMachine;

impl ForspEffectMachine {
    pub fn initial(code: ForspCode) -> ForspEffectState {
        RuntimeForspEffectMachine::new(ForspRuntime::default()).initial(code)
    }
}

fn direct_effect_error(error: RuntimeForspError<Infallible>) -> ForspError {
    match error {
        RuntimeForspError::Language(error) => error,
        RuntimeForspError::Runtime(never) => match never {},
    }
}

impl StepRelation for ForspEffectMachine {
    type Configuration = ForspEffectState;
    type Error = ForspError;

    fn successors(
        &self,
        state: &Self::Configuration,
    ) -> Result<Vec<Self::Configuration>, Self::Error> {
        self.next(state).map(|next| next.into_iter().collect())
    }
}

impl DeterministicStep for ForspEffectMachine {
    fn next(
        &self,
        state: &Self::Configuration,
    ) -> Result<Option<Self::Configuration>, Self::Error> {
        RuntimeForspEffectMachine::new(ForspRuntime::default())
            .next(state)
            .map_err(direct_effect_error)
    }
}

impl TerminalValue for ForspEffectMachine {
    type Value = ForspConfiguration;

    fn terminal_value(&self, state: &Self::Configuration) -> Option<Self::Value> {
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
        suspension: EffectSuspension<Self::Configuration, Self::Request>,
        response: Self::Response,
    ) -> Result<Self::Configuration, Self::Error> {
        RuntimeForspEffectMachine::new(ForspRuntime::default())
            .resume(suspension, response)
            .map_err(direct_effect_error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_kernel_lisp::{Evaluation, evaluate, execute, handle_to_completion};

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
    fn pure_execution_retains_may_eval_evidence_across_runtime_backends() {
        let code = program("(($x ^x ^x *) $square 7 square)");

        let direct = RuntimeForspMachine::new(ForspRuntime::default());
        let Evaluation::Value(direct_evaluation) =
            evaluate(&direct, direct.initial(code.clone()), 64).unwrap()
        else {
            panic!("direct Forsp execution must return a stack")
        };

        let handles = RuntimeForspMachine::new(ForspHandleRuntime::default());
        let Evaluation::Value(handle_evaluation) =
            evaluate(&handles, handles.initial(code), 64).unwrap()
        else {
            panic!("handle Forsp execution must return a stack")
        };

        assert!(direct_evaluation.trace.steps() > 0);
        assert!(handle_evaluation.trace.steps() > 0);
        assert_eq!(direct_evaluation.value.operands.len(), 1);
        assert_eq!(handle_evaluation.value.operands.len(), 1);
        assert_eq!(
            direct
                .runtime()
                .values()
                .view(&direct_evaluation.value.operands[0]),
            Ok(StackValueView::Datum(Datum::Atom(CoreAtom::Integer(
                Int::from(49)
            ))))
        );
        assert_eq!(
            handles
                .runtime()
                .values()
                .view(&handle_evaluation.value.operands[0])
                .unwrap(),
            StackValueView::Datum(Datum::Atom(CoreAtom::Integer(Int::from(49))))
        );
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

    struct RecordingIo<V = ForspValue> {
        input: Vec<V>,
        printed: Vec<V>,
    }

    impl<V> Default for RecordingIo<V> {
        fn default() -> Self {
            Self {
                input: Vec::new(),
                printed: Vec::new(),
            }
        }
    }

    impl<V: Clone> ForspIo<V> for RecordingIo<V> {
        type Error = &'static str;

        fn read(&mut self) -> Result<V, Self::Error> {
            if self.input.is_empty() {
                Err("end of input")
            } else {
                Ok(self.input.remove(0))
            }
        }

        fn write(&mut self, value: &V) -> Result<(), Self::Error> {
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
    fn forged_instruction_cursors_fail_without_panicking() {
        let pure = RuntimeForspMachine::new(ForspRuntime::default());
        let mut pure_state = pure.initial(program("(1)"));
        pure_state.cursor = 2;
        assert_eq!(
            pure.next(&pure_state),
            Err(RuntimeForspError::Language(ForspError::InvalidCursor {
                cursor: 2,
                length: 1,
            }))
        );

        let effects = RuntimeForspEffectMachine::new(ForspHandleRuntime::default());
        let EffectState::Running(mut effect_state) = effects.initial(program("(read)")) else {
            panic!("initial effect state must be running")
        };
        effect_state.cursor = 2;
        assert!(matches!(
            effects.next(&EffectState::Running(effect_state)),
            Err(RuntimeForspError::Language(ForspError::InvalidCursor {
                cursor: 2,
                length: 1,
            }))
        ));
    }

    #[test]
    fn safe_io_suspends_resumes_and_retains_a_transcript() {
        let machine = RuntimeForspEffectMachine::new(ForspRuntime::default());
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
            machine.initial(program("(read 1 + print)")),
            &mut handler,
            32,
        )
        .unwrap();

        assert!(run.returned.operands.is_empty());
        assert_eq!(run.transcript.len(), 2);
        assert!(matches!(
            run.transcript[0].request,
            ForspRequest::Io(LispIoRequest::Read)
        ));
        assert!(matches!(
            run.transcript[1].request,
            ForspRequest::Io(LispIoRequest::Write(_))
        ));
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

    #[test]
    fn closures_and_effects_run_on_the_handle_backend() {
        let machine = RuntimeForspEffectMachine::new(ForspHandleRuntime::default());
        let input = machine
            .runtime()
            .values()
            .datum(Datum::Atom(CoreAtom::Integer(Int::from(6))))
            .unwrap();
        let mut handler = ForspIoHandler {
            host: RecordingIo {
                input: vec![input],
                printed: Vec::new(),
            },
        };
        let run = handle_to_completion(
            &machine,
            machine.initial(program("(($x ^x ^x *) $square read square print)")),
            &mut handler,
            64,
        )
        .unwrap();

        assert!(run.returned.operands.is_empty());
        assert_eq!(run.transcript.len(), 2);
        let printed = handler.host.printed.first().expect("printed value");
        assert_eq!(
            machine.runtime().values().view(printed).unwrap(),
            StackValueView::Datum(Datum::Atom(CoreAtom::Integer(Int::from(36))))
        );
    }
}

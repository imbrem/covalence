//! Shared surface lowering and proof-free execution for Lisp frontends.
//!
//! Parsing remains outside the kernel API. This module translates the common
//! parsed S-expression tree into [`covalence_kernel_lisp::CoreExpr`], using an
//! explicit dialect policy for names, primitives, special forms, and numeric
//! literals. Sector, Scheme, and ACL2's expression fragment therefore share
//! the same core syntax without sharing ACL2 admission or Scheme-specific
//! surface extensions.

use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use std::str::FromStr;

use covalence_kernel_lisp::{
    ArenaRuntime, CoreExpr, CoreMachine, CoreMachineError, CorePrimitive, Datum,
    Definition as LispDefinition, ExecutionError, HostConfiguration, HostEnvironment, HostValue,
    LispEnvironment, LispMachine, LispRuntime, LispValue, MachineConfiguration, MayEval,
    PrimitiveSemantics, RuntimeBinding, RuntimeValueView, execute,
};
use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

/// Atoms supported by the common proof-free frontend realization.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoreAtom {
    Symbol(Vec<u8>),
    String { format: String, bytes: Vec<u8> },
    Integer(Int),
}

impl CoreAtom {
    pub fn symbol(name: impl AsRef<[u8]>) -> Self {
        Self::Symbol(name.as_ref().to_vec())
    }
}

/// Primitive vocabulary shared by the initial Lisp-family frontends.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Primitive {
    Cons,
    Car,
    Cdr,
    Atom,
    Consp,
    Null,
    Integer,
    Equal,
    Add,
    Subtract,
    Multiply,
    LessEqual,
    Append,
}

/// Concrete surface dialects targeting the common core.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SurfaceDialect {
    /// Pure Sector: pair operations and predicates, with numerals remaining
    /// symbols.
    Sector,
    /// Sector plus exact integer literals and arithmetic.
    SectorInt,
    /// Scheme-like lexical lambdas plus exact integer primitives.
    Scheme,
    /// The expression fragment used beneath ACL2 admission and worlds.
    Acl2Core,
}

impl SurfaceDialect {
    fn parses_integers(self) -> bool {
        matches!(self, Self::SectorInt | Self::Scheme | Self::Acl2Core)
    }

    pub(crate) fn primitive(self, name: &str) -> Option<Primitive> {
        Some(match name {
            "cons" => Primitive::Cons,
            "car" => Primitive::Car,
            "cdr" => Primitive::Cdr,
            "atom?" | "atom" => Primitive::Atom,
            "consp" | "pair?" => Primitive::Consp,
            "null?" | "null" => Primitive::Null,
            "integer?" | "integerp" => Primitive::Integer,
            "eq?" | "equal" => Primitive::Equal,
            "=" if self.parses_integers() => Primitive::Equal,
            "+" => Primitive::Add,
            "-" => Primitive::Subtract,
            "*" => Primitive::Multiply,
            "<=" => Primitive::LessEqual,
            "append" => Primitive::Append,
            _ => return None,
        })
    }
}

pub type FrontendExpr = CoreExpr<String, Datum<CoreAtom>, Primitive>;
pub type FrontendValue = HostValue<String, CoreAtom, Primitive>;
pub type FrontendConfiguration = HostConfiguration<String, CoreAtom, Primitive>;
pub type FrontendEnvironment = HostEnvironment<String, FrontendValue>;

/// A checked common-machine evaluation over an arbitrary Lisp runtime.
///
/// Keeping this alias public lets ACL2 admission, Scheme conformance suites,
/// and future WIT adapters exchange the same `MayEval` witness without naming
/// a concrete value or environment representation.
pub type RuntimeEvaluation<R> = MayEval<
    MachineConfiguration<
        <R as LispRuntime>::Expr,
        <R as LispRuntime>::Value,
        <R as LispRuntime>::Environment,
        <R as LispRuntime>::Primitive,
    >,
    <R as LispRuntime>::Value,
>;

/// A surface-to-core lowering error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowerError {
    EmptyApplication,
    Malformed { form: &'static str, detail: String },
}

impl Display for LowerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyApplication => f.write_str("an empty list is data, not an application"),
            Self::Malformed { form, detail } => write!(f, "malformed {form}: {detail}"),
        }
    }
}

impl core::error::Error for LowerError {}

/// Reusable lowering policy for a concrete Lisp-family frontend.
#[derive(Clone, Copy, Debug)]
pub struct Frontend {
    dialect: SurfaceDialect,
}

struct ParsedFormals {
    required: Vec<covalence_kernel_lisp::Parameter<String>>,
    rest: Option<covalence_kernel_lisp::Parameter<String>>,
}

impl Frontend {
    pub fn new(dialect: SurfaceDialect) -> Self {
        Self { dialect }
    }

    pub fn dialect(&self) -> SurfaceDialect {
        self.dialect
    }

    /// Lower one parsed form into the common expression core.
    pub fn lower(&self, form: &SExpr) -> Result<FrontendExpr, LowerError> {
        match form {
            SExpr::Atom(atom) => self.lower_atom(atom),
            SExpr::List(items) if items.is_empty() => Ok(CoreExpr::Literal(Datum::Nil)),
            SExpr::List(items) => self.lower_list(items),
        }
    }

    /// Quote parsed data into the direct inductive representation.
    pub fn quote(&self, form: &SExpr) -> Result<Datum<CoreAtom>, LowerError> {
        Ok(match form {
            SExpr::Atom(atom) => Datum::Atom(self.datum_atom(atom)),
            SExpr::List(items) => {
                let values = items
                    .iter()
                    .map(|item| self.quote(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Datum::list(values)
            }
        })
    }

    /// Lower `(define name (lambda (parameters...) body))` or
    /// `(defun name (parameters...) body)` into a named core closure.
    ///
    /// Naming the closure gives the partial operational semantics a recursive
    /// self-binding. It does not establish ACL2 termination or totality.
    pub fn definition(&self, form: &SExpr) -> Result<Option<(String, FrontendExpr)>, LowerError> {
        let Some(items) = form.as_list() else {
            return Ok(None);
        };
        let Some(kind) = items.first().and_then(SExpr::as_symbol) else {
            return Ok(None);
        };
        if kind == "define"
            && self.dialect == SurfaceDialect::Scheme
            && items.len() >= 3
            && let Some(signature) = items[1].as_list()
        {
            let (name, parameters) =
                signature
                    .split_first()
                    .ok_or_else(|| LowerError::Malformed {
                        form: "define",
                        detail: "procedure signature is empty".to_owned(),
                    })?;
            let name = self.symbol(name, "define", "name")?;
            let formals = self.parameters(&SExpr::List(parameters.to_vec()), "define")?;
            let body = self.lower_body("define", &items[2..])?;
            return Ok(Some((
                name.clone(),
                CoreExpr::Lambda {
                    name: Some(name),
                    parameters: formals.required,
                    rest: formals.rest,
                    body: Box::new(body),
                },
            )));
        }
        if kind == "define" && self.dialect == SurfaceDialect::Scheme && items.len() == 3 {
            let name = self.symbol(&items[1], "define", "name")?;
            let is_lambda = items[2]
                .as_list()
                .is_some_and(|value| value.first().and_then(SExpr::as_symbol) == Some("lambda"));
            if !is_lambda {
                return Ok(Some((name, self.lower(&items[2])?)));
            }
        }
        let (name, formals, body) = match kind {
            "define" | "label" if items.len() == 3 => {
                let name = self.symbol(&items[1], "definition", "name")?;
                let lambda = items[2].as_list().ok_or_else(|| LowerError::Malformed {
                    form: "definition",
                    detail: "value is not a lambda".to_owned(),
                })?;
                if lambda.len() < 3 || lambda[0].as_symbol() != Some("lambda") {
                    return Err(LowerError::Malformed {
                        form: "definition",
                        detail: "value is not a lambda".to_owned(),
                    });
                }
                (
                    name,
                    self.parameters(&lambda[1], "definition")?,
                    self.lower_body("definition", &lambda[2..])?,
                )
            }
            "defun" if items.len() == 4 => {
                let name = self.symbol(&items[1], "defun", "name")?;
                let formals = self.parameters(&items[2], "definition")?;
                if formals.rest.is_some() {
                    return Err(LowerError::Malformed {
                        form: "defun",
                        detail: "ACL2 logical functions have fixed arity".to_owned(),
                    });
                }
                (name, formals, self.lower(&items[3])?)
            }
            "define" | "label" | "defun" => {
                return Err(LowerError::Malformed {
                    form: "definition",
                    detail: "wrong number of fields".to_owned(),
                });
            }
            _ => return Ok(None),
        };
        Ok(Some((
            name.clone(),
            CoreExpr::Lambda {
                name: Some(name),
                parameters: formals.required,
                rest: formals.rest,
                body: Box::new(body),
            },
        )))
    }

    fn datum_atom(&self, atom: &Atom) -> CoreAtom {
        match atom {
            Atom::Symbol(text) if self.dialect.parses_integers() => Int::from_str(text)
                .map_or_else(|_| CoreAtom::symbol(text.as_bytes()), CoreAtom::Integer),
            Atom::Symbol(text) => CoreAtom::symbol(text.as_bytes()),
            Atom::Str { format, bytes } => CoreAtom::String {
                format: format.to_string(),
                bytes: bytes.to_vec(),
            },
        }
    }

    fn lower_atom(&self, atom: &Atom) -> Result<FrontendExpr, LowerError> {
        Ok(match atom {
            Atom::Symbol(text) if text.eq_ignore_ascii_case("nil") => CoreExpr::Truth(false),
            Atom::Symbol(text) if text.eq_ignore_ascii_case("t") => CoreExpr::Truth(true),
            Atom::Symbol(text) if self.dialect.parses_integers() && Int::from_str(text).is_ok() => {
                CoreExpr::Literal(Datum::Atom(CoreAtom::Integer(
                    Int::from_str(text).expect("checked integer"),
                )))
            }
            Atom::Symbol(text)
                if matches!(
                    self.dialect,
                    SurfaceDialect::Sector | SurfaceDialect::SectorInt
                ) =>
            {
                CoreExpr::Literal(Datum::Atom(CoreAtom::symbol(text.as_bytes())))
            }
            Atom::Symbol(text) => CoreExpr::Variable(text.to_string()),
            Atom::Str { .. } => CoreExpr::Literal(Datum::Atom(self.datum_atom(atom))),
        })
    }

    fn lower_list(&self, items: &[SExpr]) -> Result<FrontendExpr, LowerError> {
        let head = items[0].as_symbol();
        match head {
            Some("quote") => {
                self.exact_arity("quote", items, 2)?;
                Ok(CoreExpr::Quote(self.quote(&items[1])?))
            }
            Some("if") => {
                self.exact_arity("if", items, 4)?;
                Ok(CoreExpr::If {
                    condition: Box::new(self.lower(&items[1])?),
                    consequent: Box::new(self.lower(&items[2])?),
                    alternative: Box::new(self.lower(&items[3])?),
                })
            }
            Some("lambda") => self.lower_lambda(items),
            Some("let") => self.lower_let(items, false),
            Some("letrec") if self.dialect == SurfaceDialect::Scheme => self.lower_let(items, true),
            Some("begin") if self.dialect == SurfaceDialect::Scheme => {
                self.lower_sequence("begin", &items[1..])
            }
            Some("cond") => Ok(CoreExpr::Cond {
                clauses: self.lower_cond(&items[1..])?,
            }),
            Some(name) if self.dialect == SurfaceDialect::Scheme => Ok(CoreExpr::Apply {
                operator: Box::new(CoreExpr::Variable(name.to_owned())),
                arguments: items[1..]
                    .iter()
                    .map(|argument| self.lower(argument))
                    .collect::<Result<_, _>>()?,
            }),
            Some(name) if self.dialect.primitive(name).is_some() => Ok(CoreExpr::Primitive {
                operator: self.dialect.primitive(name).expect("matched"),
                arguments: items[1..]
                    .iter()
                    .map(|argument| self.lower(argument))
                    .collect::<Result<_, _>>()?,
            }),
            Some(name) => Ok(CoreExpr::Apply {
                operator: Box::new(CoreExpr::Variable(name.to_owned())),
                arguments: items[1..]
                    .iter()
                    .map(|argument| self.lower(argument))
                    .collect::<Result<_, _>>()?,
            }),
            None => Ok(CoreExpr::Apply {
                operator: Box::new(self.lower(&items[0])?),
                arguments: items[1..]
                    .iter()
                    .map(|argument| self.lower(argument))
                    .collect::<Result<_, _>>()?,
            }),
        }
    }

    fn lower_lambda(&self, items: &[SExpr]) -> Result<FrontendExpr, LowerError> {
        if items.len() < 3 {
            return Err(LowerError::Malformed {
                form: "lambda",
                detail: "expected parameters and at least one body expression".to_owned(),
            });
        }
        let formals = self.parameters(&items[1], "lambda")?;
        Ok(CoreExpr::Lambda {
            name: None,
            parameters: formals.required,
            rest: formals.rest,
            body: Box::new(self.lower_body("lambda", &items[2..])?),
        })
    }

    fn lower_sequence(
        &self,
        form: &'static str,
        expressions: &[SExpr],
    ) -> Result<FrontendExpr, LowerError> {
        let (first, rest) = expressions
            .split_first()
            .ok_or_else(|| LowerError::Malformed {
                form,
                detail: "expected at least one expression".to_owned(),
            })?;
        Ok(CoreExpr::Sequence {
            first: Box::new(self.lower(first)?),
            rest: rest
                .iter()
                .map(|expression| self.lower(expression))
                .collect::<Result<_, _>>()?,
        })
    }

    fn lower_body(
        &self,
        form: &'static str,
        expressions: &[SExpr],
    ) -> Result<FrontendExpr, LowerError> {
        if expressions.len() == 1 {
            self.lower(&expressions[0])
        } else if self.dialect != SurfaceDialect::Scheme {
            Err(LowerError::Malformed {
                form,
                detail: "this dialect requires exactly one body expression".to_owned(),
            })
        } else {
            self.lower_sequence(form, expressions)
        }
    }

    fn parameters(&self, form: &SExpr, owner: &'static str) -> Result<ParsedFormals, LowerError> {
        if let Some(rest) = form.as_symbol() {
            if self.dialect != SurfaceDialect::Scheme || rest == "." {
                return Err(LowerError::Malformed {
                    form: owner,
                    detail: "rest-only formals are Scheme syntax".to_owned(),
                });
            }
            return Ok(ParsedFormals {
                required: Vec::new(),
                rest: Some(covalence_kernel_lisp::Parameter::new(rest.to_owned())),
            });
        }

        let parameters = form.as_list().ok_or_else(|| LowerError::Malformed {
            form: owner,
            detail: "parameter declaration is not a list".to_owned(),
        })?;
        let dot = parameters
            .iter()
            .position(|parameter| parameter.as_symbol() == Some("."));
        let (required, rest) = match dot {
            None => (parameters, None),
            Some(index)
                if self.dialect == SurfaceDialect::Scheme
                    && index > 0
                    && index + 2 == parameters.len() =>
            {
                let rest =
                    parameters[index + 1]
                        .as_symbol()
                        .ok_or_else(|| LowerError::Malformed {
                            form: owner,
                            detail: "rest parameter is not a symbol".to_owned(),
                        })?;
                (&parameters[..index], Some(rest))
            }
            Some(_) => {
                return Err(LowerError::Malformed {
                    form: owner,
                    detail: "dotted formals must end in exactly one Scheme rest parameter"
                        .to_owned(),
                });
            }
        };
        let required = required
            .iter()
            .map(|parameter| {
                parameter
                    .as_symbol()
                    .filter(|name| *name != ".")
                    .map(|name| covalence_kernel_lisp::Parameter::new(name.to_owned()))
                    .ok_or_else(|| LowerError::Malformed {
                        form: owner,
                        detail: "parameter is not a symbol".to_owned(),
                    })
            })
            .collect::<Result<_, _>>()?;
        let parsed = ParsedFormals {
            required,
            rest: rest.map(|name| covalence_kernel_lisp::Parameter::new(name.to_owned())),
        };
        for (index, parameter) in parsed.required.iter().enumerate() {
            if parsed.required[..index]
                .iter()
                .any(|earlier| earlier.name == parameter.name)
                || parsed
                    .rest
                    .as_ref()
                    .is_some_and(|rest| rest.name == parameter.name)
            {
                return Err(LowerError::Malformed {
                    form: owner,
                    detail: format!("duplicate formal `{}`", parameter.name),
                });
            }
        }
        Ok(parsed)
    }

    fn symbol(&self, form: &SExpr, owner: &'static str, field: &str) -> Result<String, LowerError> {
        form.as_symbol()
            .map(str::to_owned)
            .ok_or_else(|| LowerError::Malformed {
                form: owner,
                detail: format!("{field} is not a symbol"),
            })
    }

    fn lower_let(&self, items: &[SExpr], recursive: bool) -> Result<FrontendExpr, LowerError> {
        let form = if recursive { "letrec" } else { "let" };
        if items.len() < 3 {
            return Err(LowerError::Malformed {
                form,
                detail: "expected bindings and at least one body expression".to_owned(),
            });
        }
        let bindings = items[1].as_list().ok_or_else(|| LowerError::Malformed {
            form,
            detail: "bindings are not a list".to_owned(),
        })?;
        let bindings = bindings
            .iter()
            .map(|binding| {
                let pair = binding.as_list().ok_or_else(|| LowerError::Malformed {
                    form,
                    detail: "binding is not a list".to_owned(),
                })?;
                if pair.len() != 2 {
                    return Err(LowerError::Malformed {
                        form,
                        detail: "binding must contain a name and expression".to_owned(),
                    });
                }
                let name = pair[0]
                    .as_symbol()
                    .ok_or_else(|| LowerError::Malformed {
                        form,
                        detail: "binding name is not a symbol".to_owned(),
                    })?
                    .to_owned();
                Ok(covalence_kernel_lisp::Binding::new(
                    name,
                    self.lower(&pair[1])?,
                ))
            })
            .collect::<Result<_, _>>()?;
        let body = Box::new(self.lower_body(form, &items[2..])?);
        Ok(if recursive {
            CoreExpr::LetRec { bindings, body }
        } else {
            CoreExpr::Let { bindings, body }
        })
    }

    fn lower_cond(
        &self,
        clauses: &[SExpr],
    ) -> Result<Vec<(FrontendExpr, FrontendExpr)>, LowerError> {
        clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| {
                let pair = clause.as_list().ok_or_else(|| LowerError::Malformed {
                    form: "cond",
                    detail: "clause is not a list".to_owned(),
                })?;
                if pair.len() != 2 {
                    return Err(LowerError::Malformed {
                        form: "cond",
                        detail: "clause must contain a condition and result".to_owned(),
                    });
                }
                let condition = if pair[0].as_symbol() == Some("else") {
                    if index + 1 != clauses.len() {
                        return Err(LowerError::Malformed {
                            form: "cond",
                            detail: "else must be the final clause".to_owned(),
                        });
                    }
                    CoreExpr::Truth(true)
                } else {
                    self.lower(&pair[0])?
                };
                Ok((condition, self.lower(&pair[1])?))
            })
            .collect()
    }

    fn exact_arity(
        &self,
        form: &'static str,
        items: &[SExpr],
        expected: usize,
    ) -> Result<(), LowerError> {
        if items.len() == expected {
            Ok(())
        } else {
            Err(LowerError::Malformed {
                form,
                detail: format!(
                    "expected {} operands, got {}",
                    expected - 1,
                    items.len().saturating_sub(1)
                ),
            })
        }
    }
}

/// Standard proof-free primitive implementation shared by differential tests
/// and interactive frontends.
#[derive(Clone, Copy, Debug, Default)]
pub struct StandardPrimitives;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrimitiveError {
    Arity { expected: usize, actual: usize },
    ExpectedDatum,
    ExpectedCons,
    ExpectedInteger,
}

/// Primitive-language failure separated from representation failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrimitiveExecutionError<E> {
    Language(PrimitiveError),
    Runtime(E),
}

impl<E> From<PrimitiveError> for PrimitiveExecutionError<E> {
    fn from(error: PrimitiveError) -> Self {
        Self::Language(error)
    }
}

pub type HostPrimitiveError = PrimitiveExecutionError<Infallible>;

impl CorePrimitive for StandardPrimitives {
    type Symbol = String;
    type Atom = CoreAtom;
    type Primitive = Primitive;
}

impl<V> PrimitiveSemantics<V> for StandardPrimitives
where
    V: LispValue<Atom = CoreAtom, Primitive = Primitive>,
{
    type Error = PrimitiveExecutionError<V::Error>;

    fn apply(
        &self,
        runtime: &V,
        primitive: &Primitive,
        arguments: Vec<V::Value>,
    ) -> Result<V::Value, Self::Error> {
        let arguments = arguments.as_slice();
        match primitive {
            Primitive::Cons => {
                let [head, tail] = self.values::<_, 2>(arguments)?;
                runtime
                    .cons(head, tail)
                    .map_err(PrimitiveExecutionError::Runtime)
            }
            Primitive::Car => {
                let [value] = self.values::<_, 1>(arguments)?;
                match runtime
                    .view(&value)
                    .map_err(PrimitiveExecutionError::Runtime)?
                {
                    RuntimeValueView::Cons { head, .. } => Ok(head),
                    _ => Ok(runtime.nil()),
                }
            }
            Primitive::Cdr => {
                let [value] = self.values::<_, 1>(arguments)?;
                match runtime
                    .view(&value)
                    .map_err(PrimitiveExecutionError::Runtime)?
                {
                    RuntimeValueView::Cons { tail, .. } => Ok(tail),
                    _ => Ok(runtime.nil()),
                }
            }
            Primitive::Atom => {
                let [value] = self.values::<_, 1>(arguments)?;
                let is_atom = !matches!(
                    runtime
                        .view(&value)
                        .map_err(PrimitiveExecutionError::Runtime)?,
                    RuntimeValueView::Cons { .. }
                );
                self.truth(runtime, is_atom)
            }
            Primitive::Consp => {
                let [value] = self.values::<_, 1>(arguments)?;
                let is_cons = matches!(
                    runtime
                        .view(&value)
                        .map_err(PrimitiveExecutionError::Runtime)?,
                    RuntimeValueView::Cons { .. }
                );
                self.truth(runtime, is_cons)
            }
            Primitive::Null => {
                let [value] = self.values::<_, 1>(arguments)?;
                let is_nil = matches!(
                    runtime
                        .view(&value)
                        .map_err(PrimitiveExecutionError::Runtime)?,
                    RuntimeValueView::Nil
                );
                self.truth(runtime, is_nil)
            }
            Primitive::Integer => {
                let [value] = self.values::<_, 1>(arguments)?;
                let is_integer = matches!(
                    runtime
                        .view(&value)
                        .map_err(PrimitiveExecutionError::Runtime)?,
                    RuntimeValueView::Atom(CoreAtom::Integer(_))
                );
                self.truth(runtime, is_integer)
            }
            Primitive::Equal => {
                let [left, right] = self.values::<_, 2>(arguments)?;
                let equal = runtime
                    .equivalent(&left, &right)
                    .map_err(PrimitiveExecutionError::Runtime)?;
                self.truth(runtime, equal)
            }
            Primitive::Add => self.integer_binary(runtime, arguments, |left, right| left + right),
            Primitive::Subtract => {
                self.integer_binary(runtime, arguments, |left, right| left - right)
            }
            Primitive::Multiply => {
                self.integer_binary(runtime, arguments, |left, right| left * right)
            }
            Primitive::LessEqual => {
                let [left, right] = self.integers(runtime, arguments)?;
                self.truth(runtime, left <= right)
            }
            Primitive::Append => {
                let [left, right] = self.values::<_, 2>(arguments)?;
                self.append(runtime, left, right)
            }
        }
    }

    fn truth(&self, runtime: &V, value: bool) -> Result<V::Value, Self::Error> {
        if value {
            runtime
                .atom(CoreAtom::symbol("t"))
                .map_err(PrimitiveExecutionError::Runtime)
        } else {
            Ok(runtime.nil())
        }
    }

    fn is_false(&self, runtime: &V, value: &V::Value) -> Result<bool, Self::Error> {
        Ok(matches!(
            runtime
                .view(value)
                .map_err(PrimitiveExecutionError::Runtime)?,
            RuntimeValueView::Nil
        ))
    }
}

impl StandardPrimitives {
    fn append<V: LispValue<Atom = CoreAtom, Primitive = Primitive>>(
        &self,
        runtime: &V,
        left: V::Value,
        right: V::Value,
    ) -> Result<V::Value, PrimitiveExecutionError<V::Error>> {
        match runtime
            .view(&left)
            .map_err(PrimitiveExecutionError::Runtime)?
        {
            RuntimeValueView::Nil => Ok(right),
            RuntimeValueView::Cons { head, tail } => {
                let tail = self.append(runtime, tail, right)?;
                runtime
                    .cons(head, tail)
                    .map_err(PrimitiveExecutionError::Runtime)
            }
            // ACL2's `binary-append` and the existing kernel Lisp theory use
            // this total extension. Scheme programs should still pass proper
            // lists; the shared primitive remains defined on every datum.
            RuntimeValueView::Atom(_)
            | RuntimeValueView::Closure
            | RuntimeValueView::Primitive(_)
            | RuntimeValueView::ApplyListProcedure => Ok(right),
        }
    }

    fn values<V: Clone, const N: usize>(&self, arguments: &[V]) -> Result<[V; N], PrimitiveError> {
        if arguments.len() != N {
            return Err(PrimitiveError::Arity {
                expected: N,
                actual: arguments.len(),
            });
        }
        arguments
            .to_vec()
            .try_into()
            .map_err(|_| unreachable!("length checked"))
    }

    fn integers<V: LispValue<Atom = CoreAtom, Primitive = Primitive>>(
        &self,
        runtime: &V,
        arguments: &[V::Value],
    ) -> Result<[Int; 2], PrimitiveExecutionError<V::Error>> {
        let values = self.values::<_, 2>(arguments)?;
        values
            .map(|value| {
                match runtime
                    .view(&value)
                    .map_err(PrimitiveExecutionError::Runtime)?
                {
                    RuntimeValueView::Atom(CoreAtom::Integer(value)) => {
                        Ok::<Int, PrimitiveExecutionError<V::Error>>(value)
                    }
                    _ => Err(PrimitiveError::ExpectedInteger.into()),
                }
            })
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| unreachable!("array length preserved"))
    }

    fn integer_binary<V: LispValue<Atom = CoreAtom, Primitive = Primitive>>(
        &self,
        runtime: &V,
        arguments: &[V::Value],
        operation: impl FnOnce(Int, Int) -> Int,
    ) -> Result<V::Value, PrimitiveExecutionError<V::Error>> {
        let [left, right] = self.integers(runtime, arguments)?;
        runtime
            .atom(CoreAtom::Integer(operation(left, right)))
            .map_err(PrimitiveExecutionError::Runtime)
    }
}

pub fn host_machine() -> CoreMachine<StandardPrimitives> {
    CoreMachine::new(StandardPrimitives)
}

pub type ArenaFrontendRuntime = ArenaRuntime<String, CoreAtom, Primitive>;
pub type ArenaFrontendMachine = LispMachine<ArenaFrontendRuntime, StandardPrimitives>;

pub fn arena_machine() -> ArenaFrontendMachine {
    LispMachine::with_runtime(
        ArenaFrontendRuntime::default(),
        StandardPrimitives,
        covalence_kernel_lisp::Strategy::STRICT_LEXICAL,
    )
}

const SCHEME_PRIMITIVES: &[(&str, Primitive)] = &[
    ("cons", Primitive::Cons),
    ("car", Primitive::Car),
    ("cdr", Primitive::Cdr),
    ("atom?", Primitive::Atom),
    ("atom", Primitive::Atom),
    ("pair?", Primitive::Consp),
    ("consp", Primitive::Consp),
    ("null?", Primitive::Null),
    ("null", Primitive::Null),
    ("integer?", Primitive::Integer),
    ("integerp", Primitive::Integer),
    ("eq?", Primitive::Equal),
    ("equal", Primitive::Equal),
    ("=", Primitive::Equal),
    ("+", Primitive::Add),
    ("-", Primitive::Subtract),
    ("*", Primitive::Multiply),
    ("<=", Primitive::LessEqual),
    ("append", Primitive::Append),
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InitialEnvironmentError<V, E> {
    Value(V),
    Environment(E),
}

/// Initial lexical bindings supplied by a concrete frontend runtime.
///
/// Kernel evaluation itself has no distinguished names: Scheme chooses these
/// bindings as language policy, making primitives ordinary shadowable values
/// rather than syntax.
pub fn initial_environment_for<V, E>(
    values: &V,
    environments: &E,
    dialect: SurfaceDialect,
) -> Result<E::Environment, InitialEnvironmentError<V::Error, E::Error>>
where
    V: LispValue<Atom = CoreAtom, Primitive = Primitive, Value = E::Value>,
    E: LispEnvironment<Symbol = String>,
{
    let environment = environments.empty();
    if dialect != SurfaceDialect::Scheme {
        return Ok(environment);
    }
    environments
        .extend(
            &environment,
            SCHEME_PRIMITIVES
                .iter()
                .map(|(name, primitive)| {
                    values
                        .primitive(*primitive)
                        .map(|value| RuntimeBinding::new((*name).to_owned(), value))
                        .map_err(InitialEnvironmentError::Value)
                })
                .chain([Ok(RuntimeBinding::new(
                    "apply".to_owned(),
                    values.apply_list_procedure(),
                ))])
                .collect::<Result<Vec<_>, _>>()?,
        )
        .map_err(InitialEnvironmentError::Environment)
}

pub fn initial_environment(dialect: SurfaceDialect) -> FrontendEnvironment {
    let runtime = covalence_kernel_lisp::HostRuntime::<String, CoreAtom, Primitive>::default();
    initial_environment_for(runtime.values(), runtime.environments(), dialect).unwrap_or_else(
        |error| match error {
            InitialEnvironmentError::Value(never) | InitialEnvironmentError::Environment(never) => {
                match never {}
            }
        },
    )
}

type ValueErrorOf<R> = <<R as LispRuntime>::Values as LispValue>::Error;
type EnvironmentErrorOf<R> = <<R as LispRuntime>::Environments as LispEnvironment>::Error;
pub type RuntimeSessionMachineError<R> =
    CoreMachineError<String, PrimitiveExecutionError<ValueErrorOf<R>>, <R as LispRuntime>::Error>;

#[derive(Debug)]
pub enum SessionError<M, V, E> {
    Setup(InitialEnvironmentError<V, E>),
    Lower(LowerError),
    Execute(ExecutionError<M>),
    Machine(M),
    ExpectedDefinition { index: usize },
    DefinitionDidNotProduceClosure,
}

impl<M: Display, V: Debug, E: Debug> Display for SessionError<M, V, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Setup(error) => write!(f, "failed to initialize frontend environment: {error:?}"),
            Self::Lower(error) => Display::fmt(error, f),
            Self::Execute(error) => Display::fmt(error, f),
            Self::Machine(error) => Display::fmt(error, f),
            Self::ExpectedDefinition { index } => {
                write!(f, "form {index} is not a Lisp definition")
            }
            Self::DefinitionDidNotProduceClosure => {
                f.write_str("definition did not evaluate to a closure")
            }
        }
    }
}

impl<M, V, E> core::error::Error for SessionError<M, V, E>
where
    M: core::error::Error,
    V: Debug,
    E: Debug,
{
}

pub type RuntimeSessionError<R> =
    SessionError<RuntimeSessionMachineError<R>, ValueErrorOf<R>, EnvironmentErrorOf<R>>;

/// Stateful proof-free frontend execution over a selected runtime backend.
///
/// Definitions are lexical named closures. Recursive calls may diverge; fuel
/// exhaustion is an ordinary result and carries no ACL2 admission claim.
#[derive(Clone, Debug)]
pub struct RuntimeSession<R>
where
    R: LispRuntime,
{
    frontend: Frontend,
    machine: LispMachine<R, StandardPrimitives>,
    environment: R::Environment,
    fuel: usize,
}

impl<R> RuntimeSession<R>
where
    R: LispRuntime<
            Symbol = String,
            Atom = CoreAtom,
            Datum = Datum<CoreAtom>,
            Primitive = Primitive,
            Expr = FrontendExpr,
        >,
    R::Value: Debug + PartialEq,
    R::Environment: Debug + PartialEq,
{
    pub fn with_runtime(
        dialect: SurfaceDialect,
        fuel: usize,
        runtime: R,
    ) -> Result<Self, RuntimeSessionError<R>> {
        let environment =
            initial_environment_for(runtime.values(), runtime.environments(), dialect)
                .map_err(SessionError::Setup)?;
        Ok(Self {
            frontend: Frontend::new(dialect),
            machine: LispMachine::with_runtime(
                runtime,
                StandardPrimitives,
                covalence_kernel_lisp::Strategy::STRICT_LEXICAL,
            ),
            environment,
            fuel,
        })
    }

    pub fn runtime(&self) -> &R {
        self.machine.runtime()
    }

    pub fn environment(&self) -> &R::Environment {
        &self.environment
    }

    pub fn evaluate(&self, form: &SExpr) -> Result<R::Value, RuntimeSessionError<R>> {
        let expression = self.frontend.lower(form).map_err(SessionError::Lower)?;
        self.evaluate_core(&expression)
    }

    pub fn define(&mut self, form: &SExpr) -> Result<Option<String>, RuntimeSessionError<R>> {
        let Some((name, expression)) = self
            .frontend
            .definition(form)
            .map_err(SessionError::Lower)?
        else {
            return Ok(None);
        };
        let value = self.evaluate_core(&expression)?;
        self.environment = self
            .machine
            .runtime()
            .environments()
            .extend(
                &self.environment,
                vec![RuntimeBinding::new(name.clone(), value)],
            )
            .map_err(|error| {
                SessionError::Machine(CoreMachineError::Runtime(
                    self.machine.runtime().environment_error(error),
                ))
            })?;
        Ok(Some(name))
    }

    /// Install an already-lowered recursive definition into the partial
    /// operational environment.
    ///
    /// This establishes only executable recursive binding. In particular it
    /// does not inspect or replay ACL2 admission evidence and makes no
    /// termination or totality claim.
    pub fn define_core(
        &mut self,
        definition: LispDefinition<String, FrontendExpr>,
    ) -> Result<String, RuntimeSessionError<R>> {
        let name = definition.name.clone();
        let expression = definition.into_recursive_lambda();
        self.environment = self
            .machine
            .bind_recursive(&self.environment, vec![(name.clone(), expression)])
            .map_err(SessionError::Machine)?;
        Ok(name)
    }

    /// Atomically install a mutually recursive group of `define`, `label`, or
    /// `defun` forms.
    ///
    /// Every closure captures the same newly allocated lexical generation, so
    /// definitions may refer forward as well as backward within the group.
    pub fn define_group(&mut self, forms: &[SExpr]) -> Result<Vec<String>, RuntimeSessionError<R>> {
        let mut names = Vec::with_capacity(forms.len());
        let mut bindings = Vec::with_capacity(forms.len());
        for (index, form) in forms.iter().enumerate() {
            let Some((name, expression)) = self
                .frontend
                .definition(form)
                .map_err(SessionError::Lower)?
            else {
                return Err(SessionError::ExpectedDefinition { index });
            };
            names.push(name.clone());
            bindings.push((name, expression));
        }
        self.environment = self
            .machine
            .bind_recursive(&self.environment, bindings)
            .map_err(SessionError::Machine)?;
        Ok(names)
    }

    /// Evaluate already-lowered shared Lisp syntax.
    ///
    /// This is the backend seam used by conformance suites and callers that
    /// parse/lower once before selecting among host and proof-producing
    /// realizations.
    pub fn evaluate_core(
        &self,
        expression: &FrontendExpr,
    ) -> Result<R::Value, RuntimeSessionError<R>> {
        Ok(self.evaluate_core_evidence(expression)?.value)
    }

    /// Evaluate lowered syntax and retain checked `MayEval` evidence.
    ///
    /// This is still proof-free evidence: a theorem-producing backend must
    /// replay its trace through the kernel relation. Unlike returning only a
    /// value, however, it preserves the exact finite execution needed by the
    /// admission adequacy bridge.
    pub fn evaluate_core_evidence(
        &self,
        expression: &FrontendExpr,
    ) -> Result<RuntimeEvaluation<R>, RuntimeSessionError<R>> {
        let trace = execute(
            &self.machine,
            MachineConfiguration::with_environment(expression.clone(), self.environment.clone()),
            self.fuel,
        )
        .map_err(SessionError::Execute)?;
        let value = trace
            .end()
            .terminal_value()
            .cloned()
            .ok_or(SessionError::DefinitionDidNotProduceClosure)?;
        MayEval::check(&self.machine, trace, value).map_err(SessionError::Execute)
    }
}

pub type HostFrontendRuntime = covalence_kernel_lisp::HostRuntime<String, CoreAtom, Primitive>;
pub type HostSession = RuntimeSession<HostFrontendRuntime>;
pub type HostSessionError = RuntimeSessionError<HostFrontendRuntime>;
pub type ArenaSession = RuntimeSession<ArenaFrontendRuntime>;

impl RuntimeSession<HostFrontendRuntime> {
    pub fn new(dialect: SurfaceDialect, fuel: usize) -> Self {
        Self::with_runtime(dialect, fuel, HostFrontendRuntime::default()).unwrap_or_else(|error| {
            match error {
                SessionError::Setup(InitialEnvironmentError::Value(never))
                | SessionError::Setup(InitialEnvironmentError::Environment(never))
                | SessionError::Machine(CoreMachineError::Runtime(never)) => match never {},
                _ => unreachable!("constructing an empty host session does not execute code"),
            }
        })
    }
}

impl RuntimeSession<ArenaFrontendRuntime> {
    pub fn arena(
        dialect: SurfaceDialect,
        fuel: usize,
    ) -> Result<Self, RuntimeSessionError<ArenaFrontendRuntime>> {
        Self::with_runtime(dialect, fuel, ArenaFrontendRuntime::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn one(source: &str) -> SExpr {
        crate::reader::read(source).unwrap().pop().unwrap()
    }

    fn run(dialect: SurfaceDialect, source: &str) -> FrontendValue {
        HostSession::new(dialect, 128)
            .evaluate(&one(source))
            .unwrap()
    }

    fn run_arena(source: &str) -> CoreAtom {
        let expression = Frontend::new(SurfaceDialect::Scheme)
            .lower(&one(source))
            .unwrap();
        let machine = arena_machine();
        let environment = initial_environment_for(
            machine.runtime().values(),
            machine.runtime().environments(),
            SurfaceDialect::Scheme,
        )
        .unwrap();
        let trace = execute(
            &machine,
            covalence_kernel_lisp::MachineConfiguration::with_environment(expression, environment),
            256,
        )
        .unwrap();
        let value = trace.end().terminal_value().expect("terminal value");
        match machine.runtime().values().view(value).unwrap() {
            RuntimeValueView::Atom(atom) => atom,
            other => panic!("expected atom, got {other:?}"),
        }
    }

    #[test]
    fn sector_pairs_lower_to_the_common_core() {
        assert_eq!(
            run(SurfaceDialect::Sector, "(car (cons (quote head) ()))"),
            HostValue::datum(Datum::Atom(CoreAtom::symbol("head")))
        );
    }

    #[test]
    fn scheme_lambda_let_and_exact_integers_share_the_machine() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(let ((twice (lambda (x) (+ x x)))) (twice 21))"
            ),
            HostValue::datum(Datum::Atom(CoreAtom::Integer(Int::from(42))))
        );
    }

    #[test]
    fn scheme_programs_run_unchanged_on_the_handle_runtime() {
        assert_eq!(
            run_arena(
                "(letrec ((length
                            (lambda (xs)
                              (if (null? xs)
                                  0
                                  (+ 1 (length (cdr xs)))))))
                   (length (quote (a b c))))"
            ),
            CoreAtom::Integer(Int::from(3))
        );
        assert_eq!(
            run_arena("(let ((invoke apply)) (invoke + (quote (20 22))))"),
            CoreAtom::Integer(Int::from(42)),
            "first-class primitive and apply-list dispatch share the owned argument API"
        );
    }

    #[test]
    fn scheme_begin_and_multi_expression_bodies_share_strict_sequence() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(begin (+ 100 200) (let ((x 40)) (+ x 1) (+ x 2)))"
            ),
            HostValue::datum(Datum::Atom(CoreAtom::Integer(Int::from(42))))
        );

        let lowered = Frontend::new(SurfaceDialect::Scheme)
            .lower(&one("(lambda (x) (+ x 1) (+ x 2))"))
            .unwrap();
        assert!(matches!(
            lowered,
            CoreExpr::Lambda {
                body,
                ..
            } if matches!(body.as_ref(), CoreExpr::Sequence { rest, .. } if rest.len() == 1)
        ));
    }

    #[test]
    fn scheme_rest_formals_hold_first_class_values() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(((lambda args (car args)) (lambda (x) x)) 42)"
            ),
            HostValue::Atom(CoreAtom::Integer(Int::from(42)))
        );
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "((lambda (head . tail) (car tail)) 1 2 3)"
            ),
            HostValue::Atom(CoreAtom::Integer(Int::from(2)))
        );
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(let ((f (lambda (x) x)))
                   (apply (car (cons f nil)) (quote (42))))"
            ),
            HostValue::Atom(CoreAtom::Integer(Int::from(42)))
        );
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(apply (lambda (a b . rest) (car rest))
                        1
                        (quote (2 42)))"
            ),
            HostValue::Atom(CoreAtom::Integer(Int::from(42)))
        );
    }

    #[test]
    fn scheme_formals_reject_duplicates_and_malformed_dots() {
        let frontend = Frontend::new(SurfaceDialect::Scheme);
        for source in [
            "(lambda (x x) x)",
            "(lambda (x . x) x)",
            "(lambda (. rest) rest)",
            "(lambda (x . rest extra) x)",
        ] {
            assert!(
                frontend.lower(&one(source)).is_err(),
                "{source} must not lower"
            );
        }
    }

    #[test]
    fn scheme_primitives_and_apply_are_first_class_shadowable_values() {
        for source in [
            "(let ((plus +)) (plus 20 22))",
            "((car (cons + nil)) 20 22)",
            "(let ((invoke apply)) (invoke + (quote (20 22))))",
            "(let ((+ (lambda (left right) left))) (+ 42 0))",
        ] {
            assert_eq!(
                run(SurfaceDialect::Scheme, source),
                HostValue::Atom(CoreAtom::Integer(Int::from(42))),
                "{source}"
            );
        }

        let mut session = HostSession::new(SurfaceDialect::Scheme, 128);
        assert_eq!(
            session.define(&one("(define plus +)")).unwrap(),
            Some("plus".to_owned())
        );
        assert_eq!(
            session.evaluate(&one("(plus 20 22)")).unwrap(),
            HostValue::Atom(CoreAtom::Integer(Int::from(42)))
        );
        assert_eq!(
            session
                .define(&one("(define (sum-with-rest first . rest)
                       0
                       (+ first (car rest)))"))
                .unwrap(),
            Some("sum-with-rest".to_owned())
        );
        assert_eq!(
            session.evaluate(&one("(sum-with-rest 20 22)")).unwrap(),
            HostValue::Atom(CoreAtom::Integer(Int::from(42)))
        );
    }

    #[test]
    fn scheme_letrec_lowers_to_mutually_recursive_core_bindings() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(letrec
                    ((even-list?
                       (lambda (xs)
                         (if (null? xs) t (odd-list? (cdr xs)))))
                     (odd-list?
                       (lambda (xs)
                         (if (null? xs) nil (even-list? (cdr xs))))))
                    (even-list? (quote (a b))))"
            ),
            HostValue::datum(Datum::Atom(CoreAtom::symbol("t")))
        );
    }

    #[test]
    fn host_append_preserves_list_order() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(append (quote (a b)) (quote (c d)))"
            ),
            HostValue::datum(Datum::list([
                Datum::Atom(CoreAtom::symbol("a")),
                Datum::Atom(CoreAtom::symbol("b")),
                Datum::Atom(CoreAtom::symbol("c")),
                Datum::Atom(CoreAtom::symbol("d")),
            ]))
        );
        assert_eq!(
            run(
                SurfaceDialect::Acl2Core,
                "(append (quote ignored) (quote (tail)))"
            ),
            HostValue::datum(Datum::list([Datum::Atom(CoreAtom::symbol("tail"))]))
        );
    }

    #[test]
    fn definition_groups_allow_forward_references() {
        let mut session = HostSession::new(SurfaceDialect::Scheme, 256);
        let forms = crate::reader::read(
            "(label first (lambda (x) (second x)))
             (label second (lambda (x) (cons x (quote ()))))",
        )
        .unwrap();
        assert_eq!(
            session.define_group(&forms).unwrap(),
            vec!["first".to_owned(), "second".to_owned()]
        );
        assert_eq!(
            session.evaluate(&one("(first (quote value))")).unwrap(),
            HostValue::datum(Datum::list([Datum::Atom(CoreAtom::symbol("value"))]))
        );
    }

    #[test]
    fn stateful_definition_groups_are_runtime_generic() {
        let mut session = ArenaSession::arena(SurfaceDialect::Scheme, 256).unwrap();
        let forms = crate::reader::read(
            "(label first (lambda (x) (second x)))
             (label second (lambda (x) (cons x (quote ()))))",
        )
        .unwrap();
        session.define_group(&forms).unwrap();
        let value = session.evaluate(&one("(first (quote value))")).unwrap();
        let datum = covalence_kernel_lisp::project_datum(
            session.runtime().data(),
            session.runtime().values(),
            &value,
        )
        .unwrap()
        .expect("result contains only data");
        assert_eq!(datum, Datum::list([Datum::Atom(CoreAtom::symbol("value"))]));
    }

    #[test]
    fn cond_is_derived_from_if_and_nil_truthiness() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(cond ((null? (quote (x))) 0) (else 1))"
            ),
            HostValue::datum(Datum::Atom(CoreAtom::Integer(Int::from(1))))
        );
    }

    #[test]
    fn acl2_expression_fragment_uses_acl2_primitive_names() {
        assert_eq!(
            run(SurfaceDialect::Acl2Core, "(equal (+ 2 3) 5)"),
            HostValue::datum(Datum::Atom(CoreAtom::symbol("t")))
        );
    }

    #[test]
    fn scheme_named_definition_is_genuinely_recursive_and_partial() {
        let mut session = HostSession::new(SurfaceDialect::Scheme, 512);
        assert_eq!(
            session
                .define(&one("(define fact (lambda (n)
                       (if (<= n 1) 1 (* n (fact (- n 1))))))"))
                .unwrap(),
            Some("fact".to_owned())
        );
        assert_eq!(
            session.evaluate(&one("(fact 5)")).unwrap(),
            HostValue::datum(Datum::Atom(CoreAtom::Integer(Int::from(120))))
        );
    }

    #[test]
    fn acl2_defun_shares_execution_but_not_admission() {
        let mut session = HostSession::new(SurfaceDialect::Acl2Core, 128);
        session.define(&one("(defun add1 (x) (+ x 1))")).unwrap();
        assert_eq!(
            session.evaluate(&one("(add1 41)")).unwrap(),
            HostValue::datum(Datum::Atom(CoreAtom::Integer(Int::from(42))))
        );
    }
}

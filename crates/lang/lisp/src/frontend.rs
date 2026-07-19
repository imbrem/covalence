//! Shared surface lowering and proof-free execution for Lisp frontends.
//!
//! Parsing remains outside the kernel API. This module translates the common
//! parsed S-expression tree into [`covalence_kernel_lisp::CoreExpr`], using an
//! explicit dialect policy for names, primitives, special forms, and numeric
//! literals. Sector, Scheme, and ACL2's expression fragment therefore share
//! the same core syntax without sharing ACL2 admission or Scheme-specific
//! surface extensions.

use core::fmt::{Display, Formatter};
use std::str::FromStr;

use covalence_kernel_lisp::{
    CoreExpr, CoreMachine, CoreMachineError, CorePrimitive, Datum, ExecutionError,
    HostConfiguration, HostEnvironment, HostValue, execute,
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

    fn primitive(self, name: &str) -> Option<Primitive> {
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
        let (name, parameters, body) = match kind {
            "define" | "label" if items.len() == 3 => {
                let name = self.symbol(&items[1], "definition", "name")?;
                let lambda = items[2].as_list().ok_or_else(|| LowerError::Malformed {
                    form: "definition",
                    detail: "value is not a lambda".to_owned(),
                })?;
                if lambda.len() != 3 || lambda[0].as_symbol() != Some("lambda") {
                    return Err(LowerError::Malformed {
                        form: "definition",
                        detail: "value is not a lambda".to_owned(),
                    });
                }
                (name, &lambda[1], &lambda[2])
            }
            "defun" if items.len() == 4 => (
                self.symbol(&items[1], "defun", "name")?,
                &items[2],
                &items[3],
            ),
            "define" | "label" | "defun" => {
                return Err(LowerError::Malformed {
                    form: "definition",
                    detail: "wrong number of fields".to_owned(),
                });
            }
            _ => return Ok(None),
        };
        let parameters = self.parameters(parameters, "definition")?;
        Ok(Some((
            name.clone(),
            CoreExpr::Lambda {
                name: Some(name),
                parameters,
                body: Box::new(self.lower(body)?),
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
            Some("cond") => Ok(CoreExpr::Cond {
                clauses: self.lower_cond(&items[1..])?,
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
        self.exact_arity("lambda", items, 3)?;
        Ok(CoreExpr::Lambda {
            name: None,
            parameters: self.parameters(&items[1], "lambda")?,
            body: Box::new(self.lower(&items[2])?),
        })
    }

    fn parameters(
        &self,
        form: &SExpr,
        owner: &'static str,
    ) -> Result<Vec<covalence_kernel_lisp::Parameter<String>>, LowerError> {
        let parameters = form.as_list().ok_or_else(|| LowerError::Malformed {
            form: owner,
            detail: "parameter declaration is not a list".to_owned(),
        })?;
        parameters
            .iter()
            .map(|parameter| {
                parameter
                    .as_symbol()
                    .map(|name| covalence_kernel_lisp::Parameter::new(name.to_owned()))
                    .ok_or_else(|| LowerError::Malformed {
                        form: owner,
                        detail: "parameter is not a symbol".to_owned(),
                    })
            })
            .collect()
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
        self.exact_arity(form, items, 3)?;
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
        let body = Box::new(self.lower(&items[2])?);
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

impl CorePrimitive for StandardPrimitives {
    type Symbol = String;
    type Atom = CoreAtom;
    type Primitive = Primitive;
    type Error = PrimitiveError;

    fn apply(
        &self,
        primitive: &Primitive,
        arguments: &[FrontendValue],
    ) -> Result<FrontendValue, PrimitiveError> {
        match primitive {
            Primitive::Cons => {
                let [head, tail] = self.datums::<2>(arguments)?;
                Ok(HostValue::Datum(Datum::cons(head, tail)))
            }
            Primitive::Car => {
                let [value] = self.datums::<1>(arguments)?;
                match value {
                    Datum::Cons(head, _) => Ok(HostValue::Datum(*head)),
                    Datum::Atom(_) | Datum::Nil => Ok(HostValue::Datum(Datum::Nil)),
                }
            }
            Primitive::Cdr => {
                let [value] = self.datums::<1>(arguments)?;
                match value {
                    Datum::Cons(_, tail) => Ok(HostValue::Datum(*tail)),
                    Datum::Atom(_) | Datum::Nil => Ok(HostValue::Datum(Datum::Nil)),
                }
            }
            Primitive::Atom => {
                let [value] = self.datums::<1>(arguments)?;
                Ok(self.truth(!matches!(value, Datum::Cons(_, _))))
            }
            Primitive::Consp => {
                let [value] = self.datums::<1>(arguments)?;
                Ok(self.truth(matches!(value, Datum::Cons(_, _))))
            }
            Primitive::Null => {
                let [value] = self.datums::<1>(arguments)?;
                Ok(self.truth(matches!(value, Datum::Nil)))
            }
            Primitive::Integer => {
                let [value] = self.datums::<1>(arguments)?;
                Ok(self.truth(matches!(value, Datum::Atom(CoreAtom::Integer(_)))))
            }
            Primitive::Equal => {
                let [left, right] = self.datums::<2>(arguments)?;
                Ok(self.truth(left == right))
            }
            Primitive::Add => self.integer_binary(arguments, |left, right| left + right),
            Primitive::Subtract => self.integer_binary(arguments, |left, right| left - right),
            Primitive::Multiply => self.integer_binary(arguments, |left, right| left * right),
            Primitive::LessEqual => {
                let [left, right] = self.integers(arguments)?;
                Ok(self.truth(left <= right))
            }
            Primitive::Append => {
                let [left, right] = self.datums::<2>(arguments)?;
                Ok(HostValue::Datum(Self::append(left, right)?))
            }
        }
    }

    fn truth(&self, value: bool) -> FrontendValue {
        StandardPrimitives::truth(self, value)
    }
}

impl StandardPrimitives {
    fn append(
        left: Datum<CoreAtom>,
        right: Datum<CoreAtom>,
    ) -> Result<Datum<CoreAtom>, PrimitiveError> {
        match left {
            Datum::Nil => Ok(right),
            Datum::Cons(head, tail) => Ok(Datum::cons(*head, Self::append(*tail, right)?)),
            // ACL2's `binary-append` and the existing kernel Lisp theory use
            // this total extension. Scheme programs should still pass proper
            // lists; the shared primitive remains defined on every datum.
            Datum::Atom(_) => Ok(right),
        }
    }

    fn truth(&self, value: bool) -> FrontendValue {
        HostValue::Datum(if value {
            Datum::Atom(CoreAtom::symbol("t"))
        } else {
            Datum::Nil
        })
    }

    fn datums<const N: usize>(
        &self,
        arguments: &[FrontendValue],
    ) -> Result<[Datum<CoreAtom>; N], PrimitiveError> {
        if arguments.len() != N {
            return Err(PrimitiveError::Arity {
                expected: N,
                actual: arguments.len(),
            });
        }
        let values = arguments
            .iter()
            .map(|value| match value {
                HostValue::Datum(datum) => Ok(datum.clone()),
                HostValue::Closure(_) => Err(PrimitiveError::ExpectedDatum),
            })
            .collect::<Result<Vec<_>, _>>()?;
        values
            .try_into()
            .map_err(|_| unreachable!("length checked"))
    }

    fn integers(&self, arguments: &[FrontendValue]) -> Result<[Int; 2], PrimitiveError> {
        let datums = self.datums::<2>(arguments)?;
        datums
            .map(|datum| match datum {
                Datum::Atom(CoreAtom::Integer(value)) => Ok(value),
                _ => Err(PrimitiveError::ExpectedInteger),
            })
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|_| unreachable!("array length preserved"))
    }

    fn integer_binary(
        &self,
        arguments: &[FrontendValue],
        operation: impl FnOnce(Int, Int) -> Int,
    ) -> Result<FrontendValue, PrimitiveError> {
        let [left, right] = self.integers(arguments)?;
        Ok(HostValue::Datum(Datum::Atom(CoreAtom::Integer(operation(
            left, right,
        )))))
    }
}

pub fn host_machine() -> CoreMachine<StandardPrimitives> {
    CoreMachine::new(StandardPrimitives)
}

/// Stateful proof-free frontend execution.
///
/// Definitions are lexical named closures. Recursive calls may diverge; fuel
/// exhaustion is an ordinary result and carries no ACL2 admission claim.
#[derive(Clone, Debug)]
pub struct HostSession {
    frontend: Frontend,
    environment: FrontendEnvironment,
    fuel: usize,
}

#[derive(Debug)]
pub enum HostSessionError {
    Lower(LowerError),
    Execute(ExecutionError<CoreMachineError<String, PrimitiveError>>),
    Machine(CoreMachineError<String, PrimitiveError>),
    ExpectedDefinition { index: usize },
    DefinitionDidNotProduceClosure,
}

impl Display for HostSessionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
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

impl core::error::Error for HostSessionError {}

impl HostSession {
    pub fn new(dialect: SurfaceDialect, fuel: usize) -> Self {
        Self {
            frontend: Frontend::new(dialect),
            environment: HostEnvironment::default(),
            fuel,
        }
    }

    pub fn environment(&self) -> &FrontendEnvironment {
        &self.environment
    }

    pub fn evaluate(&self, form: &SExpr) -> Result<FrontendValue, HostSessionError> {
        let expression = self.frontend.lower(form).map_err(HostSessionError::Lower)?;
        self.evaluate_core(&expression)
    }

    pub fn define(&mut self, form: &SExpr) -> Result<Option<String>, HostSessionError> {
        let Some((name, expression)) = self
            .frontend
            .definition(form)
            .map_err(HostSessionError::Lower)?
        else {
            return Ok(None);
        };
        let value = self.evaluate_core(&expression)?;
        if !matches!(value, HostValue::Closure(_)) {
            return Err(HostSessionError::DefinitionDidNotProduceClosure);
        }
        self.environment = self.environment.extend([(name.clone(), value)]);
        Ok(Some(name))
    }

    /// Atomically install a mutually recursive group of `define`, `label`, or
    /// `defun` forms.
    ///
    /// Every closure captures the same newly allocated lexical generation, so
    /// definitions may refer forward as well as backward within the group.
    pub fn define_group(&mut self, forms: &[SExpr]) -> Result<Vec<String>, HostSessionError> {
        let mut names = Vec::with_capacity(forms.len());
        let mut bindings = Vec::with_capacity(forms.len());
        for (index, form) in forms.iter().enumerate() {
            let Some((name, expression)) = self
                .frontend
                .definition(form)
                .map_err(HostSessionError::Lower)?
            else {
                return Err(HostSessionError::ExpectedDefinition { index });
            };
            names.push(name.clone());
            bindings.push((name, expression));
        }
        self.environment = host_machine()
            .bind_recursive(&self.environment, bindings)
            .map_err(HostSessionError::Machine)?;
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
    ) -> Result<FrontendValue, HostSessionError> {
        let trace = execute(
            &host_machine(),
            HostConfiguration::with_environment(expression.clone(), self.environment.clone()),
            self.fuel,
        )
        .map_err(HostSessionError::Execute)?;
        trace
            .end()
            .terminal_value()
            .cloned()
            .ok_or(HostSessionError::DefinitionDidNotProduceClosure)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_kernel_lisp::execute;

    fn one(source: &str) -> SExpr {
        crate::reader::read(source).unwrap().pop().unwrap()
    }

    fn run(dialect: SurfaceDialect, source: &str) -> FrontendValue {
        let expression = Frontend::new(dialect).lower(&one(source)).unwrap();
        let trace = execute(&host_machine(), HostConfiguration::initial(expression), 128).unwrap();
        trace.end().terminal_value().unwrap().clone()
    }

    #[test]
    fn sector_pairs_lower_to_the_common_core() {
        assert_eq!(
            run(SurfaceDialect::Sector, "(car (cons (quote head) ()))"),
            HostValue::Datum(Datum::Atom(CoreAtom::symbol("head")))
        );
    }

    #[test]
    fn scheme_lambda_let_and_exact_integers_share_the_machine() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(let ((twice (lambda (x) (+ x x)))) (twice 21))"
            ),
            HostValue::Datum(Datum::Atom(CoreAtom::Integer(Int::from(42))))
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
            HostValue::Datum(Datum::Atom(CoreAtom::symbol("t")))
        );
    }

    #[test]
    fn host_append_preserves_list_order() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(append (quote (a b)) (quote (c d)))"
            ),
            HostValue::Datum(Datum::list([
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
            HostValue::Datum(Datum::list([Datum::Atom(CoreAtom::symbol("tail"))]))
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
            HostValue::Datum(Datum::list([Datum::Atom(CoreAtom::symbol("value"))]))
        );
    }

    #[test]
    fn cond_is_derived_from_if_and_nil_truthiness() {
        assert_eq!(
            run(
                SurfaceDialect::Scheme,
                "(cond ((null? (quote (x))) 0) (else 1))"
            ),
            HostValue::Datum(Datum::Atom(CoreAtom::Integer(Int::from(1))))
        );
    }

    #[test]
    fn acl2_expression_fragment_uses_acl2_primitive_names() {
        assert_eq!(
            run(SurfaceDialect::Acl2Core, "(equal (+ 2 3) 5)"),
            HostValue::Datum(Datum::Atom(CoreAtom::symbol("t")))
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
            HostValue::Datum(Datum::Atom(CoreAtom::Integer(Int::from(120))))
        );
    }

    #[test]
    fn acl2_defun_shares_execution_but_not_admission() {
        let mut session = HostSession::new(SurfaceDialect::Acl2Core, 128);
        session.define(&one("(defun add1 (x) (+ x 1))")).unwrap();
        assert_eq!(
            session.evaluate(&one("(add1 41)")).unwrap(),
            HostValue::Datum(Datum::Atom(CoreAtom::Integer(Int::from(42))))
        );
    }
}

//! Common syntax shared by Lisp-family frontends.

/// Evaluation order is explicit rather than silently baked into “Lisp”.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EvaluationOrder {
    /// Evaluate operator and operands from left to right.
    ApplicativeLeftToRight,
    /// Evaluate operator and operands from right to left.
    ApplicativeRightToLeft,
    /// Do not prescribe an operand order. A relational backend may expose
    /// several successors.
    Relational,
}

/// An evaluation strategy selected by a concrete language.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Strategy {
    pub order: EvaluationOrder,
    /// Whether the dialect uses lexical rather than dynamic scope.
    pub lexical_scope: bool,
}

impl Strategy {
    pub const STRICT_LEXICAL: Self = Self {
        order: EvaluationOrder::ApplicativeLeftToRight,
        lexical_scope: true,
    };
}

/// A named parameter.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Parameter<S> {
    pub name: S,
}

impl<S> Parameter<S> {
    pub fn new(name: S) -> Self {
        Self { name }
    }
}

/// A lexical binding.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Binding<S, E> {
    pub name: S,
    pub value: E,
}

impl<S, E> Binding<S, E> {
    pub fn new(name: S, value: E) -> Self {
        Self { name, value }
    }
}

/// The common expression functor.
///
/// `D` is quoted/literal data and `P` is a dialect-specific primitive
/// identifier. Derived frontends may translate richer surface forms, macros,
/// ACL2 events, or Forsp combinators into this deliberately small core.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoreExpr<S, D, P> {
    Literal(D),
    Truth(bool),
    Variable(S),
    Quote(D),
    If {
        condition: Box<Self>,
        consequent: Box<Self>,
        alternative: Box<Self>,
    },
    Cond {
        clauses: Vec<(Self, Self)>,
    },
    /// Evaluate expressions from left to right and return the final value.
    ///
    /// The non-empty shape avoids assigning a dialect-independent value to an
    /// empty sequence. Frontends remain responsible for deciding whether an
    /// empty surface form is valid.
    Sequence {
        first: Box<Self>,
        rest: Vec<Self>,
    },
    Lambda {
        /// A name enables direct recursive calls without requiring a global
        /// world or making recursion total.
        name: Option<S>,
        parameters: Vec<Parameter<S>>,
        /// Optional binding for all arguments after `parameters`, represented
        /// as a proper list in the backend's shared S-expression carrier.
        rest: Option<Parameter<S>>,
        body: Box<Self>,
    },
    Apply {
        operator: Box<Self>,
        arguments: Vec<Self>,
    },
    /// Apply a function to explicit prefix arguments followed by the values in
    /// a runtime proper list.
    ApplyList {
        operator: Box<Self>,
        arguments: Vec<Self>,
        tail: Box<Self>,
    },
    Let {
        bindings: Vec<Binding<S, Self>>,
        body: Box<Self>,
    },
    /// A mutually recursive lexical group.
    ///
    /// Concrete semantics may restrict initializers. The host backend accepts
    /// lambdas only, avoiding unspecified reads of uninitialized cells.
    LetRec {
        bindings: Vec<Binding<S, Self>>,
        body: Box<Self>,
    },
    Primitive {
        operator: P,
        arguments: Vec<Self>,
    },
    /// A primitive procedure as a first-class callable value.
    PrimitiveValue(P),
    /// The first-class runtime-list application procedure.
    ApplyListProcedure,
}

/// One complete layer of the common Lisp-expression functor.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoreExprLayer<S, D, P, E> {
    Literal(D),
    Truth(bool),
    Variable(S),
    Quote(D),
    If {
        condition: E,
        consequent: E,
        alternative: E,
    },
    Cond {
        clauses: Vec<(E, E)>,
    },
    Sequence {
        first: E,
        rest: Vec<E>,
    },
    Lambda {
        name: Option<S>,
        parameters: Vec<Parameter<S>>,
        rest: Option<Parameter<S>>,
        body: E,
    },
    Apply {
        operator: E,
        arguments: Vec<E>,
    },
    ApplyList {
        operator: E,
        arguments: Vec<E>,
        tail: E,
    },
    Let {
        bindings: Vec<Binding<S, E>>,
        body: E,
    },
    LetRec {
        bindings: Vec<Binding<S, E>>,
        body: E,
    },
    Primitive {
        operator: P,
        arguments: Vec<E>,
    },
    PrimitiveValue(P),
    ApplyListProcedure,
}

impl<S, D, P, E> CoreExprLayer<S, D, P, E> {
    /// The functorial action on recursive expression positions.
    pub fn map_recursive<F>(self, mut map: impl FnMut(E) -> F) -> CoreExprLayer<S, D, P, F> {
        match self {
            Self::Literal(datum) => CoreExprLayer::Literal(datum),
            Self::Truth(value) => CoreExprLayer::Truth(value),
            Self::Variable(symbol) => CoreExprLayer::Variable(symbol),
            Self::Quote(datum) => CoreExprLayer::Quote(datum),
            Self::If {
                condition,
                consequent,
                alternative,
            } => CoreExprLayer::If {
                condition: map(condition),
                consequent: map(consequent),
                alternative: map(alternative),
            },
            Self::Cond { clauses } => CoreExprLayer::Cond {
                clauses: clauses
                    .into_iter()
                    .map(|(condition, body)| (map(condition), map(body)))
                    .collect(),
            },
            Self::Sequence { first, rest } => CoreExprLayer::Sequence {
                first: map(first),
                rest: rest.into_iter().map(&mut map).collect(),
            },
            Self::Lambda {
                name,
                parameters,
                rest,
                body,
            } => CoreExprLayer::Lambda {
                name,
                parameters,
                rest,
                body: map(body),
            },
            Self::Apply {
                operator,
                arguments,
            } => CoreExprLayer::Apply {
                operator: map(operator),
                arguments: arguments.into_iter().map(&mut map).collect(),
            },
            Self::ApplyList {
                operator,
                arguments,
                tail,
            } => CoreExprLayer::ApplyList {
                operator: map(operator),
                arguments: arguments.into_iter().map(&mut map).collect(),
                tail: map(tail),
            },
            Self::Let { bindings, body } => CoreExprLayer::Let {
                bindings: bindings
                    .into_iter()
                    .map(|binding| Binding::new(binding.name, map(binding.value)))
                    .collect(),
                body: map(body),
            },
            Self::LetRec { bindings, body } => CoreExprLayer::LetRec {
                bindings: bindings
                    .into_iter()
                    .map(|binding| Binding::new(binding.name, map(binding.value)))
                    .collect(),
                body: map(body),
            },
            Self::Primitive {
                operator,
                arguments,
            } => CoreExprLayer::Primitive {
                operator,
                arguments: arguments.into_iter().map(&mut map).collect(),
            },
            Self::PrimitiveValue(primitive) => CoreExprLayer::PrimitiveValue(primitive),
            Self::ApplyListProcedure => CoreExprLayer::ApplyListProcedure,
        }
    }
}

impl<S, D, P> CoreExpr<S, D, P> {
    pub fn into_layer(self) -> CoreExprLayer<S, D, P, Self> {
        match self {
            Self::Literal(datum) => CoreExprLayer::Literal(datum),
            Self::Truth(value) => CoreExprLayer::Truth(value),
            Self::Variable(symbol) => CoreExprLayer::Variable(symbol),
            Self::Quote(datum) => CoreExprLayer::Quote(datum),
            Self::If {
                condition,
                consequent,
                alternative,
            } => CoreExprLayer::If {
                condition: *condition,
                consequent: *consequent,
                alternative: *alternative,
            },
            Self::Cond { clauses } => CoreExprLayer::Cond { clauses },
            Self::Sequence { first, rest } => CoreExprLayer::Sequence {
                first: *first,
                rest,
            },
            Self::Lambda {
                name,
                parameters,
                rest,
                body,
            } => CoreExprLayer::Lambda {
                name,
                parameters,
                rest,
                body: *body,
            },
            Self::Apply {
                operator,
                arguments,
            } => CoreExprLayer::Apply {
                operator: *operator,
                arguments,
            },
            Self::ApplyList {
                operator,
                arguments,
                tail,
            } => CoreExprLayer::ApplyList {
                operator: *operator,
                arguments,
                tail: *tail,
            },
            Self::Let { bindings, body } => CoreExprLayer::Let {
                bindings,
                body: *body,
            },
            Self::LetRec { bindings, body } => CoreExprLayer::LetRec {
                bindings,
                body: *body,
            },
            Self::Primitive {
                operator,
                arguments,
            } => CoreExprLayer::Primitive {
                operator,
                arguments,
            },
            Self::PrimitiveValue(primitive) => CoreExprLayer::PrimitiveValue(primitive),
            Self::ApplyListProcedure => CoreExprLayer::ApplyListProcedure,
        }
    }

    pub fn from_layer(layer: CoreExprLayer<S, D, P, Self>) -> Self {
        match layer {
            CoreExprLayer::Literal(datum) => Self::Literal(datum),
            CoreExprLayer::Truth(value) => Self::Truth(value),
            CoreExprLayer::Variable(symbol) => Self::Variable(symbol),
            CoreExprLayer::Quote(datum) => Self::Quote(datum),
            CoreExprLayer::If {
                condition,
                consequent,
                alternative,
            } => Self::If {
                condition: Box::new(condition),
                consequent: Box::new(consequent),
                alternative: Box::new(alternative),
            },
            CoreExprLayer::Cond { clauses } => Self::Cond { clauses },
            CoreExprLayer::Sequence { first, rest } => Self::Sequence {
                first: Box::new(first),
                rest,
            },
            CoreExprLayer::Lambda {
                name,
                parameters,
                rest,
                body,
            } => Self::Lambda {
                name,
                parameters,
                rest,
                body: Box::new(body),
            },
            CoreExprLayer::Apply {
                operator,
                arguments,
            } => Self::Apply {
                operator: Box::new(operator),
                arguments,
            },
            CoreExprLayer::ApplyList {
                operator,
                arguments,
                tail,
            } => Self::ApplyList {
                operator: Box::new(operator),
                arguments,
                tail: Box::new(tail),
            },
            CoreExprLayer::Let { bindings, body } => Self::Let {
                bindings,
                body: Box::new(body),
            },
            CoreExprLayer::LetRec { bindings, body } => Self::LetRec {
                bindings,
                body: Box::new(body),
            },
            CoreExprLayer::Primitive {
                operator,
                arguments,
            } => Self::Primitive {
                operator,
                arguments,
            },
            CoreExprLayer::PrimitiveValue(primitive) => Self::PrimitiveValue(primitive),
            CoreExprLayer::ApplyListProcedure => Self::ApplyListProcedure,
        }
    }
}

/// One-layer observation of an opaque Lisp-expression representation.
pub trait LispExpression {
    type Symbol: Clone;
    type Datum: Clone;
    type Primitive: Clone;
    type Expr: Clone;
    type Error;

    fn view(
        &self,
        expression: &Self::Expr,
    ) -> Result<CoreExprLayer<Self::Symbol, Self::Datum, Self::Primitive, Self::Expr>, Self::Error>;
}

/// Construction capability for a backend-specific Lisp syntax carrier.
///
/// This is intentionally suitable for a future WIT interface: it consists of
/// constructors over opaque associated resources, without Rust closures or
/// theorem-producing callbacks.
pub trait LispSyntax {
    type Symbol: Clone;
    type Datum: Clone;
    type Primitive: Clone;
    type Expr: Clone;
    type Error;

    fn literal(&self, datum: Self::Datum) -> Result<Self::Expr, Self::Error>;
    fn truth(&self, value: bool) -> Result<Self::Expr, Self::Error>;
    fn variable(&self, symbol: Self::Symbol) -> Result<Self::Expr, Self::Error>;
    fn quote(&self, datum: Self::Datum) -> Result<Self::Expr, Self::Error>;
    fn if_then_else(
        &self,
        condition: Self::Expr,
        consequent: Self::Expr,
        alternative: Self::Expr,
    ) -> Result<Self::Expr, Self::Error>;
    fn cond(&self, clauses: Vec<(Self::Expr, Self::Expr)>) -> Result<Self::Expr, Self::Error>;
    fn sequence(&self, first: Self::Expr, rest: Vec<Self::Expr>)
    -> Result<Self::Expr, Self::Error>;
    fn lambda(
        &self,
        name: Option<Self::Symbol>,
        parameters: Vec<Self::Symbol>,
        rest: Option<Self::Symbol>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error>;
    fn apply(
        &self,
        operator: Self::Expr,
        arguments: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error>;
    fn apply_list(
        &self,
        operator: Self::Expr,
        arguments: Vec<Self::Expr>,
        tail: Self::Expr,
    ) -> Result<Self::Expr, Self::Error>;
    fn let_bind(
        &self,
        bindings: Vec<(Self::Symbol, Self::Expr)>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error>;
    fn let_rec(
        &self,
        bindings: Vec<(Self::Symbol, Self::Expr)>,
        body: Self::Expr,
    ) -> Result<Self::Expr, Self::Error>;
    fn primitive(
        &self,
        operator: Self::Primitive,
        arguments: Vec<Self::Expr>,
    ) -> Result<Self::Expr, Self::Error>;
    fn primitive_value(&self, operator: Self::Primitive) -> Result<Self::Expr, Self::Error>;
    fn apply_list_procedure(&self) -> Result<Self::Expr, Self::Error>;
}

/// Policy supplied by a concrete Lisp frontend.
pub trait LispDialect {
    type Symbol;
    type Primitive;

    fn strategy(&self) -> Strategy;
    fn is_false_symbol(&self, symbol: &Self::Symbol) -> bool;
    fn primitive_arity(&self, primitive: &Self::Primitive) -> Option<usize>;
}

#[cfg(test)]
mod tests {
    use super::*;

    type Expr = CoreExpr<&'static str, &'static str, &'static str>;

    fn variable(name: &'static str) -> Expr {
        CoreExpr::Variable(name)
    }

    #[test]
    fn every_core_expression_round_trips_through_one_functor_layer() {
        let expressions = vec![
            CoreExpr::Literal("literal"),
            CoreExpr::Truth(true),
            variable("variable"),
            CoreExpr::Quote("quoted"),
            CoreExpr::If {
                condition: Box::new(variable("condition")),
                consequent: Box::new(variable("consequent")),
                alternative: Box::new(variable("alternative")),
            },
            CoreExpr::Cond {
                clauses: vec![(variable("condition"), variable("body"))],
            },
            CoreExpr::Sequence {
                first: Box::new(variable("first")),
                rest: vec![variable("rest")],
            },
            CoreExpr::Lambda {
                name: Some("function"),
                parameters: vec![Parameter::new("parameter")],
                rest: Some(Parameter::new("rest")),
                body: Box::new(variable("body")),
            },
            CoreExpr::Apply {
                operator: Box::new(variable("operator")),
                arguments: vec![variable("argument")],
            },
            CoreExpr::ApplyList {
                operator: Box::new(variable("operator")),
                arguments: vec![variable("argument")],
                tail: Box::new(variable("tail")),
            },
            CoreExpr::Let {
                bindings: vec![Binding::new("name", variable("value"))],
                body: Box::new(variable("body")),
            },
            CoreExpr::LetRec {
                bindings: vec![Binding::new("name", variable("value"))],
                body: Box::new(variable("body")),
            },
            CoreExpr::Primitive {
                operator: "primitive",
                arguments: vec![variable("argument")],
            },
            CoreExpr::PrimitiveValue("primitive"),
            CoreExpr::ApplyListProcedure,
        ];

        for expression in expressions {
            assert_eq!(
                CoreExpr::from_layer(expression.clone().into_layer()),
                expression
            );
        }
    }
}

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

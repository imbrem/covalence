//! Abstract syntax for the surface language (**DESIGN SKETCH**).
//!
//! Every node here corresponds to a *pure* S-expression: there is **no
//! infix syntax**. The prose sugar used in [`docs/surface-syntax.md`] —
//! `'a -> 'b`, `none : option 'a`, `lhs => rhs` — is purely a convenience
//! for human readers; the real, parseable forms are the `#`-headed
//! builtins captured here (`(#fn 'a 'b)`, `(#sig none (option 'a))`,
//! `(#rw lhs rhs)`).
//!
//! Three lexical name classes (see [`Name::class`]):
//!
//! - **builtins** start with `#` — every reserved keyword of the language
//!   (directive heads *and* term/type form heads): `#theory`, `#fn`,
//!   `#lam`, `#eq`, …
//! - **type variables** start with `'` — `'a`, `'b`, …
//! - everything else is an ordinary **name**: either a *dotted catalogue*
//!   reference into the `defs/` catalogue (`coprod.case`, `option.some`,
//!   `unit.nil`) or a *local* name (a bound variable, or a symbol the
//!   surrounding `#theory` declares — `option`, `some`, `e`, `f`).
//!
//! [`docs/surface-syntax.md`]: ../../../../docs/surface-syntax.md

use bytes::Bytes;
use covalence_types::Int;
use smol_str::SmolStr;

// ============================================================================
// Names
// ============================================================================

/// A surface identifier, classified by its lexical shape (see
/// [`Name::class`]). Stored verbatim — the leading `#` / `'` (if any) is
/// kept so the token round-trips.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name(pub SmolStr);

/// The lexical class a [`Name`] falls into. The class is a pure function
/// of the spelling, so the parser can route a token without any scope
/// information; binding resolution (is this *local* name a bound variable
/// or a theory-declared constant?) is the elaborator's job, later.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NameClass {
    /// Starts with `#` — a reserved builtin keyword.
    Builtin,
    /// Starts with `'` — a type variable.
    TyVar,
    /// Contains a `.` and is not a builtin — a dotted reference into the
    /// `defs/` catalogue (`nat.add`, `coprod.case`).
    Catalogue,
    /// Anything else — a bound variable or a locally-declared symbol.
    Local,
}

impl Name {
    /// Classify this name purely from its spelling.
    pub fn class(&self) -> NameClass {
        let s = self.0.as_str();
        if s.starts_with('#') {
            NameClass::Builtin
        } else if s.starts_with('\'') {
            NameClass::TyVar
        } else if s.contains('.') {
            NameClass::Catalogue
        } else {
            NameClass::Local
        }
    }

    /// View as a string slice.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

// ============================================================================
// Kinds & types
// ============================================================================

/// A **kind** classifies type formers. The only base kind is `#ty` (the
/// kind of proper types); a type former such as `option` has kind
/// `(#fn #ty #ty)`.
///
/// Kinds appear only in `#tydecl`. In the sketch's `(#tydecl (option 'a
/// #ty))` the `'a` is a placeholder type parameter and the trailing `#ty`
/// is the *result* kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// `#ty` — the kind of proper types.
    Ty,
    /// `(#fn k1 k2 … kn)` — the kind of an `n-1`-ary type former. Curried,
    /// like [`Ty::Fn`].
    Fn(Vec<Kind>),
}

/// A surface **type** expression. Pure S-expressions throughout: the
/// arrow `'a -> 'b` is written `(#fn 'a 'b)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    /// `'a` — a type variable.
    Var(SmolStr),
    /// `#prop` — the type of propositions (the kernel's `prop`).
    Prop,
    /// `#bytes` — the type of `#blob` literals (the kernel's `bytes`).
    Bytes,
    /// `(#fn A B … Z)` — the curried function type `A -> B -> … -> Z`.
    /// Always at least two elements.
    Fn(Vec<Ty>),
    /// `(F A …)` — application of a declared or catalogue type former
    /// `F` (e.g. `(option 'a)`, `(coprod 'a unit)`). A bare type-former
    /// name with no arguments is `App { head, args: [] }`.
    App { head: Name, args: Vec<Ty> },
}

// ============================================================================
// The term sublanguage
// ============================================================================

/// The **term sublanguage** — a simply-typed lambda calculus over the
/// kernel's two logical primitives (`=`, `ε`) and the `defs/` catalogue.
///
/// This is the fragment in which `#def` bodies and the leaves of `(#by …)`
/// proof scripts are written. It is deliberately *small and total*: it has
/// variables, application, lambda, the kernel primitives, and the newtype
/// coercions — nothing with its own operational semantics (reduction is
/// the kernel's job; see `docs/surface-syntax.md` §1.1).
///
/// **Why it stands alone.** This sublanguage is the candidate we may
/// eventually lift *into the TCB* as the native input format for writing
/// `defs/` — replacing the hand-written `Term::app` / `Term::abs` plumbing
/// in `covalence-core`. Keeping it as a closed, clearly-delimited grammar
/// (rather than letting it bleed into the directive/proof layer) is what
/// makes that move tractable: only these constructors would need a
/// trusted elaboration into kernel `Term`s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A bare symbol: a bound variable, a theory-local constant, or a
    /// dotted catalogue reference (`coprod.case`). Which one it is is the
    /// elaborator's call (it depends on scope); the parser only records
    /// the [`Name`].
    Var(Name),
    /// `(f x y …)` — curried application, `((f x) y) …`. `args` is always
    /// non-empty (a lone `(f)` parses as `Var(f)`).
    App { head: Box<Term>, args: Vec<Term> },
    /// `(#lam x BODY)` or `(#lam (x A) BODY)` — lambda abstraction binding
    /// `x` (optionally type-ascribed). The one non-trivial binder of the
    /// sublanguage, and the reason it can express the `defs/` bodies at
    /// all.
    Lam {
        /// The bound variable name.
        param: SmolStr,
        /// Its type, if ascribed (`(#lam (x A) …)`).
        ty: Option<Ty>,
        /// The body, with `param` in scope.
        body: Box<Term>,
    },
    /// `(#eq a b)` — the kernel's primitive equality `=`.
    Eq(Box<Term>, Box<Term>),
    /// `(#sel (x A) P)` — Hilbert choice `ε`: "some `x : A` satisfying
    /// `P`". The kernel's other primitive (`TermKind::Select`).
    Select {
        /// The chosen variable's name.
        param: SmolStr,
        /// Its type, if ascribed.
        ty: Option<Ty>,
        /// The predicate, with `param` in scope.
        pred: Box<Term>,
    },
    /// `(#abs SPEC ARGS BODY)` — the carrier→wrapper coercion of a
    /// `TypeSpec` (kernel `Term::spec_abs`). `SPEC` names the spec,
    /// `ARGS` its type arguments.
    Abs {
        /// The `TypeSpec` being wrapped into.
        spec: Name,
        /// The spec's type arguments.
        args: Vec<Ty>,
        /// The carrier term.
        body: Box<Term>,
    },
    /// `(#rep SPEC ARGS BODY)` — the wrapper→carrier coercion (kernel
    /// `Term::spec_rep`). The inverse of [`Term::Abs`].
    Rep {
        /// The `TypeSpec` being unwrapped.
        spec: Name,
        /// The spec's type arguments.
        args: Vec<Ty>,
        /// The wrapper term.
        body: Box<Term>,
    },
    /// An integer literal (kernel `TermKind::Int`). Written as a bare
    /// numeral atom.
    Int(Int),
    /// `(#blob …)` — a byte-string literal (kernel `TermKind::Blob`).
    Blob(Bytes),
}

// ============================================================================
// Directives
// ============================================================================

/// A top-level **directive** — the unit a surface file is a sequence of.
/// Each is a pure S-expression headed by a `#`-keyword.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Directive {
    /// `(#theory NAME BODY…)` — open a named theory scope.
    Theory {
        /// The theory's name.
        name: SmolStr,
        /// The directives nested inside it.
        body: Vec<Directive>,
    },
    /// `(#tydecl ITEM…)` — declare type formers and their kinds.
    TyDecl(Vec<TyDeclItem>),
    /// `(#decl SIG…)` — declare constants with their signatures.
    Decl(Vec<Sig>),
    /// `(#clause RULE…)` — an equational / Horn constraint: a
    /// **disjunction** of [`Rule`]s, at least one of which must hold (see
    /// `docs/surface-syntax.md` §4.1 for the positional binding
    /// convention).
    Clause(Vec<Rule>),
    /// `(#def …)` — a tight definition with a body.
    Def(Def),
    /// `(#thm …)` — a named theorem and its proof.
    Thm(ThmDecl),
    /// `(#import …)` — pull in another theory / fragment.
    Import(Import),
}

/// One item of a `#tydecl`: a type former with its parameters and result
/// kind, e.g. `(option 'a #ty)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyDeclItem {
    /// The type former's name.
    pub name: SmolStr,
    /// Its declared type parameters (`'a`, …).
    pub params: Vec<SmolStr>,
    /// The result kind (`#ty` in `(option 'a #ty)`).
    pub result: Kind,
}

/// One signature in a `#decl`: `(#sig NAME TYPE)` — the pure form of the
/// sugar `NAME : TYPE`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sig {
    /// The constant's name.
    pub name: SmolStr,
    /// Its type.
    pub ty: Ty,
}

/// A single rewrite rule `(#rw LHS RHS)` — the pure form of the sugar
/// `lhs => rhs`, asserting `lhs = rhs`. Variable binding is *positional*:
/// a variable on the LHS is universally bound; one appearing only on the
/// RHS is existentially bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    /// The left-hand pattern.
    pub lhs: Term,
    /// The right-hand pattern.
    pub rhs: Term,
}

/// A tight definition `(#def NAME SORT BODY)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Def {
    /// The defined symbol.
    pub name: SmolStr,
    /// Whether this defines a type or a term, with the relevant
    /// signature.
    pub sort: DefSort,
    /// The definition body.
    pub body: DefBody,
}

/// The sort tag of a [`Def`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefSort {
    /// `(#ty 'a …)` — a type definition with the given type parameters.
    Type {
        /// The type parameters.
        params: Vec<SmolStr>,
    },
    /// `(#term TYPE)` — a term definition of the given type.
    Term(Ty),
}

/// The body of a [`Def`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefBody {
    /// `(#newtype CARRIER)` — a newtype over the given carrier type.
    Newtype(Ty),
    /// A term-sublanguage body (for term definitions).
    Term(Term),
}

/// A named theorem `(#thm NAME STATEMENT (#by …))`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThmDecl {
    /// The theorem's name.
    pub name: SmolStr,
    /// What it states.
    pub statement: Statement,
    /// Its proof script.
    pub proof: Proof,
}

/// What a [`ThmDecl`] asserts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    /// `(#spec NAME)` — discharge a named spec obligation from a
    /// `#clause`.
    Spec(Name),
    /// `(#concl TERM)` with optional `(#hyps TERM…)` — an explicit
    /// sequent.
    Sequent {
        /// The hypotheses (empty if no `#hyps`).
        hyps: Vec<Term>,
        /// The conclusion.
        concl: Term,
    },
}

/// A proof script `(#by STEP…)`.
///
/// The tactic vocabulary (LCF-style combinators naming the kernel rules —
/// see `docs/surface-syntax.md` §5) is a **later layer**; for now the
/// sketch keeps the raw step S-expressions unparsed so the directive
/// grammar can stabilize first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    /// The raw `#by` steps, pending a tactic grammar.
    pub steps: Vec<covalence_sexp::SExpr>,
}

/// An `(#import …)` dependency edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    /// What is imported.
    pub target: ImportTarget,
}

/// The resolution target of an [`Import`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportTarget {
    /// By name, resolved within the file (the only mode today).
    Name(SmolStr),
    /// By content hash — a `covalence-store` content-address. The
    /// endgame (`docs/surface-syntax.md` §7); not yet resolvable.
    Hash(SmolStr),
}

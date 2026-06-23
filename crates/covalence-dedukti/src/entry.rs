//! Top-level entries of a Dedukti `.dk` source: declarations, definitions,
//! theorems, rewrite rules, and `#`-commands — collected into a [`Signature`].

use crate::term::{Ref, Symbol, Term};

/// A typed parameter `(name : ty)` of a declaration/definition/theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    /// The parameter name.
    pub name: Symbol,
    /// The parameter type.
    pub ty: Term,
}

/// A rewrite-rule context binding: `name` or `name : ty` inside `[ … ]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextVar {
    /// The pattern variable name.
    pub name: Symbol,
    /// Its optional type annotation.
    pub ty: Option<Term>,
}

/// How a [`Declaration`] introduces its symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclKind {
    /// A plain static constant: `name : ty.`
    Static,
    /// An `injective name : ty.` declaration (Dedukti's injectivity hint).
    Injective,
    /// An associative-commutative symbol: `defac name [operand_ty].` Here the
    /// declaration's `ty` is the *operand* type written in the brackets.
    Ac,
    /// An associative-commutative symbol with a neutral element:
    /// `defacu name [operand_ty, neutral].` The declaration's `ty` is the
    /// operand type; the [`Term`] is the neutral element.
    AcU(Box<Term>),
}

/// A symbol declaration: `name params : ty.` (optionally `injective`, or an
/// AC/ACU declaration). It introduces a constant without a definitional body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    /// The declared symbol's name.
    pub name: Symbol,
    /// Curried parameters written before the `:` (empty for AC/ACU).
    pub params: Vec<Param>,
    /// The declared type (the operand type for AC/ACU — see [`DeclKind`]).
    pub ty: Term,
    /// How the symbol is introduced.
    pub kind: DeclKind,
}

/// A definition: `def name params [: ty] [:= body].` A definition may omit its
/// body (a *definable* symbol declared without a definiens) or its type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    /// The defined symbol's name.
    pub name: Symbol,
    /// Curried parameters written before the `:`/`:=`.
    pub params: Vec<Param>,
    /// The optional declared type.
    pub ty: Option<Term>,
    /// The optional definiens (`None` for a bodyless `def name : ty.`).
    pub body: Option<Term>,
}

/// A theorem: `thm name params [: ty] := body.` — an *opaque* definition (the
/// body is a proof term that does not unfold during conversion).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Theorem {
    /// The theorem's name.
    pub name: Symbol,
    /// Curried parameters.
    pub params: Vec<Param>,
    /// The optional statement type.
    pub ty: Option<Term>,
    /// The proof term.
    pub body: Term,
}

/// A rewrite rule `[ctx] lhs --> rhs`, optionally named (`{name} [ctx] …`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteRule {
    /// The optional rule name from a leading `{name}`.
    pub name: Option<Ref>,
    /// The pattern-variable context `[ … ]`.
    pub context: Vec<ContextVar>,
    /// The left-hand side pattern.
    pub lhs: Term,
    /// The right-hand side replacement.
    pub rhs: Term,
}

/// What a `#CHECK`/`#ASSERT` family command claims about a term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Claim {
    /// `term : ty` — the term has the given type.
    HasType(Term, Term),
    /// `lhs == rhs` — the two terms are convertible.
    Convertible(Term, Term),
}

/// A `#`-prefixed command / directive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// `#NAME module.` — declare the current module's name.
    Name(Symbol),
    /// `#REQUIRE module.` — load another module.
    Require(Symbol),
    /// `#EVAL [config] term.` — evaluate a term (to normal form).
    Eval {
        /// The optional `[config]` (raw, e.g. `SNF`, `WHNF`, `N`), unparsed.
        config: Option<String>,
        /// The term to evaluate.
        term: Term,
    },
    /// `#INFER [config] term.` — infer a term's type.
    Infer {
        /// The optional `[config]` (raw), unparsed.
        config: Option<String>,
        /// The term whose type to infer.
        term: Term,
    },
    /// The `#CHECK` / `#CHECKNOT` / `#ASSERT` / `#ASSERTNOT` family.
    Check {
        /// `true` for the `#ASSERT*` variants (fail the run on mismatch),
        /// `false` for `#CHECK*` (report only).
        assert: bool,
        /// `true` for the `…NOT` variants (the claim is expected to *fail*).
        negated: bool,
        /// The claim being checked.
        claim: Claim,
    },
    /// `#PRINT "string".`
    Print(String),
    /// `#GDT name.` — dump a symbol's decision tree (a debugging directive).
    Gdt(Ref),
    /// Any other / future `#`-directive, captured by name (its arguments are
    /// skipped up to the terminating `.`).
    Other(Symbol),
}

/// A top-level entry of a `.dk` source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry {
    /// A symbol declaration (`name : ty.`, `injective …`, `defac …`, `defacu …`).
    Declaration(Declaration),
    /// A `def …` definition.
    Definition(Definition),
    /// A `thm …` theorem.
    Theorem(Theorem),
    /// One or more rewrite rules sharing a terminating `.`.
    Rules(Vec<RewriteRule>),
    /// A `#`-command.
    Command(Command),
}

/// A parsed `.dk` source: its entries in source order.
///
/// This is the faithful syntactic image of a module — no scope resolution, type
/// checking, or rewriting has been performed (those are deferred; see the crate
/// `SKELETONS.md`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Signature {
    /// The entries in source order.
    pub entries: Vec<Entry>,
}

impl Signature {
    /// The module name from the first `#NAME` command, if any.
    pub fn module_name(&self) -> Option<&Symbol> {
        self.entries.iter().find_map(|e| match e {
            Entry::Command(Command::Name(n)) => Some(n),
            _ => None,
        })
    }

    /// Iterate over the symbol declarations.
    pub fn declarations(&self) -> impl Iterator<Item = &Declaration> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Declaration(d) => Some(d),
            _ => None,
        })
    }

    /// Iterate over the definitions.
    pub fn definitions(&self) -> impl Iterator<Item = &Definition> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Definition(d) => Some(d),
            _ => None,
        })
    }

    /// Iterate over the theorems.
    pub fn theorems(&self) -> impl Iterator<Item = &Theorem> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Theorem(t) => Some(t),
            _ => None,
        })
    }

    /// Iterate over every rewrite rule (flattening grouped rules).
    pub fn rules(&self) -> impl Iterator<Item = &RewriteRule> {
        self.entries.iter().flat_map(|e| match e {
            Entry::Rules(rs) => rs.as_slice(),
            _ => &[],
        })
    }

    /// Iterate over the `#`-commands.
    pub fn commands(&self) -> impl Iterator<Item = &Command> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Command(c) => Some(c),
            _ => None,
        })
    }

    /// The names introduced by declarations, definitions, and theorems, in
    /// source order (rewrite rules and commands introduce no names).
    pub fn symbol_names(&self) -> impl Iterator<Item = &Symbol> {
        self.entries.iter().filter_map(|e| match e {
            Entry::Declaration(d) => Some(&d.name),
            Entry::Definition(d) => Some(&d.name),
            Entry::Theorem(t) => Some(&t.name),
            _ => None,
        })
    }
}

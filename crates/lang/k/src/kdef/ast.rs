//! Plain-data AST for the **`.k` source** grammar fragment — the human-written
//! K definition language, *not* KORE (that is [`crate::ast`]).
//!
//! We model exactly the `syntax`-declaration fragment needed to read the
//! *grammar* of a simple K-tutorial language (LAMBDA, IMP): modules, imports,
//! `requires`, and `syntax Sort ::= …` productions (terminals, non-terminals,
//! `|` alternatives, `>` priority blocks, `[attr]` lists, `List{S,"sep"}`).
//! Non-`syntax` sentences (`rule`/`context`/`configuration`/`claim`) are counted
//! but not modelled — this frontend reads grammar, not semantics.
//!
//! Grammar surface verified against the K user manual + k-tutorial (see
//! `notes/vibes/k/research/`): `>` separates priority blocks with the *left*
//! block binding tighter; terminals are double-quoted; non-terminals are bare
//! sort names; a lone non-terminal RHS is a subsort/injection.

use smol_str::SmolStr;

/// A whole `.k` file: `require*` then `module*`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KDefinition {
    /// `requires "file"` paths, in order (also the legacy `require` spelling).
    pub requires: Vec<String>,
    pub modules: Vec<KModule>,
}

/// `module NAME [attrs] import* sentence* endmodule`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KModule {
    pub name: SmolStr,
    pub attrs: Vec<Attr>,
    pub imports: Vec<Import>,
    /// The `syntax` declarations, in source order.
    pub syntax: Vec<SyntaxDecl>,
    /// The `rule` declarations we could parse (the prefix-term fragment).
    pub rules: Vec<KRule>,
    /// How many sentences were *skipped* (`context`/`configuration`/`claim`, or a
    /// `syntax`/`rule` we couldn't parse) — this frontend reads a fragment only.
    pub skipped_sentences: usize,
}

/// A `rule LHS => RHS [requires REQ] [ATTRS]` — the minimal prefix-term fragment
/// (no cells, no `~>`, no nested/local `=>`). See the parser for what is
/// deferred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KRule {
    pub lhs: RuleTerm,
    pub rhs: RuleTerm,
    pub requires: Option<RuleTerm>,
    pub attrs: Vec<Attr>,
}

/// A first-order **rule/program term** in the prefix fragment: a constructor
/// application `sym(args…)` (nullary written `sym()`), or a variable `X[:Sort]`.
/// Bare identifiers are variables; constructors are always applied (even
/// nullary) — the convention that lets us read rules without full sort analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuleTerm {
    /// Constructor application `sym(args…)` — `args` empty for a nullary ctor.
    App { sym: SmolStr, args: Vec<RuleTerm> },
    /// A variable `name` with an optional sort annotation.
    Var { name: SmolStr, sort: Option<Sort> },
}

impl RuleTerm {
    /// A nullary constructor `sym()`.
    pub fn con(sym: impl Into<SmolStr>) -> RuleTerm {
        RuleTerm::App {
            sym: sym.into(),
            args: Vec::new(),
        }
    }
    /// A variable `name`.
    pub fn var(name: impl Into<SmolStr>) -> RuleTerm {
        RuleTerm::Var {
            name: name.into(),
            sort: None,
        }
    }
}

/// `imports [public|private] NAME`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    pub name: SmolStr,
    /// `Some(true)` = `public`, `Some(false)` = `private`, `None` = default.
    pub public: Option<bool>,
}

/// One `syntax Sort …` sentence. Either a bare sort declaration (`blocks`
/// empty), a production declaration (`Sort ::= block > block …`), or a
/// syntactic-list sugar (`Sort ::= List{Elem,"sep"}`, captured as [`list`]).
///
/// [`SyntaxDecl::list`]: SyntaxDecl::list
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxDecl {
    /// The result sort being defined/extended.
    pub sort: Sort,
    /// Priority blocks, tightest-binding first (`>`-separated in source). Empty
    /// for a bare `syntax Sort [attrs]` sort declaration.
    pub blocks: Vec<PriorityBlock>,
    /// `Some(_)` iff this declaration is a `List{…}`/`NeList{…}` sugar.
    pub list: Option<ListDecl>,
    /// Attributes on a bare sort declaration (`syntax Foo [attr]`).
    pub attrs: Vec<Attr>,
}

/// A `List{Elem,"sep"}` (or `NeList{…}`) syntactic-list production.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListDecl {
    /// `true` for `NeList` (non-empty), `false` for `List` (possibly empty).
    pub non_empty: bool,
    /// The element sort.
    pub elem: Sort,
    /// The separator terminal (may be `""`).
    pub sep: String,
    pub attrs: Vec<Attr>,
}

/// A `|`-joined group of same-priority productions, optionally tagged with a
/// block-level associativity (`left:`/`right:`/`non-assoc:`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PriorityBlock {
    pub assoc: Option<Assoc>,
    pub prods: Vec<Production>,
}

/// Block/production associativity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    NonAssoc,
}

/// One production: a sequence of items plus its attribute list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Production {
    pub items: Vec<ProdItem>,
    pub attrs: Vec<Attr>,
}

impl Production {
    /// A **subsort/injection** production: exactly one non-terminal item and
    /// nothing else (e.g. `syntax Exp ::= Val`).
    pub fn subsort_of(&self) -> Option<&Sort> {
        match self.items.as_slice() {
            [ProdItem::NonTerminal { sort, .. }] => Some(sort),
            _ => None,
        }
    }

    /// Whether this production is marked `[bracket]` (a grouping production that
    /// builds no AST node).
    pub fn is_bracket(&self) -> bool {
        self.attrs.iter().any(|a| a.key == "bracket")
    }
}

/// One item on a production's right-hand side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProdItem {
    /// A terminal: a fixed, double-quoted character sequence (`"lambda"`, `"("`).
    Terminal(String),
    /// A non-terminal: a reference to a sort, with an optional `name:` field
    /// label (which names the child slot but does not affect the tree).
    NonTerminal { label: Option<SmolStr>, sort: Sort },
}

/// A K sort: a name plus optional sort parameters (`Map{K,V}`). Tutorial
/// grammars use only nullary sorts (`Exp`, `Int`, `Id`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sort {
    pub name: SmolStr,
    pub params: Vec<Sort>,
}

impl Sort {
    /// A nullary sort `NAME`.
    pub fn simple(name: impl Into<SmolStr>) -> Sort {
        Sort {
            name: name.into(),
            params: Vec::new(),
        }
    }
}

/// A production/sort attribute `key` or `key(arg)` (e.g. `left`, `strict(1)`,
/// `symbol("+")`). The argument is carried as an opaque raw string — this
/// frontend acts on only a few attributes (`bracket`, the assoc ones) and
/// preserves the rest verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attr {
    pub key: SmolStr,
    /// The raw text between the parentheses, if any (`strict(1)` → `Some("1")`).
    pub arg: Option<String>,
}

impl Attr {
    /// A bare attribute with no argument.
    pub fn bare(key: impl Into<SmolStr>) -> Attr {
        Attr {
            key: key.into(),
            arg: None,
        }
    }
}

//! Plain-data AST for textual KORE (the `definition.kore` grammar from the
//! haskell-backend's `docs/kore-syntax.md`).
//!
//! Everything is inert data with structural equality — no interning, no
//! kernel types. Attributes are ordinary [`Pattern`]s (KORE attributes are
//! just applications), so nothing here interprets them; the [`crate::fragment`]
//! classifier reads the handful it cares about.

use smol_str::SmolStr;

/// A whole KORE definition: `[attrs] module*`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    /// Definition-level attributes (the leading `[…]`).
    pub attrs: Vec<Pattern>,
    pub modules: Vec<Module>,
}

/// `module NAME sentence* endmodule [attrs]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub name: SmolStr,
    pub sentences: Vec<Sentence>,
    pub attrs: Vec<Pattern>,
}

/// A module sentence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sentence {
    /// `import NAME [attrs]`.
    Import { name: SmolStr, attrs: Vec<Pattern> },
    /// `sort NAME { vars } [attrs]` (or `hooked-sort`).
    Sort {
        hooked: bool,
        name: SmolStr,
        vars: Vec<SmolStr>,
        attrs: Vec<Pattern>,
    },
    /// `symbol NAME { sort_vars } ( arg_sorts ) : ret [attrs]` (or
    /// `hooked-symbol`).
    Symbol {
        hooked: bool,
        name: SmolStr,
        sort_vars: Vec<SmolStr>,
        arg_sorts: Vec<Sort>,
        ret: Sort,
        attrs: Vec<Pattern>,
    },
    /// `alias NAME { sort_vars } ( arg_sorts ) : ret where lhs := rhs [attrs]`.
    /// `lhs` is the application pattern being defined; the alias is *not*
    /// expanded anywhere in this crate (see `SKELETONS.md`).
    Alias {
        name: SmolStr,
        sort_vars: Vec<SmolStr>,
        arg_sorts: Vec<Sort>,
        ret: Sort,
        /// The application pattern being defined (boxed: `Pattern` is large and
        /// would otherwise bloat every `Sentence`).
        lhs: Box<Pattern>,
        rhs: Box<Pattern>,
        attrs: Vec<Pattern>,
    },
    /// `axiom { sort_vars } pattern [attrs]`.
    Axiom {
        sort_vars: Vec<SmolStr>,
        pattern: Pattern,
        attrs: Vec<Pattern>,
    },
    /// `claim { sort_vars } pattern [attrs]` — a reachability claim.
    Claim {
        sort_vars: Vec<SmolStr>,
        pattern: Pattern,
        attrs: Vec<Pattern>,
    },
}

/// A KORE sort: a sort *variable* is a bare identifier, a sort *constructor
/// application* always carries braces (`SortInt{}`, `SortMap{SortK{},SortK{}}`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    /// Sort variable (`R`).
    Var(SmolStr),
    /// Sort constructor application (`SortInt{}` — note nullary still has `{}`).
    App(SmolStr, Vec<Sort>),
}

/// A KORE pattern. Connective names mirror the concrete `\…` syntax; the
/// leading sorts are the connectives' sort *parameters* in source order.
///
/// [`Pattern::String`] and [`Pattern::DV`] carry the **decoded** string
/// payload verbatim (no numeric interpretation — a `\dv{SortInt{}}("0")`
/// stays the string `"0"`). Set-variable names keep their leading `@`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// Element variable `X:Sort`.
    EVar(SmolStr, Sort),
    /// Set variable `@X:Sort` (name stored *with* the `@`).
    SVar(SmolStr, Sort),
    /// String literal.
    String(String),
    /// Symbol application `sym{sorts}(args)`.
    App {
        symbol: SmolStr,
        sorts: Vec<Sort>,
        args: Vec<Pattern>,
    },
    /// `\top{S}()`.
    Top(Sort),
    /// `\bottom{S}()`.
    Bottom(Sort),
    /// `\not{S}(p)`.
    Not(Sort, Box<Pattern>),
    /// `\and{S}(p, …)` — multiary since the 2025-01 grammar change (binary is
    /// the common case in older dumps); zero or more conjuncts.
    And(Sort, Vec<Pattern>),
    /// `\or{S}(p, …)` — multiary likewise.
    Or(Sort, Vec<Pattern>),
    /// `\implies{S}(p, q)`.
    Implies(Sort, Box<Pattern>, Box<Pattern>),
    /// `\iff{S}(p, q)`.
    Iff(Sort, Box<Pattern>, Box<Pattern>),
    /// `\exists{S}(x:Sx, p)`.
    Exists {
        sort: Sort,
        var: SmolStr,
        var_sort: Sort,
        body: Box<Pattern>,
    },
    /// `\forall{S}(x:Sx, p)`.
    Forall {
        sort: Sort,
        var: SmolStr,
        var_sort: Sort,
        body: Box<Pattern>,
    },
    /// `\mu{}(@X:Sx, p)` — NOTE: no sort parameter (empty braces).
    Mu {
        var: SmolStr,
        var_sort: Sort,
        body: Box<Pattern>,
    },
    /// `\nu{}(@X:Sx, p)` — no sort parameter.
    Nu {
        var: SmolStr,
        var_sort: Sort,
        body: Box<Pattern>,
    },
    /// `\ceil{Sarg, S}(p)`.
    Ceil {
        arg_sort: Sort,
        sort: Sort,
        arg: Box<Pattern>,
    },
    /// `\floor{Sarg, S}(p)`.
    Floor {
        arg_sort: Sort,
        sort: Sort,
        arg: Box<Pattern>,
    },
    /// `\equals{Sarg, S}(p, q)`.
    Equals {
        arg_sort: Sort,
        sort: Sort,
        lhs: Box<Pattern>,
        rhs: Box<Pattern>,
    },
    /// `\in{Sarg, S}(p, q)`.
    In {
        arg_sort: Sort,
        sort: Sort,
        lhs: Box<Pattern>,
        rhs: Box<Pattern>,
    },
    /// `\next{S}(p)`.
    Next(Sort, Box<Pattern>),
    /// `\rewrites{S}(p, q)`.
    Rewrites(Sort, Box<Pattern>, Box<Pattern>),
    /// Domain value `\dv{S}("literal")` — the raw literal string.
    DV(Sort, String),
}

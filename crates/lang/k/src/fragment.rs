//! The **fragment classifier**: sorts the axioms in a kompiled KORE
//! definition into the classes the K-frontend lowering will consume
//! (`notes/design/k-frontend.md`).
//!
//! # The consumption ladder this feeds
//!
//! - **F0 — ground rewriting**: unconditional [`RewriteRule`]s over ground
//!   configurations (requires/ensures absent, i.e. `\top`).
//! - **F1 — conditional rewriting + functions**: rules with boolean `requires`
//!   side conditions plus [`AxiomClass::FunctionRule`] equations.
//! - **F2 — symbolic / constrained**: constrained configurations
//!   (constructor no-confusion/no-junk, `\ceil` definedness, assoc/comm
//!   theories) needed for symbolic matching.
//! - **claims / reachability**: `claim` sentences — parsed but entirely
//!   unconsumed by this slice.
//!
//! [`classify`] reads the handful of kompile attributes that mark an axiom's
//! role (attributes win over pattern shape, since e.g. an `assoc` axiom is
//! also `\equals`-shaped) and otherwise recognizes the standard kompiled
//! rewrite-axiom shape
//!
//! ```text
//! \rewrites{S}( \and{S}(LHS, REQ), \and{S}(RHS, ENS) )
//! ```
//!
//! accepting both binary and multiary `\and`, either operand order, and
//! `\top` for a missing requires/ensures. A requires of the kompiled shape
//! `\equals{SortBool{}, S}(b, \dv{SortBool{}}("true"))` is recognized as a
//! constraint, but the **raw pattern** is stored in [`RewriteRule::requires`]
//! — no boolean interpretation happens here.

use smol_str::SmolStr;

use crate::ast::{Definition, Pattern, Sentence, Sort};

/// What role a kompiled axiom plays.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AxiomClass {
    /// A semantic rewrite rule (the extracted payload — boxed, as it dwarfs
    /// the other, unit-like, variants).
    RewriteRule(Box<RewriteRule>),
    /// A function-definition equation (`\equals` at top, possibly guarded by
    /// `\implies`).
    FunctionRule,
    /// An injection axiom marked `subsort{…}()`.
    Subsort,
    /// A constructor-theory axiom (`constructor` / `functional` / `total` /
    /// `no-confusion` / `no-junk` / `injective` attributes).
    ConstructorAxiom,
    /// A `simplification`-attributed rule.
    SimplificationRule,
    /// A `\ceil` definedness axiom.
    Ceil,
    /// An `assoc` / `comm` / `idem` / `unit` theory axiom (uninterpreted).
    AssocComm,
    /// Anything else — the reason names the unrecognized head/attribute.
    Other(SmolStr),
}

/// An extracted kompiled rewrite rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteRule {
    /// The `\rewrites` sort parameter.
    pub sort: Sort,
    /// Left-hand configuration (constraint stripped).
    pub lhs: Pattern,
    /// Right-hand configuration (constraint stripped).
    pub rhs: Pattern,
    /// The raw requires constraint, if present (`\top` ⇒ `None`).
    pub requires: Option<Pattern>,
    /// The raw ensures constraint, if present (`\top` ⇒ `None`).
    pub ensures: Option<Pattern>,
    /// `priority{}("N")` ⇒ N; `owise{}()` ⇒ 200; default 50.
    pub priority: u32,
    /// `label{}("…")`, if present.
    pub label: Option<SmolStr>,
    /// `UNIQUE'Unds'ID{}("…")`, if present.
    pub unique_id: Option<SmolStr>,
}

/// Classify one sentence (meaningful for `axiom` sentences; anything else is
/// [`AxiomClass::Other`]).
pub fn classify(sentence: &Sentence) -> AxiomClass {
    let Sentence::Axiom { pattern, attrs, .. } = sentence else {
        return AxiomClass::Other(SmolStr::new("not an axiom sentence"));
    };

    // Attributes win over pattern shape (an `assoc` axiom is also
    // `\equals`-shaped, a subsort axiom is also `\exists`-shaped, …).
    if has_attr(attrs, "subsort") {
        return AxiomClass::Subsort;
    }
    if has_attr(attrs, "simplification") {
        return AxiomClass::SimplificationRule;
    }
    if ["assoc", "comm", "idem", "unit"]
        .iter()
        .any(|a| has_attr(attrs, a))
    {
        return AxiomClass::AssocComm;
    }
    if [
        "constructor",
        "functional",
        "total",
        "no-confusion",
        "no-junk",
        "injective",
    ]
    .iter()
    .any(|a| has_attr(attrs, a))
    {
        return AxiomClass::ConstructorAxiom;
    }

    match pattern {
        Pattern::Rewrites(sort, lhs_side, rhs_side) => {
            match extract_rewrite(sort, lhs_side, rhs_side, attrs) {
                Ok(rule) => AxiomClass::RewriteRule(Box::new(rule)),
                Err(reason) => AxiomClass::Other(SmolStr::new(reason)),
            }
        }
        Pattern::Ceil { .. } => AxiomClass::Ceil,
        Pattern::Implies(_, _, rhs) if matches!(**rhs, Pattern::Ceil { .. }) => AxiomClass::Ceil,
        Pattern::Equals { .. } => AxiomClass::FunctionRule,
        Pattern::Implies(_, _, rhs) if matches!(**rhs, Pattern::Equals { .. }) => {
            AxiomClass::FunctionRule
        }
        p => AxiomClass::Other(SmolStr::new(format!(
            "unrecognized axiom shape: {}",
            pattern_head(p)
        ))),
    }
}

/// Collect every axiom in `def` that classifies as a rewrite rule.
pub fn rewrite_rules(def: &Definition) -> Vec<RewriteRule> {
    def.modules
        .iter()
        .flat_map(|m| &m.sentences)
        .filter_map(|s| match classify(s) {
            AxiomClass::RewriteRule(r) => Some(*r),
            _ => None,
        })
        .collect()
}

// -- rewrite extraction -------------------------------------------------------

fn extract_rewrite(
    sort: &Sort,
    lhs_side: &Pattern,
    rhs_side: &Pattern,
    attrs: &[Pattern],
) -> Result<RewriteRule, String> {
    let (requires, lhs) = split_side(lhs_side)?;
    let (ensures, rhs) = split_side(rhs_side)?;
    Ok(RewriteRule {
        sort: sort.clone(),
        lhs,
        rhs,
        requires,
        ensures,
        priority: priority_of(attrs),
        label: attr_string(attrs, "label"),
        unique_id: attr_string(attrs, "UNIQUE'Unds'ID"),
    })
}

/// Split one side of a kompiled `\rewrites` into `(constraint, term)`.
///
/// A top-level `\and` (binary or multiary, either operand order) is
/// partitioned into constraint-shaped conjuncts (`\top` / `\equals` / `\in` /
/// `\not` / nested `\and` of such) and the configuration term. `\top`
/// constraints vanish; several surviving constraints are re-joined with the
/// `\and`'s own sort. If the split is ambiguous (not exactly one term
/// conjunct), the whole side is taken as an unconstrained term.
fn split_side(side: &Pattern) -> Result<(Option<Pattern>, Pattern), String> {
    let Pattern::And(and_sort, args) = side else {
        return Ok((None, side.clone()));
    };
    let (constraints, terms): (Vec<&Pattern>, Vec<&Pattern>) =
        args.iter().partition(|p| is_constraint(p));
    let [term] = terms.as_slice() else {
        // Ambiguous — treat the whole `\and` as the term.
        return Ok((None, side.clone()));
    };
    let mut live: Vec<Pattern> = constraints
        .into_iter()
        .filter(|p| !matches!(p, Pattern::Top(_)))
        .cloned()
        .collect();
    let constraint = match live.len() {
        0 => None,
        1 => Some(live.pop().unwrap()),
        _ => Some(Pattern::And(and_sort.clone(), live)),
    };
    Ok((constraint, (*term).clone()))
}

/// Constraint-shaped conjuncts of a kompiled rule side (predicates, not
/// configuration terms).
fn is_constraint(p: &Pattern) -> bool {
    match p {
        Pattern::Top(_) | Pattern::Equals { .. } | Pattern::In { .. } => true,
        Pattern::Not(_, inner) => is_constraint(inner),
        Pattern::And(_, args) => args.iter().all(is_constraint),
        _ => false,
    }
}

// -- attribute helpers --------------------------------------------------------

/// Find an attribute application by symbol name.
fn attr_app<'a>(attrs: &'a [Pattern], name: &str) -> Option<&'a Pattern> {
    attrs
        .iter()
        .find(|p| matches!(p, Pattern::App { symbol, .. } if symbol == name))
}

fn has_attr(attrs: &[Pattern], name: &str) -> bool {
    attr_app(attrs, name).is_some()
}

/// The single string argument of `name{…}("…")`, if the attribute is present
/// with that shape.
fn attr_string(attrs: &[Pattern], name: &str) -> Option<SmolStr> {
    match attr_app(attrs, name)? {
        Pattern::App { args, .. } => match args.as_slice() {
            [Pattern::String(s)] => Some(SmolStr::new(s)),
            _ => None,
        },
        _ => None,
    }
}

/// `priority{}("N")` ⇒ N; else `owise{}()` ⇒ 200; else 50.
fn priority_of(attrs: &[Pattern]) -> u32 {
    if let Some(n) = attr_string(attrs, "priority")
        && let Ok(n) = n.parse::<u32>()
    {
        return n;
    }
    if has_attr(attrs, "owise") {
        return 200;
    }
    50
}

/// A short head name for `Other(…)` diagnostics.
fn pattern_head(p: &Pattern) -> &'static str {
    match p {
        Pattern::EVar(..) => "element variable",
        Pattern::SVar(..) => "set variable",
        Pattern::String(_) => "string literal",
        Pattern::App { .. } => "application",
        Pattern::Top(_) => "\\top",
        Pattern::Bottom(_) => "\\bottom",
        Pattern::Not(..) => "\\not",
        Pattern::And(..) => "\\and",
        Pattern::Or(..) => "\\or",
        Pattern::Implies(..) => "\\implies",
        Pattern::Iff(..) => "\\iff",
        Pattern::Exists { .. } => "\\exists",
        Pattern::Forall { .. } => "\\forall",
        Pattern::Mu { .. } => "\\mu",
        Pattern::Nu { .. } => "\\nu",
        Pattern::Ceil { .. } => "\\ceil",
        Pattern::Floor { .. } => "\\floor",
        Pattern::Equals { .. } => "\\equals",
        Pattern::In { .. } => "\\in",
        Pattern::Next(..) => "\\next",
        Pattern::Rewrites(..) => "\\rewrites",
        Pattern::DV(..) => "\\dv",
    }
}

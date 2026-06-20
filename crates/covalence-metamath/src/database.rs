//! The Metamath frame / database model.
//!
//! A [`Database`] is a flat, source-order list of [`Statement`]s plus a symbol
//! table classifying every symbol as a constant or a variable. Assertions
//! (`$a` axioms, `$p` theorems) carry their **mandatory [`Frame`]**: the
//! `$f`/`$e` hypotheses they depend on (in database order) and the `$d`
//! distinct-variable conditions that constrain how they may be applied.
//!
//! Building a database tracks an active scope stack (`${ ... $}`): floating
//! hypotheses, essential hypotheses, variable declarations, and `$d`
//! restrictions are scoped, while `$c`/`$a`/`$p` are global.

use std::collections::HashMap;

use crate::error::MmError;
use crate::expr::Expr;

/// A floating hypothesis (`$f`): a variable's typecode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FloatHyp {
    pub label: String,
    /// The typecode constant (e.g. `wff`, `term`, `class`).
    pub typecode: String,
    /// The variable being typed (e.g. `ph`, `t`).
    pub var: String,
}

/// An essential hypothesis (`$e`): a full logical premise as an [`Expr`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hypothesis {
    pub label: String,
    pub expr: Expr,
}

/// The mandatory frame of an assertion: the hypotheses it consumes and the
/// distinct-variable conditions it imposes.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Frame {
    /// Mandatory `$f` hypotheses, in database order. These are the variables
    /// the assertion is parameterised over (its "type signature").
    pub floats: Vec<FloatHyp>,
    /// Mandatory `$e` hypotheses, in database order.
    pub essentials: Vec<Hypothesis>,
    /// Mandatory `$d` conditions as unordered variable pairs.
    pub disjoints: Vec<(String, String)>,
}

impl Frame {
    /// The mandatory hypotheses in RPN-application order: all `$f` first
    /// (database order), then all `$e` (database order). This is the order in
    /// which they are popped off the proof stack.
    pub fn mandatory_count(&self) -> usize {
        self.floats.len() + self.essentials.len()
    }
}

/// An assertion: an axiom (`$a`) or a theorem (`$p`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    pub label: String,
    /// The asserted conclusion (typecode + body).
    pub conclusion: Expr,
    /// The mandatory frame.
    pub frame: Frame,
    /// `Some(proof)` for a `$p` theorem (an RPN sequence of labels), `None` for
    /// a `$a` axiom.
    pub proof: Option<Vec<String>>,
}

/// A top-level statement, in source order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    /// `$c` constant declaration.
    Constant(Vec<String>),
    /// `$v` variable declaration.
    Variable(Vec<String>),
    /// `$f` floating hypothesis.
    Float(FloatHyp),
    /// `$e` essential hypothesis.
    Essential(Hypothesis),
    /// `$d` distinct-variable restriction (the full symbol list).
    Disjoint(Vec<String>),
    /// `$a` / `$p` assertion.
    Assert(Assertion),
}

/// One lexical scope (`${ ... $}`).
#[derive(Debug, Clone, Default)]
struct Scope {
    floats: Vec<FloatHyp>,
    essentials: Vec<Hypothesis>,
    /// Active `$d` pairs (already expanded pairwise).
    disjoints: Vec<(String, String)>,
}

/// A parsed Metamath database.
#[derive(Debug, Clone)]
pub struct Database {
    /// Symbol classification: name → `true` if a variable, `false` if a
    /// constant.
    symbols: HashMap<String, bool>,
    /// All statements in source order.
    statements: Vec<Statement>,
    /// label → index into `statements` (only labelled statements).
    labels: HashMap<String, usize>,
    /// Active scope stack; index 0 is the global scope.
    scopes: Vec<Scope>,
}

impl Default for Database {
    fn default() -> Self {
        Self::new()
    }
}

impl Database {
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            statements: Vec::new(),
            labels: HashMap::new(),
            scopes: vec![Scope::default()],
        }
    }

    // --- queries -----------------------------------------------------------

    /// Whether `name` is a declared variable.
    pub fn is_variable(&self, name: &str) -> bool {
        self.symbols.get(name).copied().unwrap_or(false)
    }

    /// Whether `name` is a declared symbol (constant or variable).
    pub fn is_symbol(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
    }

    /// All statements in source order.
    pub fn statements(&self) -> &[Statement] {
        &self.statements
    }

    /// Look up a labelled statement.
    pub fn statement_by_label(&self, label: &str) -> Option<&Statement> {
        self.labels.get(label).map(|&i| &self.statements[i])
    }

    /// Iterate over all assertions (`$a`/`$p`) in source order.
    pub fn assertions(&self) -> impl Iterator<Item = &Assertion> {
        self.statements.iter().filter_map(|s| match s {
            Statement::Assert(a) => Some(a),
            _ => None,
        })
    }

    // --- construction (used by the parser) ---------------------------------

    pub(crate) fn declare_constants(&mut self, names: Vec<String>) -> Result<(), MmError> {
        for n in &names {
            if self.symbols.insert(n.clone(), false).is_some() {
                return Err(MmError::Parse(format!("symbol `{n}` re-declared")));
            }
        }
        self.statements.push(Statement::Constant(names));
        Ok(())
    }

    pub(crate) fn declare_variables(&mut self, names: Vec<String>) -> Result<(), MmError> {
        for n in &names {
            // A variable may be re-declared in a disjoint scope; we keep it
            // simple and allow re-declaration as a variable.
            match self.symbols.get(n) {
                Some(false) => {
                    return Err(MmError::Parse(format!(
                        "symbol `{n}` declared as both constant and variable"
                    )));
                }
                _ => {
                    self.symbols.insert(n.clone(), true);
                }
            }
        }
        self.statements.push(Statement::Variable(names));
        Ok(())
    }

    fn register_label(&mut self, label: &str, idx: usize) -> Result<(), MmError> {
        if self.labels.contains_key(label) {
            return Err(MmError::DuplicateLabel(label.to_string()));
        }
        self.labels.insert(label.to_string(), idx);
        Ok(())
    }

    pub(crate) fn add_float(&mut self, hyp: FloatHyp) -> Result<(), MmError> {
        if !self.is_symbol(&hyp.typecode) {
            return Err(MmError::UnknownSymbol {
                label: hyp.label.clone(),
                symbol: hyp.typecode.clone(),
            });
        }
        if !self.is_variable(&hyp.var) {
            return Err(MmError::Parse(format!(
                "`{}`: `{}` is not a declared variable",
                hyp.label, hyp.var
            )));
        }
        let idx = self.statements.len();
        self.register_label(&hyp.label, idx)?;
        self.scopes.last_mut().unwrap().floats.push(hyp.clone());
        self.statements.push(Statement::Float(hyp));
        Ok(())
    }

    pub(crate) fn add_essential(&mut self, hyp: Hypothesis) -> Result<(), MmError> {
        let idx = self.statements.len();
        self.register_label(&hyp.label, idx)?;
        self.scopes.last_mut().unwrap().essentials.push(hyp.clone());
        self.statements.push(Statement::Essential(hyp));
        Ok(())
    }

    pub(crate) fn add_disjoint(&mut self, vars: Vec<String>) -> Result<(), MmError> {
        for v in &vars {
            if !self.is_variable(v) {
                return Err(MmError::Parse(format!("`{v}` in $d is not a variable")));
            }
        }
        // Expand into pairwise restrictions in the current scope.
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                if vars[i] == vars[j] {
                    return Err(MmError::Parse(format!(
                        "$d lists `{}` twice (a variable is never distinct from itself)",
                        vars[i]
                    )));
                }
                self.scopes
                    .last_mut()
                    .unwrap()
                    .disjoints
                    .push((vars[i].clone(), vars[j].clone()));
            }
        }
        self.statements.push(Statement::Disjoint(vars));
        Ok(())
    }

    /// Add an assertion (`$a` or `$p`), computing its mandatory frame from the
    /// active scope stack.
    pub(crate) fn add_assertion(
        &mut self,
        label: String,
        conclusion: Expr,
        proof: Option<Vec<String>>,
    ) -> Result<(), MmError> {
        let frame = self.build_frame(&conclusion, &label)?;
        let idx = self.statements.len();
        self.register_label(&label, idx)?;
        self.statements.push(Statement::Assert(Assertion {
            label,
            conclusion,
            frame,
            proof,
        }));
        Ok(())
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    pub(crate) fn pop_scope(&mut self) -> Result<(), MmError> {
        if self.scopes.len() <= 1 {
            return Err(MmError::Parse("unmatched `$}`".into()));
        }
        self.scopes.pop();
        Ok(())
    }

    pub(crate) fn finish(self) -> Result<Self, MmError> {
        if self.scopes.len() != 1 {
            return Err(MmError::Parse("unclosed `${` at end of input".into()));
        }
        Ok(self)
    }

    // --- frame computation -------------------------------------------------

    /// Compute the mandatory frame for an assertion with the given conclusion.
    ///
    /// Per the Metamath spec, the mandatory variables are those appearing in
    /// the conclusion or in any active `$e` hypothesis. The mandatory `$f`
    /// hypotheses are the active floats for exactly those variables, in
    /// database order. The mandatory `$e` are all active essentials. The
    /// mandatory `$d` are the active disjoint pairs whose *both* variables are
    /// mandatory.
    fn build_frame(&self, conclusion: &Expr, label: &str) -> Result<Frame, MmError> {
        // Active hypotheses, outermost scope first (= database order).
        let active_floats: Vec<&FloatHyp> =
            self.scopes.iter().flat_map(|s| s.floats.iter()).collect();
        let active_essentials: Vec<&Hypothesis> =
            self.scopes.iter().flat_map(|s| s.essentials.iter()).collect();
        let active_disjoints: Vec<&(String, String)> =
            self.scopes.iter().flat_map(|s| s.disjoints.iter()).collect();

        // Mandatory variable set: from the conclusion and from active $e.
        let mut mandatory_vars: Vec<String> = Vec::new();
        let push_var = |name: &str, set: &mut Vec<String>| {
            if self.is_variable(name) && !set.contains(&name.to_string()) {
                set.push(name.to_string());
            }
        };
        self.collect_vars(conclusion, label, &mut |n| push_var(n, &mut mandatory_vars))?;
        for h in &active_essentials {
            self.collect_vars(&h.expr, &h.label, &mut |n| push_var(n, &mut mandatory_vars))?;
        }

        // Mandatory $f: active floats whose variable is mandatory, in order.
        let floats: Vec<FloatHyp> = active_floats
            .iter()
            .filter(|f| mandatory_vars.contains(&f.var))
            .map(|f| (*f).clone())
            .collect();

        // Every mandatory variable must have a floating hypothesis.
        for v in &mandatory_vars {
            if !floats.iter().any(|f| &f.var == v) {
                return Err(MmError::MalformedExpr {
                    label: label.to_string(),
                    message: format!("variable `{v}` has no active floating hypothesis (`$f`)"),
                });
            }
        }

        let essentials: Vec<Hypothesis> = active_essentials.into_iter().cloned().collect();

        let disjoints: Vec<(String, String)> = active_disjoints
            .iter()
            .filter(|(a, b)| mandatory_vars.contains(a) && mandatory_vars.contains(b))
            .map(|(a, b)| ((*a).clone(), (*b).clone()))
            .collect();

        Ok(Frame {
            floats,
            essentials,
            disjoints,
        })
    }

    /// Invoke `f` on every symbol of `expr`, validating that each is a declared
    /// symbol.
    fn collect_vars(
        &self,
        expr: &Expr,
        label: &str,
        f: &mut impl FnMut(&str),
    ) -> Result<(), MmError> {
        let syms = crate::expr::expr_symbols(expr).ok_or_else(|| MmError::MalformedExpr {
            label: label.to_string(),
            message: "expression contains a non-symbol element".into(),
        })?;
        for s in syms {
            if !self.is_symbol(s) {
                return Err(MmError::UnknownSymbol {
                    label: label.to_string(),
                    symbol: s.to_string(),
                });
            }
            f(s);
        }
        Ok(())
    }
}

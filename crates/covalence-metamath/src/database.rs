use indexmap::IndexMap;

/// Typed index into the symbol table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

/// Typed index into the statement list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StatementId(pub u32);

/// A Metamath statement.
#[derive(Debug, Clone)]
pub enum Statement {
    /// `$c` — constant declaration.
    Constant { symbols: Vec<SymbolId> },
    /// `$v` — variable declaration.
    Variable { symbols: Vec<SymbolId> },
    /// `$f` — floating (variable-type) hypothesis.
    Float {
        label: String,
        typecode: SymbolId,
        var: SymbolId,
    },
    /// `$e` — essential (logical) hypothesis.
    Essential {
        label: String,
        symbols: Vec<SymbolId>,
    },
    /// `$a` — axiomatic assertion.
    Axiom {
        label: String,
        symbols: Vec<SymbolId>,
        frame: Frame,
    },
    /// `$p` — provable assertion.
    Provable {
        label: String,
        symbols: Vec<SymbolId>,
        frame: Frame,
        proof: Proof,
    },
    /// `$d` — disjoint variable restriction (stored, not enforced).
    Disjoint { vars: Vec<SymbolId> },
}

/// A Metamath proof — either normal (list of labels) or compressed.
#[derive(Debug, Clone)]
pub enum Proof {
    /// Normal proof: sequence of statement labels.
    Normal(Vec<String>),
    /// Compressed proof: label block + encoded letter block.
    Compressed {
        labels: Vec<String>,
        letters: Vec<u8>,
    },
}

/// The mandatory frame for an `$a` or `$p` statement.
#[derive(Debug, Clone)]
pub struct Frame {
    /// Mandatory `$f` hypotheses (in order).
    pub floats: Vec<StatementId>,
    /// Mandatory `$e` hypotheses (in order).
    pub essentials: Vec<StatementId>,
    /// Mandatory `$d` restrictions.
    pub disjoints: Vec<(SymbolId, SymbolId)>,
}

/// Tracks active variables, floats, essentials, and disjoints within a `${ $}` block.
#[derive(Debug, Clone, Default)]
pub(crate) struct Scope {
    /// Variables declared in this scope.
    pub variables: Vec<SymbolId>,
    /// `$f` statements declared in this scope (label → statement index).
    pub floats: Vec<(String, StatementId)>,
    /// `$e` statements declared in this scope (label → statement index).
    pub essentials: Vec<(String, StatementId)>,
    /// `$d` restrictions declared in this scope.
    pub disjoints: Vec<(SymbolId, SymbolId)>,
}

/// A parsed Metamath database.
#[derive(Debug, Clone)]
pub struct Database {
    /// Interned symbols: name → is_variable. Index position = SymbolId.
    pub symbols: IndexMap<String, bool>,
    /// All statements in source order.
    pub statements: Vec<Statement>,
    /// Label → statement index.
    pub labels: IndexMap<String, StatementId>,
    /// Active scope stack (outermost first).
    pub(crate) scopes: Vec<Scope>,
}

impl Database {
    pub(crate) fn new() -> Self {
        Self {
            symbols: IndexMap::new(),
            statements: Vec::new(),
            labels: IndexMap::new(),
            scopes: vec![Scope::default()],
        }
    }

    /// Look up a symbol id by name.
    pub fn lookup_symbol(&self, name: &str) -> Option<SymbolId> {
        self.symbols.get_index_of(name).map(|i| SymbolId(i as u32))
    }

    /// Get a symbol name by id.
    pub fn symbol_name(&self, id: SymbolId) -> &str {
        self.symbols
            .get_index(id.0 as usize)
            .map(|(name, _)| name.as_str())
            .expect("invalid SymbolId")
    }

    /// Check whether a symbol is a variable.
    pub fn is_variable(&self, id: SymbolId) -> bool {
        self.symbols
            .get_index(id.0 as usize)
            .map(|(_, &is_var)| is_var)
            .unwrap_or(false)
    }

    /// Look up a statement index by label.
    pub fn lookup_label(&self, label: &str) -> Option<StatementId> {
        self.labels.get(label).copied()
    }

    /// Get a statement by index.
    pub fn statement(&self, id: StatementId) -> &Statement {
        &self.statements[id.0 as usize]
    }

    /// Intern or look up a symbol, returning its id.
    pub(crate) fn intern_symbol(&mut self, name: &str, is_variable: bool) -> SymbolId {
        if let Some(idx) = self.symbols.get_index_of(name) {
            // If re-declaring as variable, upgrade.
            if is_variable {
                *self.symbols.get_index_mut(idx).unwrap().1 = true;
            }
            SymbolId(idx as u32)
        } else {
            let idx = self.symbols.len();
            self.symbols.insert(name.to_owned(), is_variable);
            SymbolId(idx as u32)
        }
    }

    /// Add a statement and return its id.
    pub(crate) fn add_statement(&mut self, stmt: Statement) -> StatementId {
        let id = StatementId(self.statements.len() as u32);
        self.statements.push(stmt);
        id
    }

    /// Register a label for a statement. Returns error if duplicate.
    pub(crate) fn register_label(&mut self, label: String, id: StatementId) -> Result<(), String> {
        if self.labels.contains_key(&label) {
            return Err(label);
        }
        self.labels.insert(label, id);
        Ok(())
    }

    /// Compute the mandatory frame for an assertion with the given symbol string.
    pub(crate) fn build_frame(&self, symbols: &[SymbolId]) -> Frame {
        // Collect all variables that appear in the assertion or in active $e hypotheses.
        let mut vars_used: Vec<SymbolId> = Vec::new();
        let mut seen = std::collections::HashSet::new();

        // Variables in the assertion itself.
        for &sym in symbols {
            if self.is_variable(sym) && seen.insert(sym) {
                vars_used.push(sym);
            }
        }

        // Variables in active $e hypotheses.
        let essentials = self.active_essentials();
        for &(_, eid) in &essentials {
            if let Statement::Essential {
                symbols: ref esyms, ..
            } = self.statements[eid.0 as usize]
            {
                for &sym in esyms {
                    if self.is_variable(sym) && seen.insert(sym) {
                        vars_used.push(sym);
                    }
                }
            }
        }

        // Mandatory $f: iterate active $f in database order, include those whose
        // variable is used. Metamath requires mandatory hypotheses in database order.
        let active_floats = self.active_floats();
        let mut floats = Vec::new();
        for &(_, fid) in &active_floats {
            if let Statement::Float { var: fvar, .. } = self.statements[fid.0 as usize] {
                if seen.contains(&fvar) {
                    floats.push(fid);
                }
            }
        }

        // Mandatory $d: active disjoints where both variables are in vars_used.
        let active_disjoints = self.active_disjoints();
        let mut disjoints = Vec::new();
        for &(a, b) in &active_disjoints {
            if seen.contains(&a) && seen.contains(&b) {
                disjoints.push((a, b));
            }
        }

        Frame {
            floats,
            essentials: essentials.iter().map(|&(_, id)| id).collect(),
            disjoints,
        }
    }

    fn active_floats(&self) -> Vec<(String, StatementId)> {
        self.scopes
            .iter()
            .flat_map(|s| s.floats.iter().cloned())
            .collect()
    }

    fn active_essentials(&self) -> Vec<(String, StatementId)> {
        self.scopes
            .iter()
            .flat_map(|s| s.essentials.iter().cloned())
            .collect()
    }

    fn active_disjoints(&self) -> Vec<(SymbolId, SymbolId)> {
        self.scopes
            .iter()
            .flat_map(|s| s.disjoints.iter().copied())
            .collect()
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().expect("scope stack is empty")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_symbol() {
        let mut db = Database::new();
        let a = db.intern_symbol("wff", false);
        let b = db.intern_symbol("wff", false);
        assert_eq!(a, b);
        assert_eq!(db.symbol_name(a), "wff");
        assert!(!db.is_variable(a));
    }

    #[test]
    fn intern_variable() {
        let mut db = Database::new();
        let a = db.intern_symbol("ph", true);
        assert!(db.is_variable(a));
    }

    #[test]
    fn lookup_symbol() {
        let mut db = Database::new();
        db.intern_symbol("wff", false);
        assert!(db.lookup_symbol("wff").is_some());
        assert!(db.lookup_symbol("nope").is_none());
    }

    #[test]
    fn add_and_lookup_label() {
        let mut db = Database::new();
        let stmt = Statement::Constant {
            symbols: vec![SymbolId(0)],
        };
        let id = db.add_statement(stmt);
        db.register_label("test".into(), id).unwrap();
        assert_eq!(db.lookup_label("test"), Some(id));
    }

    #[test]
    fn duplicate_label() {
        let mut db = Database::new();
        let stmt = Statement::Constant {
            symbols: vec![SymbolId(0)],
        };
        let id = db.add_statement(stmt);
        db.register_label("dup".into(), id).unwrap();
        assert!(db.register_label("dup".into(), id).is_err());
    }
}

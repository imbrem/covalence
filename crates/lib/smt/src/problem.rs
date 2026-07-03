use covalence_sexp::SExpr;

/// A sort declaration: `(declare-sort <name> <arity>)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SortDecl {
    pub name: String,
    pub arity: u32,
}

/// A function declaration: `(declare-fun <name> (<params>...) <sort>)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDecl {
    pub name: String,
    pub params: Vec<SExpr>,
    pub sort: SExpr,
}

/// An SMT-LIB2 problem — logic, declarations, and assertions.
///
/// Terms are stored as raw `SExpr` values, matching the design of `AletheProof`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtProblem {
    logic: Option<String>,
    sorts: Vec<SortDecl>,
    funs: Vec<FunDecl>,
    assertions: Vec<SExpr>,
}

impl SmtProblem {
    /// Create an empty problem.
    pub fn new() -> Self {
        Self {
            logic: None,
            sorts: Vec::new(),
            funs: Vec::new(),
            assertions: Vec::new(),
        }
    }

    /// Set the logic (e.g. `"QF_UF"`).
    pub fn set_logic(&mut self, logic: impl Into<String>) -> &mut Self {
        self.logic = Some(logic.into());
        self
    }

    /// Add a sort declaration.
    pub fn declare_sort(&mut self, name: impl Into<String>, arity: u32) -> &mut Self {
        self.sorts.push(SortDecl {
            name: name.into(),
            arity,
        });
        self
    }

    /// Add a function declaration.
    pub fn declare_fun(
        &mut self,
        name: impl Into<String>,
        params: Vec<SExpr>,
        sort: SExpr,
    ) -> &mut Self {
        self.funs.push(FunDecl {
            name: name.into(),
            params,
            sort,
        });
        self
    }

    /// Add an assertion.
    pub fn assert_term(&mut self, term: SExpr) -> &mut Self {
        self.assertions.push(term);
        self
    }

    /// The logic, if set.
    pub fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// Sort declarations.
    pub fn sorts(&self) -> &[SortDecl] {
        &self.sorts
    }

    /// Function declarations.
    pub fn funs(&self) -> &[FunDecl] {
        &self.funs
    }

    /// Assertions.
    pub fn assertions(&self) -> &[SExpr] {
        &self.assertions
    }
}

impl Default for SmtProblem {
    fn default() -> Self {
        Self::new()
    }
}

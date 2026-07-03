use super::decl::Decl;
use super::name::Name;

/// A Lean environment: a collection of declarations.
#[derive(Debug, Clone)]
pub struct Env {
    pub decls: Vec<Decl>,
}

impl Env {
    /// Create an empty environment.
    pub fn new() -> Self {
        Env { decls: Vec::new() }
    }

    /// Find a declaration by name.
    pub fn find(&self, name: &Name) -> Option<&Decl> {
        self.decls.iter().find(|d| d.name() == name)
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

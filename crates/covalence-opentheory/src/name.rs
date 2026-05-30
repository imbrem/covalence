//! OpenTheory name representation and interning.

use std::collections::HashMap;

use smol_str::SmolStr;

use covalence_hol::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, NameId};

/// An OpenTheory name — a namespace (list of components) plus a base name.
#[derive(Debug, Clone)]
pub struct OtName {
    pub namespace: Vec<SmolStr>,
    pub name: SmolStr,
}

impl OtName {
    /// Parse an OpenTheory quoted name string.
    /// Format: `"Component1.Component2.Name"` where components before the last
    /// dot are the namespace.
    pub fn parse(s: &str) -> Self {
        let parts: Vec<&str> = s.split('.').collect();
        if parts.len() == 1 {
            OtName {
                namespace: vec![],
                name: SmolStr::new(parts[0]),
            }
        } else {
            let namespace = parts[..parts.len() - 1]
                .iter()
                .map(|p| SmolStr::new(p))
                .collect();
            let name = SmolStr::new(parts[parts.len() - 1]);
            OtName { namespace, name }
        }
    }

    /// Get the fully qualified name as a string.
    pub fn qualified(&self) -> SmolStr {
        if self.namespace.is_empty() {
            self.name.clone()
        } else {
            let mut s = String::new();
            for ns in &self.namespace {
                s.push_str(ns);
                s.push('.');
            }
            s.push_str(&self.name);
            SmolStr::new(&s)
        }
    }
}

/// Name interning table — maps strings to NameId and back.
pub struct NameTable {
    to_id: HashMap<SmolStr, NameId>,
    to_name: Vec<SmolStr>,
}

impl NameTable {
    pub fn new() -> Self {
        let mut table = NameTable {
            to_id: HashMap::new(),
            to_name: Vec::new(),
        };
        // Pre-register well-known names.
        let fun_id = table.intern(SmolStr::new("->"));
        assert_eq!(fun_id, FUN_TYCON_ID);
        let bool_id = table.intern(SmolStr::new("bool"));
        assert_eq!(bool_id, BOOL_TYCON_ID);
        let eq_id = table.intern(SmolStr::new("="));
        assert_eq!(eq_id, EQ_CONST_ID);
        table
    }

    /// Intern a name, returning its ID (or existing ID if already interned).
    pub fn intern(&mut self, name: SmolStr) -> NameId {
        if let Some(&id) = self.to_id.get(&name) {
            return id;
        }
        let id = self.to_name.len() as NameId;
        self.to_name.push(name.clone());
        self.to_id.insert(name, id);
        id
    }

    /// Intern a name from a `&str`, returning its ID.
    pub fn intern_str(&mut self, name: &str) -> NameId {
        self.intern(SmolStr::new(name))
    }

    /// Look up a name by ID.
    pub fn resolve(&self, id: NameId) -> Option<&SmolStr> {
        self.to_name.get(id as usize)
    }
}

impl Default for NameTable {
    fn default() -> Self {
        Self::new()
    }
}

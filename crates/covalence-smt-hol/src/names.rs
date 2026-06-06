//! Name interning for the Alethe → HOL bridge.
//!
//! Mirrors the pre-registration pattern used by `covalence-opentheory::NameTable`
//! (the well-known kernel names `->`, `bool`, `=` must occupy slots 0, 1, 2
//! to satisfy `HolKernel::new`'s contract). We keep a *local* copy so the
//! bridge crate doesn't take an OT dependency.

use std::collections::HashMap;

use covalence_hol::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, NameId};
use smol_str::SmolStr;

/// Interning table keyed by `SmolStr`.
pub struct NameTable {
    to_id: HashMap<SmolStr, NameId>,
    to_name: Vec<SmolStr>,
}

impl NameTable {
    /// Build a table with the well-known names pre-registered at the slots
    /// expected by `HolKernel::new`.
    pub fn new() -> Self {
        let mut table = NameTable {
            to_id: HashMap::new(),
            to_name: Vec::new(),
        };
        let fun_id = table.intern_str("->");
        assert_eq!(fun_id, FUN_TYCON_ID);
        let bool_id = table.intern_str("bool");
        assert_eq!(bool_id, BOOL_TYCON_ID);
        let eq_id = table.intern_str("=");
        assert_eq!(eq_id, EQ_CONST_ID);
        table
    }

    pub fn intern_str(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.to_id.get(name) {
            return id;
        }
        let s = SmolStr::new(name);
        let id = self.to_name.len() as NameId;
        self.to_name.push(s.clone());
        self.to_id.insert(s, id);
        id
    }

    pub fn resolve(&self, id: NameId) -> Option<&SmolStr> {
        self.to_name.get(id as usize)
    }
}

impl Default for NameTable {
    fn default() -> Self {
        Self::new()
    }
}

//! The variable [`Scope`] — `fix`-declared and binder-introduced variables,
//! pushed and popped in groups as the interpreter enters and leaves binders.
//!
//! Backed by a private [`SymbolTable`]: an ordered `Vec` of bindings (binder
//! order, which the elaborator wants) plus an index from name to a *stack* of
//! positions, so a name can be **shadowed** (an inner binding hides an outer
//! one and lookup recovers the innermost) and lookup is still O(1). The table
//! is the unit we mean to make cleverer (or swap for an imported
//! implementation) later — hence its private, self-contained interface.

use covalence_core::Type;
use indexmap::IndexMap;

/// An ordered, shadowing symbol table: insertion order is preserved (for
/// `iter`), names may repeat (the most recent binding wins on `get`), and the
/// tail can be truncated to undo a batch of bindings. Private on purpose — the
/// public surface is [`Scope`].
#[derive(Clone)]
struct SymbolTable<V> {
    /// Bindings in insertion order; a name may appear more than once.
    entries: Vec<(String, V)>,
    /// Name → stack of positions into `entries` (innermost binding last).
    index: IndexMap<String, Vec<usize>>,
}

impl<V> SymbolTable<V> {
    fn new() -> Self {
        SymbolTable {
            entries: Vec::new(),
            index: IndexMap::new(),
        }
    }

    /// Append a binding (shadowing any existing one of the same name until it
    /// is truncated away).
    fn push(&mut self, name: String, val: V) {
        let pos = self.entries.len();
        self.index.entry(name.clone()).or_default().push(pos);
        self.entries.push((name, val));
    }

    /// The innermost (most recent) binding of `name`, if any.
    fn get(&self, name: &str) -> Option<&V> {
        let pos = *self.index.get(name)?.last()?;
        Some(&self.entries[pos].1)
    }

    /// Drop bindings until exactly `len` remain, repairing the position
    /// stacks (and removing names that no longer bind anything).
    fn truncate(&mut self, len: usize) {
        while self.entries.len() > len {
            let (name, _) = self.entries.pop().expect("len checked");
            // The popped entry is the highest-positioned binding of `name`,
            // hence the top of its stack.
            if let Some(stack) = self.index.get_mut(&name) {
                stack.pop();
                if stack.is_empty() {
                    self.index.swap_remove(&name);
                }
            }
        }
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn iter(&self) -> impl Iterator<Item = (&String, &V)> {
        self.entries.iter().map(|(n, v)| (n, v))
    }
}

/// A scope of named, fully-typed variables (`fix`-declared, with types
/// inferred from the conclusion, plus binder variables introduced by proof
/// rules). Implicit/unannotated variables are resolved by the elaborator, not
/// here.
///
/// Variables are pushed and popped in **groups**: [`Scope::open`] starts a
/// group, [`Scope::define`] adds variables to the current group, and
/// [`Scope::close`] drops the whole group at once. Scope opening/closing is
/// thus separate from variable definition. Shadowing is correct — defining a
/// name that already binds an outer variable hides it until the inner group
/// closes, at which point the outer binding is restored.
#[derive(Clone)]
pub struct Scope {
    table: SymbolTable<Type>,
    /// Boundary stack: the table length captured at each [`Scope::open`].
    groups: Vec<usize>,
}

impl Default for Scope {
    fn default() -> Self {
        Scope::new()
    }
}

impl Scope {
    /// An empty scope.
    pub fn new() -> Self {
        Scope {
            table: SymbolTable::new(),
            groups: Vec::new(),
        }
    }

    /// A scope holding a single root group of `vars` (the `fix`-declared
    /// variables of a theorem).
    pub fn with_vars(vars: impl IntoIterator<Item = (String, Type)>) -> Self {
        let mut s = Scope::new();
        for (n, t) in vars {
            s.define(n, t);
        }
        s
    }

    /// Start a new variable group.
    pub fn open(&mut self) {
        self.groups.push(self.table.len());
    }

    /// Drop the innermost group and every variable defined in it.
    pub fn close(&mut self) {
        let boundary = self.groups.pop().unwrap_or(0);
        self.table.truncate(boundary);
    }

    /// Define a variable in the current group.
    pub fn define(&mut self, name: impl Into<String>, ty: Type) {
        self.table.push(name.into(), ty);
    }

    /// Look up a variable's type by name (the innermost binding).
    pub fn get(&self, name: &str) -> Option<&Type> {
        self.table.get(name)
    }

    /// The variables in scope, in binder order (including shadowed ones).
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Type)> {
        self.table.iter()
    }

    /// The number of variables in scope (shadowed bindings included).
    pub fn len(&self) -> usize {
        self.table.len()
    }

    /// Whether the scope holds no variables.
    pub fn is_empty(&self) -> bool {
        self.table.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n() -> Type {
        Type::nat()
    }
    fn b() -> Type {
        Type::bool()
    }

    #[test]
    fn symbol_table_get_is_innermost() {
        let mut t: SymbolTable<Type> = SymbolTable::new();
        assert!(t.get("x").is_none());
        t.push("x".into(), n());
        assert_eq!(t.get("x"), Some(&n()));
        // shadow `x` with a bool binding — lookup must see the newer one.
        t.push("x".into(), b());
        assert_eq!(t.get("x"), Some(&b()));
        assert_eq!(t.len(), 2, "shadowing keeps both entries");
    }

    #[test]
    fn symbol_table_truncate_restores_shadowed() {
        let mut t: SymbolTable<Type> = SymbolTable::new();
        t.push("x".into(), n()); // pos 0
        t.push("y".into(), n()); // pos 1
        t.push("x".into(), b()); // pos 2 — shadows pos 0
        assert_eq!(t.get("x"), Some(&b()));
        // undo back to two entries: the inner `x` (bool) disappears, the
        // outer `x` (nat) is restored, `y` remains.
        t.truncate(2);
        assert_eq!(t.get("x"), Some(&n()));
        assert_eq!(t.get("y"), Some(&n()));
        assert_eq!(t.len(), 2);
        // undo everything.
        t.truncate(0);
        assert!(t.get("x").is_none());
        assert!(t.get("y").is_none());
        assert_eq!(t.len(), 0);
    }

    #[test]
    fn symbol_table_iter_is_insertion_order_with_dups() {
        let mut t: SymbolTable<Type> = SymbolTable::new();
        t.push("a".into(), n());
        t.push("b".into(), b());
        t.push("a".into(), b());
        let got: Vec<(&str, &Type)> = t.iter().map(|(s, v)| (s.as_str(), v)).collect();
        assert_eq!(got, vec![("a", &n()), ("b", &b()), ("a", &b())]);
    }

    #[test]
    fn symbol_table_index_is_pruned_when_empty() {
        let mut t: SymbolTable<Type> = SymbolTable::new();
        t.push("x".into(), n());
        t.truncate(0);
        // After removing the only `x` binding, its index entry is gone (so a
        // re-push starts a fresh stack rather than appending to a stale one).
        assert!(t.index.get("x").is_none());
        t.push("x".into(), b());
        assert_eq!(t.get("x"), Some(&b()));
    }

    #[test]
    fn scope_groups_open_define_close() {
        let mut s = Scope::new();
        s.define("root", n());
        s.open();
        s.define("a", b());
        s.define("c", n());
        assert_eq!(s.len(), 3);
        assert_eq!(s.get("a"), Some(&b()));
        s.close();
        // the whole inner group is gone; the root binding stays.
        assert_eq!(s.len(), 1);
        assert!(s.get("a").is_none());
        assert!(s.get("c").is_none());
        assert_eq!(s.get("root"), Some(&n()));
    }

    #[test]
    fn scope_close_restores_shadowed_outer() {
        let mut s = Scope::new();
        s.define("x", n());
        s.open();
        s.define("x", b()); // shadow within the inner group
        assert_eq!(s.get("x"), Some(&b()));
        s.close();
        assert_eq!(s.get("x"), Some(&n()), "outer x restored on close");
    }

    #[test]
    fn scope_nested_groups_unwind_in_order() {
        let mut s = Scope::new();
        s.open();
        s.define("a", n());
        s.open();
        s.define("a", b()); // nested shadow
        s.define("d", n());
        assert_eq!(s.get("a"), Some(&b()));
        assert_eq!(s.get("d"), Some(&n()));
        s.close(); // pop the inner group
        assert_eq!(s.get("a"), Some(&n()));
        assert!(s.get("d").is_none());
        s.close(); // pop the outer group
        assert!(s.get("a").is_none());
        assert!(s.is_empty());
    }

    #[test]
    fn scope_close_without_open_clears_to_root() {
        // Defensive: closing with no matching open truncates to zero rather
        // than panicking.
        let mut s = Scope::new();
        s.define("x", n());
        s.close();
        assert!(s.is_empty());
    }

    #[test]
    fn scope_with_vars_seeds_root_group() {
        let s = Scope::with_vars([("p".to_string(), b()), ("q".to_string(), b())]);
        assert_eq!(s.len(), 2);
        assert_eq!(s.get("p"), Some(&b()));
        assert_eq!(s.get("q"), Some(&b()));
        assert!(!s.is_empty());
    }
}

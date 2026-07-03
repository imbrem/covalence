use std::fmt;
use std::sync::Arc;

use smol_str::SmolStr;

/// Lean hierarchical name.
///
/// Names are built inductively: `Nat.add` = `Str(Str(Anon, "Nat"), "add")`.
/// Uses `Arc` for sharing — the same prefix appears thousands of times in a
/// mathlib export.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Name {
    /// Anonymous (root) name.
    Anon,
    /// String component: `prefix.str`.
    Str(Arc<Name>, SmolStr),
    /// Numeric component: `prefix.num`.
    Num(Arc<Name>, u64),
}

impl Name {
    /// Returns `true` if this is the anonymous (root) name.
    pub fn is_anon(&self) -> bool {
        matches!(self, Name::Anon)
    }

    /// Iterate over the components of this name from root to leaf.
    pub fn components(&self) -> Vec<NameComponent<'_>> {
        let mut parts = Vec::new();
        self.collect_components(&mut parts);
        parts.reverse();
        parts
    }

    fn collect_components<'a>(&'a self, acc: &mut Vec<NameComponent<'a>>) {
        match self {
            Name::Anon => {}
            Name::Str(prefix, s) => {
                acc.push(NameComponent::Str(s));
                prefix.collect_components(acc);
            }
            Name::Num(prefix, n) => {
                acc.push(NameComponent::Num(*n));
                prefix.collect_components(acc);
            }
        }
    }
}

/// A single component of a hierarchical name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameComponent<'a> {
    Str(&'a SmolStr),
    Num(u64),
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Anon => write!(f, "[anonymous]"),
            _ => {
                let parts = self.components();
                for (i, part) in parts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ".")?;
                    }
                    match part {
                        NameComponent::Str(s) => write!(f, "{s}")?,
                        NameComponent::Num(n) => write!(f, "{n}")?,
                    }
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn anon_display() {
        assert_eq!(Name::Anon.to_string(), "[anonymous]");
    }

    #[test]
    fn simple_name() {
        let name = Name::Str(Arc::new(Name::Anon), "Nat".into());
        assert_eq!(name.to_string(), "Nat");
    }

    #[test]
    fn dotted_name() {
        let nat = Arc::new(Name::Str(Arc::new(Name::Anon), "Nat".into()));
        let nat_add = Name::Str(nat, "add".into());
        assert_eq!(nat_add.to_string(), "Nat.add");
    }

    #[test]
    fn numeric_component() {
        let prefix = Arc::new(Name::Str(Arc::new(Name::Anon), "foo".into()));
        let name = Name::Num(prefix, 42);
        assert_eq!(name.to_string(), "foo.42");
    }

    #[test]
    fn name_sharing() {
        let prefix = Arc::new(Name::Str(Arc::new(Name::Anon), "Nat".into()));
        let a = Name::Str(prefix.clone(), "add".into());
        let b = Name::Str(prefix.clone(), "mul".into());
        // Both share the same prefix Arc
        assert!(Arc::ptr_eq(
            match &a {
                Name::Str(p, _) => p,
                _ => unreachable!(),
            },
            match &b {
                Name::Str(p, _) => p,
                _ => unreachable!(),
            },
        ));
    }

    #[test]
    fn components() {
        let nat = Arc::new(Name::Str(Arc::new(Name::Anon), "Nat".into()));
        let nat_add = Name::Str(nat, "add".into());
        let components = nat_add.components();
        assert_eq!(components.len(), 2);
        assert_eq!(components[0], NameComponent::Str(&"Nat".into()));
        assert_eq!(components[1], NameComponent::Str(&"add".into()));
    }
}

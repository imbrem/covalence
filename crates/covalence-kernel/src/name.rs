//! Distinct name namespaces.
//!
//! The kernel keeps user-side names in separate ID spaces — a `ConstName`
//! and a `VarName` with the same string content are distinct. Builtins
//! (Bool, True, Eq, Bits, …) live as TermDef/TypeDef enum variants and
//! never appear in these tables.

use smol_str::SmolStr;

/// A free-variable name, used in `TermDef::Free` and `TermDef::Abs`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarName(SmolStr);

/// A user-declared HOL constant name, used in `TermDef::Const`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstName(SmolStr);

/// A user-declared type-constructor name, used in `TypeDef::Tyapp`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeName(SmolStr);

/// A polymorphic type-variable name, used in `TypeDef::TVar`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVarId(SmolStr);

macro_rules! name_impls {
    ($($t:ident),* $(,)?) => {
        $(
            impl $t {
                /// Build from any string-like value.
                pub fn new(s: impl AsRef<str>) -> Self {
                    Self(SmolStr::new(s.as_ref()))
                }

                /// View the underlying string.
                pub fn as_str(&self) -> &str {
                    self.0.as_str()
                }
            }

            impl From<&str> for $t {
                fn from(s: &str) -> Self {
                    Self::new(s)
                }
            }

            impl From<String> for $t {
                fn from(s: String) -> Self {
                    Self(SmolStr::new(s))
                }
            }
        )*
    };
}

name_impls!(VarName, ConstName, TypeName, TypeVarId);

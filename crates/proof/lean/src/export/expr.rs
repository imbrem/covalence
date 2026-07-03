use std::sync::Arc;

use super::level::Level;
use super::name::Name;

/// Binder annotation (how arguments are passed).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    /// Explicit argument `(x : A)`.
    Default,
    /// Implicit argument `{x : A}` (inferred by unification).
    Implicit,
    /// Strict implicit `⦃x : A⦄` (always inserted even if next arg is `_`).
    StrictImplicit,
    /// Instance implicit `[x : A]` (resolved by typeclass synthesis).
    InstImplicit,
}

/// Literal value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Nat(u64),
    Str(String),
}

/// Lean expression (CIC term).
///
/// Matches Lean's kernel expression type exactly. Uses de Bruijn indices
/// for bound variables (like `covalence-isabelle`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Bound variable (de Bruijn index).
    BVar(u32),
    /// Sort (Type u / Prop).
    Sort(Arc<Level>),
    /// Constant reference with universe arguments.
    Const(Name, Vec<Arc<Level>>),
    /// Application: `f a`.
    App(Arc<Expr>, Arc<Expr>),
    /// Lambda abstraction: `fun (x : A) => b`.
    Lam(Name, BinderInfo, Arc<Expr>, Arc<Expr>),
    /// Dependent function type (forallE): `(x : A) -> B`.
    Pi(Name, BinderInfo, Arc<Expr>, Arc<Expr>),
    /// Let binding: `let x : A := v in b`.
    Let(Name, Arc<Expr>, Arc<Expr>, Arc<Expr>),
    /// Structure projection: `s.idx` on structure type `name`.
    Proj(Name, u32, Arc<Expr>),
    /// Literal (nat or string).
    Lit(Literal),
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use smol_str::SmolStr;

    use super::*;
    use crate::Name;

    fn mk_name(s: &str) -> Name {
        Name::Str(Arc::new(Name::Anon), SmolStr::new(s))
    }

    #[test]
    fn bvar() {
        let e = Expr::BVar(0);
        assert_eq!(e, Expr::BVar(0));
    }

    #[test]
    fn sort_prop() {
        let prop = Expr::Sort(Arc::new(Level::Zero));
        match &prop {
            Expr::Sort(l) => assert_eq!(**l, Level::Zero),
            _ => panic!("expected Sort"),
        }
    }

    #[test]
    fn identity_function() {
        // fun (A : Type) (a : A) => a
        // = Lam("A", Default, Sort(1), Lam("a", Default, BVar(0), BVar(0)))
        let type1 = Arc::new(Expr::Sort(Arc::new(Level::Succ(Arc::new(Level::Zero)))));
        let inner = Arc::new(Expr::Lam(
            mk_name("a"),
            BinderInfo::Default,
            Arc::new(Expr::BVar(0)),
            Arc::new(Expr::BVar(0)),
        ));
        let id = Expr::Lam(mk_name("A"), BinderInfo::Default, type1, inner);
        match &id {
            Expr::Lam(_, BinderInfo::Default, _, body) => match body.as_ref() {
                Expr::Lam(_, BinderInfo::Default, _, body2) => {
                    assert_eq!(**body2, Expr::BVar(0));
                }
                _ => panic!("expected inner Lam"),
            },
            _ => panic!("expected Lam"),
        }
    }

    #[test]
    fn const_with_universe_args() {
        let u = Arc::new(Level::Param(mk_name("u")));
        let e = Expr::Const(mk_name("List.nil"), vec![u.clone()]);
        match &e {
            Expr::Const(name, levels) => {
                assert_eq!(name.to_string(), "List.nil");
                assert_eq!(levels.len(), 1);
            }
            _ => panic!("expected Const"),
        }
    }

    #[test]
    fn literal() {
        let n = Expr::Lit(Literal::Nat(42));
        let s = Expr::Lit(Literal::Str("hello".to_string()));
        assert_ne!(n, s);
    }
}

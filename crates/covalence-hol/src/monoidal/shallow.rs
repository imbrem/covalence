//! The **shallow** embedding of the coproduct's monoidal structure into
//! HOL: the [`Monoidal`] impl on [`Hol`].
//!
//! [`Hol`] itself — the zero-sized handle and its [`Category`] impl —
//! lives in [`crate::category::shallow`]; this module adds the coproduct
//! layer. Every axiom forwards to a genuine, hypothesis-free theorem: the
//! coproduct universal property (β-laws + η/fusion) to
//! [`init::coprod`](mod@crate::init::coprod). So a shallow point-free
//! proof is an outright HOL theorem — nothing is postulated.

use covalence_core::defs::coprod_spec;
use covalence_core::{Error, Result, Term, Thm, Type, TypeKind};

use crate::category::{Category, Hol};
use crate::init::ext::TermExt;
use crate::init::{cat, coprod};
use crate::monoidal::Monoidal;

/// Split `α → β` into `(α, β)`.
fn fun_parts(ty: &Type) -> Result<(Type, Type)> {
    match ty.kind() {
        TypeKind::Fun(dom, cod) => Ok((dom.clone(), cod.clone())),
        _ => Err(Error::NotFunction(ty.clone())),
    }
}

impl Hol {
    /// `[f, g] : a ⊕ b → c` as a raw term (`f : a → c`, `g : b → c`).
    fn copair_term(&self, f: &Term, g: &Term) -> Result<Term> {
        let (a, c) = fun_parts(&f.type_of()?)?;
        let (b, _c) = fun_parts(&g.type_of()?)?;
        coprod::coprod_case(a, b, c)
            .apply(f.clone())?
            .apply(g.clone())
    }
}

impl Monoidal for Hol {
    // ---- objects ----

    fn oplus(&self, a: Type, b: Type) -> Type {
        coprod::coprod(a, b)
    }

    // ---- morphisms: coproduct join morphisms ----

    fn inl(&self, a: Type, b: Type) -> Term {
        coprod::inl(a, b)
    }

    fn inr(&self, a: Type, b: Type) -> Term {
        coprod::inr(a, b)
    }

    fn copair(&self, f: Term, g: Term) -> Result<Term> {
        self.copair_term(&f, &g)
    }

    fn bimap(&self, f: Term, g: Term) -> Result<Term> {
        // f : a → a', g : b → b'  ⟹  f ⊕ g = [inl' ∘ f, inr' ∘ g].
        let (_a, a2) = fun_parts(&f.type_of()?)?;
        let (_b, b2) = fun_parts(&g.type_of()?)?;
        let inl2 = self.inl(a2.clone(), b2.clone());
        let inr2 = self.inr(a2, b2);
        let left = cat::comp(&inl2, &f)?;
        let right = cat::comp(&inr2, &g)?;
        self.copair_term(&left, &right)
    }

    fn swap(&self, a: Type, b: Type) -> Result<Term> {
        // σ : a ⊕ b → b ⊕ a = [inr_{b,a}, inl_{b,a}].
        let left = self.inr(b.clone(), a.clone()); // a → b ⊕ a
        let right = self.inl(b, a); // b → b ⊕ a
        self.copair_term(&left, &right)
    }

    fn codiag(&self, a: Type) -> Result<Term> {
        let id = self.id(a);
        self.copair_term(&id, &id)
    }

    // ---- axioms: coproduct universal property ----

    fn copair_inl(&self, f: Term, g: Term) -> Result<Thm> {
        // ⊢ [f, g] ∘ inl = f, via the pointwise β-law + extensionality.
        let (a, c) = fun_parts(&f.type_of()?)?;
        let (b, _c) = fun_parts(&g.type_of()?)?;
        let cp = self.copair_term(&f, &g)?;
        let lhs = cat::comp(&cp, &self.inl(a.clone(), b.clone()))?;
        let x = Term::free("__cpx", a.clone());
        let app_eq = cat::comp_beta(&lhs, &x)? // ⊢ ([f,g]∘inl) x = [f,g](inl x)
            .trans(coprod::case_inl(&a, &b, &c, &f, &g, &x)?)?; // ⊢ … = f x
        cat::fun_ext(app_eq, "__cpx", &a)
    }

    fn copair_inr(&self, f: Term, g: Term) -> Result<Thm> {
        let (a, c) = fun_parts(&f.type_of()?)?;
        let (b, _c) = fun_parts(&g.type_of()?)?;
        let cp = self.copair_term(&f, &g)?;
        let lhs = cat::comp(&cp, &self.inr(a.clone(), b.clone()))?;
        let y = Term::free("__cpy", b.clone());
        let app_eq = cat::comp_beta(&lhs, &y)?
            .trans(coprod::case_inr(&a, &b, &c, &f, &g, &y)?)?;
        cat::fun_ext(app_eq, "__cpy", &b)
    }

    fn fusion(&self, m: Term) -> Result<Thm> {
        // m : a ⊕ b → c.
        let (dom, c) = fun_parts(&m.type_of()?)?;
        let (a, b) = coprod_parts(&dom)?;
        coprod::case_eta(&a, &b, &c, &m)
    }

    // ---- inference rules: coproduct congruence ----

    fn copair_cong(&self, f_eq: Thm, g_eq: Thm) -> Result<Thm> {
        // ⊢ [f, g] = [f', g'] by congruence on `coprod_case`.
        let (f, _f2) = f_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
        let (g, _g2) = g_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
        let (a, c) = fun_parts(&f.type_of()?)?;
        let (b, _c) = fun_parts(&g.type_of()?)?;
        Thm::refl(coprod::coprod_case(a, b, c))?
            .cong_app(f_eq)?
            .cong_app(g_eq)
    }
}

/// Split a `coprod a b` type into `(a, b)` (the domain of a map out of a
/// coproduct). Errors unless `ty` really is a `coprod` instance.
fn coprod_parts(ty: &Type) -> Result<(Type, Type)> {
    match ty.kind() {
        TypeKind::Spec(spec, args) if spec.ptr_eq(&coprod_spec()) && args.len() == 2 => {
            Ok((args[0].clone(), args[1].clone()))
        }
        _ => Err(Error::TypeMismatch {
            expected: coprod::coprod(Type::tfree("a"), Type::tfree("b")),
            got: ty.clone(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn obj(n: &str) -> Type {
        Type::tfree(n)
    }

    fn hol() -> Hol {
        Hol::new()
    }

    #[test]
    fn copair_beta_laws_are_genuine() {
        let h = hol();
        let (a, b, c) = (obj("a"), obj("b"), obj("c"));
        let f = Term::free("f", Type::fun(a.clone(), c.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let l = h.copair_inl(f.clone(), g.clone()).unwrap();
        let r = h.copair_inr(f.clone(), g.clone()).unwrap();
        assert!(l.hyps().is_empty() && l.has_no_obs());
        assert!(r.hyps().is_empty() && r.has_no_obs());
        // [f,g] ∘ inl = f  and  [f,g] ∘ inr = g.
        assert_eq!(h.concl(&l).1, f);
        assert_eq!(h.concl(&r).1, g);
    }

    #[test]
    fn fusion_is_genuine() {
        let h = hol();
        let (a, b, c) = (obj("a"), obj("b"), obj("c"));
        let m = Term::free("m", Type::fun(h.oplus(a, b), c));
        let p = h.fusion(m.clone()).unwrap();
        assert!(p.hyps().is_empty() && p.has_no_obs());
        assert_eq!(h.concl(&p).0, m);
    }

    #[test]
    fn derived_swap_involution_is_genuine() {
        // ⊢ σ_{b,a} ∘ σ_{a,b} = id, proved through the trait API only.
        use crate::monoidal::derived::swap_involution;
        let h = hol();
        let (a, b) = (obj("a"), obj("b"));
        let p = swap_involution(&h, a.clone(), b.clone()).unwrap();
        assert!(p.hyps().is_empty(), "derived from proved axioms only");
        assert!(p.has_no_obs());
        // RHS is the identity on a ⊕ b.
        let (_lhs, rhs) = h.concl(&p);
        assert_eq!(rhs, h.id(h.oplus(a, b)));
    }

    #[test]
    fn derived_swap_injection_laws() {
        use crate::monoidal::derived::{swap_inl, swap_inr};
        let h = hol();
        let (a, b) = (obj("a"), obj("b"));
        // σ∘inl = inr, σ∘inr = inl.
        let l = swap_inl(&h, a.clone(), b.clone()).unwrap();
        let r = swap_inr(&h, a.clone(), b.clone()).unwrap();
        assert_eq!(h.concl(&l).1, h.inr(b.clone(), a.clone()));
        assert_eq!(h.concl(&r).1, h.inl(b, a));
    }

    #[test]
    fn structural_morphisms_typecheck() {
        let h = hol();
        let (a, b) = (obj("a"), obj("b"));
        // swap : a⊕b → b⊕a, codiag : a⊕a → a, bimap of ids.
        let sw = h.swap(a.clone(), b.clone()).unwrap();
        assert_eq!(
            sw.type_of().unwrap(),
            Type::fun(h.oplus(a.clone(), b.clone()), h.oplus(b.clone(), a.clone()))
        );
        let nabla = h.codiag(a.clone()).unwrap();
        assert_eq!(nabla.type_of().unwrap(), Type::fun(h.oplus(a.clone(), a.clone()), a.clone()));
        let bi = h
            .bimap(h.id(a.clone()), h.id(b.clone()))
            .unwrap();
        assert_eq!(
            bi.type_of().unwrap(),
            Type::fun(h.oplus(a.clone(), b.clone()), h.oplus(a, b))
        );
    }
}

//! `cat` — the **category** structure on HOL functions, point-free.
//!
//! HOL types are the objects and total functions `α → β` are the
//! morphisms of a category: composition is [`compose`] (`fun.compose`,
//! `λg f x. g (f x)`) and the identities are [`id`] (`fun.id`, `λx. x`).
//! These combinators already live in `defs/fun.rs`; this module pairs
//! them with the three **category laws** as genuine, hypothesis- and
//! oracle-free HOL theorems:
//!
//! ```text
//!     ⊢ id ∘ f = f            (id_left)
//!     ⊢ f ∘ id = f            (id_right)
//!     ⊢ (h ∘ g) ∘ f = h ∘ (g ∘ f)   (comp_assoc)
//! ```
//!
//! Each is proved the point-free way: apply both sides to a fresh point,
//! δ-unfold `compose` / `id` and β-reduce to a common applicative normal
//! form, then re-abstract and η-contract (function extensionality, built
//! from [`Thm::abs`] + [`Thm::eta_conv`]). The same machinery is exposed
//! as [`comp`] (typed composition of two morphism *terms*) and
//! [`comp_cong`] (the congruence that lets composition act on equational
//! proofs), which the higher-level
//! [`monoidal`](crate::monoidal) API builds on.

use covalence_core::{Error, Result, Term, Thm, Type, TypeKind};

use crate::init::ext::{TermExt, ThmExt};

pub use covalence_core::defs::{compose, compose_spec, flip, id, id_spec, konst};

// ============================================================================
// Typed composition of morphism terms.
// ============================================================================

/// Split a function type `α → β` into `(α, β)`.
fn fun_parts(ty: &Type) -> Result<(Type, Type)> {
    match ty.kind() {
        TypeKind::Fun(dom, cod) => Ok((dom.clone(), cod.clone())),
        _ => Err(Error::NotBool(ty.clone())),
    }
}

/// `g ∘ f` — [`compose`] instantiated at the types read off `f : α → β`
/// and `g : β → γ`. Errors if either is not a function or the middle
/// objects disagree.
pub fn comp(g: &Term, f: &Term) -> Result<Term> {
    let (alpha, beta) = fun_parts(&f.type_of()?)?;
    let (beta2, gamma) = fun_parts(&g.type_of()?)?;
    if beta != beta2 {
        return Err(Error::TypeMismatch {
            expected: Type::fun(beta, gamma),
            got: g.type_of()?,
        });
    }
    compose(alpha, beta2, gamma)
        .apply(g.clone())?
        .apply(f.clone())
}

// ============================================================================
// Point-free normalisation + function extensionality.
// ============================================================================

/// `⊢ t = nf`, the applicative normal form of a `compose` / `id` term:
/// δ-unfold every `compose`, β-reduce, δ-unfold every `id`, β-reduce.
/// Free morphism variables and other heads are left untouched, so a term
/// like `(h ∘ g) ∘ f) x` lands on `h (g (f x))`.
fn normalize(t: &Term) -> Result<Thm> {
    let compose_spec = compose_spec();
    let id_spec = id_spec();
    t.delta_all(compose_spec.symbol())?
        .rhs_conv(|r| r.reduce())?
        .rhs_conv(|r| r.delta_all(id_spec.symbol()))?
        .rhs_conv(|r| r.reduce())
}

/// Prove `⊢ lhs = rhs` for two morphisms `α → β` that share an
/// applicative normal form, by extensionality: both `lhs x` and `rhs x`
/// [`normalize`] to the same term, then re-abstract and η-contract.
///
/// `lhs` / `rhs` must not contain a free `__catx` variable (they are
/// closed combinators over the caller's morphism variables, so this
/// holds).
fn ext_eq(lhs: Term, rhs: Term, alpha: &Type) -> Result<Thm> {
    let x = Term::free("__catx", alpha.clone());
    let l_nf = normalize(&Term::app(lhs, x.clone()))?; // ⊢ lhs x = nf
    let r_nf = normalize(&Term::app(rhs, x))?; // ⊢ rhs x = nf
    let app_eq = l_nf.trans(r_nf.sym()?)?; // ⊢ lhs x = rhs x
    fun_ext(app_eq, "__catx", alpha)
}

/// Function extensionality. From `⊢ lhs x = rhs x` — where `x =
/// Free(name, α)` is not free in `lhs` / `rhs` — derive `⊢ lhs = rhs` by
/// re-abstracting and η-contracting both sides. The point variable can be
/// any chosen fresh name; callers building the pointwise equation supply
/// it.
pub fn fun_ext(app_eq: Thm, name: &str, alpha: &Type) -> Result<Thm> {
    let abs_eq = app_eq.abs(name, alpha.clone())?; // ⊢ (λx. lhs x) = (λx. rhs x)
    let (l_abs, r_abs) = {
        let (l, r) = abs_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
        (l.clone(), r.clone())
    };
    let eta_l = Thm::eta_conv(l_abs)?; // ⊢ (λx. lhs x) = lhs
    let eta_r = Thm::eta_conv(r_abs)?; // ⊢ (λx. rhs x) = rhs
    eta_l.sym()?.trans(abs_eq)?.trans(eta_r)
}

// ============================================================================
// The category laws.
// ============================================================================

/// `⊢ id ∘ f = f` — left identity. `f : α → β`, `id` at `β`.
pub fn id_left(f: &Term) -> Result<Thm> {
    let (alpha, beta) = fun_parts(&f.type_of()?)?;
    let lhs = comp(&id(beta), f)?;
    ext_eq(lhs, f.clone(), &alpha)
}

/// `⊢ f ∘ id = f` — right identity. `f : α → β`, `id` at `α`.
pub fn id_right(f: &Term) -> Result<Thm> {
    let (alpha, _beta) = fun_parts(&f.type_of()?)?;
    let lhs = comp(f, &id(alpha.clone()))?;
    ext_eq(lhs, f.clone(), &alpha)
}

/// `⊢ (h ∘ g) ∘ f = h ∘ (g ∘ f)` — associativity. `f : α → β`,
/// `g : β → γ`, `h : γ → δ`.
pub fn comp_assoc(h: &Term, g: &Term, f: &Term) -> Result<Thm> {
    let (alpha, _beta) = fun_parts(&f.type_of()?)?;
    let lhs = comp(&comp(h, g)?, f)?;
    let rhs = comp(h, &comp(g, f)?)?;
    ext_eq(lhs, rhs, &alpha)
}

/// `⊢ (g ∘ f) x = g (f x)` — δβ-unfold a single composition applied to a
/// point. Only the **outermost** `∘` is reduced (via [`delta_head`]), so
/// `g` / `f` may themselves contain compositions (or copairings) that are
/// left intact — essential when reducing composites of structure
/// morphisms.
pub fn comp_beta(gf: &Term, x: &Term) -> Result<Thm> {
    crate::init::eq::delta_head(&Term::app(gf.clone(), x.clone()))?.rhs_conv(|t| t.reduce())
}

// ============================================================================
// Congruence — composition acting on equational proofs.
// ============================================================================

/// From `⊢ g = g'` and `⊢ f = f'` conclude `⊢ g ∘ f = g' ∘ f'` — the
/// bifunctoriality of `∘` on morphisms, i.e. the congruence that lets a
/// proof be whiskered on either side. `f : α → β`, `g : β → γ`.
pub fn comp_cong(g_eq: &Thm, f_eq: &Thm) -> Result<Thm> {
    let (g, _g2) = g_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let (f, _f2) = f_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let (alpha, beta) = fun_parts(&f.type_of()?)?;
    let (_beta2, gamma) = fun_parts(&g.type_of()?)?;
    Thm::refl(compose(alpha, beta, gamma))?
        .cong_app(g_eq.clone())?
        .cong_app(f_eq.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ab() -> (Type, Type) {
        (Type::tfree("a"), Type::tfree("b"))
    }

    #[test]
    fn id_left_is_genuine() {
        let (a, b) = ab();
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let thm = id_left(&f).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let lhs = comp(&id(b), &f).unwrap();
        assert_eq!(thm.concl(), &lhs.equals(f).unwrap());
    }

    #[test]
    fn id_right_is_genuine() {
        let (a, b) = ab();
        let f = Term::free("f", Type::fun(a.clone(), b));
        let thm = id_right(&f).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let lhs = comp(&f, &id(a)).unwrap();
        assert_eq!(thm.concl(), &lhs.equals(f).unwrap());
    }

    #[test]
    fn comp_assoc_is_genuine() {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let d = Type::tfree("d");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let h = Term::free("h", Type::fun(c, d));
        let thm = comp_assoc(&h, &g, &f).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        let lhs = comp(&comp(&h, &g).unwrap(), &f).unwrap();
        let rhs = comp(&h, &comp(&g, &f).unwrap()).unwrap();
        assert_eq!(thm.concl(), &lhs.equals(rhs).unwrap());
    }

    #[test]
    fn comp_cong_whiskers_both_sides() {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let g = Term::free("g", Type::fun(b, c));
        let f_eq = Thm::refl(f.clone()).unwrap();
        let g_eq = Thm::refl(g.clone()).unwrap();
        let thm = comp_cong(&g_eq, &f_eq).unwrap();
        let expected = comp(&g, &f).unwrap();
        assert_eq!(thm.concl(), &expected.clone().equals(expected).unwrap());
    }
}

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
//! [`monoidal`](crate::algebra::monoidal) API builds on.

use covalence_core::{Error, Result, Term, Type, TypeKind};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::ext::{TermExt, ThmExt};
use crate::script::{ConstDef, Env};

pub use covalence_hol_eval::defs::{compose, compose_spec, flip, id, id_spec, konst};

// ============================================================================
// Typed composition of morphism terms.
// ============================================================================

/// Split a function type `α → β` into `(α, β)`.
fn fun_parts(ty: &Type) -> Result<(Type, Type)> {
    match ty.kind() {
        TypeKind::Fun(dom, cod) => Ok((dom.clone(), cod.clone())),
        _ => Err(Error::NotFunction(ty.clone())),
    }
}

/// `g ∘ f` — [`compose`] instantiated at the types read off `f : α → β`
/// and `g : β → γ`. Errors if either is not a function or the middle
/// objects disagree.
pub fn comp(g: &Term, f: &Term) -> Result<Term> {
    let g_ty = g.type_of()?;
    let (alpha, beta) = fun_parts(&f.type_of()?)?;
    let (beta2, gamma) = fun_parts(&g_ty)?;
    if beta != beta2 {
        return Err(Error::TypeMismatch {
            expected: Type::fun(beta, gamma),
            got: g_ty,
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
/// like `((h ∘ g) ∘ f) x` lands on `h (g (f x))`.
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
/// point. Only the **outermost** `∘` is reduced (via [`delta_head`](crate::init::eq::delta_head)), so
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

// ============================================================================
// Categorical normalizer — the function-category rewriter.
// ============================================================================

/// If `t` is `compose g f` (the `fun.compose` head applied to two morphisms),
/// return `(g, f)`. Detected by the spec symbol so it matches at *any* triple
/// of objects `(α, β, γ)` — the heterogeneous-object case the single-carrier
/// [`monoid`](crate::init::monoid) normalizer can't express.
fn dest_comp(t: &Term) -> Option<(Term, Term)> {
    let (gf, f) = t.as_app()?;
    let (head, g) = gf.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.symbol()
        .label()
        .eq(compose_spec().symbol().label())
        .then(|| (g.clone(), f.clone()))
}

/// Whether `t` is an identity morphism `id` at some object (any `α`).
fn is_id(t: &Term) -> bool {
    t.as_spec()
        .is_some_and(|(spec, _)| spec.symbol().label() == id_spec().symbol().label())
}

/// **The categorical rewriter** for the function category: `⊢ t = nf`, where
/// `nf` is `t` with every composite **right-associated** and every `id` factor
/// eliminated. The general (heterogeneous-object) analogue of
/// [`monoid::Monoid::normalize`](crate::init::monoid::Monoid::normalize): each
/// step is a genuine kernel rewrite via the *type-inferring* category laws
/// [`comp_assoc`] / [`id_left`] / [`id_right`] and the congruence [`comp_cong`],
/// so it works on `(h ∘ g) ∘ f` even when `f : α→β`, `g : β→γ`, `h : γ→δ` all
/// differ — where a fixed monoid `op` term would not type-check.
///
/// Mirrors the monoid algorithm: normalize children, drop `id`, re-associate a
/// left-nested composite, recurse on the new right child.
pub fn cat_normalize(t: &Term) -> Result<Thm> {
    let Some((g, f)) = dest_comp(t) else {
        return Thm::refl(t.clone());
    };

    let g_eq = cat_normalize(&g)?; // ⊢ g = g'
    let f_eq = cat_normalize(&f)?; // ⊢ f = f'
    let (_, g_nf) = g_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let (_, f_nf) = f_eq.concl().as_eq().ok_or(Error::NotAnEquation)?;
    let (g_nf, f_nf) = (g_nf.clone(), f_nf.clone());

    // ⊢ g ∘ f = g' ∘ f'  (whisker both sides).
    let cong = comp_cong(&g_eq, &f_eq)?;

    // id ∘ f' → f'   (left identity).
    if is_id(&g_nf) {
        return cong.trans(id_left(&f_nf)?);
    }
    // g' ∘ id → g'   (right identity).
    if is_id(&f_nf) {
        return cong.trans(id_right(&g_nf)?);
    }
    // Re-associate: (p ∘ q) ∘ f' → p ∘ (q ∘ f').
    if let Some((p, q)) = dest_comp(&g_nf) {
        let assoc = comp_assoc(&p, &q, &f_nf)?; // ⊢ (p∘q)∘f' = p∘(q∘f')
        let inner = comp(&q, &f_nf)?;
        let inner_nf = cat_normalize(&inner)?; // ⊢ q∘f' = (q∘f')'
        let right = comp_cong(&Thm::refl(p)?, &inner_nf)?; // ⊢ p∘(q∘f') = p∘(q∘f')'
        return cong.trans(assoc)?.trans(right);
    }
    Ok(cong)
}

/// Decide a function-category word equation `⊢ lhs = rhs` by normalizing both
/// sides to canonical (right-associated, `id`-free) form and bridging. Errors
/// (in `trans`) if the two composites are not equal as categorical words.
pub fn cat_prove_eq(lhs: &Term, rhs: &Term) -> Result<Thm> {
    let l = cat_normalize(lhs)?;
    let r = cat_normalize(rhs)?;
    l.trans(r.sym()?)
}

// ============================================================================
// .cov proof language support
// ============================================================================

/// The primitives environment for `cat.cov`: just the composition operators.
///
/// `compose` / `id` are registered as `ConstDef::Poly`, so each use site
/// instantiates their free type variables with fresh metavariables — letting
/// `id` appear at `'a` and `'b` within one term (the polymorphism that
/// `id_left` / `id_right` / `comp_assoc` rely on).
///
/// Every category law (`fun_ext`, `comp_beta`, `comp_cong`, `id_beta`,
/// `id_left`, `id_right`, `comp_assoc`) is proved in `cat.cov` directly;
/// none is supplied here as a Rust given.
pub fn cat_env() -> Env {
    let a = Type::tfree("a");
    let b = Type::tfree("b");
    let c = Type::tfree("c");
    let mut e = Env::empty();
    e.define_const(
        "compose",
        ConstDef::Poly(compose(a.clone(), b.clone(), c.clone())),
    );
    e.define_const("id", ConstDef::Poly(id(a.clone())));
    e
}

// Universally-quantified wrappers matching the `.cov` theorem statements.

cached_thm! {
    /// `⊢ ∀(f:'a→'b)(g:'a→'b). (∀x:'a. f x = g x) ⟹ (f = g)`
    pub fn fun_ext_thm() -> Thm {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let g_var = Term::free("g", Type::fun(a.clone(), b.clone()));
        let x = Term::free("x", a.clone());
        // Build the hypothesis: ∀(x:'a). f x = g x
        let hyp = Term::app(f.clone(), x.clone())
            .equals(Term::app(g_var.clone(), x.clone()))
            .and_then(|eq| eq.forall("x", a.clone()))
            .expect("fun_ext_thm: build hyp");
        // Discharge by assuming the hyp, all-elim at x, then fun_ext
        let hyp_thm = Thm::assume(hyp.clone()).expect("fun_ext_thm: assume");
        let app_eq = hyp_thm.all_elim(x).expect("fun_ext_thm: all_elim");
        fun_ext(app_eq, "x", &a)
            .and_then(|t| t.imp_intro(&hyp))
            .and_then(|t| t.all_intro("g", Type::fun(a.clone(), b.clone())))
            .and_then(|t| t.all_intro("f", Type::fun(a.clone(), b.clone())))
            .expect("fun_ext_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(g:'b→'c)(f:'a→'b)(x:'a). compose g f x = g (f x)`
    pub fn comp_beta_thm() -> Thm {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let x = Term::free("x", a.clone());
        let gf = comp(&g, &f).expect("comp_beta_thm: comp");
        comp_beta(&gf, &x)
            .and_then(|t| t.all_intro("x", a.clone()))
            .and_then(|t| t.all_intro("f", Type::fun(a.clone(), b.clone())))
            .and_then(|t| t.all_intro("g", Type::fun(b.clone(), c.clone())))
            .expect("comp_beta_thm")
    }
}

cached_thm! {
    /// `⊢ ∀g g' f f'. (g=g') ⟹ (f=f') ⟹ (compose g f = compose g' f')`
    pub fn comp_cong_thm() -> Thm {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let g2 = Term::free("g2", Type::fun(b.clone(), c.clone()));
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let f2 = Term::free("f2", Type::fun(a.clone(), b.clone()));
        let g_eq_g2 = g.clone().equals(g2.clone()).expect("comp_cong_thm: g=g2");
        let f_eq_f2 = f.clone().equals(f2.clone()).expect("comp_cong_thm: f=f2");
        let g_thm = Thm::assume(g_eq_g2.clone()).expect("comp_cong_thm: assume g");
        let f_thm = Thm::assume(f_eq_f2.clone()).expect("comp_cong_thm: assume f");
        comp_cong(&g_thm, &f_thm)
            .and_then(|t| t.imp_intro(&f_eq_f2))
            .and_then(|t| t.imp_intro(&g_eq_g2))
            .and_then(|t| t.all_intro("f2", Type::fun(a.clone(), b.clone())))
            .and_then(|t| t.all_intro("f", Type::fun(a.clone(), b.clone())))
            .and_then(|t| t.all_intro("g2", Type::fun(b.clone(), c.clone())))
            .and_then(|t| t.all_intro("g", Type::fun(b.clone(), c.clone())))
            .expect("comp_cong_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(f:'a→'b). compose id f = f`
    pub fn id_left_thm() -> Thm {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        id_left(&f)
            .and_then(|t| t.all_intro("f", Type::fun(a.clone(), b.clone())))
            .expect("id_left_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(f:'a→'b). compose f id = f`
    pub fn id_right_thm() -> Thm {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        id_right(&f)
            .and_then(|t| t.all_intro("f", Type::fun(a.clone(), b.clone())))
            .expect("id_right_thm")
    }
}

cached_thm! {
    /// `⊢ ∀(h:'c→'d)(g:'b→'c)(f:'a→'b).
    ///      compose (compose h g) f = compose h (compose g f)`
    pub fn comp_assoc_thm() -> Thm {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let d = Type::tfree("d");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let h = Term::free("h", Type::fun(c.clone(), d.clone()));
        comp_assoc(&h, &g, &f)
            .and_then(|t| t.all_intro("f", Type::fun(a.clone(), b.clone())))
            .and_then(|t| t.all_intro("g", Type::fun(b.clone(), c.clone())))
            .and_then(|t| t.all_intro("h", Type::fun(c.clone(), d.clone())))
            .expect("comp_assoc_thm")
    }
}

crate::cov_theory! {
    /// cat lemmas ported to `cat.cov`, over `core` + the `catprim` env.
    pub mod cov from "cat.cov" {
        import "core" = crate::script::Env::core();
        import "catprim" = crate::init::cat::cat_env();
        "fun.ext"    => pub fn fun_ext_cov;
        "comp.beta"  => pub fn comp_beta_cov;
        "comp.cong"  => pub fn comp_cong_cov;
        "id.left"    => pub fn id_left_cov;
        "id.right"   => pub fn id_right_cov;
        "comp.assoc" => pub fn comp_assoc_cov;
    }
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
        assert!(thm.hyps().is_empty());
        let lhs = comp(&id(b), &f).unwrap();
        assert_eq!(thm.concl(), &lhs.equals(f).unwrap());
    }

    #[test]
    fn id_right_is_genuine() {
        let (a, b) = ab();
        let f = Term::free("f", Type::fun(a.clone(), b));
        let thm = id_right(&f).unwrap();
        assert!(thm.hyps().is_empty());
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
        assert!(thm.hyps().is_empty());
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

    // -- the categorical (function-category) rewriter ------------------------

    #[test]
    fn cat_normalize_reassociates_heterogeneous_objects() {
        // f : a→b, g : b→c, h : c→d  —  objects all differ, so this is the
        // genuinely-categorical (non-monoid) case.
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let d = Type::tfree("d");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let h = Term::free("h", Type::fun(c, d));
        // (h ∘ g) ∘ f  →  h ∘ (g ∘ f).
        let expr = comp(&comp(&h, &g).unwrap(), &f).unwrap();
        let thm = cat_normalize(&expr).unwrap();
        assert!(thm.hyps().is_empty());
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &expr);
        assert_eq!(rhs, &comp(&h, &comp(&g, &f).unwrap()).unwrap());
    }

    #[test]
    fn cat_normalize_eliminates_id() {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        // (id_b ∘ f) ∘ id_a  →  f.
        let expr = comp(&comp(&id(b), &f).unwrap(), &id(a)).unwrap();
        let thm = cat_normalize(&expr).unwrap();
        assert!(thm.hyps().is_empty());
        let (_, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(rhs, &f);
    }

    #[test]
    fn cat_prove_eq_assoc_law() {
        let a = Type::tfree("a");
        let b = Type::tfree("b");
        let c = Type::tfree("c");
        let d = Type::tfree("d");
        let f = Term::free("f", Type::fun(a.clone(), b.clone()));
        let g = Term::free("g", Type::fun(b.clone(), c.clone()));
        let h = Term::free("h", Type::fun(c, d));
        let lhs = comp(&comp(&h, &g).unwrap(), &f).unwrap();
        let rhs = comp(&h, &comp(&g, &f).unwrap()).unwrap();
        let thm = cat_prove_eq(&lhs, &rhs).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl().as_eq().unwrap(), (&lhs, &rhs));
    }

    #[test]
    fn cat_cov_matches_rust() {
        // Every ported cat lemma must state exactly what the Rust proof states.
        assert_eq!(cov::fun_ext_cov().concl(), super::fun_ext_thm().concl());
        assert_eq!(cov::comp_beta_cov().concl(), super::comp_beta_thm().concl());
        assert_eq!(cov::comp_cong_cov().concl(), super::comp_cong_thm().concl());
        assert_eq!(cov::id_left_cov().concl(), super::id_left_thm().concl());
        assert_eq!(cov::id_right_cov().concl(), super::id_right_thm().concl());
        assert_eq!(
            cov::comp_assoc_cov().concl(),
            super::comp_assoc_thm().concl()
        );
    }
}

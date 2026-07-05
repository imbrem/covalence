//! The **recursion graph**, built generically from an [`InductiveSig`].
//!
//! For an inductive type `T` with constructors `C₁ … Cₖ` and a recursor
//! result type `β`, the graph is the least relation `G : T → β → bool`
//! closed under one rule per constructor: for `Cᵢ` with arguments `x⃗`
//! (recursive ones `r⃗`, with images `b⃗`),
//!
//! ```text
//!   ∀x⃗ b⃗. (⋀ⱼ G rⱼ bⱼ) ⟹ G (Cᵢ x⃗) (fᵢ x⃗ b⃗)
//! ```
//!
//! where `fᵢ` is the *step term* for `Cᵢ`. The step receives **both** the
//! constructor's arguments and the recursive images — the *paramorphic*
//! shape (`nat`'s `natRec n (rec n)`); catamorphic folds (`listFoldr`,
//! which drops `r⃗`) are a downstream specialisation.
//!
//! Encoded impredicatively,
//!
//! ```text
//!   Graph fs t a  ≜  ∀G. closed(fs, G) ⟹ G t a
//! ```
//!
//! These are **pure term builders** — no proof. They are generic over the
//! [`Hol`] backend (`gen_*`); the bare `graph` / `closed` / … are native
//! shims so the (un-ported) callers stay unchanged. The proofs over them
//! are the engine's other layers ([`super::existence`] / [`super::uniqueness`]
//! / [`super::determinacy`], generic; the ε-assembly still `nat`-specific in
//! [`crate::init::recursion`]).

use covalence_core::{Error, Result, Term, Type};

use super::hol::{self, Hol, NativeHol};
use super::sig::{GenArg, GenConstructor, GenSig, InductiveSig};

// ============================================================================
// Generic term builders — over any `Hol`
// ============================================================================

/// `g x y`.
pub(super) fn gen_app2<H: Hol>(hol: &H, g: &H::Term, x: H::Term, y: H::Term) -> Result<H::Term> {
    hol.app(hol.app(g.clone(), x)?, y)
}

/// Apply `head` to `args` left-to-right (the identity on an empty list).
fn gen_apply_all<H: Hol>(hol: &H, head: H::Term, args: &[H::Term]) -> Result<H::Term> {
    args.iter().try_fold(head, |acc, a| hol.app(acc, a.clone()))
}

/// One constructor's clause materialised over **fresh argument / image
/// variables** (named from the constructor's binder hints) — the shared
/// backbone of both the closure clause and the per-constructor
/// graph-introduction proof ([`super::existence::graph_intro`]).
pub(super) struct GenCtorInstance<Tm> {
    /// The argument variables `x⃗`, in declaration order.
    pub args: Vec<Tm>,
    /// The constructor applied to its arguments, `C x⃗`.
    pub head: Tm,
    /// The step value `f x⃗ b⃗` — the recursor's result at this case.
    pub value: Tm,
    /// The recursive `(sub-term rⱼ, image bⱼ)` pairs, in declaration order.
    pub rec_pairs: Vec<(Tm, Tm)>,
}

/// Materialise constructor `ctor` with step term `step` over fresh
/// variables. See [`GenCtorInstance`].
pub(super) fn gen_ctor_instance<H: Hol>(
    hol: &H,
    t_ty: &H::Type,
    beta: &H::Type,
    ctor: &GenConstructor<H::Term, H::Type>,
    step: &H::Term,
) -> Result<GenCtorInstance<H::Term>> {
    let mut args = Vec::with_capacity(ctor.args.len());
    let mut rec_pairs = Vec::new();
    for arg in &ctor.args {
        let v = hol.var(arg.name(), arg.ty(t_ty));
        args.push(v.clone());
        if let Some(image) = arg.image() {
            rec_pairs.push((v, hol.var(image, beta.clone())));
        }
    }
    let head = gen_apply_all(hol, ctor.ctor.clone(), &args)?;
    let step_args: Vec<H::Term> = args
        .iter()
        .cloned()
        .chain(rec_pairs.iter().map(|(_, b)| b.clone()))
        .collect();
    let value = gen_apply_all(hol, step.clone(), &step_args)?;
    Ok(GenCtorInstance {
        args,
        head,
        value,
        rec_pairs,
    })
}

/// The closure clause for one constructor:
/// `∀x⃗ b⃗. (⋀ G rⱼ bⱼ) ⟹ G (C x⃗) (f x⃗ b⃗)` (no antecedent when the
/// constructor is non-recursive).
fn gen_clause<H: Hol>(
    hol: &H,
    t_ty: &H::Type,
    beta: &H::Type,
    ctor: &GenConstructor<H::Term, H::Type>,
    step: &H::Term,
    g: &H::Term,
) -> Result<H::Term> {
    let inst = gen_ctor_instance(hol, t_ty, beta, ctor, step)?;
    let consequent = gen_app2(hol, g, inst.head, inst.value)?;

    // antecedent (⋀ G rⱼ bⱼ), folded in only when there are recursive args
    let body = if inst.rec_pairs.is_empty() {
        consequent
    } else {
        let conjs: Vec<H::Term> = inst
            .rec_pairs
            .iter()
            .map(|(sub, img)| gen_app2(hol, g, sub.clone(), img.clone()))
            .collect::<Result<_>>()?;
        hol.imp(hol::conj(hol, &conjs)?, consequent)?
    };

    // ∀-close: images innermost, then the arguments — so the quantifier
    // prefix reads `∀ x⃗ b⃗.` left-to-right.
    let mut t = body;
    for image in ctor.args.iter().rev().filter_map(GenArg::image) {
        t = hol.forall(image, beta.clone(), t)?;
    }
    for arg in ctor.args.iter().rev() {
        t = hol.forall(arg.name(), arg.ty(t_ty), t)?;
    }
    Ok(t)
}

/// The type of the impredicative relation variable, `T → β → bool`.
pub(super) fn gen_relation_ty<H: Hol>(
    hol: &H,
    sig: &GenSig<H::Term, H::Type>,
    beta: &H::Type,
) -> H::Type {
    hol.fun_ty(sig.ty.clone(), hol.fun_ty(beta.clone(), hol.bool_ty()))
}

/// `closed(fs, G)` — `G` is closed under every constructor's recursion
/// rule: the right-associated conjunction of the per-constructor clauses.
pub(super) fn gen_closed<H: Hol>(
    hol: &H,
    sig: &GenSig<H::Term, H::Type>,
    steps: &[H::Term],
    beta: &H::Type,
    g: &H::Term,
) -> Result<H::Term> {
    if steps.len() != sig.arity() {
        return Err(Error::ConnectiveRule(format!(
            "inductive::graph::closed: {} step terms for {} constructors",
            steps.len(),
            sig.arity()
        )));
    }
    let clauses: Vec<H::Term> = sig
        .ctors
        .iter()
        .zip(steps)
        .map(|(c, s)| gen_clause(hol, &sig.ty, beta, c, s, g))
        .collect::<Result<_>>()?;
    hol::conj(hol, &clauses)
}

/// `Graph fs t a ≜ ∀G. closed(fs, G) ⟹ G t a` — the impredicative graph
/// relating `t : T` to `a : β`.
pub(super) fn gen_graph<H: Hol>(
    hol: &H,
    sig: &GenSig<H::Term, H::Type>,
    steps: &[H::Term],
    beta: &H::Type,
    t: H::Term,
    a: H::Term,
) -> Result<H::Term> {
    let g_ty = gen_relation_ty(hol, sig, beta);
    let g = hol.var(sig.relation, g_ty.clone());
    let gta = gen_app2(hol, &g, t, a)?;
    let body = hol.imp(gen_closed(hol, sig, steps, beta, &g)?, gta)?;
    hol.forall(sig.relation, g_ty, body)
}

// ============================================================================
// Native shims — `NativeHol` instantiations, so callers stay unchanged
// ============================================================================

/// One constructor's materialised clause, at the native representation.
pub(super) type CtorInstance = GenCtorInstance<Term>;

/// `g x y`. [`gen_app2`] at [`NativeHol`] (used only by this module's tests).
#[cfg(test)]
pub(super) fn app2(g: &Term, x: Term, y: Term) -> Result<Term> {
    gen_app2(&NativeHol, g, x, y)
}

/// Right-associated conjunction. [`hol::conj`] at [`NativeHol`].
pub(super) fn conj(ts: &[Term]) -> Result<Term> {
    hol::conj(&NativeHol, ts)
}

/// [`gen_ctor_instance`] at [`NativeHol`].
pub(super) fn ctor_instance(
    t_ty: &Type,
    beta: &Type,
    ctor: &super::sig::Constructor,
    step: &Term,
) -> Result<CtorInstance> {
    gen_ctor_instance(&NativeHol, t_ty, beta, ctor, step)
}

/// [`gen_relation_ty`] at [`NativeHol`].
pub(super) fn relation_ty(sig: &InductiveSig, beta: &Type) -> Type {
    gen_relation_ty(&NativeHol, sig, beta)
}

/// `gen_closed` at [`NativeHol`].
pub fn closed(sig: &InductiveSig, steps: &[Term], beta: &Type, g: &Term) -> Result<Term> {
    gen_closed(&NativeHol, sig, steps, beta, g)
}

/// `gen_graph` at [`NativeHol`].
pub fn graph(sig: &InductiveSig, steps: &[Term], beta: &Type, t: Term, a: Term) -> Result<Term> {
    gen_graph(&NativeHol, sig, steps, beta, t, a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use crate::init::inductive::sig::{Arg, Constructor};
    use crate::init::nat::{nat_succ, succ, zero};

    fn nat() -> Type {
        Type::nat()
    }

    /// The `nat` signature, mirroring [`crate::init::recursion`].
    fn nat_sig() -> InductiveSig {
        InductiveSig {
            ty: nat(),
            relation: "G",
            ctors: vec![
                Constructor::nullary(zero()),
                Constructor::new(
                    nat_succ(),
                    vec![Arg::Rec {
                        name: "m",
                        image: "b",
                    }],
                ),
            ],
        }
    }

    fn g_var() -> Term {
        Term::free("G", relation_ty(&nat_sig(), &nat()))
    }

    /// The generated `closed` reproduces the hand-written
    /// `G 0 z ∧ (∀m b. G m b ⟹ G (S m) (f m b))` byte-for-byte.
    #[test]
    fn closed_reproduces_the_nat_clause() {
        let z = Term::free("z", nat());
        let f = Term::free("f", Type::fun(nat(), Type::fun(nat(), nat())));
        let g = g_var();

        let got = closed(&nat_sig(), &[z.clone(), f.clone()], &nat(), &g).unwrap();

        // Hand-built expected term.
        let m = Term::free("m", nat());
        let b = Term::free("b", nat());
        let g0z = app2(&g, zero(), z).unwrap();
        let gmb = app2(&g, m.clone(), b.clone()).unwrap();
        let fmb = f.apply(m.clone()).unwrap().apply(b.clone()).unwrap();
        let g_succ = app2(&g, succ(m), fmb).unwrap();
        let step = gmb
            .imp(g_succ)
            .unwrap()
            .forall("b", nat())
            .unwrap()
            .forall("m", nat())
            .unwrap();
        let expected = g0z.and(step).unwrap();

        assert_eq!(got, expected);
    }

    /// The generated `graph` reproduces `∀G. closed ⟹ G n a`.
    #[test]
    fn graph_reproduces_the_nat_predicate() {
        let z = Term::free("z", nat());
        let f = Term::free("f", Type::fun(nat(), Type::fun(nat(), nat())));
        let n = Term::free("n", nat());
        let a = Term::free("a", nat());

        let got = graph(
            &nat_sig(),
            &[z.clone(), f.clone()],
            &nat(),
            n.clone(),
            a.clone(),
        )
        .unwrap();

        let g = g_var();
        let g_ty = relation_ty(&nat_sig(), &nat());
        let gna = app2(&g, n, a).unwrap();
        let expected = closed(&nat_sig(), &[z, f], &nat(), &g)
            .unwrap()
            .imp(gna)
            .unwrap()
            .forall("G", g_ty)
            .unwrap();

        assert_eq!(got, expected);
        assert!(got.type_of().unwrap().is_bool());
    }

    /// A `cons`-shaped constructor (`Param` then `Rec`) yields
    /// `∀x xs b. G xs b ⟹ G (C x xs) (f x xs b)` — the paramorphic step
    /// receives the element `x`, the sub-list `xs`, *and* its image `b`.
    #[test]
    fn mixed_param_and_rec_clause() {
        let elem = Type::bool(); // α
        let t = nat(); // stand-in for `list α`
        let beta = nat();
        let c = Term::free(
            "C",
            Type::fun(elem.clone(), Type::fun(t.clone(), t.clone())),
        );
        let f = Term::free(
            "f",
            Type::fun(
                elem.clone(),
                Type::fun(t.clone(), Type::fun(beta.clone(), beta.clone())),
            ),
        );
        let sig = InductiveSig {
            ty: t.clone(),
            relation: "G",
            ctors: vec![Constructor::new(
                c.clone(),
                vec![
                    Arg::Param {
                        ty: elem.clone(),
                        name: "x",
                    },
                    Arg::Rec {
                        name: "xs",
                        image: "b",
                    },
                ],
            )],
        };
        let g = Term::free("G", relation_ty(&sig, &beta));

        let got = closed(&sig, std::slice::from_ref(&f), &beta, &g).unwrap();

        let x = Term::free("x", elem.clone());
        let xs = Term::free("xs", t.clone());
        let b = Term::free("b", beta.clone());
        let gxsb = app2(&g, xs.clone(), b.clone()).unwrap();
        let cons = c.apply(x.clone()).unwrap().apply(xs.clone()).unwrap();
        let fval = f
            .apply(x.clone())
            .unwrap()
            .apply(xs.clone())
            .unwrap()
            .apply(b.clone())
            .unwrap();
        let g_cons = app2(&g, cons, fval).unwrap();
        let expected = gxsb
            .imp(g_cons)
            .unwrap()
            .forall("b", beta)
            .unwrap()
            .forall("xs", t)
            .unwrap()
            .forall("x", elem)
            .unwrap();

        assert_eq!(got, expected);
    }

    /// A wrong number of step terms is a structured error, not a panic.
    #[test]
    fn step_count_must_match_arity() {
        let g = g_var();
        let err = closed(&nat_sig(), &[Term::free("z", nat())], &nat(), &g);
        assert!(
            err.is_err(),
            "1 step for a 2-constructor signature must error"
        );
    }
}

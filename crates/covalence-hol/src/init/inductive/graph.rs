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
//! These are **pure term builders** — no proof. The proofs over them are
//! the engine's other layers: [`super::existence`] (graph introduction +
//! totality) and [`super::uniqueness`] (the inversion lemmas), both generic;
//! and — still specialised to `nat` in [`crate::init::recursion`] —
//! determinacy and the ε-assembly.

use covalence_core::{Error, Result, Term, Type};

use super::sig::{Arg, Constructor, InductiveSig};
use crate::init::ext::TermExt;

/// `g x y`.
pub(super) fn app2(g: &Term, x: Term, y: Term) -> Result<Term> {
    g.clone().apply(x)?.apply(y)
}

/// Apply `head` to `args` left-to-right (the identity on an empty list).
fn apply_all(head: Term, args: &[Term]) -> Result<Term> {
    args.iter().try_fold(head, |acc, a| acc.apply(a.clone()))
}

/// Right-associated conjunction `t₀ ∧ (t₁ ∧ … ∧ tₙ)`. Errors on an empty
/// slice (the engine never builds an empty antecedent — a constructor
/// with no recursive arguments drops the antecedent entirely).
pub(super) fn conj(ts: &[Term]) -> Result<Term> {
    match ts {
        [] => Err(Error::ConnectiveRule(
            "inductive::graph: empty conjunction".into(),
        )),
        [last] => Ok(last.clone()),
        [head, rest @ ..] => head.clone().and(conj(rest)?),
    }
}

/// One constructor's clause materialised over **fresh argument / image
/// variables** (named from the [`Constructor`]'s binder hints) — the
/// shared backbone of both the closure clause (`clause`) and the
/// per-constructor graph-introduction proof
/// ([`super::existence::graph_intro`]).
pub(super) struct CtorInstance {
    /// The argument variables `x⃗`, in declaration order.
    pub args: Vec<Term>,
    /// The constructor applied to its arguments, `C x⃗`.
    pub head: Term,
    /// The step value `f x⃗ b⃗` — the recursor's result at this case.
    pub value: Term,
    /// The recursive `(sub-term rⱼ, image bⱼ)` pairs, in declaration order.
    pub rec_pairs: Vec<(Term, Term)>,
}

/// Materialise constructor `ctor` with step term `step` over fresh
/// variables. See [`CtorInstance`].
pub(super) fn ctor_instance(
    t_ty: &Type,
    beta: &Type,
    ctor: &Constructor,
    step: &Term,
) -> Result<CtorInstance> {
    let mut args = Vec::with_capacity(ctor.args.len());
    let mut rec_pairs = Vec::new();
    for arg in &ctor.args {
        let v = Term::free(arg.name(), arg.ty(t_ty));
        args.push(v.clone());
        if let Some(image) = arg.image() {
            rec_pairs.push((v, Term::free(image, beta.clone())));
        }
    }
    let head = apply_all(ctor.ctor.clone(), &args)?;
    let step_args: Vec<Term> = args
        .iter()
        .cloned()
        .chain(rec_pairs.iter().map(|(_, b)| b.clone()))
        .collect();
    let value = apply_all(step.clone(), &step_args)?;
    Ok(CtorInstance {
        args,
        head,
        value,
        rec_pairs,
    })
}

/// The closure clause for one constructor:
/// `∀x⃗ b⃗. (⋀ G rⱼ bⱼ) ⟹ G (C x⃗) (f x⃗ b⃗)` (no antecedent when the
/// constructor is non-recursive).
fn clause(t_ty: &Type, beta: &Type, ctor: &Constructor, step: &Term, g: &Term) -> Result<Term> {
    let inst = ctor_instance(t_ty, beta, ctor, step)?;
    let consequent = app2(g, inst.head, inst.value)?;

    // antecedent (⋀ G rⱼ bⱼ), folded in only when there are recursive args
    let body = if inst.rec_pairs.is_empty() {
        consequent
    } else {
        let conjs: Vec<Term> = inst
            .rec_pairs
            .iter()
            .map(|(sub, img)| app2(g, sub.clone(), img.clone()))
            .collect::<Result<_>>()?;
        conj(&conjs)?.imp(consequent)?
    };

    // ∀-close: images innermost, then the arguments — so the quantifier
    // prefix reads `∀ x⃗ b⃗.` left-to-right.
    let mut t = body;
    for image in ctor.args.iter().rev().filter_map(Arg::image) {
        t = t.forall(image, beta.clone())?;
    }
    for arg in ctor.args.iter().rev() {
        t = t.forall(arg.name(), arg.ty(t_ty))?;
    }
    Ok(t)
}

/// The type of the impredicative relation variable, `T → β → bool`.
pub(super) fn relation_ty(sig: &InductiveSig, beta: &Type) -> Type {
    Type::fun(sig.ty.clone(), Type::fun(beta.clone(), Type::bool()))
}

/// `closed(fs, G)` — `G` is closed under every constructor's recursion
/// rule: the right-associated conjunction of the per-constructor clauses.
/// `steps` must have one entry per constructor.
pub fn closed(sig: &InductiveSig, steps: &[Term], beta: &Type, g: &Term) -> Result<Term> {
    if steps.len() != sig.arity() {
        return Err(Error::ConnectiveRule(format!(
            "inductive::graph::closed: {} step terms for {} constructors",
            steps.len(),
            sig.arity()
        )));
    }
    let clauses: Vec<Term> = sig
        .ctors
        .iter()
        .zip(steps)
        .map(|(c, s)| clause(&sig.ty, beta, c, s, g))
        .collect::<Result<_>>()?;
    conj(&clauses)
}

/// `Graph fs t a ≜ ∀G. closed(fs, G) ⟹ G t a` — the impredicative graph
/// relating `t : T` to `a : β`.
pub fn graph(sig: &InductiveSig, steps: &[Term], beta: &Type, t: Term, a: Term) -> Result<Term> {
    let g_ty = relation_ty(sig, beta);
    let g = Term::free(sig.relation, g_ty.clone());
    let gta = app2(&g, t, a)?;
    closed(sig, steps, beta, &g)?
        .imp(gta)?
        .forall(sig.relation, g_ty)
}

#[cfg(test)]
mod tests {
    use super::*;
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
        // C : α → T → T  and step f : α → T → β → β.
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

        let got = closed(&sig, &[f.clone()], &beta, &g).unwrap();

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

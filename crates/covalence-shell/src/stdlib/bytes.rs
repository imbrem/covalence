//! HOL bytes — backed by Pure's primitive `bytes` type plus the
//! `BytesCat`/`BytesConsNat`/`BytesLen`/`BytesAt`/`BytesSlice`
//! reduction prims.
//!
//! Closed-form facts (`cat (blob[1,2]) (blob[3]) = blob[1,2,3]`)
//! decide by `Thm::reduce_prim`. Open-form facts (induction over
//! bytes, cat-empty laws, slice-cat-decomposition) are postulated
//! HOL axioms here.

use std::sync::LazyLock;

use covalence_hol::HolLightCtx;
use covalence_pure::{Prim, Term, Thm, Type};

use crate::stdlib::nat;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn assume_hol(body: Term) -> Thm {
    let wrapped = ctx().mk_trueprop(body).expect("stdlib::bytes: mk_trueprop");
    Thm::assume(wrapped).expect("stdlib::bytes: assume")
}

// ============================================================================
// Types and literal constructors
// ============================================================================

pub fn ty() -> Type {
    Type::bytes()
}

/// `blob(bs)` — a literal bytes value.
pub fn blob(bs: impl Into<bytes::Bytes>) -> Term {
    Term::blob(bs)
}

/// `empty` — `blob []`.
pub fn empty() -> Term {
    blob(Vec::<u8>::new())
}

// ============================================================================
// Function constants (the Pure prims wrapped as named accessors)
// ============================================================================

pub fn cat_fn() -> Term {
    Term::prim(Prim::BytesCat)
}
pub fn cat(a: Term, b: Term) -> Term {
    Term::app(Term::app(cat_fn(), a), b)
}

pub fn cons_nat_fn() -> Term {
    Term::prim(Prim::BytesConsNat)
}
pub fn cons_nat(n: Term, bs: Term) -> Term {
    Term::app(Term::app(cons_nat_fn(), n), bs)
}

pub fn len_fn() -> Term {
    Term::prim(Prim::BytesLen)
}
pub fn len(bs: Term) -> Term {
    Term::app(len_fn(), bs)
}

pub fn at_fn() -> Term {
    Term::prim(Prim::BytesAt)
}
pub fn at(bs: Term, i: Term) -> Term {
    Term::app(Term::app(at_fn(), bs), i)
}

pub fn slice_fn() -> Term {
    Term::prim(Prim::BytesSlice)
}
pub fn slice(bs: Term, start: Term, n: Term) -> Term {
    Term::app(Term::app(Term::app(slice_fn(), bs), start), n)
}

// ============================================================================
// Axioms (open-form)
// ============================================================================

/// `⊢ ∀bs:bytes. cat empty bs = bs`.
pub fn axiom_cat_empty_l() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let bs = Term::free("bs", ty());
        let lhs = cat(empty(), bs.clone());
        let eq = ctx.mk_eq(lhs, bs).expect("axiom_cat_empty_l: mk_eq");
        let body = ctx.mk_forall("bs", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀bs:bytes. cat bs empty = bs`.
pub fn axiom_cat_empty_r() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let bs = Term::free("bs", ty());
        let lhs = cat(bs.clone(), empty());
        let eq = ctx.mk_eq(lhs, bs).expect("axiom_cat_empty_r: mk_eq");
        let body = ctx.mk_forall("bs", ty(), eq);
        assume_hol(body)
    });
    AX.clone()
}

/// `⊢ ∀a b c. cat (cat a b) c = cat a (cat b c)` — cat is associative.
pub fn axiom_cat_assoc() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let b = Term::free("b", ty());
        let c = Term::free("c", ty());
        let lhs = cat(cat(a.clone(), b.clone()), c.clone());
        let rhs = cat(a, cat(b, c));
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_cat_assoc: mk_eq");
        let i1 = ctx.mk_forall("c", ty(), eq);
        let i2 = ctx.mk_forall("b", ty(), i1);
        let outer = ctx.mk_forall("a", ty(), i2);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ len empty = 0`.
pub fn axiom_len_empty() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let eq = ctx
            .mk_eq(len(empty()), nat::zero())
            .expect("axiom_len_empty: mk_eq");
        assume_hol(eq)
    });
    AX.clone()
}

/// `⊢ ∀a b. len (cat a b) = len a + len b`.
pub fn axiom_len_cat() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let a = Term::free("a", ty());
        let b = Term::free("b", ty());
        let lhs = len(cat(a.clone(), b.clone()));
        let rhs = nat::add(len(a), len(b));
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_len_cat: mk_eq");
        let inner = ctx.mk_forall("b", ty(), eq);
        let outer = ctx.mk_forall("a", ty(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀n bs. len (cons_nat n bs) = succ (len bs)`.
pub fn axiom_len_cons_nat() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let n = Term::free("n", Type::nat());
        let bs = Term::free("bs", ty());
        let lhs = len(cons_nat(n.clone(), bs.clone()));
        let rhs = nat::succ(len(bs));
        let eq = ctx.mk_eq(lhs, rhs).expect("axiom_len_cons_nat: mk_eq");
        let inner = ctx.mk_forall("bs", ty(), eq);
        let outer = ctx.mk_forall("n", Type::nat(), inner);
        assume_hol(outer)
    });
    AX.clone()
}

/// `⊢ ∀P. P empty ∧ (∀n bs. P bs ⟹ P (cons_nat n bs)) ⟹ ∀bs. P bs` —
/// structural induction on bytes.
pub fn axiom_bytes_induction() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let bytes_ty = ty();
        let nat_ty = Type::nat();
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(bytes_ty.clone(), bool_ty);
        let p = Term::free("P", pred_ty.clone());

        let p_empty = Term::app(p.clone(), empty());

        let n = Term::free("n", nat_ty.clone());
        let bs = Term::free("bs", bytes_ty.clone());
        let consed = cons_nat(n.clone(), bs.clone());
        let p_bs = Term::app(p.clone(), bs);
        let p_consed = Term::app(p.clone(), consed);
        let step_body = ctx.mk_imp(p_bs, p_consed);
        let step_inner = ctx.mk_forall("bs", bytes_ty.clone(), step_body);
        let step = ctx.mk_forall("n", nat_ty, step_inner);

        let antecedent = ctx.mk_and(p_empty, step);

        let bs2 = Term::free("bs", bytes_ty.clone());
        let p_bs2 = Term::app(p.clone(), bs2);
        let consequent = ctx.mk_forall("bs", bytes_ty, p_bs2);

        let imp = ctx.mk_imp(antecedent, consequent);
        let body = ctx.mk_forall("P", pred_ty, imp);
        assume_hol(body)
    });
    AX.clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_pure::{TermKind, Thm};

    fn rhs_of_reduction(t: Term) -> Term {
        let thm = Thm::reduce_prim(t).unwrap();
        match thm.concl().kind() {
            TermKind::Eq(_, r) => r.clone(),
            _ => panic!(),
        }
    }

    #[test]
    fn cat_reduces() {
        let a = blob(vec![1u8, 2]);
        let b = blob(vec![3u8, 4, 5]);
        assert_eq!(rhs_of_reduction(cat(a, b)), blob(vec![1u8, 2, 3, 4, 5]));
    }

    #[test]
    fn cons_nat_mod_256_reduces() {
        let n = nat::lit(257u32);
        let bs = blob(vec![9u8, 10]);
        assert_eq!(rhs_of_reduction(cons_nat(n, bs)), blob(vec![1u8, 9, 10]));
    }

    #[test]
    fn len_at_slice_reduce() {
        assert_eq!(rhs_of_reduction(len(blob(vec![7u8, 8, 9]))), nat::lit(3u32));
        assert_eq!(
            rhs_of_reduction(at(blob(vec![7u8, 8, 9]), nat::lit(1u32))),
            nat::lit(8u32)
        );
        assert_eq!(
            rhs_of_reduction(slice(blob(vec![10u8, 20, 30, 40]), nat::lit(1u32), nat::lit(2u32))),
            blob(vec![20u8, 30])
        );
    }

    #[test]
    fn axioms_well_formed() {
        for ax in [
            axiom_cat_empty_l(),
            axiom_cat_empty_r(),
            axiom_cat_assoc(),
            axiom_len_empty(),
            axiom_len_cat(),
            axiom_len_cons_nat(),
            axiom_bytes_induction(),
        ] {
            assert!(ax.concl().type_of().unwrap().is_prop());
        }
    }
}

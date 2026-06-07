//! HOL natural numbers.
//!
//! `Nat` is a HOL type defined by `Thm::new_type_definition` over a
//! `bytes` carrier. The MVP uses the trivially-true predicate
//! `λx:bytes. x ≡ x`, so the bijection `Nat ↔ bytes` is total:
//! every bytes value corresponds to a `Nat`, and vice versa. Under
//! this view, content-addressing / serialisation / hashing of nats
//! all reduce to the same operations on the underlying bytes —
//! "plays nice with bytes" in the simplest possible sense.
//!
//! ## Why not a canonical little-endian carve-out?
//!
//! A subset-style typedef (`Nat = { bs : bytes | bs = [] ∨ last bs ≠ 0 }`)
//! gives unique-representation semantics but requires byte
//! structural operations (`last`, `length`) that Pure doesn't expose
//! as primitives yet. The public surface here is identical to what
//! the subset version would expose, so a later upgrade swaps the
//! predicate without touching downstream code.
//!
//! ## Internals (subject to change)
//!
//! - Carrier: `Type::bytes()`
//! - Witness: `⊢ (λy:bytes. y ≡ y) (blob [])` constructed via
//!   `β-conv` + `sym` + `eq_mp` of `Thm::refl(blob [])`
//! - `nat_of_bytes` / `bytes_of_nat`: the typedef's `abs` / `rep`,
//!   Pure `Obs` leaves whose Arc identity is preserved by
//!   `subst_tfree_in_term` (so they round-trip identically through
//!   any kernel-level walk).

use std::sync::LazyLock;

use covalence_hol::HolLightCtx;
use covalence_pure::{BinderHint, Term, Thm, Type, TypeDef};

/// Internal typedef bundle. Private because the predicate / witness
/// /carrier may change.
static NAT: LazyLock<TypeDef> = LazyLock::new(build_nat_typedef);

fn build_nat_typedef() -> TypeDef {
    let bytes_ty = Type::bytes();
    let empty = Term::blob(Vec::new());

    // P = `λy:bytes. y ≡ y` — type `bytes → prop`. Body uses
    // `Bound(0)` for the binder; both sides of the eq are the
    // bound var, so the eq type-checks at any α and produces prop.
    let p_body = Term::eq(Term::bound(0), Term::bound(0));
    let p = Term::abs(BinderHint::new("y"), bytes_ty, p_body);

    // Witness: ⊢ App(P, empty).
    // β-conv on the App gives us `⊢ App(P, empty) ≡ (empty ≡ empty)`.
    // refl on `empty` gives `⊢ empty ≡ empty`.
    // sym + eq_mp combine to `⊢ App(P, empty)`.
    let p_at_empty = Term::app(p, empty.clone());
    let beta = Thm::beta_conv(p_at_empty).expect("Nat: β-conv on witness shape");
    let refl = Thm::refl(empty).expect("Nat: refl on empty bytes");
    let witness = beta
        .sym()
        .expect("Nat: sym on β-conv equation")
        .eq_mp(refl)
        .expect("Nat: eq_mp combining witness");

    Thm::new_type_definition("nat", "nat_of_bytes", "bytes_of_nat", witness)
        .expect("Nat: new_type_definition rejected a hand-built witness")
}

// ============================================================================
// Public surface
// ============================================================================

/// The HOL natural-number type.
pub fn ty() -> Type {
    NAT.tau.clone()
}

/// `nat_of_bytes : bytes → Nat`. Total; bijective for the MVP
/// carrier.
pub fn of_bytes() -> Term {
    NAT.abs.clone()
}

/// `bytes_of_nat : Nat → bytes`. Right inverse of `of_bytes`.
pub fn to_bytes() -> Term {
    NAT.rep.clone()
}

/// Apply `of_bytes` to a concrete `bytes` term.
pub fn lift(bytes_term: Term) -> Term {
    Term::app(of_bytes(), bytes_term)
}

/// Apply `bytes_of_nat` to a concrete `Nat` term.
pub fn lower(nat_term: Term) -> Term {
    Term::app(to_bytes(), nat_term)
}

/// The canonical zero `Nat`: `nat_of_bytes (blob [])`.
pub fn zero() -> Term {
    static ZERO: LazyLock<Term> = LazyLock::new(|| lift(Term::blob(Vec::new())));
    ZERO.clone()
}

// ============================================================================
// Successor + Peano axioms
// ============================================================================
//
// `succ` is postulated as a constant of type `Nat → Nat`. Its
// behaviour is pinned by the three Peano axioms below, each
// provided as a lazy `Thm` (assumed via `Thm::assume`, with the
// axiom term carried as the single hypothesis — the standard
// audit-trail pattern: every theorem derived from a Peano axiom
// transparently records the dependency).
//
// These postulates correspond exactly to the three Peano-Dedekind
// axioms HOL Light eventually DERIVES from `INFINITY_AX` + the
// `num` typedef. For now we stress-test the stdlib infrastructure
// by accepting them outright; later versions can substitute
// derivations as the supporting machinery (`one_one`/`onto`/INFINITY
// bridge, IND_0/IND_SUC extraction, recursive carve-out) lands.

/// The successor constant `succ : Nat → Nat`. Postulated. Relation
/// to the underlying bytes-bijection is not established — the
/// Peano axioms below are the contract.
pub fn succ() -> Term {
    static SUCC: LazyLock<Term> = LazyLock::new(|| Term::const_("succ", Type::fun(ty(), ty())));
    SUCC.clone()
}

/// `succ` applied to a concrete `Nat` term.
pub fn succ_of(n: Term) -> Term {
    Term::app(succ(), n)
}

/// **Peano axiom 1**: `⊢ ∀n:Nat. ¬ (zero = succ n)` — zero is
/// not a successor.
pub fn axiom_zero_not_succ() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let nat_ty = ty();
        let n = Term::free("n", nat_ty.clone());
        let eq = ctx
            .mk_eq(zero(), succ_of(n))
            .expect("axiom_zero_not_succ: mk_eq");
        let not_eq = ctx.mk_not(eq);
        let body = ctx.mk_forall("n", nat_ty, not_eq);
        let wrapped = ctx
            .mk_trueprop(body)
            .expect("axiom_zero_not_succ: mk_trueprop");
        Thm::assume(wrapped).expect("axiom_zero_not_succ: assume")
    });
    AX.clone()
}

/// **Peano axiom 2**: `⊢ ∀m n:Nat. succ m = succ n ⟹ m = n` —
/// successor is injective.
pub fn axiom_succ_injective() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let nat_ty = ty();
        let m = Term::free("m", nat_ty.clone());
        let n = Term::free("n", nat_ty.clone());
        let lhs_eq = ctx
            .mk_eq(succ_of(m.clone()), succ_of(n.clone()))
            .expect("axiom_succ_injective: mk_eq lhs");
        let rhs_eq = ctx
            .mk_eq(m, n)
            .expect("axiom_succ_injective: mk_eq rhs");
        let imp = ctx.mk_imp(lhs_eq, rhs_eq);
        let inner = ctx.mk_forall("n", nat_ty.clone(), imp);
        let body = ctx.mk_forall("m", nat_ty, inner);
        let wrapped = ctx
            .mk_trueprop(body)
            .expect("axiom_succ_injective: mk_trueprop");
        Thm::assume(wrapped).expect("axiom_succ_injective: assume")
    });
    AX.clone()
}

/// **Peano axiom 3 (induction)**:
/// `⊢ ∀P:Nat→bool. P zero ∧ (∀n. P n ⟹ P (succ n)) ⟹ ∀n. P n`.
pub fn axiom_induction() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let nat_ty = ty();
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(nat_ty.clone(), bool_ty);
        let p = Term::free("P", pred_ty.clone());

        // P zero
        let p_zero = Term::app(p.clone(), zero());

        // ∀n. P n ⟹ P (succ n)
        let n = Term::free("n", nat_ty.clone());
        let p_n = Term::app(p.clone(), n.clone());
        let p_succ_n = Term::app(p.clone(), succ_of(n));
        let step_body = ctx.mk_imp(p_n, p_succ_n);
        let step = ctx.mk_forall("n", nat_ty.clone(), step_body);

        // P zero ∧ (∀n. P n ⟹ P (succ n))
        let antecedent = ctx.mk_and(p_zero, step);

        // ∀n. P n  (conclusion)
        let n2 = Term::free("n", nat_ty.clone());
        let p_n2 = Term::app(p.clone(), n2);
        let consequent = ctx.mk_forall("n", nat_ty, p_n2);

        // antecedent ⟹ consequent
        let imp = ctx.mk_imp(antecedent, consequent);

        // ∀P. (antecedent ⟹ consequent)
        let body = ctx.mk_forall("P", pred_ty, imp);

        let wrapped = ctx
            .mk_trueprop(body)
            .expect("axiom_induction: mk_trueprop");
        Thm::assume(wrapped).expect("axiom_induction: assume")
    });
    AX.clone()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nat_type_is_stable_across_calls() {
        // ty() returns the same Type identity each invocation —
        // process-global lazy init guarantees the same typedef
        // marker Arc across calls.
        let a = ty();
        let b = ty();
        assert_eq!(a, b);
    }

    #[test]
    fn of_bytes_and_to_bytes_are_typedef_consts() {
        // abs : bytes → Nat, rep : Nat → bytes.
        let abs_ty = of_bytes().type_of().expect("nat_of_bytes well-typed");
        let rep_ty = to_bytes().type_of().expect("bytes_of_nat well-typed");
        assert_eq!(abs_ty, Type::fun(Type::bytes(), ty()));
        assert_eq!(rep_ty, Type::fun(ty(), Type::bytes()));
    }

    #[test]
    fn zero_has_nat_type() {
        let z = zero();
        assert_eq!(z.type_of().expect("zero well-typed"), ty());
    }

    #[test]
    fn lift_lower_compose_to_nat() {
        let bs = Term::blob(vec![1u8, 2, 3]);
        let n = lift(bs);
        assert_eq!(n.type_of().unwrap(), ty());
        let back = lower(n);
        assert_eq!(back.type_of().unwrap(), Type::bytes());
    }

    #[test]
    fn succ_has_function_type_nat_to_nat() {
        let s = succ();
        let s_ty = s.type_of().expect("succ well-typed");
        assert_eq!(s_ty, Type::fun(ty(), ty()));
    }

    #[test]
    fn succ_of_zero_has_nat_type() {
        let s_zero = succ_of(zero());
        assert_eq!(s_zero.type_of().expect("succ zero well-typed"), ty());
    }

    #[test]
    fn axiom_zero_not_succ_is_well_formed() {
        let ax = axiom_zero_not_succ();
        // Concl is a Trueprop-wrapped proposition.
        assert!(ax.concl().type_of().expect("axiom concl typed").is_prop());
        // The axiom is its own hypothesis (Thm::assume pattern).
        assert_eq!(ax.hyps().len(), 1);
        assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
    }

    #[test]
    fn axiom_succ_injective_is_well_formed() {
        let ax = axiom_succ_injective();
        assert!(ax.concl().type_of().expect("axiom concl typed").is_prop());
    }

    #[test]
    fn axiom_induction_is_well_formed() {
        let ax = axiom_induction();
        assert!(ax.concl().type_of().expect("axiom concl typed").is_prop());
    }

    #[test]
    fn peano_axioms_are_stable_lazy_constants() {
        // Each call returns a Thm equal to the previously cached
        // one — verifying the LazyLock identity story for HOL
        // theorems works correctly (no fresh allocation per call).
        let a1 = axiom_zero_not_succ();
        let a2 = axiom_zero_not_succ();
        assert_eq!(a1.concl(), a2.concl());

        let b1 = axiom_succ_injective();
        let b2 = axiom_succ_injective();
        assert_eq!(b1.concl(), b2.concl());

        let c1 = axiom_induction();
        let c2 = axiom_induction();
        assert_eq!(c1.concl(), c2.concl());
    }

    #[test]
    fn induction_axiom_can_be_instantiated_at_a_predicate() {
        // Pick the trivially-true predicate `λ_:Nat. T` and
        // peel off the ∀P binder via the induction axiom's
        // structure. After `dest_eq_concl`-like extraction we
        // should land at a specific imp: `(T ∧ ⋀n. T ⟹ T) ⟹ ⋀n. T`.
        //
        // For this test we just check the axiom's outer shape:
        // it's `Trueprop (∀P. …)`, where ∀ is the HOL forall obs.
        let ax = axiom_induction();
        // Concl shape: Trueprop (forall (λP. ...)).
        let ctx = HolLightCtx::new();
        let covalence_pure::TermKind::App(tp_head, body) = ax.concl().kind() else {
            panic!("axiom concl not an App");
        };
        assert!(
            ctx.is_trueprop(tp_head),
            "axiom concl head is not Trueprop"
        );
        // body should be `forall (λP. …)` — an App with forall_at as head.
        match body.kind() {
            covalence_pure::TermKind::App(_, lam) => match lam.kind() {
                covalence_pure::TermKind::Abs(hint, _, _) => assert_eq!(hint.as_str(), "P"),
                _ => panic!("expected Abs as forall's argument"),
            },
            _ => panic!("expected App for forall body"),
        }
    }

    #[test]
    fn typedef_bijection_theorems_are_derivable() {
        // The typedef bundle exposes abs_rep / rep_abs_fwd /
        // rep_abs_back. We don't expose them in the public API yet,
        // but they ARE the proof witnesses that the bijection
        // holds. Sanity-check that they instantiate at the bytes
        // carrier (i.e., the typedef construction succeeded).
        //
        // We instantiate `abs_rep: ⋀a:Nat. abs(rep a) ≡ a` at
        // `zero` and check it produces a meta-eq concl.
        let z = zero();
        let abs_rep_at_z = NAT
            .abs_rep
            .clone()
            .all_elim(z.clone())
            .expect("abs_rep instantiates at zero");
        // Concl shape: `abs(rep zero) ≡ zero`.
        match abs_rep_at_z.concl().kind() {
            covalence_pure::TermKind::Eq(_, r) => assert_eq!(r, &z),
            _ => panic!("abs_rep at zero must yield a Pure ≡"),
        }
    }
}

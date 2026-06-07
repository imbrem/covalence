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

//! **Generic (non-recursive) variant datatypes** — realize a sum-of-payloads
//! type from a constructor description, through a *pluggable backend*.
//!
//! This complements the recursion engine ([`super`]): where that derives
//! induction/recursion for an *existing* carrier (`nat`, `list`), this
//! **synthesizes a fresh type** for a finite, non-recursive sum — the common
//! shape of many first-order enum/union declarations (WASM's `numtype`,
//! `valtype`, `mut`, …). A [`Variant`] is an ordered list of named constructors,
//! each with a **payload** HOL type (`unit` for a nullary constructor, a `prod`
//! for several fields — the payload is whatever the front end already resolved).
//!
//! ## Backend-swappable
//!
//! The realization is behind the [`VariantBackend`] trait so the *how* can change
//! without the callers (e.g. [`crate::wasm::syntax`]) changing. [`CoprodBackend`]
//! is the first backend: a right-nested [`coprod`](crate::init::coprod) of the
//! payloads — a genuine monomorphic HOL type whose constructor **injectivity** and
//! **disjointness** come free from the coproduct lemmas. Later backends (a sealed
//! `new_type_definition`, or an impredicative Church encoding once recursion is in
//! scope) can slot in behind the same trait — which matters while the kernel
//! backend itself (`covalence-pure`) is in flux.
//!
//! **Scope:** non-recursive only. A payload that refers back to the variant
//! (recursive/mutually-recursive types like `instr`) is out of scope here and is
//! the recursion engine's job; the caller detects the self-reference (a cyclic
//! alias) and defers.

use covalence_core::subst::close;
use covalence_core::{Error, Result, Term, Type};

use crate::init::coprod::{coprod, inl, inr};
use crate::init::ext::TermExt;

/// One constructor: a name and the HOL type of its payload.
#[derive(Debug, Clone)]
pub struct VCtor {
    pub name: String,
    pub payload: Type,
}

impl VCtor {
    pub fn new(name: impl Into<String>, payload: Type) -> Self {
        VCtor {
            name: name.into(),
            payload,
        }
    }
}

/// A finite, non-recursive variant: an ordered, non-empty list of constructors.
#[derive(Debug, Clone)]
pub struct Variant {
    pub ctors: Vec<VCtor>,
}

impl Variant {
    pub fn new(ctors: Vec<VCtor>) -> Self {
        Variant { ctors }
    }

    fn payloads(&self) -> Vec<Type> {
        self.ctors.iter().map(|c| c.payload.clone()).collect()
    }
}

fn variant_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("variant: {}", msg.into()))
}

/// A pluggable realization of a [`Variant`] as a concrete HOL type + constructor
/// terms. Swap the impl to change the encoding without touching callers.
pub trait VariantBackend {
    /// The HOL type realizing the variant.
    fn ty(&self, v: &Variant) -> Result<Type>;

    /// Constructor `i` as a function term `payloadᵢ → ty(v)`.
    fn ctor(&self, v: &Variant, i: usize) -> Result<Term>;
}

/// The coproduct-of-payloads backend: `ty = P₀ ⊕ (P₁ ⊕ (… ⊕ Pₙ))`, constructors
/// are the corresponding injection composites. Constructor injectivity /
/// disjointness are inherited from [`coprod`](crate::init::coprod)'s lemmas.
pub struct CoprodBackend;

/// `P₀ ⊕ (P₁ ⊕ (… ⊕ Pₙ))` — right-nested coproduct (`[P]` = `P`).
fn fold_coprod(payloads: &[Type]) -> Result<Type> {
    match payloads {
        [] => Err(variant_err("empty variant has no type")),
        [only] => Ok(only.clone()),
        [head, rest @ ..] => Ok(coprod(head.clone(), fold_coprod(rest)?)),
    }
}

/// Inject `x : payloads[i]` into `fold_coprod(payloads)`.
fn inject(payloads: &[Type], i: usize, x: Term) -> Result<Term> {
    match payloads {
        [] => Err(variant_err("constructor index out of range")),
        [_only] => Ok(x), // single constructor: the type *is* the payload.
        [head, rest @ ..] => {
            let rest_ty = fold_coprod(rest)?;
            if i == 0 {
                inl(head.clone(), rest_ty).apply(x)
            } else {
                let inner = inject(rest, i - 1, x)?;
                inr(head.clone(), rest_ty).apply(inner)
            }
        }
    }
}

impl VariantBackend for CoprodBackend {
    fn ty(&self, v: &Variant) -> Result<Type> {
        fold_coprod(&v.payloads())
    }

    fn ctor(&self, v: &Variant, i: usize) -> Result<Term> {
        if i >= v.ctors.len() {
            return Err(variant_err("constructor index out of range"));
        }
        let payloads = v.payloads();
        let payload_i = payloads[i].clone();
        let x = Term::free("x", payload_i.clone());
        let body = inject(&payloads, i, x)?;
        Ok(Term::abs(payload_i, close(&body, "x")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::prod::prod;

    fn enum3() -> Variant {
        // like `numtype = I32 | I64 | F32` — three nullary constructors.
        Variant::new(vec![
            VCtor::new("I32", Type::unit()),
            VCtor::new("I64", Type::unit()),
            VCtor::new("F32", Type::unit()),
        ])
    }

    #[test]
    fn single_constructor_is_its_payload() {
        let v = Variant::new(vec![VCtor::new("wrap", Type::nat())]);
        assert_eq!(CoprodBackend.ty(&v).unwrap(), Type::nat());
        // the constructor is the identity λx. x : nat → nat.
        let c = CoprodBackend.ctor(&v, 0).unwrap();
        assert_eq!(c.type_of().unwrap(), Type::fun(Type::nat(), Type::nat()));
    }

    #[test]
    fn enum_type_is_nested_coprod() {
        let v = enum3();
        let ty = CoprodBackend.ty(&v).unwrap();
        assert_eq!(ty, coprod(Type::unit(), coprod(Type::unit(), Type::unit())));
    }

    #[test]
    fn constructors_are_well_typed_functions_into_the_variant() {
        let v = enum3();
        let ty = CoprodBackend.ty(&v).unwrap();
        for i in 0..3 {
            let c = CoprodBackend.ctor(&v, i).unwrap();
            assert_eq!(
                c.type_of().unwrap(),
                Type::fun(Type::unit(), ty.clone()),
                "ctor {i}"
            );
        }
    }

    #[test]
    fn payloads_can_be_products() {
        // `valtype`-ish: NUM (nat) | PAIR (nat × nat)
        let v = Variant::new(vec![
            VCtor::new("NUM", Type::nat()),
            VCtor::new("PAIR", prod(Type::nat(), Type::nat())),
        ]);
        let ty = CoprodBackend.ty(&v).unwrap();
        assert_eq!(ty, coprod(Type::nat(), prod(Type::nat(), Type::nat())));
        let c0 = CoprodBackend.ctor(&v, 0).unwrap();
        assert_eq!(c0.type_of().unwrap(), Type::fun(Type::nat(), ty.clone()));
        let c1 = CoprodBackend.ctor(&v, 1).unwrap();
        assert_eq!(
            c1.type_of().unwrap(),
            Type::fun(prod(Type::nat(), Type::nat()), ty)
        );
    }

    #[test]
    fn out_of_range_constructor_errors() {
        assert!(CoprodBackend.ctor(&enum3(), 3).is_err());
    }
}

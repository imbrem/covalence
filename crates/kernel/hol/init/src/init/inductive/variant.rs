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
//! is the first backend: a right-nested [`coprod`](mod@crate::init::coprod) of the
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
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::coprod::{coprod, inl, inl_inj, inl_ne_inr, inr, inr_inj};
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

    /// Whether a payload mentions the reserved recursive self type.
    ///
    /// Such a description belongs to [`ChurchBackend`], not to the exact
    /// non-recursive [`CoprodVariantTheory`].
    pub fn is_recursive(&self) -> bool {
        let self_vars = self_ty_var().free_tvars();
        self.ctors.iter().any(|ctor| {
            ctor.payload
                .free_tvars()
                .iter()
                .any(|v| self_vars.contains(v))
        })
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

/// The theorem-bearing interface to a realized, non-recursive variant.
///
/// Constructor names remain part of this interface even when the concrete
/// representation has no runtime tag to retain.  In particular, the
/// behavior-preserving coproduct backend realizes a one-constructor variant as
/// its payload and its sole constructor as the identity; callers must not
/// mistake that representation choice for nominal separation between two
/// separately declared one-constructor variants.
pub trait VariantTheory {
    /// The concrete HOL carrier.
    fn carrier(&self) -> &Type;

    /// Number of constructors, in source order.
    fn constructor_count(&self) -> usize;

    /// Source-level constructor name at `i`.
    fn constructor_name(&self, i: usize) -> Result<&str>;

    /// Payload type at `i`.
    fn payload_type(&self, i: usize) -> Result<&Type>;

    /// Constructor `i`, as `payloadᵢ → carrier`.
    fn constructor(&self, i: usize) -> Result<&Term>;

    /// Look up a source-level constructor name.  Duplicate names are rejected
    /// as ambiguous instead of silently selecting one.
    fn constructor_named(&self, name: &str) -> Result<(usize, &Term)>;

    /// `⊢ Cᵢ x = Cᵢ y ⟹ x = y`.
    fn injective(&self, i: usize, x: &Term, y: &Term) -> Result<Thm>;

    /// `⊢ ¬(Cᵢ x = Cⱼ y)` for distinct `i` and `j`.
    fn distinct(&self, i: usize, j: usize, x: &Term, y: &Term) -> Result<Thm>;
}

/// A backend that can supply the theorem-bearing variant interface.
pub trait VariantTheoryBackend {
    type Theory: VariantTheory;

    fn theory(&self, variant: &Variant) -> Result<Self::Theory>;
}

/// The coproduct-of-payloads backend: `ty = P₀ ⊕ (P₁ ⊕ (… ⊕ Pₙ))`, constructors
/// are the corresponding injection composites. Constructor injectivity /
/// disjointness are inherited from [`coprod`](mod@crate::init::coprod)'s lemmas.
pub struct CoprodBackend;

/// A cached coproduct realization with freeness proofs derived from the
/// existing kernel-checked coproduct injection laws.
#[derive(Debug, Clone)]
pub struct CoprodVariantTheory {
    variant: Variant,
    carrier: Type,
    constructors: Vec<Term>,
}

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

impl VariantTheoryBackend for CoprodBackend {
    type Theory = CoprodVariantTheory;

    fn theory(&self, variant: &Variant) -> Result<Self::Theory> {
        if variant.is_recursive() {
            return Err(variant_err(
                "coproduct theory is only faithful for non-recursive variants",
            ));
        }
        let carrier = self.ty(variant)?;
        let constructors = (0..variant.ctors.len())
            .map(|i| self.ctor(variant, i))
            .collect::<Result<Vec<_>>>()?;
        Ok(CoprodVariantTheory {
            variant: variant.clone(),
            carrier,
            constructors,
        })
    }
}

impl CoprodVariantTheory {
    fn checked_payload(&self, i: usize, value: &Term) -> Result<()> {
        let expected = self.payload_type(i)?;
        let actual = value.type_of()?;
        if &actual != expected {
            return Err(variant_err(format!(
                "constructor {i} payload has type {actual:?}, expected {expected:?}"
            )));
        }
        Ok(())
    }

    /// Convert an equality between the public constructor applications to the
    /// β-reduced nested-injection equality used by the coproduct laws.
    fn reduced_constructor_eq(
        &self,
        i: usize,
        x: &Term,
        j: usize,
        y: &Term,
    ) -> Result<(Term, Thm)> {
        self.checked_payload(i, x)?;
        self.checked_payload(j, y)?;
        let lhs = self.constructor(i)?.clone().apply(x.clone())?;
        let rhs = self.constructor(j)?.clone().apply(y.clone())?;
        let public_eq = lhs.clone().equals(rhs.clone())?;
        let assumed = Thm::assume(public_eq.clone())?;
        let reduced = lhs.reduce()?.sym()?.trans(assumed)?.trans(rhs.reduce()?)?;
        Ok((public_eq, reduced))
    }
}

impl VariantTheory for CoprodVariantTheory {
    fn carrier(&self) -> &Type {
        &self.carrier
    }

    fn constructor_count(&self) -> usize {
        self.constructors.len()
    }

    fn constructor_name(&self, i: usize) -> Result<&str> {
        self.variant
            .ctors
            .get(i)
            .map(|ctor| ctor.name.as_str())
            .ok_or_else(|| variant_err("constructor index out of range"))
    }

    fn payload_type(&self, i: usize) -> Result<&Type> {
        self.variant
            .ctors
            .get(i)
            .map(|ctor| &ctor.payload)
            .ok_or_else(|| variant_err("constructor index out of range"))
    }

    fn constructor(&self, i: usize) -> Result<&Term> {
        self.constructors
            .get(i)
            .ok_or_else(|| variant_err("constructor index out of range"))
    }

    fn constructor_named(&self, name: &str) -> Result<(usize, &Term)> {
        let mut found = self
            .variant
            .ctors
            .iter()
            .enumerate()
            .filter(|(_, ctor)| ctor.name == name);
        let Some((i, _)) = found.next() else {
            return Err(variant_err(format!("unknown constructor `{name}`")));
        };
        if found.next().is_some() {
            return Err(variant_err(format!("ambiguous constructor `{name}`")));
        }
        Ok((i, &self.constructors[i]))
    }

    fn injective(&self, i: usize, x: &Term, y: &Term) -> Result<Thm> {
        let (public_eq, mut reduced) = self.reduced_constructor_eq(i, x, i, y)?;
        let payloads = self.variant.payloads();
        if i >= payloads.len() {
            return Err(variant_err("constructor index out of range"));
        }

        // Strip the common right-injection prefix.
        for depth in 0..i {
            let rest = fold_coprod(&payloads[depth + 1..])?;
            let left = inject(&payloads[depth + 1..], i - depth - 1, x.clone())?;
            let right = inject(&payloads[depth + 1..], i - depth - 1, y.clone())?;
            reduced = inr_inj(&payloads[depth], &rest, &left, &right)?.imp_elim(reduced)?;
        }

        // The final arm is an `inl`, except that the last/single arm is the
        // behavior-preserving identity representation.
        if i + 1 < payloads.len() {
            let rest = fold_coprod(&payloads[i + 1..])?;
            reduced = inl_inj(&payloads[i], &rest, x, y)?.imp_elim(reduced)?;
        }
        reduced.imp_intro(&public_eq)
    }

    fn distinct(&self, i: usize, j: usize, x: &Term, y: &Term) -> Result<Thm> {
        if i == j {
            return Err(variant_err(
                "distinctness requires two different constructors",
            ));
        }
        let (public_eq, mut reduced) = self.reduced_constructor_eq(i, x, j, y)?;
        let payloads = self.variant.payloads();
        if i >= payloads.len() || j >= payloads.len() {
            return Err(variant_err("constructor index out of range"));
        }

        let common = i.min(j);
        for depth in 0..common {
            let rest = fold_coprod(&payloads[depth + 1..])?;
            let left = inject(&payloads[depth + 1..], i - depth - 1, x.clone())?;
            let right = inject(&payloads[depth + 1..], j - depth - 1, y.clone())?;
            reduced = inr_inj(&payloads[depth], &rest, &left, &right)?.imp_elim(reduced)?;
        }

        let rest = fold_coprod(&payloads[common + 1..])?;
        let false_thm = if i < j {
            let right = inject(&payloads[common + 1..], j - common - 1, y.clone())?;
            inl_ne_inr(&payloads[common], &rest, x, &right)?.not_elim(reduced)?
        } else {
            let left = inject(&payloads[common + 1..], i - common - 1, x.clone())?;
            inl_ne_inr(&payloads[common], &rest, y, &left)?.not_elim(reduced.sym()?)?
        };
        false_thm.imp_intro(&public_eq)?.not_intro()
    }
}

/// The reserved type variable a **recursive** payload uses for the type being
/// defined (`Φ⟨'r⟩`'s `'r`). A caller building a recursive [`Variant`] substitutes
/// this for the type's self-references before handing the payloads over, and
/// [`ChurchBackend`] uses it as the fold's result type.
pub fn self_ty_var() -> Type {
    Type::tfree("cov$self")
}

/// The impredicative (Church-encoded) backend, for **recursive** variants the
/// coproduct backend can't express: `ty = (P₀ → r) → (P₁ → r) → … → r` where `r`
/// is [`self_ty_var`] and each recursive occurrence inside a payload is already
/// `r`. This is the polymorphic `Φ⟨'r⟩` encoding used across the catalogue
/// (`init::prop`, `metalogic::toy`); a monomorphic sealed type is a later backend.
///
/// Only the type is built here; the recursive constructor/fold terms need the
/// handler-threading machinery (`metalogic::toy`-style) and are deferred.
pub struct ChurchBackend;

impl VariantBackend for ChurchBackend {
    fn ty(&self, v: &Variant) -> Result<Type> {
        if v.ctors.is_empty() {
            return Err(variant_err("empty variant has no type"));
        }
        let r = self_ty_var();
        let mut acc = r.clone();
        for p in v.payloads().iter().rev() {
            // handler for this constructor: payload → r
            acc = Type::fun(Type::fun(p.clone(), r.clone()), acc);
        }
        Ok(acc)
    }

    fn ctor(&self, _v: &Variant, _i: usize) -> Result<Term> {
        Err(variant_err(
            "recursive constructor terms not built yet (needs handler-threading)",
        ))
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

    #[test]
    fn theory_proves_every_constructor_injective() {
        let theory = CoprodBackend.theory(&enum3()).unwrap();
        for i in 0..theory.constructor_count() {
            let x = Term::free(format!("x{i}"), Type::unit());
            let y = Term::free(format!("y{i}"), Type::unit());
            let theorem = theory.injective(i, &x, &y).unwrap();
            let expected = theory
                .constructor(i)
                .unwrap()
                .clone()
                .apply(x.clone())
                .unwrap()
                .equals(
                    theory
                        .constructor(i)
                        .unwrap()
                        .clone()
                        .apply(y.clone())
                        .unwrap(),
                )
                .unwrap()
                .imp(x.equals(y).unwrap())
                .unwrap();
            assert_eq!(theorem.concl(), &expected, "ctor {i}");
            assert!(theorem.hyps().is_empty(), "ctor {i}");
        }
    }

    #[test]
    fn theory_proves_all_ordered_constructor_pairs_distinct() {
        let theory = CoprodBackend.theory(&enum3()).unwrap();
        for i in 0..theory.constructor_count() {
            for j in 0..theory.constructor_count() {
                if i == j {
                    continue;
                }
                let x = Term::free(format!("x{i}{j}"), Type::unit());
                let y = Term::free(format!("y{i}{j}"), Type::unit());
                let theorem = theory.distinct(i, j, &x, &y).unwrap();
                let expected = theory
                    .constructor(i)
                    .unwrap()
                    .clone()
                    .apply(x)
                    .unwrap()
                    .equals(theory.constructor(j).unwrap().clone().apply(y).unwrap())
                    .unwrap()
                    .not()
                    .unwrap();
                assert_eq!(theorem.concl(), &expected, "ctors {i}, {j}");
                assert!(theorem.hyps().is_empty(), "ctors {i}, {j}");
            }
        }
    }

    #[test]
    fn single_constructor_keeps_its_nominal_api_tag_and_identity_behavior() {
        let variant = Variant::new(vec![VCtor::new("ONLY", Type::nat())]);
        let theory = CoprodBackend.theory(&variant).unwrap();
        assert_eq!(theory.carrier(), &Type::nat());
        assert_eq!(theory.constructor_count(), 1);
        assert_eq!(theory.constructor_name(0).unwrap(), "ONLY");
        assert_eq!(theory.constructor_named("ONLY").unwrap().0, 0);
        assert!(theory.constructor_named("OTHER").is_err());

        let x = Term::free("x", Type::nat());
        let y = Term::free("y", Type::nat());
        let theorem = theory.injective(0, &x, &y).unwrap();
        assert!(theorem.hyps().is_empty());
        assert!(theory.distinct(0, 0, &x, &y).is_err());
    }

    #[test]
    fn theory_refuses_recursive_self_placeholder() {
        let recursive = Variant::new(vec![
            VCtor::new("NIL", Type::unit()),
            VCtor::new("CONS", self_ty_var()),
        ]);
        assert!(CoprodBackend.theory(&recursive).is_err());
    }

    #[test]
    fn church_backend_builds_a_recursive_type() {
        // nat-like: ZERO (unit) | SUCC (self) — the SUCC payload is `self_ty_var`.
        let r = self_ty_var();
        let v = Variant::new(vec![
            VCtor::new("ZERO", Type::unit()),
            VCtor::new("SUCC", r.clone()),
        ]);
        // Φ = (unit → r) → (r → r) → r
        let expected = Type::fun(
            Type::fun(Type::unit(), r.clone()),
            Type::fun(Type::fun(r.clone(), r.clone()), r.clone()),
        );
        assert_eq!(ChurchBackend.ty(&v).unwrap(), expected);
        // the recursive constructor terms are deferred.
        assert!(ChurchBackend.ctor(&v, 1).is_err());
    }
}

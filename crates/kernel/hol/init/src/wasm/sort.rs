//! Semantic type-resolution vocabulary for SpecTec.
//!
//! A HOL carrier alone is not an honest interpretation of a refined SpecTec
//! type.  [`HolSort`] therefore keeps the carrier and its invariant state
//! together.  The compatibility resolver in this module delegates to the
//! existing carrier renderer, but marks the invariant [`Unresolved`]; it does
//! not silently replace erased case/field premises with truth.

use covalence_core::{Error, Result, Term, Type};
use covalence_spectec::ast::SpecTecTyp;

use super::syntax;
use super::type_family::{TypeFamilies, TypeFamilySource};

/// Whether and how membership in a semantic sort is represented.
#[derive(Debug, Clone)]
pub enum SortInvariant {
    /// No restriction is required by this interpretation.
    Unconstrained,
    /// A checked predicate of type `carrier → bool`.
    Predicate(Term),
    /// The carrier exists, but source refinements have not yet been lowered.
    Unresolved,
}

/// A HOL carrier paired with its semantic membership information.
#[derive(Debug, Clone)]
pub struct HolSort {
    carrier: Type,
    invariant: SortInvariant,
}

impl HolSort {
    /// Build an explicitly unresolved sort around an existing carrier.
    pub fn carrier_only(carrier: Type) -> Self {
        Self {
            carrier,
            invariant: SortInvariant::Unresolved,
        }
    }

    /// Build a sort whose interpretation needs no membership restriction.
    pub fn unconstrained(carrier: Type) -> Self {
        Self {
            carrier,
            invariant: SortInvariant::Unconstrained,
        }
    }

    /// Build a sort with a kernel-typechecked membership predicate.
    pub fn with_invariant(carrier: Type, invariant: Term) -> Result<Self> {
        let actual = invariant.type_of()?;
        let expected = Type::fun(carrier.clone(), Type::bool());
        if actual != expected {
            return Err(Error::ConnectiveRule(format!(
                "SpecTec sort invariant has type {actual:?}, expected {expected:?}"
            )));
        }
        Ok(Self {
            carrier,
            invariant: SortInvariant::Predicate(invariant),
        })
    }

    pub fn carrier(&self) -> &Type {
        &self.carrier
    }

    pub fn invariant(&self) -> &SortInvariant {
        &self.invariant
    }

    pub fn is_resolved(&self) -> bool {
        !matches!(self.invariant, SortInvariant::Unresolved)
    }
}

/// Where the current resolution result came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeProvenance {
    /// Compatibility result from the pre-semantic carrier renderer.
    CarrierRenderer,
    /// A future backend supplied carrier and invariant together.
    SemanticBackend,
}

/// The result exposed to consumers that need semantic type information.
#[derive(Debug, Clone)]
pub struct ResolvedType {
    pub sort: HolSort,
    pub provenance: TypeProvenance,
}

/// Backend-neutral type resolution interface.
pub trait SemanticTypeResolver {
    fn resolve_type(&self, ty: &SpecTecTyp) -> Result<ResolvedType>;
}

/// Behavior-preserving adapter around [`syntax::resolve_typ`].
///
/// It intentionally reports [`SortInvariant::Unresolved`] for every result:
/// the existing renderer may have chased a refined alias or nested refined
/// field, and this adapter cannot prove otherwise without refinement lowering.
pub struct CarrierTypeResolver<'ctx, 'defs> {
    ctx: &'ctx syntax::TypeCtx<'defs>,
}

impl<'ctx, 'defs> CarrierTypeResolver<'ctx, 'defs> {
    pub fn new(ctx: &'ctx syntax::TypeCtx<'defs>) -> Self {
        Self { ctx }
    }
}

impl SemanticTypeResolver for CarrierTypeResolver<'_, '_> {
    fn resolve_type(&self, ty: &SpecTecTyp) -> Result<ResolvedType> {
        Ok(ResolvedType {
            sort: HolSort::carrier_only(syntax::resolve_typ(ty, self.ctx)?),
            provenance: TypeProvenance::CarrierRenderer,
        })
    }
}

/// Semantic adapter that resolves the exact refinement-free fragment.
///
/// A successfully rendered carrier is marked [`SortInvariant::Unconstrained`]
/// only when its complete declared type-family dependency closure contains no
/// case or field refinements. Refined closures remain explicitly unresolved.
pub struct RefinementAwareTypeResolver<'ctx, 'defs, 'families> {
    ctx: &'ctx syntax::TypeCtx<'defs>,
    families: &'families TypeFamilies<'defs>,
}

impl<'ctx, 'defs, 'families> RefinementAwareTypeResolver<'ctx, 'defs, 'families> {
    pub fn new(
        ctx: &'ctx syntax::TypeCtx<'defs>,
        families: &'families TypeFamilies<'defs>,
    ) -> Self {
        Self { ctx, families }
    }

    fn refinement_free(&self, ty: &SpecTecTyp) -> bool {
        match ty {
            SpecTecTyp::Bool | SpecTecTyp::Num(_) | SpecTecTyp::Text => true,
            SpecTecTyp::Tup { ets } => ets.iter().all(|bind| {
                let covalence_spectec::ast::SpecTecTypBind::Bind { typ, .. } = bind;
                self.refinement_free(typ)
            }),
            SpecTecTyp::Iter { t1, .. } => self.refinement_free(t1),
            SpecTecTyp::Var { x, as1 } => {
                let args_are_free = as1.iter().all(|arg| match arg {
                    covalence_spectec::ast::SpecTecArg::Typ { t } => self.refinement_free(t),
                    _ => true,
                });
                args_are_free && self.families.refinement_free_closure(x).unwrap_or(true)
            }
        }
    }
}

impl SemanticTypeResolver for RefinementAwareTypeResolver<'_, '_, '_> {
    fn resolve_type(&self, ty: &SpecTecTyp) -> Result<ResolvedType> {
        let carrier = syntax::resolve_typ(ty, self.ctx)?;
        if self.refinement_free(ty) {
            Ok(ResolvedType {
                sort: HolSort::unconstrained(carrier),
                provenance: TypeProvenance::SemanticBackend,
            })
        } else {
            Ok(ResolvedType {
                sort: HolSort::carrier_only(carrier),
                provenance: TypeProvenance::CarrierRenderer,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_eval::mk_nat;

    use crate::init::ext::TermExt;
    use crate::init::nat;

    #[test]
    fn compatibility_resolution_preserves_carrier_but_not_faithfulness() {
        let defs = Vec::new();
        let ctx = syntax::TypeCtx::new(&defs);
        let resolved = CarrierTypeResolver::new(&ctx)
            .resolve_type(&SpecTecTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Nat))
            .unwrap();
        assert_eq!(resolved.sort.carrier(), &Type::nat());
        assert!(!resolved.sort.is_resolved());
        assert!(matches!(
            resolved.sort.invariant(),
            SortInvariant::Unresolved
        ));
        assert_eq!(resolved.provenance, TypeProvenance::CarrierRenderer);
    }

    #[test]
    fn invariant_must_be_a_bool_predicate_on_the_carrier() {
        // `(0 <) : nat → bool`.
        let predicate = nat::nat_lt().apply(mk_nat(0u64)).unwrap();
        let sort = HolSort::with_invariant(Type::nat(), predicate).unwrap();
        assert!(sort.is_resolved());
        assert!(matches!(sort.invariant(), SortInvariant::Predicate(_)));

        assert!(HolSort::with_invariant(Type::nat(), mk_nat(0u64)).is_err());
    }

    #[test]
    fn refinement_aware_resolution_certifies_the_primitive_fragment() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolved = RefinementAwareTypeResolver::new(&ctx, &families)
            .resolve_type(&SpecTecTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Nat))
            .unwrap();
        assert_eq!(resolved.sort.carrier(), &Type::nat());
        assert!(matches!(
            resolved.sort.invariant(),
            SortInvariant::Unconstrained
        ));
        assert_eq!(resolved.provenance, TypeProvenance::SemanticBackend);
    }
}

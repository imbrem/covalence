//! Semantic type-resolution vocabulary for SpecTec.
//!
//! A HOL carrier alone is not an honest interpretation of a refined SpecTec
//! type.  [`HolSort`] therefore keeps the carrier and its invariant state
//! together.  The compatibility resolver in this module delegates to the
//! existing carrier renderer, but marks the invariant [`Unresolved`]; it does
//! not silently replace erased case/field premises with truth.

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_spectec::ast::{SpecTecPrem, SpecTecTyp, SpecTecTypBind};

use super::denote::{self, DenoteCtx, TypeEnv};
use super::syntax;
use super::type_family::{TypeFamilies, TypeFamily, TypeFamilySource, TypeShape};
use crate::init::ext::TermExt;

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
    /// Retained source premises were rendered as a checked HOL predicate.
    SourceRefinement,
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

/// Exact result of attempting to lower one retained type-family refinement.
///
/// `NotApplicable` means the family has no direct source refinements.
/// `Unsupported` preserves the distinction between a genuinely unconstrained
/// family and a refined shape that this backend cannot yet interpret.
#[derive(Debug, Clone)]
pub enum RefinementLowering<'a> {
    NotApplicable,
    Predicate {
        predicate: Term,
        /// Exact retained premises, in source order.
        source_premises: &'a [SpecTecPrem],
    },
    Unsupported,
}

/// Backend seam for interpreting retained case/field premises as membership.
///
/// Implementations are ordinary, untrusted term builders. [`HolSort`] checks
/// the resulting predicate's type before a resolver exposes it.
pub trait RefinementLowerer {
    fn lower<'a>(&self, family: &TypeFamily<'a>, carrier: &Type) -> Result<RefinementLowering<'a>>;
}

/// Exact value-refinement fragment used by the bundled WASM syntax.
///
/// It accepts precisely a nullary family with one instance and one
/// single-constructor variant whose payload is one named value. Every retained
/// premise must be an `If`; those expressions are denoted in HOL under that
/// payload binder, conjoined in source order, and lambda-abstracted. Parametric,
/// dependent, multi-case, field, and non-`If` refinements are refused.
// TODO(cov:kernel.hol.init.src.wasm.case-field-refinement-premises-prs-erased, severe): Lower the dependent/parametric remainder of 56 retained refinements across 29 types; four singleton value predicates are exact.
#[derive(Debug, Default, Clone, Copy)]
pub struct SingletonValueRefinementLowerer;

impl RefinementLowerer for SingletonValueRefinementLowerer {
    fn lower<'a>(&self, family: &TypeFamily<'a>, carrier: &Type) -> Result<RefinementLowering<'a>> {
        if family.refinements().next().is_none() {
            return Ok(RefinementLowering::NotApplicable);
        }
        if !family.params.is_empty() || family.instances.len() != 1 {
            return Ok(RefinementLowering::Unsupported);
        }
        let instance = &family.instances[0];
        if !instance.params.is_empty() || !instance.args.is_empty() {
            return Ok(RefinementLowering::Unsupported);
        }
        let TypeShape::Variant(cases) = &instance.shape else {
            return Ok(RefinementLowering::Unsupported);
        };
        let [case] = cases.as_slice() else {
            return Ok(RefinementLowering::Unsupported);
        };
        if !case.params.is_empty() || case.refinements.is_empty() {
            return Ok(RefinementLowering::Unsupported);
        }
        let SpecTecTyp::Tup { ets } = case.payload else {
            return Ok(RefinementLowering::Unsupported);
        };
        let [SpecTecTypBind::Bind { id, typ }] = ets.as_slice() else {
            return Ok(RefinementLowering::Unsupported);
        };
        // The one-constructor representation is carrier-transparent only when
        // the payload itself renders to the exposed carrier.
        let payload = match typ {
            SpecTecTyp::Bool => Type::bool(),
            SpecTecTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Nat) => Type::nat(),
            SpecTecTyp::Num(covalence_spectec::ast::SpecTecNumTyp::Int) => Type::int(),
            _ => return Ok(RefinementLowering::Unsupported),
        };
        if &payload != carrier {
            return Ok(RefinementLowering::Unsupported);
        }

        let mut types = TypeEnv::new();
        types.insert(id.clone(), payload.clone());
        let ctx = DenoteCtx::values(types);
        let mut bodies = Vec::with_capacity(case.refinements.len());
        for premise in case.refinements {
            let SpecTecPrem::If { e } = premise else {
                return Ok(RefinementLowering::Unsupported);
            };
            let Ok(body) = denote::denote(e, &ctx) else {
                return Ok(RefinementLowering::Unsupported);
            };
            bodies.push(body);
        }
        let mut bodies = bodies.into_iter();
        let Some(first) = bodies.next() else {
            return Ok(RefinementLowering::Unsupported);
        };
        let body = bodies.try_fold(first, |left, right| left.and(right))?;
        let predicate = Term::abs(payload, subst::close(&body, id));
        Ok(RefinementLowering::Predicate {
            predicate,
            source_premises: case.refinements,
        })
    }
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
    refinements: SingletonValueRefinementLowerer,
}

impl<'ctx, 'defs, 'families> RefinementAwareTypeResolver<'ctx, 'defs, 'families> {
    pub fn new(
        ctx: &'ctx syntax::TypeCtx<'defs>,
        families: &'families TypeFamilies<'defs>,
    ) -> Self {
        Self {
            ctx,
            families,
            refinements: SingletonValueRefinementLowerer,
        }
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
        } else if let SpecTecTyp::Var { x, as1 } = ty
            && as1.is_empty()
            && let Some(family) = self.families.family(x)
            && let RefinementLowering::Predicate { predicate, .. } =
                self.refinements.lower(family, &carrier)?
        {
            Ok(ResolvedType {
                sort: HolSort::with_invariant(carrier, predicate)?,
                provenance: TypeProvenance::SourceRefinement,
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

    #[test]
    fn retained_byte_refinement_becomes_an_exact_checked_predicate() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolved = RefinementAwareTypeResolver::new(&ctx, &families)
            .resolve_type(&SpecTecTyp::Var {
                x: "byte".into(),
                as1: vec![],
            })
            .unwrap();

        assert_eq!(resolved.sort.carrier(), &Type::nat());
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("byte must retain its source membership predicate");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(Type::nat(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

        let family = families.family("byte").unwrap();
        let RefinementLowering::Predicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(family, &Type::nat())
            .unwrap()
        else {
            panic!("byte source refinement must lower");
        };
        assert_eq!(source_premises.len(), 1);
        assert!(std::ptr::eq(
            &source_premises[0],
            family.refinements().next().unwrap()
        ));
    }

    #[test]
    fn exact_value_fragment_is_live_but_dependent_refinements_still_refuse() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);

        for name in ["bit", "byte", "char", "dim"] {
            let resolved = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: name.into(),
                    as1: vec![],
                })
                .unwrap();
            assert!(
                matches!(resolved.sort.invariant(), SortInvariant::Predicate(_)),
                "{name}"
            );
            assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);
        }

        let unresolved = resolver
            .resolve_type(&SpecTecTyp::Var {
                x: "bshape".into(),
                as1: vec![],
            })
            .unwrap();
        assert!(matches!(
            unresolved.sort.invariant(),
            SortInvariant::Unresolved
        ));
    }
}

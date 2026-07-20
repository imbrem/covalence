//! Semantic type-resolution vocabulary for SpecTec.
//!
//! A HOL carrier alone is not an honest interpretation of a refined SpecTec
//! type.  [`HolSort`] therefore keeps the carrier and its invariant state
//! together.  The compatibility resolver in this module delegates to the
//! existing carrier renderer, but marks the invariant [`Unresolved`]; it does
//! not silently replace erased case/field premises with truth.

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_spectec::ast::{
    SpecTecArg, SpecTecBinOp, SpecTecCmpOp, SpecTecExp, SpecTecIter, SpecTecIterExp, SpecTecNum,
    SpecTecNumTyp, SpecTecOpTyp, SpecTecParam, SpecTecPrem, SpecTecTyp, SpecTecTypBind,
};

use super::denote::{self, DenoteCtx, TypeEnv};
use super::syntax;
use super::type_family::{TypeFamilies, TypeFamily, TypeFamilySource, TypeShape};
use crate::init::ext::TermExt;
use crate::init::inductive::{CoprodBackend, VCtor, Variant, VariantTheory, VariantTheoryBackend};

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
    /// A predicate assembled across several variant cases.
    CasePredicate {
        predicate: Term,
        /// Exact retained premises, flattened in source case/premise order.
        source_premises: Vec<&'a SpecTecPrem>,
    },
    Unsupported,
}

/// Backend seam for interpreting retained case/field premises as membership.
///
/// Implementations are ordinary, untrusted term builders. [`HolSort`] checks
/// the resulting predicate's type before a resolver exposes it.
pub trait RefinementLowerer {
    fn lower<'a>(
        &self,
        family: &TypeFamily<'a>,
        arguments: &[SpecTecArg],
        carrier: &Type,
        ctx: &syntax::TypeCtx<'a>,
    ) -> Result<RefinementLowering<'a>>;
}

/// Exact value-refinement fragment used by the bundled WASM syntax.
///
/// It accepts a one-instance, single-constructor value family whose payload is
/// carrier-transparent. Primitive payload predicates are denoted directly.
/// The parametric `list(X)` family is also compiled exactly: its retained
/// `|X*| < 2^32` premise becomes a predicate over the resolved `list X`
/// carrier. Multi-case, field, existentially bound, and non-`If` refinements
/// are refused.
// TODO(cov:kernel.hol.init.src.wasm.case-field-refinement-premises-prs-erased, severe): Lower the 3 instr refinements (VSHUFFLE length, VNARROW width, VEXTRACT_LANE signedness) once recursive Church instruction carriers have checked constructors/observation; every rigid indexed operator family is exact.
#[derive(Debug, Default, Clone, Copy)]
pub struct SingletonValueRefinementLowerer;

impl RefinementLowerer for SingletonValueRefinementLowerer {
    fn lower<'a>(
        &self,
        family: &TypeFamily<'a>,
        arguments: &[SpecTecArg],
        carrier: &Type,
        ctx: &syntax::TypeCtx<'a>,
    ) -> Result<RefinementLowering<'a>> {
        if family.refinements().next().is_none() {
            return Ok(RefinementLowering::NotApplicable);
        }
        if arguments.len() != family.params.len() {
            return Ok(RefinementLowering::Unsupported);
        }
        if let Some((predicate, source_premises)) =
            lower_numeric_unary_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_numeric_conversion_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_unary_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_relation_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_binary_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_conversion_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if family.instances.len() != 1 {
            return Ok(RefinementLowering::Unsupported);
        }
        let instance = &family.instances[0];
        let TypeShape::Variant(cases) = &instance.shape else {
            return Ok(RefinementLowering::Unsupported);
        };
        if let Some((predicate, source_premises)) =
            lower_float_magnitude(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_load_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_extended_ternary_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_extended_unary_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_vector_extended_binary_operator(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::CasePredicate {
                predicate,
                source_premises,
            });
        }
        let [case] = cases.as_slice() else {
            return Ok(RefinementLowering::Unsupported);
        };
        if let Some((predicate, source_premises)) =
            lower_integer_shape(family, arguments, carrier, ctx)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_shape_family(family, arguments, carrier, ctx)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if !case.params.is_empty() || case.refinements.is_empty() {
            return Ok(RefinementLowering::Unsupported);
        }

        if let Some((predicate, source_premises)) =
            lower_bounded_list(family, arguments, carrier, ctx)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_bounded_unsigned(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_bounded_signed(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) = lower_bounded_name(family, arguments, carrier)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if let Some((predicate, source_premises)) =
            lower_packed_operator(family, arguments, carrier, ctx)?
        {
            return Ok(RefinementLowering::Predicate {
                predicate,
                source_premises,
            });
        }
        if !family.params.is_empty() || !instance.params.is_empty() || !instance.args.is_empty() {
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

/// Compile `uN(N)` for a ground natural width.
///
/// The source spells the upper bound through `nat → int → nat`
/// conversions. Once `N` is ground this is exactly `i ≤ 2^N - 1`; keeping the
/// subtraction in `nat` also preserves the source's `N = 0` behavior. The
/// complete source expression is recognized before this normalization.
fn lower_bounded_unsigned<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    if family.name != "uN" || carrier != &Type::nat() {
        return Ok(None);
    }
    let (
        [SpecTecParam::Exp { x: width_name, .. }],
        [
            SpecTecArg::Exp {
                e:
                    SpecTecExp::Num {
                        n: SpecTecNum::Nat(width),
                    },
            },
        ],
        [instance],
    ) = (family.params, arguments, family.instances.as_slice())
    else {
        return Ok(None);
    };
    if !matches!(
        (instance.params, instance.args),
        (
            [SpecTecParam::Exp { x: instance_width, .. }],
            [SpecTecArg::Exp {
                e: SpecTecExp::Var { id: instance_arg },
            }],
        ) if instance_width == width_name && instance_arg == width_name
    ) {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let SpecTecTyp::Tup { ets } = case.payload else {
        return Ok(None);
    };
    let [
        SpecTecTypBind::Bind {
            id: value_name,
            typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
        },
    ] = ets.as_slice()
    else {
        return Ok(None);
    };
    let [SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if !case.params.is_empty() || !is_exact_unsigned_bound(e, value_name, width_name) {
        return Ok(None);
    }

    let value = Term::free(value_name.clone(), Type::nat());
    let zero_le = crate::init::nat::nat_le()
        .apply(covalence_hol_eval::mk_nat(0u64))?
        .apply(value.clone())?;
    let top = crate::init::nat::nat_sub()
        .apply(
            crate::init::nat::nat_pow()
                .apply(covalence_hol_eval::mk_nat(2u64))?
                .apply(covalence_hol_eval::mk_nat(*width))?,
        )?
        .apply(covalence_hol_eval::mk_nat(1u64))?;
    let upper = crate::init::nat::nat_le().apply(value)?.apply(top)?;
    let body = zero_le.and(upper)?;
    let predicate = Term::abs(Type::nat(), subst::close(&body, value_name));
    Ok(Some((predicate, case.refinements)))
}

fn is_exact_unsigned_bound(e: &SpecTecExp, value_name: &str, width_name: &str) -> bool {
    let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        t: SpecTecOpTyp::Bool(_),
        e1,
        e2,
    } = e
    else {
        return false;
    };
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Ge,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1: lower_value,
        e2: lower_zero,
    } = e1.as_ref()
    else {
        return false;
    };
    if !matches!(lower_value.as_ref(), SpecTecExp::Var { id } if id == value_name)
        || !matches!(
            lower_zero.as_ref(),
            SpecTecExp::Num {
                n: SpecTecNum::Nat(0)
            }
        )
    {
        return false;
    }
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Le,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1: upper_value,
        e2: upper,
    } = e2.as_ref()
    else {
        return false;
    };
    if !matches!(upper_value.as_ref(), SpecTecExp::Var { id } if id == value_name) {
        return false;
    }
    let SpecTecExp::Cvt {
        nt1: SpecTecNumTyp::Int,
        nt2: SpecTecNumTyp::Nat,
        e1: difference,
    } = upper.as_ref()
    else {
        return false;
    };
    let SpecTecExp::Bin {
        op: SpecTecBinOp::Sub,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
        e1: power_as_int,
        e2: one_as_int,
    } = difference.as_ref()
    else {
        return false;
    };
    let SpecTecExp::Cvt {
        nt1: SpecTecNumTyp::Nat,
        nt2: SpecTecNumTyp::Int,
        e1: power,
    } = power_as_int.as_ref()
    else {
        return false;
    };
    let SpecTecExp::Bin {
        op: SpecTecBinOp::Pow,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1: two,
        e2: width,
    } = power.as_ref()
    else {
        return false;
    };
    matches!(
        two.as_ref(),
        SpecTecExp::Num {
            n: SpecTecNum::Nat(2)
        }
    ) && matches!(width.as_ref(), SpecTecExp::Var { id } if id == width_name)
        && matches!(
            one_as_int.as_ref(),
            SpecTecExp::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Int,
                e1,
            } if matches!(e1.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(1) })
        )
}

/// Compile `sN(N)` for a ground positive natural width.
///
/// The source partitions the interval into negative, zero, and positive
/// branches. For `N > 0` that disjunction is exactly the closed interval
/// `[-2^(N-1), 2^(N-1)-1]`. We only perform this normalization after matching
/// the complete retained disjunction and all of its conversion nodes.
fn lower_bounded_signed<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    if family.name != "sN" || carrier != &Type::int() {
        return Ok(None);
    }
    let (
        [SpecTecParam::Exp { x: width_name, .. }],
        [
            SpecTecArg::Exp {
                e:
                    SpecTecExp::Num {
                        n: SpecTecNum::Nat(width),
                    },
            },
        ],
        [instance],
    ) = (family.params, arguments, family.instances.as_slice())
    else {
        return Ok(None);
    };
    if *width == 0
        || !matches!(
            (instance.params, instance.args),
            (
                [SpecTecParam::Exp { x: instance_width, .. }],
                [SpecTecArg::Exp {
                    e: SpecTecExp::Var { id: instance_arg },
                }],
            ) if instance_width == width_name && instance_arg == width_name
        )
    {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let SpecTecTyp::Tup { ets } = case.payload else {
        return Ok(None);
    };
    let [
        SpecTecTypBind::Bind {
            id: value_name,
            typ: SpecTecTyp::Num(SpecTecNumTyp::Int),
        },
    ] = ets.as_slice()
    else {
        return Ok(None);
    };
    let [SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if !case.params.is_empty() || !is_exact_signed_bound(e, value_name, width_name) {
        return Ok(None);
    }

    let half = covalence_hol_eval::defs::nat_to_int().apply(
        crate::init::nat::nat_pow()
            .apply(covalence_hol_eval::mk_nat(2u64))?
            .apply(covalence_hol_eval::mk_nat(width - 1))?,
    )?;
    let lower = crate::init::int::int_neg().apply(half.clone())?;
    let upper = crate::init::int::int_sub()
        .apply(half)?
        .apply(covalence_hol_eval::mk_int(1i128))?;
    let value = Term::free(value_name.clone(), Type::int());
    let body = crate::init::int::int_le()
        .apply(lower)?
        .apply(value.clone())?
        .and(crate::init::int::int_le().apply(value)?.apply(upper)?)?;
    let predicate = Term::abs(Type::int(), subst::close(&body, value_name));
    Ok(Some((predicate, case.refinements)))
}

fn is_exact_signed_bound(e: &SpecTecExp, value_name: &str, width_name: &str) -> bool {
    let Some((left, positive)) = bool_bin(e, SpecTecBinOp::Or) else {
        return false;
    };
    let Some((negative, zero)) = bool_bin(left, SpecTecBinOp::Or) else {
        return false;
    };
    let Some((neg_lower, neg_upper)) = bool_bin(negative, SpecTecBinOp::And) else {
        return false;
    };
    let Some((pos_lower, pos_upper)) = bool_bin(positive, SpecTecBinOp::And) else {
        return false;
    };
    int_cmp(neg_lower, SpecTecCmpOp::Ge, value_name, |bound| {
        matches!(bound, SpecTecExp::Un { op: covalence_spectec::ast::SpecTecUnOp::Minus, e2, .. }
            if is_signed_half_power(e2, width_name))
    }) && int_cmp(neg_upper, SpecTecCmpOp::Le, value_name, |bound| {
        matches!(bound, SpecTecExp::Un { op: covalence_spectec::ast::SpecTecUnOp::Minus, e2, .. }
            if is_nat_to_int_literal(e2, 1))
    }) && matches!(
        zero,
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1,
            e2,
            ..
        } if matches!(e1.as_ref(), SpecTecExp::Var { id } if id == value_name)
            && is_nat_to_int_literal(e2, 0)
    ) && int_cmp(pos_lower, SpecTecCmpOp::Ge, value_name, |bound| {
        matches!(bound, SpecTecExp::Un { op: covalence_spectec::ast::SpecTecUnOp::Plus, e2, .. }
            if is_nat_to_int_literal(e2, 1))
    }) && int_cmp(pos_upper, SpecTecCmpOp::Le, value_name, |bound| {
        matches!(
            bound,
            SpecTecExp::Bin {
                op: SpecTecBinOp::Sub,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
                e1,
                e2,
            } if matches!(e1.as_ref(), SpecTecExp::Un {
                op: covalence_spectec::ast::SpecTecUnOp::Plus,
                e2,
                ..
            } if is_signed_half_power(e2, width_name))
                && is_nat_to_int_literal(e2, 1)
        )
    })
}

fn bool_bin(e: &SpecTecExp, expected: SpecTecBinOp) -> Option<(&SpecTecExp, &SpecTecExp)> {
    match e {
        SpecTecExp::Bin {
            op,
            t: SpecTecOpTyp::Bool(_),
            e1,
            e2,
        } if *op == expected => Some((e1, e2)),
        _ => None,
    }
}

fn int_cmp(
    e: &SpecTecExp,
    expected: SpecTecCmpOp,
    value_name: &str,
    bound: impl FnOnce(&SpecTecExp) -> bool,
) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp {
            op,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
            e1,
            e2,
        } if *op == expected
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == value_name)
            && bound(e2)
    )
}

fn is_nat_to_int_literal(e: &SpecTecExp, literal: u64) -> bool {
    matches!(
        e,
        SpecTecExp::Cvt {
            nt1: SpecTecNumTyp::Nat,
            nt2: SpecTecNumTyp::Int,
            e1,
        } if matches!(e1.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(n) } if *n == literal)
    )
}

fn is_signed_half_power(e: &SpecTecExp, width_name: &str) -> bool {
    let SpecTecExp::Cvt {
        nt1: SpecTecNumTyp::Nat,
        nt2: SpecTecNumTyp::Int,
        e1: power,
    } = e
    else {
        return false;
    };
    let SpecTecExp::Bin {
        op: SpecTecBinOp::Pow,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1: two,
        e2: exponent,
    } = power.as_ref()
    else {
        return false;
    };
    matches!(
        two.as_ref(),
        SpecTecExp::Num {
            n: SpecTecNum::Nat(2)
        }
    ) && matches!(
        exponent.as_ref(),
        SpecTecExp::Cvt {
            nt1: SpecTecNumTyp::Int,
            nt2: SpecTecNumTyp::Nat,
            e1: difference,
        } if matches!(
            difference.as_ref(),
            SpecTecExp::Bin {
                op: SpecTecBinOp::Sub,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
                e1,
                e2,
            } if matches!(
                e1.as_ref(),
                SpecTecExp::Cvt {
                    nt1: SpecTecNumTyp::Nat,
                    nt2: SpecTecNumTyp::Int,
                    e1,
                } if matches!(e1.as_ref(), SpecTecExp::Var { id } if id == width_name)
            ) && is_nat_to_int_literal(e2, 1)
        )
    )
}

/// Compile the exact UTF-8 byte-length bound on `name`.
fn lower_bounded_name<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    if family.name != "name" || !arguments.is_empty() || !family.params.is_empty() {
        return Ok(None);
    }
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    if !instance.params.is_empty() || !instance.args.is_empty() {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let SpecTecTyp::Tup { ets } = case.payload else {
        return Ok(None);
    };
    let [
        SpecTecTypBind::Bind {
            id: payload_name,
            typ:
                SpecTecTyp::Iter {
                    t1,
                    it: payload_iterations,
                },
        },
    ] = ets.as_slice()
    else {
        return Ok(None);
    };
    if !matches!(
        t1.as_ref(),
        SpecTecTyp::Var { x, as1 } if x == "char" && as1.is_empty()
    ) || payload_iterations.as_slice() != [SpecTecIter::List]
        || !case.params.is_empty()
    {
        return Ok(None);
    }
    let [SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if !is_exact_name_bound(e, payload_name) {
        return Ok(None);
    }

    // The current SpecTec carrier renderer represents `char` transparently
    // as `nat`; retain that nested refinement explicitly rather than treating
    // every natural as a scalar value.
    let expected_carrier = crate::init::list::list(Type::nat());
    if carrier != &expected_carrier {
        return Ok(None);
    }
    let value = Term::free(payload_name.clone(), carrier.clone());
    let scalar = Term::free("__name_char", Type::nat());
    let below_surrogates = crate::init::nat::nat_le()
        .apply(scalar.clone())?
        .apply(covalence_hol_eval::mk_nat(0xd7ffu64))?;
    let above_surrogates = crate::init::nat::nat_le()
        .apply(covalence_hol_eval::mk_nat(0xe000u64))?
        .apply(scalar.clone())?
        .and(
            crate::init::nat::nat_le()
                .apply(scalar.clone())?
                .apply(covalence_hol_eval::mk_nat(0x10ffffu64))?,
        )?;
    let scalar_body = below_surrogates.or(above_surrogates)?;
    let scalar_predicate = Term::abs(Type::nat(), subst::close(&scalar_body, "__name_char"));
    let valid =
        crate::init::nat_parse::list_all(&Type::nat(), &scalar_predicate).apply(value.clone())?;
    let chars =
        covalence_hol_eval::defs::list_map(Type::nat(), covalence_hol_eval::defs::char_ty())
            .apply(covalence_hol_eval::defs::char_mk())?
            .apply(value)?;
    let bytes = crate::init::utf8::encode_bytes().apply(chars)?;
    let length =
        covalence_hol_eval::defs::list_length(covalence_hol_eval::defs::u8_ty()).apply(bytes)?;
    let bound = crate::init::nat::nat_pow()
        .apply(covalence_hol_eval::mk_nat(2u64))?
        .apply(covalence_hol_eval::mk_nat(32u64))?;
    let bounded = crate::init::nat::nat_lt().apply(length)?.apply(bound)?;
    let body = valid.and(bounded)?;
    let predicate = Term::abs(carrier.clone(), subst::close(&body, payload_name));
    Ok(Some((predicate, case.refinements)))
}

fn is_exact_name_bound(e: &SpecTecExp, payload_name: &str) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Lt,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1,
        e2,
    } = e
    else {
        return false;
    };
    let SpecTecExp::Len { e1: encoded } = e1.as_ref() else {
        return false;
    };
    let SpecTecExp::Call { x, as1 } = encoded.as_ref() else {
        return false;
    };
    let [
        SpecTecArg::Exp {
            e:
                SpecTecExp::Iter {
                    e1: element,
                    it: SpecTecIter::List,
                    xes,
                },
        },
    ] = as1.as_slice()
    else {
        return false;
    };
    let [
        SpecTecIterExp::Dom {
            x: domain_x,
            e: domain,
        },
    ] = xes.as_slice()
    else {
        return false;
    };
    x == "utf8"
        && matches!(element.as_ref(), SpecTecExp::Var { id } if id == "char")
        && domain_x == "char"
        && matches!(domain, SpecTecExp::Var { id } if id == payload_name)
        && matches!(
            e2.as_ref(),
            SpecTecExp::Bin {
                op: SpecTecBinOp::Pow,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
                e1,
                e2,
            } if matches!(e1.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
                && matches!(e2.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(32) })
        )
}

/// Compile the indexed packed `loadop_`/`storeop_` size bounds at the two
/// rigid integer types admitted by the source family.
fn lower_packed_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
    ctx: &syntax::TypeCtx<'a>,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    let is_load = match family.name {
        "loadop_" => true,
        "storeop_" => false,
        _ => return Ok(None),
    };
    let [
        SpecTecParam::Exp {
            x: family_param, ..
        },
    ] = family.params
    else {
        return Ok(None);
    };
    let [
        SpecTecArg::Exp {
            e: SpecTecExp::Case { op, e1 },
        },
    ] = arguments
    else {
        return Ok(None);
    };
    if !matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty()) {
        return Ok(None);
    }
    let width = match super::encode::mixop_key(op).as_str() {
        "I32" => 32u64,
        "I64" => 64u64,
        _ => return Ok(None),
    };
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    let [
        SpecTecParam::Exp {
            x: integer_param, ..
        },
    ] = instance.params
    else {
        return Ok(None);
    };
    let [SpecTecArg::Exp { e: instance_arg }] = instance.args else {
        return Ok(None);
    };
    if !is_index_substitution(instance_arg, integer_param, family_param) {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let SpecTecTyp::Tup { ets } = case.payload else {
        return Ok(None);
    };
    let size_name = match (is_load, ets.as_slice()) {
        (
            true,
            [
                SpecTecTypBind::Bind {
                    id,
                    typ: SpecTecTyp::Var { x: size_ty, as1 },
                },
                SpecTecTypBind::Bind {
                    typ:
                        SpecTecTyp::Var {
                            x: sign_ty,
                            as1: sign_args,
                        },
                    ..
                },
            ],
        ) if size_ty == "sz" && as1.is_empty() && sign_ty == "sx" && sign_args.is_empty() => id,
        (
            false,
            [
                SpecTecTypBind::Bind {
                    id,
                    typ: SpecTecTyp::Var { x: size_ty, as1 },
                },
            ],
        ) if size_ty == "sz" && as1.is_empty() => id,
        _ => return Ok(None),
    };
    let [SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if !case.params.is_empty() || !is_exact_packed_bound(e, size_name, integer_param, family_param)
    {
        return Ok(None);
    }

    let packed = Term::free("__packed", carrier.clone());
    let size = if is_load {
        let sign = syntax::resolve_typ(
            &SpecTecTyp::Var {
                x: "sx".into(),
                as1: vec![],
            },
            ctx,
        )?;
        let expected = covalence_hol_eval::defs::prod(Type::nat(), sign.clone());
        if carrier != &expected {
            return Ok(None);
        }
        covalence_hol_eval::defs::fst(Type::nat(), sign).apply(packed)?
    } else {
        if carrier != &Type::nat() {
            return Ok(None);
        }
        packed
    };
    let mut sizes = [8u64, 16, 32, 64].into_iter();
    let first = size
        .clone()
        .equals(covalence_hol_eval::mk_nat(sizes.next().expect("nonempty")))?;
    let valid_size = sizes.try_fold(first, |left, n| {
        left.or(size.clone().equals(covalence_hol_eval::mk_nat(n))?)
    })?;
    let bounded = crate::init::nat::nat_lt()
        .apply(size)?
        .apply(covalence_hol_eval::mk_nat(width))?;
    let body = valid_size.and(bounded)?;
    let predicate = Term::abs(carrier.clone(), subst::close(&body, "__packed"));
    Ok(Some((predicate, case.refinements)))
}

fn is_index_substitution(e: &SpecTecExp, instance: &str, family: &str) -> bool {
    matches!(
        e,
        SpecTecExp::Sub {
            t1: SpecTecTyp::Var { x: left, as1: left_args },
            t2: SpecTecTyp::Var { x: right, as1: right_args },
            e1,
        } if left == instance && left_args.is_empty()
            && right == family && right_args.is_empty()
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == instance)
    )
}

fn is_exact_packed_bound(
    e: &SpecTecExp,
    size_name: &str,
    integer_param: &str,
    family_param: &str,
) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Lt,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1,
        e2,
    } = e
    else {
        return false;
    };
    let left_ok = matches!(
        e1.as_ref(),
        SpecTecExp::Proj { e1, i: 0 } if matches!(
            e1.as_ref(),
            SpecTecExp::Uncase { e1, op }
                if op.fragments() == ["", ""]
                    && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == size_name)
        )
    );
    left_ok
        && matches!(
            e2.as_ref(),
            SpecTecExp::Call { x, as1 }
                if x == "sizenn"
                    && matches!(as1.as_slice(), [SpecTecArg::Exp { e }]
                        if is_index_substitution(e, integer_param, family_param))
        )
}

/// Compile `ishape` as the four exactly valid integer-lane shapes.
///
/// This eliminates the case-local existential `Jnn` by finite enumeration:
/// `(I8,16)`, `(I16,8)`, `(I32,4)`, `(I64,2)`. Those pairs simultaneously
/// preserve the nested `shape` equation (`lsize(lane) * dim = 128`) and the
/// nested `dim` refinement.
fn lower_integer_shape<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
    ctx: &syntax::TypeCtx<'a>,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    if family.name != "ishape" || !family.params.is_empty() || !arguments.is_empty() {
        return Ok(None);
    }
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    if !instance.params.is_empty() || !instance.args.is_empty() {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let SpecTecTyp::Tup { ets } = case.payload else {
        return Ok(None);
    };
    let [
        SpecTecTypBind::Bind {
            id: shape_name,
            typ: SpecTecTyp::Var { x: shape_ty, as1 },
        },
    ] = ets.as_slice()
    else {
        return Ok(None);
    };
    let [
        SpecTecParam::Exp {
            x: integer_name, ..
        },
    ] = case.params
    else {
        return Ok(None);
    };
    let [SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if shape_ty != "shape"
        || !as1.is_empty()
        || !is_exact_integer_shape_guard(e, shape_name, integer_name)
    {
        return Ok(None);
    }

    let lane_ty = syntax::resolve_typ(
        &SpecTecTyp::Var {
            x: "lanetype".into(),
            as1: vec![],
        },
        ctx,
    )?;
    let expected = covalence_hol_eval::defs::prod(lane_ty.clone(), Type::nat());
    if carrier != &expected {
        return Ok(None);
    }
    let unit = covalence_hol_eval::defs::unit_nil();
    let lane_variant = Variant::new(
        ["I32", "I64", "F32", "F64", "I8", "I16"]
            .into_iter()
            .map(|name| VCtor::new(name, Type::unit()))
            .collect(),
    );
    let theory = CoprodBackend.theory(&lane_variant)?;
    if theory.carrier() != &lane_ty {
        return Ok(None);
    }
    let shape = Term::free("__ishape", carrier.clone());
    let mut allowed = Vec::new();
    for (lane, dim) in [("I8", 16u64), ("I16", 8), ("I32", 4), ("I64", 2)] {
        let (_, ctor) = theory.constructor_named(lane)?;
        let lane_value = ctor.clone().apply(unit.clone())?;
        let pair = covalence_hol_eval::defs::pair(lane_ty.clone(), Type::nat())
            .apply(lane_value)?
            .apply(covalence_hol_eval::mk_nat(dim))?;
        allowed.push(shape.clone().equals(pair)?);
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("four integer shapes");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    let predicate = Term::abs(carrier.clone(), subst::close(&body, "__ishape"));
    Ok(Some((predicate, case.refinements)))
}

fn is_exact_integer_shape_guard(e: &SpecTecExp, shape_name: &str, integer_name: &str) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Eq,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    matches!(
        e1.as_ref(),
        SpecTecExp::Call { x, as1 }
            if x == "lanetype"
                && matches!(as1.as_slice(), [SpecTecArg::Exp {
                    e: SpecTecExp::Var { id }
                }] if id == shape_name)
    ) && matches!(
        e2.as_ref(),
        SpecTecExp::Sub {
            t1: SpecTecTyp::Var { x: left, as1: left_args },
            t2: SpecTecTyp::Var { x: right, as1: right_args },
            e1,
        } if left == integer_name && left_args.is_empty()
            && right == "lanetype" && right_args.is_empty()
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == integer_name)
    )
}

/// Compile the finite 128-bit vector-shape universes exactly.
///
/// `shape` admits every lane/dimension pair whose lane width times dimension
/// is 128. `bshape` is the nested `shape` refinement restricted to byte lanes.
fn lower_shape_family<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
    ctx: &syntax::TypeCtx<'a>,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    if !matches!(family.name, "shape" | "bshape")
        || !family.params.is_empty()
        || !arguments.is_empty()
    {
        return Ok(None);
    }
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    if !instance.params.is_empty() || !instance.args.is_empty() {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let [SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if !case.params.is_empty() {
        return Ok(None);
    }
    let exact_guard = match (family.name, case.payload) {
        ("shape", SpecTecTyp::Tup { ets }) => matches!(
            ets.as_slice(),
            [
                SpecTecTypBind::Bind {
                    id: lane,
                    typ: SpecTecTyp::Var { x: lane_ty, as1: lane_args },
                },
                SpecTecTypBind::Bind {
                    id: dim,
                    typ: SpecTecTyp::Var { x: dim_ty, as1: dim_args },
                },
            ] if lane_ty == "lanetype"
                && lane_args.is_empty()
                && dim_ty == "dim"
                && dim_args.is_empty()
                && is_exact_shape_guard(e, lane, dim)
        ),
        ("bshape", SpecTecTyp::Tup { ets }) => matches!(
            ets.as_slice(),
            [SpecTecTypBind::Bind {
                id: shape,
                typ: SpecTecTyp::Var { x: shape_ty, as1: shape_args },
            }] if shape_ty == "shape"
                && shape_args.is_empty()
                && is_exact_byte_shape_guard(e, shape)
        ),
        _ => false,
    };
    if !exact_guard {
        return Ok(None);
    }

    let lane_ty = syntax::resolve_typ(
        &SpecTecTyp::Var {
            x: "lanetype".into(),
            as1: vec![],
        },
        ctx,
    )?;
    let expected = covalence_hol_eval::defs::prod(lane_ty.clone(), Type::nat());
    if carrier != &expected {
        return Ok(None);
    }
    let lane_variant = Variant::new(
        ["I32", "I64", "F32", "F64", "I8", "I16"]
            .into_iter()
            .map(|name| VCtor::new(name, Type::unit()))
            .collect(),
    );
    let theory = CoprodBackend.theory(&lane_variant)?;
    if theory.carrier() != &lane_ty {
        return Ok(None);
    }

    let shape = Term::free("__shape", carrier.clone());
    let pairs: &[(&str, u64)] = if family.name == "bshape" {
        &[("I8", 16)]
    } else {
        &[
            ("I8", 16),
            ("I16", 8),
            ("I32", 4),
            ("F32", 4),
            ("I64", 2),
            ("F64", 2),
        ]
    };
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::with_capacity(pairs.len());
    for (lane, dim) in pairs {
        let (_, ctor) = theory.constructor_named(lane)?;
        let lane_value = ctor.clone().apply(unit.clone())?;
        let pair = covalence_hol_eval::defs::pair(lane_ty.clone(), Type::nat())
            .apply(lane_value)?
            .apply(covalence_hol_eval::mk_nat(*dim))?;
        allowed.push(shape.clone().equals(pair)?);
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("shape universe is nonempty");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__shape")),
        case.refinements,
    )))
}

fn is_exact_shape_guard(e: &SpecTecExp, lane_name: &str, dim_name: &str) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Eq,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    matches!(
        e1.as_ref(),
        SpecTecExp::Bin {
            op: SpecTecBinOp::Mul,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
            e1: left,
            e2: right,
        } if matches!(
            left.as_ref(),
            SpecTecExp::Call { x, as1 }
                if x == "lsize"
                    && matches!(as1.as_slice(), [SpecTecArg::Exp {
                        e: SpecTecExp::Var { id }
                    }] if id == lane_name)
        ) && matches!(
            right.as_ref(),
            SpecTecExp::Proj { e1, i: 0 } if matches!(
                e1.as_ref(),
                SpecTecExp::Uncase { e1, op }
                    if op.fragments() == ["", ""]
                        && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == dim_name)
            )
        )
    ) && matches!(
        e2.as_ref(),
        SpecTecExp::Num {
            n: SpecTecNum::Nat(128),
        }
    )
}

fn is_exact_byte_shape_guard(e: &SpecTecExp, shape_name: &str) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Eq,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    matches!(
        e1.as_ref(),
        SpecTecExp::Call { x, as1 }
            if x == "lanetype"
                && matches!(as1.as_slice(), [SpecTecArg::Exp {
                    e: SpecTecExp::Var { id }
                }] if id == shape_name)
    ) && matches!(
        e2.as_ref(),
        SpecTecExp::Case { op, e1 }
            if op.fragments() == ["I8"]
                && matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty())
    )
}

fn lower_numeric_unary_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "unop_" {
        return Ok(None);
    }
    let [
        SpecTecParam::Exp {
            x: family_param, ..
        },
    ] = family.params
    else {
        return Ok(None);
    };
    let [
        SpecTecArg::Exp {
            e:
                SpecTecExp::Case {
                    op: numeric_kind,
                    e1,
                },
        },
    ] = arguments
    else {
        return Ok(None);
    };
    if !matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty()) {
        return Ok(None);
    }
    let [kind] = numeric_kind.fragments() else {
        return Ok(None);
    };
    let width = match kind.as_str() {
        "I32" => Some(32u64),
        "I64" => Some(64u64),
        "F32" | "F64" => None,
        _ => return Ok(None),
    };
    let [integer, float] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(integer_cases) = &integer.shape else {
        return Ok(None);
    };
    let TypeShape::Variant(float_cases) = &float.shape else {
        return Ok(None);
    };
    let [clz, ctz, popcnt, extend] = integer_cases.as_slice() else {
        return Ok(None);
    };
    let [abs, neg, sqrt, ceil, floor, trunc, nearest] = float_cases.as_slice() else {
        return Ok(None);
    };
    if [clz, ctz, popcnt]
        .into_iter()
        .zip(["CLZ", "CTZ", "POPCNT"])
        .any(|(case, name)| !exact_unit_case(case, name))
        || [abs, neg, sqrt, ceil, floor, trunc, nearest]
            .into_iter()
            .zip(["ABS", "NEG", "SQRT", "CEIL", "FLOOR", "TRUNC", "NEAREST"])
            .any(|(case, name)| !exact_unit_case(case, name))
    {
        return Ok(None);
    }
    let SpecTecTyp::Tup { ets } = extend.payload else {
        return Ok(None);
    };
    let [
        SpecTecTypBind::Bind {
            id: size_name,
            typ: SpecTecTyp::Var { x: size_ty, as1 },
        },
    ] = ets.as_slice()
    else {
        return Ok(None);
    };
    let [SpecTecPrem::If { e: guard }] = extend.refinements else {
        return Ok(None);
    };
    let [
        SpecTecParam::Exp {
            x: integer_param, ..
        },
    ] = integer.params
    else {
        return Ok(None);
    };
    if size_ty != "sz"
        || !as1.is_empty()
        || extend.operator.fragments() != ["EXTEND"]
        || !extend.params.is_empty()
        || !is_exact_packed_bound(guard, size_name, integer_param, family_param)
        || !exact_numeric_family_instance(integer, integer_param, family_param)
    {
        return Ok(None);
    }
    let [SpecTecParam::Exp { x: float_param, .. }] = float.params else {
        return Ok(None);
    };
    if !exact_numeric_family_instance(float, float_param, family_param) {
        return Ok(None);
    }

    let (variant, allowed_sizes): (Variant, &[u64]) = if let Some(width) = width {
        (
            Variant::new(vec![
                VCtor::new("CLZ", Type::unit()),
                VCtor::new("CTZ", Type::unit()),
                VCtor::new("POPCNT", Type::unit()),
                VCtor::new("EXTEND", Type::nat()),
            ]),
            if width == 32 { &[8, 16] } else { &[8, 16, 32] },
        )
    } else {
        (
            Variant::new(
                ["ABS", "NEG", "SQRT", "CEIL", "FLOOR", "TRUNC", "NEAREST"]
                    .into_iter()
                    .map(|name| VCtor::new(name, Type::unit()))
                    .collect(),
            ),
            &[],
        )
    };
    let theory = CoprodBackend.theory(&variant)?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    if width.is_none() {
        return Ok(Some((
            Term::abs(carrier.clone(), covalence_hol_eval::mk_bool(true)),
            vec![],
        )));
    }

    let value = Term::free("__unop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::new();
    for name in ["CLZ", "CTZ", "POPCNT"] {
        let (_, ctor) = theory.constructor_named(name)?;
        allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
    }
    let (_, extend_ctor) = theory.constructor_named("EXTEND")?;
    for size in allowed_sizes {
        allowed.push(
            value.clone().equals(
                extend_ctor
                    .clone()
                    .apply(covalence_hol_eval::mk_nat(*size))?,
            )?,
        );
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("numeric unary universe is nonempty");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__unop")),
        vec![&extend.refinements[0]],
    )))
}

fn exact_unit_case(case: &super::type_family::CaseShape<'_>, name: &str) -> bool {
    case.operator.fragments() == [name]
        && matches!(case.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        && case.params.is_empty()
        && case.refinements.is_empty()
}

fn exact_numeric_family_instance(
    instance: &super::type_family::FamilyInstance<'_>,
    instance_param: &str,
    family_param: &str,
) -> bool {
    matches!(
        instance.args,
        [SpecTecArg::Exp { e }]
            if is_index_substitution(e, instance_param, family_param)
    )
}

fn lower_numeric_conversion_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "cvtop__" {
        return Ok(None);
    }
    let [
        SpecTecParam::Exp { x: family_left, .. },
        SpecTecParam::Exp {
            x: family_right, ..
        },
    ] = family.params
    else {
        return Ok(None);
    };
    let [left, right] = arguments else {
        return Ok(None);
    };
    let Some((left_kind, left_width)) = rigid_numeric_kind(left) else {
        return Ok(None);
    };
    let Some((right_kind, right_width)) = rigid_numeric_kind(right) else {
        return Ok(None);
    };
    let [ii, iff, fi, ff] = family.instances.as_slice() else {
        return Ok(None);
    };
    if !exact_cvtop_source(ii, "I", "I", family_left, family_right)
        || !exact_cvtop_source(iff, "I", "F", family_left, family_right)
        || !exact_cvtop_source(fi, "F", "I", family_left, family_right)
        || !exact_cvtop_source(ff, "F", "F", family_left, family_right)
    {
        return Ok(None);
    }
    let selected = match (left_kind, right_kind) {
        ("I", "I") => ii,
        ("I", "F") => iff,
        ("F", "I") => fi,
        ("F", "F") => ff,
        _ => unreachable!(),
    };
    let (constructors, allowed): (Vec<VCtor>, Vec<(&str, Option<&str>)>) =
        match (left_kind, right_kind) {
            ("I", "I") => (
                vec![
                    VCtor::new("EXTEND", signedness_carrier()?),
                    VCtor::new("WRAP", Type::unit()),
                ],
                if left_width < right_width {
                    vec![("EXTEND", Some("U")), ("EXTEND", Some("S"))]
                } else if left_width > right_width {
                    vec![("WRAP", None)]
                } else {
                    vec![]
                },
            ),
            ("I", "F") => (
                vec![
                    VCtor::new("CONVERT", signedness_carrier()?),
                    VCtor::new("REINTERPRET", Type::unit()),
                ],
                {
                    let mut values = vec![("CONVERT", Some("U")), ("CONVERT", Some("S"))];
                    if left_width == right_width {
                        values.push(("REINTERPRET", None));
                    }
                    values
                },
            ),
            ("F", "I") => (
                vec![
                    VCtor::new("TRUNC", signedness_carrier()?),
                    VCtor::new("TRUNC_SAT", signedness_carrier()?),
                    VCtor::new("REINTERPRET", Type::unit()),
                ],
                {
                    let mut values = vec![
                        ("TRUNC", Some("U")),
                        ("TRUNC", Some("S")),
                        ("TRUNC_SAT", Some("U")),
                        ("TRUNC_SAT", Some("S")),
                    ];
                    if left_width == right_width {
                        values.push(("REINTERPRET", None));
                    }
                    values
                },
            ),
            ("F", "F") => (
                vec![
                    VCtor::new("PROMOTE", Type::unit()),
                    VCtor::new("DEMOTE", Type::unit()),
                ],
                if left_width < right_width {
                    vec![("PROMOTE", None)]
                } else if left_width > right_width {
                    vec![("DEMOTE", None)]
                } else {
                    vec![]
                },
            ),
            _ => unreachable!(),
        };
    let theory = CoprodBackend.theory(&Variant::new(constructors))?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let value = Term::free("__cvtop", carrier.clone());
    let sx_theory = CoprodBackend.theory(&Variant::new(vec![
        VCtor::new("U", Type::unit()),
        VCtor::new("S", Type::unit()),
    ]))?;
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut equalities = Vec::new();
    for (name, sign) in allowed {
        let payload = if let Some(sign) = sign {
            let (_, sign_ctor) = sx_theory.constructor_named(sign)?;
            sign_ctor.clone().apply(unit.clone())?
        } else {
            unit.clone()
        };
        let (_, ctor) = theory.constructor_named(name)?;
        equalities.push(value.clone().equals(ctor.clone().apply(payload)?)?);
    }
    let body = if equalities.is_empty() {
        covalence_hol_eval::mk_bool(false)
    } else {
        let mut equalities = equalities.into_iter();
        let first = equalities.next().expect("checked nonempty");
        equalities.try_fold(first, |left, right| left.or(right))?
    };
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__cvtop")),
        match &selected.shape {
            TypeShape::Variant(cases) => cases
                .iter()
                .flat_map(|case| case.refinements.iter())
                .collect(),
            _ => unreachable!("validated variant"),
        },
    )))
}

fn rigid_numeric_kind(argument: &SpecTecArg) -> Option<(&'static str, u64)> {
    let SpecTecArg::Exp {
        e: SpecTecExp::Case { op, e1 },
    } = argument
    else {
        return None;
    };
    if !matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty()) {
        return None;
    }
    match op.fragments().first().map(String::as_str) {
        Some("I32") if op.fragments().len() == 1 => Some(("I", 32)),
        Some("I64") if op.fragments().len() == 1 => Some(("I", 64)),
        Some("F32") if op.fragments().len() == 1 => Some(("F", 32)),
        Some("F64") if op.fragments().len() == 1 => Some(("F", 64)),
        _ => None,
    }
}

fn signedness_carrier() -> Result<Type> {
    Ok(CoprodBackend
        .theory(&Variant::new(vec![
            VCtor::new("U", Type::unit()),
            VCtor::new("S", Type::unit()),
        ]))?
        .carrier()
        .clone())
}

fn exact_cvtop_source(
    instance: &super::type_family::FamilyInstance<'_>,
    left_kind: &str,
    right_kind: &str,
    family_left: &str,
    family_right: &str,
) -> bool {
    let [
        SpecTecParam::Exp { x: left, .. },
        SpecTecParam::Exp { x: right, .. },
    ] = instance.params
    else {
        return false;
    };
    let [left_arg, right_arg] = instance.args else {
        return false;
    };
    if !exact_cvtop_instance_arg(left_arg, left, left_kind)
        || !exact_cvtop_instance_arg(right_arg, right, right_kind)
        || family_left != "numtype_1"
        || family_right != "numtype_2"
    {
        return false;
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return false;
    };
    let expected: &[(&str, bool, Option<SpecTecCmpOp>)] = match (left_kind, right_kind) {
        ("I", "I") => &[
            ("EXTEND", true, Some(SpecTecCmpOp::Lt)),
            ("WRAP", false, Some(SpecTecCmpOp::Gt)),
        ],
        ("I", "F") => &[
            ("CONVERT", true, None),
            ("REINTERPRET", false, Some(SpecTecCmpOp::Eq)),
        ],
        ("F", "I") => &[
            ("TRUNC", true, None),
            ("TRUNC_SAT", true, None),
            ("REINTERPRET", false, Some(SpecTecCmpOp::Eq)),
        ],
        ("F", "F") => &[
            ("PROMOTE", false, Some(SpecTecCmpOp::Lt)),
            ("DEMOTE", false, Some(SpecTecCmpOp::Gt)),
        ],
        _ => return false,
    };
    cases.len() == expected.len()
        && cases
            .iter()
            .zip(expected)
            .all(|(case, (name, signed, cmp))| {
                case.operator.fragments() == [*name]
                    && case.params.is_empty()
                    && exact_cvtop_payload(case.payload, *signed)
                    && match (cmp, case.refinements) {
                        (None, []) => true,
                        (Some(op), [SpecTecPrem::If { e }]) => {
                            exact_width_comparison(e, op, left, right)
                        }
                        _ => false,
                    }
            })
}

fn exact_cvtop_instance_arg(argument: &SpecTecArg, param: &str, kind: &str) -> bool {
    let expected = if kind == "I" { "Inn" } else { "Fnn" };
    matches!(
        argument,
        SpecTecArg::Exp {
            e: SpecTecExp::Sub {
                t1: SpecTecTyp::Var { x: left, as1: left_args },
                t2: SpecTecTyp::Var { x: right, as1: right_args },
                e1,
            },
        } if left == expected
            && left_args.is_empty()
            && right == "numtype"
            && right_args.is_empty()
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == param)
    )
}

fn exact_cvtop_payload(payload: &SpecTecTyp, signed: bool) -> bool {
    let SpecTecTyp::Tup { ets } = payload else {
        return false;
    };
    if signed {
        matches!(
            ets.as_slice(),
            [SpecTecTypBind::Bind {
                typ: SpecTecTyp::Var { x, as1 },
                ..
            }] if x == "sx" && as1.is_empty()
        )
    } else {
        ets.is_empty()
    }
}

fn exact_width_comparison(
    e: &SpecTecExp,
    expected_op: &SpecTecCmpOp,
    left: &str,
    right: &str,
) -> bool {
    let SpecTecExp::Cmp { op, e1, e2, .. } = e else {
        return false;
    };
    op == expected_op
        && exact_width_call(e1, "sizenn1", left)
        && exact_width_call(e2, "sizenn2", right)
}

fn exact_width_call(e: &SpecTecExp, function: &str, param: &str) -> bool {
    matches!(
        e,
        SpecTecExp::Call { x, as1 }
            if x == function
                && matches!(
                    as1.as_slice(),
                    [SpecTecArg::Exp { e: SpecTecExp::Sub { e1, .. } }]
                        if matches!(e1.as_ref(), SpecTecExp::Var { id } if id == param)
                )
    )
}

fn lower_vector_load_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vloadop_"
        || !matches!(arguments, [arg] if rigid_case_name(arg) == Some("V128"))
    {
        return Ok(None);
    }
    let [
        SpecTecParam::Exp {
            x: family_param, ..
        },
    ] = family.params
    else {
        return Ok(None);
    };
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    if !matches!(
        (instance.params, instance.args),
        (
            [SpecTecParam::Exp { x: instance_param, .. }],
            [SpecTecArg::Exp { e: SpecTecExp::Var { id } }]
        ) if instance_param == family_param && id == instance_param
    ) {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [shape, splat, zero] = cases.as_slice() else {
        return Ok(None);
    };
    if !exact_vload_cases(shape, splat, zero, family_param) {
        return Ok(None);
    }

    let sx = signedness_carrier()?;
    let shape_payload = covalence_hol_eval::defs::prod(
        Type::nat(),
        covalence_hol_eval::defs::prod(Type::nat(), sx.clone()),
    );
    let theory = CoprodBackend.theory(&Variant::new(vec![
        VCtor::new("SHAPEX_", shape_payload),
        VCtor::new("SPLAT", Type::nat()),
        VCtor::new("ZERO", Type::nat()),
    ]))?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let sx_theory = CoprodBackend.theory(&Variant::new(vec![
        VCtor::new("U", Type::unit()),
        VCtor::new("S", Type::unit()),
    ]))?;
    let value = Term::free("__vloadop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::new();
    let (_, shape_ctor) = theory.constructor_named("SHAPEX_")?;
    for (size, dim) in [(8u64, 8u64), (16, 4), (32, 2), (64, 1)] {
        for sign in ["U", "S"] {
            let (_, sign_ctor) = sx_theory.constructor_named(sign)?;
            let sign = sign_ctor.clone().apply(unit.clone())?;
            let tail = covalence_hol_eval::defs::pair(Type::nat(), sx.clone())
                .apply(covalence_hol_eval::mk_nat(dim))?
                .apply(sign)?;
            let payload = covalence_hol_eval::defs::pair(
                Type::nat(),
                covalence_hol_eval::defs::prod(Type::nat(), sx.clone()),
            )
            .apply(covalence_hol_eval::mk_nat(size))?
            .apply(tail)?;
            allowed.push(value.clone().equals(shape_ctor.clone().apply(payload)?)?);
        }
    }
    let (_, splat_ctor) = theory.constructor_named("SPLAT")?;
    for size in [8u64, 16, 32, 64] {
        allowed.push(
            value
                .clone()
                .equals(splat_ctor.clone().apply(covalence_hol_eval::mk_nat(size))?)?,
        );
    }
    let (_, zero_ctor) = theory.constructor_named("ZERO")?;
    for size in [32u64, 64] {
        allowed.push(
            value
                .clone()
                .equals(zero_ctor.clone().apply(covalence_hol_eval::mk_nat(size))?)?,
        );
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("vector load universe is nonempty");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vloadop")),
        vec![&shape.refinements[0], &zero.refinements[0]],
    )))
}

fn rigid_case_name(argument: &SpecTecArg) -> Option<&str> {
    let SpecTecArg::Exp {
        e: SpecTecExp::Case { op, e1 },
    } = argument
    else {
        return None;
    };
    matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty())
        .then(|| op.fragments().first().map(String::as_str))
        .flatten()
        .filter(|_| op.fragments().len() == 1)
}

fn exact_vload_cases(
    shape: &super::type_family::CaseShape<'_>,
    splat: &super::type_family::CaseShape<'_>,
    zero: &super::type_family::CaseShape<'_>,
    vectype: &str,
) -> bool {
    if shape.operator.fragments() != ["SHAPE", "X", "_", ""]
        || splat.operator.fragments() != ["SPLAT"]
        || zero.operator.fragments() != ["ZERO"]
        || [shape, splat, zero]
            .iter()
            .any(|case| !case.params.is_empty())
    {
        return false;
    }
    let SpecTecTyp::Tup { ets: shape_fields } = shape.payload else {
        return false;
    };
    let SpecTecTyp::Tup { ets: splat_fields } = splat.payload else {
        return false;
    };
    let SpecTecTyp::Tup { ets: zero_fields } = zero.payload else {
        return false;
    };
    let exact_size = |field: &SpecTecTypBind| {
        matches!(
            field,
            SpecTecTypBind::Bind {
                typ: SpecTecTyp::Var { x, as1 },
                ..
            } if x == "sz" && as1.is_empty()
        )
    };
    if !matches!(shape_fields.as_slice(), [size, SpecTecTypBind::Bind { id, .. }, SpecTecTypBind::Bind { typ: SpecTecTyp::Var { x, as1 }, .. }]
        if exact_size(size) && id == "M" && x == "sx" && as1.is_empty())
        || !matches!(splat_fields.as_slice(), [size] if exact_size(size))
        || !matches!(zero_fields.as_slice(), [size] if exact_size(size))
    {
        return false;
    }
    matches!(shape.refinements, [SpecTecPrem::If { e }] if exact_vload_shape_guard(e, vectype))
        && splat.refinements.is_empty()
        && matches!(zero.refinements, [SpecTecPrem::If { e }] if exact_vload_zero_guard(e))
}

fn exact_vload_shape_guard(e: &SpecTecExp, vectype: &str) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Eq,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    let SpecTecExp::Cvt {
        nt1: SpecTecNumTyp::Nat,
        nt2: SpecTecNumTyp::Rat,
        e1: product,
    } = e1.as_ref()
    else {
        return false;
    };
    let left_ok = matches!(
        product.as_ref(),
        SpecTecExp::Bin {
            op: SpecTecBinOp::Mul,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
            e1: size,
            e2: dim,
        } if matches!(
            size.as_ref(),
            SpecTecExp::Proj { e1, i: 0 } if matches!(
                e1.as_ref(),
                SpecTecExp::Uncase { e1, op }
                    if op.fragments() == ["", ""]
                        && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == "sz")
            )
        ) && matches!(dim.as_ref(), SpecTecExp::Var { id } if id == "M")
    );
    let right_ok = matches!(
        e2.as_ref(),
        SpecTecExp::Bin {
            op: SpecTecBinOp::Div,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
            e1: numerator,
            e2: denominator,
        } if matches!(
            numerator.as_ref(),
            SpecTecExp::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Rat,
                e1,
            } if matches!(
                e1.as_ref(),
                SpecTecExp::Call { x, as1 }
                    if x == "vsize"
                        && matches!(as1.as_slice(), [SpecTecArg::Exp {
                            e: SpecTecExp::Var { id }
                        }] if id == vectype)
            )
        ) && matches!(
            denominator.as_ref(),
            SpecTecExp::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Rat,
                e1,
            } if matches!(e1.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
        )
    );
    left_ok && right_ok
}

fn exact_vload_zero_guard(e: &SpecTecExp) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Ge,
            e1,
            e2,
            ..
        } if matches!(
            e1.as_ref(),
            SpecTecExp::Proj { e1, i: 0 } if matches!(
                e1.as_ref(),
                SpecTecExp::Uncase { e1, op }
                    if op.fragments() == ["", ""]
                        && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == "sz")
            )
        ) && matches!(e2.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(32) })
    )
}

fn lower_vector_unary_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vunop_" {
        return Ok(None);
    }
    let [argument] = arguments else {
        return Ok(None);
    };
    let Some((lane, dim)) = rigid_vector_shape(argument) else {
        return Ok(None);
    };
    if !matches!(
        (lane, dim),
        ("I8", 16) | ("I16", 8) | ("I32", 4) | ("I64", 2) | ("F32", 4) | ("F64", 2)
    ) {
        return Ok(None);
    }
    let [integer, float] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(integer_cases) = &integer.shape else {
        return Ok(None);
    };
    let TypeShape::Variant(float_cases) = &float.shape else {
        return Ok(None);
    };
    let [abs_i, neg_i, popcnt] = integer_cases.as_slice() else {
        return Ok(None);
    };
    let [abs_f, neg_f, sqrt, ceil, floor, trunc, nearest] = float_cases.as_slice() else {
        return Ok(None);
    };
    if !exact_unit_case(abs_i, "ABS")
        || !exact_unit_case(neg_i, "NEG")
        || popcnt.operator.fragments() != ["POPCNT"]
        || !matches!(
            (popcnt.payload, popcnt.params, popcnt.refinements),
            (SpecTecTyp::Tup { ets }, [], [SpecTecPrem::If { e }])
                if ets.is_empty() && exact_vunop_popcnt_guard(e)
        )
        || [abs_f, neg_f, sqrt, ceil, floor, trunc, nearest]
            .into_iter()
            .zip(["ABS", "NEG", "SQRT", "CEIL", "FLOOR", "TRUNC", "NEAREST"])
            .any(|(case, name)| !exact_unit_case(case, name))
    {
        return Ok(None);
    }
    let (selected, constructors, names): (
        &super::type_family::FamilyInstance<'_>,
        &[&str],
        &[&str],
    ) = if lane.starts_with('I') {
        (
            integer,
            &["ABS", "NEG", "POPCNT"],
            if lane == "I8" {
                &["ABS", "NEG", "POPCNT"]
            } else {
                &["ABS", "NEG"]
            },
        )
    } else {
        (
            float,
            &["ABS", "NEG", "SQRT", "CEIL", "FLOOR", "TRUNC", "NEAREST"],
            &["ABS", "NEG", "SQRT", "CEIL", "FLOOR", "TRUNC", "NEAREST"],
        )
    };
    let theory = CoprodBackend.theory(&Variant::new(
        constructors
            .iter()
            .map(|name| VCtor::new(*name, Type::unit()))
            .collect(),
    ))?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let value = Term::free("__vunop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::new();
    for name in names {
        let (_, ctor) = theory.constructor_named(name)?;
        allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("vector unary universe is nonempty");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vunop")),
        match &selected.shape {
            TypeShape::Variant(cases) => cases
                .iter()
                .flat_map(|case| case.refinements.iter())
                .collect(),
            _ => unreachable!("validated variant"),
        },
    )))
}

fn rigid_vector_shape(argument: &SpecTecArg) -> Option<(&str, u64)> {
    let SpecTecArg::Exp { e } = argument else {
        return None;
    };
    rigid_vector_shape_exp(e)
}

fn rigid_vector_shape_exp(e: &SpecTecExp) -> Option<(&str, u64)> {
    let SpecTecExp::Case { op, e1 } = e else {
        return None;
    };
    if op.fragments() != ["", "X", ""] {
        return None;
    }
    let SpecTecExp::Tup { es } = e1.as_ref() else {
        return None;
    };
    let [lane, dim] = es.as_slice() else {
        return None;
    };
    let SpecTecExp::Case {
        op: lane_op,
        e1: lane_payload,
    } = lane
    else {
        return None;
    };
    let [lane] = lane_op.fragments() else {
        return None;
    };
    if !matches!(lane_payload.as_ref(), SpecTecExp::Tup { es } if es.is_empty()) {
        return None;
    }
    let SpecTecExp::Case {
        op: dim_op,
        e1: dim_payload,
    } = dim
    else {
        return None;
    };
    let SpecTecExp::Tup { es } = dim_payload.as_ref() else {
        return None;
    };
    (dim_op.fragments() == ["", ""])
        .then_some(es.as_slice())
        .is_some_and(|es| {
            matches!(
                es,
                [SpecTecExp::Num {
                    n: SpecTecNum::Nat(_)
                }]
            )
        })
        .then(|| match &es[0] {
            SpecTecExp::Num {
                n: SpecTecNum::Nat(n),
            } => Some((lane.as_str(), *n)),
            _ => None,
        })
        .flatten()
}

fn exact_vunop_popcnt_guard(e: &SpecTecExp) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1,
            e2,
            ..
        } if matches!(
            e1.as_ref(),
            SpecTecExp::Call { x, as1 }
                if x == "lsizenn"
                    && matches!(as1.as_slice(), [SpecTecArg::Exp {
                        e: SpecTecExp::Sub { e1, .. }
                    }] if matches!(e1.as_ref(), SpecTecExp::Var { id } if id == "Jnn"))
        ) && matches!(e2.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(8) })
    )
}

fn lower_vector_extended_ternary_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vextternop__" {
        return Ok(None);
    }
    let [left, right] = arguments else {
        return Ok(None);
    };
    let Some((left_lane, left_dim)) = rigid_integer_shape(left) else {
        return Ok(None);
    };
    let Some((right_lane, right_dim)) = rigid_integer_shape(right) else {
        return Ok(None);
    };
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    if case.operator.fragments() != ["RELAXED_DOT_ADDS"]
        || !case.params.is_empty()
        || !matches!(case.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        || !matches!(case.refinements, [SpecTecPrem::If { e }] if exact_vextternop_guard(e))
        || !exact_vextternop_instance(instance)
    {
        return Ok(None);
    }
    let theory = CoprodBackend.theory(&Variant::new(vec![VCtor::new(
        "RELAXED_DOT_ADDS",
        Type::unit(),
    )]))?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let body = if (left_lane, left_dim, right_lane, right_dim) == ("I8", 16, "I32", 4) {
        let value = Term::free("__vextternop", carrier.clone());
        let (_, ctor) = theory.constructor_named("RELAXED_DOT_ADDS")?;
        value.equals(ctor.clone().apply(covalence_hol_eval::defs::unit_nil())?)?
    } else {
        covalence_hol_eval::mk_bool(false)
    };
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vextternop")),
        vec![&case.refinements[0]],
    )))
}

fn rigid_integer_shape(argument: &SpecTecArg) -> Option<(&str, u64)> {
    let SpecTecArg::Exp {
        e: SpecTecExp::Case { op, e1 },
    } = argument
    else {
        return None;
    };
    if op.fragments() != ["", ""] {
        return None;
    }
    let SpecTecExp::Tup { es } = e1.as_ref() else {
        return None;
    };
    let [shape] = es.as_slice() else {
        return None;
    };
    rigid_vector_shape_exp(shape).filter(|(lane, _)| lane.starts_with('I'))
}

fn exact_vextternop_instance(instance: &super::type_family::FamilyInstance<'_>) -> bool {
    let [
        SpecTecParam::Exp { x: lane1, .. },
        SpecTecParam::Exp { x: dim1, .. },
        SpecTecParam::Exp { x: lane2, .. },
        SpecTecParam::Exp { x: dim2, .. },
    ] = instance.params
    else {
        return false;
    };
    let [left, right] = instance.args else {
        return false;
    };
    exact_ishape_pattern(left, lane1, dim1) && exact_ishape_pattern(right, lane2, dim2)
}

fn exact_ishape_pattern(argument: &SpecTecArg, lane: &str, dim: &str) -> bool {
    let SpecTecArg::Exp {
        e: SpecTecExp::Case { op, e1 },
    } = argument
    else {
        return false;
    };
    let SpecTecExp::Tup { es } = e1.as_ref() else {
        return false;
    };
    let [
        SpecTecExp::Case {
            op: shape_op,
            e1: shape_payload,
        },
    ] = es.as_slice()
    else {
        return false;
    };
    let SpecTecExp::Tup { es: fields } = shape_payload.as_ref() else {
        return false;
    };
    matches!(
        fields.as_slice(),
        [
            SpecTecExp::Sub { e1, .. },
            SpecTecExp::Case { op: dim_op, e1: dim_payload },
        ] if op.fragments() == ["", ""]
            && shape_op.fragments() == ["", "X", ""]
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == lane)
            && dim_op.fragments() == ["", ""]
            && matches!(
                dim_payload.as_ref(),
                SpecTecExp::Tup { es }
                    if matches!(es.as_slice(), [SpecTecExp::Var { id }] if id == dim)
            )
    )
}

fn exact_vextternop_guard(e: &SpecTecExp) -> bool {
    let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    matches!(
        e1.as_ref(),
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1: product,
            e2: width2,
            ..
        } if matches!(
            product.as_ref(),
            SpecTecExp::Bin {
                op: SpecTecBinOp::Mul,
                e1: four,
                e2: width1,
                ..
            } if matches!(four.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(4) })
                && exact_lane_width_call(width1, "lsizenn1", "Jnn_1")
        ) && exact_lane_width_call(width2, "lsizenn2", "Jnn_2")
    ) && matches!(
        e2.as_ref(),
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1: width2,
            e2: thirty_two,
            ..
        } if exact_lane_width_call(width2, "lsizenn2", "Jnn_2")
            && matches!(thirty_two.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(32) })
    )
}

fn exact_lane_width_call(e: &SpecTecExp, function: &str, param: &str) -> bool {
    matches!(
        e,
        SpecTecExp::Call { x, as1 }
            if x == function
                && matches!(
                    as1.as_slice(),
                    [SpecTecArg::Exp { e: SpecTecExp::Sub { e1, .. } }]
                        if matches!(e1.as_ref(), SpecTecExp::Var { id } if id == param)
                )
    )
}

fn lower_vector_extended_unary_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vextunop__" {
        return Ok(None);
    }
    let [left, right] = arguments else {
        return Ok(None);
    };
    let Some((left_lane, left_dim)) = rigid_integer_shape(left) else {
        return Ok(None);
    };
    let Some((right_lane, right_dim)) = rigid_integer_shape(right) else {
        return Ok(None);
    };
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    if case.operator.fragments() != ["EXTADD_PAIRWISE"]
        || !case.params.is_empty()
        || !matches!(
            case.payload,
            SpecTecTyp::Tup { ets }
                if matches!(
                    ets.as_slice(),
                    [SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x, as1 },
                        ..
                    }] if x == "sx" && as1.is_empty()
                )
        )
        || !matches!(case.refinements, [SpecTecPrem::If { e }] if exact_vextunop_guard(e))
        || !exact_vextternop_instance(instance)
    {
        return Ok(None);
    }
    let sx = signedness_carrier()?;
    let theory = CoprodBackend.theory(&Variant::new(vec![VCtor::new(
        "EXTADD_PAIRWISE",
        sx.clone(),
    )]))?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let valid = matches!(
        (left_lane, left_dim, right_lane, right_dim),
        ("I8", 16, "I16", 8) | ("I16", 8, "I32", 4)
    );
    let body = if valid {
        let value = Term::free("__vextunop", carrier.clone());
        let (_, ctor) = theory.constructor_named("EXTADD_PAIRWISE")?;
        let sx_theory = CoprodBackend.theory(&Variant::new(vec![
            VCtor::new("U", Type::unit()),
            VCtor::new("S", Type::unit()),
        ]))?;
        let unit = covalence_hol_eval::defs::unit_nil();
        let (_, unsigned) = sx_theory.constructor_named("U")?;
        let (_, signed) = sx_theory.constructor_named("S")?;
        value
            .clone()
            .equals(ctor.clone().apply(unsigned.clone().apply(unit.clone())?)?)?
            .or(value.equals(ctor.clone().apply(signed.clone().apply(unit)?)?)?)?
    } else {
        covalence_hol_eval::mk_bool(false)
    };
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vextunop")),
        vec![&case.refinements[0]],
    )))
}

fn exact_vextunop_guard(e: &SpecTecExp) -> bool {
    let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        e1: lower,
        e2: tail,
        ..
    } = e
    else {
        return false;
    };
    let twice_left = |e: &SpecTecExp| {
        matches!(
            e,
            SpecTecExp::Bin {
                op: SpecTecBinOp::Mul,
                e1: two,
                e2: width,
                ..
            } if matches!(two.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
                && exact_lane_width_call(width, "lsizenn1", "Jnn_1")
        )
    };
    matches!(
        lower.as_ref(),
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Le,
            e1: sixteen,
            e2: twice,
            ..
        } if matches!(sixteen.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(16) })
            && twice_left(twice)
    ) && matches!(
        tail.as_ref(),
        SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            e1: equality,
            e2: upper,
            ..
        } if matches!(
            equality.as_ref(),
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                e1: twice,
                e2: right,
                ..
            } if twice_left(twice) && exact_lane_width_call(right, "lsizenn2", "Jnn_2")
        ) && matches!(
            upper.as_ref(),
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Le,
                e1: right,
                e2: thirty_two,
                ..
            } if exact_lane_width_call(right, "lsizenn2", "Jnn_2")
                && matches!(thirty_two.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(32) })
        )
    )
}

fn lower_vector_extended_binary_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vextbinop__" {
        return Ok(None);
    }
    let [left, right] = arguments else {
        return Ok(None);
    };
    let Some((left_lane, left_dim)) = rigid_integer_shape(left) else {
        return Ok(None);
    };
    let Some((right_lane, right_dim)) = rigid_integer_shape(right) else {
        return Ok(None);
    };
    let [instance] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [extmul, dot, relaxed_dot] = cases.as_slice() else {
        return Ok(None);
    };
    if extmul.operator.fragments() != ["EXTMUL"]
        || dot.operator.fragments() != ["DOTS"]
        || relaxed_dot.operator.fragments() != ["RELAXED_DOTS"]
        || [extmul, dot, relaxed_dot]
            .iter()
            .any(|case| !case.params.is_empty())
        || !exact_half_signed_payload(extmul.payload)
        || !matches!(dot.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        || !matches!(relaxed_dot.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        || !matches!(extmul.refinements, [SpecTecPrem::If { e }] if exact_vextbinop_guard(e, SpecTecCmpOp::Ge, 16))
        || !matches!(dot.refinements, [SpecTecPrem::If { e }] if exact_vextbinop_guard(e, SpecTecCmpOp::Eq, 32))
        || !matches!(relaxed_dot.refinements, [SpecTecPrem::If { e }] if exact_vextbinop_guard(e, SpecTecCmpOp::Eq, 16))
        || !exact_vextternop_instance(instance)
    {
        return Ok(None);
    }
    let half = CoprodBackend
        .theory(&Variant::new(vec![
            VCtor::new("LOW", Type::unit()),
            VCtor::new("HIGH", Type::unit()),
        ]))?
        .carrier()
        .clone();
    let sx = signedness_carrier()?;
    let theory = CoprodBackend.theory(&Variant::new(vec![
        VCtor::new(
            "EXTMUL",
            covalence_hol_eval::defs::prod(half.clone(), sx.clone()),
        ),
        VCtor::new("DOTS", Type::unit()),
        VCtor::new("RELAXED_DOTS", Type::unit()),
    ]))?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let pair = (left_lane, left_dim, right_lane, right_dim);
    let doubled = matches!(
        pair,
        ("I8", 16, "I16", 8) | ("I16", 8, "I32", 4) | ("I32", 4, "I64", 2)
    );
    let value = Term::free("__vextbinop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::new();
    if doubled {
        let half_theory = CoprodBackend.theory(&Variant::new(vec![
            VCtor::new("LOW", Type::unit()),
            VCtor::new("HIGH", Type::unit()),
        ]))?;
        let sx_theory = CoprodBackend.theory(&Variant::new(vec![
            VCtor::new("U", Type::unit()),
            VCtor::new("S", Type::unit()),
        ]))?;
        let (_, ctor) = theory.constructor_named("EXTMUL")?;
        for half_name in ["LOW", "HIGH"] {
            for sign_name in ["U", "S"] {
                let (_, half_ctor) = half_theory.constructor_named(half_name)?;
                let (_, sign_ctor) = sx_theory.constructor_named(sign_name)?;
                let payload = covalence_hol_eval::defs::pair(half.clone(), sx.clone())
                    .apply(half_ctor.clone().apply(unit.clone())?)?
                    .apply(sign_ctor.clone().apply(unit.clone())?)?;
                allowed.push(value.clone().equals(ctor.clone().apply(payload)?)?);
            }
        }
    }
    for (valid, name) in [
        (pair == ("I16", 8, "I32", 4), "DOTS"),
        (pair == ("I8", 16, "I16", 8), "RELAXED_DOTS"),
    ] {
        if valid {
            let (_, ctor) = theory.constructor_named(name)?;
            allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
        }
    }
    let body = if allowed.is_empty() {
        covalence_hol_eval::mk_bool(false)
    } else {
        let mut allowed = allowed.into_iter();
        let first = allowed.next().expect("checked nonempty");
        allowed.try_fold(first, |left, right| left.or(right))?
    };
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vextbinop")),
        vec![
            &extmul.refinements[0],
            &dot.refinements[0],
            &relaxed_dot.refinements[0],
        ],
    )))
}

fn exact_half_signed_payload(payload: &SpecTecTyp) -> bool {
    matches!(
        payload,
        SpecTecTyp::Tup { ets }
            if matches!(
                ets.as_slice(),
                [
                    SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x: half, as1: half_args },
                        ..
                    },
                    SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x: sx, as1: sx_args },
                        ..
                    },
                ] if half == "half" && half_args.is_empty() && sx == "sx" && sx_args.is_empty()
            )
    )
}

fn exact_vextbinop_guard(e: &SpecTecExp, bound_op: SpecTecCmpOp, bound: u64) -> bool {
    let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        e1: equality,
        e2: boundary,
        ..
    } = e
    else {
        return false;
    };
    matches!(
        equality.as_ref(),
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1: twice,
            e2: right,
            ..
        } if matches!(
            twice.as_ref(),
            SpecTecExp::Bin {
                op: SpecTecBinOp::Mul,
                e1: two,
                e2: left,
                ..
            } if matches!(two.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
                && exact_lane_width_call(left, "lsizenn1", "Jnn_1")
        ) && exact_lane_width_call(right, "lsizenn2", "Jnn_2")
    ) && matches!(
        boundary.as_ref(),
        SpecTecExp::Cmp { op, e1: right, e2: limit, .. }
            if *op == bound_op
                && exact_lane_width_call(right, "lsizenn2", "Jnn_2")
                && matches!(limit.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(n) } if *n == bound)
    )
}

fn lower_vector_relation_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vrelop_" {
        return Ok(None);
    }
    let [argument] = arguments else {
        return Ok(None);
    };
    let Some((lane, dim)) = rigid_vector_shape(argument) else {
        return Ok(None);
    };
    if !matches!(
        (lane, dim),
        ("I8", 16) | ("I16", 8) | ("I32", 4) | ("I64", 2) | ("F32", 4) | ("F64", 2)
    ) {
        return Ok(None);
    }
    let [integer, float] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(integer_cases) = &integer.shape else {
        return Ok(None);
    };
    let TypeShape::Variant(float_cases) = &float.shape else {
        return Ok(None);
    };
    let [eq_i, ne_i, lt_i, gt_i, le_i, ge_i] = integer_cases.as_slice() else {
        return Ok(None);
    };
    let [eq_f, ne_f, lt_f, gt_f, le_f, ge_f] = float_cases.as_slice() else {
        return Ok(None);
    };
    if !exact_unit_case(eq_i, "EQ")
        || !exact_unit_case(ne_i, "NE")
        || [lt_i, gt_i, le_i, ge_i]
            .into_iter()
            .zip(["LT", "GT", "LE", "GE"])
            .any(|(case, name)| !exact_signed_relation_case(case, name))
        || [eq_f, ne_f, lt_f, gt_f, le_f, ge_f]
            .into_iter()
            .zip(["EQ", "NE", "LT", "GT", "LE", "GE"])
            .any(|(case, name)| !exact_unit_case(case, name))
        || !exact_vector_shape_instance(integer, "Jnn")
        || !exact_vector_shape_instance(float, "Fnn")
    {
        return Ok(None);
    }
    let integer_lane = lane.starts_with('I');
    let sx = signedness_carrier()?;
    let variant = if integer_lane {
        Variant::new(vec![
            VCtor::new("EQ", Type::unit()),
            VCtor::new("NE", Type::unit()),
            VCtor::new("LT", sx.clone()),
            VCtor::new("GT", sx.clone()),
            VCtor::new("LE", sx.clone()),
            VCtor::new("GE", sx.clone()),
        ])
    } else {
        Variant::new(
            ["EQ", "NE", "LT", "GT", "LE", "GE"]
                .into_iter()
                .map(|name| VCtor::new(name, Type::unit()))
                .collect(),
        )
    };
    let theory = CoprodBackend.theory(&variant)?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let value = Term::free("__vrelop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::new();
    for name in ["EQ", "NE"] {
        let (_, ctor) = theory.constructor_named(name)?;
        allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
    }
    if integer_lane {
        let sx_theory = CoprodBackend.theory(&Variant::new(vec![
            VCtor::new("U", Type::unit()),
            VCtor::new("S", Type::unit()),
        ]))?;
        for name in ["LT", "GT", "LE", "GE"] {
            let (_, ctor) = theory.constructor_named(name)?;
            for sign in if lane == "I64" {
                &["S"][..]
            } else {
                &["U", "S"][..]
            } {
                let (_, sign_ctor) = sx_theory.constructor_named(sign)?;
                allowed.push(
                    value
                        .clone()
                        .equals(ctor.clone().apply(sign_ctor.clone().apply(unit.clone())?)?)?,
                );
            }
        }
    } else {
        for name in ["LT", "GT", "LE", "GE"] {
            let (_, ctor) = theory.constructor_named(name)?;
            allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
        }
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("relation universe nonempty");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vrelop")),
        if integer_lane {
            vec![
                &lt_i.refinements[0],
                &gt_i.refinements[0],
                &le_i.refinements[0],
                &ge_i.refinements[0],
            ]
        } else {
            vec![]
        },
    )))
}

fn exact_signed_relation_case(case: &super::type_family::CaseShape<'_>, name: &str) -> bool {
    case.operator.fragments() == [name]
        && case.params.is_empty()
        && matches!(
            case.payload,
            SpecTecTyp::Tup { ets }
                if matches!(
                    ets.as_slice(),
                    [SpecTecTypBind::Bind {
                        id,
                        typ: SpecTecTyp::Var { x, as1 },
                    }] if id == "sx" && x == "sx" && as1.is_empty()
                )
        )
        && matches!(case.refinements, [SpecTecPrem::If { e }] if exact_signed_relation_guard(e))
}

fn exact_signed_relation_guard(e: &SpecTecExp) -> bool {
    matches!(
        e,
        SpecTecExp::Bin {
            op: SpecTecBinOp::Or,
            e1,
            e2,
            ..
        } if matches!(
            e1.as_ref(),
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Ne,
                e1: width,
                e2: sixty_four,
                ..
            } if exact_lane_width_call(width, "lsizenn", "Jnn")
                && matches!(sixty_four.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(64) })
        ) && matches!(
            e2.as_ref(),
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                e1: sign,
                e2: signed,
                ..
            } if matches!(sign.as_ref(), SpecTecExp::Var { id } if id == "sx")
                && matches!(
                    signed.as_ref(),
                    SpecTecExp::Case { op, e1 }
                        if op.fragments() == ["S"]
                            && matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty())
                )
        )
    )
}

fn exact_vector_shape_instance(
    instance: &super::type_family::FamilyInstance<'_>,
    lane_kind: &str,
) -> bool {
    let [
        SpecTecParam::Exp { x: lane, .. },
        SpecTecParam::Exp { x: dim, .. },
    ] = instance.params
    else {
        return false;
    };
    let [
        SpecTecArg::Exp {
            e: SpecTecExp::Case { op, e1 },
        },
    ] = instance.args
    else {
        return false;
    };
    let SpecTecExp::Tup { es } = e1.as_ref() else {
        return false;
    };
    matches!(
        es.as_slice(),
        [
            SpecTecExp::Sub { t1, t2, e1 },
            SpecTecExp::Case { op: dim_op, e1: dim_payload },
        ] if op.fragments() == ["", "X", ""]
            && matches!(t1, SpecTecTyp::Var { x, as1 } if x == lane_kind && as1.is_empty())
            && matches!(t2, SpecTecTyp::Var { x, as1 } if x == "lanetype" && as1.is_empty())
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == lane)
            && dim_op.fragments() == ["", ""]
            && matches!(
                dim_payload.as_ref(),
                SpecTecExp::Tup { es }
                    if matches!(es.as_slice(), [SpecTecExp::Var { id }] if id == dim)
            )
    )
}

fn lower_vector_binary_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vbinop_" {
        return Ok(None);
    }
    let [argument] = arguments else {
        return Ok(None);
    };
    let Some((lane, dim)) = rigid_vector_shape(argument) else {
        return Ok(None);
    };
    if !matches!(
        (lane, dim),
        ("I8", 16) | ("I16", 8) | ("I32", 4) | ("I64", 2) | ("F32", 4) | ("F64", 2)
    ) {
        return Ok(None);
    }
    let [integer, float] = family.instances.as_slice() else {
        return Ok(None);
    };
    let TypeShape::Variant(integer_cases) = &integer.shape else {
        return Ok(None);
    };
    let TypeShape::Variant(float_cases) = &float.shape else {
        return Ok(None);
    };
    let [
        add,
        sub,
        add_sat,
        sub_sat,
        mul,
        avgr,
        q15,
        relaxed_q15,
        min,
        max,
    ] = integer_cases.as_slice()
    else {
        return Ok(None);
    };
    let float_names = [
        "ADD",
        "SUB",
        "MUL",
        "DIV",
        "MIN",
        "MAX",
        "PMIN",
        "PMAX",
        "RELAXED_MIN",
        "RELAXED_MAX",
    ];
    if !exact_unit_case(add, "ADD")
        || !exact_unit_case(sub, "SUB")
        || !exact_guarded_signed_case(add_sat, "ADD_SAT", SpecTecCmpOp::Le, 16)
        || !exact_guarded_signed_case(sub_sat, "SUB_SAT", SpecTecCmpOp::Le, 16)
        || !exact_guarded_unit_case(mul, "MUL", SpecTecCmpOp::Ge, 16)
        || !exact_guarded_unit_case(avgr, "AVGRU", SpecTecCmpOp::Le, 16)
        || !exact_guarded_unit_case(q15, "Q15MULR_SATS", SpecTecCmpOp::Eq, 16)
        || !exact_guarded_unit_case(relaxed_q15, "RELAXED_Q15MULRS", SpecTecCmpOp::Eq, 16)
        || !exact_guarded_signed_case(min, "MIN", SpecTecCmpOp::Le, 32)
        || !exact_guarded_signed_case(max, "MAX", SpecTecCmpOp::Le, 32)
        || float_cases.len() != float_names.len()
        || float_cases
            .iter()
            .zip(float_names)
            .any(|(case, name)| !exact_unit_case(case, name))
        || !exact_vector_shape_instance(integer, "Jnn")
        || !exact_vector_shape_instance(float, "Fnn")
    {
        return Ok(None);
    }
    let integer_lane = lane.starts_with('I');
    let sx = signedness_carrier()?;
    let variant = if integer_lane {
        Variant::new(vec![
            VCtor::new("ADD", Type::unit()),
            VCtor::new("SUB", Type::unit()),
            VCtor::new("ADD_SAT", sx.clone()),
            VCtor::new("SUB_SAT", sx.clone()),
            VCtor::new("MUL", Type::unit()),
            VCtor::new("AVGRU", Type::unit()),
            VCtor::new("Q15MULR_SATS", Type::unit()),
            VCtor::new("RELAXED_Q15MULRS", Type::unit()),
            VCtor::new("MIN", sx.clone()),
            VCtor::new("MAX", sx.clone()),
        ])
    } else {
        Variant::new(
            float_names
                .into_iter()
                .map(|name| VCtor::new(name, Type::unit()))
                .collect(),
        )
    };
    let theory = CoprodBackend.theory(&variant)?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let value = Term::free("__vbinop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let width = match lane {
        "I8" => 8,
        "I16" => 16,
        "I32" | "F32" => 32,
        "I64" | "F64" => 64,
        _ => unreachable!(),
    };
    let mut allowed = Vec::new();
    if integer_lane {
        let sx_theory = CoprodBackend.theory(&Variant::new(vec![
            VCtor::new("U", Type::unit()),
            VCtor::new("S", Type::unit()),
        ]))?;
        for name in ["ADD", "SUB"] {
            let (_, ctor) = theory.constructor_named(name)?;
            allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
        }
        for (valid, name) in [
            (width >= 16, "MUL"),
            (width <= 16, "AVGRU"),
            (width == 16, "Q15MULR_SATS"),
            (width == 16, "RELAXED_Q15MULRS"),
        ] {
            if valid {
                let (_, ctor) = theory.constructor_named(name)?;
                allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
            }
        }
        for (valid, name) in [
            (width <= 16, "ADD_SAT"),
            (width <= 16, "SUB_SAT"),
            (width <= 32, "MIN"),
            (width <= 32, "MAX"),
        ] {
            if valid {
                let (_, ctor) = theory.constructor_named(name)?;
                for sign in ["U", "S"] {
                    let (_, sign_ctor) = sx_theory.constructor_named(sign)?;
                    allowed.push(
                        value
                            .clone()
                            .equals(ctor.clone().apply(sign_ctor.clone().apply(unit.clone())?)?)?,
                    );
                }
            }
        }
    } else {
        for name in float_names {
            let (_, ctor) = theory.constructor_named(name)?;
            allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
        }
    }
    let mut allowed = allowed.into_iter();
    let first = allowed.next().expect("binary universe nonempty");
    let body = allowed.try_fold(first, |left, right| left.or(right))?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vbinop")),
        if integer_lane {
            vec![
                &add_sat.refinements[0],
                &sub_sat.refinements[0],
                &mul.refinements[0],
                &avgr.refinements[0],
                &q15.refinements[0],
                &relaxed_q15.refinements[0],
                &min.refinements[0],
                &max.refinements[0],
            ]
        } else {
            vec![]
        },
    )))
}

fn exact_guarded_signed_case(
    case: &super::type_family::CaseShape<'_>,
    name: &str,
    op: SpecTecCmpOp,
    bound: u64,
) -> bool {
    case.operator.fragments() == [name]
        && case.params.is_empty()
        && matches!(
            case.payload,
            SpecTecTyp::Tup { ets }
                if matches!(
                    ets.as_slice(),
                    [SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x, as1 },
                        ..
                    }] if x == "sx" && as1.is_empty()
                )
        )
        && matches!(case.refinements, [SpecTecPrem::If { e }] if exact_lane_bound(e, op, bound))
}

fn exact_guarded_unit_case(
    case: &super::type_family::CaseShape<'_>,
    name: &str,
    op: SpecTecCmpOp,
    bound: u64,
) -> bool {
    case.operator.fragments() == [name]
        && case.params.is_empty()
        && matches!(case.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        && matches!(case.refinements, [SpecTecPrem::If { e }] if exact_lane_bound(e, op, bound))
}

fn exact_lane_bound(e: &SpecTecExp, expected: SpecTecCmpOp, bound: u64) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp { op, e1, e2, .. }
            if *op == expected
                && exact_lane_width_call(e1, "lsizenn", "Jnn")
                && matches!(e2.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(n) } if *n == bound)
    )
}

fn lower_vector_conversion_operator<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "vcvtop__" {
        return Ok(None);
    }
    let [left_arg, right_arg] = arguments else {
        return Ok(None);
    };
    let Some((left_lane, _left_dim)) = rigid_vector_shape(left_arg) else {
        return Ok(None);
    };
    let Some((right_lane, _right_dim)) = rigid_vector_shape(right_arg) else {
        return Ok(None);
    };
    let [ii, iff, fi, ff] = family.instances.as_slice() else {
        return Ok(None);
    };
    let left_i = left_lane.starts_with('I');
    let right_i = right_lane.starts_with('I');
    let selected = match (left_i, right_i) {
        (true, true) => ii,
        (true, false) => iff,
        (false, true) => fi,
        (false, false) => ff,
    };
    if !exact_vcvtop_sources(ii, iff, fi, ff) {
        return Ok(None);
    }
    let half_theory = CoprodBackend.theory(&Variant::new(vec![
        VCtor::new("LOW", Type::unit()),
        VCtor::new("HIGH", Type::unit()),
    ]))?;
    let half = half_theory.carrier().clone();
    let sx_theory = CoprodBackend.theory(&Variant::new(vec![
        VCtor::new("U", Type::unit()),
        VCtor::new("S", Type::unit()),
    ]))?;
    let sx = sx_theory.carrier().clone();
    let zero_theory =
        CoprodBackend.theory(&Variant::new(vec![VCtor::new("ZERO", Type::unit())]))?;
    let zero = zero_theory.carrier().clone();
    let (variant, class): (Variant, u8) = match (left_i, right_i) {
        (true, true) => (
            Variant::new(vec![VCtor::new(
                "EXTEND",
                covalence_hol_eval::defs::prod(half.clone(), sx.clone()),
            )]),
            0,
        ),
        (true, false) => (
            Variant::new(vec![VCtor::new(
                "CONVERT",
                covalence_hol_eval::defs::prod(
                    covalence_hol_eval::defs::option(half.clone()),
                    sx.clone(),
                ),
            )]),
            1,
        ),
        (false, true) => (
            Variant::new(vec![
                VCtor::new(
                    "TRUNC_SAT",
                    covalence_hol_eval::defs::prod(
                        sx.clone(),
                        covalence_hol_eval::defs::option(zero.clone()),
                    ),
                ),
                VCtor::new(
                    "RELAXED_TRUNC",
                    covalence_hol_eval::defs::prod(
                        sx.clone(),
                        covalence_hol_eval::defs::option(zero.clone()),
                    ),
                ),
            ]),
            2,
        ),
        (false, false) => (
            Variant::new(vec![
                VCtor::new("DEMOTE", zero.clone()),
                VCtor::new("PROMOTELOW", Type::unit()),
            ]),
            3,
        ),
    };
    let theory = CoprodBackend.theory(&variant)?;
    if theory.carrier() != carrier {
        return Ok(None);
    }
    let width = |lane: &str| match lane {
        "I8" => 8u64,
        "I16" => 16,
        "I32" | "F32" => 32,
        "I64" | "F64" => 64,
        _ => unreachable!(),
    };
    let lw = width(left_lane);
    let rw = width(right_lane);
    let value = Term::free("__vcvtop", carrier.clone());
    let unit = covalence_hol_eval::defs::unit_nil();
    let mut allowed = Vec::new();
    match class {
        0 if rw == 2 * lw => {
            let (_, ctor) = theory.constructor_named("EXTEND")?;
            for h in ["LOW", "HIGH"] {
                for s in ["U", "S"] {
                    let (_, hc) = half_theory.constructor_named(h)?;
                    let (_, sc) = sx_theory.constructor_named(s)?;
                    let payload = covalence_hol_eval::defs::pair(half.clone(), sx.clone())
                        .apply(hc.clone().apply(unit.clone())?)?
                        .apply(sc.clone().apply(unit.clone())?)?;
                    allowed.push(value.clone().equals(ctor.clone().apply(payload)?)?);
                }
            }
        }
        1 => {
            let option_half = covalence_hol_eval::defs::option(half.clone());
            let selected_half = if lw == rw && lw == 32 {
                Some(covalence_hol_eval::defs::none(half.clone()))
            } else if rw == 2 * lw {
                let (_, low) = half_theory.constructor_named("LOW")?;
                Some(
                    covalence_hol_eval::defs::some(half.clone())
                        .apply(low.clone().apply(unit.clone())?)?,
                )
            } else {
                None
            };
            if let Some(selected_half) = selected_half {
                let (_, ctor) = theory.constructor_named("CONVERT")?;
                for s in ["U", "S"] {
                    let (_, sc) = sx_theory.constructor_named(s)?;
                    let payload = covalence_hol_eval::defs::pair(option_half.clone(), sx.clone())
                        .apply(selected_half.clone())?
                        .apply(sc.clone().apply(unit.clone())?)?;
                    allowed.push(value.clone().equals(ctor.clone().apply(payload)?)?);
                }
            }
        }
        2 => {
            let option_zero = covalence_hol_eval::defs::option(zero.clone());
            let selected_zero = if lw == rw && lw == 32 {
                Some(covalence_hol_eval::defs::none(zero.clone()))
            } else if lw == 2 * rw {
                let (_, z) = zero_theory.constructor_named("ZERO")?;
                Some(
                    covalence_hol_eval::defs::some(zero.clone())
                        .apply(z.clone().apply(unit.clone())?)?,
                )
            } else {
                None
            };
            if let Some(selected_zero) = selected_zero {
                for name in ["TRUNC_SAT", "RELAXED_TRUNC"] {
                    let (_, ctor) = theory.constructor_named(name)?;
                    for s in ["U", "S"] {
                        let (_, sc) = sx_theory.constructor_named(s)?;
                        let payload =
                            covalence_hol_eval::defs::pair(sx.clone(), option_zero.clone())
                                .apply(sc.clone().apply(unit.clone())?)?
                                .apply(selected_zero.clone())?;
                        allowed.push(value.clone().equals(ctor.clone().apply(payload)?)?);
                    }
                }
            }
        }
        3 => {
            if lw == 2 * rw {
                let (_, ctor) = theory.constructor_named("DEMOTE")?;
                let (_, z) = zero_theory.constructor_named("ZERO")?;
                allowed.push(
                    value
                        .clone()
                        .equals(ctor.clone().apply(z.clone().apply(unit.clone())?)?)?,
                );
            }
            if 2 * lw == rw {
                let (_, ctor) = theory.constructor_named("PROMOTELOW")?;
                allowed.push(value.clone().equals(ctor.clone().apply(unit.clone())?)?);
            }
        }
        _ => {}
    }
    let body = if allowed.is_empty() {
        covalence_hol_eval::mk_bool(false)
    } else {
        let mut allowed = allowed.into_iter();
        let first = allowed.next().expect("checked nonempty");
        allowed.try_fold(first, |left, right| left.or(right))?
    };
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__vcvtop")),
        match &selected.shape {
            TypeShape::Variant(cases) => cases
                .iter()
                .flat_map(|case| case.refinements.iter())
                .collect(),
            _ => unreachable!("validated variant"),
        },
    )))
}

fn exact_vcvtop_sources(
    ii: &super::type_family::FamilyInstance<'_>,
    iff: &super::type_family::FamilyInstance<'_>,
    fi: &super::type_family::FamilyInstance<'_>,
    ff: &super::type_family::FamilyInstance<'_>,
) -> bool {
    let TypeShape::Variant(ii_cases) = &ii.shape else {
        return false;
    };
    let TypeShape::Variant(if_cases) = &iff.shape else {
        return false;
    };
    let TypeShape::Variant(fi_cases) = &fi.shape else {
        return false;
    };
    let TypeShape::Variant(ff_cases) = &ff.shape else {
        return false;
    };
    let [extend] = ii_cases.as_slice() else {
        return false;
    };
    let [convert] = if_cases.as_slice() else {
        return false;
    };
    let [trunc, relaxed] = fi_cases.as_slice() else {
        return false;
    };
    let [demote, promote] = ff_cases.as_slice() else {
        return false;
    };
    extend.operator.fragments() == ["EXTEND"]
        && exact_half_signed_payload(extend.payload)
        && matches!(extend.refinements, [SpecTecPrem::If { e }] if exact_vcvtop_simple_guard(e, 0))
        && convert.operator.fragments() == ["CONVERT"]
        && exact_optional_half_signed_payload(convert.payload)
        && matches!(convert.refinements, [SpecTecPrem::If { e }] if exact_vcvtop_optional_guard(e, "half?", "half", "LOW"))
        && trunc.operator.fragments() == ["TRUNC_SAT"]
        && exact_signed_optional_zero_payload(trunc.payload)
        && matches!(trunc.refinements, [SpecTecPrem::If { e }] if exact_vcvtop_optional_guard(e, "zero?", "zero", "ZERO"))
        && relaxed.operator.fragments() == ["RELAXED_TRUNC"]
        && exact_signed_optional_zero_payload(relaxed.payload)
        && matches!(relaxed.refinements, [SpecTecPrem::If { e }] if exact_vcvtop_optional_guard(e, "zero?", "zero", "ZERO"))
        && demote.operator.fragments() == ["DEMOTE"]
        && matches!(
            demote.payload,
            SpecTecTyp::Tup { ets }
                if matches!(
                    ets.as_slice(),
                    [SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x, as1 },
                        ..
                    }] if x == "zero" && as1.is_empty()
                )
        )
        && matches!(demote.refinements, [SpecTecPrem::If { e }] if exact_vcvtop_simple_guard(e, 1))
        && promote.operator.fragments() == ["PROMOTELOW"]
        && matches!(promote.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        && matches!(promote.refinements, [SpecTecPrem::If { e }] if exact_vcvtop_simple_guard(e, 2))
        && [extend, convert, trunc, relaxed, demote, promote]
            .iter()
            .all(|case| case.params.is_empty())
        && exact_two_vector_shape_instance(ii, "Jnn", "Jnn")
        && exact_two_vector_shape_instance(iff, "Jnn", "Fnn")
        && exact_two_vector_shape_instance(fi, "Fnn", "Jnn")
        && exact_two_vector_shape_instance(ff, "Fnn", "Fnn")
}

fn exact_two_vector_shape_instance(
    instance: &super::type_family::FamilyInstance<'_>,
    left_kind: &str,
    right_kind: &str,
) -> bool {
    let [
        SpecTecParam::Exp { x: left_lane, .. },
        SpecTecParam::Exp { x: left_dim, .. },
        SpecTecParam::Exp { x: right_lane, .. },
        SpecTecParam::Exp { x: right_dim, .. },
    ] = instance.params
    else {
        return false;
    };
    let [left, right] = instance.args else {
        return false;
    };
    exact_vector_shape_pattern(left, left_kind, left_lane, left_dim)
        && exact_vector_shape_pattern(right, right_kind, right_lane, right_dim)
}

fn exact_vector_shape_pattern(
    argument: &SpecTecArg,
    lane_kind: &str,
    lane: &str,
    dim: &str,
) -> bool {
    let SpecTecArg::Exp {
        e: SpecTecExp::Case { op, e1 },
    } = argument
    else {
        return false;
    };
    let SpecTecExp::Tup { es } = e1.as_ref() else {
        return false;
    };
    matches!(
        es.as_slice(),
        [
            SpecTecExp::Sub { t1, t2, e1 },
            SpecTecExp::Case { op: dim_op, e1: dim_payload },
        ] if op.fragments() == ["", "X", ""]
            && matches!(t1, SpecTecTyp::Var { x, as1 } if x == lane_kind && as1.is_empty())
            && matches!(t2, SpecTecTyp::Var { x, as1 } if x == "lanetype" && as1.is_empty())
            && matches!(e1.as_ref(), SpecTecExp::Var { id } if id == lane)
            && dim_op.fragments() == ["", ""]
            && matches!(
                dim_payload.as_ref(),
                SpecTecExp::Tup { es }
                    if matches!(es.as_slice(), [SpecTecExp::Var { id }] if id == dim)
            )
    )
}

fn exact_optional_half_signed_payload(payload: &SpecTecTyp) -> bool {
    matches!(
        payload,
        SpecTecTyp::Tup { ets }
            if matches!(
                ets.as_slice(),
                [
                    SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Iter { t1, it },
                        ..
                    },
                    SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x, as1 },
                        ..
                    },
                ] if matches!(t1.as_ref(), SpecTecTyp::Var { x, as1 } if x == "half" && as1.is_empty())
                    && matches!(it.as_slice(), [SpecTecIter::Opt])
                    && x == "sx" && as1.is_empty()
            )
    )
}

fn exact_signed_optional_zero_payload(payload: &SpecTecTyp) -> bool {
    matches!(
        payload,
        SpecTecTyp::Tup { ets }
            if matches!(
                ets.as_slice(),
                [
                    SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Var { x: sx, as1: sx_args },
                        ..
                    },
                    SpecTecTypBind::Bind {
                        typ: SpecTecTyp::Iter { t1, it },
                        ..
                    },
                ] if sx == "sx" && sx_args.is_empty()
                    && matches!(t1.as_ref(), SpecTecTyp::Var { x, as1 } if x == "zero" && as1.is_empty())
                    && matches!(it.as_slice(), [SpecTecIter::Opt])
            )
    )
}

fn exact_vcvtop_simple_guard(e: &SpecTecExp, class: u8) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Eq,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    let twice = |e: &SpecTecExp, function: &str, param: &str| {
        matches!(
            e,
            SpecTecExp::Bin {
                op: SpecTecBinOp::Mul,
                e1: two,
                e2: width,
                ..
            } if matches!(two.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
                && exact_lane_width_call(width, function, param)
        )
    };
    match class {
        0 => exact_lane_width_call(e1, "lsizenn2", "Jnn_2") && twice(e2, "lsizenn1", "Jnn_1"),
        1 => exact_lane_width_call(e1, "sizenn1", "Fnn_1") && twice(e2, "sizenn2", "Fnn_2"),
        2 => twice(e1, "sizenn1", "Fnn_1") && exact_lane_width_call(e2, "sizenn2", "Fnn_2"),
        _ => false,
    }
}

fn exact_vcvtop_optional_guard(
    e: &SpecTecExp,
    option_field: &str,
    binder: &str,
    some_ctor: &str,
) -> bool {
    let SpecTecExp::Bin {
        op: SpecTecBinOp::Or,
        e1: same_width,
        e2: double_width,
        ..
    } = e
    else {
        return false;
    };
    exact_vcvtop_optional_branch(same_width, option_field, binder, None, false)
        && exact_vcvtop_optional_branch(double_width, option_field, binder, Some(some_ctor), true)
}

fn exact_vcvtop_optional_branch(
    e: &SpecTecExp,
    option_field: &str,
    binder: &str,
    expected: Option<&str>,
    doubled: bool,
) -> bool {
    let SpecTecExp::Bin {
        op: SpecTecBinOp::And,
        e1: widths,
        e2: option,
        ..
    } = e
    else {
        return false;
    };
    let (outer_fn, outer_param, inner_fn, inner_param) = if option_field == "half?" {
        ("sizenn2", "Fnn_2", "lsizenn1", "Jnn_1")
    } else {
        ("sizenn1", "Fnn_1", "lsizenn2", "Jnn_2")
    };
    let width_ok = if doubled {
        exact_vcvtop_double_width(widths, outer_fn, outer_param, inner_fn, inner_param)
    } else {
        let SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            e1: equality,
            e2: thirty_two,
            ..
        } = widths.as_ref()
        else {
            return false;
        };
        exact_vcvtop_equal_width(equality, outer_fn, outer_param, inner_fn, inner_param)
            && matches!(
                thirty_two.as_ref(),
                SpecTecExp::Cmp {
                    op: SpecTecCmpOp::Eq,
                    e1,
                    e2,
                    ..
                } if exact_lane_width_call(e1, inner_fn, inner_param)
                    && matches!(e2.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(32) })
            )
    };
    width_ok && exact_vcvtop_option_equality(option, option_field, binder, expected)
}

fn exact_vcvtop_equal_width(
    e: &SpecTecExp,
    left_fn: &str,
    left_param: &str,
    right_fn: &str,
    right_param: &str,
) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1,
            e2,
            ..
        } if exact_lane_width_call(e1, left_fn, left_param)
            && exact_lane_width_call(e2, right_fn, right_param)
    )
}

fn exact_vcvtop_double_width(
    e: &SpecTecExp,
    outer_fn: &str,
    outer_param: &str,
    inner_fn: &str,
    inner_param: &str,
) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            e1,
            e2,
            ..
        } if exact_lane_width_call(e1, outer_fn, outer_param)
            && matches!(
                e2.as_ref(),
                SpecTecExp::Bin {
                    op: SpecTecBinOp::Mul,
                    e1: two,
                    e2: width,
                    ..
                } if matches!(two.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
                    && exact_lane_width_call(width, inner_fn, inner_param)
            )
    )
}

fn exact_vcvtop_option_equality(
    e: &SpecTecExp,
    option_field: &str,
    binder: &str,
    expected: Option<&str>,
) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Eq,
        e1,
        e2,
        ..
    } = e
    else {
        return false;
    };
    let left_ok = matches!(
        e1.as_ref(),
        SpecTecExp::Iter {
            e1,
            it: SpecTecIter::Opt,
            xes,
        } if matches!(e1.as_ref(), SpecTecExp::Var { id } if id == binder)
            && matches!(
                xes.as_slice(),
                [SpecTecIterExp::Dom {
                    x,
                    e: SpecTecExp::Var { id },
                }] if x == binder && id == option_field
            )
    );
    let right_ok = match expected {
        None => matches!(e2.as_ref(), SpecTecExp::Opt { eo: None }),
        Some(name) => matches!(
            e2.as_ref(),
            SpecTecExp::Opt { eo: Some(value) }
                if matches!(
                    value.as_ref(),
                    SpecTecExp::Case { op, e1 }
                        if op.fragments() == [name]
                            && matches!(e1.as_ref(), SpecTecExp::Tup { es } if es.is_empty())
                )
        ),
    };
    left_ok && right_ok
}

fn float_magnitude_theory() -> Result<crate::init::inductive::CoprodVariantTheory> {
    CoprodBackend.theory(&Variant::new(vec![
        VCtor::new(
            "NORM",
            covalence_hol_eval::defs::prod(Type::nat(), Type::int()),
        ),
        VCtor::new("SUBNORM", Type::nat()),
        VCtor::new("INF", Type::unit()),
        VCtor::new("NAN", Type::nat()),
    ]))
}

fn lower_float_magnitude<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
) -> Result<Option<(Term, Vec<&'a SpecTecPrem>)>> {
    if family.name != "fNmag" {
        return Ok(None);
    }
    let (
        [SpecTecParam::Exp { x: width_name, .. }],
        [
            SpecTecArg::Exp {
                e:
                    SpecTecExp::Num {
                        n: SpecTecNum::Nat(width),
                    },
            },
        ],
        [instance],
    ) = (family.params, arguments, family.instances.as_slice())
    else {
        return Ok(None);
    };
    let (m_bits, e_bits) = match *width {
        32 => (23u64, 8u64),
        64 => (52u64, 11u64),
        _ => return Ok(None),
    };
    if !matches!(
        (instance.params, instance.args),
        (
            [SpecTecParam::Exp { x, .. }],
            [SpecTecArg::Exp { e: SpecTecExp::Var { id } }]
        ) if x == width_name && id == width_name
    ) {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [norm, sub, inf, nan] = cases.as_slice() else {
        return Ok(None);
    };
    if !exact_fnmag_case_shapes(norm, sub, inf, nan, width_name) {
        return Ok(None);
    }
    let theory = float_magnitude_theory()?;
    if theory.carrier() != carrier {
        return Ok(None);
    }

    let x = Term::free("__fmag", carrier.clone());
    let p2m = crate::init::nat::nat_pow()
        .apply(covalence_hol_eval::mk_nat(2u64))?
        .apply(covalence_hol_eval::mk_nat(m_bits))?;
    let epow = crate::init::nat::nat_pow()
        .apply(covalence_hol_eval::mk_nat(2u64))?
        .apply(covalence_hol_eval::mk_nat(e_bits - 1))?;
    let epow_i = covalence_hol_eval::defs::nat_to_int().apply(epow)?;
    let emin = crate::init::int::int_sub()
        .apply(covalence_hol_eval::mk_int(2i128))?
        .apply(epow_i.clone())?;
    let emax = crate::init::int::int_sub()
        .apply(epow_i)?
        .apply(covalence_hol_eval::mk_int(1i128))?;

    let np = Term::free(
        "__fmag_norm",
        covalence_hol_eval::defs::prod(Type::nat(), Type::int()),
    );
    let nm = covalence_hol_eval::defs::fst(Type::nat(), Type::int()).apply(np.clone())?;
    let ne = covalence_hol_eval::defs::snd(Type::nat(), Type::int()).apply(np.clone())?;
    let nc = crate::init::nat::nat_lt()
        .apply(nm)?
        .apply(p2m.clone())?
        .and(
            crate::init::int::int_le()
                .apply(emin)?
                .apply(ne.clone())?
                .and(crate::init::int::int_le().apply(ne)?.apply(emax)?)?,
        )?;
    let norm_case = injected_case_exists(&theory, 0, &x, np, nc)?;

    let sp = Term::free("__fmag_sub", Type::nat());
    let sc = crate::init::nat::nat_lt()
        .apply(sp.clone())?
        .apply(p2m.clone())?;
    let sub_case = injected_case_exists(&theory, 1, &x, sp, sc)?;

    let inf_case = x.clone().equals(
        theory
            .constructor(2)?
            .clone()
            .apply(covalence_hol_eval::defs::unit_nil())?,
    )?;

    let qp = Term::free("__fmag_nan", Type::nat());
    let qc = crate::init::nat::nat_le()
        .apply(covalence_hol_eval::mk_nat(1u64))?
        .apply(qp.clone())?
        .and(crate::init::nat::nat_lt().apply(qp.clone())?.apply(p2m)?)?;
    let nan_case = injected_case_exists(&theory, 3, &x, qp, qc)?;
    let body = norm_case.or(sub_case)?.or(inf_case)?.or(nan_case)?;
    Ok(Some((
        Term::abs(carrier.clone(), subst::close(&body, "__fmag")),
        cases
            .iter()
            .flat_map(|case| case.refinements.iter())
            .collect(),
    )))
}

fn injected_case_exists(
    theory: &crate::init::inductive::CoprodVariantTheory,
    index: usize,
    value: &Term,
    payload: Term,
    condition: Term,
) -> Result<Term> {
    let var = payload.as_free().expect("local payload witness").clone();
    let ty = payload.type_of()?;
    value
        .clone()
        .equals(theory.constructor(index)?.clone().apply(payload)?)?
        .and(condition)?
        .exists(var.name(), ty)
}

fn exact_fnmag_case_shapes(
    norm: &super::type_family::CaseShape<'_>,
    sub: &super::type_family::CaseShape<'_>,
    inf: &super::type_family::CaseShape<'_>,
    nan: &super::type_family::CaseShape<'_>,
    width: &str,
) -> bool {
    let keys = [norm, sub, inf, nan].map(|c| super::encode::mixop_key(c.operator));
    if keys != ["NORM", "SUBNORM", "INF", "NAN"] {
        return false;
    }
    let payloads = matches!(norm.payload, SpecTecTyp::Tup { ets }
        if matches!(ets.as_slice(), [
            SpecTecTypBind::Bind { id: m, typ: SpecTecTyp::Var { x: mt, as1: ma } },
            SpecTecTypBind::Bind { id: e, typ: SpecTecTyp::Var { x: et, as1: ea } },
        ] if m == "m" && mt == "m" && ma.is_empty() && e == "exp" && et == "exp" && ea.is_empty()))
        && matches!(sub.payload, SpecTecTyp::Tup { ets }
            if matches!(ets.as_slice(), [SpecTecTypBind::Bind { id, typ: SpecTecTyp::Var { x, as1 } }]
                if id == "m" && x == "m" && as1.is_empty()))
        && matches!(inf.payload, SpecTecTyp::Tup { ets } if ets.is_empty())
        && matches!(nan.payload, SpecTecTyp::Tup { ets }
            if matches!(ets.as_slice(), [SpecTecTypBind::Bind { id, typ: SpecTecTyp::Var { x, as1 } }]
                if id == "m" && x == "m" && as1.is_empty()));
    payloads
        && norm.params.is_empty()
        && matches!(sub.params, [SpecTecParam::Exp { x, .. }] if x == "exp")
        && inf.params.is_empty()
        && nan.params.is_empty()
        && exact_fnmag_guard(norm.refinements, width, 1, 2)
        && exact_fnmag_guard(sub.refinements, width, 1, 1)
        && inf.refinements.is_empty()
        && exact_fnmag_guard(nan.refinements, width, 1, 0)
}

fn exact_fnmag_guard(
    premises: &[SpecTecPrem],
    width: &str,
    expected_m_calls: usize,
    expected_e_calls: usize,
) -> bool {
    let [SpecTecPrem::If { e }] = premises else {
        return false;
    };
    if !matches!(
        e,
        SpecTecExp::Bin {
            op: SpecTecBinOp::And,
            ..
        }
    ) {
        return false;
    }
    fn calls(e: &SpecTecExp, width: &str, m: &mut usize, ex: &mut usize) -> bool {
        match e {
            SpecTecExp::Call { x, as1 } if x == "M" || x == "E" => {
                if !matches!(as1.as_slice(), [SpecTecArg::Exp {
                    e: SpecTecExp::Var { id }
                }] if id == width)
                {
                    return false;
                }
                if x == "M" {
                    *m += 1;
                } else {
                    *ex += 1;
                }
                true
            }
            SpecTecExp::Bin { e1, e2, .. } | SpecTecExp::Cmp { e1, e2, .. } => {
                calls(e1, width, m, ex) && calls(e2, width, m, ex)
            }
            SpecTecExp::Cvt { e1, .. } | SpecTecExp::Un { e2: e1, .. } => calls(e1, width, m, ex),
            SpecTecExp::Num { .. } | SpecTecExp::Var { .. } => true,
            _ => false,
        }
    }
    let (mut m, mut ex) = (0, 0);
    calls(e, width, &mut m, &mut ex) && m == expected_m_calls && ex == expected_e_calls
}

/// Compile the exact source refinement on `list(X)`.
///
/// This recognizer is deliberately structural and fail-closed. In particular,
/// it does not infer that an arbitrary list-shaped premise means a length
/// bound: every operator, literal, binder, and source-domain occurrence is
/// checked before the normalized HOL predicate is built.
fn lower_bounded_list<'a>(
    family: &TypeFamily<'a>,
    arguments: &[SpecTecArg],
    carrier: &Type,
    ctx: &syntax::TypeCtx<'a>,
) -> Result<Option<(Term, &'a [SpecTecPrem])>> {
    if family.name != "list" {
        return Ok(None);
    }
    let ([SpecTecParam::Typ { x: type_param }], [SpecTecArg::Typ { t: element_ast }], [instance]) =
        (family.params, arguments, family.instances.as_slice())
    else {
        return Ok(None);
    };
    if !matches!(
        (instance.params, instance.args),
        (
            [SpecTecParam::Typ { x: instance_element }],
            [SpecTecArg::Typ {
                t: SpecTecTyp::Var {
                    x: instance_arg,
                    as1,
                },
            }],
        ) if instance_element == type_param && instance_arg == type_param && as1.is_empty()
    ) {
        return Ok(None);
    }
    let TypeShape::Variant(cases) = &instance.shape else {
        return Ok(None);
    };
    let [case] = cases.as_slice() else {
        return Ok(None);
    };
    let SpecTecTyp::Tup { ets } = case.payload else {
        return Ok(None);
    };
    let [
        SpecTecTypBind::Bind {
            id: payload_name,
            typ:
                SpecTecTyp::Iter {
                    t1,
                    it: payload_iterations,
                },
        },
    ] = ets.as_slice()
    else {
        return Ok(None);
    };
    let SpecTecTyp::Var {
        x: payload_element,
        as1: payload_element_args,
    } = t1.as_ref()
    else {
        return Ok(None);
    };
    if payload_element != type_param
        || !payload_element_args.is_empty()
        || payload_iterations.as_slice() != [SpecTecIter::List]
        || !case.params.is_empty()
    {
        return Ok(None);
    }
    let [premise @ SpecTecPrem::If { e }] = case.refinements else {
        return Ok(None);
    };
    if !is_exact_list_bound(e, type_param, payload_name) {
        return Ok(None);
    }

    let element = syntax::resolve_typ(element_ast, ctx)?;
    let expected_carrier = crate::init::list::list(element.clone());
    if carrier != &expected_carrier {
        return Ok(None);
    }
    let value = Term::free(payload_name.clone(), carrier.clone());
    let length = covalence_hol_eval::defs::list_length(element).apply(value.clone())?;
    let bound = crate::init::nat::nat_pow()
        .apply(covalence_hol_eval::mk_nat(2u64))?
        .apply(covalence_hol_eval::mk_nat(32u64))?;
    let body = crate::init::nat::nat_lt().apply(length)?.apply(bound)?;
    let predicate = Term::abs(carrier.clone(), subst::close(&body, payload_name));
    Ok(Some((predicate, std::slice::from_ref(premise))))
}

fn is_exact_list_bound(e: &SpecTecExp, type_param: &str, payload_name: &str) -> bool {
    let SpecTecExp::Cmp {
        op: SpecTecCmpOp::Lt,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
        e1,
        e2,
    } = e
    else {
        return false;
    };
    let SpecTecExp::Len { e1: iterated } = e1.as_ref() else {
        return false;
    };
    let SpecTecExp::Iter {
        e1: element,
        it: SpecTecIter::List,
        xes,
    } = iterated.as_ref()
    else {
        return false;
    };
    let SpecTecExp::Var { id: element_name } = element.as_ref() else {
        return false;
    };
    let [SpecTecIterExp::Dom { x, e: domain }] = xes.as_slice() else {
        return false;
    };
    let SpecTecExp::Var { id: domain_name } = domain else {
        return false;
    };
    if element_name != type_param || x != type_param || domain_name != payload_name {
        return false;
    }
    matches!(
        e2.as_ref(),
        SpecTecExp::Bin {
            op: SpecTecBinOp::Pow,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Nat),
            e1,
            e2,
        } if matches!(e1.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(2) })
            && matches!(e2.as_ref(), SpecTecExp::Num { n: SpecTecNum::Nat(32) })
    )
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
        let carrier = match syntax::resolve_typ(ty, self.ctx) {
            Ok(carrier) => carrier,
            Err(_)
                if matches!(ty, SpecTecTyp::Var { x, as1 } if x == "ishape" && as1.is_empty())
                    && self
                        .families
                        .family("ishape")
                        .is_some_and(ishape_is_carrier_transparent) =>
            {
                syntax::resolve_typ(
                    &SpecTecTyp::Var {
                        x: "shape".into(),
                        as1: vec![],
                    },
                    self.ctx,
                )?
            }
            Err(_)
                if matches!(ty, SpecTecTyp::Var { x, as1 } if x == "fNmag"
                && matches!(as1.as_slice(), [SpecTecArg::Exp {
                    e: SpecTecExp::Num { n: SpecTecNum::Nat(32 | 64) }
                }])) =>
            {
                float_magnitude_theory()?.carrier().clone()
            }
            Err(original) => return Err(original),
        };
        if self.refinement_free(ty) {
            Ok(ResolvedType {
                sort: HolSort::unconstrained(carrier),
                provenance: TypeProvenance::SemanticBackend,
            })
        } else if let SpecTecTyp::Var { x, as1 } = ty
            && let Some(family) = self.families.family(x)
            && let lowering = self.refinements.lower(family, as1, &carrier, self.ctx)?
            && let Some(predicate) = match lowering {
                RefinementLowering::Predicate { predicate, .. }
                | RefinementLowering::CasePredicate { predicate, .. } => Some(predicate),
                RefinementLowering::NotApplicable | RefinementLowering::Unsupported => None,
            }
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

fn ishape_is_carrier_transparent(family: &TypeFamily<'_>) -> bool {
    let [instance] = family.instances.as_slice() else {
        return false;
    };
    let TypeShape::Variant(cases) = &instance.shape else {
        return false;
    };
    let [case] = cases.as_slice() else {
        return false;
    };
    matches!(
        case.payload,
        SpecTecTyp::Tup { ets } if matches!(
            ets.as_slice(),
            [SpecTecTypBind::Bind {
                typ: SpecTecTyp::Var { x, as1 },
                ..
            }] if x == "shape" && as1.is_empty()
        )
    )
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
            .lower(family, &[], &Type::nat(), &ctx)
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
    fn parametric_list_bound_becomes_an_exact_checked_predicate() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let list_bool = SpecTecTyp::Var {
            x: "list".into(),
            as1: vec![SpecTecArg::Typ {
                t: SpecTecTyp::Bool,
            }],
        };
        let resolved = RefinementAwareTypeResolver::new(&ctx, &families)
            .resolve_type(&list_bool)
            .unwrap();
        let carrier = crate::init::list::list(Type::bool());
        assert_eq!(resolved.sort.carrier(), &carrier);
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("list(bool) must retain its source length bound");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(carrier.clone(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

        let family = families.family("list").unwrap();
        let arguments = match &list_bool {
            SpecTecTyp::Var { as1, .. } => as1,
            _ => unreachable!(),
        };
        let RefinementLowering::Predicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(family, arguments, &carrier, &ctx)
            .unwrap()
        else {
            panic!("list(bool) source refinement must lower");
        };
        assert_eq!(source_premises.len(), 1);
        assert!(std::ptr::eq(
            &source_premises[0],
            family.refinements().next().unwrap()
        ));

        // Wrong argument kinds and carriers fail closed.
        assert!(matches!(
            SingletonValueRefinementLowerer
                .lower(family, &[], &carrier, &ctx)
                .unwrap(),
            RefinementLowering::Unsupported
        ));
        assert!(matches!(
            SingletonValueRefinementLowerer
                .lower(family, arguments, &Type::nat(), &ctx)
                .unwrap(),
            RefinementLowering::Unsupported
        ));
    }

    #[test]
    fn ground_unsigned_width_becomes_an_exact_checked_predicate() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let u32_ty = SpecTecTyp::Var {
            x: "uN".into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Num {
                    n: SpecTecNum::Nat(32),
                },
            }],
        };
        let resolved = resolver.resolve_type(&u32_ty).unwrap();
        assert_eq!(resolved.sort.carrier(), &Type::nat());
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("uN(32) must retain its source numeric bound");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(Type::nat(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);
        let family = families.family("uN").unwrap();
        let arguments = match &u32_ty {
            SpecTecTyp::Var { as1, .. } => as1,
            _ => unreachable!(),
        };
        let RefinementLowering::Predicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(family, arguments, &Type::nat(), &ctx)
            .unwrap()
        else {
            panic!("uN(32) source refinement must lower");
        };
        assert_eq!(source_premises.len(), 1);
        assert!(std::ptr::eq(
            &source_premises[0],
            family.refinements().next().unwrap()
        ));

        let symbolic = SpecTecTyp::Var {
            x: "uN".into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Var { id: "N".into() },
            }],
        };
        // Carrier rendering does not require a value environment, but the
        // refinement lowerer must not pretend an uninstantiated bound is
        // closed.
        let unresolved = resolver.resolve_type(&symbolic).unwrap();
        assert!(matches!(
            unresolved.sort.invariant(),
            SortInvariant::Unresolved
        ));
    }

    #[test]
    fn ground_positive_signed_width_becomes_an_exact_checked_predicate() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let s64_ty = SpecTecTyp::Var {
            x: "sN".into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Num {
                    n: SpecTecNum::Nat(64),
                },
            }],
        };
        let resolved = resolver.resolve_type(&s64_ty).unwrap();
        assert_eq!(resolved.sort.carrier(), &Type::int());
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("sN(64) must retain its source signed bound");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(Type::int(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

        let family = families.family("sN").unwrap();
        let arguments = match &s64_ty {
            SpecTecTyp::Var { as1, .. } => as1,
            _ => unreachable!(),
        };
        let RefinementLowering::Predicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(family, arguments, &Type::int(), &ctx)
            .unwrap()
        else {
            panic!("sN(64) source refinement must lower");
        };
        assert_eq!(source_premises.len(), 1);
        assert!(std::ptr::eq(
            &source_premises[0],
            family.refinements().next().unwrap()
        ));

        // Width zero would force the source's `N - 1` conversion outside the
        // positive-width fragment, so it remains explicitly unresolved.
        let s0_ty = SpecTecTyp::Var {
            x: "sN".into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Num {
                    n: SpecTecNum::Nat(0),
                },
            }],
        };
        let unresolved = resolver.resolve_type(&s0_ty).unwrap();
        assert!(matches!(
            unresolved.sort.invariant(),
            SortInvariant::Unresolved
        ));
    }

    #[test]
    fn name_utf8_bound_becomes_an_exact_checked_predicate() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let name_ty = SpecTecTyp::Var {
            x: "name".into(),
            as1: vec![],
        };
        let resolved = RefinementAwareTypeResolver::new(&ctx, &families)
            .resolve_type(&name_ty)
            .unwrap();
        let carrier = crate::init::list::list(Type::nat());
        assert_eq!(resolved.sort.carrier(), &carrier);
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("name must retain its source UTF-8 byte-length bound");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(carrier.clone(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

        let family = families.family("name").unwrap();
        let RefinementLowering::Predicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(family, &[], &carrier, &ctx)
            .unwrap()
        else {
            panic!("name source refinement must lower");
        };
        assert_eq!(source_premises.len(), 1);
        assert!(std::ptr::eq(
            &source_premises[0],
            family.refinements().next().unwrap()
        ));
        assert!(matches!(
            SingletonValueRefinementLowerer
                .lower(family, &[], &Type::nat(), &ctx)
                .unwrap(),
            RefinementLowering::Unsupported
        ));
    }

    #[test]
    fn exact_value_and_list_fragments_are_live() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);

        for name in [
            "bit", "byte", "char", "dim", "sz", "relaxed2", "relaxed4", "symdots",
        ] {
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
    }

    #[test]
    fn shape_and_byte_shape_are_exactly_enumerated() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let mut carrier = None;

        for name in ["shape", "bshape"] {
            let ty = SpecTecTyp::Var {
                x: name.into(),
                as1: vec![],
            };
            let resolved = resolver.resolve_type(&ty).unwrap();
            let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
                panic!("{name} must retain its exact finite source refinement");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(resolved.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);
            if let Some(expected) = &carrier {
                assert_eq!(resolved.sort.carrier(), expected);
            } else {
                carrier = Some(resolved.sort.carrier().clone());
            }

            let family = families.family(name).unwrap();
            let RefinementLowering::Predicate {
                source_premises, ..
            } = SingletonValueRefinementLowerer
                .lower(family, &[], resolved.sort.carrier(), &ctx)
                .unwrap()
            else {
                panic!("{name} source refinement must lower");
            };
            assert_eq!(source_premises.len(), 1);
            assert!(std::ptr::eq(
                &source_premises[0],
                family.refinements().next().unwrap()
            ));
        }
    }

    #[test]
    fn exact_refinement_family_census_is_pinned() {
        let defs = crate::wasm::spec::wasm_spec();
        let families = TypeFamilies::new(&defs);
        let refined: Vec<_> = families
            .families()
            .filter(|family| family.refinements().next().is_some())
            .collect();
        assert_eq!(refined.len(), 29);
        assert_eq!(
            refined
                .iter()
                .map(|family| family.refinements().count())
                .sum::<usize>(),
            56
        );

        let exact = [
            "bit",
            "byte",
            "char",
            "dim",
            "sz",
            "relaxed2",
            "relaxed4",
            "symdots",
            "list",
            "name",
            "uN",
            "sN",
            "loadop_",
            "storeop_",
            "ishape",
            "fNmag",
            "shape",
            "bshape",
            "unop_",
            "cvtop__",
            "vloadop_",
            "vunop_",
            "vextternop__",
            "vextunop__",
            "vextbinop__",
            "vrelop_",
            "vbinop_",
            "vcvtop__",
        ];
        assert_eq!(
            exact
                .iter()
                .map(|name| families.family(name).unwrap().refinements().count())
                .sum::<usize>(),
            53
        );
        assert_eq!(refined.len() - exact.len(), 1);
        assert_eq!(56 - 53, 3);
    }

    #[test]
    fn recursive_instruction_refinement_residue_is_exactly_classified() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let family = families.family("instr").unwrap();
        let mut refined = Vec::new();
        for instance in &family.instances {
            if let TypeShape::Variant(cases) = &instance.shape {
                for case in cases {
                    if let [SpecTecPrem::If { e }] = case.refinements {
                        refined.push((case.operator.fragments(), e));
                    } else {
                        assert!(case.refinements.is_empty());
                    }
                }
            }
        }
        assert_eq!(refined.len(), 3);
        assert_eq!(refined[0].0, ["VSHUFFLE"]);
        assert!(matches!(
            refined[0].1,
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Eq,
                ..
            }
        ));
        assert_eq!(refined[1].0, ["VNARROW"]);
        assert!(matches!(
            refined[1].1,
            SpecTecExp::Bin {
                op: SpecTecBinOp::And,
                ..
            }
        ));
        assert_eq!(refined[2].0, ["VEXTRACT_LANE"]);
        assert!(matches!(
            refined[2].1,
            SpecTecExp::Bin {
                op: SpecTecBinOp::Equiv,
                ..
            }
        ));

        let error = RefinementAwareTypeResolver::new(&ctx, &families)
            .resolve_type(&SpecTecTyp::Var {
                x: "instr".into(),
                as1: vec![],
            })
            .unwrap_err();
        assert!(format!("{error:?}").contains("parametric field/case not modelled yet"));
    }

    #[test]
    fn rigid_integer_packed_operator_bounds_are_exact() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let rigid = |family: &str, name: &str| SpecTecTyp::Var {
            x: family.into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Case {
                    op: covalence_spectec::ast::MixOp::new(vec![name.into()]),
                    e1: Box::new(SpecTecExp::Tup { es: vec![] }),
                },
            }],
        };
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        for family_name in ["loadop_", "storeop_"] {
            for integer in ["I32", "I64"] {
                let ty = rigid(family_name, integer);
                let resolved = resolver.resolve_type(&ty).unwrap();
                let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
                    panic!("{family_name}({integer}) must retain its packed-size bound");
                };
                assert_eq!(
                    predicate.type_of().unwrap(),
                    Type::fun(resolved.sort.carrier().clone(), Type::bool())
                );
                assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

                let SpecTecTyp::Var { as1, .. } = &ty else {
                    unreachable!()
                };
                let source = families.family(family_name).unwrap();
                let RefinementLowering::Predicate {
                    source_premises, ..
                } = SingletonValueRefinementLowerer
                    .lower(source, as1, resolved.sort.carrier(), &ctx)
                    .unwrap()
                else {
                    panic!("{family_name}({integer}) source refinement must lower");
                };
                assert_eq!(source_premises.len(), 1);
                assert!(std::ptr::eq(
                    &source_premises[0],
                    source.refinements().next().unwrap()
                ));
            }
        }

        for family_name in ["loadop_", "storeop_"] {
            let float = resolver.resolve_type(&rigid(family_name, "F32")).unwrap();
            assert!(matches!(float.sort.invariant(), SortInvariant::Unresolved));
        }
    }

    #[test]
    fn rigid_numeric_unary_operator_refinement_is_exact() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        for numeric in ["I32", "I64", "F32", "F64"] {
            let ty = SpecTecTyp::Var {
                x: "unop_".into(),
                as1: vec![SpecTecArg::Exp {
                    e: SpecTecExp::Case {
                        op: covalence_spectec::ast::MixOp::new(vec![numeric.into()]),
                        e1: Box::new(SpecTecExp::Tup { es: vec![] }),
                    },
                }],
            };
            let resolved = resolver.resolve_type(&ty).unwrap();
            let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
                panic!("unop_({numeric}) must have an exact invariant");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(resolved.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);
        }

        let symbolic = SpecTecTyp::Var {
            x: "unop_".into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Var { id: "N".into() },
            }],
        };
        let unresolved = resolver.resolve_type(&symbolic).unwrap();
        assert!(matches!(
            unresolved.sort.invariant(),
            SortInvariant::Unresolved
        ));
    }

    #[test]
    fn rigid_numeric_conversion_operator_refinements_are_exact() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let rigid = |name: &str| SpecTecArg::Exp {
            e: SpecTecExp::Case {
                op: covalence_spectec::ast::MixOp::new(vec![name.into()]),
                e1: Box::new(SpecTecExp::Tup { es: vec![] }),
            },
        };
        for left in ["I32", "I64", "F32", "F64"] {
            for right in ["I32", "I64", "F32", "F64"] {
                let ty = SpecTecTyp::Var {
                    x: "cvtop__".into(),
                    as1: vec![rigid(left), rigid(right)],
                };
                let resolved = resolver.resolve_type(&ty).unwrap();
                let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
                    panic!("cvtop__({left}, {right}) must have an exact invariant");
                };
                assert_eq!(
                    predicate.type_of().unwrap(),
                    Type::fun(resolved.sort.carrier().clone(), Type::bool())
                );
                assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);
            }
        }
        let symbolic = SpecTecTyp::Var {
            x: "cvtop__".into(),
            as1: vec![
                SpecTecArg::Exp {
                    e: SpecTecExp::Var { id: "A".into() },
                },
                rigid("I32"),
            ],
        };
        assert!(matches!(
            resolver.resolve_type(&symbolic).unwrap().sort.invariant(),
            SortInvariant::Unresolved
        ));
    }

    #[test]
    fn rigid_vector_load_operator_refinements_are_exact() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let v128 = SpecTecTyp::Var {
            x: "vloadop_".into(),
            as1: vec![SpecTecArg::Exp {
                e: SpecTecExp::Case {
                    op: covalence_spectec::ast::MixOp::new(vec!["V128".into()]),
                    e1: Box::new(SpecTecExp::Tup { es: vec![] }),
                },
            }],
        };
        let resolved = resolver.resolve_type(&v128).unwrap();
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("vloadop_(V128) must have an exact finite invariant");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(resolved.sort.carrier().clone(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

        let family = families.family("vloadop_").unwrap();
        let RefinementLowering::CasePredicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(
                family,
                match &v128 {
                    SpecTecTyp::Var { as1, .. } => as1,
                    _ => unreachable!(),
                },
                resolved.sort.carrier(),
                &ctx,
            )
            .unwrap()
        else {
            panic!("vloadop_ source refinements must lower");
        };
        assert_eq!(source_premises.len(), 2);
        let retained: Vec<_> = family.refinements().collect();
        assert!(
            source_premises
                .iter()
                .zip(retained)
                .all(|(left, right)| std::ptr::eq(*left, right))
        );
    }

    #[test]
    fn rigid_vector_unary_operator_refinement_is_exact() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let shape = |lane: &str, dim: u64| SpecTecArg::Exp {
            e: SpecTecExp::Case {
                op: covalence_spectec::ast::MixOp::new(vec!["".into(), "X".into(), "".into()]),
                e1: Box::new(SpecTecExp::Tup {
                    es: vec![
                        SpecTecExp::Case {
                            op: covalence_spectec::ast::MixOp::new(vec![lane.into()]),
                            e1: Box::new(SpecTecExp::Tup { es: vec![] }),
                        },
                        SpecTecExp::Case {
                            op: covalence_spectec::ast::MixOp::new(vec!["".into(), "".into()]),
                            e1: Box::new(SpecTecExp::Tup {
                                es: vec![SpecTecExp::Num {
                                    n: SpecTecNum::Nat(dim),
                                }],
                            }),
                        },
                    ],
                }),
            },
        };
        for (lane, dim) in [
            ("I8", 16),
            ("I16", 8),
            ("I32", 4),
            ("I64", 2),
            ("F32", 4),
            ("F64", 2),
        ] {
            let resolved = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: "vunop_".into(),
                    as1: vec![shape(lane, dim)],
                })
                .unwrap();
            assert!(
                matches!(resolved.sort.invariant(), SortInvariant::Predicate(_)),
                "{lane}x{dim}"
            );
            assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

            let relation = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: "vrelop_".into(),
                    as1: vec![shape(lane, dim)],
                })
                .unwrap();
            let SortInvariant::Predicate(predicate) = relation.sort.invariant() else {
                panic!("vrelop_({lane}x{dim}) must have an exact invariant");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(relation.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(relation.provenance, TypeProvenance::SourceRefinement);

            let binary = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: "vbinop_".into(),
                    as1: vec![shape(lane, dim)],
                })
                .unwrap();
            let SortInvariant::Predicate(predicate) = binary.sort.invariant() else {
                panic!("vbinop_({lane}x{dim}) must have an exact invariant");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(binary.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(binary.provenance, TypeProvenance::SourceRefinement);
        }

        let shapes = [
            ("I8", 16),
            ("I16", 8),
            ("I32", 4),
            ("I64", 2),
            ("F32", 4),
            ("F64", 2),
        ];
        for (left, left_dim) in shapes {
            for (right, right_dim) in shapes {
                let conversion = resolver
                    .resolve_type(&SpecTecTyp::Var {
                        x: "vcvtop__".into(),
                        as1: vec![shape(left, left_dim), shape(right, right_dim)],
                    })
                    .unwrap();
                let SortInvariant::Predicate(predicate) = conversion.sort.invariant() else {
                    panic!("vcvtop__({left}x{left_dim}, {right}x{right_dim}) must be exact");
                };
                assert_eq!(
                    predicate.type_of().unwrap(),
                    Type::fun(conversion.sort.carrier().clone(), Type::bool())
                );
                assert_eq!(conversion.provenance, TypeProvenance::SourceRefinement);
            }
        }
    }

    #[test]
    fn rigid_extended_vector_unary_and_ternary_refinements_are_exact() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let ishape = |lane: &str, dim: u64| SpecTecArg::Exp {
            e: SpecTecExp::Case {
                op: covalence_spectec::ast::MixOp::new(vec!["".into(), "".into()]),
                e1: Box::new(SpecTecExp::Tup {
                    es: vec![SpecTecExp::Case {
                        op: covalence_spectec::ast::MixOp::new(vec![
                            "".into(),
                            "X".into(),
                            "".into(),
                        ]),
                        e1: Box::new(SpecTecExp::Tup {
                            es: vec![
                                SpecTecExp::Case {
                                    op: covalence_spectec::ast::MixOp::new(vec![lane.into()]),
                                    e1: Box::new(SpecTecExp::Tup { es: vec![] }),
                                },
                                SpecTecExp::Case {
                                    op: covalence_spectec::ast::MixOp::new(vec![
                                        "".into(),
                                        "".into(),
                                    ]),
                                    e1: Box::new(SpecTecExp::Tup {
                                        es: vec![SpecTecExp::Num {
                                            n: SpecTecNum::Nat(dim),
                                        }],
                                    }),
                                },
                            ],
                        }),
                    }],
                }),
            },
        };
        for ((left, left_dim), (right, right_dim)) in [
            (("I8", 16), ("I32", 4)),
            (("I8", 16), ("I16", 8)),
            (("I16", 8), ("I32", 4)),
            (("I32", 4), ("I64", 2)),
        ] {
            let resolved = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: "vextternop__".into(),
                    as1: vec![ishape(left, left_dim), ishape(right, right_dim)],
                })
                .unwrap();
            let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
                panic!("rigid vextternop__ pair must have an exact invariant");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(resolved.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

            let unary = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: "vextunop__".into(),
                    as1: vec![ishape(left, left_dim), ishape(right, right_dim)],
                })
                .unwrap();
            let SortInvariant::Predicate(predicate) = unary.sort.invariant() else {
                panic!("rigid vextunop__ pair must have an exact invariant");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(unary.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(unary.provenance, TypeProvenance::SourceRefinement);

            let binary = resolver
                .resolve_type(&SpecTecTyp::Var {
                    x: "vextbinop__".into(),
                    as1: vec![ishape(left, left_dim), ishape(right, right_dim)],
                })
                .unwrap();
            let SortInvariant::Predicate(predicate) = binary.sort.invariant() else {
                panic!("rigid vextbinop__ pair must have an exact invariant");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(binary.sort.carrier().clone(), Type::bool())
            );
            assert_eq!(binary.provenance, TypeProvenance::SourceRefinement);
        }
    }

    #[test]
    fn integer_shape_existential_is_exactly_enumerated() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let ty = SpecTecTyp::Var {
            x: "ishape".into(),
            as1: vec![],
        };
        let resolved = RefinementAwareTypeResolver::new(&ctx, &families)
            .resolve_type(&ty)
            .unwrap();
        let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
            panic!("ishape must enumerate the four integer-lane shapes");
        };
        assert_eq!(
            predicate.type_of().unwrap(),
            Type::fun(resolved.sort.carrier().clone(), Type::bool())
        );
        assert_eq!(resolved.provenance, TypeProvenance::SourceRefinement);

        let source = families.family("ishape").unwrap();
        let RefinementLowering::Predicate {
            source_premises, ..
        } = SingletonValueRefinementLowerer
            .lower(source, &[], resolved.sort.carrier(), &ctx)
            .unwrap()
        else {
            panic!("ishape source refinement must lower");
        };
        assert_eq!(source_premises.len(), 1);
        assert!(std::ptr::eq(
            &source_premises[0],
            source.refinements().next().unwrap()
        ));
    }

    #[test]
    fn ground_float_magnitude_preserves_all_case_refinements() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);
        let source = families.family("fNmag").unwrap();
        for width in [32u64, 64] {
            let ty = SpecTecTyp::Var {
                x: "fNmag".into(),
                as1: vec![SpecTecArg::Exp {
                    e: SpecTecExp::Num {
                        n: SpecTecNum::Nat(width),
                    },
                }],
            };
            let resolved = resolver.resolve_type(&ty).unwrap();
            let SortInvariant::Predicate(predicate) = resolved.sort.invariant() else {
                panic!("fNmag({width}) must retain its case refinements");
            };
            assert_eq!(
                predicate.type_of().unwrap(),
                Type::fun(resolved.sort.carrier().clone(), Type::bool())
            );
            let SpecTecTyp::Var { as1, .. } = &ty else {
                unreachable!()
            };
            let RefinementLowering::CasePredicate {
                source_premises, ..
            } = SingletonValueRefinementLowerer
                .lower(source, as1, resolved.sort.carrier(), &ctx)
                .unwrap()
            else {
                panic!("fNmag({width}) must use the multi-case boundary");
            };
            let expected: Vec<_> = source.refinements().collect();
            assert_eq!(source_premises.len(), 3);
            assert!(
                source_premises
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| std::ptr::eq(*actual, expected))
            );
        }
    }
}

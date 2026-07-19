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
// TODO(cov:kernel.hol.init.src.wasm.case-field-refinement-premises-prs-erased, severe): Lower 48 refinements in 21 unsupported families plus symbolic uN/sN indices; five primitives, list(X), ground uN, and positive-width sN are exact.
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
        if arguments.len() != family.params.len() || family.instances.len() != 1 {
            return Ok(RefinementLowering::Unsupported);
        }
        let instance = &family.instances[0];
        let TypeShape::Variant(cases) = &instance.shape else {
            return Ok(RefinementLowering::Unsupported);
        };
        let [case] = cases.as_slice() else {
            return Ok(RefinementLowering::Unsupported);
        };
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
        let carrier = syntax::resolve_typ(ty, self.ctx)?;
        if self.refinement_free(ty) {
            Ok(ResolvedType {
                sort: HolSort::unconstrained(carrier),
                provenance: TypeProvenance::SemanticBackend,
            })
        } else if let SpecTecTyp::Var { x, as1 } = ty
            && let Some(family) = self.families.family(x)
            && let RefinementLowering::Predicate { predicate, .. } =
                self.refinements.lower(family, as1, &carrier, self.ctx)?
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
    fn exact_value_and_list_fragments_are_live_but_other_dependent_refinements_refuse() {
        let defs = crate::wasm::spec::wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let families = TypeFamilies::new(&defs);
        let resolver = RefinementAwareTypeResolver::new(&ctx, &families);

        for name in ["bit", "byte", "char", "dim", "sz"] {
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

        let exact = ["bit", "byte", "char", "dim", "sz", "list", "uN", "sN"];
        assert_eq!(
            exact
                .iter()
                .map(|name| families.family(name).unwrap().refinements().count())
                .sum::<usize>(),
            8
        );
        assert_eq!(refined.len() - exact.len(), 21);
        assert_eq!(56 - 8, 48);
    }
}

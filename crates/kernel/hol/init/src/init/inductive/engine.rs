//! The **exact-type (recursion-engine) HOL backend** for the
//! inductive-types API — an *adapter* over the existing typedef +
//! recursion-theorem machinery, not a rebuild.
//!
//! Where the [Church backend](super::church) synthesizes a junk-carrying
//! encoding for any spec, this backend serves specs whose type is already
//! **carved** in the kernel with induction + freeness supplied through the
//! engine's [`Inductive`](super::Inductive) seam and a recursor built by
//! [`super::recursor::recursion_theorem`]. The bundle statements are the
//! same membership-relativized shapes — with `mem = λt. ⊤` and
//! [`InductiveFacts::mem_trivial`] available, so consumers discharge every
//! guard for free — which is exactly what makes the two backends
//! swappable.
//!
//! **`nat`** is the delivered instance ([`nat_backend`] / [`nat_spec`]):
//! its facts ride on the *engine end to end* — `comp` comes from
//! `recursion::rec_holds_proof_at` (the recursion theorem
//! run at the `nat` signature: graph → totality → determinacy → ε-recursor
//! → `spec_ax` transfer), induction from the kernel's `nat_induct` through
//! the same `NatTheory` adapter the engine uses, freeness from
//! `succ_inj` / `zero_ne_succ`. Further carved types (`list`, …) get their
//! own adapter instances the same way; a *generic* `Inductive`-to-bundle
//! adapter is deliberately deferred until a second carved consumer exists.
//!
//! ## Recursor shape: iteration
//!
//! The bundle contract is a **catamorphism** (steps receive fold images
//! only), while `natRec` is primitive-recursive (its step also receives
//! the raw predecessor). The adapter wraps: `rec [z, s] t` is
//! `natRec z (λn b. s b) t`, and `comp` β-bridges the equations to the
//! contract shape `⊢ ∀m. rec [z,s] (succ m) = s (rec [z,s] m)`.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use covalence_hol_eval::derived::DerivedRules;
use covalence_inductive::{
    ArgSort, BackendCaps, CtorSpec, IndResult, InductiveBackend, InductiveError, InductiveFacts,
    InductiveSpec, InductiveTheory,
};

use super::api::{derive_cases_native, internal, prove_beta_eq, relativize_induct};
use super::hol::NativeHol;
use crate::init::eq::beta_expand;
use crate::init::ext::TermExt;
use crate::init::logic::truth;
use crate::init::nat::{nat_succ, succ, zero};
use crate::init::recursion::rec_holds_proof_at;

/// The spec the `nat` adapter realizes: `nat := zero | succ nat`.
pub fn nat_spec() -> InductiveSpec<Type> {
    InductiveSpec::new(
        "nat",
        vec![
            CtorSpec::nullary("zero"),
            CtorSpec::new("succ", [("m", ArgSort::Rec)]),
        ],
    )
}

/// The engine-backed `nat` backend.
#[derive(Clone, Copy, Debug, Default)]
pub struct NatEngineBackend;

/// The engine-backed `nat` backend value.
pub fn nat_backend() -> NatEngineBackend {
    NatEngineBackend
}

impl InductiveBackend<NativeHol> for NatEngineBackend {
    fn realize(
        &self,
        _logic: &NativeHol,
        spec: &InductiveSpec<Type>,
    ) -> IndResult<InductiveTheory<NativeHol>, NativeHol> {
        spec.validate().map_err(InductiveError::spec)?;
        let expected = nat_spec();
        if spec.ctors.len() != expected.ctors.len()
            || spec.ctors.iter().zip(&expected.ctors).any(|(a, b)| {
                a.args
                    .iter()
                    .map(|(_, s)| s)
                    .ne(b.args.iter().map(|(_, s)| s))
            })
        {
            return Err(InductiveError::SpecMismatch(format!(
                "the engine adapter realizes the carved `nat` shape only, got `{}`",
                spec.name
            )));
        }
        let th = NatEngineTheory {
            spec: spec.clone(),
            mem: Term::abs(Type::nat(), Term::bool_lit(true)),
        };
        Ok(InductiveTheory {
            spec: spec.clone(),
            ty: Type::nat(),
            mem: th.mem.clone(),
            ctors: vec![zero(), nat_succ()],
            facts: Box::new(th),
        })
    }
}

struct NatEngineTheory {
    spec: InductiveSpec<Type>,
    /// `λt:nat. ⊤`.
    mem: Term,
}

impl NatEngineTheory {
    /// Split and validate the step slice.
    fn steps<'a>(&self, steps: &'a [Term]) -> IndResult<(&'a Term, &'a Term), NativeHol> {
        match steps {
            [z, s] => Ok((z, s)),
            _ => Err(InductiveError::Arity {
                what: "recursor steps",
                expected: 2,
                got: steps.len(),
            }),
        }
    }

    /// The catamorphism step `s : β → β` wrapped to `natRec`'s
    /// primitive-recursive shape `λ__n __b. s __b : nat → β → β`.
    fn wrap_step(s: &Term, beta: &Type) -> Result<Term> {
        let b = Term::free("__b", beta.clone());
        let body = s.clone().apply(b)?;
        let inner = Term::abs(beta.clone(), subst::close(&body, "__b"));
        Ok(Term::abs(Type::nat(), inner))
    }
}

impl InductiveFacts<NativeHol> for NatEngineTheory {
    fn rec_app(&self, steps: &[Term], t: &Term) -> IndResult<Term, NativeHol> {
        let (z, s) = self.steps(steps)?;
        let beta = z.type_of()?;
        Ok(defs::nat_rec(beta.clone())
            .apply(z.clone())?
            .apply(Self::wrap_step(s, &beta)?)?
            .apply(t.clone())?)
    }

    fn comp(&self, steps: &[Term], i: usize) -> IndResult<Thm, NativeHol> {
        let (z, s) = self.steps(steps)?;
        let beta = z.type_of()?;
        let ws = Self::wrap_step(s, &beta)?;
        // ⊢ (natRec z ws 0 = z) ∧ (∀n. natRec z ws (S n) = ws n (natRec z ws n))
        let eqs = rec_holds_proof_at(&beta)?
            .all_elim(z.clone())?
            .all_elim(ws.clone())?;
        match i {
            0 => Ok(eqs.and_elim_l()?),
            1 => {
                // β-bridge the RHS to the contract shape `s (rec … m)`.
                let m = Term::free("m", Type::nat());
                let raw = eqs.and_elim_r()?.all_elim(m.clone())?;
                // ⊢ natRec z ws (S m) = ws m (natRec z ws m)
                let Some((_, rhs)) = raw.concl().as_eq() else {
                    return internal("nat comp: recursion equation is not an equation");
                };
                let target = s.clone().apply(self.rec_app(steps, &m)?)?;
                let bridge = prove_beta_eq(rhs.clone(), target)?;
                Ok(raw.trans(bridge)?.all_intro("m", Type::nat())?)
            }
            _ => Err(InductiveError::CtorIndex { index: i, arity: 2 }),
        }
    }

    fn injective(&self, i: usize, k: usize, xs: &[Term], ys: &[Term]) -> IndResult<Thm, NativeHol> {
        match (i, k, xs, ys) {
            (1, 0, [x], [y]) => Ok(Thm::succ_inj(x.clone(), y.clone())?),
            (1, _, _, _) => Err(InductiveError::Arity {
                what: "injectivity argument tuples",
                expected: 1,
                got: xs.len().max(ys.len()),
            }),
            _ => Err(InductiveError::ArgIndex {
                ctor: self.spec.ctors[i.min(1)].name.clone(),
                index: k,
                arity: self.spec.ctors[i.min(1)].arity(),
            }),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> IndResult<Thm, NativeHol> {
        // `zero_ne_succ m : ⊢ ¬(0 = S m)`, bridged to `(Cᵢ = Cⱼ) ⟹ F`.
        match (i, j, xs, ys) {
            (0, 1, [], [m]) => {
                let eq = zero().equals(succ(m.clone()))?;
                Ok(Thm::zero_ne_succ(m.clone())?
                    .not_elim(Thm::assume(eq.clone())?)?
                    .imp_intro(&eq)?)
            }
            (1, 0, [m], []) => {
                let eq = succ(m.clone()).equals(zero())?;
                Ok(Thm::zero_ne_succ(m.clone())?
                    .not_elim(Thm::assume(eq.clone())?.sym()?)?
                    .imp_intro(&eq)?)
            }
            _ => Err(InductiveError::Unsupported {
                what: "distinctness",
                why: format!("no rule for constructor pair ({i}, {j})"),
            }),
        }
    }

    fn induct(&self, _motive: &Term, cases: Vec<Thm>) -> IndResult<Thm, NativeHol> {
        let [base, step]: [Thm; 2] =
            cases
                .try_into()
                .map_err(|c: Vec<Thm>| InductiveError::Arity {
                    what: "induction cases",
                    expected: 2,
                    got: c.len(),
                })?;
        let bare = crate::init::ext::nat_induct(base, step)?; // ⊢ ∀n. motive n
        Ok(relativize_induct(bare, &self.mem, &Type::nat())?)
    }

    fn cases(&self) -> IndResult<Thm, NativeHol> {
        let ctors = [zero(), nat_succ()];
        derive_cases_native(&self.spec, &Type::nat(), &ctors, &|m, cs| {
            self.induct(m, cs)
        })
    }

    fn mem_ctor(&self, i: usize, args: &[Term], _rec_mems: Vec<Thm>) -> IndResult<Thm, NativeHol> {
        let target = match (i, args) {
            (0, []) => zero(),
            (1, [m]) => succ(m.clone()),
            _ => {
                return Err(InductiveError::Arity {
                    what: "constructor arguments",
                    expected: if i == 0 { 0 } else { 1 },
                    got: args.len(),
                });
            }
        };
        // `mem = λt. ⊤`, so `⊢ mem (Cᵢ x⃗)` is a β-expansion of `⊢ ⊤`.
        Ok(beta_expand(&self.mem, target, truth())?)
    }

    fn mem_trivial(&self) -> Option<Thm> {
        let tv = Term::free("__t", Type::nat());
        beta_expand(&self.mem, tv, truth())
            .and_then(|t| t.all_intro("__t", Type::nat()))
            .ok()
    }

    fn caps(&self) -> BackendCaps {
        BackendCaps {
            mem_trivial: true,
            rec_injective: true,
            prim_rec: true,
        }
    }

    fn prec_app(&self, steps: &[Term], t: &Term) -> IndResult<Term, NativeHol> {
        // `natRec` *is* primitive-recursive: the para steps `[z, s]` with
        // `s : nat → β → β` are exactly its own shape — no wrapping.
        let (z, s) = self.steps(steps)?;
        let beta = z.type_of()?;
        Ok(defs::nat_rec(beta)
            .apply(z.clone())?
            .apply(s.clone())?
            .apply(t.clone())?)
    }

    fn pcomp(&self, steps: &[Term], i: usize) -> IndResult<Thm, NativeHol> {
        let (z, s) = self.steps(steps)?;
        let beta = z.type_of()?;
        // ⊢ (natRec z s 0 = z) ∧ (∀n. natRec z s (S n) = s n (natRec z s n))
        let eqs = rec_holds_proof_at(&beta)?
            .all_elim(z.clone())?
            .all_elim(s.clone())?;
        match i {
            0 => Ok(eqs.and_elim_l()?),
            1 => Ok(eqs.and_elim_r()?),
            _ => Err(InductiveError::CtorIndex { index: i, arity: 2 }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_inductive::conformance;

    fn logic() -> NativeHol {
        NativeHol
    }

    /// The engine-backed `nat` bundle passes the full conformance suite —
    /// `comp` genuinely rides the recursion engine (`rec_holds_proof_at`).
    #[test]
    fn nat_engine_conformance() {
        let th = conformance::check_backend(&logic(), &nat_backend(), &nat_spec(), &Type::nat())
            .unwrap();
        assert!(th.facts.caps().mem_trivial);
        assert!(th.facts.caps().rec_injective);
        let triv = th.facts.mem_trivial().expect("exact carrier");
        assert!(triv.hyps().is_empty());
    }

    /// **The backend-swap test**: the same consumer code (the generic
    /// conformance suite) runs verbatim against the engine backend and the
    /// impredicative backend on the *same spec* — representation is fully
    /// abstracted behind the bundle.
    #[test]
    fn backend_swap_same_consumer() {
        let church = crate::init::inductive::ImpredicativeBackend::new();
        let backends: [&dyn InductiveBackend<NativeHol>; 2] = [&NatEngineBackend, &church];
        for b in backends {
            conformance::check_backend(&logic(), b, &nat_spec(), &Type::bool()).unwrap();
        }
    }

    /// `comp` at `succ` has the contract (catamorphism) shape
    /// `⊢ ∀m. rec [z,s] (succ m) = s (rec [z,s] m)`.
    #[test]
    fn nat_comp_shape() {
        let th = nat_backend().realize(&logic(), &nat_spec()).unwrap();
        let z = Term::free("z", Type::nat());
        let s = Term::free("s", Type::fun(Type::nat(), Type::nat()));
        let steps = [z, s.clone()];
        let c1 = th.facts.comp(&steps, 1).unwrap();
        assert!(c1.hyps().is_empty());
        let m = Term::free("m", Type::nat());
        let inst = c1.all_elim(m.clone()).unwrap();
        let lhs = th.facts.rec_app(&steps, &succ(m.clone())).unwrap();
        let rhs = s.apply(th.facts.rec_app(&steps, &m).unwrap()).unwrap();
        assert_eq!(inst.concl(), &lhs.equals(rhs).unwrap());
    }

    /// Freeness through the adapter: kernel `succ_inj` / `zero_ne_succ`
    /// surfaced in the bundle shapes.
    #[test]
    fn nat_freeness() {
        let th = nat_backend().realize(&logic(), &nat_spec()).unwrap();
        let x = Term::free("x", Type::nat());
        let y = Term::free("y", Type::nat());
        let inj = th
            .facts
            .injective(1, 0, std::slice::from_ref(&x), std::slice::from_ref(&y))
            .unwrap();
        assert!(inj.hyps().is_empty());
        let d = th.facts.distinct(0, 1, &[], &[x]).unwrap();
        assert!(d.hyps().is_empty());
    }

    /// `cases` for `nat`: `⊢ ∀t. mem t ⟹ (t = 0 ∨ ∃m. t = succ m)`.
    #[test]
    fn nat_cases() {
        let th = nat_backend().realize(&logic(), &nat_spec()).unwrap();
        let c = th.facts.cases().unwrap();
        assert!(c.hyps().is_empty());
    }
}

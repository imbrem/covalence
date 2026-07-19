//! A **generic, consumer-facing conformance check** for realized bundles —
//! and the demonstration that consumers can be written once, against the
//! bundle alone, and run against *any* backend of *any* [`LogicOps`] logic.
//!
//! [`check_theory`] exercises the bundle exactly the way a downstream
//! theory would: it builds recursor steps and an induction motive through
//! the logic's ops, proves the case obligations itself, and checks the
//! bundle's answers have the contracted shapes (hypothesis-free, correct
//! conclusions where they are representation-independent). Backend-swap
//! tests are just this function called twice.
//!
//! What it checks per constructor:
//!
//! - `comp` with fresh-variable steps: hypothesis-free; for **nullary**
//!   constructors the exact conclusion `rec steps Cᵢ = stepᵢ` (for
//!   recursive constructors the ∀-bound recursive arguments live at a
//!   backend-chosen instance of the carrier, so only shape is checked).
//! - `induct` with the motive `λt. t = t`, all case obligations proved
//!   here from `refl`: exact conclusion `∀t. mem t ⟹ motive t`.
//! - `mem_ctor` bottom-up: exact conclusion `mem (Cᵢ x⃗)`,
//!   hypothesis-free, for a non-recursive constructor and (if present) a
//!   recursive one fed by the base sample.
//! - `distinct` on the first constructor pair: hypothesis-free.
//!
//! Reserved names: this module uses `__conf_`-prefixed variable names; the
//! caller's `beta` type must not mention a backend's internal type
//! variables (see the backend's docs).

use crate::backend::InductiveBackend;
use crate::error::{IndResult, InductiveError};
use crate::logic::{LogicOps, beta_expand};
use crate::spec::{ArgSort, InductiveSpec};
use crate::theory::InductiveTheory;
use crate::validated::Validated;

// TODO(cov:inductive.coinductive-conformance, major): Add backend-neutral conformance for proof-bearing GreatestFixpointFacts; reference streams currently exercise only computational observation.

fn fail<E>(msg: String) -> InductiveError<E> {
    InductiveError::Internal(msg)
}

/// The step type for constructor `i` at result type `beta`:
/// `B₁ → … → Bₖ → β` with `Bⱼ = β` at recursive positions.
fn step_ty<L: LogicOps>(
    logic: &L,
    spec: &InductiveSpec<L::Type>,
    i: usize,
    beta: &L::Type,
) -> L::Type {
    let mut ty = beta.clone();
    for (_, sort) in spec.ctors[i].args.iter().rev() {
        let arg = match sort {
            ArgSort::Rec => beta.clone(),
            ArgSort::Ext(x) => x.clone(),
        };
        ty = logic.fun_ty(arg, ty);
    }
    ty
}

/// The **para** step type for constructor `i` at result type `beta`:
/// `A₁ → … → Aₖ → B₁ → … → Bₘ → β` — raw arguments (recursive ones at the
/// `carrier`), then one image slot per recursive argument.
fn para_step_ty<L: LogicOps>(
    logic: &L,
    spec: &InductiveSpec<L::Type>,
    carrier: &L::Type,
    i: usize,
    beta: &L::Type,
) -> L::Type {
    let mut ty = beta.clone();
    for _ in spec.ctors[i].rec_positions() {
        ty = logic.fun_ty(beta.clone(), ty);
    }
    for (_, sort) in spec.ctors[i].args.iter().rev() {
        let arg = match sort {
            ArgSort::Rec => carrier.clone(),
            ArgSort::Ext(x) => x.clone(),
        };
        ty = logic.fun_ty(arg, ty);
    }
    ty
}

/// Fresh argument variables for constructor `i`, named by the spec's
/// binder hints (recursive arguments at the carrier).
fn ctor_arg_vars<L: LogicOps>(logic: &L, theory: &InductiveTheory<L>, i: usize) -> Vec<L::Term> {
    theory.spec.ctors[i]
        .args
        .iter()
        .map(|(n, s)| {
            let ty = match s {
                ArgSort::Rec => theory.ty.clone(),
                ArgSort::Ext(x) => x.clone(),
            };
            logic.var(n, ty)
        })
        .collect()
}

/// Run the full conformance suite against a realized bundle. `beta` is the
/// recursor result type used for the `comp` checks (any type of the
/// logic).
pub fn check_theory<L: LogicOps>(
    logic: &L,
    theory: &InductiveTheory<L>,
    beta: &L::Type,
) -> IndResult<(), L> {
    theory.spec.validate().map_err(InductiveError::spec)?;
    let n = theory.spec.arity();
    if theory.ctors.len() != n {
        return Err(fail(format!(
            "bundle has {} constructor terms for {} spec constructors",
            theory.ctors.len(),
            n
        )));
    }

    // -- computation laws, with fresh-variable steps --
    let steps: Vec<L::Term> = (0..n)
        .map(|i| {
            logic.var(
                &format!("__conf_s{i}"),
                step_ty(logic, &theory.spec, i, beta),
            )
        })
        .collect();
    for i in 0..n {
        let comp = theory.facts.comp(&steps, i)?;
        if !logic.hyps(&comp).is_empty() {
            return Err(fail(format!("comp({i}) has hypotheses")));
        }
        if theory.spec.ctors[i].arity() == 0 {
            // Exact conclusion is representation-independent for nullary
            // constructors: rec steps Cᵢ = stepᵢ.
            let lhs = theory.facts.rec_app(&steps, theory.ctor(i)?)?;
            let expected = logic.eq(lhs, steps[i].clone())?;
            if logic.concl(&comp) != expected {
                return Err(fail(format!(
                    "comp({i}): got {:?}, expected {:?}",
                    logic.concl(&comp),
                    expected
                )));
            }
        }
    }

    // -- primitive recursion, when the backend claims it --
    if theory.facts.caps().prim_rec {
        let psteps: Vec<L::Term> = (0..n)
            .map(|i| {
                logic.var(
                    &format!("__conf_p{i}"),
                    para_step_ty(logic, &theory.spec, &theory.ty, i, beta),
                )
            })
            .collect();
        for i in 0..n {
            let pc = theory.facts.pcomp(&psteps, i)?;
            if !logic.hyps(&pc).is_empty() {
                return Err(fail(format!("pcomp({i}) has hypotheses")));
            }
            if theory.spec.ctors[i].arity() == 0 {
                let lhs = theory.facts.prec_app(&psteps, theory.ctor(i)?)?;
                let expected = logic.eq(lhs, psteps[i].clone())?;
                if logic.concl(&pc) != expected {
                    return Err(fail(format!(
                        "pcomp({i}): got {:?}, expected {:?}",
                        logic.concl(&pc),
                        expected
                    )));
                }
            }
        }
    }

    // -- induction with the motive `λt. t = t` --
    let tv = logic.var("__conf_t", theory.ty.clone());
    let motive = logic.lam(
        "__conf_t",
        theory.ty.clone(),
        logic.eq(tv.clone(), tv.clone())?,
    );
    let mut case_thms = Vec::with_capacity(n);
    for i in 0..n {
        let args = ctor_arg_vars(logic, theory, i);
        let capp = theory.ctor_app(logic, i, &args)?;
        let refl = logic.refl(capp.clone())?;
        // ⊢ motive (Cᵢ x⃗)  (applied form)
        let mut case = beta_expand(logic, &motive, capp, refl)?;
        // Curried IHs for the recursive arguments, innermost last.
        for k in theory.spec.ctors[i]
            .rec_positions()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
        {
            let ih = logic.app(motive.clone(), args[k].clone())?;
            case = logic.imp_intro(case, &ih)?;
        }
        case_thms.push(case);
    }
    let ind = theory.facts.induct(&motive, case_thms)?;
    if !logic.hyps(&ind).is_empty() {
        return Err(fail("induct result has hypotheses".into()));
    }
    let expected = {
        let guard = theory.mem_app(logic, &tv)?;
        let body = logic.imp(guard, logic.app(motive.clone(), tv.clone())?)?;
        logic.forall("__conf_t", theory.ty.clone(), body)?
    };
    if logic.concl(&ind) != expected {
        return Err(fail(format!(
            "induct: got {:?}, expected {:?}",
            logic.concl(&ind),
            expected
        )));
    }

    // -- membership plumbing, bottom-up --
    if let Some(base) = (0..n).find(|&i| !theory.spec.ctors[i].is_recursive()) {
        let base_args = ctor_arg_vars(logic, theory, base);
        let base_mem = theory.facts.mem_ctor(base, &base_args, vec![])?;
        if !logic.hyps(&base_mem).is_empty() {
            return Err(fail("mem_ctor(base) has hypotheses".into()));
        }
        let base_term = theory.ctor_app(logic, base, &base_args)?;
        if logic.concl(&base_mem) != theory.mem_app(logic, &base_term)? {
            return Err(fail("mem_ctor(base): wrong conclusion".into()));
        }
        // A recursive constructor, fed the base sample everywhere.
        if let Some(rc) = (0..n).find(|&i| theory.spec.ctors[i].is_recursive()) {
            let args: Vec<L::Term> = theory.spec.ctors[rc]
                .args
                .iter()
                .map(|(nm, s)| match s {
                    ArgSort::Rec => Ok(base_term.clone()),
                    ArgSort::Ext(x) => Ok(logic.var(nm, x.clone())),
                })
                .collect::<IndResult<_, L>>()?;
            let mems = theory.spec.ctors[rc]
                .rec_positions()
                .map(|_| base_mem.clone())
                .collect();
            let rec_mem = theory.facts.mem_ctor(rc, &args, mems)?;
            if !logic.hyps(&rec_mem).is_empty() {
                return Err(fail("mem_ctor(recursive) has hypotheses".into()));
            }
            let rc_term = theory.ctor_app(logic, rc, &args)?;
            if logic.concl(&rec_mem) != theory.mem_app(logic, &rc_term)? {
                return Err(fail("mem_ctor(recursive): wrong conclusion".into()));
            }
        }
    }

    // -- distinctness on the first pair --
    if n >= 2 {
        let xs = ctor_arg_vars(logic, theory, 0);
        let ys: Vec<L::Term> = theory.spec.ctors[1]
            .args
            .iter()
            .map(|(nm, s)| {
                let ty = match s {
                    ArgSort::Rec => theory.ty.clone(),
                    ArgSort::Ext(x) => x.clone(),
                };
                logic.var(&format!("{nm}'"), ty)
            })
            .collect();
        let d = theory.facts.distinct(0, 1, &xs, &ys)?;
        if !logic.hyps(&d).is_empty() {
            return Err(fail("distinct(0,1) has hypotheses".into()));
        }
    }

    Ok(())
}

/// Realize `spec` through `backend` and run [`check_theory`]; returns the
/// bundle for further use.
pub fn check_backend<L: LogicOps, B: InductiveBackend<L> + ?Sized>(
    logic: &L,
    backend: &B,
    spec: &InductiveSpec<L::Type>,
    beta: &L::Type,
) -> IndResult<InductiveTheory<L>, L> {
    let spec = Validated::try_from(spec.clone()).map_err(InductiveError::spec)?;
    let theory = backend.realize_validated(logic, &spec)?;
    check_theory(logic, &theory, beta)?;
    Ok(theory)
}

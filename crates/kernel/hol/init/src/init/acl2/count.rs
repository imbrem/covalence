//! ACL2's default structural termination measure.
//!
//! `ACL2-COUNT` is a checked recursive definition over the deep ACL2 model.
//! It is installed through the ordinary S4 admission path and is shared by
//! production book replay and the measured-induction gates.

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_int;
use smol_str::SmolStr;

use super::defun::{DefunSpec, admit_defun};
use super::derivable::{
    Acl2Env, AxiomRow, Discharge, derive_axiom, model_eq_target, model_holds_target,
    model_implies_target,
};
use super::hilbert::Fact;
use super::ordinal::ordinals;

/// The canonical ACL2-COUNT definition used by ACL2 termination measures.
pub fn acl2_count_spec(env: &Acl2Env) -> Result<DefunSpec> {
    let tm = &*env.tm;
    let x = tm.sym(b"X")?;
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64))?)?;
    let q1 = tm.quote(&tm.th.aint_at(&mk_int(1i64))?)?;
    let cnt = |v: &Term| tm.app(b"ACL2-COUNT", std::slice::from_ref(v));
    let car_x = tm.app(b"CAR", std::slice::from_ref(&x))?;
    let cdr_x = tm.app(b"CDR", std::slice::from_ref(&x))?;
    let sum = tm.app(b"BINARY-+", &[cnt(&car_x)?, cnt(&cdr_x)?])?;
    let step = tm.app(b"BINARY-+", &[q1, sum])?;
    let negative = tm.app(b"<", &[x.clone(), q0.clone()])?;
    let absolute = tm.app(b"UNARY--", std::slice::from_ref(&x))?;
    let integer_base = tm.mk_if(&negative, &absolute, &x)?;
    let base = tm.mk_if(
        &tm.app(b"INTEGERP", std::slice::from_ref(&x))?,
        &integer_base,
        &q0,
    )?;
    let body = tm.mk_if(&tm.app(b"CONSP", std::slice::from_ref(&x))?, &step, &base)?;
    Ok(DefunSpec {
        name: SmolStr::new("ACL2-COUNT"),
        formals: vec![SmolStr::new("X")],
        body,
        rec_formal: Some(0),
    })
}

/// Extend an ACL2 environment with the checked ACL2-COUNT definition.
pub fn with_acl2_count(env: &Acl2Env) -> Result<Acl2Env> {
    let mut out = admit_defun(env, &acl2_count_spec(env)?)?;
    let tm = out.tm.clone();
    let x = tm.sym(b"X")?;
    let enc = tm.app(b"NATP", &[tm.app(b"ACL2-COUNT", std::slice::from_ref(&x))?])?;
    let (_, count) = out.user("ACL2-COUNT")?;
    let ord = ordinals()?;
    let invariant = ord.acl2_count_invariant_thm(&count.model, &count.def_eq_model)?;
    let model = ord.acl2_count_natp_from_invariant(&count.model, &invariant)?;
    let target = model_holds_target(&out, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(
            "acl2-count NATP model theorem does not match its ModelHolds target".into(),
        ));
    }
    out.axioms.push(AxiomRow {
        name: SmolStr::new("acl2-count-natp"),
        enc,
        discharge: Discharge::ModelHolds(model),
    });
    let car_x = tm.app(b"CAR", std::slice::from_ref(&x))?;
    let cdr_x = tm.app(b"CDR", std::slice::from_ref(&x))?;
    let count = |v: &Term| tm.app(b"ACL2-COUNT", std::slice::from_ref(v));
    let sum = tm.app(b"BINARY-+", &[count(&car_x)?, count(&cdr_x)?])?;
    let strict = tm.app(b"<", &[sum, count(&x)?])?;
    let enc = tm.mk_implies(&tm.app(b"CONSP", std::slice::from_ref(&x))?, &strict)?;
    let (_, count_row) = out.user("ACL2-COUNT")?;
    let count_row = count_row.clone();
    let model = ord.acl2_count_sum_strict_thm(&count_row.model, &count_row.def_eq_model)?;
    let target = model_implies_target(&out, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(
            "ACL2-COUNT sum-strict model theorem does not match its ModelImplies target".into(),
        ));
    }
    out.axioms.push(AxiomRow {
        name: SmolStr::new("acl2-count-sum-strict"),
        enc,
        discharge: Discharge::ModelImplies(model),
    });
    let sum = tm.app(b"BINARY-+", &[count(&car_x)?, count(&cdr_x)?])?;
    let enc = tm.mk_equal(&tm.app(b"<", &[count(&x)?, sum])?, &tm.quote(&tm.th.nil)?)?;
    let model =
        ord.acl2_count_sum_weak_thm(&count_row.model, &count_row.def_eq_model, &invariant)?;
    let target = model_eq_target(&out, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(format!(
            "ACL2-COUNT sum-weak model theorem does not match its ModelEq target: got {}; expected {target}",
            model.concl()
        )));
    }
    out.axioms.push(AxiomRow {
        name: SmolStr::new("acl2-count-sum-weak"),
        enc,
        discharge: Discharge::ModelEq(model),
    });
    let projection_strict_models = ord.acl2_count_projection_strict_thms(
        &count_row.model,
        &count_row.def_eq_model,
        &invariant,
    )?;
    for (name, projection, model) in [
        (
            "acl2-count-car-strict",
            car_x.clone(),
            projection_strict_models[0].clone(),
        ),
        (
            "acl2-count-cdr-strict",
            cdr_x.clone(),
            projection_strict_models[1].clone(),
        ),
    ] {
        let enc = tm.mk_implies(
            &tm.app(b"CONSP", std::slice::from_ref(&x))?,
            &tm.app(b"<", &[count(&projection)?, count(&x)?])?,
        )?;
        let target = model_implies_target(&out, &enc)?;
        if !model.hyps().is_empty() || model.concl() != &target {
            return Err(Error::ConnectiveRule(format!(
                "{name} model theorem does not match its ModelImplies target"
            )));
        }
        out.axioms.push(AxiomRow {
            name: SmolStr::new(name),
            enc,
            discharge: Discharge::ModelImplies(model),
        });
    }
    let projection_weak_models = ord.acl2_count_projection_weak_thms(
        &count_row.model,
        &count_row.def_eq_model,
        &invariant,
        &projection_strict_models,
    )?;
    for (name, projection, model) in [
        (
            "acl2-count-car-weak",
            car_x,
            projection_weak_models[0].clone(),
        ),
        (
            "acl2-count-cdr-weak",
            cdr_x,
            projection_weak_models[1].clone(),
        ),
    ] {
        let enc = tm.mk_equal(
            &tm.app(b"<", &[count(&x)?, count(&projection)?])?,
            &tm.quote(&tm.th.nil)?,
        )?;
        let target = model_eq_target(&out, &enc)?;
        if !model.hyps().is_empty() || model.concl() != &target {
            return Err(Error::ConnectiveRule(format!(
                "{name} model theorem does not match its ModelEq target"
            )));
        }
        out.axioms.push(AxiomRow {
            name: SmolStr::new(name),
            enc,
            discharge: Discharge::ModelEq(model),
        });
    }
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64))?)?;
    let enc = tm.mk_implies(
        &tm.app(b"CONSP", std::slice::from_ref(&x))?,
        &tm.app(b"<", &[q0, count(&x)?])?,
    )?;
    let model = ord.acl2_count_consp_positive_thm(
        &count_row.model,
        &invariant,
        &projection_strict_models[1],
    )?;
    let target = model_implies_target(&out, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(
            "ACL2-COUNT consp-positive theorem does not match its ModelImplies target".into(),
        ));
    }
    out.axioms.push(AxiomRow {
        name: SmolStr::new("acl2-count-consp-positive"),
        enc,
        discharge: Discharge::ModelImplies(model),
    });

    let a = tm.sym(b"A")?;
    let b = tm.sym(b"B")?;
    let cons = tm.app(b"CONS", &[a.clone(), b.clone()])?;
    let sum = tm.app(b"BINARY-+", &[count(&a)?, count(&b)?])?;
    let enc = tm.app(b"<", &[sum, count(&cons)?])?;
    let model = ord.acl2_count_cons_greater_thm(&count_row.model, &count_row.def_eq_model)?;
    let target = model_holds_target(&out, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(
            "ACL2-COUNT cons-greater theorem does not match its ModelHolds target".into(),
        ));
    }
    out.axioms.push(AxiomRow {
        name: SmolStr::new("acl2-count-cons-greater"),
        enc,
        discharge: Discharge::ModelHolds(model),
    });
    Ok(out)
}

/// The checked, reusable object-level fact `(NATP (ACL2-COUNT X))`.
pub fn acl2_count_natp_fact(env: &Acl2Env) -> Result<Fact> {
    let (_, enc) = env.axiom("acl2-count-natp")?;
    Ok(Fact {
        phi: enc.clone(),
        thm: derive_axiom(env, "acl2-count-natp")?,
    })
}

/// Under `(CONSP X)`, the sum of ACL2-COUNT's two recursive calls is
/// strictly below `(ACL2-COUNT X)`.
pub fn acl2_count_sum_strict_fact(env: &Acl2Env) -> Result<Fact> {
    let (_, enc) = env.axiom("acl2-count-sum-strict")?;
    Ok(Fact {
        phi: enc.clone(),
        thm: derive_axiom(env, "acl2-count-sum-strict")?,
    })
}

/// The checked unconditional weak sum bound.
pub fn acl2_count_sum_weak_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-sum-weak")
}

fn count_fact(env: &Acl2Env, name: &str) -> Result<Fact> {
    let (_, enc) = env.axiom(name)?;
    Ok(Fact {
        phi: enc.clone(),
        thm: derive_axiom(env, name)?,
    })
}

/// The checked guarded strict CAR decrease law.
pub fn acl2_count_car_strict_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-car-strict")
}

/// The checked guarded strict CDR decrease law.
pub fn acl2_count_cdr_strict_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-cdr-strict")
}

/// The closed model theorem behind the guarded CDR decrease row.
///
/// Cross-definition law packs use this theorem only to construct new checked
/// model proofs.  Keeping the accessor crate-private avoids exposing model
/// implementation details through the ACL2-facing fact API.
pub(crate) fn acl2_count_cdr_strict_model(env: &Acl2Env) -> Result<Thm> {
    let (index, _) = env.axiom("acl2-count-cdr-strict")?;
    match &env.axioms[index].discharge {
        Discharge::ModelImplies(model) => Ok(model.clone()),
        _ => Err(Error::ConnectiveRule(
            "acl2-count-cdr-strict does not have a ModelImplies discharge".into(),
        )),
    }
}

/// The checked unconditional weak CAR bound.
pub fn acl2_count_car_weak_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-car-weak")
}

/// The checked unconditional weak CDR bound.
pub fn acl2_count_cdr_weak_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-cdr-weak")
}

/// The checked guarded positivity law.
pub fn acl2_count_consp_positive_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-consp-positive")
}

/// The checked unconditional explicit-cons strictness law.
pub fn acl2_count_cons_greater_fact(env: &Acl2Env) -> Result<Fact> {
    count_fact(env, "acl2-count-cons-greater")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::acl2::derivable::s6_env;
    use crate::init::acl2::fixers::with_fixers;
    use crate::init::acl2::ordinal::with_ordinals;

    #[test]
    fn acl2_count_is_a_checked_recursive_user_row() {
        let env = with_fixers(&with_ordinals(&s6_env().unwrap()).unwrap()).unwrap();
        let env = with_acl2_count(&env).unwrap();
        let (_, row) = env.user("ACL2-COUNT").unwrap();
        assert_eq!(row.rec_formal, Some(0));
        assert!(row.def_eq_model.hyps().is_empty());
    }

    #[test]
    fn natp_model_introduction_is_closed_and_checked() {
        let thm = crate::init::acl2::ordinal::ordinals()
            .unwrap()
            .natp_intro_thm()
            .unwrap();
        assert!(thm.hyps().is_empty());
    }

    #[test]
    fn acl2_count_natp_is_a_checked_model_row_and_fact() {
        let env = with_fixers(&with_ordinals(&s6_env().unwrap()).unwrap()).unwrap();
        let env = with_acl2_count(&env).unwrap();
        let fact = acl2_count_natp_fact(&env).unwrap();
        assert!(fact.thm.hyps().is_empty());
        assert_eq!(
            fact.thm.concl(),
            &crate::init::acl2::derivable::derivable(&env, &fact.phi).unwrap()
        );
        let strict = acl2_count_sum_strict_fact(&env).unwrap();
        assert!(strict.thm.hyps().is_empty());
        assert_eq!(
            strict.thm.concl(),
            &crate::init::acl2::derivable::derivable(&env, &strict.phi).unwrap()
        );
        let weak = acl2_count_sum_weak_fact(&env).unwrap();
        assert_eq!(
            weak.thm.concl(),
            &crate::init::acl2::derivable::derivable(&env, &weak.phi).unwrap()
        );
        for projection in [
            acl2_count_car_strict_fact(&env).unwrap(),
            acl2_count_cdr_strict_fact(&env).unwrap(),
            acl2_count_car_weak_fact(&env).unwrap(),
            acl2_count_cdr_weak_fact(&env).unwrap(),
            acl2_count_consp_positive_fact(&env).unwrap(),
            acl2_count_cons_greater_fact(&env).unwrap(),
        ] {
            assert!(projection.thm.hyps().is_empty());
            assert_eq!(
                projection.thm.concl(),
                &crate::init::acl2::derivable::derivable(&env, &projection.phi).unwrap()
            );
        }
    }

    #[test]
    fn checked_count_components_replay_as_acl2_and() {
        use crate::init::acl2::simplify::{FactCache, Limits, prove_under, with_arith_rules};

        let env = with_fixers(&with_ordinals(&s6_env().unwrap()).unwrap()).unwrap();
        let env = with_arith_rules(&with_acl2_count(&env).unwrap()).unwrap();
        let cache = FactCache::default();
        let strict = acl2_count_car_strict_fact(&env).unwrap();
        let weak = acl2_count_car_weak_fact(&env).unwrap();
        cache.add_lemma(strict.clone());
        cache.add_lemma(weak.clone());
        let goal = env
            .tm
            .mk_if(
                &strict.phi,
                &weak.phi,
                &env.tm.quote(&env.tm.th.nil).unwrap(),
            )
            .unwrap();
        prove_under(&env, &cache, &[], &goal, &Limits::default()).unwrap();
    }
}

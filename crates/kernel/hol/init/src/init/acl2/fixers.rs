//! ACL2's integer and natural fixing functions.
//!
//! `IFIX` and `NFIX` are conservative, non-recursive definitions over the
//! deep ACL2 model.  Installing them goes through the ordinary S4 admission
//! path, which checks the encoded body, defines the model constant, proves its
//! model equation, and re-pins that equation against the rebuilt evaluator.

use covalence_core::{Error, Result};
use covalence_hol_eval::mk_int;
use smol_str::SmolStr;

use super::defun::{DefunSpec, admit_defun};
use super::derivable::{Acl2Env, AxiomRow, Discharge, model_holds_target, ne_from_eq};
use super::ordinal::ordinals;
use crate::init::ext::TermExt;

/// Extend an ordinal-capable environment with `IFIX`, then `NFIX`.
///
/// The order is stable and tested because it determines derivation-clause
/// indexes.  `NFIX` requires the existing `NATP` row; both definitions use
/// only checked model operations.
pub fn with_fixers(env: &Acl2Env) -> Result<Acl2Env> {
    let tm = &*env.tm;
    let x = tm.sym(b"X")?;
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64))?)?;

    let ifix = DefunSpec {
        name: SmolStr::new("IFIX"),
        formals: vec![SmolStr::new("X")],
        body: tm.mk_if(&tm.app(b"INTEGERP", std::slice::from_ref(&x))?, &x, &q0)?,
        rec_formal: None,
    };
    let env = admit_defun(env, &ifix)?;

    let tm = &*env.tm;
    let x = tm.sym(b"X")?;
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64))?)?;
    let nfix = DefunSpec {
        name: SmolStr::new("NFIX"),
        formals: vec![SmolStr::new("X")],
        body: tm.mk_if(&tm.app(b"NATP", std::slice::from_ref(&x))?, &x, &q0)?,
        rec_formal: None,
    };
    let mut env = admit_defun(&env, &nfix)?;

    // The false arm of NFIX is the quoted integer zero.  Expose the ordinary
    // ground NATP computation as a checked model-holds row so the reified
    // simplifier can close that arm without expanding NATP into a redundant
    // INTEGERP case split.  This is not the target `natp-of-nfix` theorem:
    // its discharge is independently computed by the ordinal normalizer.
    let tm = &*env.tm;
    let a0 = tm.th.aint_at(&mk_int(0i64))?;
    let enc = tm.app(b"NATP", &[tm.quote(&a0)?])?;
    let model = ordinals()?.natp.clone().apply(a0)?;
    let model_holds = ne_from_eq(tm, ordinals()?.ord_fold(&model)?, tm.pr.t_ne_nil()?)?;
    if model_holds.hyps().is_empty() && model_holds.concl() == &model_holds_target(&env, &enc)? {
        env.axioms.push(AxiomRow {
            name: SmolStr::new("natp-zero"),
            enc,
            discharge: Discharge::ModelHolds(model_holds),
        });
        Ok(env)
    } else {
        Err(Error::ConnectiveRule(
            "acl2 natp-zero model theorem does not state its target".into(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::acl2::defun::Acl2Session;
    use crate::init::acl2::derivable::{ClauseKind, s6_env};
    use crate::init::acl2::ordinal::with_ordinals;
    use crate::init::acl2::simplify::{FactCache, IndConfig, prove_by_induction};
    use crate::init::ext::TermExt;

    fn check_closed(thm: &covalence_hol_eval::EvalThm, expected: &covalence_core::Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    fn fixer_env() -> Acl2Env {
        with_fixers(&with_ordinals(&s6_env().unwrap()).unwrap()).unwrap()
    }

    #[test]
    fn fixers_are_exact_checked_rows_in_stable_order() {
        let env = fixer_env();
        let (ifix, iu) = env.user("IFIX").unwrap();
        let (nfix, nu) = env.user("NFIX").unwrap();
        assert_eq!((ifix, nfix), (7, 8));
        assert_eq!(env.row("IFIX").unwrap() + 1, env.row("NFIX").unwrap());
        assert_eq!(
            env.clause_index(ClauseKind::Def(ifix)) + 1,
            env.clause_index(ClauseKind::Def(nfix))
        );
        assert!(iu.def_eq_model.hyps().is_empty());
        assert!(nu.def_eq_model.hyps().is_empty());
    }

    #[test]
    fn four_fixing_theorems_replay_to_exact_closed_model_facts() {
        let sess = Acl2Session::new(fixer_env());
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        let x = tm.sym(b"X").unwrap();
        let xh = covalence_core::Term::free("x", tm.th.ty.clone());
        let nil = tm.th.nil.clone();
        let intp_x = tm.app(b"INTEGERP", std::slice::from_ref(&x)).unwrap();
        let natp_x = tm.app(b"NATP", std::slice::from_ref(&x)).unwrap();
        let ifix_x = tm.app(b"IFIX", std::slice::from_ref(&x)).unwrap();
        let nfix_x = tm.app(b"NFIX", std::slice::from_ref(&x)).unwrap();

        let goals = [
            tm.mk_implies(&intp_x, &tm.mk_equal(&ifix_x, &x).unwrap())
                .unwrap(),
            tm.app(
                b"INTEGERP",
                &[tm.app(b"IFIX", std::slice::from_ref(&x)).unwrap()],
            )
            .unwrap(),
            tm.mk_implies(&natp_x, &tm.mk_equal(&nfix_x, &x).unwrap())
                .unwrap(),
            tm.app(
                b"NATP",
                &[tm.app(b"NFIX", std::slice::from_ref(&x)).unwrap()],
            )
            .unwrap(),
        ];
        let ifix = env.user("IFIX").unwrap().1.model.clone();
        let nfix = env.user("NFIX").unwrap().1.model.clone();
        let natp = env.rows[env.row("NATP").unwrap()].model.clone();
        let expected = [
            tm.pr
                .intp
                .clone()
                .apply(xh.clone())
                .unwrap()
                .equals(nil.clone())
                .unwrap()
                .not()
                .unwrap()
                .imp(
                    ifix.clone()
                        .apply(xh.clone())
                        .unwrap()
                        .equals(xh.clone())
                        .unwrap(),
                )
                .unwrap()
                .forall("x", tm.th.ty.clone())
                .unwrap(),
            tm.pr
                .intp
                .clone()
                .apply(ifix.apply(xh.clone()).unwrap())
                .unwrap()
                .equals(nil.clone())
                .unwrap()
                .not()
                .unwrap()
                .forall("x", tm.th.ty.clone())
                .unwrap(),
            natp.clone()
                .apply(xh.clone())
                .unwrap()
                .equals(nil.clone())
                .unwrap()
                .not()
                .unwrap()
                .imp(
                    nfix.clone()
                        .apply(xh.clone())
                        .unwrap()
                        .equals(xh.clone())
                        .unwrap(),
                )
                .unwrap()
                .forall("x", tm.th.ty.clone())
                .unwrap(),
            natp.apply(nfix.apply(xh).unwrap())
                .unwrap()
                .equals(nil)
                .unwrap()
                .not()
                .unwrap()
                .forall("x", tm.th.ty.clone())
                .unwrap(),
        ];
        let cfg = IndConfig::default();
        for (i, (goal, want)) in goals.iter().zip(expected.iter()).enumerate() {
            let proof = prove_by_induction(&sess, &cache, goal, &cfg)
                .unwrap_or_else(|e| panic!("fixing theorem {i} failed: {e}"));
            assert_eq!(proof.var, None, "fixing laws need no induction");
            check_closed(&proof.transported, want);
        }
    }
}

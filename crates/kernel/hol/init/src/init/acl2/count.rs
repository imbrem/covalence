//! ACL2's default structural termination measure.
//!
//! `ACL2-COUNT` is a checked recursive definition over the deep ACL2 model.
//! It is installed through the ordinary S4 admission path and is shared by
//! production book replay and the measured-induction gates.

use covalence_core::{Result, Term};
use covalence_hol_eval::mk_int;
use smol_str::SmolStr;

use super::defun::{DefunSpec, admit_defun};
use super::derivable::Acl2Env;

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
    admit_defun(env, &acl2_count_spec(env)?)
}

// TODO(cov:acl2.count.upstream-five-theorem-gate, major): Transport all five exports of pinned std/lists/acl2-count.lisp and make its six-event, include-free report source-green.

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
}

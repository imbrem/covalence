//! ACL2's built-in binary `APPEND` and its checked structural laws.
//!
//! The definition goes through the ordinary S4 admission path.  The law
//! pack below contains only model theorems proved from that definition and
//! validates every theorem against the exact target expected by its
//! [`Discharge`].  Host-side matching of these laws therefore carries no
//! theorem authority.

use covalence_core::{Error, Result, Term, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use smol_str::SmolStr;

use super::carrier::acl2_payload;
use super::count::acl2_count_cdr_strict_model;
use super::defun::{DefunSpec, admit_defun, defun_law};
use super::derivable::{
    Acl2Env, AxiomRow, Discharge, derive_axiom, model_eq_target, model_implies_target,
};
use super::hilbert::Fact;
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::int;

/// ACL2's canonical total `APPEND` definition.
pub fn append_spec(env: &Acl2Env) -> Result<DefunSpec> {
    let tm = &*env.tm;
    let x = tm.sym(b"X")?;
    let y = tm.sym(b"Y")?;
    let step = tm.app(
        b"CONS",
        &[
            tm.app(b"CAR", std::slice::from_ref(&x))?,
            tm.app(
                b"APPEND",
                &[tm.app(b"CDR", std::slice::from_ref(&x))?, y.clone()],
            )?,
        ],
    )?;
    let body = tm.mk_if(&tm.app(b"CONSP", std::slice::from_ref(&x))?, &step, &y)?;
    Ok(DefunSpec {
        name: SmolStr::new("APPEND"),
        formals: vec![SmolStr::new("X"), SmolStr::new("Y")],
        body,
        rec_formal: Some(0),
    })
}

fn checked_eq_row(env: &Acl2Env, name: &str, enc: Term, model: Thm) -> Result<AxiomRow> {
    let target = model_eq_target(env, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(format!(
            "{name} model theorem does not match its ModelEq target"
        )));
    }
    Ok(AxiomRow {
        name: SmolStr::new(name),
        enc,
        discharge: Discharge::ModelEq(model),
    })
}

fn checked_implies_row(env: &Acl2Env, name: &str, enc: Term, model: Thm) -> Result<AxiomRow> {
    let target = model_implies_target(env, &enc)?;
    if !model.hyps().is_empty() || model.concl() != &target {
        return Err(Error::ConnectiveRule(format!(
            "{name} model theorem does not match its ModelImplies target"
        )));
    }
    Ok(AxiomRow {
        name: SmolStr::new(name),
        enc,
        discharge: Discharge::ModelImplies(model),
    })
}

/// Extend an ACL2 environment with checked `APPEND` and its reusable laws.
pub fn with_append(env: &Acl2Env) -> Result<Acl2Env> {
    let mut out = admit_defun(env, &append_spec(env)?)?;
    let tm = out.tm.clone();
    let (_, row) = out.user("APPEND")?;
    let row = row.clone();

    // The exact defining equation is useful as an unconditional opening law.
    out.axioms.push(checked_eq_row(
        &out,
        "append-definition",
        row.def_enc.clone(),
        row.def_eq_model.clone(),
    )?);

    let a = tm.sym(b"A")?;
    let x = tm.sym(b"X")?;
    let y = tm.sym(b"Y")?;
    let cons = tm.app(b"CONS", &[a.clone(), x.clone()])?;
    let enc = tm.mk_equal(
        &tm.app(b"APPEND", &[cons.clone(), y.clone()])?,
        &tm.app(
            b"CONS",
            &[a.clone(), tm.app(b"APPEND", &[x.clone(), y.clone()])?],
        )?,
    )?;
    let model = {
        let aa = Term::free("A", tm.th.ty.clone());
        let xx = Term::free("X", tm.th.ty.clone());
        let yy = Term::free("Y", tm.th.ty.clone());
        let cons = tm.th.cons.clone().apply(aa)?.apply(xx)?;
        defun_law(&out, &row, &[cons, yy])?
            .all_intro("Y", tm.th.ty.clone())?
            .all_intro("X", tm.th.ty.clone())?
            .all_intro("A", tm.th.ty.clone())?
    };
    out.axioms
        .push(checked_eq_row(&out, "append-of-cons", enc, model)?);

    let consp_x = tm.app(b"CONSP", std::slice::from_ref(&x))?;
    let nil = tm.quote(&tm.th.nil)?;
    let enc = tm.mk_implies(
        &tm.mk_equal(&consp_x, &nil)?,
        &tm.mk_equal(&tm.app(b"APPEND", &[x.clone(), y.clone()])?, &y)?,
    )?;
    let model = append_when_consp_nil_model(&out, &row)?;
    out.axioms.push(checked_implies_row(
        &out,
        "append-when-consp-nil",
        enc,
        model,
    )?);

    // ACL2's `OR` macro preserves the value of its first true argument, so
    // keep the exact nested-IF encoding produced by the Lisp bridge here.
    let consp_y = tm.app(b"CONSP", std::slice::from_ref(&y))?;
    let false_value = tm.quote(&tm.th.nil)?;
    let or_tail = tm.mk_if(&consp_y, &consp_y, &false_value)?;
    let enc = tm.mk_equal(
        &tm.app(b"CONSP", &[tm.app(b"APPEND", &[x.clone(), y.clone()])?])?,
        &tm.mk_if(&consp_x, &consp_x, &or_tail)?,
    )?;
    let model = consp_of_append_model(&out, &row)?;
    out.axioms
        .push(checked_eq_row(&out, "consp-of-append", enc, model)?);

    let y1 = tm.sym(b"Y1")?;
    let y2 = tm.sym(b"Y2")?;
    let enc = tm.mk_equal(
        &tm.mk_equal(
            &tm.app(b"APPEND", &[x.clone(), y1.clone()])?,
            &tm.app(b"APPEND", &[x.clone(), y2.clone()])?,
        )?,
        &tm.mk_equal(&y1, &y2)?,
    )?;
    let model = equal_when_append_same_model(&out, &row)?;
    out.axioms
        .push(checked_eq_row(&out, "equal-when-append-same", enc, model)?);

    let car_append = tm.app(b"CAR", &[tm.app(b"APPEND", &[x.clone(), y.clone()])?])?;
    let car_x = tm.app(b"CAR", std::slice::from_ref(&x))?;
    let car_y = tm.app(b"CAR", std::slice::from_ref(&y))?;
    let enc = tm.mk_equal(&car_append, &tm.mk_if(&consp_x, &car_x, &car_y)?)?;
    let model = append_projection_model(&out, &row, false)?;
    out.axioms
        .push(checked_eq_row(&out, "car-of-append", enc, model)?);

    let enc = tm.mk_implies(&consp_x, &tm.mk_equal(&car_append, &car_x)?)?;
    let model = append_projection_when_consp_model(&out, &row, false)?;
    out.axioms.push(checked_implies_row(
        &out,
        "car-of-append-when-consp",
        enc,
        model,
    )?);

    let cdr_append = tm.app(b"CDR", &[tm.app(b"APPEND", &[x.clone(), y.clone()])?])?;
    let cdr_x = tm.app(b"CDR", std::slice::from_ref(&x))?;
    let cdr_y = tm.app(b"CDR", std::slice::from_ref(&y))?;
    let append_cdr_x = tm.app(b"APPEND", &[cdr_x.clone(), y.clone()])?;
    let enc = tm.mk_equal(&cdr_append, &tm.mk_if(&consp_x, &append_cdr_x, &cdr_y)?)?;
    let model = append_projection_model(&out, &row, true)?;
    out.axioms
        .push(checked_eq_row(&out, "cdr-of-append", enc, model)?);

    let enc = tm.mk_implies(&consp_x, &tm.mk_equal(&cdr_append, &append_cdr_x)?)?;
    let model = append_projection_when_consp_model(&out, &row, true)?;
    out.axioms.push(checked_implies_row(
        &out,
        "cdr-of-append-when-consp",
        enc,
        model,
    )?);

    let b = tm.sym(b"B")?;
    let c = tm.sym(b"C")?;
    let enc = tm.mk_equal(
        &tm.app(
            b"APPEND",
            &[tm.app(b"APPEND", &[a.clone(), b.clone()])?, c.clone()],
        )?,
        &tm.app(b"APPEND", &[a, tm.app(b"APPEND", &[b, c])?])?,
    )?;
    let model = append_assoc_model(&out, &row)?;
    out.axioms
        .push(checked_eq_row(&out, "associativity-of-append", enc, model)?);
    Ok(out)
}

/// Add laws which connect checked `APPEND` with checked `ACL2-COUNT`.
///
/// This is deliberately separate from [`with_append`]: the core list
/// operation remains usable without installing the ordinal/count stack, while
/// production book replay can opt into the stronger cross-definition pack.
pub fn with_append_count_laws(env: &Acl2Env) -> Result<Acl2Env> {
    let mut out = env.clone();
    let tm = out.tm.clone();
    let (_, append) = out.user("APPEND")?;
    let append = append.clone();
    let (_, count) = out.user("ACL2-COUNT")?;
    let count = count.clone();

    let x = tm.sym(b"X")?;
    let y = tm.sym(b"Y")?;
    let consp_x = tm.app(b"CONSP", std::slice::from_ref(&x))?;
    let app_xy = tm.app(b"APPEND", &[x.clone(), y.clone()])?;
    let count_y = tm.app(b"ACL2-COUNT", std::slice::from_ref(&y))?;
    let count_app = tm.app(b"ACL2-COUNT", std::slice::from_ref(&app_xy))?;
    let growth = tm.app(b"<", &[count_y, count_app])?;
    let growth_enc = tm.mk_implies(&consp_x, &growth)?;
    let growth_model = append_count_growth_model(&out, &append, &count)?;
    out.axioms.push(checked_implies_row(
        &out,
        "acl2-count-of-append-strict",
        growth_enc,
        growth_model.clone(),
    )?);

    // Exact macro-expanded shape of the local upstream theorem:
    // (implies (consp x) (not (equal (append x y) y))).
    let equal = tm.mk_equal(&app_xy, &y)?;
    let not_equal = tm.mk_if(&equal, &tm.quote(&tm.th.nil)?, &tm.quote(&tm.pr.t)?)?;
    let enc = tm.mk_implies(&consp_x, &not_equal)?;
    let model = append_nonempty_model(&out, &append, &count, &growth_model)?;
    out.axioms.push(checked_implies_row(
        &out,
        "append-nonempty-list",
        enc,
        model,
    )?);
    Ok(out)
}

fn consp_guard(env: &Acl2Env, v: &Term) -> Result<Term> {
    env.tm
        .pr
        .consp
        .clone()
        .apply(v.clone())?
        .equals(env.tm.th.nil.clone())?
        .not()
}

fn append_count_growth_model(
    env: &Acl2Env,
    append: &super::derivable::UserRow,
    count: &super::derivable::UserRow,
) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y = Term::free("Y", a.clone());
    let app = |p: &Term| append.model.clone().apply(p.clone())?.apply(y.clone());
    let cnt = |p: &Term| count.model.clone().apply(p.clone());
    let alt_holds = |l: &Term, r: &Term| {
        tm.pr
            .lt
            .clone()
            .apply(l.clone())?
            .apply(r.clone())?
            .equals(tm.th.nil.clone())?
            .not()
    };
    let count_y = cnt(&y)?;
    let motive = {
        let v = Term::free("__append_count_x", a.clone());
        let goal = consp_guard(env, &v)?.imp(alt_holds(&count_y, &cnt(&app(&v)?)?)?)?;
        Term::abs(a.clone(), subst::close(&goal, "__append_count_x"))
    };
    let leaf_case = |leaf: Term, consp_nil: Thm| -> Result<Thm> {
        let guard = consp_guard(env, &leaf)?;
        let goal = alt_holds(&count_y, &cnt(&app(&leaf)?)?)?;
        let absurd = Thm::assume(guard.clone())?.not_elim(consp_nil)?;
        beta_expand(&motive, leaf, absurd.false_elim(goal)?.imp_intro(&guard)?)
    };
    let payload = Term::free("b", acl2_payload());
    let case_atom = leaf_case(
        tm.th.atom.clone().apply(payload.clone())?,
        tm.pr.consp_atom()?.all_elim(payload)?,
    )?;
    let case_nil = leaf_case(tm.th.nil.clone(), tm.pr.consp_nil()?)?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let app_t = app(&t)?;
        let z = tm.th.cons.clone().apply(h.clone())?.apply(app_t.clone())?;
        let cons = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let ph = motive.clone().apply(h.clone())?;
        let pt = motive.clone().apply(t.clone())?;
        let guard_cons = consp_guard(env, &cons)?;
        let consp_z = tm.pr.consp.clone().apply(z.clone())?;
        let consp_z_t = tm
            .pr
            .consp_cons()?
            .all_elim(h.clone())?
            .all_elim(app_t.clone())?;
        let z_nil = consp_z.clone().equals(tm.th.nil.clone())?;
        let t_nil = consp_z_t.sym()?.trans(Thm::assume(z_nil.clone())?)?;
        let z_guard = tm
            .pr
            .t_ne_nil()?
            .not_elim(t_nil)?
            .imp_intro(&z_nil)?
            .not_intro()?;
        let strict_tail_z = acl2_count_cdr_strict_model(env)?
            .all_elim(z.clone())?
            .imp_elim(z_guard)?;
        let cdr_eq = tm
            .pr
            .cdr_cons()?
            .all_elim(h.clone())?
            .all_elim(app_t.clone())?;
        let tail_strict = strict_tail_z.rewrite(&cdr_eq.cong_arg(count.model.clone())?)?;
        let opened = defun_law(env, append, &[cons.clone(), y.clone()])?;
        let target_open = opened.cong_arg(count.model.clone())?;
        let tail_strict = tail_strict.rewrite(&target_open.sym()?)?;

        let eq = tm
            .pr
            .consp
            .clone()
            .apply(t.clone())?
            .equals(tm.th.nil.clone())?;
        let tail_consp = eq.clone().not()?;
        let positive = {
            let ih = beta_reduce(Thm::assume(pt.clone())?)?
                .imp_elim(Thm::assume(tail_consp.clone())?)?;
            let first = tm.pr.alt_iff_at(&count_y, &cnt(&app_t)?)?.eq_mp(ih)?;
            let second = tm
                .pr
                .alt_iff_at(&cnt(&app_t)?, &cnt(&app(&cons)?)?)?
                .eq_mp(tail_strict.clone())?;
            let trans = int::lt_trans()
                .all_elim(tm.pr.intval.clone().apply(count_y.clone())?)?
                .all_elim(tm.pr.intval.clone().apply(cnt(&app_t)?)?)?
                .all_elim(tm.pr.intval.clone().apply(cnt(&app(&cons)?)?)?)?
                .imp_elim(first)?
                .imp_elim(second)?;
            tm.pr
                .alt_iff_at(&count_y, &cnt(&app(&cons)?)?)?
                .sym()?
                .eq_mp(trans)?
                .imp_intro(&tail_consp)?
        };
        let negative = {
            let car_t = tm.th.car.clone().apply(t.clone())?;
            let cdr_t = tm.th.cdr.clone().apply(t.clone())?;
            let step = tm.th.cons.clone().apply(car_t)?.apply(app(&cdr_t)?)?;
            let app_leaf = append
                .def_eq_model
                .clone()
                .all_elim(t.clone())?
                .all_elim(y.clone())?
                .rhs_conv(|rhs| rhs.rw_all(&Thm::assume(eq.clone())?))?
                .trans(tm.pr.if_nil()?.all_elim(step)?.all_elim(y.clone())?)?;
            tail_strict
                .clone()
                .rewrite(&app_leaf.cong_arg(count.model.clone())?)?
                .imp_intro(&eq)?
        };
        let raw = Thm::lem(eq)?.or_elim(negative, positive)?;
        let guarded = raw.imp_intro(&guard_cons)?;
        beta_expand(&motive, cons, guarded)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };
    let by_x = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    beta_reduce(by_x.all_elim(x)?)?
        .all_intro("Y", a.clone())?
        .all_intro("X", a)
}

fn append_nonempty_model(
    env: &Acl2Env,
    append: &super::derivable::UserRow,
    count: &super::derivable::UserRow,
    growth: &Thm,
) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y = Term::free("Y", a.clone());
    let app = append.model.clone().apply(x.clone())?.apply(y.clone())?;
    let count_y = count.model.clone().apply(y.clone())?;
    let count_app = count.model.clone().apply(app.clone())?;
    let guard = consp_guard(env, &x)?;
    let strict_holds = growth
        .clone()
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .imp_elim(Thm::assume(guard.clone())?)?;
    let strict = tm
        .pr
        .alt_iff_at(&count_y, &count_app)?
        .eq_mp(strict_holds)?;
    let eq = app.clone().equals(y.clone())?;
    let neq = {
        let count_eq = Thm::assume(eq.clone())?.cong_arg(count.model.clone())?;
        let intval_eq = count_eq.cong_arg(tm.pr.intval.clone())?;
        let looped = strict.rewrite(&intval_eq)?;
        int::lt_irrefl()
            .all_elim(tm.pr.intval.clone().apply(count_y.clone())?)?
            .not_elim(looped)?
            .imp_intro(&eq)?
            .not_intro()?
    };
    let equal_answer = tm.pr.equal.clone().apply(app.clone())?.apply(y.clone())?;
    let equal_nil = tm
        .pr
        .equal_ne()?
        .all_elim(app)?
        .all_elim(y)?
        .imp_elim(neq)?;
    let result = tm
        .pr
        .aif
        .clone()
        .apply(equal_answer)?
        .apply(tm.th.nil.clone())?
        .apply(tm.pr.t.clone())?;
    let result_t = equal_nil
        .cong_arg(tm.pr.aif.clone())?
        .cong_fn(tm.th.nil.clone())?
        .cong_fn(tm.pr.t.clone())?
        .trans(
            tm.pr
                .if_nil()?
                .all_elim(tm.th.nil.clone())?
                .all_elim(tm.pr.t.clone())?,
        )?;
    let result_nil = result.clone().equals(tm.th.nil.clone())?;
    let t_nil = result_t.sym()?.trans(Thm::assume(result_nil.clone())?)?;
    let result_ne = tm
        .pr
        .t_ne_nil()?
        .not_elim(t_nil)?
        .imp_intro(&result_nil)?
        .not_intro()?;
    result_ne
        .imp_intro(&guard)?
        .all_intro("Y", a.clone())?
        .all_intro("X", a)
}

fn append_when_consp_nil_model(env: &Acl2Env, row: &super::derivable::UserRow) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y = Term::free("Y", a.clone());
    let consp = tm.pr.consp.clone().apply(x.clone())?;
    let equal = tm
        .pr
        .equal
        .clone()
        .apply(consp.clone())?
        .apply(tm.th.nil.clone())?;
    let hyp = equal.equals(tm.th.nil.clone())?.not()?;
    let guard_eq = tm
        .pr
        .equal_holds()?
        .all_elim(consp)?
        .all_elim(tm.th.nil.clone())?
        .imp_elim(Thm::assume(hyp.clone())?)?;
    let step = tm
        .th
        .cons
        .clone()
        .apply(tm.th.car.clone().apply(x.clone())?)?
        .apply(
            row.model
                .clone()
                .apply(tm.th.cdr.clone().apply(x.clone())?)?
                .apply(y.clone())?,
        )?;
    let opened = row.def_eq_model.clone().all_elim(x)?.all_elim(y.clone())?;
    let reduced = opened
        .rhs_conv(|rhs| rhs.rw_all(&guard_eq))?
        .trans(tm.pr.if_nil()?.all_elim(step)?.all_elim(y)?)?;
    reduced
        .imp_intro(&hyp)?
        .all_intro("Y", a.clone())?
        .all_intro("X", a)
}

fn append_assoc_model(env: &Acl2Env, row: &super::derivable::UserRow) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let (x, y, z) = (
        Term::free("A", a.clone()),
        Term::free("B", a.clone()),
        Term::free("C", a.clone()),
    );
    let app = |p: &Term, q: &Term| row.model.clone().apply(p.clone())?.apply(q.clone());
    let yz = app(&y, &z)?;
    let motive = {
        let v = Term::free("__append_x", a.clone());
        let goal = app(&app(&v, &y)?, &z)?.equals(app(&v, &yz)?)?;
        Term::abs(a.clone(), subst::close(&goal, "__append_x"))
    };
    let law = |v: &Term, w: &Term| defun_law(env, row, &[v.clone(), w.clone()]);
    let leaf_case = |leaf: Term| -> Result<Thm> {
        let inner = law(&leaf, &y)?;
        let lhs = inner.cong_arg(row.model.clone())?.cong_fn(z.clone())?;
        let rhs = law(&leaf, &yz)?;
        beta_expand(&motive, leaf, lhs.trans(rhs.sym()?)?)
    };
    let payload = Term::free("b", acl2_payload());
    let case_atom = leaf_case(tm.th.atom.clone().apply(payload)?)?;
    let case_nil = leaf_case(tm.th.nil.clone())?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let ph = motive.clone().apply(h.clone())?;
        let pt = motive.clone().apply(t.clone())?;
        let ih = beta_reduce(Thm::assume(pt.clone())?)?;
        let ht = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let lhs1 = law(&ht, &y)?
            .cong_arg(row.model.clone())?
            .cong_fn(z.clone())?;
        let ty = app(&t, &y)?;
        let hty = tm.th.cons.clone().apply(h.clone())?.apply(ty)?;
        let lhs = lhs1.trans(law(&hty, &z)?)?;
        let mid = ih.cong_arg(tm.th.cons.clone().apply(h.clone())?)?;
        let raw = lhs.trans(mid)?.trans(law(&ht, &yz)?.sym()?)?;
        beta_expand(&motive, ht, raw)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };
    let by_x = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    beta_reduce(by_x.all_elim(x)?)?
        .all_intro("C", a.clone())?
        .all_intro("B", a.clone())?
        .all_intro("A", a)
}

/// `CONSP` returns only ACL2 booleans, hence its value is unchanged by the
/// value-preserving final arm generated for `(OR (CONSP Y))`.
fn consp_or_tail_model(env: &Acl2Env) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let y = Term::free("Y", a.clone());
    let motive = {
        let v = Term::free("__consp_or_y", a.clone());
        let consp = tm.pr.consp.clone().apply(v)?;
        let goal = tm
            .pr
            .aif
            .clone()
            .apply(consp.clone())?
            .apply(consp.clone())?
            .apply(tm.th.nil.clone())?
            .equals(consp)?;
        Term::abs(a.clone(), subst::close(&goal, "__consp_or_y"))
    };
    let leaf_case = |leaf: Term, consp_leaf: Thm| -> Result<Thm> {
        let consp = tm.pr.consp.clone().apply(leaf.clone())?;
        let lhs = consp_leaf
            .clone()
            .cong_arg(tm.pr.aif.clone())?
            .cong_fn(consp.clone())?
            .cong_fn(tm.th.nil.clone())?
            .trans(
                tm.pr
                    .if_nil()?
                    .all_elim(consp)?
                    .all_elim(tm.th.nil.clone())?,
            )?;
        beta_expand(&motive, leaf, lhs.trans(consp_leaf.sym()?)?)
    };
    let payload = Term::free("b", acl2_payload());
    let atom = tm.th.atom.clone().apply(payload.clone())?;
    let case_atom = leaf_case(atom, tm.pr.consp_atom()?.all_elim(payload)?)?;
    let case_nil = leaf_case(tm.th.nil.clone(), tm.pr.consp_nil()?)?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let cons = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let consp_cons = tm
            .pr
            .consp_cons()?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        let consp = tm.pr.consp.clone().apply(cons.clone())?;
        let lhs = consp_cons
            .clone()
            .cong_arg(tm.pr.aif.clone())?
            .cong_fn(consp.clone())?
            .cong_fn(tm.th.nil.clone())?
            .trans(
                tm.pr
                    .if_t()?
                    .all_elim(tm.pr.t.clone())?
                    .all_elim(consp)?
                    .all_elim(tm.th.nil.clone())?
                    .imp_elim(tm.pr.t_ne_nil()?)?,
            )?;
        let ph = motive.clone().apply(h)?;
        let pt = motive.clone().apply(t)?;
        beta_expand(&motive, cons, lhs)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };
    let by_y = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    beta_reduce(by_y.all_elim(y)?)?.all_intro("Y", a)
}

fn consp_of_append_model(env: &Acl2Env, row: &super::derivable::UserRow) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y = Term::free("Y", a.clone());
    let consp_y = tm.pr.consp.clone().apply(y.clone())?;
    let or_tail = tm
        .pr
        .aif
        .clone()
        .apply(consp_y.clone())?
        .apply(consp_y)?
        .apply(tm.th.nil.clone())?;
    let motive = {
        let v = Term::free("__consp_append_x", a.clone());
        let consp_v = tm.pr.consp.clone().apply(v.clone())?;
        let append_vy = row.model.clone().apply(v)?.apply(y.clone())?;
        let goal = tm.pr.consp.clone().apply(append_vy)?.equals(
            tm.pr
                .aif
                .clone()
                .apply(consp_v.clone())?
                .apply(consp_v)?
                .apply(or_tail.clone())?,
        )?;
        Term::abs(a.clone(), subst::close(&goal, "__consp_append_x"))
    };
    let tail = consp_or_tail_model(env)?.all_elim(y.clone())?;
    let leaf_case = |leaf: Term, consp_leaf: Thm| -> Result<Thm> {
        let opened =
            defun_law(env, row, &[leaf.clone(), y.clone()])?.cong_arg(tm.pr.consp.clone())?;
        let consp = tm.pr.consp.clone().apply(leaf.clone())?;
        let rhs = consp_leaf
            .cong_arg(tm.pr.aif.clone())?
            .cong_fn(consp.clone())?
            .cong_fn(or_tail.clone())?
            .trans(tm.pr.if_nil()?.all_elim(consp)?.all_elim(or_tail.clone())?)?
            .trans(tail.clone())?;
        beta_expand(&motive, leaf, opened.trans(rhs.sym()?)?)
    };
    let payload = Term::free("b", acl2_payload());
    let atom = tm.th.atom.clone().apply(payload.clone())?;
    let case_atom = leaf_case(atom, tm.pr.consp_atom()?.all_elim(payload)?)?;
    let case_nil = leaf_case(tm.th.nil.clone(), tm.pr.consp_nil()?)?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let cons = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let append_ty = row.model.clone().apply(t.clone())?.apply(y.clone())?;
        let opened = defun_law(env, row, &[cons.clone(), y.clone()])?
            .cong_arg(tm.pr.consp.clone())?
            .trans(
                tm.pr
                    .consp_cons()?
                    .all_elim(h.clone())?
                    .all_elim(append_ty)?,
            )?;
        let consp_cons = tm
            .pr
            .consp_cons()?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        let consp = tm.pr.consp.clone().apply(cons.clone())?;
        let rhs = consp_cons
            .clone()
            .cong_arg(tm.pr.aif.clone())?
            .cong_fn(consp.clone())?
            .cong_fn(or_tail.clone())?
            .trans(
                tm.pr
                    .if_t()?
                    .all_elim(tm.pr.t.clone())?
                    .all_elim(consp)?
                    .all_elim(or_tail.clone())?
                    .imp_elim(tm.pr.t_ne_nil()?)?,
            )?
            .trans(consp_cons)?;
        let raw = opened.trans(rhs.sym()?)?;
        let ph = motive.clone().apply(h)?;
        let pt = motive.clone().apply(t)?;
        beta_expand(&motive, cons, raw)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };
    let by_x = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    beta_reduce(by_x.all_elim(x)?)?
        .all_intro("Y", a.clone())?
        .all_intro("X", a)
}

/// Turn a proved HOL-level equivalence `(a = b) ⇔ (c = d)` into equality
/// of ACL2's total `EQUAL` answers.  The proof splits on `a = b`; positive
/// branches reduce both answers with `equal_refl`, and negative branches
/// with `equal_ne`.  Consequently this helper depends only on S1's checked
/// equality model, not on host evaluation.
fn equal_answers_from_iff(
    env: &Acl2Env,
    a: &Term,
    b: &Term,
    c: &Term,
    d: &Term,
    p_to_q: Thm,
    q_to_p: Thm,
) -> Result<Thm> {
    let tm = &*env.tm;
    let p = a.clone().equals(b.clone())?;
    let q = c.clone().equals(d.clone())?;
    let answer = |x: &Term, y: &Term| tm.pr.equal.clone().apply(x.clone())?.apply(y.clone());
    let positive = {
        let hp = Thm::assume(p.clone())?;
        let hq = p_to_q.imp_elim(hp.clone())?;
        let left = hp
            .cong_arg(tm.pr.equal.clone().apply(a.clone())?)?
            .sym()?
            .trans(tm.pr.equal_refl()?.all_elim(a.clone())?)?;
        let right = hq
            .cong_arg(tm.pr.equal.clone().apply(c.clone())?)?
            .sym()?
            .trans(tm.pr.equal_refl()?.all_elim(c.clone())?)?;
        left.trans(right.sym()?)?.imp_intro(&p)?
    };
    let negative = {
        let np = p.clone().not()?;
        let hnp = Thm::assume(np.clone())?;
        let nq = {
            let hq = Thm::assume(q.clone())?;
            let hp = q_to_p.imp_elim(hq)?;
            hnp.clone().not_elim(hp)?.imp_intro(&q)?.not_intro()?
        };
        let left = tm
            .pr
            .equal_ne()?
            .all_elim(a.clone())?
            .all_elim(b.clone())?
            .imp_elim(hnp)?;
        let right = tm
            .pr
            .equal_ne()?
            .all_elim(c.clone())?
            .all_elim(d.clone())?
            .imp_elim(nq)?;
        left.trans(right.sym()?)?.imp_intro(&np)?
    };
    let expected = answer(a, b)?.equals(answer(c, d)?)?;
    let out = Thm::lem(p)?.or_elim(positive, negative)?;
    if out.concl() != &expected {
        return Err(Error::ConnectiveRule(
            "acl2 append equality-answer bridge built an unexpected target".into(),
        ));
    }
    Ok(out)
}

fn equal_cons_same_head(env: &Acl2Env, h: &Term, left: &Term, right: &Term) -> Result<Thm> {
    let tm = &*env.tm;
    let cons_left = tm.th.cons.clone().apply(h.clone())?.apply(left.clone())?;
    let cons_right = tm.th.cons.clone().apply(h.clone())?.apply(right.clone())?;
    let p = cons_left.clone().equals(cons_right.clone())?;
    let q = left.clone().equals(right.clone())?;
    let p_to_q = tm
        .th
        .cons_inj(h, left, h, right)?
        .imp_elim(Thm::assume(p.clone())?)?
        .conjuncts()?
        .1
        .imp_intro(&p)?;
    let q_to_p = Thm::assume(q.clone())?
        .cong_arg(tm.th.cons.clone().apply(h.clone())?)?
        .imp_intro(&q)?;
    equal_answers_from_iff(env, &cons_left, &cons_right, left, right, p_to_q, q_to_p)
}

fn equal_when_append_same_model(env: &Acl2Env, row: &super::derivable::UserRow) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y1 = Term::free("Y1", a.clone());
    let y2 = Term::free("Y2", a.clone());
    let app = |p: &Term, q: &Term| row.model.clone().apply(p.clone())?.apply(q.clone());
    let answer = |p: &Term, q: &Term| tm.pr.equal.clone().apply(p.clone())?.apply(q.clone());
    let rhs = answer(&y1, &y2)?;
    let motive = {
        let v = Term::free("__append_cancel_x", a.clone());
        let goal = answer(&app(&v, &y1)?, &app(&v, &y2)?)?.equals(rhs.clone())?;
        Term::abs(a.clone(), subst::close(&goal, "__append_cancel_x"))
    };
    let leaf_case = |leaf: Term| -> Result<Thm> {
        let app2 = app(&leaf, &y2)?;
        let raw = defun_law(env, row, &[leaf.clone(), y1.clone()])?
            .cong_arg(tm.pr.equal.clone())?
            .cong_fn(app2)?
            .trans(
                defun_law(env, row, &[leaf.clone(), y2.clone()])?
                    .cong_arg(tm.pr.equal.clone().apply(y1.clone())?)?,
            )?;
        beta_expand(&motive, leaf, raw)
    };
    let payload = Term::free("b", acl2_payload());
    let case_atom = leaf_case(tm.th.atom.clone().apply(payload)?)?;
    let case_nil = leaf_case(tm.th.nil.clone())?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let cons = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let app_t_y1 = app(&t, &y1)?;
        let app_t_y2 = app(&t, &y2)?;
        let app_cons_y2 = app(&cons, &y2)?;
        let open_left = defun_law(env, row, &[cons.clone(), y1.clone()])?
            .cong_arg(tm.pr.equal.clone())?
            .cong_fn(app_cons_y2)?;
        let cons_left = tm
            .th
            .cons
            .clone()
            .apply(h.clone())?
            .apply(app_t_y1.clone())?;
        let open_right = defun_law(env, row, &[cons.clone(), y2.clone()])?
            .cong_arg(tm.pr.equal.clone().apply(cons_left)?)?;
        let strip = equal_cons_same_head(env, &h, &app_t_y1, &app_t_y2)?;
        let ph = motive.clone().apply(h.clone())?;
        let pt = motive.clone().apply(t.clone())?;
        let ih = beta_reduce(Thm::assume(pt.clone())?)?;
        beta_expand(
            &motive,
            cons,
            open_left.trans(open_right)?.trans(strip)?.trans(ih)?,
        )?
        .imp_intro(&pt)?
        .imp_intro(&ph)?
    };
    let by_x = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    beta_reduce(by_x.all_elim(x)?)?
        .all_intro("Y2", a.clone())?
        .all_intro("Y1", a.clone())?
        .all_intro("X", a)
}

/// Prove the two unconditional projection laws in one structural argument.
///
/// `take_cdr = false` proves `car (append x y) =
/// if (consp x) (car x) (car y)`.  The `cdr` branch substitutes
/// `append (cdr x) y` for the true arm.  This goes through the same carrier
/// induction and admitted `APPEND` equation as associativity; no host
/// simplifier result enters the theorem.
fn append_projection_model(
    env: &Acl2Env,
    row: &super::derivable::UserRow,
    take_cdr: bool,
) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y = Term::free("Y", a.clone());
    let projection = |v: &Term| {
        if take_cdr {
            tm.th.cdr.clone().apply(v.clone())
        } else {
            tm.th.car.clone().apply(v.clone())
        }
    };
    let app = |p: &Term, q: &Term| row.model.clone().apply(p.clone())?.apply(q.clone());
    let true_arm = |v: &Term| {
        if take_cdr {
            app(&projection(v)?, &y)
        } else {
            projection(v)
        }
    };
    let motive = {
        let v = Term::free("__append_projection_x", a.clone());
        let goal = projection(&app(&v, &y)?)?.equals(
            tm.pr
                .aif
                .clone()
                .apply(tm.pr.consp.clone().apply(v.clone())?)?
                .apply(true_arm(&v)?)?
                .apply(projection(&y)?)?,
        )?;
        Term::abs(a.clone(), subst::close(&goal, "__append_projection_x"))
    };
    let leaf_case = |leaf: Term, consp_leaf: Thm| -> Result<Thm> {
        let lhs = defun_law(env, row, &[leaf.clone(), y.clone()])?.cong_arg(if take_cdr {
            tm.th.cdr.clone()
        } else {
            tm.th.car.clone()
        })?;
        let true_value = true_arm(&leaf)?;
        let false_value = projection(&y)?;
        let rhs = consp_leaf
            .cong_arg(tm.pr.aif.clone())?
            .cong_fn(true_value.clone())?
            .cong_fn(false_value.clone())?
            .trans(
                tm.pr
                    .if_nil()?
                    .all_elim(true_value)?
                    .all_elim(false_value)?,
            )?;
        beta_expand(&motive, leaf, lhs.trans(rhs.sym()?)?)
    };
    let payload = Term::free("b", acl2_payload());
    let atom = tm.th.atom.clone().apply(payload.clone())?;
    let case_atom = leaf_case(atom, tm.pr.consp_atom()?.all_elim(payload)?)?;
    let case_nil = leaf_case(tm.th.nil.clone(), tm.pr.consp_nil()?)?;
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let cons = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let app_t_y = app(&t, &y)?;
        let lhs = defun_law(env, row, &[cons.clone(), y.clone()])?
            .cong_arg(if take_cdr {
                tm.th.cdr.clone()
            } else {
                tm.th.car.clone()
            })?
            .trans(if take_cdr {
                tm.pr.cdr_cons()?.all_elim(h.clone())?.all_elim(app_t_y)?
            } else {
                tm.pr.car_cons()?.all_elim(h.clone())?.all_elim(app_t_y)?
            })?;
        let true_value = true_arm(&cons)?;
        let false_value = projection(&y)?;
        let true_reduced = if take_cdr {
            tm.pr
                .cdr_cons()?
                .all_elim(h.clone())?
                .all_elim(t.clone())?
                .cong_arg(row.model.clone())?
                .cong_fn(y.clone())?
        } else {
            tm.pr.car_cons()?.all_elim(h.clone())?.all_elim(t.clone())?
        };
        let rhs = tm
            .pr
            .consp_cons()?
            .all_elim(h.clone())?
            .all_elim(t.clone())?
            .cong_arg(tm.pr.aif.clone())?
            .cong_fn(true_value.clone())?
            .cong_fn(false_value.clone())?
            .trans(
                tm.pr
                    .if_t()?
                    .all_elim(tm.pr.t.clone())?
                    .all_elim(true_value)?
                    .all_elim(false_value)?
                    .imp_elim(tm.pr.t_ne_nil()?)?,
            )?
            .trans(true_reduced)?;
        let ph = motive.clone().apply(h.clone())?;
        let pt = motive.clone().apply(t.clone())?;
        beta_expand(&motive, cons, lhs.trans(rhs.sym()?)?)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };
    let by_x = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    beta_reduce(by_x.all_elim(x)?)?
        .all_intro("Y", a.clone())?
        .all_intro("X", a)
}

/// Specialize an unconditional projection theorem under ACL2 truth of
/// `CONSP X`; `if_t` turns its true arm into the guarded theorem's target.
fn append_projection_when_consp_model(
    env: &Acl2Env,
    row: &super::derivable::UserRow,
    take_cdr: bool,
) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let x = Term::free("X", a.clone());
    let y = Term::free("Y", a.clone());
    let consp = tm.pr.consp.clone().apply(x.clone())?;
    let hyp = consp.clone().equals(tm.th.nil.clone())?.not()?;
    let projection = if take_cdr {
        tm.th.cdr.clone()
    } else {
        tm.th.car.clone()
    };
    let true_value = if take_cdr {
        row.model
            .clone()
            .apply(projection.clone().apply(x.clone())?)?
            .apply(y.clone())?
    } else {
        projection.clone().apply(x.clone())?
    };
    let false_value = projection.apply(y.clone())?;
    append_projection_model(env, row, take_cdr)?
        .all_elim(x)?
        .all_elim(y)?
        .trans(
            tm.pr
                .if_t()?
                .all_elim(consp)?
                .all_elim(true_value)?
                .all_elim(false_value)?
                .imp_elim(Thm::assume(hyp.clone())?)?,
        )?
        .imp_intro(&hyp)?
        .all_intro("Y", a.clone())?
        .all_intro("X", a)
}

fn append_fact(env: &Acl2Env, name: &str) -> Result<Fact> {
    let (_, enc) = env.axiom(name)?;
    Ok(Fact {
        phi: enc.clone(),
        thm: derive_axiom(env, name)?,
    })
}

/// Checked defining-equation fact for `APPEND`.
pub fn append_definition_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "append-definition")
}

/// Checked `(APPEND (CONS A X) Y)` opening fact.
pub fn append_of_cons_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "append-of-cons")
}

/// Checked non-cons opening fact, expressed with ACL2's false guard.
pub fn append_when_consp_nil_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "append-when-consp-nil")
}

/// Checked predicate characterization for `CONSP` of `APPEND`.
pub fn consp_of_append_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "consp-of-append")
}

/// Checked cancellation of a shared left `APPEND` prefix.
pub fn equal_when_append_same_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "equal-when-append-same")
}

/// Checked unconditional `CAR` projection through `APPEND`.
pub fn car_of_append_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "car-of-append")
}

/// Checked `CAR` projection through `APPEND` under a `CONSP` guard.
pub fn car_of_append_when_consp_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "car-of-append-when-consp")
}

/// Checked unconditional `CDR` projection through `APPEND`.
pub fn cdr_of_append_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "cdr-of-append")
}

/// Checked `CDR` projection through `APPEND` under a `CONSP` guard.
pub fn cdr_of_append_when_consp_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "cdr-of-append-when-consp")
}

/// Checked associativity fact for ACL2 `APPEND`.
pub fn append_assoc_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "associativity-of-append")
}

/// Checked strict growth of `ACL2-COUNT` across nonempty `APPEND`.
pub fn append_count_strict_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "acl2-count-of-append-strict")
}

/// Exact checked fact used by the upstream local `append-nonempty-list`.
pub fn append_nonempty_fact(env: &Acl2Env) -> Result<Fact> {
    append_fact(env, "append-nonempty-list")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::acl2::count::with_acl2_count;
    use crate::init::acl2::derivable::ground_env;
    use crate::init::acl2::derivable::s6_env;
    use crate::init::acl2::fixers::with_fixers;
    use crate::init::acl2::ordinal::with_ordinals;

    #[test]
    fn append_is_checked_and_every_law_matches_its_exact_model_target() {
        let env = with_append(&ground_env().unwrap()).unwrap();
        assert!(env.user("APPEND").is_ok());
        for name in [
            "append-definition",
            "append-of-cons",
            "append-when-consp-nil",
            "consp-of-append",
            "equal-when-append-same",
            "car-of-append",
            "car-of-append-when-consp",
            "cdr-of-append",
            "cdr-of-append-when-consp",
            "associativity-of-append",
        ] {
            let (index, enc) = env.axiom(name).unwrap();
            let model = match &env.axioms[index].discharge {
                Discharge::ModelEq(model) => {
                    assert_eq!(model.concl(), &model_eq_target(&env, enc).unwrap());
                    model
                }
                Discharge::ModelImplies(model) => {
                    assert_eq!(model.concl(), &model_implies_target(&env, enc).unwrap());
                    model
                }
                _ => panic!("{name} has the wrong discharge"),
            };
            assert!(model.hyps().is_empty(), "{name} must be closed");
            let fact = append_fact(&env, name).unwrap();
            assert!(fact.thm.hyps().is_empty(), "{name} fact must be closed");
        }
    }

    #[test]
    fn append_count_bridge_is_closed_and_matches_exact_upstream_targets() {
        let env = with_fixers(&with_ordinals(&s6_env().unwrap()).unwrap()).unwrap();
        let env = with_acl2_count(&env).unwrap();
        let env = with_append(&env).unwrap();
        let env = with_append_count_laws(&env).unwrap();
        for name in ["acl2-count-of-append-strict", "append-nonempty-list"] {
            let (index, enc) = env.axiom(name).unwrap();
            let Discharge::ModelImplies(model) = &env.axioms[index].discharge else {
                panic!("{name} must use checked ModelImplies replay");
            };
            assert!(model.hyps().is_empty());
            assert_eq!(model.concl(), &model_implies_target(&env, enc).unwrap());
            let fact = append_fact(&env, name).unwrap();
            assert!(fact.thm.hyps().is_empty());
        }
    }
}

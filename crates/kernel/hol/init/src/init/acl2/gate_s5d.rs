//! **S5d — THE G4 GATE** (design `notes/vibes/lisp/acl2-s5-design.md`
//! §11 №13–16): `ACL2-COUNT` admitted through the plain S4 template on
//! the ordinal env, its `NATP`/`O-P` totality and `O<`-decrease
//! obligations **derived in the object logic** (Hilbert-move scripts
//! over the S5 axiom pack), and app-assoc **re-derived by measured
//! induction** through the IND-ORD clause — cross-checked against the
//! committed S6 structural-induction route on the same env. Test-only
//! (`#[cfg(test)]` in `mod.rs`); the shared script scaffolding lives in
//! [`super::hilbert::scripts`].

use std::sync::LazyLock;

use covalence_core::Term;
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_int;
use smol_str::SmolStr;

use crate::init::acl2::defun::{Acl2Session, DefunSpec, admit_defun};
use crate::init::acl2::derivable::{
    Acl2Env, derivable, derive_axiom, derive_comp_folded, derive_ind, derive_ind_ord, derive_inst,
    finite_sigma, ground_env, s6_env, soundness, subst_ground, sym_lit_of, transport_equal_open,
    uncons,
};
use crate::init::acl2::hilbert::scripts::{
    B, app_assoc_base, app_assoc_step, app_assoc_terms, app_spec,
};
use crate::init::acl2::hilbert::{
    Fact, axiom_inst, cong_impl, def_inst, derive_under, eq_refl, equal_parts, implies_parts,
};
use crate::init::acl2::ordinal::{ordinals, with_ordinals};
use crate::init::acl2::term::Terms;
use crate::init::ext::{TermExt, ThmExt};

/// Assert a closed theorem with an exact conclusion.
fn check(thm: &Thm, expected: &Term) {
    assert!(thm.hyps().is_empty(), "must be closed: {thm}");
    assert_eq!(thm.concl(), expected);
}

// ============================================================================
// The G4 session: ordinal env + ACL2-COUNT + APP
// ============================================================================

/// `(defun acl2-count (x) (if (consp x) (binary-+ '1 (binary-+
/// (acl2-count (car x)) (acl2-count (cdr x)))) (if (integerp x)
/// (if (< x '0) (unary-- x) x) '0)))` — the §11 №14 spec (tree
/// recursion, exactly the S4 template).
fn count_spec(tm: &Terms) -> DefunSpec {
    let x = tm.sym(b"X").unwrap();
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64)).unwrap()).unwrap();
    let q1 = tm.quote(&tm.th.aint_at(&mk_int(1i64)).unwrap()).unwrap();
    let cnt = |v: &Term| tm.app(b"ACL2-COUNT", std::slice::from_ref(v)).unwrap();
    let step = tm
        .app(
            b"BINARY-+",
            &[
                q1,
                tm.app(
                    b"BINARY-+",
                    &[
                        cnt(&tm.app(b"CAR", &[x.clone()]).unwrap()),
                        cnt(&tm.app(b"CDR", &[x.clone()]).unwrap()),
                    ],
                )
                .unwrap(),
            ],
        )
        .unwrap();
    let inner = tm
        .mk_if(
            &tm.app(b"<", &[x.clone(), q0.clone()]).unwrap(),
            &tm.app(b"UNARY--", &[x.clone()]).unwrap(),
            &x,
        )
        .unwrap();
    let base = tm
        .mk_if(&tm.app(b"INTEGERP", &[x.clone()]).unwrap(), &inner, &q0)
        .unwrap();
    let body = tm
        .mk_if(&tm.app(b"CONSP", &[x.clone()]).unwrap(), &step, &base)
        .unwrap();
    DefunSpec {
        name: SmolStr::new("ACL2-COUNT"),
        formals: vec![SmolStr::new("X")],
        body,
        rec_formal: Some(0),
    }
}

/// The gate session — ordinal env (`with_ordinals(s6_env)`, IND-ORD
/// registered) + `ACL2-COUNT` + `APP`, its soundness proved once.
pub(crate) fn g4_session() -> &'static Acl2Session {
    static G4: LazyLock<std::result::Result<Acl2Session, String>> = LazyLock::new(|| {
        let e6 = s6_env().map_err(|e| e.to_string())?;
        let env = with_ordinals(&e6).map_err(|e| e.to_string())?;
        let sess = Acl2Session::new(env);
        let cspec = count_spec(&sess.env().tm);
        let sess = sess.admit_defun(&cspec).map_err(|e| e.to_string())?;
        let aspec = app_spec(&sess.env().tm);
        sess.admit_defun(&aspec).map_err(|e| e.to_string())
    });
    G4.as_ref().unwrap()
}

// ============================================================================
// Script-level helpers over the S5 axiom pack
// ============================================================================

/// Parse `⌜(IF c y z)⌝`.
fn if_parts(env: &Acl2Env, t: &Term) -> (Term, Term, Term) {
    let tm = &*env.tm;
    let (h, tail) = uncons(tm, t).unwrap();
    assert_eq!(sym_lit_of(tm, &h).as_deref(), Some(b"IF".as_slice()));
    let (c, rest) = uncons(tm, &tail).unwrap();
    let (y, rest) = uncons(tm, &rest).unwrap();
    let (z, rest) = uncons(tm, &rest).unwrap();
    assert_eq!(rest, tm.th.nil);
    (c, y, z)
}

/// Close a script: `⊢ D ⌜(IMPLIES h₁ (… (IMPLIES hₖ goal)))⌝` as a
/// [`Fact`] (statement re-checked against `derivable`).
fn under(env: &Acl2Env, hyps: &[Term], b: B, goal_line: usize) -> Fact {
    let goal = b.phis[goal_line].clone();
    let thm = derive_under(env, hyps, &b.st, &goal).unwrap();
    let mut phi = goal;
    for h in hyps.iter().rev() {
        phi = env.tm.mk_implies(h, &phi).unwrap();
    }
    assert_eq!(thm.concl(), &derivable(env, &phi).unwrap());
    Fact { phi, thm }
}

/// The classical case split (the S5 `cases` row): `⌜p⌝` from
/// `pos : ⊢ D ⌜(IMPLIES q p)⌝` and `neg : ⊢ D ⌜(IMPLIES (EQUAL q 'NIL) p)⌝`.
fn by_cases(env: &Acl2Env, pos: &Fact, neg: &Fact) -> Fact {
    let (q, p) = implies_parts(env, &pos.phi).unwrap();
    let cs = axiom_inst(env, "cases", &[(b"X", q), (b"Y", p)]).unwrap();
    crate::init::acl2::hilbert::mp(
        env,
        &crate::init::acl2::hilbert::mp(env, &cs, pos).unwrap(),
        neg,
    )
    .unwrap()
}

/// INST a derived [`Fact`] at a finite substitution (the `axiom_inst`
/// pattern for non-axiom derivations — every derivable formula
/// instantiates).
fn fact_inst(env: &Acl2Env, f: &Fact, binds: &[(&[u8], Term)]) -> Fact {
    let s = finite_sigma(&env.tm, binds).unwrap();
    let raw = derive_inst(env, &f.phi, &s, f.thm.clone()).unwrap();
    let fold = subst_ground(&env.tm, &f.phi, &s).unwrap();
    let phi = fold.concl().as_eq().unwrap().1.clone();
    Fact {
        phi,
        thm: raw.rewrite(&fold).unwrap(),
    }
}

/// Line `(EQUAL e 'T)` → line `e` (equal-symm + equal-mp + truth).
fn detach(b: &mut B, l_eq: usize) -> usize {
    let l_sym = b.symm_u(l_eq); // (EQUAL 'T e)
    let (qt, e) = equal_parts(b.env, &b.phis[l_sym]).unwrap();
    let emp = axiom_inst(b.env, "equal-mp", &[(b"X", qt), (b"Y", e)]).unwrap();
    let l_emp = b.fact(emp);
    let l_imp = b.mp(l_emp, l_sym); // (IMPLIES 'T e)
    let l_t = b.fact(axiom_inst(b.env, "truth", &[]).unwrap());
    b.mp(l_imp, l_t)
}

/// Lines `(EQUAL p q)` + `p` → line `q` (equal-mp + two MPs).
fn eq_mp_u(b: &mut B, l_eq: usize, l_p: usize) -> usize {
    let (p, q) = equal_parts(b.env, &b.phis[l_eq]).unwrap();
    let emp = axiom_inst(b.env, "equal-mp", &[(b"X", p), (b"Y", q)]).unwrap();
    let l_emp = b.fact(emp);
    let l_i = b.mp(l_emp, l_eq);
    b.mp(l_i, l_p)
}

/// Lines `p` + `(EQUAL p 'NIL)` → line `y` (contra + two MPs).
fn contra_u(b: &mut B, l_p: usize, l_pn: usize, y: &Term) -> usize {
    let p = b.phis[l_p].clone();
    let ct = axiom_inst(b.env, "contra", &[(b"X", p), (b"Y", y.clone())]).unwrap();
    let l_ct = b.fact(ct);
    let l_1 = b.mp(l_ct, l_p);
    b.mp(l_1, l_pn)
}

/// Unary-row congruence: line `(EQUAL x y)` → line `(EQUAL (F x) (F y))`.
fn cong1_u(b: &mut B, sym: &str, l_eq: usize) -> usize {
    let (x, y) = equal_parts(b.env, &b.phis[l_eq]).unwrap();
    let ci = cong_impl(b.env, sym, &[(x, y)]).unwrap();
    let l_ci = b.fact(ci);
    b.mp(l_ci, l_eq)
}

/// `if-true` fired by line `l_c` (`c` holds): line
/// `(EQUAL (IF c y z) y)` for the encoding `ifenc = (IF c y z)`.
fn if_true_u(b: &mut B, ifenc: &Term, l_c: usize) -> usize {
    let (c, y, z) = if_parts(b.env, ifenc);
    let ax = axiom_inst(b.env, "if-true", &[(b"X", c), (b"Y", y), (b"Z", z)]).unwrap();
    let l = b.fact(ax);
    b.mp(l, l_c)
}

/// `if-false` fired by line `l_cn` (`(EQUAL c 'NIL)`): line
/// `(EQUAL (IF c y z) z)`.
fn if_false_u(b: &mut B, ifenc: &Term, l_cn: usize) -> usize {
    let (c, y, z) = if_parts(b.env, ifenc);
    let ax = axiom_inst(b.env, "if-false", &[(b"X", c), (b"Y", y), (b"Z", z)]).unwrap();
    let l = b.fact(ax);
    b.mp(l, l_cn)
}

/// `(NATP u)` from lines `(INTEGERP u)` and `(EQUAL (< u '0) 'NIL)`
/// (the NATP Def chain + detach).
fn natp_intro_u(b: &mut B, u: &Term, l_iu: usize, l_ltn: usize) -> usize {
    let def = def_inst(b.env, "NATP", &[(b"X", u.clone())]).unwrap();
    let (_, body) = equal_parts(b.env, &def.phi).unwrap();
    let l_def = b.fact(def);
    let l_1 = if_true_u(b, &body, l_iu); // (EQUAL body inner)
    let l_c1 = b.trans_u(l_def, l_1); // (EQUAL (NATP u) inner)
    let (_, inner, _) = if_parts(b.env, &body);
    let l_2 = if_false_u(b, &inner, l_ltn); // (EQUAL inner 'T)
    let l_c2 = b.trans_u(l_c1, l_2); // (EQUAL (NATP u) 'T)
    detach(b, l_c2)
}

/// From lines `(EQUAL w' w)` and `(NATP w)`, the line `(NATP w')`
/// (CongImpl(NATP) + symm + equal-mp).
fn transfer_natp(b: &mut B, l_eq: usize, l_natp_w: usize) -> usize {
    let l_c = cong1_u(b, "NATP", l_eq); // (EQUAL (NATP w') (NATP w))
    let l_s = b.symm_u(l_c); // (EQUAL (NATP w) (NATP w'))
    eq_mp_u(b, l_s, l_natp_w)
}

// ============================================================================
// The NATP elimination lemmas (object-level, hyp-free)
// ============================================================================

/// `⊢ D ⌜(IMPLIES (NATP u) (EQUAL (< u '0) 'NIL))⌝` — cases on
/// `(INTEGERP u)` then `(< u '0)`; the contradictory arms explode
/// through the NATP Def + `contra`.
fn natp_nonneg_fact(env: &Acl2Env, u: &Term) -> Fact {
    let tm = &*env.tm;
    let qnil = tm.quote(&tm.th.nil).unwrap();
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64)).unwrap()).unwrap();
    let natpu = tm.app(b"NATP", std::slice::from_ref(u)).unwrap();
    let iu = tm.app(b"INTEGERP", std::slice::from_ref(u)).unwrap();
    let iun = tm.mk_equal(&iu, &qnil).unwrap();
    let lt = tm.app(b"<", &[u.clone(), q0]).unwrap();
    let ltn = tm.mk_equal(&lt, &qnil).unwrap();

    // (IMPLIES lt (IMPLIES iu (IMPLIES natpu ltn))): NATP Def fires to
    // 'NIL under lt — contradiction with natpu.
    let s_lt = {
        let hyps = [lt.clone(), iu.clone(), natpu.clone()];
        let mut b = B::new(env);
        let l_lt = b.hyp(0, &lt);
        let l_iu = b.hyp(1, &iu);
        let l_np = b.hyp(2, &natpu);
        let def = def_inst(env, "NATP", &[(b"X", u.clone())]).unwrap();
        let (_, body) = equal_parts(env, &def.phi).unwrap();
        let l_def = b.fact(def);
        let l_1 = if_true_u(&mut b, &body, l_iu);
        let l_c1 = b.trans_u(l_def, l_1); // (EQUAL (NATP u) inner)
        let (_, inner, _) = if_parts(env, &body);
        let l_2 = if_true_u(&mut b, &inner, l_lt); // (EQUAL inner 'NIL)
        let l_c2 = b.trans_u(l_c1, l_2); // (EQUAL (NATP u) 'NIL)
        let l_g = contra_u(&mut b, l_np, l_c2, &ltn);
        under(env, &hyps, b, l_g)
    };
    // (IMPLIES ltn (IMPLIES iu (IMPLIES natpu ltn))): the goal IS the
    // case hypothesis.
    let s_ltn = {
        let hyps = [ltn.clone(), iu.clone(), natpu.clone()];
        let mut b = B::new(env);
        let l = b.hyp(0, &ltn);
        under(env, &hyps, b, l)
    };
    let arm_iu = by_cases(env, &s_lt, &s_ltn); // (IMPLIES iu (IMPLIES natpu ltn))
    // (IMPLIES iun (IMPLIES natpu ltn)): NATP Def fires to 'NIL outright.
    let arm_iun = {
        let hyps = [iun.clone(), natpu.clone()];
        let mut b = B::new(env);
        let l_iun = b.hyp(0, &iun);
        let l_np = b.hyp(1, &natpu);
        let def = def_inst(env, "NATP", &[(b"X", u.clone())]).unwrap();
        let (_, body) = equal_parts(env, &def.phi).unwrap();
        let l_def = b.fact(def);
        let l_1 = if_false_u(&mut b, &body, l_iun);
        let l_c = b.trans_u(l_def, l_1); // (EQUAL (NATP u) 'NIL)
        let l_g = contra_u(&mut b, l_np, l_c, &ltn);
        under(env, &hyps, b, l_g)
    };
    by_cases(env, &arm_iu, &arm_iun)
}

/// `⊢ D ⌜(IMPLIES (NATP u) (INTEGERP u))⌝`.
fn natp_integerp_fact(env: &Acl2Env, u: &Term) -> Fact {
    let tm = &*env.tm;
    let qnil = tm.quote(&tm.th.nil).unwrap();
    let natpu = tm.app(b"NATP", std::slice::from_ref(u)).unwrap();
    let iu = tm.app(b"INTEGERP", std::slice::from_ref(u)).unwrap();
    let iun = tm.mk_equal(&iu, &qnil).unwrap();
    let pos = {
        let hyps = [iu.clone(), natpu.clone()];
        let mut b = B::new(env);
        let l = b.hyp(0, &iu);
        under(env, &hyps, b, l)
    };
    let neg = {
        let hyps = [iun.clone(), natpu.clone()];
        let mut b = B::new(env);
        let l_iun = b.hyp(0, &iun);
        let l_np = b.hyp(1, &natpu);
        let def = def_inst(env, "NATP", &[(b"X", u.clone())]).unwrap();
        let (_, body) = equal_parts(env, &def.phi).unwrap();
        let l_def = b.fact(def);
        let l_1 = if_false_u(&mut b, &body, l_iun);
        let l_c = b.trans_u(l_def, l_1);
        let l_g = contra_u(&mut b, l_np, l_c, &iu);
        under(env, &hyps, b, l_g)
    };
    by_cases(env, &pos, &neg)
}

/// `⊢ D ⌜(IMPLIES (NATP u) (EQUAL (CONSP u) 'NIL))⌝` (through
/// `integerp-not-consp`).
fn not_consp_of_natp(env: &Acl2Env, u: &Term) -> Fact {
    let tm = &*env.tm;
    let natpu = tm.app(b"NATP", std::slice::from_ref(u)).unwrap();
    let hyps = [natpu.clone()];
    let mut b = B::new(env);
    let l_np = b.hyp(0, &natpu);
    let l_ni = b.fact(natp_integerp_fact(env, u));
    let l_iu = b.mp(l_ni, l_np);
    let incp = axiom_inst(env, "integerp-not-consp", &[(b"X", u.clone())]).unwrap();
    let l_incp = b.fact(incp);
    let l_cn = b.mp(l_incp, l_iu);
    under(env, &hyps, b, l_cn)
}

// ============================================================================
// The ACL2-COUNT obligations (§11 №15)
// ============================================================================

/// The shared count terms over the gate env, read off the admitted row.
pub(crate) struct Ct {
    /// `(ACL2-COUNT X)`.
    pub(crate) cx: Term,
    /// `(BINARY-+ '1 (BINARY-+ a d))` — the cons-step value.
    pub(crate) s: Term,
    /// `(IF (INTEGERP X) (IF (< X '0) (UNARY-- X) X) '0)`.
    pub(crate) base0: Term,
    /// `(IF (< X '0) (UNARY-- X) X)`.
    pub(crate) inner0: Term,
    /// `(ACL2-COUNT (CAR X))` / `(ACL2-COUNT (CDR X))`.
    pub(crate) a: Term,
    pub(crate) d: Term,
    /// `(CONSP X)` and `(EQUAL (CONSP X) 'NIL)`.
    pub(crate) c: Term,
    pub(crate) g: Term,
    /// `(INTEGERP X)` / `(< X '0)`.
    pub(crate) iu: Term,
    pub(crate) lt: Term,
    /// The NATP goal `(NATP (ACL2-COUNT X))`.
    pub(crate) phi: Term,
}

pub(crate) fn count_terms(env: &Acl2Env) -> Ct {
    let tm = &*env.tm;
    let (_, u) = env.user("ACL2-COUNT").unwrap();
    let (cx, body) = equal_parts(env, &u.def_enc).unwrap();
    let (c, s, base0) = if_parts(env, &body);
    let (iu, inner0, _q0) = if_parts(env, &base0);
    let (lt, _negx, _x) = if_parts(env, &inner0);
    let g = tm.mk_equal(&c, &tm.quote(&tm.th.nil).unwrap()).unwrap();
    let x = tm.sym(b"X").unwrap();
    let cnt = |v: &Term| tm.app(b"ACL2-COUNT", std::slice::from_ref(v)).unwrap();
    let a = cnt(&tm.app(b"CAR", &[x.clone()]).unwrap());
    let d = cnt(&tm.app(b"CDR", &[x.clone()]).unwrap());
    let phi = tm.app(b"NATP", &[cx.clone()]).unwrap();
    Ct {
        cx,
        s,
        base0,
        inner0,
        a,
        d,
        c,
        g,
        iu,
        lt,
        phi,
    }
}

/// The count unfold: line `(EQUAL (ACL2-COUNT X) S)` (under a `(CONSP
/// X)` line) or `(EQUAL (ACL2-COUNT X) base0)` (under the negated
/// guard).
fn count_unfold(b: &mut B, l_guard: usize, cons_side: bool) -> usize {
    let def = def_inst(b.env, "ACL2-COUNT", &[]).unwrap();
    let (_, body) = equal_parts(b.env, &def.phi).unwrap();
    let l_def = b.fact(def);
    let l_if = if cons_side {
        if_true_u(b, &body, l_guard)
    } else {
        if_false_u(b, &body, l_guard)
    };
    b.trans_u(l_def, l_if)
}

/// `⊢ D ⌜(EQUAL (NATP '0) 'T)⌝` — the NATP computation clause folded
/// by `ord_fold`.
fn natp_zero_fact(env: &Acl2Env) -> Fact {
    let o = ordinals().unwrap();
    let tm = &*env.tm;
    let a0 = tm.th.aint_at(&mk_int(0i64)).unwrap();
    let k = env.row("NATP").unwrap();
    let ground = o
        .ord_fold(&o.natp.clone().apply(a0.clone()).unwrap())
        .unwrap(); // ⊢ natp (aint 0) = t
    let thm = derive_comp_folded(env, k, std::slice::from_ref(&a0), &ground).unwrap();
    let phi = tm
        .mk_equal(
            &tm.app(b"NATP", &[tm.quote(&a0).unwrap()]).unwrap(),
            &tm.quote(&tm.pr.t).unwrap(),
        )
        .unwrap();
    assert_eq!(thm.concl(), &derivable(env, &phi).unwrap());
    Fact { phi, thm }
}

/// `⊢ D ⌜(EQUAL (< '1 '0) 'NIL)⌝` — the `<` computation clause folded
/// by `lt_lit`.
fn lt10_fact(env: &Acl2Env) -> Fact {
    let tm = &*env.tm;
    let a1 = tm.th.aint_at(&mk_int(1i64)).unwrap();
    let a0 = tm.th.aint_at(&mk_int(0i64)).unwrap();
    let k = env.row("<").unwrap();
    let thm = derive_comp_folded(
        env,
        k,
        &[a1.clone(), a0.clone()],
        &tm.pr.lt_lit(1, 0).unwrap(),
    )
    .unwrap();
    let phi = tm
        .mk_equal(
            &tm.app(b"<", &[tm.quote(&a1).unwrap(), tm.quote(&a0).unwrap()])
                .unwrap(),
            &tm.quote(&tm.th.nil).unwrap(),
        )
        .unwrap();
    assert_eq!(thm.concl(), &derivable(env, &phi).unwrap());
    Fact { phi, thm }
}

/// The IND base premise `⊢ D ⌜(IMPLIES (EQUAL (CONSP X) 'NIL) (NATP
/// (ACL2-COUNT X)))⌝` — cases on `(INTEGERP X)`, then `(< X '0)`;
/// the three branches land `(NATP w)` for `w = (UNARY-- X) | X | '0`
/// and transfer back along the count unfold.
fn count_natp_base(env: &Acl2Env, ct: &Ct) -> Fact {
    let tm = &*env.tm;
    let qnil = tm.quote(&tm.th.nil).unwrap();
    let x = tm.sym(b"X").unwrap();
    let iun = tm.mk_equal(&ct.iu, &qnil).unwrap();
    let ltn = tm.mk_equal(&ct.lt, &qnil).unwrap();
    let negx = tm.app(b"UNARY--", &[x.clone()]).unwrap();

    // (IMPLIES lt (IMPLIES iu (IMPLIES g phi))): count = (UNARY-- X);
    // integerp-neg + neg-nonneg give its NATP.
    let s_lt = {
        let hyps = [ct.lt.clone(), ct.iu.clone(), ct.g.clone()];
        let mut b = B::new(env);
        let l_lt = b.hyp(0, &ct.lt);
        let l_iu = b.hyp(1, &ct.iu);
        let l_g = b.hyp(2, &ct.g);
        let l_ceq = count_unfold(&mut b, l_g, false); // (EQUAL CX base0)
        let l_b1 = if_true_u(&mut b, &ct.base0, l_iu); // (EQUAL base0 inner0)
        let l_c1 = b.trans_u(l_ceq, l_b1);
        let l_b2 = if_true_u(&mut b, &ct.inner0, l_lt); // (EQUAL inner0 (UNARY-- X))
        let l_c2 = b.trans_u(l_c1, l_b2); // (EQUAL CX (UNARY-- X))
        let l_ineg = b.fact(axiom_inst(env, "integerp-neg", &[(b"A", x.clone())]).unwrap());
        let nn = axiom_inst(env, "neg-nonneg", &[(b"A", x.clone())]).unwrap();
        let l_nn = b.fact(nn);
        let l_ltn_neg = b.mp(l_nn, l_lt); // (EQUAL (< (UNARY-- X) '0) 'NIL)
        let l_natp = natp_intro_u(&mut b, &negx, l_ineg, l_ltn_neg);
        let l_goal = transfer_natp(&mut b, l_c2, l_natp);
        under(env, &hyps, b, l_goal)
    };
    // (IMPLIES ltn (IMPLIES iu (IMPLIES g phi))): count = X itself.
    let s_ltn = {
        let hyps = [ltn.clone(), ct.iu.clone(), ct.g.clone()];
        let mut b = B::new(env);
        let l_ltn = b.hyp(0, &ltn);
        let l_iu = b.hyp(1, &ct.iu);
        let l_g = b.hyp(2, &ct.g);
        let l_ceq = count_unfold(&mut b, l_g, false);
        let l_b1 = if_true_u(&mut b, &ct.base0, l_iu);
        let l_c1 = b.trans_u(l_ceq, l_b1);
        let l_b2 = if_false_u(&mut b, &ct.inner0, l_ltn); // (EQUAL inner0 X)
        let l_c2 = b.trans_u(l_c1, l_b2); // (EQUAL CX X)
        let l_natp = natp_intro_u(&mut b, &x, l_iu, l_ltn);
        let l_goal = transfer_natp(&mut b, l_c2, l_natp);
        under(env, &hyps, b, l_goal)
    };
    let arm_iu = by_cases(env, &s_lt, &s_ltn); // (IMPLIES iu (IMPLIES g phi))
    // (IMPLIES iun (IMPLIES g phi)): count = '0, ground computation.
    let arm_iun = {
        let hyps = [iun.clone(), ct.g.clone()];
        let mut b = B::new(env);
        let l_iun = b.hyp(0, &iun);
        let l_g = b.hyp(1, &ct.g);
        let l_ceq = count_unfold(&mut b, l_g, false);
        let l_b1 = if_false_u(&mut b, &ct.base0, l_iun); // (EQUAL base0 '0)
        let l_c = b.trans_u(l_ceq, l_b1); // (EQUAL CX '0)
        let l_nz = b.fact(natp_zero_fact(env)); // (EQUAL (NATP '0) 'T)
        let l_n0 = detach(&mut b, l_nz); // (NATP '0)
        let l_goal = transfer_natp(&mut b, l_c, l_n0);
        under(env, &hyps, b, l_goal)
    };
    by_cases(env, &arm_iu, &arm_iun) // (IMPLIES g phi)
}

/// The IND step premise `⊢ D ⌜(IMPLIES (CONSP X) (IMPLIES (NATP a)
/// (IMPLIES (NATP d) (NATP (ACL2-COUNT X)))))⌝` — `integerp-plus` +
/// `plus-nonneg` twice through the NATP Def, IHs woven by the
/// elimination lemmas.
fn count_natp_step(env: &Acl2Env, ct: &Ct) -> Fact {
    let tm = &*env.tm;
    let q1 = tm.quote(&tm.th.aint_at(&mk_int(1i64)).unwrap()).unwrap();
    let ad = tm.app(b"BINARY-+", &[ct.a.clone(), ct.d.clone()]).unwrap();
    // The IH formulas exactly as derive_ind folds them.
    let ih_at = |proj: &[u8]| {
        let e = tm.app(proj, &[tm.sym(b"X").unwrap()]).unwrap();
        let s = finite_sigma(tm, &[(b"X", e)]).unwrap();
        subst_ground(tm, &ct.phi, &s)
            .unwrap()
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone()
    };
    let iha = ih_at(b"CAR"); // (NATP (ACL2-COUNT (CAR X)))
    let ihd = ih_at(b"CDR");
    let hyps = [ct.c.clone(), iha.clone(), ihd.clone()];
    let mut b = B::new(env);
    let l_c = b.hyp(0, &ct.c);
    let l_iha = b.hyp(1, &iha);
    let l_ihd = b.hyp(2, &ihd);
    let l_cx = count_unfold(&mut b, l_c, true); // (EQUAL CX S)
    // (INTEGERP S) outright.
    let l_ia = b.fact(
        axiom_inst(
            env,
            "integerp-plus",
            &[(b"A", q1.clone()), (b"B", ad.clone())],
        )
        .unwrap(),
    );
    // (EQUAL (< a '0) 'NIL) / (EQUAL (< d '0) 'NIL) from the IHs.
    let l_na_f = b.fact(natp_nonneg_fact(env, &ct.a));
    let l_na = b.mp(l_na_f, l_iha);
    let l_nd_f = b.fact(natp_nonneg_fact(env, &ct.d));
    let l_nd = b.mp(l_nd_f, l_ihd);
    // plus-nonneg twice: (EQUAL (< (BINARY-+ a d) '0) 'NIL), then with '1.
    let pn1 = axiom_inst(
        env,
        "plus-nonneg",
        &[(b"A", ct.a.clone()), (b"B", ct.d.clone())],
    )
    .unwrap();
    let l_pn1 = b.fact(pn1);
    let l_m = b.mp(l_pn1, l_na);
    let l_ad = b.mp(l_m, l_nd);
    let l_lt10 = b.fact(lt10_fact(env));
    let pn2 = axiom_inst(env, "plus-nonneg", &[(b"A", q1), (b"B", ad)]).unwrap();
    let l_pn2 = b.fact(pn2);
    let l_m2 = b.mp(l_pn2, l_lt10);
    let l_s0 = b.mp(l_m2, l_ad); // (EQUAL (< S '0) 'NIL)
    let l_natp_s = natp_intro_u(&mut b, &ct.s, l_ia, l_s0);
    let l_goal = transfer_natp(&mut b, l_cx, l_natp_s);
    under(env, &hyps, b, l_goal)
}

/// `⊢ D ⌜(IMPLIES (NATP X) (O-P X))⌝` — cases on `(CONSP X)`: the cons
/// arm contradicts through `integerp-not-consp`; the atom arm is the
/// O-P Def's `(NATP X)` branch.
fn natp_op_fact(env: &Acl2Env) -> Fact {
    let tm = &*env.tm;
    let qnil = tm.quote(&tm.th.nil).unwrap();
    let x = tm.sym(b"X").unwrap();
    let natpx = tm.app(b"NATP", &[x.clone()]).unwrap();
    let opx = tm.app(b"O-P", &[x.clone()]).unwrap();
    let cx = tm.app(b"CONSP", &[x.clone()]).unwrap();
    let cn = tm.mk_equal(&cx, &qnil).unwrap();
    let pos = {
        let hyps = [cx.clone(), natpx.clone()];
        let mut b = B::new(env);
        let l_c = b.hyp(0, &cx);
        let l_np = b.hyp(1, &natpx);
        let l_ni = b.fact(natp_integerp_fact(env, &x));
        let l_iu = b.mp(l_ni, l_np);
        let l_incp = b.fact(axiom_inst(env, "integerp-not-consp", &[]).unwrap());
        let l_cn = b.mp(l_incp, l_iu);
        let l_goal = contra_u(&mut b, l_c, l_cn, &opx);
        under(env, &hyps, b, l_goal)
    };
    let neg = {
        let hyps = [cn.clone(), natpx.clone()];
        let mut b = B::new(env);
        let l_cn = b.hyp(0, &cn);
        let l_np = b.hyp(1, &natpx);
        let def = def_inst(env, "O-P", &[]).unwrap();
        let (_, opbody) = equal_parts(env, &def.phi).unwrap();
        let l_def = b.fact(def);
        let l_1 = if_false_u(&mut b, &opbody, l_cn); // (EQUAL op_body (NATP X))
        let l_c1 = b.trans_u(l_def, l_1); // (EQUAL (O-P X) (NATP X))
        let l_s = b.symm_u(l_c1);
        let l_goal = eq_mp_u(&mut b, l_s, l_np);
        under(env, &hyps, b, l_goal)
    };
    by_cases(env, &pos, &neg)
}

/// The three §11 №15 obligation derivations, computed once.
pub(crate) struct Obligations {
    /// `⊢ D ⌜(NATP (ACL2-COUNT X))⌝` (via S6 IND).
    pub(crate) d_natp: Fact,
    /// `⊢ D ⌜(O-P (ACL2-COUNT X))⌝` (via the `natp_op` object lemma).
    pub(crate) d_opm: Fact,
    /// `⊢ D ⌜(IMPLIES (CONSP X) (O< (ACL2-COUNT (CDR X)) (ACL2-COUNT X)))⌝`.
    pub(crate) d_dec: Fact,
}

pub(crate) fn obligations() -> &'static Obligations {
    static OBL: LazyLock<std::result::Result<Obligations, String>> = LazyLock::new(|| {
        let env = g4_session().env();
        let ct = count_terms(env);
        // NATP totality by S6 structural induction.
        let base = count_natp_base(env, &ct);
        let step = count_natp_step(env, &ct);
        let d_natp_thm =
            derive_ind(env, &ct.phi, b"X", base.thm, step.thm).map_err(|e| e.to_string())?;
        let d_natp = Fact {
            phi: ct.phi.clone(),
            thm: d_natp_thm,
        };
        // O-P totality via the natp→o-p object lemma, INSTed at CX.
        let lemma = natp_op_fact(env);
        let at_cx = fact_inst(env, &lemma, &[(b"X", ct.cx.clone())]);
        let d_opm =
            crate::init::acl2::hilbert::mp(env, &at_cx, &d_natp).map_err(|e| e.to_string())?;
        // O< decrease: unfold O< at two non-conses to the `<` branch,
        // close by lt-plus-one.
        let d_dec = {
            let tm = &*env.tm;
            let natp_a = fact_inst(
                env,
                &d_natp,
                &[(b"X", tm.app(b"CAR", &[tm.sym(b"X").unwrap()]).unwrap())],
            );
            let natp_d = fact_inst(
                env,
                &d_natp,
                &[(b"X", tm.app(b"CDR", &[tm.sym(b"X").unwrap()]).unwrap())],
            );
            assert_eq!(natp_a.phi, tm.app(b"NATP", &[ct.a.clone()]).unwrap());
            assert_eq!(natp_d.phi, tm.app(b"NATP", &[ct.d.clone()]).unwrap());
            let ncd = crate::init::acl2::hilbert::mp(env, &not_consp_of_natp(env, &ct.d), &natp_d)
                .map_err(|e| e.to_string())?; // (EQUAL (CONSP d) 'NIL)
            let ncx = crate::init::acl2::hilbert::mp(env, &not_consp_of_natp(env, &ct.cx), &d_natp)
                .map_err(|e| e.to_string())?; // (EQUAL (CONSP CX) 'NIL)
            let hyps = [ct.c.clone()];
            let mut b = B::new(env);
            let l_c = b.hyp(0, &ct.c);
            let l_cx = count_unfold(&mut b, l_c, true); // (EQUAL CX S)
            let defo = def_inst(env, "O<", &[(b"X", ct.d.clone()), (b"Y", ct.cx.clone())]).unwrap();
            let (_, oltbody) = equal_parts(env, &defo.phi).unwrap();
            let l_defo = b.fact(defo);
            let l_ncd = b.fact(ncd);
            let l_1 = if_false_u(&mut b, &oltbody, l_ncd); // (EQUAL oltbody fin_arm)
            let l_c1 = b.trans_u(l_defo, l_1);
            let (_, _, fin_arm) = if_parts(env, &oltbody);
            let l_ncx = b.fact(ncx);
            let l_2 = if_false_u(&mut b, &fin_arm, l_ncx); // (EQUAL fin_arm (< d CX))
            let l_c2 = b.trans_u(l_c1, l_2); // (EQUAL (O< d CX) (< d CX))
            // (< d S) by lt-plus-one under (EQUAL (< a '0) 'NIL).
            let l_naf = b.fact(natp_nonneg_fact(env, &ct.a));
            let l_na_h = b.fact(natp_a);
            let l_na = b.mp(l_naf, l_na_h);
            let lpo = axiom_inst(
                env,
                "lt-plus-one",
                &[(b"A", ct.a.clone()), (b"B", ct.d.clone())],
            )
            .unwrap();
            let l_lpo = b.fact(lpo);
            let l_lds = b.mp(l_lpo, l_na); // (< d S)
            // Transfer (< d S) to (< d CX) along (EQUAL S CX).
            let l_scx = b.symm_u(l_cx); // (EQUAL S CX)
            let ci = cong_impl(
                env,
                "<",
                &[(ct.d.clone(), ct.d.clone()), (ct.s.clone(), ct.cx.clone())],
            )
            .unwrap();
            let l_ci = b.fact(ci);
            let l_rd = b.fact(eq_refl(env, &ct.d).unwrap());
            let l_m1 = b.mp(l_ci, l_rd);
            let l_eq_lt = b.mp(l_m1, l_scx); // (EQUAL (< d S) (< d CX))
            let l_lt = eq_mp_u(&mut b, l_eq_lt, l_lds); // (< d CX)
            // Back through (EQUAL (O< d CX) (< d CX)).
            let l_s2 = b.symm_u(l_c2);
            let l_goal = eq_mp_u(&mut b, l_s2, l_lt); // (O< d CX)
            under(env, &hyps, b, l_goal)
        };
        Ok(Obligations {
            d_natp,
            d_opm,
            d_dec,
        })
    });
    OBL.as_ref().unwrap()
}

// ============================================================================
// The gates
// ============================================================================

/// **G4 №14 — `ACL2-COUNT` admits** through the plain S4 tree-recursion
/// template on the ordinal env (95-clause layout), with the exact Def
/// clause; re-admission collides.
#[test]
fn t_acl2_count_admits() {
    use crate::init::acl2::derivable::{ClauseKind, derive_def};
    let sess = g4_session();
    let env = sess.env();
    // Layout: ordinal 87 + 2 defuns × (3 row clauses + 1 Def) = 95.
    assert_eq!(env.rows.len(), 20);
    assert_eq!(env.users.len(), 9);
    assert_eq!(env.ind_ord, vec![1]);
    assert_eq!(env.n_clauses(), 95);
    assert_eq!(env.clause_index(ClauseKind::IndOrd(0)), 94);

    let (j, u) = env.user("ACL2-COUNT").unwrap();
    assert_eq!(u.rec_formal, Some(0));
    // The Def clause encoding is exactly the spec body.
    let spec = count_spec(&env.tm);
    let want_enc = env
        .tm
        .mk_equal(
            &env.tm
                .app(b"ACL2-COUNT", &[env.tm.sym(b"X").unwrap()])
                .unwrap(),
            &spec.body,
        )
        .unwrap();
    assert_eq!(u.def_enc, want_enc);
    let der = derive_def(env, j).unwrap();
    check(&der, &derivable(env, &want_enc).unwrap());

    // Re-admission is a name collision (nothing minted).
    assert!(admit_defun(env, &count_spec(&env.tm)).is_err());
}

/// **G4 №15 — the ACL2-COUNT obligations**, exact `Derivable`
/// statements: `(NATP (ACL2-COUNT X))` (S6 IND over the S5 pack),
/// `(O-P (ACL2-COUNT X))` (the natp→o-p object lemma), and the guarded
/// `O<`-decrease along `(CDR X)`.
#[test]
fn t_count_obligations() {
    let sess = g4_session();
    let env = sess.env();
    let tm = &*env.tm;
    let ct = count_terms(env);
    let obl = obligations();

    check(&obl.d_natp.thm, &derivable(env, &ct.phi).unwrap());

    let opm = tm.app(b"O-P", &[ct.cx.clone()]).unwrap();
    assert_eq!(obl.d_opm.phi, opm);
    check(&obl.d_opm.thm, &derivable(env, &opm).unwrap());

    let dec = tm
        .mk_implies(
            &ct.c,
            &tm.app(b"O<", &[ct.d.clone(), ct.cx.clone()]).unwrap(),
        )
        .unwrap();
    assert_eq!(obl.d_dec.phi, dec);
    check(&obl.d_dec.thm, &derivable(env, &dec).unwrap());
}

/// **G4 №16 — THE GATE: app-assoc by measured induction.**
/// `derive_ind_ord` at `m := (ACL2-COUNT X)`, `q := (CONSP X)`,
/// `t₁ := (CDR X)` with the committed S6 hilbert scripts (car-IH
/// dropped), projected through the 95-clause soundness, transported to
/// the closed base-HOL equation — and cross-checked against the
/// committed S6 structural-IND route on the *same* env (same model
/// constant, exact conclusion equality). Plus №13's kernel-level
/// negative controls.
#[test]
fn t_app_assoc_by_measure() {
    let sess = g4_session();
    let env = sess.env();
    let tm = &*env.tm;
    let ct = count_terms(env);
    let obl = obligations();
    let t = app_assoc_terms(env);
    let cdr_x = tm.app(b"CDR", &[tm.sym(b"X").unwrap()]).unwrap();

    // Premises: the committed scripts, car-IH dropped in the step.
    let base = app_assoc_base(env, &t);
    let step1 = app_assoc_step(env, &t, false);
    let step1_phi = tm
        .mk_implies(&t.c, &tm.mk_implies(&t.ihcdr, &t.phi).unwrap())
        .unwrap();
    check(&step1, &derivable(env, &step1_phi).unwrap());

    // IND-ORD: ⊢ Derivable ⌜φ⌝ by measure (ACL2-COUNT X).
    let der = derive_ind_ord(
        env,
        &t.phi,
        b"X",
        &ct.cx,
        &ct.c,
        std::slice::from_ref(&cdr_x),
        obl.d_opm.thm.clone(),
        vec![obl.d_dec.thm.clone()],
        base.clone(),
        step1.clone(),
    )
    .unwrap();
    check(&der, &derivable(env, &t.phi).unwrap());

    // Project + open transport: the closed base-HOL model equation.
    let projected = sess.project(&t.phi, der).unwrap();
    let final_thm =
        transport_equal_open(env, &projected, &[(b"X", "x"), (b"Y", "y"), (b"Z", "z")]).unwrap();
    let (_, u) = env.user("APP").unwrap();
    let a = tm.th.ty.clone();
    let (x, y, z) = (
        Term::free("x", a.clone()),
        Term::free("y", a.clone()),
        Term::free("z", a.clone()),
    );
    let ap = |p: &Term, q: &Term| {
        u.model
            .clone()
            .apply(p.clone())
            .unwrap()
            .apply(q.clone())
            .unwrap()
    };
    let expected = ap(&ap(&x, &y), &z)
        .equals(ap(&x, &ap(&y, &z)))
        .unwrap()
        .forall("z", a.clone())
        .unwrap()
        .forall("y", a.clone())
        .unwrap()
        .forall("x", a.clone())
        .unwrap();
    check(&final_thm, &expected);

    // Cross-check: the committed S6 structural-IND route on the SAME
    // env (3-hypothesis step script) transports to the exact same
    // conclusion.
    let step3 = app_assoc_step(env, &t, true);
    let der6 = derive_ind(env, &t.phi, b"X", base.clone(), step3).unwrap();
    let proj6 = sess.project(&t.phi, der6).unwrap();
    let thm6 = transport_equal_open(env, &proj6, &[(b"X", "x"), (b"Y", "y"), (b"Z", "z")]).unwrap();
    assert!(thm6.hyps().is_empty());
    assert_eq!(final_thm.concl(), thm6.concl());

    // №13 negative controls (each errors at the kernel; nothing minted).
    // (a) Swapped base/step.
    assert!(
        derive_ind_ord(
            env,
            &t.phi,
            b"X",
            &ct.cx,
            &ct.c,
            std::slice::from_ref(&cdr_x),
            obl.d_opm.thm.clone(),
            vec![obl.d_dec.thm.clone()],
            step1.clone(),
            base.clone(),
        )
        .is_err()
    );
    // (b) A decrease premise of the wrong statement (the O-P premise in
    // the decrease slot).
    assert!(
        derive_ind_ord(
            env,
            &t.phi,
            b"X",
            &ct.cx,
            &ct.c,
            std::slice::from_ref(&cdr_x),
            obl.d_opm.thm.clone(),
            vec![obl.d_opm.thm.clone()],
            base.clone(),
            step1.clone(),
        )
        .is_err()
    );
    // (c) Non-decreasing descent t₁ := X — the supplied (CDR X)-decrease
    // premise cannot justify it.
    assert!(
        derive_ind_ord(
            env,
            &t.phi,
            b"X",
            &ct.cx,
            &ct.c,
            std::slice::from_ref(&tm.sym(b"X").unwrap()),
            obl.d_opm.thm.clone(),
            vec![obl.d_dec.thm.clone()],
            base.clone(),
            step1.clone(),
        )
        .is_err()
    );
    // (d) Wrong induction variable name.
    assert!(
        derive_ind_ord(
            env,
            &t.phi,
            b"Y",
            &ct.cx,
            &ct.c,
            std::slice::from_ref(&cdr_x),
            obl.d_opm.thm.clone(),
            vec![obl.d_dec.thm.clone()],
            base.clone(),
            step1.clone(),
        )
        .is_err()
    );
    // (e) Wrong shape (k = 2 is not registered).
    assert!(
        derive_ind_ord(
            env,
            &t.phi,
            b"X",
            &ct.cx,
            &ct.c,
            &[cdr_x.clone(), cdr_x.clone()],
            obl.d_opm.thm.clone(),
            vec![obl.d_dec.thm.clone(), obl.d_dec.thm.clone()],
            base,
            step1,
        )
        .is_err()
    );
}

/// **G4 №13 — env-level controls:** no IND-ORD clause outside ordinal
/// envs (`derive_ind_ord` on `s6_env` errors), and a bogus `ind_ord`
/// registration on a non-ordinal env **fails the soundness build**
/// (fail-safe: the discharge demands the ordinal `O-P`/`O<` rows —
/// no metatheorem is minted, so nothing projects).
#[test]
fn t_ind_ord_soundness_controls() {
    let e6 = s6_env().unwrap();
    let dummy = derive_axiom(&e6, "equal-refl").unwrap();
    let x = e6.tm.sym(b"X").unwrap();
    let phi = e6.tm.mk_equal(&x, &x).unwrap();
    assert!(
        derive_ind_ord(
            &e6,
            &phi,
            b"X",
            &x,
            &x,
            std::slice::from_ref(&x),
            dummy.clone(),
            vec![dummy.clone()],
            dummy.clone(),
            dummy,
        )
        .is_err()
    );

    // ground env + hand-registered ind_ord: the rule set builds (the
    // clause is just data) but soundness fails safe at the discharge.
    let mut bogus = ground_env().unwrap();
    bogus.ind_ord = vec![1];
    assert_eq!(bogus.n_clauses(), 30);
    assert!(soundness(&bogus).is_err());
}

//! **S4 — the definitional principle (conservative tier)**, per the
//! S4+S6 design `notes/vibes/lisp/acl2-s4-s6-design.md` §3–§6.
//!
//! [`admit_defun`] turns a user `defun` into a new [`Acl2Env`]
//! generation: the model function is **genuinely defined** (a plain
//! `Thm::define` for non-recursive bodies; the S0 carrier's paramorphic
//! recursor — the promoted `carrier.rs` `aappend` machinery — for
//! structural recursion), the defining equation is a **proved** model
//! theorem ([`UserRow::def_eq_model`], by carrier induction with unused
//! IHs), and the env gains the row's congruence/computation clauses (for
//! free, from the generic row discharges) plus one `Def(j)`
//! defining-equation clause whose soundness discharge is the uniform
//! `discharge_def` in [`super::derivable`]. **No postulates anywhere**:
//! admissibility failures error with nothing minted.
//!
//! The kernel-side admissibility check is deliberately **stricter** than
//! `lang/lisp/acl2.rs`'s syntactic check (design §0.6): recursive bodies
//! must match the consp-guarded single-formal depth-1 template
//! `(IF (CONSP xr) STEP BASE)` of §4. Deeper `car`/`cdr` descent,
//! multiple recursive formals, mutual recursion and measures are S5/S7
//! (this directory's the generated open-work index).
//!
//! The **single source of truth** for what a body *means* is
//! [`model_image`] (§3.1): it defines both the `def_eq_model` statement
//! and — through `eval_open`'s image — the `discharge_def` chain, so the
//! two meet syntactically; any drift is a kernel error, never an unsound
//! theorem.

use std::sync::{Arc, OnceLock};

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{as_blob, as_int};
use smol_str::SmolStr;

use crate::init::acl2::carrier::acl2_payload;
use crate::init::acl2::derivable::{Acl2Env, UserRow, project_with, soundness, sym_lit_of, uncons};
use crate::init::acl2::prims::PrimRow;
use crate::init::acl2::term::Terms;
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::carved::apply_def;

/// A user `defun` candidate. The body arrives *encoded* (a closed
/// carrier value over the formals as object variables `asym ⌜Xᵢ⌝`) —
/// surface parsing stays untrusted lang-side; everything here is
/// re-checked syntactically on the encoding.
pub struct DefunSpec {
    /// The surface symbol, e.g. `"APP"`.
    pub name: SmolStr,
    /// The formal parameter names (distinct).
    pub formals: Vec<SmolStr>,
    /// The encoded pseudo-term body over the formals.
    pub body: Term,
    /// `Some(r)` = structurally recursive on formal `r` (the §4
    /// template); `None` = non-recursive.
    pub rec_formal: Option<usize>,
}

/// A resolved head table for the model translation: `(name, arity,
/// model)` per callable row (primitives ++ earlier users).
type TableRow = (SmolStr, usize, Term);

fn env_table(env: &Acl2Env) -> Vec<TableRow> {
    env.rows
        .iter()
        .map(|r| (r.sym.clone(), r.arity, r.model.clone()))
        .collect()
}

/// [`model_image`] over the env's full row table with explicit formal
/// bindings — the statement-computation entry the
/// [`super::derivable::model_eq_target`]/[`super::derivable::model_holds_target`]
/// helpers use (§5.2's single-source-of-truth contract).
pub(crate) fn model_image_of(
    env: &Acl2Env,
    formals: &[(SmolStr, Term)],
    enc: &Term,
) -> Result<Term> {
    model_image(&env.tm, &env_table(env), formals, enc)
}

fn bad(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("acl2 defun: {}", msg.into()))
}

/// The nil-terminated argument list of an application form, as a vec.
fn args_of(tm: &Terms, mut t: Term) -> Result<Vec<Term>> {
    let mut out = Vec::new();
    while t != tm.th.nil {
        let (h, rest) =
            uncons(tm, &t).ok_or_else(|| bad(format!("improper argument list: {t}")))?;
        out.push(h);
        t = rest;
    }
    Ok(out)
}

// ============================================================================
// §3.1 model_image — the single source of truth
// ============================================================================

/// The compositional model translation of an encoded pseudo-term with
/// formal `Xᵢ ↦ args[i]`: symbols → the matching argument (error
/// otherwise), `aint`/`anil` literals → themselves, `(QUOTE v)` → `v`,
/// `(IF a b c)` → `aif ⟦a⟧ ⟦b⟧ ⟦c⟧`, table heads → `row.model ⟦a⃗⟧`.
/// By construction this is exactly `eval_open`'s image of the encoding
/// at a valuation sending `⌜Xᵢ⌝ ↦ args[i]` — the §3.1 agreement that
/// makes `discharge_def` close syntactically.
fn model_image(
    tm: &Terms,
    table: &[TableRow],
    formals: &[(SmolStr, Term)],
    enc: &Term,
) -> Result<Term> {
    if *enc == tm.th.nil {
        return Ok(tm.th.nil.clone());
    }
    if let Some(name) = sym_lit_of(tm, enc) {
        return formals
            .iter()
            .find(|(f, _)| f.as_bytes() == name.as_slice())
            .map(|(_, v)| v.clone())
            .ok_or_else(|| {
                bad(format!(
                    "symbol `{}` is not a formal",
                    String::from_utf8_lossy(&name)
                ))
            });
    }
    if let Some((f, _)) = enc.as_app()
        && *f == tm.th.aint
    {
        return Ok(enc.clone());
    }
    let Some((h, tail)) = uncons(tm, enc) else {
        return Err(bad(format!("not an encoded pseudo-term: {enc}")));
    };
    if h == tm.qsym {
        let (v, rest) = uncons(tm, &tail).ok_or_else(|| bad("malformed quote payload"))?;
        if rest != tm.th.nil {
            return Err(bad("malformed quote payload"));
        }
        return Ok(v);
    }
    let name = sym_lit_of(tm, &h).ok_or_else(|| bad(format!("non-symbol head in {enc}")))?;
    let args = args_of(tm, tail)?;
    if name == b"IF" {
        if args.len() != 3 {
            return Err(bad("IF wants exactly 3 arguments"));
        }
        let mut out = tm.pr.aif.clone();
        for a in &args {
            out = out.apply(model_image(tm, table, formals, a)?)?;
        }
        return Ok(out);
    }
    let Some((_, arity, model)) = table
        .iter()
        .find(|(n, _, _)| n.as_bytes() == name.as_slice())
    else {
        return Err(bad(format!(
            "unknown head `{}`",
            String::from_utf8_lossy(&name)
        )));
    };
    if args.len() != *arity {
        return Err(bad(format!(
            "head `{}` wants {arity} arguments, got {}",
            String::from_utf8_lossy(&name),
            args.len()
        )));
    }
    let mut out = model.clone();
    for a in &args {
        out = out.apply(model_image(tm, table, formals, a)?)?;
    }
    Ok(out)
}

// ============================================================================
// §3.3 the paramorphic step translation (STEP under the cons case)
// ============================================================================

/// Everything the recursive-step translation needs to know.
struct ParaCx<'a> {
    tm: &'a Terms,
    /// Table WITHOUT the candidate itself (self-calls must match the
    /// template and are handled before the table).
    table: &'a [TableRow],
    /// The non-recursive formals `Xᵢ ↦ args[i]` (the recursive formal is
    /// deliberately absent: a raw `xr` in STEP is an error — the
    /// paramorphism never rebuilds it).
    formals: &'a [(SmolStr, Term)],
    /// The candidate's name / arity / recursive position.
    fname: &'a [u8],
    arity: usize,
    r: usize,
    /// `⌜(CAR xr)⌝` / `⌜(CDR xr)⌝` — the two admissible descents.
    car_xr: Term,
    cdr_xr: Term,
    /// The formal encodings `asym ⌜Xᵢ⌝` (verbatim-argument check).
    formal_encs: &'a [Term],
    /// The cons-step binders: head, tail, and the two recursor images.
    hv: &'a Term,
    tv: &'a Term,
    bhv: &'a Term,
    btv: &'a Term,
}

/// The paramorphic image of a STEP subterm: `(CAR xr) ↦ h`,
/// `(CDR xr) ↦ t`, template self-calls ↦ `bh`/`bt`, raw `xr` rejected,
/// everything else compositional (design §3.3.1 / §4).
fn para_image(cx: &ParaCx, enc: &Term) -> Result<Term> {
    let tm = cx.tm;
    if *enc == cx.car_xr {
        return Ok(cx.hv.clone());
    }
    if *enc == cx.cdr_xr {
        return Ok(cx.tv.clone());
    }
    // A self-call: must be the exact template shape.
    if let Some((h, tail)) = uncons(tm, enc)
        && let Some(name) = sym_lit_of(tm, &h)
        && name.as_slice() == cx.fname
    {
        let args = args_of(tm, tail)?;
        if args.len() != cx.arity {
            return Err(bad(format!("recursive call arity mismatch in {enc}")));
        }
        for (i, a) in args.iter().enumerate() {
            if i != cx.r && *a != cx.formal_encs[i] {
                return Err(bad(format!(
                    "recursive call must pass formal {i} verbatim: {enc}"
                )));
            }
        }
        return if args[cx.r] == cx.car_xr {
            Ok(cx.bhv.clone())
        } else if args[cx.r] == cx.cdr_xr {
            Ok(cx.btv.clone())
        } else {
            Err(bad(format!(
                "recursive call must descend by exactly (CAR xr) or (CDR xr): {enc}"
            )))
        };
    }
    if *enc == tm.th.nil {
        return Ok(tm.th.nil.clone());
    }
    if let Some(name) = sym_lit_of(tm, enc) {
        return cx
            .formals
            .iter()
            .find(|(f, _)| f.as_bytes() == name.as_slice())
            .map(|(_, v)| v.clone())
            .ok_or_else(|| {
                bad(format!(
                    "raw recursive formal (or unknown symbol) `{}` in STEP",
                    String::from_utf8_lossy(&name)
                ))
            });
    }
    if let Some((f, _)) = enc.as_app()
        && *f == tm.th.aint
    {
        return Ok(enc.clone());
    }
    let Some((h, tail)) = uncons(tm, enc) else {
        return Err(bad(format!("not an encoded pseudo-term: {enc}")));
    };
    if h == tm.qsym {
        let (v, rest) = uncons(tm, &tail).ok_or_else(|| bad("malformed quote payload"))?;
        if rest != tm.th.nil {
            return Err(bad("malformed quote payload"));
        }
        return Ok(v);
    }
    let name = sym_lit_of(tm, &h).ok_or_else(|| bad(format!("non-symbol head in {enc}")))?;
    let args = args_of(tm, tail)?;
    if name == b"IF" {
        if args.len() != 3 {
            return Err(bad("IF wants exactly 3 arguments"));
        }
        let mut out = tm.pr.aif.clone();
        for a in &args {
            out = out.apply(para_image(cx, a)?)?;
        }
        return Ok(out);
    }
    let Some((_, arity, model)) = cx
        .table
        .iter()
        .find(|(n, _, _)| n.as_bytes() == name.as_slice())
    else {
        return Err(bad(format!(
            "unknown head `{}`",
            String::from_utf8_lossy(&name)
        )));
    };
    if args.len() != *arity {
        return Err(bad(format!(
            "head `{}` wants {arity} arguments, got {}",
            String::from_utf8_lossy(&name),
            args.len()
        )));
    }
    let mut out = model.clone();
    for a in &args {
        out = out.apply(para_image(cx, a)?)?;
    }
    Ok(out)
}

// ============================================================================
// The recursion engine (the promoted carrier.rs `Append` machinery,
// generalized to n formals with a designated recursive position)
// ============================================================================

/// The parsed §4 template of a recursive body.
struct RecTemplate {
    step: Term,
    base: Term,
}

/// Parse `body = (IF (CONSP xr) STEP BASE)` (exactly — the flipped
/// orientation is not accepted; the untrusted front end normalizes).
fn parse_template(tm: &Terms, body: &Term, xr: &SmolStr) -> Result<RecTemplate> {
    let (h, tail) = uncons(tm, body).ok_or_else(|| bad("recursive body must be an IF form"))?;
    if sym_lit_of(tm, &h).as_deref() != Some(b"IF") {
        return Err(bad("recursive body must be (IF (CONSP xr) STEP BASE)"));
    }
    let args = args_of(tm, tail)?;
    if args.len() != 3 {
        return Err(bad("recursive body must be (IF (CONSP xr) STEP BASE)"));
    }
    let guard_want = tm.app(b"CONSP", &[tm.sym(xr.as_bytes())?])?;
    if args[0] != guard_want {
        return Err(bad(format!("recursive body's guard must be (CONSP {xr})")));
    }
    Ok(RecTemplate {
        step: args[1].clone(),
        base: args[2].clone(),
    })
}

/// The three paramorphism steps of a recursive defun at concrete
/// non-recursive formal values `others` (position `r` ignored):
/// atom `λb. ⟦BASE⟧[xr := aatom b]`, nil `⟦BASE⟧[xr := anil]`, cons
/// `λh t bh bt. ⟦STEP⟧` under the §3.3 translation. Deterministic in
/// its inputs — the same function runs at define time (with the
/// definition's bound formals as free variables) and at law-derivation
/// time (with the law's arguments), which is what makes `prec_eq`
/// re-derivation line up syntactically.
fn rec_steps(
    tm: &Terms,
    table_no_self: &[TableRow],
    formals: &[SmolStr],
    r: usize,
    fname: &[u8],
    tpl: &RecTemplate,
    others: &[Term],
) -> Result<[Term; 3]> {
    let a = tm.th.ty.clone();
    let formal_pairs = |xr_val: &Term| -> Vec<(SmolStr, Term)> {
        formals
            .iter()
            .enumerate()
            .map(|(i, f)| {
                (
                    f.clone(),
                    if i == r {
                        xr_val.clone()
                    } else {
                        others[i].clone()
                    },
                )
            })
            .collect()
    };
    // Atom step: λb. ⟦BASE⟧[xr := aatom b].
    let sa = {
        let b = Term::free("__sb", acl2_payload());
        let atom_b = tm.th.atom.clone().apply(b)?;
        let img = model_image(tm, table_no_self, &formal_pairs(&atom_b), &tpl.base)?;
        Term::abs(acl2_payload(), subst::close(&img, "__sb"))
    };
    // Nil step: ⟦BASE⟧[xr := anil].
    let sn = model_image(tm, table_no_self, &formal_pairs(&tm.th.nil), &tpl.base)?;
    // Cons step: λh t bh bt. ⟦STEP⟧ (paramorphic translation).
    let sc = {
        let hv = Term::free("__sh", a.clone());
        let tv = Term::free("__st", a.clone());
        let bhv = Term::free("__sbh", a.clone());
        let btv = Term::free("__sbt", a.clone());
        let others_pairs: Vec<(SmolStr, Term)> = formals
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != r)
            .map(|(i, f)| (f.clone(), others[i].clone()))
            .collect();
        let formal_encs: Vec<Term> = formals
            .iter()
            .map(|f| tm.sym(f.as_bytes()))
            .collect::<Result<_>>()?;
        let xr = &formals[r];
        let cx = ParaCx {
            tm,
            table: table_no_self,
            formals: &others_pairs,
            fname,
            arity: formals.len(),
            r,
            car_xr: tm.app(b"CAR", &[tm.sym(xr.as_bytes())?])?,
            cdr_xr: tm.app(b"CDR", &[tm.sym(xr.as_bytes())?])?,
            formal_encs: &formal_encs,
            hv: &hv,
            tv: &tv,
            bhv: &bhv,
            btv: &btv,
        };
        let img = para_image(&cx, &tpl.step)?;
        let l_bt = Term::abs(a.clone(), subst::close(&img, "__sbt"));
        let l_bh = Term::abs(a.clone(), subst::close(&l_bt, "__sbh"));
        let l_t = Term::abs(a.clone(), subst::close(&l_bh, "__st"));
        Term::abs(a.clone(), subst::close(&l_t, "__sh"))
    };
    Ok([sa, sn, sc])
}

// ============================================================================
// §3–§4 admission
// ============================================================================

/// Names a new table row may not shadow / use as formals — the shared
/// core of [`check_names`] and [`super::derivable::install_user_rows`]'s
/// hand-row seam. `b`/`h`/`t` are the carrier `induct` binder hints
/// (they name the case variables of the `def_eq_model` proof), so
/// formals may not collide with them.
pub(crate) fn check_new_row(rows: &[PrimRow], name: &SmolStr, formals: &[SmolStr]) -> Result<()> {
    if name.is_empty() || name == "QUOTE" || name == "IF" {
        return Err(bad(format!("illegal defun name `{name}`")));
    }
    if rows.iter().any(|r| r.sym == *name) {
        return Err(bad(format!(
            "name `{name}` collides with an existing table row"
        )));
    }
    for (i, f) in formals.iter().enumerate() {
        if f.is_empty() {
            return Err(bad("empty formal name"));
        }
        if formals[..i].contains(f) {
            return Err(bad(format!("duplicate formal `{f}`")));
        }
        if matches!(f.as_str(), "b" | "h" | "t" | "sg") || f.starts_with("__") {
            return Err(bad(format!(
                "formal name `{f}` is reserved (induct binder hints / internals)"
            )));
        }
    }
    Ok(())
}

fn check_names(env: &Acl2Env, spec: &DefunSpec) -> Result<()> {
    check_new_row(&env.rows, &spec.name, &spec.formals)?;
    if let Some(r) = spec.rec_formal
        && r >= spec.formals.len()
    {
        return Err(bad(format!("recursive formal index {r} out of range")));
    }
    Ok(())
}

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

/// **Admit a user `defun`** (design §3–§5): validate admissibility (§4;
/// everything checked *before* the first `Thm::define` — a rejection
/// mints nothing), define the model function, prove `def_eq_model`, and
/// return the extended environment (new rows + `Def` clause; the
/// deep-term theory is rebuilt over the extended table).
pub fn admit_defun(env: &Acl2Env, spec: &DefunSpec) -> Result<Acl2Env> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    check_names(env, spec)?;
    let table = env_table(env);
    let n = spec.formals.len();

    // ---- dry-run validation (no defines yet) ----
    let dry_args: Vec<Term> = (0..n)
        .map(|i| Term::free(format!("__dry{i}").as_str(), a.clone()))
        .collect();
    let dry_pairs: Vec<(SmolStr, Term)> = spec
        .formals
        .iter()
        .cloned()
        .zip(dry_args.iter().cloned())
        .collect();
    let tpl = match spec.rec_formal {
        None => {
            // Non-recursive: the whole body must translate over the
            // env's table (any self-call is an unknown head → error).
            model_image(tm, &table, &dry_pairs, &spec.body)?;
            None
        }
        Some(r) => {
            let tpl = parse_template(tm, &spec.body, &spec.formals[r])?;
            // BASE: no self-calls (unknown head in the env table), any
            // formal (including a raw xr) allowed.
            model_image(tm, &table, &dry_pairs, &tpl.base)?;
            // STEP: the paramorphic template check (raw xr rejected,
            // self-calls in template form only).
            rec_steps(
                tm,
                &table,
                &spec.formals,
                r,
                spec.name.as_bytes(),
                &tpl,
                &dry_args,
            )?;
            Some(tpl)
        }
    };

    // ---- define the model constant (minted ONCE, §1) ----
    let def_args: Vec<Term> = (0..n)
        .map(|i| Term::free(format!("__df{i}").as_str(), a.clone()))
        .collect();
    let (model, def_eq) = match (spec.rec_formal, &tpl) {
        (None, _) => {
            let img = model_image(
                tm,
                &table,
                &spec
                    .formals
                    .iter()
                    .cloned()
                    .zip(def_args.iter().cloned())
                    .collect::<Vec<_>>(),
                &spec.body,
            )?;
            let mut lam = img;
            for i in (0..n).rev() {
                lam = Term::abs(a.clone(), subst::close(&lam, &format!("__df{i}")));
            }
            defined(&format!("acl2.user.{}", spec.name), lam)?
        }
        (Some(r), Some(tpl)) => {
            let steps = rec_steps(
                tm,
                &table,
                &spec.formals,
                r,
                spec.name.as_bytes(),
                tpl,
                &def_args,
            )?;
            let body = tm.th.cs.prec(&steps, &a)?.apply(def_args[r].clone())?;
            let mut lam = body;
            for i in (0..n).rev() {
                lam = Term::abs(a.clone(), subst::close(&lam, &format!("__df{i}")));
            }
            defined(&format!("acl2.user.{}", spec.name), lam)?
        }
        _ => unreachable!("template parsed iff recursive"),
    };

    // ---- the defining-equation clause formula ⌜(EQUAL (f X⃗) body)⌝ ----
    let formal_syms: Vec<Term> = spec
        .formals
        .iter()
        .map(|f| tm.sym(f.as_bytes()))
        .collect::<Result<_>>()?;
    let def_enc = tm.mk_equal(&tm.app(spec.name.as_bytes(), &formal_syms)?, &spec.body)?;

    // ---- prove def_eq_model: ⊢ ∀x⃗. f_model x⃗ = ⟦body⟧(x⃗) ----
    // (needs the FULL table — the body's self-calls translate through
    // the just-minted model constant.)
    let mut full_table = table.clone();
    full_table.push((spec.name.clone(), n, model.clone()));
    let u = UserRow {
        name: spec.name.clone(),
        formals: spec.formals.clone(),
        body: spec.body.clone(),
        rec_formal: spec.rec_formal,
        model: model.clone(),
        def_enc,
        // Placeholder; replaced below once proved (never observable —
        // the env is only returned with the proved equation in place).
        def_eq_model: def_eq.clone(),
        def_eq: def_eq.clone(),
    };
    let def_eq_model = prove_def_eq_model(env, &full_table, &u, tpl.as_ref())?;
    let u = UserRow { def_eq_model, ..u };

    // ---- assemble the new generation ----
    let mut rows = env.rows.clone();
    rows.push(PrimRow {
        sym: spec.name.clone(),
        arity: n,
        model,
    });
    let tm2 = Arc::new(Terms::build_with(rows.clone())?);
    let mut users = env.users.clone();
    users.push(u);
    Ok(Acl2Env {
        tm: tm2,
        axioms: env.axioms.clone(),
        rows,
        users,
        s6: env.s6,
        ind_ord: env.ind_ord.clone(),
    })
}

/// `⊢ ∀x⃗. f_model x⃗ = ⟦body⟧(x⃗)` — trivial `apply_def` for
/// non-recursive rows; carrier induction (unused IHs) at the motive
/// `λxr. f_model …x⃗… = ⟦body⟧[xr]` for recursive ones (design §3.3.4).
fn prove_def_eq_model(
    env: &Acl2Env,
    full_table: &[TableRow],
    u: &UserRow,
    tpl: Option<&RecTemplate>,
) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let xs: Vec<Term> = u
        .formals
        .iter()
        .map(|f| Term::free(f.as_str(), a.clone()))
        .collect();
    let pairs_at = |xr_val: &Term, r: usize| -> Vec<(SmolStr, Term)> {
        u.formals
            .iter()
            .enumerate()
            .map(|(i, f)| {
                (
                    f.clone(),
                    if i == r {
                        xr_val.clone()
                    } else {
                        xs[i].clone()
                    },
                )
            })
            .collect()
    };

    let Some(r) = u.rec_formal else {
        // Non-recursive: apply_def at the formal-named frees.
        let mut out = apply_def(&u.def_eq, &xs)?;
        for f in u.formals.iter().rev() {
            out = out.all_intro(f.as_str(), a.clone())?;
        }
        return Ok(out);
    };
    let tpl = tpl.ok_or_else(|| bad("internal: recursive row without template"))?;
    let pr = tm.pr;

    // The motive λxr'. f_model x⃗[r:=xr'] = ⟦body⟧(x⃗[r:=xr']).
    let mv = Term::free("__dm", a.clone());
    let motive = {
        let mut lhs = u.model.clone();
        for (i, x) in xs.iter().enumerate() {
            lhs = lhs.apply(if i == r { mv.clone() } else { x.clone() })?;
        }
        let rhs = model_image(tm, full_table, &pairs_at(&mv, r), &u.body)?;
        Term::abs(a.clone(), subst::close(&lhs.equals(rhs)?, "__dm"))
    };

    // One leaf case: LHS by the per-constructor law, RHS by firing the
    // (CONSP xr) guard to `anil` (consp_atom / consp_nil) then if_nil.
    let leaf_case = |xr_val: &Term, guard_eq: Thm| -> Result<Thm> {
        let lhs = rec_law_at(env, full_table, u, tpl, &xs, xr_val)?;
        let img_s = model_image(tm, full_table, &pairs_at(xr_val, r), &tpl.step)?;
        let img_b = model_image(tm, full_table, &pairs_at(xr_val, r), &tpl.base)?;
        let rhs = guard_eq
            .cong_arg(pr.aif.clone())?
            .cong_fn(img_s.clone())?
            .cong_fn(img_b.clone())? // aif (aconsp xr_val) S B = aif anil S B
            .trans(pr.if_nil()?.all_elim(img_s)?.all_elim(img_b)?)?; // = B
        let raw = lhs.trans(rhs.sym()?)?;
        beta_expand(&motive, xr_val.clone(), raw)
    };

    // Atom case (free `b` — the induct binder hint).
    let case_atom = {
        let b = Term::free("b", acl2_payload());
        let atom_b = tm.th.atom.clone().apply(b.clone())?;
        leaf_case(&atom_b, pr.consp_atom()?.all_elim(b)?)?
    };
    // Nil case.
    let case_nil = leaf_case(&tm.th.nil.clone(), pr.consp_nil()?)?;

    // Cons case (free `h`, `t`; IHs unused): LHS by the folded scons
    // law; RHS by consp_cons + if_t (+ t_ne_nil), then proj_scons
    // rewrites `car/cdr (acons h t)` down to `h`/`t` everywhere
    // (including inside the recursive-call arguments).
    let case_cons = {
        let h = Term::free("h", a.clone());
        let t = Term::free("t", a.clone());
        let acons_ht = tm.th.cons.clone().apply(h.clone())?.apply(t.clone())?;
        let lhs = rec_law_at(env, full_table, u, tpl, &xs, &acons_ht)?;
        let img_s = model_image(tm, full_table, &pairs_at(&acons_ht, r), &tpl.step)?;
        let img_b = model_image(tm, full_table, &pairs_at(&acons_ht, r), &tpl.base)?;
        let guard = pr.consp_cons()?.all_elim(h.clone())?.all_elim(t.clone())?; // aconsp (acons h t) = t
        let car_eq = tm.th.cs.proj_scons(false, &h, &t)?;
        let cdr_eq = tm.th.cs.proj_scons(true, &h, &t)?;
        let rhs = guard
            .cong_arg(pr.aif.clone())?
            .cong_fn(img_s.clone())?
            .cong_fn(img_b.clone())? // aif (aconsp (acons h t)) S B = aif t S B
            .trans(
                pr.if_t()?
                    .all_elim(pr.t.clone())?
                    .all_elim(img_s)?
                    .all_elim(img_b)?
                    .imp_elim(pr.t_ne_nil()?)?,
            )? // = S[xr := acons h t]
            .rhs_conv(|u| u.rw_all(&car_eq))?
            .rhs_conv(|u| u.rw_all(&cdr_eq))?; // = the folded step value
        let raw = lhs.trans(rhs.sym()?)?;
        let ph = motive.clone().apply(h)?;
        let pt = motive.clone().apply(t)?;
        beta_expand(&motive, acons_ht, raw)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?
    };

    let by = tm
        .th
        .induct(&motive, vec![case_atom, case_nil, case_cons])?;
    // Clean the η/β shape (the `soundness` pattern) and re-quantify the
    // formals in declaration order.
    let clean = beta_reduce(by.all_elim(xs[r].clone())?)?;
    let mut out = clean;
    for f in u.formals.iter().rev() {
        out = out.all_intro(f.as_str(), a.clone())?;
    }
    Ok(out)
}

/// The per-constructor computation law of a *recursive* row at
/// `args[r] := xr_val` (a constructor form `aatom b` / `anil` /
/// `acons h t`): `⊢ f_model x⃗[xr_val] = <case value>`, recursor images
/// folded back to `f_model` (the promoted `Append::leaf`/`scons`).
fn rec_law_at(
    env: &Acl2Env,
    full_table: &[TableRow],
    u: &UserRow,
    tpl: &RecTemplate,
    others: &[Term],
    xr_val: &Term,
) -> Result<Thm> {
    let tm = &*env.tm;
    let a = tm.th.ty.clone();
    let r = u
        .rec_formal
        .ok_or_else(|| bad("rec_law_at on a non-recursive row"))?;
    // The table without the row itself (steps never mention the model).
    let table_no_self: Vec<TableRow> = full_table
        .iter()
        .filter(|(n, _, _)| *n != u.name)
        .cloned()
        .collect();
    let steps = rec_steps(
        tm,
        &table_no_self,
        &u.formals,
        r,
        u.name.as_bytes(),
        tpl,
        others,
    )?;
    let args_at = |v: &Term| -> Vec<Term> {
        others
            .iter()
            .enumerate()
            .map(|(i, x)| if i == r { v.clone() } else { x.clone() })
            .collect()
    };
    let e = apply_def(&u.def_eq, &args_at(xr_val))?; // f x⃗[v] = prec(steps) v
    // Case on the constructor shape of xr_val.
    if let Some((f, b)) = xr_val.as_app()
        && *f == tm.th.atom
    {
        let comp = tm.th.cs.prec_eq(&steps, 0, &a)?.all_elim(b.clone())?;
        return e.trans(comp)?.reduce_rhs();
    }
    if *xr_val == tm.th.nil {
        let comp = tm.th.cs.prec_eq(&steps, 1, &a)?;
        return e.trans(comp);
    }
    if let Some((h, t)) = uncons(tm, xr_val) {
        let comp = tm
            .th
            .cs
            .prec_eq(&steps, 2, &a)?
            .all_elim(h.clone())?
            .all_elim(t.clone())?;
        // Fold the recursor images back to f_model (the lisp.rs:301
        // trick) before reducing.
        let fold_h = apply_def(&u.def_eq, &args_at(&h))?;
        let fold_t = apply_def(&u.def_eq, &args_at(&t))?;
        return e
            .trans(comp)?
            .rhs_conv(|x| x.rw_all(&fold_h.sym()?))?
            .rhs_conv(|x| x.rw_all(&fold_t.sym()?))?
            .reduce_rhs();
    }
    Err(bad(format!("rec_law_at: not a constructor form: {xr_val}")))
}

/// The public per-constructor / defining law of user row `u` at concrete
/// arguments: `⊢ f_model a⃗ = <value of the defining equation at a⃗>`.
/// For recursive rows `args[r]` must be `aatom b` / `anil` /
/// `acons h t` / `aint ⌜i⌝` / `asym ⌜s⌝` (payload constructors are
/// unfolded to the atom case); non-recursive rows unfold outright.
pub fn defun_law(env: &Acl2Env, u: &UserRow, args: &[Term]) -> Result<Thm> {
    let tm = &*env.tm;
    if args.len() != u.formals.len() {
        return Err(bad(format!(
            "defun_law: `{}` wants {} arguments",
            u.name,
            u.formals.len()
        )));
    }
    let Some(r) = u.rec_formal else {
        return apply_def(&u.def_eq, args);
    };
    let mut full_table = env_table(env);
    if !full_table.iter().any(|(n, _, _)| *n == u.name) {
        full_table.push((u.name.clone(), u.formals.len(), u.model.clone()));
    }
    let tpl = parse_template(tm, &u.body, &u.formals[r])?;
    let others: Vec<Term> = args.to_vec();
    let v = &args[r];
    // Payload constructors unfold to the atom case first.
    let unfold = if let Some((f, i)) = v.as_app()
        && *f == tm.th.aint
    {
        Some((tm.th.int_unfold(i)?, {
            let inl_i = crate::init::coprod::inl(Type::int(), Type::bytes()).apply(i.clone())?;
            tm.th.atom.clone().apply(inl_i)?
        }))
    } else if let Some((f, s)) = v.as_app()
        && *f == tm.th.asym
    {
        Some((tm.th.sym_unfold(s)?, {
            let inr_s = crate::init::coprod::inr(Type::int(), Type::bytes()).apply(s.clone())?;
            tm.th.atom.clone().apply(inr_s)?
        }))
    } else {
        None
    };
    match unfold {
        None => rec_law_at(env, &full_table, u, &tpl, &others, v),
        Some((eq, atom_form)) => {
            // ⊢ f_model …v… = f_model …(aatom (in* w))… then the atom law.
            let mut partial = u.model.clone();
            for x in args.iter().take(r) {
                partial = partial.apply(x.clone())?;
            }
            let mut start = eq.cong_arg(partial)?;
            for x in args.iter().skip(r + 1) {
                start = start.cong_fn(x.clone())?;
            }
            let law = rec_law_at(env, &full_table, u, &tpl, &others, &atom_form)?;
            start.trans(law)
        }
    }
}

// ============================================================================
// Ground folding (`defun_ground` — the `plus_lit` analogue for user rows)
// ============================================================================

/// Is `t` a constructor-literal carrier value (`anil`, `aint ⌜i⌝`,
/// `asym ⌜s⌝`, `acons` of values)?
fn is_value(tm: &Terms, t: &Term) -> bool {
    if *t == tm.th.nil {
        return true;
    }
    if let Some((f, x)) = t.as_app() {
        if *f == tm.th.aint {
            return as_int(x).is_some();
        }
        if *f == tm.th.asym {
            return as_blob(x).is_some();
        }
    }
    if let Some((h, t2)) = uncons(tm, t) {
        return is_value(tm, &h) && is_value(tm, &t2);
    }
    false
}

/// `⊢ t = v` for a ground *model expression* `t` (constructor-literal
/// values, user-row applications, `aplus` of int literals), `v` a value.
/// The covered head set is the S4 gate fragment; extend on demand
/// (source-local TODO markers). Errors — mints nothing — outside the fragment.
pub fn fold_ground(env: &Acl2Env, t: &Term) -> Result<Thm> {
    let tm = &*env.tm;
    if is_value(tm, t) {
        return Thm::refl(t.clone());
    }
    // Unwind the application spine.
    let mut head = t.clone();
    let mut args: Vec<Term> = Vec::new();
    while let Some((f, x)) = head.clone().as_app() {
        args.push(x.clone());
        head = f.clone();
    }
    args.reverse();
    // Fold the arguments first (left-to-right congruence).
    let mut acc = Thm::refl(t.clone())?;
    let mut vals: Vec<Term> = Vec::with_capacity(args.len());
    for (i, x) in args.iter().enumerate() {
        let fx = fold_ground(env, x)?;
        let (l, r) = fx.concl().as_eq().ok_or(Error::NotAnEquation)?;
        let (l, r) = (l.clone(), r.clone());
        vals.push(r.clone());
        if l != r {
            let mut partial = head.clone();
            for v in vals.iter().take(i) {
                partial = partial.apply(v.clone())?;
            }
            let mut step = fx.cong_arg(partial)?;
            for y in args.iter().skip(i + 1) {
                step = step.cong_fn(y.clone())?;
            }
            acc = acc.trans(step)?;
        }
    }
    // acc: ⊢ t = head v⃗. Now fire the head's ground rule.
    if head == tm.th.cons && vals.len() == 2 {
        return Ok(acc); // a value now (args folded)
    }
    if head == tm.pr.plus && vals.len() == 2 {
        let get = |v: &Term| -> Result<i128> {
            let (f, x) = v.as_app().ok_or_else(|| bad("aplus on non-literal"))?;
            if *f != tm.th.aint {
                return Err(bad(format!("aplus on non-int value {v}")));
            }
            let i = as_int(x).ok_or_else(|| bad("aplus on non-literal int"))?;
            i128::try_from(&i).map_err(|_| bad("int literal out of i128 range"))
        };
        let (i, j) = (get(&vals[0])?, get(&vals[1])?);
        return acc.trans(tm.pr.plus_lit(i, j)?);
    }
    if let Some(u) = env.users.iter().find(|u| u.model == head) {
        let law = defun_law(env, u, &vals)?; // head v⃗ = img
        let img = law.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let rest = fold_ground(env, &img)?;
        return acc.trans(law)?.trans(rest);
    }
    Err(bad(format!(
        "fold_ground: no ground rule for head {head} (S4 fragment: values, CONS, \
         BINARY-+ literals, user rows)"
    )))
}

/// `⊢ f_model v⃗ = w` for user row `sym` at constructor-literal
/// arguments — the model-equation input of
/// [`super::derivable::derive_comp_folded`] for user computation clauses.
pub fn defun_ground(env: &Acl2Env, sym: &str, args: &[Term]) -> Result<Thm> {
    let (_, u) = env.user(sym)?;
    let mut t = u.model.clone();
    for x in args {
        t = t.apply(x.clone())?;
    }
    fold_ground(env, &t)
}

// ============================================================================
// §5.3 Acl2Session — per-generation soundness cache
// ============================================================================

/// An [`Acl2Env`] generation with its (expensive) soundness metatheorem
/// proved once on first projection and cached. `admit_defun` consumes
/// the session: derivations are **per-generation values** — admit
/// defuns first, then derive and project within the generation.
pub struct Acl2Session {
    env: Acl2Env,
    snd: OnceLock<Thm>,
}

impl Acl2Session {
    /// Wrap an environment as a fresh generation.
    pub fn new(env: Acl2Env) -> Self {
        Acl2Session {
            env,
            snd: OnceLock::new(),
        }
    }

    /// The current environment.
    pub fn env(&self) -> &Acl2Env {
        &self.env
    }

    /// Admit a defun: a new generation (the soundness cache is cleared —
    /// the clause set changed).
    pub fn admit_defun(self, spec: &DefunSpec) -> Result<Acl2Session> {
        Ok(Acl2Session::new(admit_defun(&self.env, spec)?))
    }

    /// The soundness metatheorem for this generation, proved on first
    /// use ([`soundness`]) and cached.
    pub fn soundness(&self) -> Result<Thm> {
        if let Some(s) = self.snd.get() {
            return Ok(s.clone());
        }
        let s = soundness(&self.env)?;
        let _ = self.snd.set(s.clone());
        Ok(s)
    }

    /// Project a derivation `⊢ Derivable ⌜φ⌝` to
    /// `⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)` through the cached soundness.
    pub fn project(&self, phi: &Term, der: Thm) -> Result<Thm> {
        project_with(&self.soundness()?, phi, der)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::acl2::derivable::{
        ClauseKind, acl2_rule_set, derivable, derive_comp_folded, derive_def, derive_plus_lit,
        ground_env, transport_equal,
    };
    use covalence_hol_eval::mk_int;
    use std::sync::LazyLock;

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    fn aint(tm: &Terms, i: i64) -> Term {
        tm.th.aint_at(&mk_int(i)).unwrap()
    }

    fn acons(tm: &Terms, h: &Term, t: &Term) -> Term {
        tm.th
            .cons
            .clone()
            .apply(h.clone())
            .unwrap()
            .apply(t.clone())
            .unwrap()
    }

    /// `(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))`.
    fn app_spec(tm: &Terms) -> DefunSpec {
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let step = tm
            .app(
                b"CONS",
                &[
                    tm.app(b"CAR", &[x.clone()]).unwrap(),
                    tm.app(b"APP", &[tm.app(b"CDR", &[x.clone()]).unwrap(), y.clone()])
                        .unwrap(),
                ],
            )
            .unwrap();
        let body = tm
            .mk_if(&tm.app(b"CONSP", &[x.clone()]).unwrap(), &step, &y)
            .unwrap();
        DefunSpec {
            name: SmolStr::new("APP"),
            formals: vec![SmolStr::new("X"), SmolStr::new("Y")],
            body,
            rec_formal: Some(0),
        }
    }

    /// The APP-extended session, shared across tests (admission + the
    /// per-generation soundness are proved once, like the S3 `snd()`).
    fn app_session() -> &'static Acl2Session {
        static APP: LazyLock<std::result::Result<Acl2Session, String>> = LazyLock::new(|| {
            let e0 = ground_env().map_err(|e| e.to_string())?;
            let spec = app_spec(&e0.tm);
            Acl2Session::new(e0)
                .admit_defun(&spec)
                .map_err(|e| e.to_string())
        });
        APP.as_ref().unwrap()
    }

    /// **S4 gate (layout regression):** the ground env keeps the
    /// committed 29-clause layout; one admitted defun adds exactly its
    /// congruence + computation + defining-equation clauses at the
    /// design-§2.1 indices (s6 = 0).
    #[test]
    fn t_env_layout_regression() {
        let e0 = ground_env().unwrap();
        assert_eq!(e0.n_clauses(), 29);
        assert_eq!(e0.clause_index(ClauseKind::Comp(10)), 28);

        let env = app_session().env();
        assert_eq!(env.rows.len(), 12);
        assert_eq!(env.users.len(), 1);
        assert_eq!(env.n_clauses(), 32); // 29 + user Cong + Comp + Def
        assert_eq!(env.clause_index(ClauseKind::Mp), 5);
        assert_eq!(env.clause_index(ClauseKind::Inst), 6);
        assert_eq!(env.clause_index(ClauseKind::Cong(11)), 18);
        assert_eq!(env.clause_index(ClauseKind::Comp(11)), 30);
        assert_eq!(env.clause_index(ClauseKind::Def(0)), 31);

        let rs = acl2_rule_set(env);
        assert_eq!(rs.n_clauses().unwrap(), env.n_clauses());

        // The Def clause fires with the exact statement.
        let (_, u) = env.user("APP").unwrap();
        let d = derive_def(env, 0).unwrap();
        check(&d, &derivable(env, &u.def_enc).unwrap());
    }

    /// **S4 gate (app admitted):** the model defining equation is a
    /// closed proved theorem with the exact §3.3 statement, and the
    /// three per-constructor laws come out of the promoted engine.
    #[test]
    fn t_defun_app_admitted() {
        let env = app_session().env();
        let tm = &*env.tm;
        let (pr, th) = (tm.pr, tm.th);
        let a = th.ty.clone();
        let (_, u) = env.user("APP").unwrap();
        let app_m = |p: &Term, q: &Term| {
            u.model
                .clone()
                .apply(p.clone())
                .unwrap()
                .apply(q.clone())
                .unwrap()
        };

        // ⊢ ∀X Y. app X Y = aif (aconsp X) (acons (car X) (app (cdr X) Y)) Y.
        let xx = Term::free("X", a.clone());
        let yy = Term::free("Y", a.clone());
        let car_x = th.car.clone().apply(xx.clone()).unwrap();
        let cdr_x = th.cdr.clone().apply(xx.clone()).unwrap();
        let step_img = acons(tm, &car_x, &app_m(&cdr_x, &yy));
        let rhs = pr
            .aif
            .clone()
            .apply(pr.consp.clone().apply(xx.clone()).unwrap())
            .unwrap()
            .apply(step_img)
            .unwrap()
            .apply(yy.clone())
            .unwrap();
        let expected = app_m(&xx, &yy)
            .equals(rhs)
            .unwrap()
            .forall("Y", a.clone())
            .unwrap()
            .forall("X", a.clone())
            .unwrap();
        check(&u.def_eq_model, &expected);

        // Per-constructor laws.
        let b = Term::free("b", acl2_payload());
        let w = Term::free("w", a.clone());
        let atom_b = th.atom.clone().apply(b.clone()).unwrap();
        let l_atom = defun_law(env, u, &[atom_b.clone(), w.clone()]).unwrap();
        check(&l_atom, &app_m(&atom_b, &w).equals(w.clone()).unwrap());
        let l_nil = defun_law(env, u, &[th.nil.clone(), w.clone()]).unwrap();
        check(&l_nil, &app_m(&th.nil, &w).equals(w.clone()).unwrap());
        let (h, t) = (Term::free("h", a.clone()), Term::free("t", a));
        let ht = acons(tm, &h, &t);
        let l_cons = defun_law(env, u, &[ht.clone(), w.clone()]).unwrap();
        check(
            &l_cons,
            &app_m(&ht, &w)
                .equals(acons(tm, &h, &app_m(&t, &w)))
                .unwrap(),
        );
    }

    /// **S4 gate (len):** an int-valued list recursion —
    /// `(defun len2 (x) (if (consp x) (binary-+ '1 (len2 (cdr x))) '0))`
    /// — admits, and `defun_ground` folds `⊢ len2 ⌜(7 7)⌝ = aint 2`.
    #[test]
    fn t_defun_len() {
        let e0 = ground_env().unwrap();
        let spec = {
            let tm = &*e0.tm;
            let x = tm.sym(b"X").unwrap();
            let step = tm
                .app(
                    b"BINARY-+",
                    &[
                        tm.quote(&aint(tm, 1)).unwrap(),
                        tm.app(b"LEN2", &[tm.app(b"CDR", &[x.clone()]).unwrap()])
                            .unwrap(),
                    ],
                )
                .unwrap();
            let body = tm
                .mk_if(
                    &tm.app(b"CONSP", &[x.clone()]).unwrap(),
                    &step,
                    &tm.quote(&aint(tm, 0)).unwrap(),
                )
                .unwrap();
            DefunSpec {
                name: SmolStr::new("LEN2"),
                formals: vec![SmolStr::new("X")],
                body,
                rec_formal: Some(0),
            }
        };
        let env = admit_defun(&e0, &spec).unwrap();
        let tm = &*env.tm;
        let (_, u) = env.user("LEN2").unwrap();
        let l77 = acons(
            tm,
            &aint(tm, 7),
            &acons(tm, &aint(tm, 7), &tm.th.nil.clone()),
        );
        let g = defun_ground(&env, "LEN2", &[l77.clone()]).unwrap();
        let expected = u
            .model
            .clone()
            .apply(l77)
            .unwrap()
            .equals(aint(tm, 2))
            .unwrap();
        check(&g, &expected);
    }

    /// **S4 gate (non-recursive):** `(defun endp2 (x) (if (consp x) 'nil 't))`
    /// — a plain `Thm::define`, defining equation exact.
    #[test]
    fn t_defun_nonrec() {
        let e0 = ground_env().unwrap();
        let spec = {
            let tm = &*e0.tm;
            let x = tm.sym(b"X").unwrap();
            let body = tm
                .mk_if(
                    &tm.app(b"CONSP", &[x.clone()]).unwrap(),
                    &tm.quote(&tm.th.nil).unwrap(),
                    &tm.quote(&tm.pr.t).unwrap(),
                )
                .unwrap();
            DefunSpec {
                name: SmolStr::new("ENDP2"),
                formals: vec![SmolStr::new("X")],
                body,
                rec_formal: None,
            }
        };
        let env = admit_defun(&e0, &spec).unwrap();
        let tm = &*env.tm;
        let (pr, th) = (tm.pr, tm.th);
        let a = th.ty.clone();
        let (_, u) = env.user("ENDP2").unwrap();
        let xx = Term::free("X", a.clone());
        let rhs = pr
            .aif
            .clone()
            .apply(pr.consp.clone().apply(xx.clone()).unwrap())
            .unwrap()
            .apply(th.nil.clone())
            .unwrap()
            .apply(pr.t.clone())
            .unwrap();
        let expected = u
            .model
            .clone()
            .apply(xx)
            .unwrap()
            .equals(rhs)
            .unwrap()
            .forall("X", a)
            .unwrap();
        check(&u.def_eq_model, &expected);
    }

    /// **S4 gate (rejection):** inadmissible defuns error with nothing
    /// minted and the env unchanged (design §4 — the kernel tier is
    /// deliberately stricter than the lang-side check).
    #[test]
    fn t_defun_rejects() {
        let e0 = ground_env().unwrap();
        let n_before = e0.n_clauses();
        let rows_before = e0.rows.len();
        let tm = e0.tm.clone();
        let x = tm.sym(b"X").unwrap();
        let mk = |name: &str, body: Term, rec: Option<usize>| DefunSpec {
            name: SmolStr::new(name),
            formals: vec![SmolStr::new("X")],
            body,
            rec_formal: rec,
        };

        // No descent template: (defun bad (x) (bad x)).
        let bad = mk("BAD", tm.app(b"BAD", &[x.clone()]).unwrap(), Some(0));
        assert!(admit_defun(&e0, &bad).is_err());

        // Raw xr in STEP: (defun bad2 (x) (if (consp x) x 'nil)).
        let bad2 = mk(
            "BAD2",
            tm.mk_if(
                &tm.app(b"CONSP", &[x.clone()]).unwrap(),
                &x,
                &tm.quote(&tm.th.nil).unwrap(),
            )
            .unwrap(),
            Some(0),
        );
        assert!(admit_defun(&e0, &bad2).is_err());

        // Non-structural descent: (defun bad3 (x) (if (consp x) (bad3 x) 'nil)).
        let bad3 = mk(
            "BAD3",
            tm.mk_if(
                &tm.app(b"CONSP", &[x.clone()]).unwrap(),
                &tm.app(b"BAD3", &[x.clone()]).unwrap(),
                &tm.quote(&tm.th.nil).unwrap(),
            )
            .unwrap(),
            Some(0),
        );
        assert!(admit_defun(&e0, &bad3).is_err());

        // Name collision with a primitive.
        let bad4 = mk("CAR", tm.quote(&tm.th.nil).unwrap(), None);
        assert!(admit_defun(&e0, &bad4).is_err());

        // Unknown head.
        let bad5 = mk("BAD5", tm.app(b"FOO", &[x.clone()]).unwrap(), None);
        assert!(admit_defun(&e0, &bad5).is_err());

        // Self-call in a non-recursive defun (unknown head to itself).
        let bad6 = mk("BAD6", tm.app(b"BAD6", &[x]).unwrap(), None);
        assert!(admit_defun(&e0, &bad6).is_err());

        assert_eq!(e0.n_clauses(), n_before);
        assert_eq!(e0.rows.len(), rows_before);
    }

    /// **S4 gate (soundness):** the metatheorem for the app-extended env
    /// is closed with the exact ∀A statement (over THIS env's eval).
    #[test]
    fn t_defun_soundness_extended() {
        let sess = app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let s = sess.soundness().unwrap();

        let a = tm.th.ty.clone();
        let av = Term::free("A", a.clone());
        let sg = Term::free("sg", tm.val_ty.clone());
        let body = tm
            .eval
            .clone()
            .apply(av.clone())
            .unwrap()
            .apply(sg)
            .unwrap()
            .equals(tm.th.nil.clone())
            .unwrap()
            .not()
            .unwrap()
            .forall("sg", tm.val_ty.clone())
            .unwrap();
        let expected = derivable(env, &av)
            .unwrap()
            .imp(body)
            .unwrap()
            .forall("A", a)
            .unwrap();
        check(&s, &expected);
    }

    /// **THE S4 GATE (design §6.7):** derive
    /// `⊢ Derivable ⌜(EQUAL (APP '(1) '(2)) '(1 2))⌝` (user computation
    /// clause + `defun_ground` fold), project through the session's
    /// soundness, and transport to the closed base-HOL model equation
    /// `⊢ app ⌜(1)⌝ ⌜(2)⌝ = ⌜(1 2)⌝`. Negative control: projecting a
    /// mismatched formula errors.
    #[test]
    fn t_defun_ground_transport() {
        let sess = app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let (_, u) = env.user("APP").unwrap();
        let anil = tm.th.nil.clone();
        let v1 = acons(tm, &aint(tm, 1), &anil); // ⌜(1)⌝
        let v2 = acons(tm, &aint(tm, 2), &anil); // ⌜(2)⌝
        let v12 = acons(tm, &aint(tm, 1), &v2); // ⌜(1 2)⌝
        let app_m = |p: &Term, q: &Term| {
            u.model
                .clone()
                .apply(p.clone())
                .unwrap()
                .apply(q.clone())
                .unwrap()
        };

        // 1. The ground model fold: ⊢ app ⌜(1)⌝ ⌜(2)⌝ = ⌜(1 2)⌝.
        let ground = defun_ground(env, "APP", &[v1.clone(), v2.clone()]).unwrap();
        check(&ground, &app_m(&v1, &v2).equals(v12.clone()).unwrap());

        // 2. The derivation via APP's computation clause, model image
        //    folded by the ground equation.
        let k = env.row("APP").unwrap();
        let der = derive_comp_folded(env, k, &[v1.clone(), v2.clone()], &ground).unwrap();
        let phi = tm
            .mk_equal(
                &tm.app(b"APP", &[tm.quote(&v1).unwrap(), tm.quote(&v2).unwrap()])
                    .unwrap(),
                &tm.quote(&v12).unwrap(),
            )
            .unwrap();
        check(&der, &derivable(env, &phi).unwrap());

        // 3. Projection through the (cached) soundness metatheorem.
        let projected = sess.project(&phi, der).unwrap();
        let sg = Term::free("sg", tm.val_ty.clone());
        let expected_proj = tm
            .eval
            .clone()
            .apply(phi.clone())
            .unwrap()
            .apply(sg)
            .unwrap()
            .equals(anil.clone())
            .unwrap()
            .not()
            .unwrap()
            .forall("sg", tm.val_ty.clone())
            .unwrap();
        check(&projected, &expected_proj);

        // 4. Transport: the closed base-HOL model equation.
        let final_thm = transport_equal(env, &projected).unwrap();
        check(&final_thm, &app_m(&v1, &v2).equals(v12.clone()).unwrap());

        // Negative control: a mismatched φ is rejected by the kernel.
        let bad_phi = tm
            .mk_equal(&tm.quote(&v1).unwrap(), &tm.quote(&v12).unwrap())
            .unwrap();
        let other = derive_plus_lit(env, 2, 2).unwrap();
        assert!(sess.project(&bad_phi, other).is_err());
    }
}

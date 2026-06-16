//! The **proof term** ([`Drv`]) and the **replay interpreter** ([`check`]).
//!
//! A `Drv` is untrusted *data*: a transcript of which kernel rules to
//! apply. It carries no soundness of its own — [`check`] replays it by
//! calling the real `covalence-core` rules, each of which re-validates.
//! A corrupt or hostile `Drv` can at worst fail to check or produce a
//! different (still kernel-valid) theorem; it can never manufacture an
//! unsound `Thm`.
//!
//! [`check`] is the *only* kernel-coupled surface here: every variant is
//! one rule call. Edit the kernel's rule set → fix the matching arm;
//! authored proofs (the `Drv` data) stay put.
//!
//! Two `Drv` variants are **tactics** — `Tauto` and `Rw` — which
//! elaborate to longer derivations at replay time (they are *not* extra
//! trust, just convenience that bottoms out in the same rules).

use covalence_core::{Term, TermKind, Thm};
use covalence_sexp::SExpr;

use super::env::Env;
use super::scope::Scope;
use super::syntax::{arity, head_sym, list, parse_term, parse_type, sym};
use super::ScriptError;

type R<T> = Result<T, ScriptError>;

/// A proof term. One constructor per kernel rule (plus the two tactics).
#[derive(Debug, Clone)]
pub enum Drv {
    // leaves
    Refl(Term),
    Assume(Term),
    Lem(Term),
    /// Reference a lemma proven earlier in the file (looked up in
    /// [`Env::lemmas`] and re-checked in-session — never trusted from
    /// disk).
    Lemma(String),
    ReducePrim(Term),
    UnfoldTermSpec(Term),
    /// `⊢ op arg = body[arg]` — unfold a unary defined constant at an
    /// argument (one β-step). Wraps `proofs::rewrite::unfold_at_1`.
    UnfoldAt1 { op: Term, arg: Term },
    /// `⊢ op a b = body[a,b]` — unfold a binary defined constant at two
    /// arguments. Wraps `proofs::rewrite::unfold_at_2`.
    UnfoldAt2 { op: Term, a: Term, b: Term },
    BetaConv(Term),
    // unary
    Sym(Box<Drv>),
    AbsRule { name: String, ty: covalence_core::Type, body: Box<Drv> },
    AllIntro { name: String, ty: covalence_core::Type, body: Box<Drv> },
    AllElim { witness: Term, body: Box<Drv> },
    ImpIntro { phi: Term, body: Box<Drv> },
    NotIntro(Box<Drv>),
    Inst { name: String, term: Term, body: Box<Drv> },
    /// Type-variable instantiation (HOL Light `INST_TYPE`) — the way a
    /// *polymorphic* lemma is applied at a concrete type.
    InstTfree { name: String, ty: covalence_core::Type, body: Box<Drv> },
    /// `⊢ f a = f b` from `⊢ a = b`.
    CongArg { f: Term, body: Box<Drv> },
    /// `⊢ f a = g a` from `⊢ f = g`.
    CongFn { arg: Term, body: Box<Drv> },
    AndElimL(Box<Drv>),
    AndElimR(Box<Drv>),
    OrIntroL { q: Term, body: Box<Drv> },
    OrIntroR { p: Term, body: Box<Drv> },
    FalseElim { p: Term, body: Box<Drv> },
    // binary
    Trans(Box<Drv>, Box<Drv>),
    MkComb(Box<Drv>, Box<Drv>),
    EqMp(Box<Drv>, Box<Drv>),
    ImpElim(Box<Drv>, Box<Drv>),
    DeductAntisym(Box<Drv>, Box<Drv>),
    AndIntro(Box<Drv>, Box<Drv>),
    NotElim(Box<Drv>, Box<Drv>),
    // ternary
    OrElim { disj: Box<Drv>, left: Box<Drv>, right: Box<Drv> },
    NatInduct { base: Box<Drv>, step: Box<Drv> },
    // tactics (elaborate to longer derivations at replay time)
    /// Prove a propositional / closed-arithmetic tautology via
    /// [`crate::init::logic::tauto`].
    Tauto(Term),
    /// Rewrite `target`'s conclusion left-to-right with the equation
    /// proved by `eqn` (congruence over every occurrence).
    Rw { eqn: Box<Drv>, target: Box<Drv> },
}

/// Replay a proof term into a kernel theorem. The sole kernel-coupled
/// function in the script layer.
pub fn check(d: &Drv, env: &Env) -> R<Thm> {
    Ok(match d {
        Drv::Refl(t) => Thm::refl(t.clone())?,
        Drv::Assume(t) => Thm::assume(t.clone())?,
        Drv::Lem(t) => Thm::lem(t.clone())?,
        Drv::Lemma(name) => env
            .lookup_lemma(name)
            .cloned()
            .ok_or_else(|| ScriptError::Unbound(format!("lemma `{name}`")))?,
        Drv::ReducePrim(t) => Thm::reduce_prim(t.clone())?,
        Drv::UnfoldTermSpec(t) => Thm::unfold_term_spec(t.clone())?,
        Drv::UnfoldAt1 { op, arg } => {
            crate::proofs::rewrite::unfold_at_1(op.clone(), arg.clone())
        }
        Drv::UnfoldAt2 { op, a, b } => {
            crate::proofs::rewrite::unfold_at_2(op.clone(), a.clone(), b.clone())
        }
        Drv::BetaConv(t) => Thm::beta_conv(t.clone())?,
        Drv::Sym(a) => check(a, env)?.sym()?,
        Drv::AbsRule { name, ty, body } => check(body, env)?.abs(name, ty.clone())?,
        Drv::AllIntro { name, ty, body } => check(body, env)?.all_intro(name, ty.clone())?,
        Drv::AllElim { witness, body } => check(body, env)?.all_elim(witness.clone())?,
        Drv::ImpIntro { phi, body } => check(body, env)?.imp_intro(phi)?,
        Drv::NotIntro(a) => check(a, env)?.not_intro()?,
        Drv::Inst { name, term, body } => check(body, env)?.inst(name, term.clone())?,
        Drv::InstTfree { name, ty, body } => check(body, env)?.inst_tfree(name, ty.clone())?,
        Drv::CongArg { f, body } => Thm::refl(f.clone())?.mk_comb(check(body, env)?)?,
        Drv::CongFn { arg, body } => check(body, env)?.mk_comb(Thm::refl(arg.clone())?)?,
        Drv::AndElimL(a) => check(a, env)?.and_elim_l()?,
        Drv::AndElimR(a) => check(a, env)?.and_elim_r()?,
        Drv::OrIntroL { q, body } => check(body, env)?.or_intro_l(q.clone())?,
        Drv::OrIntroR { p, body } => check(body, env)?.or_intro_r(p.clone())?,
        Drv::FalseElim { p, body } => check(body, env)?.false_elim(p.clone())?,
        Drv::Trans(a, b) => check(a, env)?.trans(check(b, env)?)?,
        Drv::MkComb(a, b) => check(a, env)?.mk_comb(check(b, env)?)?,
        Drv::EqMp(a, b) => check(a, env)?.eq_mp(check(b, env)?)?,
        Drv::ImpElim(a, b) => check(a, env)?.imp_elim(check(b, env)?)?,
        Drv::DeductAntisym(a, b) => check(a, env)?.deduct_antisym(check(b, env)?)?,
        Drv::AndIntro(a, b) => check(a, env)?.and_intro(check(b, env)?)?,
        Drv::NotElim(a, b) => check(a, env)?.not_elim(check(b, env)?)?,
        Drv::OrElim { disj, left, right } => {
            check(disj, env)?.or_elim(check(left, env)?, check(right, env)?)?
        }
        Drv::NatInduct { base, step } => {
            Thm::nat_induct(check(base, env)?, check(step, env)?)?
        }
        Drv::Tauto(t) => crate::init::logic::tauto(t)?,
        Drv::Rw { eqn, target } => {
            let eq = check(eqn, env)?;
            let tgt = check(target, env)?;
            let cong = rewrite_conv(tgt.concl(), &eq)?;
            cong.eq_mp(tgt)?
        }
    })
}

/// `⊢ t = t'` where `t'` is `t` with every occurrence of the equation's
/// LHS replaced by its RHS, built by congruence. Carries the equation's
/// hypotheses.
///
/// Does not descend under binders (`Abs`) — adequate for the
/// quantifier-free rewriting the tactic targets today; see SKELETONS.md.
pub(super) fn rewrite_conv(t: &Term, eq: &Thm) -> R<Thm> {
    let (lhs, _rhs) = dest_eq(eq.concl())
        .ok_or_else(|| ScriptError::Syntax("rw: equation theorem is not an `=`".into()))?;
    if *t == lhs {
        return Ok(eq.clone());
    }
    Ok(match t.kind() {
        TermKind::App(f, x) => rewrite_conv(f, eq)?.mk_comb(rewrite_conv(x, eq)?)?,
        _ => Thm::refl(t.clone())?,
    })
}

/// Destructure an `=`-headed term `App(App(Eq α, lhs), rhs)`.
fn dest_eq(t: &Term) -> Option<(Term, Term)> {
    let TermKind::App(f, rhs) = t.kind() else {
        return None;
    };
    let TermKind::App(h, lhs) = f.kind() else {
        return None;
    };
    matches!(h.kind(), TermKind::Eq(_)).then(|| (lhs.clone(), rhs.clone()))
}

// ============================================================================
// Parsing: S-expression → Drv (terms resolved against `env` + `scope`)
// ============================================================================

/// Parse a proof term. Term/type/name arguments are resolved eagerly
/// through `env`/`scope`; nested proofs recurse. Binder-introducing
/// rules (`abs-rule`, `all-intro`) extend `scope` for their sub-proof.
pub fn parse_drv(s: &SExpr, scope: &mut Scope, env: &Env) -> R<Drv> {
    let ch = list(s, "proof")?;
    let head = head_sym(ch)?;
    // `(head TERM)` / `(head NAME)` shorthands.
    let t1 = |scope: &mut Scope| parse_term(&ch[1], scope, env);
    Ok(match head {
        "refl" => {
            arity(ch, 2, "refl")?;
            Drv::Refl(t1(scope)?)
        }
        "assume" => {
            arity(ch, 2, "assume")?;
            Drv::Assume(t1(scope)?)
        }
        "lem" => {
            arity(ch, 2, "lem")?;
            Drv::Lem(t1(scope)?)
        }
        "lemma" => {
            arity(ch, 2, "lemma")?;
            Drv::Lemma(sym(&ch[1], "lemma name")?.to_string())
        }
        "reduce-prim" => {
            arity(ch, 2, "reduce-prim")?;
            Drv::ReducePrim(t1(scope)?)
        }
        "unfold-term-spec" => {
            arity(ch, 2, "unfold-term-spec")?;
            Drv::UnfoldTermSpec(t1(scope)?)
        }
        "unfold-at-1" => {
            arity(ch, 3, "unfold-at-1")?;
            Drv::UnfoldAt1 {
                op: parse_term(&ch[1], scope, env)?,
                arg: parse_term(&ch[2], scope, env)?,
            }
        }
        "unfold-at-2" => {
            arity(ch, 4, "unfold-at-2")?;
            Drv::UnfoldAt2 {
                op: parse_term(&ch[1], scope, env)?,
                a: parse_term(&ch[2], scope, env)?,
                b: parse_term(&ch[3], scope, env)?,
            }
        }
        "beta-conv" => {
            arity(ch, 2, "beta-conv")?;
            Drv::BetaConv(t1(scope)?)
        }
        "sym" => {
            arity(ch, 2, "sym")?;
            Drv::Sym(boxed(&ch[1], scope, env)?)
        }
        "not-intro" => {
            arity(ch, 2, "not-intro")?;
            Drv::NotIntro(boxed(&ch[1], scope, env)?)
        }
        "and-elim-l" => {
            arity(ch, 2, "and-elim-l")?;
            Drv::AndElimL(boxed(&ch[1], scope, env)?)
        }
        "and-elim-r" => {
            arity(ch, 2, "and-elim-r")?;
            Drv::AndElimR(boxed(&ch[1], scope, env)?)
        }
        "tauto" => {
            arity(ch, 2, "tauto")?;
            Drv::Tauto(t1(scope)?)
        }
        // binder-introducing: NAME TYPE D  (NAME is free in the sub-proof)
        "abs-rule" | "all-intro" => {
            arity(ch, 4, head)?;
            let name = sym(&ch[1], "var name")?.to_string();
            let ty = parse_type(&ch[2])?;
            scope.open();
            scope.define(name.clone(), ty.clone());
            let body = parse_drv(&ch[3], scope, env);
            scope.close();
            let body = Box::new(body?);
            if head == "abs-rule" {
                Drv::AbsRule { name, ty, body }
            } else {
                Drv::AllIntro { name, ty, body }
            }
        }
        "all-elim" => {
            arity(ch, 3, "all-elim")?;
            Drv::AllElim {
                witness: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "imp-intro" => {
            arity(ch, 3, "imp-intro")?;
            Drv::ImpIntro {
                phi: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "inst" => {
            arity(ch, 4, "inst")?;
            Drv::Inst {
                name: sym(&ch[1], "inst var")?.to_string(),
                term: parse_term(&ch[2], scope, env)?,
                body: boxed(&ch[3], scope, env)?,
            }
        }
        "inst-tfree" => {
            arity(ch, 4, "inst-tfree")?;
            Drv::InstTfree {
                name: sym(&ch[1], "inst-tfree var")?.to_string(),
                ty: parse_type(&ch[2])?,
                body: boxed(&ch[3], scope, env)?,
            }
        }
        "cong-arg" => {
            arity(ch, 3, "cong-arg")?;
            Drv::CongArg {
                f: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "cong-fn" => {
            arity(ch, 3, "cong-fn")?;
            Drv::CongFn {
                arg: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "or-intro-l" => {
            arity(ch, 3, "or-intro-l")?;
            Drv::OrIntroL {
                q: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "or-intro-r" => {
            arity(ch, 3, "or-intro-r")?;
            Drv::OrIntroR {
                p: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "false-elim" => {
            arity(ch, 3, "false-elim")?;
            Drv::FalseElim {
                p: parse_term(&ch[1], scope, env)?,
                body: boxed(&ch[2], scope, env)?,
            }
        }
        "trans" => bin(ch, scope, env, Drv::Trans)?,
        "mk-comb" => bin(ch, scope, env, Drv::MkComb)?,
        "eq-mp" => bin(ch, scope, env, Drv::EqMp)?,
        "imp-elim" => bin(ch, scope, env, Drv::ImpElim)?,
        "deduct-antisym" => bin(ch, scope, env, Drv::DeductAntisym)?,
        "and-intro" => bin(ch, scope, env, Drv::AndIntro)?,
        "not-elim" => bin(ch, scope, env, Drv::NotElim)?,
        "rw" => bin(ch, scope, env, |eqn, target| Drv::Rw { eqn, target })?,
        "or-elim" => {
            arity(ch, 4, "or-elim")?;
            Drv::OrElim {
                disj: boxed(&ch[1], scope, env)?,
                left: boxed(&ch[2], scope, env)?,
                right: boxed(&ch[3], scope, env)?,
            }
        }
        "nat-induct" => {
            arity(ch, 3, "nat-induct")?;
            Drv::NatInduct {
                base: boxed(&ch[1], scope, env)?,
                step: boxed(&ch[2], scope, env)?,
            }
        }
        other => return Err(ScriptError::Syntax(format!("unknown proof rule: {other}"))),
    })
}

fn boxed(s: &SExpr, scope: &mut Scope, env: &Env) -> R<Box<Drv>> {
    Ok(Box::new(parse_drv(s, scope, env)?))
}

fn bin(
    ch: &[SExpr],
    scope: &mut Scope,
    env: &Env,
    f: impl FnOnce(Box<Drv>, Box<Drv>) -> Drv,
) -> R<Drv> {
    arity(ch, 3, "binary rule")?;
    Ok(f(boxed(&ch[1], scope, env)?, boxed(&ch[2], scope, env)?))
}

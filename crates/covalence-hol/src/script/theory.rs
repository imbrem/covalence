//! **Declared signatures, theories, and models** — the script-layer data the
//! `#sig` / `#thy` / `#model` / `#models` directives build
//! (`docs/surface-compiler.md` §3.0–§3.0.3). This is the surface↔script
//! *fusion*: the `.cov` language gains the theory-defining forms, so the
//! `Nat` signature + theory the `models::` module hand-built in Rust can be
//! written as **declared data** and the abstract `add_comm` proof replayed
//! through it.
//!
//! # The shapes
//!
//! - [`Signature`] — a name, one **sort variable** name (the carrier `α`), and
//!   the operation symbols with their sort-var-typed templates
//!   (`zero : α`, `succ : α → α`, `add : α → α → α`). Single-sorted,
//!   first-order: a generic multi-sort / HOL-ω signature is deferred (see
//!   `SKELETONS.md`).
//! - [`Theory`] — a signature ref plus named **abstract specs** (`(#spec …)`):
//!   proof *obligations*, not postulates. Each spec is stored as its raw `SExpr`
//!   (so a model can re-elaborate it at *its* carrier) alongside the abstract
//!   formula validated against the signature.
//! - [`Model`] — a signature ref, a **carrier** type, the op **interpretation**
//!   terms (typechecked against each op's template with `α := carrier`), and the
//!   induction-handler tactic name.
//!
//! # How `#models` builds + checks the instantiated goal
//!
//! For each axiom of the theory, the goal is the abstract formula **instantiated
//! at the model**: `α := carrier`, each op symbol := the model's interpretation
//! term. This is done not by term substitution but by **re-elaborating the
//! axiom's stored `SExpr`** against a model-specific [`Env`]
//! ([`Model::axiom_env`]) where the op names resolve to the interpretation terms
//! (as consts) and the sort name resolves to the carrier type — so the existing
//! elaborator produces the instantiated goal directly. The supplied `(#by …)`
//! must prove exactly that goal (the conclusion is re-checked against it).
//!
//! On success the model's **dispatch env** ([`Model::dispatch_env`]) is built —
//! the `NatModel::env()` shape: `m.<op>` consts (the interpretations), each
//! axiom bound under its theory name (the verified `Thm`), and `m.induct`
//! registered to the model's induction tactic — exactly what `(#in M …)` opens
//! and the abstract `add_comm.cov` proof dispatches over.

use covalence_core::{Term, Type};
use covalence_sexp::SExpr;

use super::env::{ConstDef, Env};
use super::scope::Scope;
use super::{ScriptError, syntax};

type R<T> = Result<T, ScriptError>;

/// One operation of a [`Signature`]: its name and its **template** type, a
/// `Type` mentioning the signature's sort variable (e.g. `add : α → α → α`,
/// stored as `tfree(α) → tfree(α) → tfree(α)`).
#[derive(Clone)]
pub struct SigOp {
    pub name: String,
    /// The operation's type over the sort variable (`α := tfree(sort)`).
    pub ty: Type,
}

/// A **single-sorted, first-order signature**: a name, the sort variable name
/// `α`, and the typed operation symbols. The `docs/surface-compiler.md` §3.0
/// `(#sig …)` form. A generic multi-sort / kinded-family (HOL-ω) signature is
/// deferred — see `SKELETONS.md`.
#[derive(Clone)]
pub struct Signature {
    pub name: String,
    /// The single sort variable `α` (the carrier a model instantiates).
    pub sort: String,
    pub ops: Vec<SigOp>,
}

impl Signature {
    /// The op template `ty` for `name`, if present.
    fn op_ty(&self, name: &str) -> Option<&Type> {
        self.ops.iter().find(|o| o.name == name).map(|o| &o.ty)
    }

    /// An [`Env`] in which the signature's vocabulary is in scope for parsing an
    /// **abstract** formula: the sort `α` resolves to `tfree(α)` (handled by
    /// `parse_type`'s leading-`'` rule — we store the sort already prefixed) and
    /// each op resolves to a `Const` of its sort-var-typed template. Used to
    /// validate axioms at `#thy` time.
    fn abstract_env(&self, base: &Env) -> Env {
        let mut e = base.clone();
        for op in &self.ops {
            e.define_const(
                op.name.clone(),
                ConstDef::Op(Term::const_(op.name.as_str(), op.ty.clone())),
            );
        }
        // The sort name resolves to its own type variable, so a typed axiom
        // binder `(forall (a α) …)` parses (untyped binders infer it from the
        // ops). The bare-`'`-prefix rule already covers `'α`; the alias covers
        // a bare sort symbol.
        e.define_sort_alias(self.sort.clone(), Type::tfree(self.sort.as_str()));
        e
    }
}

/// One **spec** of a [`Theory`]: a named proof obligation — its name, the
/// **abstract** formula (validated against the signature), and the raw `SExpr`
/// body (kept so a model can re-elaborate it at its carrier). A spec is *not* a
/// postulate: it asserts nothing, it is a goal a model must discharge.
#[derive(Clone)]
pub struct Spec {
    pub name: String,
    /// The abstract formula `⊢-shape` term (over the signature's vocabulary).
    pub formula: Term,
    /// The raw spec body, re-elaborated per model in `#models`.
    pub body: SExpr,
}

/// A **theory**: a signature plus named abstract specs — the proof obligations
/// any model of the signature must discharge (the `docs/surface-compiler.md`
/// §3.0 `(#thy …)` form, `(#spec …)` clauses). The signature is stored inline
/// (resolved from the `(over SIG)` ref at parse time).
#[derive(Clone)]
pub struct Theory {
    pub name: String,
    pub sig: Signature,
    pub specs: Vec<Spec>,
}

/// A **model** of a signature: a carrier type, an interpretation term for each
/// op (typechecked against the op's template with `α := carrier`), and the name
/// of the induction-handler tactic. The `docs/surface-compiler.md` §3.0.3
/// `(#model …)` form. Pure semantics — *nothing about axioms*; satisfaction is
/// the separate `(#models …)` certificate.
#[derive(Clone)]
pub struct Model {
    pub name: String,
    pub sig: Signature,
    pub carrier: Type,
    /// `(op-name, interpretation term)`, in signature order.
    pub interp: Vec<(String, Term)>,
    /// The name of the model's induction handler tactic (resolved from the
    /// running env when the dispatch env is built).
    pub induct: String,
}

impl Model {
    /// An [`Env`] for elaborating an axiom **at this model**: the sort name
    /// resolves to the carrier type and each op resolves to its interpretation
    /// term (as a `Const`). Re-elaborating an abstract axiom's `SExpr` against
    /// this env yields the axiom **instantiated at the carrier** — the
    /// satisfaction goal — with no term substitution.
    fn axiom_env(&self, base: &Env) -> Env {
        let mut e = base.clone();
        for (name, term) in &self.interp {
            e.define_const(name.clone(), ConstDef::Op(term.clone()));
        }
        // The sort resolves to the carrier type. `parse_type` consults
        // `lookup_type_spec` for a bare unknown symbol — but the carrier may be
        // a built-in (`nat`) or a spec (`list unit`); we register a 0-ary type
        // alias under the sort name so `(forall (a SORT) …)` reads the carrier.
        e.define_sort_alias(self.sig.sort.clone(), self.carrier.clone());
        e
    }

    /// Build the model's **dispatch env** — the `NatModel::env()` shape that
    /// `(#in M …)` opens: each op bound as `m.<op>` (the interpretation), each
    /// verified axiom bound under its theory name, and `m.induct` registered to
    /// the model's induction tactic.
    ///
    /// `axioms` are the satisfaction-proved theorems (name → `Thm`), in the
    /// theory's axiom order; `base` supplies the induction tactic by name.
    fn dispatch_env(&self, axioms: &[super::NamedThm], base: &Env) -> R<Env> {
        let mut e = Env::empty();
        for (name, term) in &self.interp {
            e.define_const(format!("m.{name}"), ConstDef::Op(term.clone()));
        }
        for nt in axioms {
            e.define_lemma(nt.name.clone(), nt.thm.clone());
        }
        let induct = base.lookup_tactic(&self.induct).ok_or_else(|| {
            ScriptError::Unbound(format!(
                "#model {}: induction tactic `{}` is not in scope",
                self.name, self.induct
            ))
        })?;
        e.register_tactic("m.induct", induct);
        Ok(e)
    }
}

// ============================================================================
// Parsing — the four directives.
// ============================================================================

/// Parse a `(#sig NAME (sort α) (op NAME TYPE) …)` directive into a
/// [`Signature`]. The sort name is stored **already `'`-prefixed** so the op
/// templates parse it as a type variable.
pub fn parse_sig(ch: &[SExpr], env: &Env) -> R<Signature> {
    if ch.len() < 2 {
        return Err(ScriptError::Syntax(
            "#sig: expected (#sig NAME (sort α) (op …) …)".into(),
        ));
    }
    let name = syntax::sym(&ch[1], "#sig name")?.to_string();

    let mut sort: Option<String> = None;
    let mut ops: Vec<SigOp> = Vec::new();
    for clause in &ch[2..] {
        let c = syntax::list(clause, "#sig clause")?;
        match syntax::head_sym(c)? {
            "sort" => {
                syntax::arity(c, 2, "sort")?;
                if sort.is_some() {
                    return Err(ScriptError::Syntax(
                        "#sig: multi-sort signatures are not supported (one `sort` only)".into(),
                    ));
                }
                sort = Some(syntax::sym(&c[1], "sort name")?.to_string());
            }
            "op" => {
                // `op` clauses are typed against the sort, parsed *after* the
                // sort is known (below).
                if sort.is_none() {
                    return Err(ScriptError::Syntax(
                        "#sig: the `(sort …)` clause must precede the `(op …)` clauses".into(),
                    ));
                }
                let s = sort.as_ref().unwrap();
                let op = parse_op(c, s, env)?;
                ops.push(op);
            }
            other => {
                return Err(ScriptError::Syntax(format!(
                    "#sig: unknown clause `{other}` (expected `sort` or `op`)"
                )));
            }
        }
    }
    let sort = sort
        .ok_or_else(|| ScriptError::Syntax("#sig: missing the `(sort α)` clause".into()))?;
    Ok(Signature { name, sort, ops })
}

/// Parse one `(op NAME TYPE)` clause: `NAME` typed by `TYPE`, where the sort
/// symbol `sort` reads as a type variable.
fn parse_op(c: &[SExpr], sort: &str, env: &Env) -> R<SigOp> {
    syntax::arity(c, 3, "op")?;
    let name = syntax::sym(&c[1], "op name")?.to_string();
    let ty = parse_sig_type(&c[2], sort, env)?;
    Ok(SigOp { name, ty })
}

/// Parse a type in a signature/axiom context, where the bare symbol `sort`
/// denotes the sort type variable `tfree(sort)`. Everything else delegates to
/// the standard [`syntax::parse_type`] (so `(-> A B)`, `(list A)`, `nat`, … all
/// work, and other sorts could be added later).
fn parse_sig_type(s: &SExpr, sort: &str, env: &Env) -> R<Type> {
    use covalence_sexp::{Atom, SExp};
    match s {
        SExp::Atom(Atom::Symbol(n)) if n.as_str() == sort => Ok(Type::tfree(sort)),
        SExp::List(ch) => {
            // Rebuild a `(-> …)` / ctor application recursively so an inner
            // `sort` symbol still maps to the type variable.
            let head = syntax::head_sym(ch)?;
            match head {
                "fun" | "->" => {
                    if ch.len() < 3 {
                        return Err(ScriptError::Syntax("->: expected (-> A B …)".into()));
                    }
                    let mut tys = ch[1..]
                        .iter()
                        .map(|c| parse_sig_type(c, sort, env))
                        .collect::<R<Vec<_>>>()?;
                    let mut acc = tys.pop().unwrap();
                    while let Some(t) = tys.pop() {
                        acc = Type::fun(t, acc);
                    }
                    Ok(acc)
                }
                // Any other type form: no inner `sort` occurrence is supported
                // (single-sorted, the sort appears bare or in `->`). Delegate.
                _ => syntax::parse_type(s, env),
            }
        }
        _ => syntax::parse_type(s, env),
    }
}

/// Parse a `(#thy NAME (over SIG) (#spec NAME FORMULA) …)` directive into a
/// [`Theory`]. `SIG` is resolved from the signature registry in `env`. Each
/// `(#spec …)` is a proof OBLIGATION (validated against the signature), not an
/// asserted axiom.
pub fn parse_thy(ch: &[SExpr], env: &Env) -> R<Theory> {
    if ch.len() < 3 {
        return Err(ScriptError::Syntax(
            "#thy: expected (#thy NAME (over SIG) (#spec …) …)".into(),
        ));
    }
    let name = syntax::sym(&ch[1], "#thy name")?.to_string();

    let mut sig: Option<Signature> = None;
    let mut specs: Vec<Spec> = Vec::new();
    for clause in &ch[2..] {
        let c = syntax::list(clause, "#thy clause")?;
        match syntax::head_sym(c)? {
            // `(over SIG)` / `(sig SIG)` — the signature reference.
            "over" | "sig" => {
                syntax::arity(c, 2, "over")?;
                let sig_name = syntax::sym(&c[1], "signature ref")?;
                sig = Some(env.lookup_signature(sig_name).ok_or_else(|| {
                    ScriptError::Unbound(format!("#thy: signature `{sig_name}` not declared"))
                })?);
            }
            // `(#spec NAME FORMULA)` — a **proof obligation** a model must
            // discharge. *Not* a postulate: nothing is asserted, the formula is
            // merely validated against the signature; satisfaction is proved
            // separately (`#models` / the `nat.cov ⊨ nat.thy` test).
            "#spec" => {
                syntax::arity(c, 3, "#spec")?;
                let s = sig.as_ref().ok_or_else(|| {
                    ScriptError::Syntax(
                        "#thy: the `(over SIG)` clause must precede the specs".into(),
                    )
                })?;
                let ax_name = syntax::sym(&c[1], "#spec name")?.to_string();
                let body = c[2].clone();
                // Validate the abstract formula against the signature's
                // vocabulary (ops as consts, sort as a tfree).
                let aenv = s.abstract_env(env);
                let mut scope = Scope::new();
                let formula = syntax::parse_term(&body, &mut scope, &aenv)?;
                specs.push(Spec {
                    name: ax_name,
                    formula,
                    body,
                });
            }
            other => {
                return Err(ScriptError::Syntax(format!(
                    "#thy: unknown clause `{other}` (expected `over`/`sig` or `#spec`)"
                )));
            }
        }
    }
    let sig =
        sig.ok_or_else(|| ScriptError::Syntax("#thy: missing the `(over SIG)` clause".into()))?;
    Ok(Theory {
        name,
        sig,
        specs,
    })
}

/// Parse a `(#model NAME (of SIG) (carrier TY) (OP TERM) … (induct TACTIC))`
/// directive into a [`Model`]. Each op interpretation is typechecked against the
/// signature op's template with `α := carrier`.
pub fn parse_model(ch: &[SExpr], env: &Env) -> R<Model> {
    if ch.len() < 3 {
        return Err(ScriptError::Syntax(
            "#model: expected (#model NAME (of SIG) (carrier TY) (OP TERM) … (induct T))".into(),
        ));
    }
    let name = syntax::sym(&ch[1], "#model name")?.to_string();

    let mut sig: Option<Signature> = None;
    let mut carrier: Option<Type> = None;
    let mut interp: Vec<(String, Term)> = Vec::new();
    let mut induct: Option<String> = None;

    for clause in &ch[2..] {
        let c = syntax::list(clause, "#model clause")?;
        let head = syntax::head_sym(c)?;
        match head {
            "of" => {
                syntax::arity(c, 2, "of")?;
                let sig_name = syntax::sym(&c[1], "signature ref")?;
                sig = Some(env.lookup_signature(sig_name).ok_or_else(|| {
                    ScriptError::Unbound(format!("#model: signature `{sig_name}` not declared"))
                })?);
            }
            "carrier" => {
                syntax::arity(c, 2, "carrier")?;
                carrier = Some(syntax::parse_type(&c[1], env)?);
            }
            "induct" => {
                syntax::arity(c, 2, "induct")?;
                induct = Some(syntax::sym(&c[1], "induct tactic ref")?.to_string());
            }
            // Otherwise: `(OP TERM)` — an op interpretation. Validated below
            // (needs the signature + carrier in hand).
            op_name => {
                let s = sig.as_ref().ok_or_else(|| {
                    ScriptError::Syntax(
                        "#model: the `(of SIG)` clause must precede the op interpretations".into(),
                    )
                })?;
                let cr = carrier.as_ref().ok_or_else(|| {
                    ScriptError::Syntax(
                        "#model: the `(carrier TY)` clause must precede the op interpretations"
                            .into(),
                    )
                })?;
                syntax::arity(c, 2, op_name)?;
                let template = s.op_ty(op_name).ok_or_else(|| {
                    ScriptError::Syntax(format!(
                        "#model: `{op_name}` is not an operation of signature `{}`",
                        s.name
                    ))
                })?;
                // Elaborate the interpretation term and check its type matches
                // the op's template with `α := carrier`.
                let mut scope = Scope::new();
                let term = syntax::parse_term(&c[1], &mut scope, env)?;
                let got = term.type_of()?;
                let want = inst_sort(template, &s.sort, cr);
                if got != want {
                    return Err(ScriptError::Syntax(format!(
                        "#model {name}: interpretation of `{op_name}` has type `{got}`, \
                         expected `{want}` (op template at carrier)"
                    )));
                }
                interp.push((op_name.to_string(), term));
            }
        }
    }

    let sig =
        sig.ok_or_else(|| ScriptError::Syntax("#model: missing the `(of SIG)` clause".into()))?;
    let carrier = carrier
        .ok_or_else(|| ScriptError::Syntax("#model: missing the `(carrier TY)` clause".into()))?;
    let induct = induct
        .ok_or_else(|| ScriptError::Syntax("#model: missing the `(induct TACTIC)` clause".into()))?;
    // Every signature op must be interpreted.
    for op in &sig.ops {
        if !interp.iter().any(|(n, _)| *n == op.name) {
            return Err(ScriptError::Syntax(format!(
                "#model {name}: missing interpretation for op `{}`",
                op.name
            )));
        }
    }
    Ok(Model {
        name,
        sig,
        carrier,
        interp,
        induct,
    })
}

/// Substitute the sort type variable `α := carrier` in a template type.
fn inst_sort(template: &Type, sort: &str, carrier: &Type) -> Type {
    covalence_core::subst::subst_tfree_in_type(template, sort, carrier)
}

// ============================================================================
// `#models` — certify satisfaction, then build the dispatch env.
// ============================================================================

/// Execute `(#models M T (axname (#by …)) …)`: prove every axiom of theory `T`
/// at model `M`'s carrier and return `(dispatch_env, [verified theorems])`.
///
/// For each axiom, the **goal** is the abstract formula re-elaborated against
/// `M`'s [`axiom_env`](Model::axiom_env) (`α := carrier`, op := interpretation),
/// and the supplied proof must conclude exactly it. A transitional
/// `(from WITNESS)` clause instead imports a host-supplied env carrying the
/// axioms already proved (so a heavy Rust proof — `models::unary` — need not be
/// ported to `.cov`); see `SKELETONS.md`.
pub async fn run_models(
    model: &Model,
    theory: &Theory,
    clauses: &[SExpr],
    base: &Env,
) -> R<(Env, Vec<super::NamedThm>)> {
    if model.sig.name != theory.sig.name {
        return Err(ScriptError::Syntax(format!(
            "#models: model `{}` is of signature `{}`, but theory `{}` is over `{}`",
            model.name, model.sig.name, theory.name, theory.sig.name
        )));
    }

    // Transitional witness form: `(from WITNESS)` — pull the axioms from a
    // host-supplied imported env instead of proving them inline.
    if clauses.len() == 1
        && let SExpr::List(c) = &clauses[0]
        && syntax::head_sym(c)? == "from"
    {
        syntax::arity(c, 2, "from")?;
        let witness = syntax::sym(&c[1], "witness env name")?;
        return models_from_witness(model, theory, witness, base).await;
    }

    let aenv = model.axiom_env(base);
    let mut verified: Vec<super::NamedThm> = Vec::new();
    for ax in &theory.specs {
        // Find the clause `(axname (#by …))` for this axiom.
        let clause = clauses
            .iter()
            .find_map(|c| match c {
                SExpr::List(items)
                    if items.first().and_then(|x| x.as_symbol()) == Some(ax.name.as_str()) =>
                {
                    Some(items)
                }
                _ => None,
            })
            .ok_or_else(|| {
                ScriptError::Syntax(format!(
                    "#models {}: missing a proof for spec `{}`",
                    model.name, ax.name
                ))
            })?;
        syntax::arity(clause, 2, &ax.name)?;
        // The instantiated goal: re-elaborate the abstract axiom at the carrier.
        let mut scope = Scope::new();
        let goal = syntax::parse_term(&ax.body, &mut scope, &aenv)?;
        let thm = super::tactic::prove(&goal, &clause[1], &mut scope, &aenv).await?;
        if thm.concl() != &goal {
            return Err(ScriptError::ConclMismatch {
                name: format!("{}.{}", model.name, ax.name),
                expected: format!("{goal}"),
                got: format!("{}", thm.concl()),
            });
        }
        verified.push(super::NamedThm {
            name: ax.name.clone(),
            thm,
        });
    }

    let env = model.dispatch_env(&verified, base)?;
    Ok((env, verified))
}

/// `(#models M T (from WITNESS))` — the transitional host-witness path. The
/// imported env `WITNESS` carries the four axioms proved under their theory
/// names (e.g. `models::unary`'s Rust proofs); we read each verified `Thm` out,
/// re-check its conclusion against the instantiated goal, and build the dispatch
/// env. Keeps a heavy Rust proof in place until ported to `.cov`.
async fn models_from_witness(
    model: &Model,
    theory: &Theory,
    witness: &str,
    base: &Env,
) -> R<(Env, Vec<super::NamedThm>)> {
    let wenv = base
        .get_import(witness)
        .cloned()
        .ok_or_else(|| ScriptError::Unbound(format!("#models: witness env `{witness}` not imported")))?;
    let aenv = model.axiom_env(base);
    let mut verified: Vec<super::NamedThm> = Vec::new();
    for ax in &theory.specs {
        let thm = wenv
            .lookup_lemma(&ax.name)
            .await
            .ok_or_else(|| {
                ScriptError::Unbound(format!(
                    "#models (from {witness}): the witness env has no spec `{}`",
                    ax.name
                ))
            })??;
        // Re-check the witnessed theorem proves the instantiated axiom goal.
        let mut scope = Scope::new();
        let goal = syntax::parse_term(&ax.body, &mut scope, &aenv)?;
        if thm.concl() != &goal {
            return Err(ScriptError::ConclMismatch {
                name: format!("{}.{} (from {witness})", model.name, ax.name),
                expected: format!("{goal}"),
                got: format!("{}", thm.concl()),
            });
        }
        verified.push(super::NamedThm {
            name: ax.name.clone(),
            thm,
        });
    }
    let env = model.dispatch_env(&verified, base)?;
    Ok((env, verified))
}

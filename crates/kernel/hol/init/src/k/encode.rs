//! **KORE pattern → HOL term** — the reified-syntax encoder the K-frontend
//! lowering sits on ([`super::reduce`] lowers a rule set's rewrite rules to
//! clauses over *these* terms).
//!
//! ## The encoding: an uninterpreted free term algebra over `nat`
//!
//! Exactly the recipe [`crate::wasm::encode`] uses for SpecTec and
//! [`crate::metalogic::mm_database`] uses for Metamath, specialised to KORE
//! configuration terms. The carrier is `Φ = `[`Type::nat`]`()` and every node is
//! built from two kinds of uninterpreted free variable:
//!
//! - one binary combinator `app : nat → nat → nat` ([`app`]) that attaches an
//!   argument to a node head;
//! - one `nat` **constant** per KORE symbol / domain value ([`con`]);
//! - each KORE **element variable** `X` is the plain free var `k$v$X : nat`
//!   ([`metavar`]) — the metavariable a rewrite rule's clause `∀`-binds.
//!
//! A KORE application `sym{…}(a, b)` encodes to `app (app k$c$sym ⌜a⌝) ⌜b⌝`: the
//! constant tags the node and successive `app`s attach the encoded children.
//! Distinct symbols are distinct leaves, so distinct patterns encode to distinct
//! trees.
//!
//! ## Why substitution = `all_elim`
//!
//! Because `app` and the `k$c$…` constants are *uninterpreted* and element
//! variables are *variables*, HOL's capture-avoiding substitution of `⌜arg⌝` for
//! `k$v$X` in a rule schema is syntactically identical to KORE substitution — so
//! a rule clause instantiates by [`all_elim`](covalence_hol_eval::derived::DerivedRules::all_elim)
//! on the nose. This is what makes [`super::reduce`] a rule set the generic
//! [`crate::metalogic`] engine drives unchanged.
//!
//! ## Scope (F0)
//!
//! Only the fragment of KORE that appears in a *configuration term* — element
//! variables, symbol applications, and domain values — is encoded here. Set
//! variables, the logical connectives (`\and`/`\rewrites`/…), and the `\dv` sort
//! are collapsed or unsupported; see `SKELETONS.md`. Sorts are dropped from the
//! encoding (a symbol's identity, not its sort parameters, distinguishes it).
//!
//! ## Faithfulness, not soundness
//!
//! Nothing here is trusted: derivability is a purely syntactic HOL predicate and
//! the kernel re-checks every step, so an encoding *collision* could only ever
//! lose faithfulness, never mint a false `Thm`.

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type};
use covalence_k::ast::Pattern;

use crate::init::ext::TermExt;

/// The reified-syntax carrier `Φ` for the free term algebra: plain `nat`.
pub fn phi() -> Type {
    Type::nat()
}

/// The uninterpreted binary combinator `app : nat → nat → nat`. Cached once: it
/// is the single most-cloned node in the encoding.
fn app_fn() -> Term {
    static APP: LazyLock<Term> = LazyLock::new(|| {
        Term::free(
            "k$app",
            Type::fun(Type::nat(), Type::fun(Type::nat(), Type::nat())),
        )
    });
    APP.clone()
}

/// `app(a, b)` — attach argument `b` to node head `a`.
pub fn app(a: Term, b: Term) -> Result<Term> {
    app_fn().apply(a)?.apply(b)
}

/// The `app` combinator itself (`k$app : Φ→Φ→Φ`) — the one the
/// [`crate::metalogic::rewrite::RewriteRelation`] congruence clauses range over.
pub fn app_combinator() -> Term {
    app_fn()
}

/// Render an encoded `Φ`-term back to readable K-ish text (`sym(a, b)`), the
/// inverse of [`encode_pattern`] over the app/con/metavar fragment — for showing
/// a reduced normal form. Unrecognised terms render as `?`.
pub fn render(t: &Term) -> String {
    // Walk the `app` spine: app(app(head, a1), a2)… collects head + args.
    let mut args_rev = Vec::new();
    let mut cur = t;
    while let Some((f, x)) = cur.as_app() {
        // `f` should itself be `app(app_fn, head-or-inner)`; peel one `app`.
        if let Some((g, a)) = f.as_app()
            && g == &app_fn()
        {
            args_rev.push(x);
            cur = a;
            continue;
        }
        break;
    }
    args_rev.reverse();
    let head = render_leaf(cur);
    if args_rev.is_empty() {
        head
    } else {
        let inner: Vec<String> = args_rev.iter().map(|a| render(a)).collect();
        format!("{head}({})", inner.join(", "))
    }
}

/// Render a leaf constant/metavariable to its source name.
fn render_leaf(t: &Term) -> String {
    if let Some(v) = t.as_free() {
        let n = v.name();
        if let Some(sym) = n.strip_prefix("k$c$sym.") {
            return sym.to_string();
        }
        if let Some(dv) = n.strip_prefix("k$c$dv.") {
            return dv.to_string();
        }
        if let Some(s) = n.strip_prefix("k$c$str.") {
            return format!("{s:?}");
        }
        if let Some(mv) = n.strip_prefix("k$v$") {
            return mv.to_string();
        }
        if let Some(c) = n.strip_prefix("k$c$") {
            return c.to_string();
        }
    }
    "?".to_string()
}

/// A KORE **symbol / atom** constant `k$c$<name> : nat`.
pub fn con(name: impl AsRef<str>) -> Term {
    Term::free(format!("k$c${}", name.as_ref()), phi())
}

/// The HOL free-variable name of a KORE **element variable** `<id>` — the mangled
/// leaf `k$v$<id>` that [`metavar`] builds and that its rule's clause `∀`-binds
/// (so [`super::reduce`] must quantify over *this* name, not the raw id).
pub fn metavar_name(id: impl AsRef<str>) -> String {
    format!("k$v${}", id.as_ref())
}

/// A KORE **element variable** `k$v$<id> : nat` — a leaf to be `∀`-bound in its
/// rule's clause (and instantiated by `all_elim`).
pub fn metavar(id: impl AsRef<str>) -> Term {
    Term::free(metavar_name(id), phi())
}

/// Tag an encoded judgement body with its **relation**: `app(k$c$rel.<R>, body)`.
/// Mirrors [`crate::wasm::encode::tag`]; lets one combined rule set mix relations
/// and lets a cross-relation premise be `d (rel.<R'> ⌜e⌝)` under one shared `d`.
pub fn tag(rel: impl AsRef<str>, body: Term) -> Result<Term> {
    app(con(format!("rel.{}", rel.as_ref())), body)
}

/// The **`Step` judgement** body relating two configuration terms `lhs`, `rhs`:
/// `app(app(k$c$k.step, ⌜lhs⌝), ⌜rhs⌝)` — a binary node under the `k.step`
/// head. [`super::reduce`] wraps this in [`tag`] `"Step"`.
pub fn step_body(lhs: &Pattern, rhs: &Pattern) -> Result<Term> {
    let node = app(con("k.step"), encode_pattern(lhs)?)?;
    app(node, encode_pattern(rhs)?)
}

fn encode_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("k::encode: {}", msg.into()))
}

/// `app(app(… app(head, ⌜child₀⌝) …), ⌜childₙ⌝)` — a node with the given head
/// constant and encoded child spine.
fn spine(head: Term, children: &[&Pattern]) -> Result<Term> {
    let mut acc = head;
    for c in children {
        acc = app(acc, encode_pattern(c)?)?;
    }
    Ok(acc)
}

/// Encode a KORE configuration [`Pattern`] into its reified `Φ = nat` term.
///
/// Supported (the F0 configuration fragment): [`Pattern::EVar`] (→ metavariable),
/// [`Pattern::App`] (→ tagged node over encoded args; sorts dropped),
/// [`Pattern::DV`] and [`Pattern::String`] (→ distinct literal constants). Other
/// patterns — set variables and the logical connectives — are not part of a
/// configuration term and are a clean error here (see `SKELETONS.md`).
pub fn encode_pattern(p: &Pattern) -> Result<Term> {
    match p {
        Pattern::EVar(id, _sort) => Ok(metavar(id)),
        Pattern::App { symbol, args, .. } => {
            let children: Vec<&Pattern> = args.iter().collect();
            spine(con(format!("sym.{symbol}")), &children)
        }
        // Domain values and string literals are distinct nullary constants keyed
        // by their raw payload (`\dv{SortInt{}}("0")` stays the atom `0`).
        Pattern::DV(_sort, lit) => Ok(con(format!("dv.{lit}"))),
        Pattern::String(s) => Ok(con(format!("str.{s}"))),
        other => Err(encode_err(format!(
            "pattern `{}` is not a configuration term (F0 encodes evar/app/dv only)",
            pattern_head(other)
        ))),
    }
}

/// Collect a rule's element variables (free [`Pattern::EVar`] ids reachable
/// through the configuration fragment) in first-seen order — the
/// universal-quantifier order of its clause (see [`super::reduce`]). Skips the
/// non-configuration patterns [`encode_pattern`] rejects.
pub fn collect_metavars(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::EVar(id, _) => push_unique(out, id.as_str()),
        Pattern::App { args, .. } => {
            for a in args {
                collect_metavars(a, out);
            }
        }
        _ => {}
    }
}

/// Append `id` to `out` if not already present (first-seen dedup).
fn push_unique(out: &mut Vec<String>, id: &str) {
    if !out.iter().any(|s| s == id) {
        out.push(id.to_string());
    }
}

/// The element variables of a rewrite rule (its LHS then RHS), in first-seen
/// order — the `∀`/instantiation order its clause quantifies over.
pub fn rule_metavars(lhs: &Pattern, rhs: &Pattern) -> Vec<String> {
    let mut order = Vec::new();
    collect_metavars(lhs, &mut order);
    collect_metavars(rhs, &mut order);
    order
}

/// Substitute each element-variable leaf `k$v$<id>` in an encoded term by the
/// corresponding `args[i]` (in the given `order`) — the term-level analogue of
/// instantiating a rule clause with `all_elim`. `args` must match `order` in
/// length. Used to recover the concrete endpoint configs of a fired rule.
pub fn subst_metavars(t: &Term, order: &[String], args: &[Term]) -> Result<Term> {
    if args.len() != order.len() {
        return Err(encode_err(format!(
            "expected {} argument(s) for the rule's element variables, got {}",
            order.len(),
            args.len()
        )));
    }
    let mut t = t.clone();
    for (mv, a) in order.iter().zip(args) {
        let var = covalence_core::Var::new(metavar_name(mv), phi());
        t = covalence_core::subst::subst_free(&t, &var, a);
    }
    Ok(t)
}

/// A short head name for error messages.
fn pattern_head(p: &Pattern) -> &'static str {
    match p {
        Pattern::EVar(..) => "element variable",
        Pattern::SVar(..) => "set variable",
        Pattern::String(_) => "string literal",
        Pattern::App { .. } => "application",
        Pattern::Top(_) => "\\top",
        Pattern::Bottom(_) => "\\bottom",
        Pattern::Not(..) => "\\not",
        Pattern::And(..) => "\\and",
        Pattern::Or(..) => "\\or",
        Pattern::Implies(..) => "\\implies",
        Pattern::Iff(..) => "\\iff",
        Pattern::Exists { .. } => "\\exists",
        Pattern::Forall { .. } => "\\forall",
        Pattern::Mu { .. } => "\\mu",
        Pattern::Nu { .. } => "\\nu",
        Pattern::Ceil { .. } => "\\ceil",
        Pattern::Floor { .. } => "\\floor",
        Pattern::Equals { .. } => "\\equals",
        Pattern::In { .. } => "\\in",
        Pattern::Next(..) => "\\next",
        Pattern::Rewrites(..) => "\\rewrites",
        Pattern::DV(..) => "\\dv",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_k::ast::Sort;

    fn evar(id: &str) -> Pattern {
        Pattern::EVar(id.into(), Sort::App("SortK".into(), vec![]))
    }
    fn app_pat(sym: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::App {
            symbol: sym.into(),
            sorts: vec![],
            args,
        }
    }

    #[test]
    fn evar_and_symbol_are_distinct_leaves() {
        assert_ne!(
            encode_pattern(&evar("X")).unwrap(),
            encode_pattern(&evar("Y")).unwrap()
        );
        assert_ne!(metavar("X"), con("sym.X"));
    }

    #[test]
    fn distinct_symbols_give_distinct_trees() {
        let a = app_pat("f", vec![evar("X")]);
        let b = app_pat("g", vec![evar("X")]);
        assert_ne!(encode_pattern(&a).unwrap(), encode_pattern(&b).unwrap());
    }

    #[test]
    fn encoding_is_well_typed_nat() {
        let p = app_pat("cons", vec![evar("X"), app_pat("nil", vec![])]);
        assert_eq!(encode_pattern(&p).unwrap().type_of().unwrap(), phi());
    }

    #[test]
    fn dv_and_string_are_distinct_constants() {
        let zero = Pattern::DV(Sort::App("SortInt".into(), vec![]), "0".into());
        let one = Pattern::DV(Sort::App("SortInt".into(), vec![]), "1".into());
        assert_ne!(
            encode_pattern(&zero).unwrap(),
            encode_pattern(&one).unwrap()
        );
        // A domain value and a same-text application symbol don't collide.
        assert_ne!(
            encode_pattern(&zero).unwrap(),
            encode_pattern(&app_pat("0", vec![])).unwrap()
        );
    }

    #[test]
    fn metavars_collected_in_first_seen_order() {
        let p = app_pat("f", vec![evar("B"), evar("A"), evar("B")]);
        let mut mv = Vec::new();
        collect_metavars(&p, &mut mv);
        assert_eq!(mv, vec!["B".to_string(), "A".to_string()]);
    }

    #[test]
    fn non_config_pattern_is_rejected() {
        let bad = Pattern::Top(Sort::App("SortK".into(), vec![]));
        assert!(encode_pattern(&bad).is_err());
    }

    #[test]
    fn step_body_pairs_two_configs() {
        let lhs = app_pat(
            "count",
            vec![Pattern::DV(Sort::App("SortInt".into(), vec![]), "0".into())],
        );
        let rhs = app_pat("done", vec![]);
        let body = step_body(&lhs, &rhs).unwrap();
        assert_eq!(body.type_of().unwrap(), phi());
    }
}

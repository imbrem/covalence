//! **SpecTec expression → HOL term** — the reified-syntax encoder every other
//! part of the WASM-spec front end sits on ([`super::relation`] lowers a `rel`'s
//! rules to clauses over *these* terms; a later `function`/`grammar` layer will
//! reuse the same encoding).
//!
//! ## The encoding: an uninterpreted free term algebra over `nat`
//!
//! Exactly the recipe [`crate::metalogic::mm_database`] uses for Metamath, but
//! **tree-structured** (SpecTec expressions are trees, not token sequences).
//! The carrier is `Φ = `[`Type::nat`]`()` and every node is built from two kinds
//! of uninterpreted free variable:
//!
//! - one binary combinator `app : nat → nat → nat` (`app_fn`) that attaches an
//!   argument to a node head;
//! - one `nat` **constant** per SpecTec constructor/atom (`st$c$…`, [`con`]);
//! - each SpecTec **variable** (a rule metavariable) `x` is the plain free var
//!   `st$v$x : nat` ([`metavar`]).
//!
//! A node `f(a, b)` encodes to `app (app st$c$f ⌜a⌝) ⌜b⌝`: the constant tags the
//! node and successive `app`s attach the encoded children. Distinct constructors
//! are distinct leaves, so distinct expressions encode to distinct trees.
//!
//! ## Why substitution = `all_elim` (the key idea)
//!
//! Because `app` and the `st$c$…` constants are *uninterpreted* and the
//! metavariables are *variables*, HOL's capture-avoiding substitution of
//! `⌜arg⌝` for `st$v$x` in `⌜schema⌝` is syntactically identical to SpecTec
//! metavariable substitution. So a rule clause `∀ x…. premises ⟹ d ⌜concl⌝`
//! instantiates by [`Thm::all_elim`](covalence_core::Thm::all_elim) on the nose — no denotation, no β-redex,
//! no normalisation. This is what makes [`super::relation`] a rule set the
//! generic [`crate::metalogic`] engine drives unchanged.
//!
//! ## Shape: one source of truth
//!
//! Both [`encode_exp`] and [`collect_metavars`] route through `shape`, which
//! maps a `SpecTecExp` to a tag plus the child sub-expressions the encoding
//! exposes. So the metavariables a clause quantifies over are *exactly* those in
//! its encoding — no vacuous binders, no free leaks.
//!
//! ## Faithfulness, not soundness
//!
//! Nothing here is trusted: derivability is a purely syntactic HOL predicate and
//! the kernel re-checks every step, so an encoding *collision* — two distinct
//! SpecTec expressions mapping to one term — could only ever lose completeness /
//! faithfulness, never mint a false `Thm`. Some positions are **coarsely tagged**
//! (iteration binders, `upd`/`ext` paths, non-expression `call` arguments, `sub`
//! types are dropped from the tag/children); those approximations are recorded in
//! `SKELETONS.md`.

use std::sync::LazyLock;

use covalence_core::{Result, Term, Type};
use covalence_spectec::ast::{
    MixOp, SpecTecArg, SpecTecExp, SpecTecExpField, SpecTecIter, SpecTecNum, SpecTecPath,
};

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
            "st$app",
            Type::fun(Type::nat(), Type::fun(Type::nat(), Type::nat())),
        )
    });
    APP.clone()
}

/// `app(a, b)` — attach argument `b` to node head `a`.
fn app(a: Term, b: Term) -> Result<Term> {
    app_fn().apply(a)?.apply(b)
}

/// A SpecTec **constructor / atom** constant `st$c$<name> : nat`.
pub fn con(name: impl AsRef<str>) -> Term {
    Term::free(format!("st$c${}", name.as_ref()), phi())
}

/// The HOL free-variable name of a SpecTec **metavariable** `<id>` — the mangled
/// leaf `st$v$<id>` that [`metavar`] builds and that its rule's clause `∀`-binds
/// (so [`super::relation`] must quantify over *this* name, not the raw id).
pub fn metavar_name(id: impl AsRef<str>) -> String {
    format!("st$v${}", id.as_ref())
}

/// A SpecTec **metavariable** `st$v$<id> : nat` — a leaf to be `∀`-bound in its
/// rule's clause (and instantiated by [`Thm::all_elim`](covalence_core::Thm::all_elim)).
pub fn metavar(id: impl AsRef<str>) -> Term {
    Term::free(metavar_name(id), phi())
}

/// A stable string key for a mixfix operator (`%`-joined fragments), naming the
/// `case`/`field` constructor it introduces.
pub fn mixop_key(op: &MixOp) -> String {
    op.fragments().join("%")
}

/// Tag an encoded judgement body with its **relation**: `app(st$c$rel.<R>, body)`.
/// This is what lets one combined rule set mix judgements of many relations —
/// a cross-relation premise `R'(e)` is just `d (rel.<R'> ⌜e⌝)` under the same `d`
/// (see [`super::relation::spec_rule_set`]).
pub fn tag(rel: impl AsRef<str>, body: Term) -> Result<Term> {
    app(con(format!("rel.{}", rel.as_ref())), body)
}

/// `app(app(… app(head, ⌜child₀⌝) …), ⌜childₙ⌝)` — a node with the given head
/// constant and encoded child spine.
fn spine(head: Term, children: &[&SpecTecExp]) -> Result<Term> {
    let mut acc = head;
    for c in children {
        acc = app(acc, encode_exp(c)?)?;
    }
    Ok(acc)
}

/// The structural view of an expression: a leaf constant, a metavariable, or a
/// tagged node with the child sub-expressions the encoding exposes.
enum Shape<'a> {
    /// A metavariable `<id>`.
    Var(&'a str),
    /// A nullary leaf tagged `<tag>` (`st$c$<tag>`).
    Leaf(String),
    /// A node tagged `<tag>` over encoded children.
    Node(String, Vec<&'a SpecTecExp>),
    /// A record `{ field.<key> e … }` — bespoke (per-field wrapper constants).
    Struct(&'a [SpecTecExpField]),
}

/// A `nat`/`int` literal key (`num.<kind>.<v>`).
fn num_key(n: &SpecTecNum) -> String {
    match n {
        SpecTecNum::Nat(u) => format!("num.nat.{u}"),
        SpecTecNum::Int(i) => format!("num.int.{i}"),
        SpecTecNum::Rat(s) => format!("num.rat.{s}"),
        SpecTecNum::Real(s) => format!("num.real.{s}"),
    }
}

fn iter_key(it: &SpecTecIter) -> &'static str {
    match it {
        SpecTecIter::Opt => "opt",
        SpecTecIter::List => "list",
        SpecTecIter::List1 => "list1",
        SpecTecIter::ListN { .. } => "listn",
    }
}

/// A coarse tag for an access path (index/slice sub-expressions are dropped —
/// see the faithfulness note).
fn path_key(p: &SpecTecPath) -> String {
    match p {
        SpecTecPath::Root => "root".into(),
        SpecTecPath::Idx { p1, .. } => format!("{}.idx", path_key(p1)),
        SpecTecPath::Slice { p1, .. } => format!("{}.slice", path_key(p1)),
        SpecTecPath::Dot { p1, at } => format!("{}.dot.{}", path_key(p1), mixop_key(at)),
    }
}

/// The expression arguments of a `call` (non-expression arguments — types, defs,
/// grammars — are dropped from the child spine; see the faithfulness note).
fn call_exp_args(args: &[SpecTecArg]) -> Vec<&SpecTecExp> {
    args.iter()
        .filter_map(|a| match a {
            SpecTecArg::Exp { e } => Some(e),
            _ => None,
        })
        .collect()
}

/// Decompose an expression into its [`Shape`]. Total over `SpecTecExp`.
fn shape(e: &SpecTecExp) -> Shape<'_> {
    use SpecTecExp as E;
    match e {
        E::Var { id } => Shape::Var(id),
        E::Bool { b } => Shape::Leaf(format!("bool.{b}")),
        E::Num { n } => Shape::Leaf(num_key(n)),
        E::Text { t } => Shape::Leaf(format!("text.{t}")),
        E::Un { op, e2, .. } => Shape::Node(format!("un.{op:?}"), vec![e2]),
        E::Bin { op, e1, e2, .. } => Shape::Node(format!("bin.{op:?}"), vec![e1, e2]),
        E::Cmp { op, e1, e2, .. } => Shape::Node(format!("cmp.{op:?}"), vec![e1, e2]),
        E::Idx { e1, e2 } => Shape::Node("idx".into(), vec![e1, e2]),
        E::Slice { e1, e2, e3 } => Shape::Node("slice".into(), vec![e1, e2, e3]),
        E::Upd { e1, path, e2 } => Shape::Node(format!("upd.{}", path_key(path)), vec![e1, e2]),
        E::Ext { e1, path, e2 } => Shape::Node(format!("ext.{}", path_key(path)), vec![e1, e2]),
        E::Str { efs } => Shape::Struct(efs),
        E::Dot { e1, at } => Shape::Node(format!("dot.{}", mixop_key(at)), vec![e1]),
        E::Comp { e1, e2 } => Shape::Node("comp".into(), vec![e1, e2]),
        E::Mem { e1, e2 } => Shape::Node("mem".into(), vec![e1, e2]),
        E::Len { e1 } => Shape::Node("len".into(), vec![e1]),
        E::Tup { es } => Shape::Node("tup".into(), es.iter().collect()),
        E::Call { x, as1 } => Shape::Node(format!("call.{x}"), call_exp_args(as1)),
        E::Iter { e1, it, .. } => Shape::Node(format!("iter.{}", iter_key(it)), vec![e1]),
        E::Proj { e1, i } => Shape::Node(format!("proj.{i}"), vec![e1]),
        E::Case { op, e1 } => Shape::Node(format!("case.{}", mixop_key(op)), vec![e1]),
        E::Uncase { e1, op } => Shape::Node(format!("uncase.{}", mixop_key(op)), vec![e1]),
        E::Opt { eo } => match eo {
            None => Shape::Leaf("opt.none".into()),
            Some(inner) => Shape::Node("opt.some".into(), vec![inner]),
        },
        E::Unopt { e1 } => Shape::Node("unopt".into(), vec![e1]),
        E::List { es } => Shape::Node("list".into(), es.iter().collect()),
        E::Lift { e1 } => Shape::Node("lift".into(), vec![e1]),
        E::Cat { e1, e2 } => Shape::Node("cat".into(), vec![e1, e2]),
        E::Cvt { nt1, nt2, e1 } => Shape::Node(format!("cvt.{nt1:?}.{nt2:?}"), vec![e1]),
        E::Sub { e1, .. } => Shape::Node("sub".into(), vec![e1]),
    }
}

/// Encode a SpecTec expression into its reified `Φ = nat` term. Total over
/// `SpecTecExp` (coarse-tagging the positions noted in the module docs).
pub fn encode_exp(e: &SpecTecExp) -> Result<Term> {
    match shape(e) {
        Shape::Var(id) => Ok(metavar(id)),
        Shape::Leaf(tag) => Ok(con(tag)),
        Shape::Node(tag, children) => spine(con(tag), &children),
        Shape::Struct(efs) => {
            let mut acc = con("struct");
            for SpecTecExpField::Field { at, e } in efs {
                let field = app(con(format!("field.{}", mixop_key(at))), encode_exp(e)?)?;
                acc = app(acc, field)?;
            }
            Ok(acc)
        }
    }
}

/// Collect a rule's metavariables (free [`SpecTecExp::Var`] ids) in first-seen
/// order — the universal-quantifier order of its clause (see [`super::relation`]).
/// Routes through `shape`, so it sees exactly the positions [`encode_exp`]
/// encodes.
pub fn collect_metavars(e: &SpecTecExp, out: &mut Vec<String>) {
    match shape(e) {
        Shape::Var(id) => {
            if !out.iter().any(|s| s == id) {
                out.push(id.to_owned());
            }
        }
        Shape::Leaf(_) => {}
        Shape::Node(_, children) => {
            for c in children {
                collect_metavars(c, out);
            }
        }
        Shape::Struct(efs) => {
            for SpecTecExpField::Field { e, .. } in efs {
                collect_metavars(e, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }

    #[test]
    fn metavar_and_const_are_distinct_leaves() {
        assert_ne!(
            encode_exp(&var("x")).unwrap(),
            encode_exp(&var("y")).unwrap()
        );
        assert_ne!(metavar("x"), con("x"));
    }

    #[test]
    fn distinct_constructors_give_distinct_trees() {
        let tup = SpecTecExp::Tup {
            es: vec![var("a"), var("b")],
        };
        let list = SpecTecExp::List {
            es: vec![var("a"), var("b")],
        };
        assert_ne!(encode_exp(&tup).unwrap(), encode_exp(&list).unwrap());
    }

    #[test]
    fn encoding_is_well_typed_nat() {
        let e = SpecTecExp::Tup {
            es: vec![var("a"), SpecTecExp::Opt { eo: None }],
        };
        let t = encode_exp(&e).unwrap();
        assert_eq!(t.type_of().unwrap(), phi());
    }

    #[test]
    fn metavars_collected_in_first_seen_order() {
        let e = SpecTecExp::Tup {
            es: vec![var("b"), var("a"), var("b")],
        };
        let mut mv = Vec::new();
        collect_metavars(&e, &mut mv);
        assert_eq!(mv, vec!["b".to_string(), "a".to_string()]);
    }

    #[test]
    fn broadened_constructors_encode_and_are_well_typed() {
        // iter / cat / sub / struct — the previously-unsupported buckets.
        let iter = SpecTecExp::Iter {
            e1: Box::new(var("x")),
            it: SpecTecIter::List,
            xes: vec![],
        };
        let cat = SpecTecExp::Cat {
            e1: Box::new(var("a")),
            e2: Box::new(iter.clone()),
        };
        let t = encode_exp(&cat).unwrap();
        assert_eq!(t.type_of().unwrap(), phi());
        // metavars reach through iter and cat.
        let mut mv = Vec::new();
        collect_metavars(&cat, &mut mv);
        assert_eq!(mv, vec!["a".to_string(), "x".to_string()]);
    }
}

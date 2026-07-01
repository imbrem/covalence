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
//! - one binary combinator `app : nat → nat → nat` ([`app_fn`]) that attaches an
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
//! instantiates by [`Thm::all_elim`] on the nose — no denotation, no β-redex,
//! no normalisation. This is what makes [`super::relation`] a rule set the
//! generic [`crate::metalogic`] engine drives unchanged.
//!
//! ## Faithfulness, not soundness
//!
//! Nothing here is trusted: derivability is a purely syntactic HOL predicate and
//! the kernel re-checks every step, so an encoding *collision* (two distinct
//! SpecTec expressions mapping to one term) could only ever lose completeness /
//! faithfulness, never mint a false `Thm`. Unsupported constructors return a
//! typed error rather than a silent wrong encoding (see `SKELETONS.md`).

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type};
use covalence_spectec::ast::{MixOp, SpecTecArg, SpecTecExp, SpecTecNum};

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
/// rule's clause (and instantiated by [`Thm::all_elim`]).
pub fn metavar(id: impl AsRef<str>) -> Term {
    Term::free(metavar_name(id), phi())
}

/// A stable string key for a mixfix operator (`%`-joined fragments), naming the
/// `case`/`field` constructor it introduces.
pub fn mixop_key(op: &MixOp) -> String {
    op.fragments().join("%")
}

/// Build `app(app(… app(head, ⌜arg₀⌝) …), ⌜argₙ⌝)` — a node with the given head
/// constant and encoded argument spine.
fn node(head: Term, args: &[SpecTecExp]) -> Result<Term> {
    let mut acc = head;
    for a in args {
        acc = app(acc, encode_exp(a)?)?;
    }
    Ok(acc)
}

fn unsupported(what: &str) -> Error {
    Error::ConnectiveRule(format!("spectec encode: unsupported expression `{what}`"))
}

/// A `nat`/`int` literal as its own constant leaf (`st$c$num.<v>`).
fn num_key(n: &SpecTecNum) -> String {
    match n {
        SpecTecNum::Nat(u) => format!("num.nat.{u}"),
        SpecTecNum::Int(i) => format!("num.int.{i}"),
        SpecTecNum::Rat(s) => format!("num.rat.{s}"),
        SpecTecNum::Real(s) => format!("num.real.{s}"),
    }
}

/// Encode a SpecTec expression into its reified `Φ = nat` term.
///
/// Covers the structural core used by simple relations; richer constructors
/// (arithmetic/update/iteration/…) return [`Error::ConnectiveRule`] until the
/// front end grows to need them (`SKELETONS.md`).
pub fn encode_exp(e: &SpecTecExp) -> Result<Term> {
    match e {
        SpecTecExp::Var { id } => Ok(metavar(id)),
        SpecTecExp::Bool { b } => Ok(con(if *b { "bool.true" } else { "bool.false" })),
        SpecTecExp::Num { n } => Ok(con(num_key(n))),
        SpecTecExp::Text { t } => Ok(con(format!("text.{t}"))),
        SpecTecExp::Tup { es } => node(con("tup"), es),
        SpecTecExp::List { es } => node(con("list"), es),
        SpecTecExp::Opt { eo } => match eo {
            None => Ok(con("opt.none")),
            Some(inner) => node(con("opt.some"), std::slice::from_ref(inner)),
        },
        SpecTecExp::Case { op, e1 } => node(
            con(format!("case.{}", mixop_key(op))),
            std::slice::from_ref(e1),
        ),
        SpecTecExp::Call { x, as1 } => encode_call(x, as1),
        SpecTecExp::Cmp { op, e1, e2, .. } => node(
            con(format!("cmp.{op:?}")),
            &[(**e1).clone(), (**e2).clone()],
        ),
        SpecTecExp::Bin { op, e1, e2, .. } => node(
            con(format!("bin.{op:?}")),
            &[(**e1).clone(), (**e2).clone()],
        ),
        other => Err(unsupported(exp_tag(other))),
    }
}

/// Encode a metafunction call `f(a…)`; only expression arguments are supported
/// for now (type/def/grammar arguments error).
fn encode_call(x: &str, args: &[SpecTecArg]) -> Result<Term> {
    let mut acc = con(format!("call.{x}"));
    for a in args {
        match a {
            SpecTecArg::Exp { e } => acc = app(acc, encode_exp(e)?)?,
            _ => return Err(unsupported("call argument (non-expression)")),
        }
    }
    Ok(acc)
}

/// Collect a rule's metavariables (free [`SpecTecExp::Var`] ids) in first-seen
/// order — the universal-quantifier order of its clause (see [`super::relation`]).
pub fn collect_metavars(e: &SpecTecExp, out: &mut Vec<String>) {
    let push = |id: &str, out: &mut Vec<String>| {
        if !out.iter().any(|s| s == id) {
            out.push(id.to_owned());
        }
    };
    match e {
        SpecTecExp::Var { id } => push(id, out),
        SpecTecExp::Tup { es } | SpecTecExp::List { es } => {
            for s in es {
                collect_metavars(s, out);
            }
        }
        SpecTecExp::Opt { eo } => {
            if let Some(s) = eo {
                collect_metavars(s, out);
            }
        }
        SpecTecExp::Case { e1, .. } => collect_metavars(e1, out),
        SpecTecExp::Cmp { e1, e2, .. } | SpecTecExp::Bin { e1, e2, .. } => {
            collect_metavars(e1, out);
            collect_metavars(e2, out);
        }
        SpecTecExp::Call { as1, .. } => {
            for a in as1 {
                if let SpecTecArg::Exp { e } = a {
                    collect_metavars(e, out);
                }
            }
        }
        _ => {}
    }
}

/// A short tag naming an expression constructor (for error messages).
fn exp_tag(e: &SpecTecExp) -> &'static str {
    match e {
        SpecTecExp::Var { .. } => "var",
        SpecTecExp::Bool { .. } => "bool",
        SpecTecExp::Num { .. } => "num",
        SpecTecExp::Text { .. } => "text",
        SpecTecExp::Un { .. } => "un",
        SpecTecExp::Bin { .. } => "bin",
        SpecTecExp::Cmp { .. } => "cmp",
        SpecTecExp::Idx { .. } => "idx",
        SpecTecExp::Slice { .. } => "slice",
        SpecTecExp::Upd { .. } => "upd",
        SpecTecExp::Ext { .. } => "ext",
        SpecTecExp::Str { .. } => "struct",
        SpecTecExp::Dot { .. } => "dot",
        SpecTecExp::Comp { .. } => "comp",
        SpecTecExp::Mem { .. } => "mem",
        SpecTecExp::Len { .. } => "len",
        SpecTecExp::Tup { .. } => "tup",
        SpecTecExp::Call { .. } => "call",
        SpecTecExp::Iter { .. } => "iter",
        SpecTecExp::Proj { .. } => "proj",
        SpecTecExp::Case { .. } => "case",
        SpecTecExp::Uncase { .. } => "uncase",
        SpecTecExp::Opt { .. } => "opt",
        SpecTecExp::Unopt { .. } => "unopt",
        SpecTecExp::List { .. } => "list",
        SpecTecExp::Lift { .. } => "lift",
        SpecTecExp::Cat { .. } => "cat",
        SpecTecExp::Cvt { .. } => "cvt",
        SpecTecExp::Sub { .. } => "sub",
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
    fn unsupported_constructor_errors() {
        let e = SpecTecExp::Len {
            e1: Box::new(var("x")),
        };
        assert!(encode_exp(&e).is_err());
    }
}

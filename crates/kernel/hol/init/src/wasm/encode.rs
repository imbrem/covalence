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
//! ## Literals: real numerals live in the encoding
//!
//! Numeric literals are the one **interpreted** position ([`encode_num`]):
//! because the carrier `Φ` *is* `nat`, a SpecTec `nat` literal `n` encodes as
//! `app st$c$num.nat ⌜n⌝` where `⌜n⌝` is the **real kernel numeral**
//! ([`mk_nat`] — the very term [`super::denote`] renders `Num` to, so one
//! witness serves both the judgement spine and a denoted side condition). An
//! `int` literal `i` encodes as `app (app st$c$num.int ⌜sign⌝) ⌜|i|⌝` with
//! `sign` the numeral `0` (for `i ≥ 0`) or `1` (for `i < 0`) — sign/magnitude
//! keeps the children inside `Φ = nat`. (`rat`/`real` literals stay opaque
//! leaf constants: the catalogue has no carrier for them yet.) This is what
//! lets a future side-condition clause state a *computable* arithmetic
//! antecedent over the **same** `∀`-bound `nat` variable that appears (under
//! the `num.nat` tag) in the judgement spine: instantiating it with a bare
//! numeral yields the encoding of the substituted literal in the spine *and* a
//! closed, kernel-reducible condition.
//!
//! **Faithfulness of the mixed algebra** (tests below assert each point):
//!
//! - *Distinctness*: everything else in the encoding's image is a free
//!   variable (`st$c$…`, `st$v$…`) or an application headed by the free
//!   variable `st$app`, while a numeral is a closed literal leaf — the two
//!   syntactic classes cannot collide, and `Num` itself never encodes to a
//!   *bare* numeral (always a tagged `num.*` node).
//! - *Injectivity*: distinct values give distinct numerals — and the
//!   disequality is **kernel-computable** (`⊢ ¬(⌜2⌝ = ⌜3⌝)` by
//!   [`reduce`](crate::init::ext::TermExt::reduce)), the hook Else-negation
//!   discharge needs.
//! - *Substitution*: numerals are closed, so capture-avoidance is vacuous and
//!   `encode ∘ subst = subst_free ∘ encode` still holds on the nose —
//!   instantiating a metavariable with an encoded literal (`all_elim` in
//!   [`super::relation::derive`]) produces exactly the encoding of the
//!   substituted expression.
//!
//! One alignment gap remains for `int`: [`super::denote`] renders `Int` at HOL
//! type `int` (`mk_int`), while the encoding carries a sign/magnitude `nat`
//! pair — `int` side conditions can't yet share one witness (see
//! `SKELETONS.md`).
//!
//! ## Why substitution = `all_elim` (the key idea)
//!
//! Because `app` and the `st$c$…` constants are *uninterpreted* and the
//! metavariables are *variables*, HOL's capture-avoiding substitution of
//! `⌜arg⌝` for `st$v$x` in `⌜schema⌝` is syntactically identical to SpecTec
//! metavariable substitution. So a rule clause `∀ x…. premises ⟹ d ⌜concl⌝`
//! instantiates by [`all_elim`](covalence_hol_eval::derived::DerivedRules::all_elim) on the nose — no denotation, no β-redex,
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
//! Nothing here is trusted: derivability is a purely syntactic HOL predicate
//! and the kernel re-checks every step. But an encoding *collision* — two
//! distinct SpecTec expressions mapping to one term — is not harmless
//! incompleteness once conditions become `Side` **equations over encodings**
//! (`super::lower::flatten::cond_eq`): a collision between an equation's two
//! sides makes the antecedent vacuous and the clause fires at points where the
//! SpecTec condition is false. So the encoding is kept **injective** at every
//! encoded position: `E::Iter` carries its binder names (tag) plus domain and
//! `ListN`-bound/index sub-expressions (children); `Upd`/`Ext` path
//! `Idx`/`Slice` sub-expressions are encoded children ([`path_key`] keeps the
//! shape, the children carry the exprs); [`mixop_key`] debug-asserts its `%`
//! join character never occurs in a fragment. Every position encodes the
//! [`canon`]-ical view (`Sub` casts transparent, identity iterations collapsed
//! to their domain — the spine conventions shared with the `Dec` graph-relation
//! leg). The one remaining **coarse** position: non-expression `call` arguments
//! (`Typ`/`Gram`) are dropped from tag and children (measured: every corpus
//! `Typ` arg is a plain type variable; `Gram` args never occur) — recorded in
//! `SKELETONS.md`.

use std::sync::LazyLock;

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::mk_nat;
use covalence_spectec::ast::{
    MixOp, SpecTecArg, SpecTecExp, SpecTecExpField, SpecTecIter, SpecTecIterExp, SpecTecNum,
    SpecTecPath,
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
pub fn app(a: Term, b: Term) -> Result<Term> {
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
/// rule's clause (and instantiated by [`all_elim`](covalence_hol_eval::derived::DerivedRules::all_elim)).
pub fn metavar(id: impl AsRef<str>) -> Term {
    Term::free(metavar_name(id), phi())
}

/// A stable string key for a mixfix operator (`%`-joined fragments), naming the
/// `case`/`field` constructor it introduces. Injective because `%` never occurs
/// *inside* a fragment (debug-asserted — a fragment containing the join
/// character would let two distinct mixops share a key and their constructors
/// collide).
pub fn mixop_key(op: &MixOp) -> String {
    let fragments = op.fragments();
    debug_assert!(
        fragments.iter().all(|f| !f.contains('%')),
        "mixop fragment contains the reserved '%' join character: {fragments:?}"
    );
    fragments.join("%")
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
///
/// `pub(crate)` so the condition flattener's judgement encoder
/// ([`super::lower::flatten`]) reuses this *one* shape — tag and child order
/// can never diverge between the two encoders.
pub(crate) enum Shape<'a> {
    /// A metavariable `<id>`.
    Var(&'a str),
    /// A nullary leaf tagged `<tag>` (`st$c$<tag>`).
    Leaf(String),
    /// A numeric literal — the interpreted position (see [`encode_num`]).
    /// Binds no metavariables (literals are closed).
    Num(&'a SpecTecNum),
    /// A node tagged `<tag>` over encoded children.
    Node(String, Vec<&'a SpecTecExp>),
    /// A record `{ field.<key> e … }` — bespoke (per-field wrapper constants).
    Struct(&'a [SpecTecExpField]),
}

/// A `rat`/`real` literal key (`num.<kind>.<v>`) — the opaque-leaf fallback for
/// the literal kinds with no kernel carrier ([`encode_num`] handles `nat`/`int`
/// with real numerals instead).
fn num_key(n: &SpecTecNum) -> String {
    match n {
        SpecTecNum::Nat(u) => format!("num.nat.{u}"),
        SpecTecNum::Int(i) => format!("num.int.{i}"),
        SpecTecNum::Rat(s) => format!("num.rat.{s}"),
        SpecTecNum::Real(s) => format!("num.real.{s}"),
    }
}

/// Encode a numeric literal (the module-doc *Literals* section):
///
/// - `Nat(n)`  → `app st$c$num.nat ⌜n⌝` — the child is the **real kernel
///   numeral** [`mk_nat`]`(n)`, byte-identical to [`super::denote`]'s rendering
///   of the same literal, so one witness serves both legs.
/// - `Int(i)`  → `app (app st$c$num.int ⌜sign⌝) ⌜|i|⌝` — sign/magnitude as two
///   real `nat` numerals (`sign` is `0` for `i ≥ 0`, `1` for `i < 0`; `-0`
///   doesn't exist in `i64`, so the map is injective).
/// - `Rat`/`Real` → an opaque `st$c$num.rat.<s>` / `st$c$num.real.<s>` leaf,
///   as before (no kernel carrier yet).
fn encode_num(n: &SpecTecNum) -> Result<Term> {
    match n {
        SpecTecNum::Nat(u) => app(con("num.nat"), mk_nat(*u)),
        SpecTecNum::Int(i) => {
            let sign = mk_nat(if *i < 0 { 1u64 } else { 0u64 });
            app(app(con("num.int"), sign)?, mk_nat(i.unsigned_abs()))
        }
        SpecTecNum::Rat(_) | SpecTecNum::Real(_) => Ok(con(num_key(n))),
    }
}

/// The injective tag of a (non-collapsed) iteration node: the iterator kind
/// (with the `ListN` index-variable names) plus the binder names, e.g.
/// `iter.list[x,y]` / `iter.listn(i)[]`. The domain expressions (and `ListN`
/// bound expressions) are encoded **children** (see [`shape`]) — dropping
/// either made `C(x)*{x<-xs}` and `C(x)*{x<-ys}` (or `v^n` and `v^m`) collide,
/// which turned real `Side` equations vacuous (review R1-F1/F2).
fn iter_key(it: &SpecTecIter, xes: &[SpecTecIterExp]) -> String {
    let binders: Vec<&str> = xes
        .iter()
        .map(|SpecTecIterExp::Dom { x, .. }| x.as_str())
        .collect();
    let kind = match it {
        SpecTecIter::Opt => "opt".into(),
        SpecTecIter::List => "list".into(),
        SpecTecIter::List1 => "list1".into(),
        SpecTecIter::ListN { xo, .. } => {
            debug_assert!(
                xo.iter()
                    .all(|x| !x.contains(',') && !x.contains(['(', ')', '[', ']'])),
                "ListN index variable contains a tag delimiter: {xo:?}"
            );
            format!("listn({})", xo.join(","))
        }
    };
    debug_assert!(
        binders
            .iter()
            .all(|b| !b.contains(',') && !b.contains(['(', ')', '[', ']'])),
        "iteration binder contains a tag delimiter: {binders:?}"
    );
    format!("{kind}[{}]", binders.join(","))
}

/// The tag of an access path: shape only (`root.idx`, `root.dot.<key>.slice`,
/// …) — injective *together with* the path's index/slice sub-expressions,
/// which [`shape`] exposes as encoded children (via [`path_child_exprs`], in
/// the same left-to-right order the key renders; dropping them made
/// `s[0 := 9]` and `s[1 := 9]` collide — review R1-F2).
fn path_key(p: &SpecTecPath) -> String {
    match p {
        SpecTecPath::Root => "root".into(),
        SpecTecPath::Idx { p1, .. } => format!("{}.idx", path_key(p1)),
        SpecTecPath::Slice { p1, .. } => format!("{}.slice", path_key(p1)),
        SpecTecPath::Dot { p1, at } => format!("{}.dot.{}", path_key(p1), mixop_key(at)),
    }
}

/// The index/slice sub-expressions of an access path, innermost-first (the
/// order [`path_key`] renders segments in). Child count is determined by the
/// key's shape, so appending these to a node's children keeps it injective.
fn path_child_exprs<'e>(p: &'e SpecTecPath, out: &mut Vec<&'e SpecTecExp>) {
    match p {
        SpecTecPath::Root => {}
        SpecTecPath::Idx { p1, e } => {
            path_child_exprs(p1, out);
            out.push(e);
        }
        SpecTecPath::Slice { p1, e1, e2 } => {
            path_child_exprs(p1, out);
            out.push(e1);
            out.push(e2);
        }
        SpecTecPath::Dot { p1, .. } => path_child_exprs(p1, out),
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

/// The **canonical view** of an expression — the two spine conventions every
/// leg of the total-load lowering agrees on (established by the `Dec`
/// graph-relation leg, `super::lower::decs`, and mirrored here so *every*
/// encoding position uses them):
///
/// - **`Sub` casts are transparent** (their types are dropped from the
///   encoding anyway, and elaboration inserts them asymmetrically between a
///   `Dec` clause's patterns and its call sites — keeping the node would make
///   `fn.*` premises never meet their graph clauses);
/// - **identity iterations collapse to their domain**: `x*`/`x?` with the
///   single binding `x ← xs` and body exactly `Var x` *is* `xs` (exact — an
///   identity-mapped iteration is its domain). `ListN`/`List1` are *not*
///   collapsed (they carry a length constraint dropping would lose).
///
/// Applied by [`shape`], hence by [`encode_exp`] and [`collect_metavars`] (and
/// by the condition flattener's judgement encoder, which mirrors `shape`).
pub(crate) fn canon(e: &SpecTecExp) -> &SpecTecExp {
    match e {
        SpecTecExp::Sub { e1, .. } => canon(e1),
        SpecTecExp::Iter {
            e1,
            it: SpecTecIter::List | SpecTecIter::Opt,
            xes,
        } if xes.len() == 1 => {
            let SpecTecIterExp::Dom { x, e: dom } = &xes[0];
            if matches!(canon(e1), SpecTecExp::Var { id } if id == x) {
                canon(dom)
            } else {
                e
            }
        }
        other => other,
    }
}

/// Decompose an expression into its [`Shape`] (of the [`canon`]-ical view).
/// Total over `SpecTecExp`.
pub(crate) fn shape(e: &SpecTecExp) -> Shape<'_> {
    use SpecTecExp as E;
    match canon(e) {
        E::Var { id } => Shape::Var(id),
        E::Bool { b } => Shape::Leaf(format!("bool.{b}")),
        E::Num { n } => Shape::Num(n),
        E::Text { t } => Shape::Leaf(format!("text.{t}")),
        E::Un { op, e2, .. } => Shape::Node(format!("un.{op:?}"), vec![e2]),
        E::Bin { op, e1, e2, .. } => Shape::Node(format!("bin.{op:?}"), vec![e1, e2]),
        E::Cmp { op, e1, e2, .. } => Shape::Node(format!("cmp.{op:?}"), vec![e1, e2]),
        E::Idx { e1, e2 } => Shape::Node("idx".into(), vec![e1, e2]),
        E::Slice { e1, e2, e3 } => Shape::Node("slice".into(), vec![e1, e2, e3]),
        E::Upd { e1, path, e2 } => {
            let mut kids = vec![&**e1, &**e2];
            path_child_exprs(path, &mut kids);
            Shape::Node(format!("upd.{}", path_key(path)), kids)
        }
        E::Ext { e1, path, e2 } => {
            let mut kids = vec![&**e1, &**e2];
            path_child_exprs(path, &mut kids);
            Shape::Node(format!("ext.{}", path_key(path)), kids)
        }
        E::Str { efs } => Shape::Struct(efs),
        E::Dot { e1, at } => Shape::Node(format!("dot.{}", mixop_key(at)), vec![e1]),
        E::Comp { e1, e2 } => Shape::Node("comp".into(), vec![e1, e2]),
        E::Mem { e1, e2 } => Shape::Node("mem".into(), vec![e1, e2]),
        E::Len { e1 } => Shape::Node("len".into(), vec![e1]),
        E::Tup { es } => Shape::Node("tup".into(), es.iter().collect()),
        E::Call { x, as1 } => Shape::Node(format!("call.{x}"), call_exp_args(as1)),
        E::Iter { e1, it, xes } => {
            // Binders in the tag; domain (and ListN bound) expressions as
            // children — the injectivity restoration (see [`iter_key`]).
            let mut kids: Vec<&SpecTecExp> = vec![e1];
            for SpecTecIterExp::Dom { e, .. } in xes {
                kids.push(e);
            }
            if let SpecTecIter::ListN { e, .. } = it {
                kids.extend(e.iter());
            }
            Shape::Node(format!("iter.{}", iter_key(it, xes)), kids)
        }
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
        Shape::Num(n) => encode_num(n),
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
        Shape::Leaf(_) | Shape::Num(_) => {}
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

    fn num_nat(u: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(u),
        }
    }
    fn num_int(i: i64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Int(i),
        }
    }

    /// `Num{Nat(n)}` encodes as `app st$c$num.nat ⌜n⌝` with the **real kernel
    /// numeral** as the child — the exact term [`super::super::denote`] renders
    /// the same literal to, so one witness serves both legs.
    #[test]
    fn nat_literal_child_is_the_denotation() {
        use crate::wasm::denote::{DenoteCtx, TypeEnv, denote};
        let five = num_nat(5);
        let enc = encode_exp(&five).unwrap();
        let denoted = denote(&five, &DenoteCtx::values(TypeEnv::new())).unwrap();
        assert_eq!(denoted, mk_nat(5u64));
        assert_eq!(enc, app(con("num.nat"), denoted).unwrap());
        assert_eq!(enc.type_of().unwrap(), phi());
    }

    /// `Num{Int(i)}` encodes sign/magnitude as two real `nat` numerals, and the
    /// map is injective on `i64` (`-0` doesn't exist).
    #[test]
    fn int_literal_encodes_sign_magnitude() {
        let neg = encode_exp(&num_int(-3)).unwrap();
        let want = app(app(con("num.int"), mk_nat(1u64)).unwrap(), mk_nat(3u64)).unwrap();
        assert_eq!(neg, want);
        assert_eq!(neg.type_of().unwrap(), phi());

        let pos = encode_exp(&num_int(3)).unwrap();
        assert_ne!(pos, neg, "sign distinguishes 3 from -3");
        // int and nat literals of the same value are distinct nodes.
        assert_ne!(pos, encode_exp(&num_nat(3)).unwrap());
    }

    /// Distinctness of the mixed algebra: a literal node, a constructor leaf,
    /// a bare numeral, and the tag constant are pairwise distinct terms. In
    /// particular `Num` never encodes to a *bare* numeral — the numeral only
    /// occurs as the child of the `num.nat` node.
    #[test]
    fn literal_nodes_are_distinct_from_spines_and_bare_numerals() {
        let enc_zero = encode_exp(&num_nat(0)).unwrap();
        let enc_none = encode_exp(&SpecTecExp::Opt { eo: None }).unwrap();
        let bare = mk_nat(0u64);
        assert_ne!(enc_zero, enc_none);
        assert_ne!(enc_zero, bare);
        assert_ne!(enc_none, bare);
        assert_ne!(enc_zero, con("num.nat"));
        assert_ne!(enc_zero, metavar("x"));
        // Literals bind no metavariables (collect behavior unchanged).
        let mut mv = Vec::new();
        collect_metavars(&num_nat(7), &mut mv);
        assert!(mv.is_empty());
    }

    /// Injectivity on literals is **kernel-computable**: distinct `n` give
    /// distinct numerals and the kernel *proves* the disequality —
    /// `⊢ ¬(⌜2⌝ = ⌜3⌝)` by `reduce` (the `2 = 3` literal equation folds to `F`)
    /// plus the `⊢ ¬F` fact. This is the hook Else-negation discharge needs.
    #[test]
    fn distinct_numerals_are_kernel_provably_unequal() {
        use covalence_hol_eval::EvalThm as Thm;
        use covalence_hol_eval::derived::DerivedRules;
        use covalence_hol_eval::mk_bool;

        assert_ne!(
            encode_exp(&num_nat(2)).unwrap(),
            encode_exp(&num_nat(3)).unwrap()
        );

        // ⊢ ¬(2 = 3): reduce folds the literal equation to F, giving
        // ⊢ ¬(2 = 3) = ¬F; conclude via ⊢ ¬F.
        let ineq = mk_nat(2u64).equals(mk_nat(3u64)).unwrap().not().unwrap();
        let red = ineq.reduce().unwrap(); // ⊢ ¬(2 = 3) = ¬F
        let f = mk_bool(false);
        let not_false = Thm::assume(f.clone())
            .unwrap()
            .imp_intro(&f)
            .unwrap()
            .not_intro()
            .unwrap(); // ⊢ ¬F
        let thm = red.sym().unwrap().eq_mp(not_false).unwrap();
        assert_eq!(thm.concl(), &ineq);
        assert!(thm.hyps().is_empty(), "disequality is hypothesis-free");
    }

    /// Substitution = `all_elim` survives real numerals: substituting the
    /// *encoded* literal for the mangled metavariable in the encoding yields
    /// exactly the encoding of the SpecTec-substituted expression (numerals are
    /// closed, so capture-avoidance is vacuous).
    #[test]
    fn substitution_commutes_with_encoding_on_literals() {
        use covalence_core::Var;
        use covalence_core::subst::subst_free;

        // e = (x, 7)  and  e[x := 5].
        let e = SpecTecExp::Tup {
            es: vec![var("x"), num_nat(7)],
        };
        let e_subst = SpecTecExp::Tup {
            es: vec![num_nat(5), num_nat(7)],
        };
        let got = subst_free(
            &encode_exp(&e).unwrap(),
            &Var::new(metavar_name("x"), phi()),
            &encode_exp(&num_nat(5)).unwrap(),
        );
        assert_eq!(got, encode_exp(&e_subst).unwrap());
    }

    /// `rat`/`real` literals stay opaque leaf constants (no kernel carrier).
    #[test]
    fn rat_real_literals_stay_opaque() {
        let rat = SpecTecExp::Num {
            n: SpecTecNum::Rat("1/2".into()),
        };
        assert_eq!(encode_exp(&rat).unwrap(), con("num.rat.1/2"));
    }

    /// R1-F1 regression: iteration binders + domains are part of the
    /// encoding. `C(x)*{x<-xs}` vs `C(x)*{x<-ys}` (distinct domains) and
    /// `C(x)*{x<-xs}` vs `C(y)*{y<-xs}` (distinct binders) must not collide,
    /// and the domain metavariable must be collected.
    #[test]
    fn iteration_binders_and_domains_are_encoded() {
        let case_map = |binder: &str, dom: &str| SpecTecExp::Iter {
            e1: Box::new(SpecTecExp::Case {
                op: MixOp::new(vec!["C".into()]),
                e1: Box::new(var(binder)),
            }),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: binder.into(),
                e: var(dom),
            }],
        };
        let xs = encode_exp(&case_map("x", "xs")).unwrap();
        let ys = encode_exp(&case_map("x", "ys")).unwrap();
        assert_ne!(xs, ys, "distinct domains must encode distinctly");
        assert_ne!(
            xs,
            encode_exp(&case_map("y", "xs")).unwrap(),
            "distinct binders must encode distinctly"
        );
        // The domain metavariable is back under the quantifiers.
        let mut mv = Vec::new();
        collect_metavars(&case_map("x", "xs"), &mut mv);
        assert_eq!(mv, vec!["x".to_string(), "xs".to_string()]);
        // The identity-iteration collapse still fires FIRST: `x*{x<-xs}`
        // *is* `xs`, new children notwithstanding.
        let identity = SpecTecExp::Iter {
            e1: Box::new(var("x")),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: "x".into(),
                e: var("xs"),
            }],
        };
        assert_eq!(
            encode_exp(&identity).unwrap(),
            encode_exp(&var("xs")).unwrap()
        );
    }

    /// R1-F1 regression (`ListN`): the length bound is an encoded child (and
    /// the index variable part of the tag) — `v^n` vs `v^m` must not collide,
    /// and the bound metavariable must be collected.
    #[test]
    fn listn_bound_is_encoded() {
        let pow = |bound: &str| SpecTecExp::Iter {
            e1: Box::new(var("v")),
            it: SpecTecIter::ListN {
                e: vec![var(bound)],
                xo: vec![],
            },
            xes: vec![],
        };
        assert_ne!(
            encode_exp(&pow("n")).unwrap(),
            encode_exp(&pow("m")).unwrap(),
            "distinct ListN bounds must encode distinctly"
        );
        let mut mv = Vec::new();
        collect_metavars(&pow("n"), &mut mv);
        assert_eq!(mv, vec!["v".to_string(), "n".to_string()]);
        // The index variable distinguishes too (it scopes the body).
        let indexed = SpecTecExp::Iter {
            e1: Box::new(var("v")),
            it: SpecTecIter::ListN {
                e: vec![var("n")],
                xo: vec!["i".into()],
            },
            xes: vec![],
        };
        assert_ne!(
            encode_exp(&indexed).unwrap(),
            encode_exp(&pow("n")).unwrap()
        );
    }

    /// R1-F2 regression: `upd`/`ext` path index/slice sub-expressions are
    /// encoded children — `s[0 := 9]` vs `s[1 := 9]` must not collide, and
    /// path metavariables must be collected.
    #[test]
    fn upd_path_indices_are_encoded() {
        let upd = |i: u64| SpecTecExp::Upd {
            e1: Box::new(var("s")),
            path: Box::new(SpecTecPath::Idx {
                p1: Box::new(SpecTecPath::Root),
                e: num_nat(i),
            }),
            e2: Box::new(num_nat(9)),
        };
        assert_ne!(
            encode_exp(&upd(0)).unwrap(),
            encode_exp(&upd(1)).unwrap(),
            "distinct update indices must encode distinctly"
        );
        let ext_var = SpecTecExp::Ext {
            e1: Box::new(var("s")),
            path: Box::new(SpecTecPath::Idx {
                p1: Box::new(SpecTecPath::Root),
                e: var("x"),
            }),
            e2: Box::new(var("v")),
        };
        let mut mv = Vec::new();
        collect_metavars(&ext_var, &mut mv);
        assert_eq!(
            mv,
            vec!["s".to_string(), "v".to_string(), "x".to_string()],
            "path index metavariable collected (after e1/e2)"
        );
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

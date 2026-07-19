//! **Evaluator relations `ev.<op>…`** — schematic clauses giving *structural
//! operators* (`Len`/`Idx`/`Uncase`/`Proj`/`Dot`/`Cat`/`Mem`/`Unopt`, structural
//! disequality `Neq`) a derivable meaning over the encoded `Φ = nat` carrier, so
//! a flattened condition can consume them as ordinary [`LowerPrem::Judgement`]
//! antecedents (design note leg 3, `notes/vibes/logics/spectec-total-load.md`).
//!
//! Every judgement body is built by [`ev_graph`] (the `ev.*` twin of
//! [`super::fn_graph`]): `app`-spine of the encoded arguments followed by the
//! result, tagged `ev.<op>`. Clauses are emitted **on demand** by the
//! [`super::flatten::Flattener`] (only the tags a condition actually uses), and
//! deduplicated by key.
//!
//! Soundness: each clause is derivable-only-when-genuine —
//!
//! - `ev.len` relates a snoc spine to its real-nat length (base `st$c$list` ↦
//!   `0`, snoc ↦ `n + 1` with a **real** `nat.add`);
//! - `ev.idx` indexes a snoc spine from the left (`xs · x` has `x` at index
//!   `|xs|`; earlier elements keep their index);
//! - `ev.uncase.<key>` projects the payload out of a `case.<key>` node — pure
//!   tag-match, so only values *actually* built with that constructor project;
//! - `ev.proj.<i>` projects the `i`-th component out of a `tup` spine of any
//!   arity `i < n ≤` [`MAX_TUPLE`];
//! - `ev.dot.<key>` finds the (unique-per-struct) `field.<key>` payload in a
//!   `struct` spine;
//! - `ev.cat`/`ev.mem`/`ev.unopt` are the standard snoc-spine
//!   concatenation/membership/option-projection relations;
//! - `ev.neq` asserts disequality of two **distinct-key** constructor spines —
//!   distinct case keys are distinct constructors of any single (well-typed)
//!   comparison type, so this under-approximates SpecTec `=/=` (same-key,
//!   different-payload disequalities are simply not derivable);
//! - `ev.int.lt` / `ev.int.le` compare the sign/magnitude encoding of SpecTec
//!   integers, reducing magnitude comparisons to real HOL-natural side
//!   conditions;
//! - `ev.upd.<path>`/`ev.ext.<path>` are the **write** evaluators
//!   ([`upd_ext_families`]): `subject[path := new]` / `subject[path ++= new]`
//!   over `Dot`/`Idx` access paths, by spine rebuild — exact at genuine
//!   points, underivable out of bounds, `Slice` paths refused (a write is
//!   never approximated).

use covalence_core::{Result, Term};
use covalence_hol_eval::mk_nat;
use covalence_spectec::ast::{SpecTecExp, SpecTecPath};

use super::super::encode::{app, con, metavar, mixop_key, tag};
use super::{Clause, LowerPrem};
use crate::init::ext::TermExt;
use crate::init::nat;

/// Maximum `tup` arity `ev.proj.<i>` clauses are emitted for (the bundled spec's
/// case payloads stay well under this).
pub const MAX_TUPLE: usize = 8;

/// The canonical judgement body of an **evaluator** relation instance:
/// relation tag `ev.<op>`, body = the `app`-spine of the encoded arguments
/// followed by the encoded result — the `ev.*` twin of [`super::fn_graph`].
pub fn ev_graph(op: &str, args: &[Term], result: &Term) -> Result<Term> {
    let mut spine = con(format!("evargs.{}", args.len()));
    for a in args {
        spine = app(spine, a.clone())?;
    }
    spine = app(spine, result.clone())?;
    tag(format!("ev.{op}"), spine)
}

/// `app(st$c$num.nat, t)` — the wrapped (spine) form of a numeric term `t`
/// (see the numeric-metavar discipline in [`super::flatten`]).
pub fn wrap_nat(t: Term) -> Result<Term> {
    app(con("num.nat"), t)
}

/// `app (app st$c$num.int sign) magnitude` — the canonical encoded SpecTec
/// integer literal shape.
pub fn wrap_int(sign: u64, magnitude: Term) -> Result<Term> {
    app(app(con("num.int"), mk_nat(sign))?, magnitude)
}

fn mv(id: &str) -> Term {
    metavar(id)
}

fn clause(metavars: &[&str], prems: Vec<LowerPrem>, concl: Term) -> Clause {
    Clause {
        metavars: metavars.iter().map(|s| s.to_string()).collect(),
        prems,
        concl,
    }
}

/// Sign/magnitude integer ordering over the encoded carrier.
///
/// Only the `true` graph is needed by condition lowering:
///
/// - positive magnitudes compare in their ordinary order;
/// - negative magnitudes compare in reverse order;
/// - every canonical negative is below every non-negative.
///
/// SpecTec integer literals have no negative zero, so the third clause is
/// exact at genuine encoded points. It may also accept the junk encoding
/// `(sign=1, magnitude=0)`, which is outside the real-point faithfulness
/// contract shared by the total lowering.
pub fn int_order_clauses(strict: bool) -> Result<Vec<Clause>> {
    let op = if strict { "int.lt" } else { "int.le" };
    let order = if strict { nat::nat_lt() } else { nat::nat_le() };
    let a = mv("%a");
    let b = mv("%b");
    let positive = clause(
        &["%a", "%b"],
        vec![LowerPrem::Side(
            order.clone().apply(a.clone())?.apply(b.clone())?,
        )],
        ev_graph(
            op,
            &[wrap_int(0, a.clone())?, wrap_int(0, b.clone())?],
            &con("bool.true"),
        )?,
    );
    let negative = clause(
        &["%a", "%b"],
        vec![LowerPrem::Side(order.apply(b.clone())?.apply(a.clone())?)],
        ev_graph(
            op,
            &[wrap_int(1, a.clone())?, wrap_int(1, b.clone())?],
            &con("bool.true"),
        )?,
    );
    let negative_positive = clause(
        &["%a", "%b"],
        vec![],
        ev_graph(op, &[wrap_int(1, a)?, wrap_int(0, b)?], &con("bool.true"))?,
    );
    Ok(vec![positive, negative, negative_positive])
}

/// Exact equality of a quotient of two canonical sign/magnitude integers
/// with a positive natural:
///
/// ```text
/// a / b = n    iff    sign(a) = sign(b) ∧ |a| = n * |b|
/// ```
///
/// The relation deliberately carries `0 < |b|` (division definedness) and
/// `0 < n` (the fragment advertised by the tag).  SpecTec integer literals
/// have no negative zero, so the two same-sign clauses are exhaustive at
/// genuine encoded points; opposite signs cannot equal a positive natural.
pub fn signed_div_eq_pos_nat_clauses() -> Result<Vec<Clause>> {
    let a = mv("%a");
    let b = mv("%b");
    let n = mv("%n");
    let prems = || -> Result<Vec<LowerPrem>> {
        Ok(vec![
            LowerPrem::Side(nat::nat_lt().apply(mk_nat(0u64))?.apply(b.clone())?),
            LowerPrem::Side(nat::nat_lt().apply(mk_nat(0u64))?.apply(n.clone())?),
            LowerPrem::Side(
                a.clone()
                    .equals(nat::nat_mul().apply(n.clone())?.apply(b.clone())?)?,
            ),
        ])
    };
    let make = |sign| -> Result<Clause> {
        Ok(clause(
            &["%a", "%b", "%n"],
            prems()?,
            ev_graph(
                "signed-div-eq-pos-nat",
                &[
                    wrap_int(sign, a.clone())?,
                    wrap_int(sign, b.clone())?,
                    wrap_nat(n.clone())?,
                ],
                &con("bool.true"),
            )?,
        ))
    };
    Ok(vec![make(0)?, make(1)?])
}

/// Natural ordering over the encoded `num.nat` carrier. This is the
/// judgement-level counterpart of direct HOL-natural sides, used when a
/// numeric value is an iteration element and therefore arrives as a full
/// encoding rather than a bare arithmetic metavariable.
pub fn nat_order_clauses(strict: bool) -> Result<Vec<Clause>> {
    let op = if strict { "nat.lt" } else { "nat.le" };
    let order = if strict { nat::nat_lt() } else { nat::nat_le() };
    Ok(vec![clause(
        &["%a", "%b"],
        vec![LowerPrem::Side(order.apply(mv("%a"))?.apply(mv("%b"))?)],
        ev_graph(
            op,
            &[wrap_nat(mv("%a"))?, wrap_nat(mv("%b"))?],
            &con("bool.true"),
        )?,
    )])
}

/// `ev.len` — snoc-spine length with real-nat results:
/// `len([], 0)` and `j = S n ∧ len(xs, n) ⟹ len(xs·x, j)`. The explicit
/// successor witness keeps results in literal-numeral currency, so a derived
/// length composes syntactically with encoded numeric literals and bounds.
pub fn len_clauses() -> Result<Vec<Clause>> {
    let base = clause(
        &[],
        vec![],
        ev_graph("len", &[con("list")], &wrap_nat(mk_nat(0u64))?)?,
    );
    let step = clause(
        &["%xs", "%x", "%n", "%j"],
        vec![
            LowerPrem::Side(mv("%j").equals(Term::succ().apply(mv("%n"))?)?),
            LowerPrem::Judgement(ev_graph("len", &[mv("%xs")], &wrap_nat(mv("%n"))?)?),
        ],
        ev_graph("len", &[app(mv("%xs"), mv("%x"))?], &wrap_nat(mv("%j"))?)?,
    );
    Ok(vec![base, step])
}

/// `ev.idx` — left-to-right snoc-spine indexing (`idx(list, i, elem)`):
/// `len(xs, n) ⟹ idx(xs·x, n, x)` and `idx(xs, n, y) ⟹ idx(xs·x, n, y)`.
/// Requires [`len_clauses`] in the same rule set.
pub fn idx_clauses() -> Result<Vec<Clause>> {
    let last = clause(
        &["%xs", "%x", "%n"],
        vec![LowerPrem::Judgement(ev_graph(
            "len",
            &[mv("%xs")],
            &wrap_nat(mv("%n"))?,
        )?)],
        ev_graph(
            "idx",
            &[app(mv("%xs"), mv("%x"))?, wrap_nat(mv("%n"))?],
            &mv("%x"),
        )?,
    );
    let skip = clause(
        &["%xs", "%x", "%n", "%y"],
        vec![LowerPrem::Judgement(ev_graph(
            "idx",
            &[mv("%xs"), wrap_nat(mv("%n"))?],
            &mv("%y"),
        )?)],
        ev_graph(
            "idx",
            &[app(mv("%xs"), mv("%x"))?, wrap_nat(mv("%n"))?],
            &mv("%y"),
        )?,
    );
    Ok(vec![last, skip])
}

/// `ev.slice(s, i, n, r)` — the length-`n` segment of list `s` starting at
/// `i`. Exact through the unique genuine decomposition
/// `s = prefix ++ r ++ suffix`, `|prefix| = i`, `|r| = n`.
pub fn slice_clause() -> Result<Vec<Clause>> {
    Ok(vec![clause(
        &[
            "%prefix", "%r", "%left", "%suffix", "%s", "%start", "%count",
        ],
        vec![
            LowerPrem::Judgement(ev_graph("len", &[mv("%prefix")], &wrap_nat(mv("%start"))?)?),
            LowerPrem::Judgement(ev_graph("len", &[mv("%r")], &wrap_nat(mv("%count"))?)?),
            LowerPrem::Judgement(ev_graph("cat", &[mv("%prefix"), mv("%r")], &mv("%left"))?),
            LowerPrem::Judgement(ev_graph("cat", &[mv("%left"), mv("%suffix")], &mv("%s"))?),
        ],
        ev_graph(
            "slice",
            &[mv("%s"), wrap_nat(mv("%start"))?, wrap_nat(mv("%count"))?],
            &mv("%r"),
        )?,
    )])
}

/// `ev.uncase.<key>` — payload projection out of a `case.<key>` node:
/// `uncase(case.<key>(p), p)`. Pure tag match; one clause.
pub fn uncase_clause(key: &str) -> Result<Vec<Clause>> {
    Ok(vec![clause(
        &["%p"],
        vec![],
        ev_graph(
            &format!("uncase.{key}"),
            &[app(con(format!("case.{key}")), mv("%p"))?],
            &mv("%p"),
        )?,
    )])
}

/// `ev.proj.<i>` — `i`-th component of a `tup` spine, one clause per arity
/// `i < n ≤` [`MAX_TUPLE`].
pub fn proj_clauses(i: usize) -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for n in (i + 1)..=MAX_TUPLE {
        let names: Vec<String> = (0..n).map(|k| format!("%x{k}")).collect();
        let mut spine = con("tup");
        for name in &names {
            spine = app(spine, mv(name))?;
        }
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        out.push(clause(
            &refs,
            vec![],
            ev_graph(&format!("proj.{i}"), &[spine], &mv(&names[i]))?,
        ));
    }
    Ok(out)
}

/// `ev.dot.<key>` — the `field.<key>` payload of a `struct` spine:
/// `dot(s · field.<key>(v), v)` and `dot(s, v) ⟹ dot(s · f, v)`.
/// Struct field keys are unique per struct, so at most one value is derivable
/// per (spine, key).
pub fn dot_clauses(key: &str) -> Result<Vec<Clause>> {
    let op = format!("dot.{key}");
    let hit = clause(
        &["%s", "%v"],
        vec![],
        ev_graph(
            &op,
            &[app(mv("%s"), app(con(format!("field.{key}")), mv("%v"))?)?],
            &mv("%v"),
        )?,
    );
    let skip = clause(
        &["%s", "%f", "%v"],
        vec![LowerPrem::Judgement(ev_graph(&op, &[mv("%s")], &mv("%v"))?)],
        ev_graph(&op, &[app(mv("%s"), mv("%f"))?], &mv("%v"))?,
    );
    Ok(vec![hit, skip])
}

/// `ev.cat` — snoc-spine concatenation (`cat(xs, ys, xs++ys)`):
/// `cat(xs, [], xs)` and `cat(xs, ys, r) ⟹ cat(xs, ys·y, r·y)`.
pub fn cat_clauses() -> Result<Vec<Clause>> {
    let base = clause(
        &["%xs"],
        vec![],
        ev_graph("cat", &[mv("%xs"), con("list")], &mv("%xs"))?,
    );
    let step = clause(
        &["%xs", "%ys", "%y", "%r"],
        vec![LowerPrem::Judgement(ev_graph(
            "cat",
            &[mv("%xs"), mv("%ys")],
            &mv("%r"),
        )?)],
        ev_graph(
            "cat",
            &[mv("%xs"), app(mv("%ys"), mv("%y"))?],
            &app(mv("%r"), mv("%y"))?,
        )?,
    );
    Ok(vec![base, step])
}

/// `ev.mem` — snoc-spine membership: `mem(x, xs·x)` and
/// `mem(x, xs) ⟹ mem(x, xs·y)`.
pub fn mem_clauses() -> Result<Vec<Clause>> {
    let head = clause(
        &["%x", "%xs"],
        vec![],
        ev_graph("mem", &[mv("%x")], &app(mv("%xs"), mv("%x"))?)?,
    );
    let skip = clause(
        &["%x", "%xs", "%y"],
        vec![LowerPrem::Judgement(ev_graph(
            "mem",
            &[mv("%x")],
            &mv("%xs"),
        )?)],
        ev_graph("mem", &[mv("%x")], &app(mv("%xs"), mv("%y"))?)?,
    );
    Ok(vec![head, skip])
}

/// `ev.unopt` — option projection: `unopt(opt.some(x), x)`.
pub fn unopt_clause() -> Result<Vec<Clause>> {
    Ok(vec![clause(
        &["%x"],
        vec![],
        ev_graph("unopt", &[app(con("opt.some"), mv("%x"))?], &mv("%x"))?,
    )])
}

/// `ev.lift` — SpecTec's option→list coercion (`lift(eps) = []`,
/// `lift(x) = [x]`), exactly two ground-shape clauses:
/// `lift(opt.none, [])` and `lift(opt.some(x), [x])`. Exact at genuine
/// option encodings — this is the result-flattening family that lets
/// `fn.binop_`'s DIV/REM conclusions (`lift($idiv_ …)`) conclude the actual
/// value list `Step_pure/binop-val` / `binop-trap` consume.
pub fn lift_clauses() -> Result<Vec<Clause>> {
    let none = clause(
        &[],
        vec![],
        ev_graph("lift", &[con("opt.none")], &con("list"))?,
    );
    let some = clause(
        &["%x"],
        vec![],
        ev_graph(
            "lift",
            &[app(con("opt.some"), mv("%x"))?],
            &app(con("list"), mv("%x"))?,
        )?,
    );
    Ok(vec![none, some])
}

/// `ev.nonempty2` — the sound witness for the corpus condition shape
/// `xs =/= [] \/ ys =/= []` (the `Step/ctxt-instrs` frame guard): derivable
/// exactly when either argument is a snoc node. Two premise-free clauses:
/// `nonempty2(l·x, y)` (left disjunct) and `nonempty2(x, l·y)` (right).
/// At genuine list encodings a snoc node ⟺ a non-empty list, so this is
/// exact at real points; junk points are outside the faithfulness contract
/// (`lower/mod.rs` module docs).
pub fn nonempty2_clauses() -> Result<Vec<Clause>> {
    let left = clause(
        &["%xs", "%x", "%y"],
        vec![],
        ev_graph("nonempty2", &[app(mv("%xs"), mv("%x"))?], &mv("%y"))?,
    );
    let right = clause(
        &["%x", "%ys", "%y"],
        vec![],
        ev_graph("nonempty2", &[mv("%x")], &app(mv("%ys"), mv("%y"))?)?,
    );
    Ok(vec![left, right])
}

// ===========================================================================
// Store/struct/list writes: `ev.upd.<path>` / `ev.ext.<path>`
// ===========================================================================

/// One segment of a **supported** write path, root-first. `Slice` segments
/// are unsupported — an exact slice-write evaluator (split at `i`, splice a
/// length-`j` replacement) doesn't exist yet and a write must never be
/// represented structurally by the path algebra below.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathSeg {
    /// `.<key>` — descend into the (unique-per-struct) `field.<key>` payload.
    Dot(String),
    /// `[i]` — descend to a list index (consumes one index argument).
    Idx,
    /// `[i : n]` — descend to the length-`n` slice starting at `i`
    /// (consumes two natural arguments).
    Slice,
}

/// Decompose an access path into root-first segments.
pub fn path_segs(p: &SpecTecPath) -> Option<Vec<PathSeg>> {
    fn go(p: &SpecTecPath, out: &mut Vec<PathSeg>) -> bool {
        match p {
            SpecTecPath::Root => true,
            SpecTecPath::Idx { p1, .. } => {
                go(p1, out) && {
                    out.push(PathSeg::Idx);
                    true
                }
            }
            SpecTecPath::Dot { p1, at } => {
                go(p1, out) && {
                    out.push(PathSeg::Dot(mixop_key(at)));
                    true
                }
            }
            SpecTecPath::Slice { p1, .. } => {
                go(p1, out) && {
                    out.push(PathSeg::Slice);
                    true
                }
            }
        }
    }
    let mut out = Vec::new();
    go(p, &mut out).then_some(out)
}

/// The index/slice expressions of a path, root-first — the natural-argument
/// order of the write judgements.
pub fn path_index_exprs<'e>(p: &'e SpecTecPath, out: &mut Vec<&'e SpecTecExp>) {
    match p {
        SpecTecPath::Root => {}
        SpecTecPath::Idx { p1, e } => {
            path_index_exprs(p1, out);
            out.push(e);
        }
        SpecTecPath::Slice { p1, e1, e2 } => {
            path_index_exprs(p1, out);
            out.push(e1);
            out.push(e2);
        }
        SpecTecPath::Dot { p1, .. } => path_index_exprs(p1, out),
    }
}

/// `root[.dot.<key>|.idx]*` — the path-shape suffix of a write-relation tag
/// (mirrors the encoder's path keys). A field key equal to `idx`/`slice` or
/// containing `.` would make the tag grammar ambiguous — absent from the
/// corpus, asserted.
pub fn segs_key(segs: &[PathSeg]) -> String {
    let mut k = String::from("root");
    for s in segs {
        match s {
            PathSeg::Dot(key) => {
                debug_assert!(
                    key != "idx" && key != "slice" && !key.contains('.'),
                    "field key collides with the write-path tag grammar: {key}"
                );
                k.push_str(".dot.");
                k.push_str(key);
            }
            PathSeg::Idx => k.push_str(".idx"),
            PathSeg::Slice => k.push_str(".slice"),
        }
    }
    k
}

fn n_path_args(segs: &[PathSeg]) -> usize {
    segs.iter()
        .map(|s| match s {
            PathSeg::Idx => 1,
            PathSeg::Slice => 2,
            PathSeg::Dot(_) => 0,
        })
        .sum()
}

/// Every `(dedup key, clauses)` family needed to evaluate an `op` write
/// (`"upd"` / `"ext"`) along `segs`: one schematic level family per
/// **non-empty path suffix** (the empty tail is inlined at the last
/// segment's level), plus the `ev.len` / `ev.cat` base families the level
/// clauses reference. Judgement layout of level `S`:
/// `ev.<op>.<segs_key S>(subject, idx-args…, newval, result)` with one index
/// argument per `Idx` segment of `S`, root-first (wrapped-nat currency, like
/// `ev.idx`).
///
/// Soundness — the write is **exact at genuine points**, in both directions:
///
/// - `Dot` levels rebuild the struct spine: the *hit* clause updates the
///   last field when it is `field.<key>` (payload evaluated along the tail),
///   the *skip* clause carries any other last field through. Field keys are
///   unique per genuine struct, so exactly one derivation exists and the
///   result is the SpecTec update; a missing field is underivable (no base
///   clause). Duplicate-key subjects are junk points, outside the
///   faithfulness contract (`lower` module docs).
/// - `Idx` levels recurse like `ev.idx`: *hit* lands on the last element
///   exactly when the index equals `|prefix|` (a real `ev.len` premise),
///   *skip* rides the last element over a strictly-earlier write. Unique
///   derivation per in-bounds index; an out-of-bounds index is underivable
///   (SpecTec's partiality, under-approximated).
/// - The empty tail substitutes the new value directly (`upd`) or appends
///   through `ev.cat` (`ext` — list concatenation, the only `Ext` leaf).
///
/// A clause consuming a write premise `ev.upd(s, ī, v, r)` therefore only
/// ever fires with `r` = the encoding of the genuinely-updated value —
/// antecedent at least as strong as the SpecTec equation.
pub fn upd_ext_families(op: &str, segs: &[PathSeg]) -> Result<Vec<(String, Vec<Clause>)>> {
    assert!(op == "upd" || op == "ext", "unknown write op: {op}");
    let mut out = Vec::new();
    if n_path_args(segs) > 0 {
        out.push(("len".to_string(), len_clauses()?));
    }
    if op == "ext" || segs.iter().any(|s| matches!(s, PathSeg::Slice)) {
        out.push(("cat".to_string(), cat_clauses()?));
    }
    if segs.is_empty() {
        out.push((format!("{op}.root"), write_level_clauses(op, segs)?));
    } else {
        for start in (0..segs.len()).rev() {
            let sub = &segs[start..];
            out.push((
                format!("{op}.{}", segs_key(sub)),
                write_level_clauses(op, sub)?,
            ));
        }
    }
    Ok(out)
}

/// The schematic clauses of ONE write level (see [`upd_ext_families`]).
fn write_level_clauses(op: &str, segs: &[PathSeg]) -> Result<Vec<Clause>> {
    let this = format!("{op}.{}", segs_key(segs));
    let Some((seg, rest)) = segs.split_first() else {
        // Root-path write: `upd` replaces the whole subject; `ext` appends.
        return Ok(if op == "upd" {
            vec![clause(
                &["%s", "%v"],
                vec![],
                ev_graph(&this, &[mv("%s"), mv("%v")], &mv("%v"))?,
            )]
        } else {
            vec![clause(
                &["%s", "%v", "%r"],
                vec![LowerPrem::Judgement(ev_graph(
                    "cat",
                    &[mv("%s"), mv("%v")],
                    &mv("%r"),
                )?)],
                ev_graph(&this, &[mv("%s"), mv("%v")], &mv("%r"))?,
            )]
        });
    };

    // Tail-level index metavariables (`%i0`, …), root-first; an `Idx` segment
    // at THIS level consumes its own `%n` first.
    let tail_idx: Vec<String> = (0..n_path_args(rest)).map(|j| format!("%i{j}")).collect();
    let tail_idx_terms = tail_idx
        .iter()
        .map(|n| wrap_nat(mv(n)))
        .collect::<Result<Vec<Term>>>()?;
    // The tail evaluation `w ↦ result` of the addressed sub-value: premises,
    // the result term, and the extra metavariables it introduces.
    let tail_eval =
        |w: &str, w2: &'static str| -> Result<(Vec<LowerPrem>, Term, Vec<&'static str>)> {
            if rest.is_empty() {
                if op == "upd" {
                    Ok((vec![], mv("%v"), vec![]))
                } else {
                    Ok((
                        vec![LowerPrem::Judgement(ev_graph(
                            "cat",
                            &[mv(w), mv("%v")],
                            &mv(w2),
                        )?)],
                        mv(w2),
                        vec![w2],
                    ))
                }
            } else {
                let rest_tag = format!("{op}.{}", segs_key(rest));
                let mut args = vec![mv(w)];
                args.extend(tail_idx_terms.iter().cloned());
                args.push(mv("%v"));
                Ok((
                    vec![LowerPrem::Judgement(ev_graph(&rest_tag, &args, &mv(w2))?)],
                    mv(w2),
                    vec![w2],
                ))
            }
        };

    match seg {
        PathSeg::Dot(k) => {
            let field = |t: Term| app(con(format!("field.{k}")), t);
            // hit: the last field is `field.<k>` — rebuild with the payload
            // written along the tail.
            let (prems, w2t, extra) = tail_eval("%w", "%w2")?;
            let mut mvs: Vec<&str> = vec!["%s", "%w"];
            mvs.extend(tail_idx.iter().map(String::as_str));
            mvs.push("%v");
            mvs.extend(extra);
            let mut args = vec![app(mv("%s"), field(mv("%w"))?)?];
            args.extend(tail_idx_terms.iter().cloned());
            args.push(mv("%v"));
            let hit = clause(
                &mvs,
                prems,
                ev_graph(&this, &args, &app(mv("%s"), field(w2t)?)?)?,
            );
            // skip: carry a non-matching last field through unchanged.
            let mut prem_args = vec![mv("%s")];
            prem_args.extend(tail_idx_terms.iter().cloned());
            prem_args.push(mv("%v"));
            let mut skip_args = vec![app(mv("%s"), mv("%f"))?];
            skip_args.extend(tail_idx_terms.iter().cloned());
            skip_args.push(mv("%v"));
            let mut skip_mvs: Vec<&str> = vec!["%s", "%f"];
            skip_mvs.extend(tail_idx.iter().map(String::as_str));
            skip_mvs.extend(["%v", "%r"]);
            let skip = clause(
                &skip_mvs,
                vec![LowerPrem::Judgement(ev_graph(
                    &this,
                    &prem_args,
                    &mv("%r"),
                )?)],
                ev_graph(&this, &skip_args, &app(mv("%r"), mv("%f"))?)?,
            );
            Ok(vec![hit, skip])
        }
        PathSeg::Idx => {
            // hit: the write lands on the LAST element (`n = |xs|`).
            let (tail_prems, x2t, extra) = tail_eval("%x", "%x2")?;
            let mut prems = vec![LowerPrem::Judgement(ev_graph(
                "len",
                &[mv("%xs")],
                &wrap_nat(mv("%n"))?,
            )?)];
            prems.extend(tail_prems);
            let mut mvs: Vec<&str> = vec!["%xs", "%x", "%n"];
            mvs.extend(tail_idx.iter().map(String::as_str));
            mvs.push("%v");
            mvs.extend(extra);
            let mut args = vec![app(mv("%xs"), mv("%x"))?, wrap_nat(mv("%n"))?];
            args.extend(tail_idx_terms.iter().cloned());
            args.push(mv("%v"));
            let hit = clause(&mvs, prems, ev_graph(&this, &args, &app(mv("%xs"), x2t)?)?);
            // skip: the write lands strictly earlier; the last element rides.
            let mut prem_args = vec![mv("%xs"), wrap_nat(mv("%n"))?];
            prem_args.extend(tail_idx_terms.iter().cloned());
            prem_args.push(mv("%v"));
            let mut skip_args = vec![app(mv("%xs"), mv("%y"))?, wrap_nat(mv("%n"))?];
            skip_args.extend(tail_idx_terms.iter().cloned());
            skip_args.push(mv("%v"));
            let mut skip_mvs: Vec<&str> = vec!["%xs", "%y", "%n"];
            skip_mvs.extend(tail_idx.iter().map(String::as_str));
            skip_mvs.extend(["%v", "%r"]);
            let skip = clause(
                &skip_mvs,
                vec![LowerPrem::Judgement(ev_graph(
                    &this,
                    &prem_args,
                    &mv("%r"),
                )?)],
                ev_graph(&this, &skip_args, &app(mv("%r"), mv("%y"))?)?,
            );
            Ok(vec![hit, skip])
        }
        PathSeg::Slice => {
            // Decompose `s = prefix ++ old ++ suffix` with
            // `|prefix| = i`, `|old| = n`; evaluate the selected slice along
            // the remaining path, then rebuild
            // `prefix ++ selected' ++ suffix`. `ev.cat` and `ev.len` are
            // exact, so the witnesses describe precisely the addressed
            // segment (and replacement may change its length).
            let (mut tail_prems, selected, extra) = tail_eval("%old", "%selected")?;
            let mut prems = vec![
                LowerPrem::Judgement(ev_graph("len", &[mv("%prefix")], &wrap_nat(mv("%start"))?)?),
                LowerPrem::Judgement(ev_graph("len", &[mv("%old")], &wrap_nat(mv("%count"))?)?),
                LowerPrem::Judgement(ev_graph("cat", &[mv("%prefix"), mv("%old")], &mv("%left"))?),
                LowerPrem::Judgement(ev_graph("cat", &[mv("%left"), mv("%suffix")], &mv("%s"))?),
            ];
            prems.append(&mut tail_prems);
            prems.push(LowerPrem::Judgement(ev_graph(
                "cat",
                &[mv("%prefix"), selected],
                &mv("%newleft"),
            )?));
            prems.push(LowerPrem::Judgement(ev_graph(
                "cat",
                &[mv("%newleft"), mv("%suffix")],
                &mv("%r"),
            )?));

            let mut mvs: Vec<&str> = vec![
                "%prefix", "%old", "%left", "%suffix", "%s", "%start", "%count",
            ];
            mvs.extend(tail_idx.iter().map(String::as_str));
            mvs.push("%v");
            mvs.extend(extra);
            mvs.extend(["%newleft", "%r"]);
            let mut args = vec![mv("%s"), wrap_nat(mv("%start"))?, wrap_nat(mv("%count"))?];
            args.extend(tail_idx_terms);
            args.push(mv("%v"));
            Ok(vec![clause(
                &mvs,
                prems,
                ev_graph(&this, &args, &mv("%r"))?,
            )])
        }
    }
}

/// One `ev.neq` clause for the **ordered, distinct** case-key pair `(k1, k2)`:
/// `neq(case.<k1>(p), case.<k2>(q))`. Callers must check `k1 != k2` (distinct
/// keys are distinct constructors of any single comparison type, so the
/// disequality is genuine); this asserts it defensively.
pub fn neq_clause(k1: &str, k2: &str) -> Result<Vec<Clause>> {
    assert_ne!(k1, k2, "ev.neq: keys must be distinct");
    Ok(vec![clause(
        &["%p", "%q"],
        vec![],
        ev_graph(
            "neq",
            &[app(con(format!("case.{k1}")), mv("%p"))?],
            &app(con(format!("case.{k2}")), mv("%q"))?,
        )?,
    )])
}

/// Option-presence disequality, in both ordered directions.  These are the
/// complete complement of `opt.none` at genuine option encodings.
pub fn neq_option_clauses() -> Result<Vec<Clause>> {
    Ok(vec![
        clause(
            &["%x"],
            vec![],
            ev_graph("neq", &[con("opt.none")], &app(con("opt.some"), mv("%x"))?)?,
        ),
        clause(
            &["%x"],
            vec![],
            ev_graph("neq", &[app(con("opt.some"), mv("%x"))?], &con("opt.none"))?,
        ),
    ])
}

/// Disequality of encoded natural literals. The payloads are real HOL
/// naturals, so the side premise is kernel-computable at every ground point.
pub fn neq_nat_clauses() -> Result<Vec<Clause>> {
    let a = mv("%a");
    let b = mv("%b");
    Ok(vec![clause(
        &["%a", "%b"],
        vec![LowerPrem::Side(a.clone().equals(b.clone())?.not()?)],
        ev_graph("neq", &[app(con("num.nat"), a)?], &app(con("num.nat"), b)?)?,
    )])
}

/// Project an encoded natural value back to the shared wrapped-natural
/// result currency. This is an identity graph on genuine `num.nat` nodes,
/// used when another lowering seam has already materialized a full-encoding
/// call witness.
pub fn unnat_clause() -> Result<Vec<Clause>> {
    let n = mv("%n");
    let wrapped = app(con("num.nat"), n)?;
    Ok(vec![clause(
        &["%n"],
        vec![],
        ev_graph("unnat", &[wrapped.clone()], &wrapped)?,
    )])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic::{self, Premise};
    use crate::wasm::lower::rule_set_of;

    fn a(x: Term, y: Term) -> Term {
        app(x, y).unwrap()
    }

    #[test]
    fn option_disequality_is_exact_in_both_directions() {
        let rs = rule_set_of(neq_option_clauses().unwrap());
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 2);
        let payload = con("case.payload");
        for idx in 0..2 {
            let d = metalogic::derive_mixed(&rs, idx, n, &[payload.clone()], vec![]).unwrap();
            assert!(d.hyps().is_empty());
        }
    }

    #[test]
    fn encoded_natural_disequality_is_live_and_exact() {
        let rs = rule_set_of(neq_nat_clauses().unwrap());
        let n = rs.n_clauses().unwrap();
        let two = mk_nat(2u64);
        let three = mk_nat(3u64);
        let side_term = two.clone().equals(three.clone()).unwrap().not().unwrap();
        let side = super::super::flatten::prove_side(&side_term).unwrap();
        let d = metalogic::derive_mixed(
            &rs,
            0,
            n,
            &[two.clone(), three.clone()],
            vec![Premise::Side(side)],
        )
        .unwrap();
        assert!(d.hyps().is_empty());
        assert_eq!(
            d.concl(),
            &metalogic::derivable(
                &rs,
                &ev_graph("neq", &[a(con("num.nat"), two)], &a(con("num.nat"), three),).unwrap(),
            )
            .unwrap()
        );
    }

    #[test]
    fn unnat_projects_only_genuine_encoded_naturals() {
        let rs = rule_set_of(unnat_clause().unwrap());
        let n = rs.n_clauses().unwrap();
        let payload = mk_nat(7u64);
        let d = metalogic::derive_mixed(&rs, 0, n, std::slice::from_ref(&payload), vec![]).unwrap();
        assert!(d.hyps().is_empty());
        let wrapped = a(con("num.nat"), payload);
        assert_eq!(
            d.concl(),
            &metalogic::derivable(
                &rs,
                &ev_graph("unnat", &[wrapped.clone()], &wrapped).unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    fn signed_quotient_equals_positive_nat_exactly_and_refuses_bad_points() {
        let rs = rule_set_of(signed_div_eq_pos_nat_clauses().unwrap());
        let nclauses = rs.n_clauses().unwrap();
        assert_eq!(nclauses, 2);

        // 12 / 3 = 4, for both genuine same-sign encodings.
        let (a, b, n) = (mk_nat(12u64), mk_nat(3u64), mk_nat(4u64));
        let premises = || {
            [
                nat::nat_lt()
                    .apply(mk_nat(0u64))
                    .unwrap()
                    .apply(b.clone())
                    .unwrap(),
                nat::nat_lt()
                    .apply(mk_nat(0u64))
                    .unwrap()
                    .apply(n.clone())
                    .unwrap(),
                a.clone()
                    .equals(
                        nat::nat_mul()
                            .apply(n.clone())
                            .unwrap()
                            .apply(b.clone())
                            .unwrap(),
                    )
                    .unwrap(),
            ]
            .into_iter()
            .map(|p| {
                Premise::Side(
                    super::super::flatten::prove_side(&p).expect("ground quotient premise is true"),
                )
            })
            .collect()
        };
        for (idx, sign) in [0u64, 1].into_iter().enumerate() {
            let d = metalogic::derive_mixed(
                &rs,
                idx,
                nclauses,
                &[a.clone(), b.clone(), n.clone()],
                premises(),
            )
            .unwrap();
            assert!(d.hyps().is_empty());
            assert_eq!(
                d.concl(),
                &metalogic::derivable(
                    &rs,
                    &ev_graph(
                        "signed-div-eq-pos-nat",
                        &[
                            wrap_int(sign, a.clone()).unwrap(),
                            wrap_int(sign, b.clone()).unwrap(),
                            wrap_nat(n.clone()).unwrap(),
                        ],
                        &con("bool.true"),
                    )
                    .unwrap(),
                )
                .unwrap()
            );
        }

        // The exact relation has no opposite-sign clause.  A zero
        // denominator and a false cross-product are independently refused
        // by kernel-reducible side conditions.
        assert_eq!(nclauses, 2, "opposite signs have no defining clause");
        let zero_den = nat::nat_lt()
            .apply(mk_nat(0u64))
            .unwrap()
            .apply(mk_nat(0u64))
            .unwrap();
        assert!(super::super::flatten::prove_side(&zero_den).is_err());
        let wrong_product = mk_nat(11u64)
            .equals(
                nat::nat_mul()
                    .apply(mk_nat(4u64))
                    .unwrap()
                    .apply(mk_nat(3u64))
                    .unwrap(),
            )
            .unwrap();
        assert!(super::super::flatten::prove_side(&wrong_product).is_err());
    }

    #[test]
    fn slice_write_replaces_exact_segment_and_refuses_wrong_length() {
        let clauses: Vec<Clause> = upd_ext_families("upd", &[PathSeg::Slice])
            .unwrap()
            .into_iter()
            .flat_map(|(_, cs)| cs)
            .collect();
        // len(0,1), cat(2,3), upd.root.slice(4).
        let rs = rule_set_of(clauses);
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 5);

        let list = |xs: &[Term]| xs.iter().cloned().fold(con("list"), |acc, x| a(acc, x));
        let (va, vb, vc, vx, vy) = (
            con("case.A"),
            con("case.B"),
            con("case.C"),
            con("case.X"),
            con("case.Y"),
        );
        let prefix = list(std::slice::from_ref(&va));
        let old = list(std::slice::from_ref(&vb));
        let left = list(&[va.clone(), vb.clone()]);
        let suffix = list(std::slice::from_ref(&vc));
        let subject = list(&[va.clone(), vb, vc.clone()]);
        let replacement = list(&[vx.clone(), vy.clone()]);
        let newleft = list(&[va.clone(), vx, vy]);
        let result = list(&[va, con("case.X"), con("case.Y"), vc]);

        let len_one = |x: Term| {
            let z = metalogic::derive_mixed(&rs, 0, n, &[], vec![]).unwrap();
            let side = mk_nat(1u64)
                .equals(Term::succ().apply(mk_nat(0u64)).unwrap())
                .unwrap()
                .prove_true()
                .unwrap();
            metalogic::derive_mixed(
                &rs,
                1,
                n,
                &[con("list"), x, mk_nat(0u64), mk_nat(1u64)],
                vec![Premise::Side(side), Premise::Derivation(z)],
            )
            .unwrap()
        };
        let cat_one = |xs: Term, y: Term| {
            let base = metalogic::derive_mixed(&rs, 2, n, &[xs.clone()], vec![]).unwrap();
            metalogic::derive_mixed(
                &rs,
                3,
                n,
                &[xs.clone(), con("list"), y, xs],
                vec![Premise::Derivation(base)],
            )
            .unwrap()
        };
        let cat_many = |xs: Term, ys: &[Term]| {
            let mut state = xs.clone();
            let mut dom = con("list");
            let mut proof = metalogic::derive_mixed(&rs, 2, n, &[xs.clone()], vec![]).unwrap();
            for y in ys {
                let next = a(state.clone(), y.clone());
                proof = metalogic::derive_mixed(
                    &rs,
                    3,
                    n,
                    &[xs.clone(), dom.clone(), y.clone(), state],
                    vec![Premise::Derivation(proof)],
                )
                .unwrap();
                dom = a(dom, y.clone());
                state = next;
            }
            proof
        };

        let make_premises = || {
            vec![
                Premise::Derivation(len_one(con("case.A"))),
                Premise::Derivation(len_one(con("case.B"))),
                Premise::Derivation(cat_one(prefix.clone(), con("case.B"))),
                Premise::Derivation(cat_one(left.clone(), con("case.C"))),
                Premise::Derivation(cat_many(prefix.clone(), &[con("case.X"), con("case.Y")])),
                Premise::Derivation(cat_one(newleft.clone(), con("case.C"))),
            ]
        };
        let args = [
            prefix.clone(),
            old,
            left.clone(),
            suffix,
            subject,
            mk_nat(1u64),
            mk_nat(1u64),
            replacement,
            newleft.clone(),
            result,
        ];
        let d = metalogic::derive_mixed(&rs, 4, n, &args, make_premises()).unwrap();
        assert!(d.hyps().is_empty());
        assert!(
            metalogic::derive_mixed(
                &rs,
                4,
                n,
                &[
                    args[0].clone(),
                    args[1].clone(),
                    args[2].clone(),
                    args[3].clone(),
                    args[4].clone(),
                    args[5].clone(),
                    mk_nat(2u64),
                    args[7].clone(),
                    args[8].clone(),
                    args[9].clone(),
                ],
                make_premises(),
            )
            .is_err(),
            "a one-element old slice cannot witness a count of two"
        );
    }

    /// The write families evaluate a nested `upd` (`s[.F[0] := v]`) and an
    /// `ext` append (`s[.F ++= [b]]`) exactly on ground spines — and REFUSE
    /// an out-of-bounds write (`[a, b][2 := v]` has no derivation: the hit
    /// clause's `ev.len` premise cannot be met).
    #[test]
    fn write_families_evaluate_and_refuse() {
        // upd along [.F[·]] plus ext along [.F].
        let upd_fams = upd_ext_families("upd", &[PathSeg::Dot("F".into()), PathSeg::Idx]).unwrap();
        assert_eq!(
            upd_fams.iter().map(|(k, _)| k.as_str()).collect::<Vec<_>>(),
            ["len", "upd.root.idx", "upd.root.dot.F.idx"]
        );
        let ext_fams = upd_ext_families("ext", &[PathSeg::Dot("F".into())]).unwrap();
        assert_eq!(
            ext_fams.iter().map(|(k, _)| k.as_str()).collect::<Vec<_>>(),
            ["cat", "ext.root.dot.F"]
        );
        // Combined set: len(0,1) U2=upd.root.idx(2,3) U1=upd.root.dot.F.idx(4,5)
        // cat(6,7) E1=ext.root.dot.F(8,9); [hit, skip] within each family.
        let mut clauses: Vec<Clause> = upd_fams.into_iter().flat_map(|(_, c)| c).collect();
        clauses.extend(ext_fams.into_iter().flat_map(|(_, c)| c));
        let rs = rule_set_of(clauses);
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 10);
        let derive = |idx: usize, args: &[Term], prems: Vec<Premise>| {
            metalogic::derive_mixed(&rs, idx, n, args, prems)
        };

        let (va, vb, vv) = (con("case.A"), con("case.B"), con("case.V"));
        let list_a = a(con("list"), va.clone());
        let list_ab = a(list_a.clone(), vb.clone());
        let list_vb = a(a(con("list"), vv.clone()), vb.clone());
        let subj = |w: Term| a(con("struct"), a(con("field.F"), w));
        let zero = mk_nat(0u64);

        // -- upd: subj([a, b])[.F[0] := v] = subj([v, b]).
        let d_len0 = derive(0, &[], vec![]).unwrap();
        // U2 hit at the only element of [a] (index 0 = |[]|)…
        let d_hit = derive(
            2,
            &[con("list"), va.clone(), zero.clone(), vv.clone()],
            vec![Premise::Derivation(d_len0.clone())],
        )
        .unwrap();
        // …ridden over b by U2 skip…
        let d_u2 = derive(
            3,
            &[
                list_a.clone(),
                vb.clone(),
                zero.clone(),
                vv.clone(),
                a(con("list"), vv.clone()),
            ],
            vec![Premise::Derivation(d_hit)],
        )
        .unwrap();
        // …and rebuilt through the F field by U1 hit.
        let d_u1 = derive(
            4,
            &[
                con("struct"),
                list_ab.clone(),
                zero.clone(),
                vv.clone(),
                list_vb.clone(),
            ],
            vec![Premise::Derivation(d_u2)],
        )
        .unwrap();
        assert!(d_u1.hyps().is_empty());
        let expected = metalogic::derivable(
            &rs,
            &ev_graph(
                "upd.root.dot.F.idx",
                &[
                    subj(list_ab.clone()),
                    wrap_nat(zero.clone()).unwrap(),
                    vv.clone(),
                ],
                &subj(list_vb),
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(d_u1.concl(), &expected, "the exact updated encoding");

        // -- REFUSE: [a, b][2 := v] is out of bounds — the hit clause needs
        // `len([a], 2)`, and no genuine length theorem meets it.
        let two = mk_nat(2u64);
        let d_len1 = derive(1, &[con("list"), va.clone(), mk_nat(0u64), mk_nat(1u64)], {
            let d = derive(0, &[], vec![]).unwrap();
            let side = mk_nat(1u64)
                .equals(Term::succ().apply(mk_nat(0u64)).unwrap())
                .unwrap()
                .prove_true()
                .unwrap();
            vec![Premise::Side(side), Premise::Derivation(d)]
        })
        .unwrap(); // len([a], 0+1)
        assert!(
            derive(
                2,
                &[list_a.clone(), vb.clone(), two, vv.clone()],
                vec![Premise::Derivation(d_len1)],
            )
            .is_err(),
            "out-of-bounds write must not derive"
        );

        // -- ext: subj([a])[.F ++= [b]] = subj([a, b]) through ev.cat.
        let d_cat_base = derive(6, &[list_a.clone()], vec![]).unwrap();
        let d_cat = derive(
            7,
            &[list_a.clone(), con("list"), vb.clone(), list_a.clone()],
            vec![Premise::Derivation(d_cat_base)],
        )
        .unwrap(); // cat([a], [b], [a, b])
        let d_e1 = derive(
            8,
            &[
                con("struct"),
                list_a.clone(),
                a(con("list"), vb.clone()),
                list_ab.clone(),
            ],
            vec![Premise::Derivation(d_cat)],
        )
        .unwrap();
        let expected = metalogic::derivable(
            &rs,
            &ev_graph(
                "ext.root.dot.F",
                &[subj(list_a), a(con("list"), vb)],
                &subj(list_ab),
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(d_e1.concl(), &expected, "the exact extended encoding");
    }
}

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

/// `ev.len` — snoc-spine length with real-nat results:
/// `len([], 0)` and `len(xs, n) ⟹ len(xs·x, n + 1)`.
pub fn len_clauses() -> Result<Vec<Clause>> {
    let base = clause(
        &[],
        vec![],
        ev_graph("len", &[con("list")], &wrap_nat(mk_nat(0u64))?)?,
    );
    let n1 = nat::nat_add().apply(mv("%n"))?.apply(mk_nat(1u64))?;
    let step = clause(
        &["%xs", "%x", "%n"],
        vec![LowerPrem::Judgement(ev_graph(
            "len",
            &[mv("%xs")],
            &wrap_nat(mv("%n"))?,
        )?)],
        ev_graph("len", &[app(mv("%xs"), mv("%x"))?], &wrap_nat(n1)?)?,
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
/// approximated — so [`path_segs`] refuses and the expression keeps its
/// coarse spine (censused by the `Dec` leg's coarse-spine honesty).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathSeg {
    /// `.<key>` — descend into the (unique-per-struct) `field.<key>` payload.
    Dot(String),
    /// `[i]` — descend to a list index (consumes one index argument).
    Idx,
}

/// Decompose an access path into root-first segments (`None` on `Slice`).
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
            SpecTecPath::Slice { .. } => false,
        }
    }
    let mut out = Vec::new();
    go(p, &mut out).then_some(out)
}

/// The index expressions of a path, root-first — the index-argument order of
/// the write judgements (total; callers gate on [`path_segs`] first, so
/// `Slice` bounds are never consulted).
pub fn path_index_exprs<'e>(p: &'e SpecTecPath, out: &mut Vec<&'e SpecTecExp>) {
    match p {
        SpecTecPath::Root => {}
        SpecTecPath::Idx { p1, e } => {
            path_index_exprs(p1, out);
            out.push(e);
        }
        SpecTecPath::Slice { p1, .. } | SpecTecPath::Dot { p1, .. } => path_index_exprs(p1, out),
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
        }
    }
    k
}

fn n_idx(segs: &[PathSeg]) -> usize {
    segs.iter().filter(|s| matches!(s, PathSeg::Idx)).count()
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
    if n_idx(segs) > 0 {
        out.push(("len".to_string(), len_clauses()?));
    }
    if op == "ext" {
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
    let tail_idx: Vec<String> = (0..n_idx(rest)).map(|j| format!("%i{j}")).collect();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic::{self, Premise};
    use crate::wasm::lower::rule_set_of;

    fn a(x: Term, y: Term) -> Term {
        app(x, y).unwrap()
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
        let d_len1 = derive(1, &[con("list"), va.clone(), mk_nat(0u64)], {
            let d = derive(0, &[], vec![]).unwrap();
            vec![Premise::Derivation(d)]
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

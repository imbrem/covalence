//! Canonical S-expression syntax for kernel terms, types, and theorems.
//!
//! Outside the TCB. The kernel does not consume S-expressions for any
//! inference; this module exists so callers (tests, the REPL, FFI
//! bridges, Python bindings) can round-trip the kernel data model.
//!
//! ## Fresh constants are not serialisable
//!
//! The kernel's `TermKind::FreshConst` / `TypeKind::FreshTyCon` leaves
//! (the `new_type_definition` freshness tokens) are **process-local**
//! `Arc` identities; there is no cross-process representation that
//! preserves their unforgeability, so serialising a term containing
//! one is an error. (The old handler-based `obs` / `tycon-obs` grammar
//! forms were deleted in the toHOL purge along with the observer
//! system.)
//!
//! ## Grammar
//!
//! Types:
//!
//! ```text
//! type ::= (tfree NAME)              ;; a type variable
//!       |  (nat) | (bool) | (unit)   ;; primitive / catalogue types
//!       |  (fun TYPE TYPE)           ;; function type τ ⇒ σ
//!       |  (tycon NAME TYPE*)        ;; user-declared structural tycon
//!       |  (spec LABEL TYPE*)        ;; canonical derived TypeSpec
//! ```
//!
//! Terms (binders are anonymous — `INDEX` is a de Bruijn index):
//!
//! ```text
//! term ::= (bound INDEX)
//!       |  (free NAME TYPE)
//!       |  (const NAME TYPE)
//!       |  (app TERM TERM)
//!       |  (abs TYPE TERM)
//!       |  (eq TYPE)
//!       |  (select TYPE)
//!       |  (succ)
//!       |  (blob BYTES)
//!       |  (small-int TAG BITS)
//!       |  (def NAME TERM)
//! ```
//!
//! Theorems serialise but do **not** parse back from S-expressions.

use bytes::Bytes;
use covalence_core::{IntTag, SmallIntLiteral, Term, TermKind, Thm, Type, TypeKind};
use covalence_sexp::{Atom, SExp, SExpr};

/// Errors produced by S-expression parsing of Core terms / types.
#[derive(Debug, thiserror::Error)]
#[error("S-expression syntax: {0}")]
pub struct SexpError(pub String);

type Result<T> = std::result::Result<T, SexpError>;

// ============================================================================
// Types
// ============================================================================

/// Serialise a `Type` to S-expression form. Errors on a `FreshTyCon`
/// (process-local `new_type_definition` identity — not serialisable).
pub fn type_to_sexp(ty: &Type) -> Result<SExpr> {
    Ok(match ty.kind() {
        TypeKind::TFree(name) => list2("tfree", sym(name)),
        TypeKind::Nat => list1("nat"),
        TypeKind::Bool => list1("bool"),
        TypeKind::Fun(a, b) => list3("fun", type_to_sexp(a)?, type_to_sexp(b)?),
        TypeKind::Tycon(name, args) => {
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("tycon"));
            children.push(sym(name));
            for arg in args {
                children.push(type_to_sexp(arg)?);
            }
            SExp::List(children)
        }
        TypeKind::FreshTyCon(leaf) => {
            return Err(SexpError(format!(
                "fresh tycon#{:x} is process-local and not serialisable",
                leaf.id().ptr_id()
            )));
        }
        TypeKind::Spec(spec, args) => {
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("spec"));
            children.push(sym(spec.symbol().label()));
            for arg in args {
                children.push(type_to_sexp(arg)?);
            }
            SExp::List(children)
        }
    })
}

/// Parse a `Type` from S-expression form.
pub fn type_from_sexp(s: &SExpr) -> Result<Type> {
    let children = expect_list(s, "type")?;
    let head = head_symbol(children)?;
    match head {
        "tfree" => {
            expect_arity(children, 2, "tfree")?;
            Ok(Type::tfree(expect_symbol(&children[1], "tfree name")?))
        }
        "nat" => {
            expect_arity(children, 1, "nat")?;
            Ok(Type::nat())
        }
        "unit" => {
            expect_arity(children, 1, "unit")?;
            Ok(Type::unit())
        }
        "bool" => {
            expect_arity(children, 1, "bool")?;
            Ok(Type::bool())
        }
        "spec" => parse_type_spec(children),
        "fun" => {
            expect_arity(children, 3, "fun")?;
            Ok(Type::fun(
                type_from_sexp(&children[1])?,
                type_from_sexp(&children[2])?,
            ))
        }
        "tycon" => {
            if children.len() < 2 {
                return Err(SexpError("tycon: missing name".into()));
            }
            let name = expect_symbol(&children[1], "tycon name")?;
            let args = children[2..]
                .iter()
                .map(type_from_sexp)
                .collect::<Result<Vec<_>>>()?;
            Ok(Type::tycon(name, args))
        }
        other => Err(SexpError(format!("unknown type head: {}", other))),
    }
}

/// Parse a `(spec LABEL TYPE*)` form by looking up `LABEL` in the
/// canonical TypeSpec catalogue. This is the round-trip inverse of
/// the `TypeKind::Spec` printer above.
fn parse_type_spec(children: &[SExpr]) -> Result<Type> {
    use covalence_core::defs;

    if children.len() < 2 {
        return Err(SexpError("spec: missing canonical label".into()));
    }
    let label = expect_symbol(&children[1], "spec label")?;
    let args = children[2..]
        .iter()
        .map(type_from_sexp)
        .collect::<Result<Vec<_>>>()?;
    let spec = match label {
        // Canonical `defs/` TypeSpecs, keyed by the label that
        // `(spec LABEL …)` printed.
        "int" => defs::int_ty_spec(),
        "bytes" => defs::bytes_spec(),
        "unit" => defs::unit_spec(),
        // Other canonical TypeSpecs land here as the type-hierarchy
        // catalogue gets wired up. Anything not recognised is an error.
        other => {
            return Err(SexpError(format!(
                "spec: unknown canonical type label {other:?}"
            )));
        }
    };
    Ok(Type::spec(spec, args))
}

// ============================================================================
// Terms
// ============================================================================

/// Serialise an `abs`/`rep` spec coercion as `(HEAD LABEL TYPE*)`,
/// mirroring the `(term-spec …)` shape. `HEAD` is `spec-abs` or
/// `spec-rep`.
fn spec_coercion_to_sexp(
    head: &str,
    spec: &covalence_core::defs::TypeSpec,
    args: &[Type],
) -> Result<SExpr> {
    let mut children = Vec::with_capacity(2 + args.len());
    children.push(sym(head));
    children.push(sym(spec.symbol().label()));
    for arg in args {
        children.push(type_to_sexp(arg)?);
    }
    Ok(SExp::List(children))
}

/// Serialise a `Term` to S-expression form. Errors on a `FreshConst`
/// (process-local `new_type_definition` identity — not serialisable).
pub fn term_to_sexp(t: &Term) -> Result<SExpr> {
    Ok(match t.kind() {
        TermKind::Bound(i) => list2("bound", sym(i.to_string().as_str())),
        TermKind::Free(v) => list3("free", sym(v.name()), type_to_sexp(v.ty())?),
        TermKind::Const(name, ty) => list3("const", sym(name), type_to_sexp(ty)?),
        TermKind::App(f, x) => list3("app", term_to_sexp(f)?, term_to_sexp(x)?),
        TermKind::Abs(ty, body) => list3("abs", type_to_sexp(ty)?, term_to_sexp(body)?),
        TermKind::Blob(bytes) => list2(
            "blob",
            SExp::Atom(Atom::Str {
                format: "b".into(),
                bytes: bytes.clone(),
            }),
        ),
        TermKind::Nat(n) => list2("nat-lit", sym(n.as_inner().to_string().as_str())),
        TermKind::Int(n) => list2("int-lit", sym(n.as_inner().to_string().as_str())),
        TermKind::SmallInt(lit) => list3(
            "small-int",
            sym(lit.tag.label()),
            sym(lit.bits.to_string().as_str()),
        ),
        TermKind::Bool(b) => list2("bool-lit", sym(if *b { "T" } else { "F" })),
        TermKind::Eq(alpha) => list2("eq", type_to_sexp(alpha)?),
        TermKind::Select(alpha) => list2("select", type_to_sexp(alpha)?),
        TermKind::Succ => list1("succ"),
        TermKind::Spec(spec, args) => {
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("term-spec"));
            children.push(sym(spec.symbol().label()));
            for arg in args {
                children.push(type_to_sexp(arg)?);
            }
            SExp::List(children)
        }
        TermKind::SpecAbs(spec, args) => spec_coercion_to_sexp("spec-abs", spec, args)?,
        TermKind::SpecRep(spec, args) => spec_coercion_to_sexp("spec-rep", spec, args)?,
        TermKind::FreshConst(leaf) => {
            return Err(SexpError(format!(
                "fresh constant fresh#{:x} is process-local and not serialisable",
                leaf.id().ptr_id()
            )));
        }
        TermKind::Def(d) => list3("def", sym(d.name()), term_to_sexp(&d.body())?),
    })
}

/// Parse a `Term` from S-expression form.
pub fn term_from_sexp(s: &SExpr) -> Result<Term> {
    let children = expect_list(s, "term")?;
    let head = head_symbol(children)?;
    match head {
        "bound" => {
            expect_arity(children, 2, "bound")?;
            let s = expect_symbol(&children[1], "bound index")?;
            let i = s
                .parse::<u32>()
                .map_err(|e| SexpError(format!("bound: not a u32: {}", e)))?;
            Ok(Term::bound(i))
        }
        "free" => {
            expect_arity(children, 3, "free")?;
            let name = expect_symbol(&children[1], "free name")?;
            let ty = type_from_sexp(&children[2])?;
            Ok(Term::free(name, ty))
        }
        "const" => {
            expect_arity(children, 3, "const")?;
            let name = expect_symbol(&children[1], "const name")?;
            let ty = type_from_sexp(&children[2])?;
            Ok(Term::const_(name, ty))
        }
        "app" => {
            expect_arity(children, 3, "app")?;
            Ok(Term::app(
                term_from_sexp(&children[1])?,
                term_from_sexp(&children[2])?,
            ))
        }
        "abs" => {
            expect_arity(children, 3, "abs")?;
            let ty = type_from_sexp(&children[1])?;
            let body = term_from_sexp(&children[2])?;
            Ok(Term::abs(ty, body))
        }
        "blob" => {
            expect_arity(children, 2, "blob")?;
            let (format, bytes) = expect_str(&children[1], "blob bytes")?;
            if format != "b" {
                return Err(SexpError(format!(
                    "blob: expected b\"…\" literal, got format {:?}",
                    format
                )));
            }
            Ok(Term::blob(bytes.clone()))
        }
        "small-int" => {
            expect_arity(children, 3, "small-int")?;
            let tag_s = expect_symbol(&children[1], "small-int tag")?;
            let tag = IntTag::from_label(tag_s)
                .ok_or_else(|| SexpError(format!("small-int: unknown tag {:?}", tag_s)))?;
            let bits_s = expect_symbol(&children[2], "small-int bits")?;
            let bits = bits_s
                .parse::<u64>()
                .map_err(|e| SexpError(format!("small-int: not a u64: {}", e)))?;
            Ok(Term::small_int(SmallIntLiteral::new(tag, bits)))
        }
        "eq" => {
            expect_arity(children, 2, "eq")?;
            Ok(Term::eq_op(type_from_sexp(&children[1])?))
        }
        "select" => {
            expect_arity(children, 2, "select")?;
            Ok(Term::select_op(type_from_sexp(&children[1])?))
        }
        "succ" => {
            expect_arity(children, 1, "succ")?;
            Ok(Term::succ())
        }
        "def" => {
            // Round-trip via S-expressions *does not* preserve `Def`
            // identity: we mint a fresh `Def` from the parsed (name,
            // body). This is intentional — `Def` identity is a
            // per-process `Arc` pointer, not a serialisable concept.
            expect_arity(children, 3, "def")?;
            let name = expect_symbol(&children[1], "def name")?;
            let body = term_from_sexp(&children[2])?;
            // Construct via a fresh `Thm::define` would give us the
            // Thm too, but the sexp shell only needs the Term.
            // Reuse the kernel's path by calling `Thm::define` and
            // extracting its conclusion's LHS, or just rebuild the
            // Term shape directly. We use `Term::def` via a fresh
            // `Def` constructed through a kernel rule call to keep
            // the construction visible.
            let thm = covalence_core::Thm::define(name, body)
                .map_err(|e| SexpError(format!("invalid def: {}", e)))?;
            // The Thm has conclusion `Def(name, body) = body` (HOL
            // equation). Walk the two `App`s to extract the LHS (the
            // `Term::def` leaf).
            let TermKind::App(eq_lhs_app, _) = thm.concl().kind() else {
                return Err(SexpError(
                    "kernel produced unexpected define Thm shape".into(),
                ));
            };
            let TermKind::App(_, lhs) = eq_lhs_app.kind() else {
                return Err(SexpError(
                    "kernel produced unexpected define Thm shape".into(),
                ));
            };
            Ok(lhs.clone())
        }
        other => Err(SexpError(format!("unknown term head: {}", other))),
    }
}

// ============================================================================
// Theorems (one-way: serialise only)
// ============================================================================

pub fn thm_to_sexp(thm: &Thm) -> Result<SExpr> {
    let mut hyps_list = Vec::with_capacity(1 + thm.hyps().len());
    hyps_list.push(sym("hyps"));
    for h in thm.hyps() {
        hyps_list.push(term_to_sexp(h)?);
    }
    Ok(SExp::List(vec![
        sym("thm"),
        SExp::List(hyps_list),
        SExp::List(vec![sym("concl"), term_to_sexp(thm.concl())?]),
    ]))
}

// ============================================================================
// Helpers
// ============================================================================

fn sym(s: &str) -> SExpr {
    SExp::Atom(Atom::Symbol(s.into()))
}

fn list1(head: &str) -> SExpr {
    SExp::List(vec![sym(head)])
}
fn list2(head: &str, a: SExpr) -> SExpr {
    SExp::List(vec![sym(head), a])
}
fn list3(head: &str, a: SExpr, b: SExpr) -> SExpr {
    SExp::List(vec![sym(head), a, b])
}

fn expect_list<'a>(s: &'a SExpr, what: &str) -> Result<&'a [SExpr]> {
    match s {
        SExp::List(children) => Ok(children),
        SExp::Atom(_) => Err(SexpError(format!("expected list for {}, got atom", what))),
    }
}

fn head_symbol(children: &[SExpr]) -> Result<&str> {
    let head = children
        .first()
        .ok_or_else(|| SexpError("empty list".into()))?;
    match head {
        SExp::Atom(Atom::Symbol(s)) => Ok(s.as_str()),
        _ => Err(SexpError("list head is not a symbol".into())),
    }
}

fn expect_arity(children: &[SExpr], n: usize, what: &str) -> Result<()> {
    if children.len() != n {
        Err(SexpError(format!(
            "{}: expected {} elements, got {}",
            what,
            n,
            children.len()
        )))
    } else {
        Ok(())
    }
}

fn expect_symbol<'a>(s: &'a SExpr, what: &str) -> Result<&'a str> {
    match s {
        SExp::Atom(Atom::Symbol(sym)) => Ok(sym.as_str()),
        _ => Err(SexpError(format!("{}: not a symbol", what))),
    }
}

fn expect_str<'a>(s: &'a SExpr, what: &str) -> Result<(&'a str, &'a Bytes)> {
    match s {
        SExp::Atom(Atom::Str { format, bytes }) => Ok((format.as_str(), bytes)),
        _ => Err(SexpError(format!("{}: not a string", what))),
    }
}

//! Canonical S-expression syntax for kernel terms, types, and theorems.
//!
//! Outside the TCB. The kernel does not consume S-expressions for any
//! inference; this module exists so callers (tests, the REPL, FFI
//! bridges, Python bindings) can round-trip the kernel data model.
//!
//! ## Observers (Object) handling
//!
//! The kernel's `TermKind::Obs` leaves carry a [`Object`] — a
//! type-erased observation handle. This module cannot know about
//! every user observer type, so serialisation and parsing of the
//! `obs` form delegate to a caller-supplied **handler**:
//!
//! - [`ObsSerializer`] takes a `&Object` and produces the s-expression
//!   payload for the observer (typically by attempting `downcast` to
//!   known types).
//! - [`ObsParser`] takes the payload s-expression and produces a
//!   `Object`.
//!
//! The default [`UnitObs`] handler covers the trivial `()` observer
//! by round-tripping through nil (the empty list). User crates with
//! their own observer types compose richer handlers, often by
//! falling back to `UnitObs` for the `()` case.
//!
//! ## Grammar
//!
//! Types:
//!
//! ```text
//! type ::= (tfree NAME)              ;; a type variable
//!       |  (prop)                    ;; the kind of meta-propositions
//!       |  (bytes)                   ;; the type of Blob(_) terms
//!       |  (fun TYPE TYPE)           ;; function type τ ⇒ σ
//!       |  (tycon NAME TYPE*)        ;; user-declared structural tycon
//!       |  (tycon-obs OBS TYPE*)     ;; Arc-identity tycon (process-local;
//!                                       OBS payload is handler-specific)
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
//!       |  (eq TERM TERM)
//!       |  (blob BYTES)
//!       |  (obs OBS TYPE)            ;; OBS payload is handler-specific
//! ```
//!
//! Theorems serialise but do **not** parse back from S-expressions.

use bytes::Bytes;
use covalence_core::{IntTag, Object, SmallIntLiteral, Term, TermKind, Thm, Type, TypeKind};
use covalence_sexp::{Atom, SExp, SExpr};

/// Errors produced by S-expression parsing of Core terms / types.
#[derive(Debug, thiserror::Error)]
#[error("S-expression syntax: {0}")]
pub struct SexpError(pub String);

type Result<T> = std::result::Result<T, SexpError>;

// ============================================================================
// Observer handler traits
// ============================================================================

/// Serialise a [`Object`] payload to S-expression form. Implementations
/// typically inspect the dynamic type via [`Object::downcast`] and
/// emit a chosen format; if no known type matches, they return an
/// error.
///
/// The shell calls this for every `obs` leaf it serialises; the
/// returned `SExpr` becomes the payload child of the `(obs PAYLOAD
/// TYPE)` form.
pub trait ObsSerializer {
    fn obs_to_sexp(&self, observer: &Object) -> Result<SExpr>;
}

/// Parse a [`Object`] payload from an S-expression. The shell calls
/// this for every `obs` leaf it parses; the s-expression is the
/// payload child of the `(obs PAYLOAD TYPE)` form.
pub trait ObsParser {
    fn obs_from_sexp(&self, payload: &SExpr) -> Result<Object>;
}

/// Trivial handler: round-trips the unit observer `()` through nil
/// (the empty list). Any other observer type produces an error on
/// serialise and any non-nil payload produces an error on parse.
///
/// Most real callers compose `UnitObs` with their own handlers — fall
/// back to `UnitObs` for the `()` case, handle their custom types
/// directly.
pub struct UnitObs;

impl ObsSerializer for UnitObs {
    fn obs_to_sexp(&self, observer: &Object) -> Result<SExpr> {
        if observer.downcast::<()>().is_some() {
            Ok(SExp::List(vec![]))
        } else {
            Err(SexpError(format!(
                "UnitObs: cannot serialise observer of type {:?}",
                observer.type_id()
            )))
        }
    }
}

impl ObsParser for UnitObs {
    fn obs_from_sexp(&self, payload: &SExpr) -> Result<Object> {
        match payload {
            SExp::List(children) if children.is_empty() => Ok(Object::new(())),
            _ => Err(SexpError(
                "UnitObs: expected nil () payload for () observer".into(),
            )),
        }
    }
}

// ============================================================================
// Types
// ============================================================================

/// Serialise a `Type` to S-expression form. `ser` is used only when
/// the type contains a `TyConObs` — pass any handler (commonly
/// [`UnitObs`]) when working with types known to be free of observer
/// constructors.
pub fn type_to_sexp(ty: &Type, ser: &dyn ObsSerializer) -> Result<SExpr> {
    Ok(match ty.kind() {
        TypeKind::TFree(name) => list2("tfree", sym(name)),
        TypeKind::Nat => list1("nat"),
        TypeKind::Bool => list1("bool"),
        TypeKind::Fun(a, b) => list3("fun", type_to_sexp(a, ser)?, type_to_sexp(b, ser)?),
        TypeKind::Tycon(name, args) => {
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("tycon"));
            children.push(sym(name));
            for arg in args {
                children.push(type_to_sexp(arg, ser)?);
            }
            SExp::List(children)
        }
        TypeKind::TyConObs(observer, args) => {
            let payload = ser.obs_to_sexp(observer)?;
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("tycon-obs"));
            children.push(payload);
            for arg in args {
                children.push(type_to_sexp(arg, ser)?);
            }
            SExp::List(children)
        }
        TypeKind::Spec(spec, args) => {
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("spec"));
            children.push(sym(spec.symbol().label()));
            for arg in args {
                children.push(type_to_sexp(arg, ser)?);
            }
            SExp::List(children)
        }
    })
}

/// Parse a `Type` from S-expression form. `parser` is used only when
/// the input mentions a `tycon-obs` form.
pub fn type_from_sexp(s: &SExpr, parser: &dyn ObsParser) -> Result<Type> {
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
        "spec" => parse_type_spec(children, parser),
        "fun" => {
            expect_arity(children, 3, "fun")?;
            Ok(Type::fun(
                type_from_sexp(&children[1], parser)?,
                type_from_sexp(&children[2], parser)?,
            ))
        }
        "tycon" => {
            if children.len() < 2 {
                return Err(SexpError("tycon: missing name".into()));
            }
            let name = expect_symbol(&children[1], "tycon name")?;
            let args = children[2..]
                .iter()
                .map(|c| type_from_sexp(c, parser))
                .collect::<Result<Vec<_>>>()?;
            Ok(Type::tycon(name, args))
        }
        "tycon-obs" => {
            if children.len() < 2 {
                return Err(SexpError(
                    "tycon-obs: expected (tycon-obs PAYLOAD TYPE*)".into(),
                ));
            }
            let observer = parser.obs_from_sexp(&children[1])?;
            let args = children[2..]
                .iter()
                .map(|c| type_from_sexp(c, parser))
                .collect::<Result<Vec<_>>>()?;
            Ok(Type::tycon_obs_from_dyn(observer, args))
        }
        other => Err(SexpError(format!("unknown type head: {}", other))),
    }
}

/// Parse a `(spec LABEL TYPE*)` form by looking up `LABEL` in the
/// canonical TypeSpec catalogue. This is the round-trip inverse of
/// the `TypeKind::Spec` printer at line 159 above.
fn parse_type_spec(children: &[SExpr], parser: &dyn ObsParser) -> Result<Type> {
    use covalence_core::defs;

    if children.len() < 2 {
        return Err(SexpError("spec: missing canonical label".into()));
    }
    let label = expect_symbol(&children[1], "spec label")?;
    let args = children[2..]
        .iter()
        .map(|c| type_from_sexp(c, parser))
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
    ser: &dyn ObsSerializer,
) -> Result<SExpr> {
    let mut children = Vec::with_capacity(2 + args.len());
    children.push(sym(head));
    children.push(sym(spec.symbol().label()));
    for arg in args {
        children.push(type_to_sexp(arg, ser)?);
    }
    Ok(SExp::List(children))
}

/// Serialise a `Term` to S-expression form, delegating `Obs` payloads
/// to `ser`.
pub fn term_to_sexp(t: &Term, ser: &dyn ObsSerializer) -> Result<SExpr> {
    Ok(match t.kind() {
        TermKind::Bound(i) => list2("bound", sym(i.to_string().as_str())),
        TermKind::Free(name, ty) => list3("free", sym(name), type_to_sexp(ty, ser)?),
        TermKind::Const(name, ty) => list3("const", sym(name), type_to_sexp(ty, ser)?),
        TermKind::App(f, x) => list3("app", term_to_sexp(f, ser)?, term_to_sexp(x, ser)?),
        TermKind::Abs(ty, body) => list3("abs", type_to_sexp(ty, ser)?, term_to_sexp(body, ser)?),
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
        TermKind::Eq(alpha) => list2("eq", type_to_sexp(alpha, ser)?),
        TermKind::Select(alpha) => list2("select", type_to_sexp(alpha, ser)?),
        TermKind::Succ => list1("succ"),
        TermKind::Spec(spec, args) => {
            let mut children = Vec::with_capacity(2 + args.len());
            children.push(sym("term-spec"));
            children.push(sym(spec.symbol().label()));
            for arg in args {
                children.push(type_to_sexp(arg, ser)?);
            }
            SExp::List(children)
        }
        TermKind::SpecAbs(spec, args) => spec_coercion_to_sexp("spec-abs", spec, args, ser)?,
        TermKind::SpecRep(spec, args) => spec_coercion_to_sexp("spec-rep", spec, args, ser)?,
        TermKind::Obs(observer, ty) => {
            let payload = ser.obs_to_sexp(observer)?;
            list3("obs", payload, type_to_sexp(ty, ser)?)
        }
        TermKind::Def(d) => list3("def", sym(d.name()), term_to_sexp(&d.body(), ser)?),
    })
}

/// Parse a `Term` from S-expression form, delegating `Obs` payloads
/// to `parser`.
pub fn term_from_sexp(s: &SExpr, parser: &dyn ObsParser) -> Result<Term> {
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
            let ty = type_from_sexp(&children[2], parser)?;
            Ok(Term::free(name, ty))
        }
        "const" => {
            expect_arity(children, 3, "const")?;
            let name = expect_symbol(&children[1], "const name")?;
            let ty = type_from_sexp(&children[2], parser)?;
            Ok(Term::const_(name, ty))
        }
        "app" => {
            expect_arity(children, 3, "app")?;
            Ok(Term::app(
                term_from_sexp(&children[1], parser)?,
                term_from_sexp(&children[2], parser)?,
            ))
        }
        "abs" => {
            expect_arity(children, 3, "abs")?;
            let ty = type_from_sexp(&children[1], parser)?;
            let body = term_from_sexp(&children[2], parser)?;
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
        "obs" => {
            expect_arity(children, 3, "obs")?;
            let observer = parser.obs_from_sexp(&children[1])?;
            let ty = type_from_sexp(&children[2], parser)?;
            Ok(Term::obs_from_dyn(observer, ty))
        }
        "eq" => {
            expect_arity(children, 2, "eq")?;
            Ok(Term::eq_op(type_from_sexp(&children[1], parser)?))
        }
        "select" => {
            expect_arity(children, 2, "select")?;
            Ok(Term::select_op(type_from_sexp(&children[1], parser)?))
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
            let body = term_from_sexp(&children[2], parser)?;
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

pub fn thm_to_sexp(thm: &Thm, ser: &dyn ObsSerializer) -> Result<SExpr> {
    let mut hyps_list = Vec::with_capacity(1 + thm.hyps().len());
    hyps_list.push(sym("hyps"));
    for h in thm.hyps() {
        hyps_list.push(term_to_sexp(h, ser)?);
    }
    Ok(SExp::List(vec![
        sym("thm"),
        SExp::List(hyps_list),
        SExp::List(vec![sym("concl"), term_to_sexp(thm.concl(), ser)?]),
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

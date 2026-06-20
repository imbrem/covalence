//! A small, **synchronous, total** `.cov` parser for the kernel's
//! closed *term sublanguage* (`docs/surface-syntax.md §1.4`).
//!
//! This is the first step of lifting the `defs/` catalogue out of
//! hand-threaded `Term::app` / `Term::abs` Rust and into data: a `.cov`
//! file is a sequence of four directives —
//!
//! ```text
//! (#def     name term)        ;; a term constant  name ≡ term
//! (#newtype name ty)          ;; TypeSpec::newtype
//! (#subtype name ty pred)     ;; TypeSpec::subtype  { x : ty | pred x }
//! (#quot    name ty rel)      ;; TypeSpec::quotient  ty / rel
//! ```
//!
//! — over a minimal simply-typed lambda sublanguage. There is **no
//! inference**: every binder is type-ascribed, and polymorphic
//! catalogue constants are instantiated with explicit type arguments.
//!
//! ## Trust status
//!
//! This module lives in the same `defs/` semi-trusted tier as the
//! hand-written catalogue it replaces. It builds kernel `Term`s /
//! `Type`s / specs *exactly* as the Rust would; it never constructs a
//! `Thm`. There is **no `unsafe`** and every path returns a `CovError`
//! rather than panicking on malformed input.
//!
//! ## How `covalence-sexp` is used
//!
//! The S-expression *reader* is [`covalence_sexp::parse`] (the
//! Covalence dialect) — we never hand-roll a tokenizer. This module is
//! purely a *lowering* from [`SExpr`] into kernel objects. The same
//! reader makes for much cleaner tests: expected terms/types can be
//! written as `.cov` snippets ([`term_str`] / [`type_str`]) instead of
//! hand-built `Term::app` chains.
//!
//! ## Catalogue references and identity
//!
//! A bare `NAME` resolves, in order, to (1) a binder in scope, (2) a
//! prior `#def` / type definition in this file, (3) a kernel catalogue
//! constant (`bool.and`, `unit.nil`, …). Polymorphic catalogue
//! constants are written `(#at NAME ty …)` — the explicit type
//! application. Crucially the resolver returns the *cached* `defs::*`
//! accessor objects, so a parsed reference to `bool.and` is the very
//! same `Arc`-shared spec leaf the hand-written `defs::and()` returns:
//! parsed and hand-written objects are then **byte-identical** (`==`),
//! which the tests assert.

use std::collections::BTreeMap;

use covalence_sexp::{Atom, SExp, SExpr};
use covalence_types::{Int, Nat};

use crate::subst::close;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TypeSpec;

// ============================================================================
// Errors
// ============================================================================

/// A parse / lowering error. Always returned, never panicked.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CovError {
    /// The underlying S-expression reader failed.
    #[error("sexp parse error: {0}")]
    Sexp(String),
    /// A structural error in a directive or sublanguage form.
    #[error("cov syntax error: {0}")]
    Syntax(String),
    /// An unbound name (not a binder, prior def, or catalogue constant).
    #[error("unknown name: {0}")]
    Unknown(String),
    /// A type that did not pass the kernel's `type_of` check.
    #[error("type error: {0}")]
    Type(String),
}

type R<T> = Result<T, CovError>;

fn syn(msg: impl Into<String>) -> CovError {
    CovError::Syntax(msg.into())
}

// ============================================================================
// CoreEnv — the non-lazy core catalogue
// ============================================================================

/// A single parsed catalogue entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry {
    /// A term constant introduced by `(#def name term)`.
    Term(Term),
    /// A type introduced by `(#newtype …)` / `(#subtype …)` / `(#quot …)`.
    /// The full applied `Type` (a `TypeKind::Spec` leaf) plus the
    /// underlying [`TypeSpec`] handle (so callers can build `abs`/`rep`
    /// coercions and instantiate at other type args).
    Type(Type, TypeSpec),
}

/// The **core (non-lazy) catalogue** produced by parsing a `.cov` file.
///
/// Unlike `covalence-hol`'s async `LazyMap`, this is a plain insertion
/// over a `BTreeMap` — definitions are resolved eagerly, top-to-bottom,
/// each one able to reference everything defined before it. Exported so
/// `covalence-hol` can import it as the base catalogue.
#[derive(Debug, Clone, Default)]
pub struct CoreEnv {
    entries: BTreeMap<String, Entry>,
    order: Vec<String>,
}

impl CoreEnv {
    /// An empty environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up any entry by name.
    pub fn get(&self, name: &str) -> Option<&Entry> {
        self.entries.get(name)
    }

    /// Look up a term constant by name.
    pub fn term(&self, name: &str) -> Option<&Term> {
        match self.entries.get(name) {
            Some(Entry::Term(t)) => Some(t),
            _ => None,
        }
    }

    /// Look up a defined type (the applied `Type`) by name.
    pub fn ty(&self, name: &str) -> Option<&Type> {
        match self.entries.get(name) {
            Some(Entry::Type(t, _)) => Some(t),
            _ => None,
        }
    }

    /// Look up a defined type's underlying [`TypeSpec`] handle by name.
    pub fn type_spec(&self, name: &str) -> Option<&TypeSpec> {
        match self.entries.get(name) {
            Some(Entry::Type(_, s)) => Some(s),
            _ => None,
        }
    }

    /// Names in file-definition order.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.order.iter().map(String::as_str)
    }

    /// Number of entries.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// Whether the env is empty.
    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    fn insert(&mut self, name: String, entry: Entry) -> R<()> {
        if self.entries.contains_key(&name) {
            return Err(syn(format!("duplicate definition: {name}")));
        }
        self.order.push(name.clone());
        self.entries.insert(name, entry);
        Ok(())
    }
}

// ============================================================================
// Top-level entry points
// ============================================================================

/// The embedded core catalogue source (`defs/core.cov`).
pub const CORE_COV: &str = include_str!("core.cov");

/// The process-shared **core catalogue** [`CoreEnv`], built by parsing the
/// embedded [`CORE_COV`] source once. Each entry's kernel objects are
/// the same `Arc`-shared accessors as the hand-written `defs::*` (the
/// catalogue resolver returns the cached accessors), so this `CoreEnv` is a
/// data-driven *view* of the migrated catalogue, exported for
/// `covalence-hol` to consume as its base catalogue.
///
/// Panics only if the embedded `core.cov` fails to parse, which is a
/// build-time invariant exercised by the test suite.
pub fn core_env() -> &'static CoreEnv {
    use std::sync::LazyLock;
    static CORE: LazyLock<CoreEnv> =
        LazyLock::new(|| parse_core(CORE_COV).expect("embedded core.cov must parse"));
    &CORE
}

/// Parse a whole `.cov` source string into an [`CoreEnv`].
pub fn parse_core(src: &str) -> R<CoreEnv> {
    let forms = covalence_sexp::parse(src).map_err(|e| CovError::Sexp(e.to_string()))?;
    let mut env = CoreEnv::new();
    for form in &forms {
        directive(form, &mut env)?;
    }
    Ok(env)
}

/// Parse a single bare term from a string, in the context of `env`
/// (used heavily by tests). No binders are in scope.
pub fn term_str(env: &CoreEnv, src: &str) -> R<Term> {
    let forms = covalence_sexp::parse(src).map_err(|e| CovError::Sexp(e.to_string()))?;
    let [form] = &forms[..] else {
        return Err(syn("term_str: expected exactly one s-expression"));
    };
    let mut scope = Scope::new();
    term(form, &mut scope, env)
}

/// Parse a single bare type from a string, in the context of `env`.
pub fn type_str(env: &CoreEnv, src: &str) -> R<Type> {
    let forms = covalence_sexp::parse(src).map_err(|e| CovError::Sexp(e.to_string()))?;
    let [form] = &forms[..] else {
        return Err(syn("type_str: expected exactly one s-expression"));
    };
    parse_type(form, env)
}

// ============================================================================
// Directives
// ============================================================================

fn directive(form: &SExpr, env: &mut CoreEnv) -> R<()> {
    let ch = list(form, "directive")?;
    let head = head_sym(ch)?;
    match head {
        "#def" => {
            arity(ch, 3, "#def")?;
            let name = sym(&ch[1], "#def name")?.to_string();
            let mut scope = Scope::new();
            let t = term(&ch[2], &mut scope, env)?;
            // Type-check the body so a malformed def is rejected here,
            // not deep downstream.
            t.type_of()
                .map_err(|e| CovError::Type(format!("#def {name}: {e:?}")))?;
            env.insert(name, Entry::Term(t))
        }
        "#newtype" => {
            arity(ch, 3, "#newtype")?;
            let name = sym(&ch[1], "#newtype name")?.to_string();
            let base = parse_type(&ch[2], env)?;
            let fresh = match canonical_by_label(&name) {
                Some(sym) => TypeSpec::newtype(sym, base),
                None => TypeSpec::newtype(smol_str::SmolStr::from(&name), base),
            };
            insert_type(env, name, fresh)
        }
        "#subtype" => {
            arity(ch, 4, "#subtype")?;
            let name = sym(&ch[1], "#subtype name")?.to_string();
            let carrier = parse_type(&ch[2], env)?;
            let mut scope = Scope::new();
            let pred = term(&ch[3], &mut scope, env)?;
            let fresh = match canonical_by_label(&name) {
                Some(sym) => TypeSpec::subtype(sym, carrier, pred),
                None => TypeSpec::subtype(smol_str::SmolStr::from(&name), carrier, pred),
            };
            insert_type(env, name, fresh)
        }
        "#quot" => {
            arity(ch, 4, "#quot")?;
            let name = sym(&ch[1], "#quot name")?.to_string();
            let base = parse_type(&ch[2], env)?;
            let mut scope = Scope::new();
            let rel = term(&ch[3], &mut scope, env)?;
            let fresh = match canonical_by_label(&name) {
                Some(sym) => TypeSpec::quot(sym, base, rel),
                None => TypeSpec::quot(smol_str::SmolStr::from(&name), base, rel),
            };
            insert_type(env, name, fresh)
        }
        other => Err(syn(format!("unknown directive: {other}"))),
    }
}

/// Insert a parsed type definition. When `name` is an already-cached
/// kernel-catalogue type, we **reuse the cached spec** (so the type is
/// `Arc`-identical to what the rest of the kernel and other `.cov`
/// definitions reference) — but only after checking that the freshly
/// parsed `carrier`/`predicate` are *structurally identical* (modulo
/// the spec symbol, whose equality is pointer-based) to the cached
/// definition. That check is what makes the `.cov` an audited
/// re-expression of the Rust rather than an unverified parallel one.
///
/// For a genuinely new type (no cached accessor) the fresh spec is
/// stored directly.
fn insert_type(env: &mut CoreEnv, name: String, fresh: TypeSpec) -> R<()> {
    let spec = match catalogue_type_spec(&name) {
        Some(cached) => {
            if fresh.ty() != cached.ty() || fresh.tm() != cached.tm() {
                return Err(CovError::Type(format!(
                    "type {name}: core.cov definition does not match the hand-written \
                     catalogue (carrier/predicate differ)"
                )));
            }
            cached
        }
        None => fresh,
    };
    let applied = apply_spec(&spec, &name)?;
    env.insert(name, Entry::Type(applied, spec))
}

/// Instantiate a freshly built `TypeSpec` at the type variables that
/// occur in its carrier (in alphabetical `free_tvars` order, matching
/// the kernel convention) so the stored `Type` is a `TypeKind::Spec`
/// leaf applied at `'a`, `'b`, … just like the hand-written accessors.
fn apply_spec(spec: &TypeSpec, name: &str) -> R<Type> {
    let carrier = spec
        .ty()
        .ok_or_else(|| syn(format!("type {name}: spec has no carrier")))?;
    let tvars = carrier.free_tvars();
    let args: Vec<Type> = tvars.iter().map(|v| Type::tfree(v.clone())).collect();
    Ok(Type::spec(spec.clone(), args))
}

// ============================================================================
// Scope — binder stack for de Bruijn closing
// ============================================================================

/// A stack of named, typed binders. The sublanguage closes each `#lam`
/// / `#sel` body by name into `Bound(0)` via [`crate::subst::close`];
/// the scope only needs to remember each binder's *type* so a `NAME`
/// reference can be elaborated to a `Free(name, ty)` leaf (which the
/// enclosing binder then closes).
struct Scope {
    stack: Vec<(String, Type)>,
}

impl Scope {
    fn new() -> Self {
        Scope { stack: Vec::new() }
    }

    fn lookup(&self, name: &str) -> Option<&Type> {
        self.stack
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t)
    }

    fn push(&mut self, name: String, ty: Type) {
        self.stack.push((name, ty));
    }

    fn pop(&mut self) {
        self.stack.pop();
    }
}

// ============================================================================
// Type sublanguage
// ============================================================================

/// Parse a type form:
/// `bool`, `nat`, `int`, `unit`, `bytes`, `'a` (type var), a defined
/// type name (resolved against `env`), `(#fn A B …)` / `(-> …)`
/// curried-right, `(#tycon NAME ty*)`, or a catalogue / defined
/// type constructor applied to args `(NAME ty*)`.
fn parse_type(s: &SExpr, env: &CoreEnv) -> R<Type> {
    match s {
        SExp::Atom(Atom::Symbol(name)) => parse_type_atom(name.as_str(), env),
        SExp::Atom(_) => Err(syn("type: unexpected string atom")),
        SExp::List(ch) => {
            let head = head_sym(ch)?;
            match head {
                "#fn" | "->" => {
                    if ch.len() < 3 {
                        return Err(syn("#fn: expected (#fn A B …)"));
                    }
                    let mut tys = ch[1..].iter().map(|c| parse_type(c, env)).collect::<R<Vec<_>>>()?;
                    let mut acc = tys.pop().unwrap();
                    while let Some(t) = tys.pop() {
                        acc = Type::fun(t, acc);
                    }
                    Ok(acc)
                }
                "#tfree" => {
                    arity(ch, 2, "#tfree")?;
                    Ok(Type::tfree(sym(&ch[1], "#tfree name")?))
                }
                "#tycon" => {
                    if ch.is_empty() {
                        return Err(syn("#tycon: expected (#tycon NAME ty*)"));
                    }
                    let name = sym(&ch[1], "#tycon name")?;
                    let args = ch[2..].iter().map(|c| parse_type(c, env)).collect::<R<Vec<_>>>()?;
                    Ok(Type::tycon(name, args))
                }
                // `(NAME ty*)` — a defined type or catalogue type
                // constructor applied to type arguments.
                _ => {
                    let args = ch[1..].iter().map(|c| parse_type(c, env)).collect::<R<Vec<_>>>()?;
                    apply_type_ctor(head, args, env)
                }
            }
        }
    }
}

fn parse_type_atom(name: &str, env: &CoreEnv) -> R<Type> {
    match name {
        "bool" => Ok(Type::bool()),
        "nat" => Ok(Type::nat()),
        "int" => Ok(Type::int()),
        "unit" => Ok(Type::unit()),
        "bytes" => Ok(Type::bytes()),
        _ if name.starts_with('\'') => Ok(Type::tfree(&name[1..])),
        // A locally-defined zero-ary type.
        _ => {
            if let Some(t) = env.ty(name) {
                return Ok(t.clone());
            }
            // A zero-ary catalogue type spec (e.g. a future `rat`).
            apply_type_ctor(name, vec![], env)
        }
    }
}

/// Build `Type::spec(SPEC, args)` for a defined or catalogue type
/// constructor `name` applied to `args`.
fn apply_type_ctor(name: &str, args: Vec<Type>, env: &CoreEnv) -> R<Type> {
    if let Some(spec) = env.type_spec(name) {
        return Ok(Type::spec(spec.clone(), args));
    }
    if let Some(spec) = catalogue_type_spec(name) {
        return Ok(Type::spec(spec, args));
    }
    Err(CovError::Unknown(format!("type constructor: {name}")))
}

// ============================================================================
// Term sublanguage
// ============================================================================

/// Parse a term form against the current binder `scope` and `env`.
fn term(s: &SExpr, scope: &mut Scope, env: &CoreEnv) -> R<Term> {
    match s {
        SExp::Atom(Atom::Symbol(name)) => term_atom(name.as_str(), scope, env),
        SExp::Atom(Atom::Str { format, bytes }) => {
            // A blob literal written as a bare `b"…"` string atom.
            if format.is_empty() || format.as_str() == "b" {
                Ok(Term::blob(bytes.clone()))
            } else {
                Err(syn(format!("term: unsupported string format {format:?}")))
            }
        }
        SExp::List(ch) => {
            if ch.is_empty() {
                return Err(syn("term: empty list"));
            }
            match head_sym(ch).ok() {
                Some("#lam") => parse_lam(ch, scope, env),
                Some("#eq") => {
                    arity(ch, 3, "#eq")?;
                    let lhs = term(&ch[1], scope, env)?;
                    let rhs = term(&ch[2], scope, env)?;
                    hol_eq(lhs, rhs)
                }
                Some("#sel") => parse_sel(ch, scope, env),
                Some("#abs") => parse_coercion(ch, scope, env, true),
                Some("#rep") => parse_coercion(ch, scope, env, false),
                Some("#at") => parse_type_app(ch, env),
                Some("#blob") => {
                    arity(ch, 2, "#blob")?;
                    let (_fmt, bytes) = ch[1]
                        .as_str()
                        .ok_or_else(|| syn("#blob: expected a string literal"))?;
                    Ok(Term::blob(bytes.to_vec()))
                }
                // Otherwise it's curried application `(f x y …)`.
                _ => {
                    let mut it = ch.iter();
                    let mut acc = term(it.next().unwrap(), scope, env)?;
                    for arg in it {
                        let a = term(arg, scope, env)?;
                        acc = Term::app(acc, a);
                    }
                    Ok(acc)
                }
            }
        }
    }
}

fn term_atom(name: &str, scope: &mut Scope, env: &CoreEnv) -> R<Term> {
    // (0) bool literals.
    match name {
        "T" => return Ok(Term::bool_lit(true)),
        "F" => return Ok(Term::bool_lit(false)),
        _ => {}
    }
    // (1) numeric literal — bare `nat` literal (the sublanguage's
    // default numeral). Negative numerals are `int`.
    if let Some(t) = numeral(name) {
        return Ok(t);
    }
    // (2) a binder in scope.
    if let Some(ty) = scope.lookup(name) {
        return Ok(Term::free(name, ty.clone()));
    }
    // (3) a kernel catalogue constant, monomorphic (0 type args).
    //
    // Catalogue resolution comes *before* the `CoreEnv` lookup so that a
    // reference to a constant (e.g. `bool.and` inside `bool.imp`'s body)
    // resolves to the cached `Term::term_spec(and_spec, [])` *leaf* — the
    // same object the hand-written `hol::hol_and` uses — and *not* to the
    // unfolded lambda body the `#def` stored under that name. This is
    // what keeps the dependent definitions byte-identical to the Rust.
    if let Some(t) = catalogue_term(name, &[]) {
        return Ok(t);
    }
    // (4) a prior `#def` term constant that is *not* a kernel catalogue
    // name (user-introduced definitions in a non-core `.cov`).
    if let Some(t) = env.term(name) {
        return Ok(t.clone());
    }
    Err(CovError::Unknown(name.to_string()))
}

/// `(#lam (x A) body)` — type-ascribed lambda. (`(#lam x body)` with a
/// bare binder is **not** accepted: there is no inference, so the
/// binder type must be explicit.)
fn parse_lam(ch: &[SExpr], scope: &mut Scope, env: &CoreEnv) -> R<Term> {
    arity(ch, 3, "#lam")?;
    let (name, ty) = parse_binder(&ch[1], env)?;
    scope.push(name.clone(), ty.clone());
    let body = term(&ch[2], scope, env);
    scope.pop();
    let body = body?;
    Ok(Term::abs(ty, close(&body, &name)))
}

/// `(#sel (x A) pred)` — Hilbert choice `ε(λx:A. pred)`.
fn parse_sel(ch: &[SExpr], scope: &mut Scope, env: &CoreEnv) -> R<Term> {
    arity(ch, 3, "#sel")?;
    let (name, ty) = parse_binder(&ch[1], env)?;
    scope.push(name.clone(), ty.clone());
    let pred = term(&ch[2], scope, env);
    scope.pop();
    let pred = pred?;
    let lam = Term::abs(ty.clone(), close(&pred, &name));
    Ok(Term::app(Term::select_op(ty), lam))
}

/// `(#abs SPEC (ty*) [carrier])` / `(#rep SPEC (ty*) [carrier])` — the
/// TypeSpec carrier↔wrapper coercions. `SPEC` is a defined-or-catalogue
/// type name; `(ty*)` are its type arguments. With a third argument the
/// coercion is *applied* to it; without one it is the bare coercion
/// function.
fn parse_coercion(ch: &[SExpr], scope: &mut Scope, env: &CoreEnv, is_abs: bool) -> R<Term> {
    if ch.len() != 3 && ch.len() != 4 {
        return Err(syn("#abs/#rep: expected (#abs SPEC (ty*) [arg])"));
    }
    let spec_name = sym(&ch[1], "#abs/#rep spec name")?;
    let spec = resolve_type_spec(spec_name, env)?;
    let args = type_arg_list(&ch[2], env)?;
    let coercion = if is_abs {
        Term::spec_abs(spec, args)
    } else {
        Term::spec_rep(spec, args)
    };
    if ch.len() == 4 {
        let arg = term(&ch[3], scope, env)?;
        Ok(Term::app(coercion, arg))
    } else {
        Ok(coercion)
    }
}

/// `(#at NAME ty*)` — a polymorphic catalogue / defined term constant
/// applied to explicit type arguments.
fn parse_type_app(ch: &[SExpr], env: &CoreEnv) -> R<Term> {
    if ch.len() < 2 {
        return Err(syn("#at: expected (#at NAME ty*)"));
    }
    let name = sym(&ch[1], "#at name")?;
    let args = ch[2..].iter().map(|c| parse_type(c, env)).collect::<R<Vec<_>>>()?;
    // A prior `#def` constant cannot take type args (it is already a
    // closed term), so `#at` only resolves catalogue constants.
    catalogue_term(name, &args).ok_or_else(|| CovError::Unknown(format!("catalogue term: {name}")))
}

/// `(x A)` — a typed binder.
fn parse_binder(s: &SExpr, env: &CoreEnv) -> R<(String, Type)> {
    let ch = list(s, "binder")?;
    arity(ch, 2, "binder (x A)")?;
    let name = sym(&ch[0], "binder name")?.to_string();
    let ty = parse_type(&ch[1], env)?;
    Ok((name, ty))
}

/// `(ty*)` — a (possibly empty) list of type arguments.
fn type_arg_list(s: &SExpr, env: &CoreEnv) -> R<Vec<Type>> {
    let ch = list(s, "type-arg list")?;
    ch.iter().map(|c| parse_type(c, env)).collect()
}

fn resolve_type_spec(name: &str, env: &CoreEnv) -> R<TypeSpec> {
    if let Some(spec) = env.type_spec(name) {
        return Ok(spec.clone());
    }
    catalogue_type_spec(name).ok_or_else(|| CovError::Unknown(format!("type spec: {name}")))
}

/// HOL equality `lhs = rhs`, type taken from `lhs`. Returns a `Type`
/// error (not a panic) when `lhs` is not closed / well-typed.
fn hol_eq(lhs: Term, rhs: Term) -> R<Term> {
    let alpha = lhs
        .type_of()
        .map_err(|e| CovError::Type(format!("#eq lhs: {e:?}")))?;
    Ok(Term::app(Term::app(Term::eq_op(alpha), lhs), rhs))
}

// ============================================================================
// Numerals
// ============================================================================

/// A bare numeral: `nat` for non-negative, `int` for a leading `-`.
fn numeral(s: &str) -> Option<Term> {
    if let Some(rest) = s.strip_prefix('-') {
        let n: Int = rest.parse::<i128>().ok().map(Int::from)?;
        Some(Term::int_lit(-n))
    } else if s.chars().all(|c| c.is_ascii_digit()) && !s.is_empty() {
        let n: Nat = s.parse::<u128>().ok().map(Nat::from)?;
        Some(Term::nat_lit(n))
    } else {
        None
    }
}

// ============================================================================
// Small S-expression helpers
// ============================================================================

fn list<'a>(s: &'a SExpr, what: &str) -> R<&'a [SExpr]> {
    match s {
        SExp::List(ch) => Ok(ch),
        SExp::Atom(_) => Err(syn(format!("expected a list for {what}"))),
    }
}

fn head_sym(ch: &[SExpr]) -> R<&str> {
    ch.first()
        .and_then(|h| h.as_symbol())
        .ok_or_else(|| syn("list head is not a symbol"))
}

fn sym<'a>(s: &'a SExpr, what: &str) -> R<&'a str> {
    s.as_symbol()
        .ok_or_else(|| syn(format!("{what}: not a symbol")))
}

fn arity(ch: &[SExpr], n: usize, what: &str) -> R<()> {
    if ch.len() == n {
        Ok(())
    } else {
        Err(syn(format!(
            "{what}: expected {n} elements, got {}",
            ch.len()
        )))
    }
}

// ============================================================================
// Catalogue resolution
//
// These two tables are the *only* coupling to the hand-written
// catalogue. A `.cov` name resolves to the same `Arc`-shared accessor
// the Rust returns, so parsed and hand-written objects compare equal.
// They are intentionally exhaustive over the migrated symbols only;
// catalogue entries that have not (yet) been ported simply aren't here.
// ============================================================================

/// Resolve a label to its `Canonical` symbol (for directive heads).
fn canonical_by_label(name: &str) -> Option<Canonical> {
    // Only the symbols we migrate need to be here. Variants are spelled
    // fully-qualified so `Canonical::Some`/`Canonical::None` do not
    // shadow `Option`'s.
    Some(match name {
        "bool.and" => Canonical::And,
        "bool.or" => Canonical::Or,
        "bool.not" => Canonical::Not,
        "bool.imp" => Canonical::Imp,
        "bool.iff" => Canonical::Iff,
        "bool.forall" => Canonical::Forall,
        "bool.exists" => Canonical::Exists,
        "fail" => Canonical::Fail,
        "fun.id" => Canonical::Id,
        "fun.const" => Canonical::Const,
        "fun.compose" => Canonical::Compose,
        "fun.flip" => Canonical::Flip,
        "unit" => Canonical::Unit,
        "unit.nil" => Canonical::UnitNil,
        "coprod" => Canonical::Coprod,
        "prod" => Canonical::Prod,
        "option" => Canonical::Option,
        "result" => Canonical::Result,
        _ => return Option::None,
    })
}

/// Resolve a catalogue *type* constructor name to its cached
/// [`TypeSpec`] accessor.
fn catalogue_type_spec(name: &str) -> Option<TypeSpec> {
    use super::*;
    Some(match name {
        "unit" => unit_spec(),
        "coprod" => coprod_spec(),
        "prod" => prod_spec(),
        "option" => option_spec(),
        "result" => result_spec(),
        "rel" => rel_spec(),
        "set" => set_spec(),
        _ => return None,
    })
}

/// Resolve a catalogue *term* constant `name` at type arguments `args`
/// to its cached accessor. Returns `None` for unknown names or an
/// argument-count mismatch.
fn catalogue_term(name: &str, args: &[Type]) -> Option<Term> {
    use super::*;
    let a = |i: usize| args.get(i).cloned();
    Some(match (name, args.len()) {
        // ---- logic connectives (monomorphic) ----
        ("bool.and", 0) => and(),
        ("bool.or", 0) => or(),
        ("bool.not", 0) => not(),
        ("bool.imp", 0) => imp(),
        ("bool.iff", 0) => iff(),
        // ---- quantifiers (one type arg) ----
        ("bool.forall", 1) => forall(a(0)?),
        ("bool.exists", 1) => exists(a(0)?),
        // ---- fail (one type arg) ----
        ("fail", 1) => fail(a(0)?),
        // ---- function combinators ----
        ("fun.id", 1) => id(a(0)?),
        ("fun.const", 2) => konst(a(0)?, a(1)?),
        ("fun.compose", 3) => compose(a(0)?, a(1)?, a(2)?),
        ("fun.flip", 3) => flip(a(0)?, a(1)?, a(2)?),
        // ---- unit ----
        ("unit.nil", 0) => unit_nil(),
        // ---- coproduct ----
        ("coprod.inl", 2) => inl(a(0)?, a(1)?),
        ("coprod.inr", 2) => inr(a(0)?, a(1)?),
        ("coprod.case", 3) => coprod_case(a(0)?, a(1)?, a(2)?),
        // ---- product ----
        ("prod.pair", 2) => pair(a(0)?, a(1)?),
        ("prod.fst", 2) => fst(a(0)?, a(1)?),
        ("prod.snd", 2) => snd(a(0)?, a(1)?),
        // ---- option ----
        ("option.none", 1) => none(a(0)?),
        ("option.some", 1) => some(a(0)?),
        ("option.case", 2) => option_case(a(0)?, a(1)?),
        ("option.isSome", 1) => is_some(a(0)?),
        ("option.unwrap", 1) => unwrap(a(0)?),
        // ---- result ----
        ("result.ok", 2) => ok(a(0)?, a(1)?),
        ("result.err", 2) => err(a(0)?, a(1)?),
        _ => return None,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::defs;

    fn env() -> &'static CoreEnv {
        core_env()
    }

    /// The embedded `core.cov` parses without error and defines every
    /// migrated symbol.
    #[test]
    fn core_cov_parses() {
        let e = env();
        for name in [
            "bool.and", "bool.or", "bool.not", "bool.imp", "bool.iff", "bool.forall",
            "bool.exists", "fail", "fun.id", "fun.const", "fun.compose", "fun.flip", "unit",
            "unit.nil", "coprod", "coprod.inl", "coprod.inr", "coprod.case", "prod", "prod.pair",
            "prod.fst", "prod.snd", "option", "option.none", "option.some", "option.case",
            "option.isSome", "option.unwrap", "result", "result.ok", "result.err",
        ] {
            assert!(e.get(name).is_some(), "missing core.cov entry: {name}");
        }
    }

    /// Every `#def` body in `core.cov` is byte-identical (`==`) to the
    /// hand-written `defs::*` accessor. Because `==` on the spec leaves
    /// they reference is pointer-based (symbol identity), this only
    /// passes if the parsed term reuses the very same cached catalogue
    /// objects — proving the migration is faithful, not just shaped the
    /// same.
    #[test]
    fn migrated_terms_are_byte_identical() {
        let e = env();

        // Each `#def` body stored in the `CoreEnv` is byte-identical (`==`)
        // to the `tm` (defining body) that the hand-written `*_spec()`
        // accessor records. Since `==` bottoms out in pointer identity on
        // the catalogue spec leaves these bodies reference, this only
        // holds because the parser resolves catalogue references to the
        // very same cached `defs::*` accessors.
        let pairs: &[(&str, Term)] = &[
            ("bool.and", defs::and_spec().tm().unwrap().clone()),
            ("bool.or", defs::or_spec().tm().unwrap().clone()),
            ("bool.not", defs::not_spec().tm().unwrap().clone()),
            ("bool.imp", defs::imp_spec().tm().unwrap().clone()),
            ("bool.iff", defs::iff_spec().tm().unwrap().clone()),
            ("bool.forall", defs::forall_spec().tm().unwrap().clone()),
            ("bool.exists", defs::exists_spec().tm().unwrap().clone()),
            ("fail", defs::fail_spec().tm().unwrap().clone()),
            ("fun.id", defs::id_spec().tm().unwrap().clone()),
            ("fun.const", defs::konst_spec().tm().unwrap().clone()),
            ("fun.compose", defs::compose_spec().tm().unwrap().clone()),
            ("fun.flip", defs::flip_spec().tm().unwrap().clone()),
            ("unit.nil", defs::unit_nil_spec().tm().unwrap().clone()),
            ("coprod.inl", defs::inl_spec().tm().unwrap().clone()),
            ("coprod.inr", defs::inr_spec().tm().unwrap().clone()),
            ("coprod.case", defs::coprod_case_spec().tm().unwrap().clone()),
            ("prod.pair", defs::pair_spec().tm().unwrap().clone()),
            ("prod.fst", defs::fst_spec().tm().unwrap().clone()),
            ("prod.snd", defs::snd_spec().tm().unwrap().clone()),
            ("option.none", defs::none_spec().tm().unwrap().clone()),
            ("option.some", defs::some_spec().tm().unwrap().clone()),
            ("option.case", defs::option_case_spec().tm().unwrap().clone()),
            ("option.isSome", defs::is_some_spec().tm().unwrap().clone()),
            ("option.unwrap", defs::unwrap_spec().tm().unwrap().clone()),
            ("result.ok", defs::ok_spec().tm().unwrap().clone()),
            ("result.err", defs::err_spec().tm().unwrap().clone()),
        ];
        for (name, expected_body) in pairs {
            assert_eq!(
                e.term(name).unwrap(),
                expected_body,
                "byte-identity mismatch for {name}"
            );
        }
    }

    /// The migrated *types* (newtype/subtype) are byte-identical to the
    /// hand-written `defs::*_spec()` accessors.
    #[test]
    fn migrated_types_are_byte_identical() {
        let e = env();
        assert_eq!(e.type_spec("unit").unwrap(), &defs::unit_spec());
        assert_eq!(e.type_spec("coprod").unwrap(), &defs::coprod_spec());
        assert_eq!(e.type_spec("prod").unwrap(), &defs::prod_spec());
        assert_eq!(e.type_spec("option").unwrap(), &defs::option_spec());
        assert_eq!(e.type_spec("result").unwrap(), &defs::result_spec());

        // …and the applied `Type` leaves match the hand-written builders.
        assert_eq!(e.ty("unit").unwrap(), &Type::unit());
        assert_eq!(
            e.ty("option").unwrap(),
            &defs::option(Type::tfree("a")),
        );
        assert_eq!(
            e.ty("result").unwrap(),
            &defs::result(Type::tfree("a"), Type::tfree("b")),
        );
        assert_eq!(
            e.ty("coprod").unwrap(),
            &defs::coprod(Type::tfree("a"), Type::tfree("b")),
        );
        assert_eq!(
            e.ty("prod").unwrap(),
            &defs::prod(Type::tfree("a"), Type::tfree("b")),
        );
    }

    /// `term_str` / `type_str` give clean test-side construction from
    /// `.cov` snippets — exercising the reuse the task asks for.
    #[test]
    fn term_str_helpers_build_kernel_objects() {
        let e = env();
        // A bare connective reference resolves to the cached accessor.
        assert_eq!(term_str(e, "bool.and").unwrap(), defs::and());
        // A small lambda is byte-identical to the hand-built term.
        let parsed = term_str(e, "(#lam (x bool) x)").unwrap();
        let hand = Term::abs(Type::bool(), Term::bound(0));
        assert_eq!(parsed, hand);
        // Type snippets.
        assert_eq!(type_str(e, "(#fn nat bool)").unwrap(), Type::fun(Type::nat(), Type::bool()));
        assert_eq!(type_str(e, "(option nat)").unwrap(), defs::option(Type::nat()));
    }

    /// Numerals: bare → nat, leading `-` → int.
    #[test]
    fn numerals() {
        let e = env();
        assert_eq!(term_str(e, "0").unwrap(), Term::nat_lit(0u32));
        assert_eq!(term_str(e, "42").unwrap(), Term::nat_lit(42u32));
        assert_eq!(term_str(e, "-7").unwrap(), Term::int_lit(-7));
    }

    /// Malformed input is a typed error, never a panic.
    #[test]
    fn errors_are_total() {
        let e = env();
        assert!(matches!(term_str(e, "nope_unknown"), Err(CovError::Unknown(_))));
        assert!(matches!(term_str(e, "(#lam x x)"), Err(CovError::Syntax(_))));
        assert!(matches!(parse_core("(#bogus x)"), Err(CovError::Syntax(_))));
        assert!(matches!(parse_core("(#def x"), Err(CovError::Sexp(_))));
    }

    /// `#quot` directive works end-to-end (even though `core.cov` does
    /// not yet use it): a quotient of `nat` by `=` builds a type-spec.
    #[test]
    fn quot_directive() {
        // A user-named quotient of `nat` by `=` (an opaque SmolStr
        // symbol, not a `Canonical`): the directive builds a Spec
        // end-to-end. Exercises `#quot` even though `core.cov` does not
        // yet use it.
        let src = "(#quot natEq nat (#lam (x nat) (#lam (y nat) (#eq x y))))";
        let env = parse_core(src).unwrap();
        let spec = env.type_spec("natEq").expect("quot built");
        assert_eq!(spec.symbol().label(), "natEq");
        // Carrier is the powerset `nat → bool` (quotients live in the
        // powerset; see TypeSpec::quot).
        assert_eq!(spec.ty().unwrap(), &Type::fun(Type::nat(), Type::bool()));
    }

    /// A user `#newtype` / `#def` over non-catalogue names works (the
    /// general, not-just-core path), using opaque `SmolStr` symbols.
    #[test]
    fn user_newtype_and_def() {
        let src = "\
            (#newtype mypair (prod nat nat))\n\
            (#def myfst (#lam (p (mypair)) p))";
        let env = parse_core(src).unwrap();
        assert!(env.type_spec("mypair").is_some());
        assert_eq!(env.type_spec("mypair").unwrap().symbol().label(), "mypair");
        assert!(env.term("myfst").is_some());
    }
}

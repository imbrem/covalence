//! The **typed HOL backend** (`hol-typed` feature) — lowers *type-annotated*
//! dialect definitions and expressions into genuine, **well-typed** HOL
//! [`Term`](covalence_hol_api::Term)s, built **exclusively through the
//! `covalence-hol-api` traits** ([`Hol`] + [`Nat`]).
//!
//! # Why this is the "swap the TCB = swap the trait impl" story
//!
//! This lowering names **no** backend type except through the trait bound
//! `H: Hol + Nat`. It never mentions `covalence_core::TermKind`, never a
//! concrete `Term` constructor — every type, term, and (later) theorem is built
//! by calling a trait method (`H.tvar`, `H.fun_ty`, `H.var`, `H.lam`, `H.app`,
//! `H.eq`, `H.forall`, `Nat::lit`, …). The *only* place the concrete kernel is
//! named is where a caller picks an `H` (e.g. [`covalence_hol_api::NativeHol`]).
//! So when the trusted core changes, only the trait **impl** changes — the
//! dialect, this lowering, and any dialect source written against it are
//! untouched.
//!
//! # Why it consumes the AST, not the SExpr IR
//!
//! The untyped `SExpr` interchange IR ([`crate::sexpr`]) deliberately **drops
//! type annotations** (an untyped Lisp value). A *typed* realization needs the
//! written types, which live on the AST ([`Expr::Lam`]'s optional [`Ty`],
//! [`Decl::sig`]). There is **no inference** here (a deliberate scope choice):
//! this backend threads the *written* types through a small typing environment
//! and fails loudly on anything it cannot type. It is therefore an AST-driven
//! peer of the [`Realize`](crate::realize) seam rather than a `Realize` impl.
//!
//! # What it covers
//!
//! - **Types** ([`resolve_ty`]): type variables → [`Hol::tvar`]; the base types
//!   `nat` → [`Nat::nat_ty`] and `bool` → [`Hol::bool_ty`]; function types
//!   `a -> b` → [`Hol::fun_ty`]. Other constructors (`option a`, `list a`, …)
//!   need a per-theory trait (an `Option` / `List` surface) and are reported as
//!   unsupported — see the crate `SKELETONS.md`.
//! - **Expressions** ([`lower_expr`]): variables (typed from the environment),
//!   annotated lambdas, application, the operators `==` (→ [`Hol::eq`]) and `+`
//!   `*` (→ [`Nat::add`] / [`Nat::mul`]), and natural-number literals
//!   (→ [`Nat::lit`]). Unannotated free variables must be in scope; everything
//!   else (`if`, `let`, lists, tuples, unit, string literals, unannotated
//!   lambda binders) is reported as unsupported in the typed setting.
//!
//! The flagship consumer is the abstract **monad** module lowered in
//! `tests/typed_monad.rs`: `ret`/`bind` as typed free variables over a carrier
//! type variable, `map` defined from them, and the `map f (ret a) = ret (f a)`
//! law *stated* as a real HOL proposition — all through the traits.

use std::collections::{BTreeSet, HashMap, HashSet};

use covalence_hol_api::{Hol, Nat};

use crate::ast::{Decl, Expr, Lit, Ty};

/// An error from the typed backend.
#[derive(Clone, Debug)]
pub enum TypedError {
    /// A free variable used without a type — not bound by a lambda annotation,
    /// a signature-typed parameter, or the ambient environment.
    UnboundVar(String),
    /// A lambda binder with no type annotation (this backend does no
    /// inference, so every binder must be annotated or signature-typed).
    UnannotatedBinder(String),
    /// A type the backend cannot resolve through the trait surface (e.g. an
    /// applied constructor like `option a` with no theory trait yet).
    UnsupportedType(Ty),
    /// An expression construct the typed backend does not lower.
    Unsupported(&'static str),
    /// A signature with fewer arrows than the definition has parameters.
    TooManyParams { name: String, params: usize },
    /// An error surfaced by a `Hol` / `Nat` trait method (ill-typed
    /// application, etc.).
    Hol(covalence_hol_api::Error),
}

impl From<covalence_hol_api::Error> for TypedError {
    fn from(e: covalence_hol_api::Error) -> Self {
        TypedError::Hol(e)
    }
}

impl core::fmt::Display for TypedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TypedError::UnboundVar(n) => write!(f, "unbound variable `{n}` (needs a type)"),
            TypedError::UnannotatedBinder(n) => {
                write!(f, "lambda binder `{n}` needs a type annotation")
            }
            TypedError::UnsupportedType(t) => write!(f, "cannot resolve type: {t:?}"),
            TypedError::Unsupported(c) => write!(f, "typed backend does not lower: {c}"),
            TypedError::TooManyParams { name, params } => write!(
                f,
                "definition `{name}` has {params} parameter(s) but its signature has fewer arrows"
            ),
            TypedError::Hol(e) => write!(f, "HOL error: {e}"),
        }
    }
}

impl std::error::Error for TypedError {}

/// The result type of a typed lowering.
pub type Result<T> = std::result::Result<T, TypedError>;

/// A typing environment: variable name → its (backend) type. Threaded down the
/// expression tree; a lambda binder extends it, an application does not.
pub struct Env<H: Hol> {
    vars: HashMap<String, H::Type>,
}

impl<H: Hol> Default for Env<H> {
    fn default() -> Self {
        Env {
            vars: HashMap::new(),
        }
    }
}

impl<H: Hol> Env<H> {
    /// An empty environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind `name : ty`, returning the previous binding (for shadowing).
    pub fn bind(&mut self, name: &str, ty: H::Type) -> Option<H::Type> {
        self.vars.insert(name.to_string(), ty)
    }

    /// Look up a variable's type.
    pub fn get(&self, name: &str) -> Option<&H::Type> {
        self.vars.get(name)
    }
}

/// Resolve a dialect [`Ty`] into a backend type, through the traits only.
///
/// - [`Ty::Var`] → [`Hol::tvar`];
/// - [`Ty::Con`] `nat` → [`Nat::nat_ty`], `bool` → [`Hol::bool_ty`] (nullary);
/// - [`Ty::Fun`] → [`Hol::fun_ty`].
///
/// Any other constructor (including applied `option a` / `list a`) is
/// [`TypedError::UnsupportedType`] until a per-theory trait supplies it.
pub fn resolve_ty<H: Hol + Nat>(hol: &H, ty: &Ty) -> Result<H::Type> {
    match ty {
        Ty::Var(name) => Ok(hol.tvar(name)),
        Ty::Con(name, args) if args.is_empty() => match name.as_str() {
            "nat" => Ok(Nat::nat_ty(hol)),
            "bool" => Ok(hol.bool_ty()),
            _ => Err(TypedError::UnsupportedType(ty.clone())),
        },
        Ty::Con(..) => Err(TypedError::UnsupportedType(ty.clone())),
        Ty::Fun(a, b) => {
            let a = resolve_ty(hol, a)?;
            let b = resolve_ty(hol, b)?;
            Ok(hol.fun_ty(a, b))
        }
    }
}

/// Lower a dialect expression to a well-typed HOL term under `env`, through the
/// traits only. See the module docs for the covered constructs.
pub fn lower_expr<H: Hol + Nat>(hol: &H, env: &Env<H>, e: &Expr) -> Result<H::Term> {
    match e {
        Expr::Lit(Lit::Nat(n)) => {
            // A nat literal via the `Nat` trait. `Nat::lit` takes a u64; the
            // dialect carries arbitrary precision, so a value beyond u64 is an
            // (honest) limitation of the current `Nat` trait surface.
            let small: u64 = u64::try_from(n)
                .map_err(|_| TypedError::Unsupported("nat literal exceeding u64 (Nat::lit)"))?;
            Ok(Nat::lit(hol, small))
        }
        Expr::Lit(Lit::Str(_)) => Err(TypedError::Unsupported("string literal")),
        Expr::Var(name) => {
            let ty = env
                .get(name)
                .ok_or_else(|| TypedError::UnboundVar(name.clone()))?;
            Ok(hol.var(name, ty.clone()))
        }
        Expr::App(f, x) => {
            let f = lower_expr(hol, env, f)?;
            let x = lower_expr(hol, env, x)?;
            Ok(hol.app(f, x)?)
        }
        Expr::Lam(param, Some(ty), body) => {
            let pty = resolve_ty(hol, ty)?;
            let mut inner = Env::new();
            // Clone the ambient bindings, then shadow with the binder.
            for (k, v) in env.vars.iter() {
                inner.vars.insert(k.clone(), v.clone());
            }
            inner.bind(param, pty.clone());
            let body = lower_expr(hol, &inner, body)?;
            Ok(hol.lam(param, pty, body))
        }
        Expr::Lam(param, None, _) => Err(TypedError::UnannotatedBinder(param.clone())),
        Expr::BinOp(op, l, r) => {
            let l = lower_expr(hol, env, l)?;
            let r = lower_expr(hol, env, r)?;
            match op.as_str() {
                "==" => Ok(hol.eq(l, r)?),
                "+" => Ok(Nat::add(hol, l, r)?),
                "*" => Ok(Nat::mul(hol, l, r)?),
                _ => Err(TypedError::Unsupported("operator (only == + *)")),
            }
        }
        Expr::If(..) => Err(TypedError::Unsupported("if/then/else")),
        Expr::Let(..) => Err(TypedError::Unsupported("let")),
        Expr::List(_) => Err(TypedError::Unsupported("list literal")),
        Expr::Tuple(_) => Err(TypedError::Unsupported("tuple literal")),
        Expr::Unit => Err(TypedError::Unsupported("unit")),
    }
}

/// Collect the free variables of a dialect expression (identifiers used but not
/// bound by an enclosing lambda or `let`), in a deterministic (sorted) order.
///
/// This is what a theorem statement's implicitly-∀-quantified variables are:
/// every free identifier that is *not* a theory operation supplied by the
/// ambient environment. Used by [`lower_statement`] to decide which binders to
/// universally close.
pub fn free_vars(e: &Expr) -> Vec<String> {
    let mut acc = BTreeSet::new();
    let mut bound = HashSet::new();
    collect_free(e, &mut bound, &mut acc);
    acc.into_iter().collect()
}

fn collect_free(e: &Expr, bound: &mut HashSet<String>, acc: &mut BTreeSet<String>) {
    match e {
        Expr::Var(n) => {
            if !bound.contains(n) {
                acc.insert(n.clone());
            }
        }
        Expr::Lit(_) | Expr::Unit => {}
        Expr::App(f, x) | Expr::BinOp(_, f, x) => {
            collect_free(f, bound, acc);
            collect_free(x, bound, acc);
        }
        Expr::Lam(p, _ty, body) => {
            let fresh = bound.insert(p.clone());
            collect_free(body, bound, acc);
            if fresh {
                bound.remove(p);
            }
        }
        Expr::Let(n, v, body) => {
            collect_free(v, bound, acc);
            let fresh = bound.insert(n.clone());
            collect_free(body, bound, acc);
            if fresh {
                bound.remove(n);
            }
        }
        Expr::If(c, t, f) => {
            collect_free(c, bound, acc);
            collect_free(t, bound, acc);
            collect_free(f, bound, acc);
        }
        Expr::List(xs) | Expr::Tuple(xs) => {
            for x in xs {
                collect_free(x, bound, acc);
            }
        }
    }
}

/// Lower a **theorem statement** — an equation *expression* — into a HOL
/// proposition (`Term : bool`) with its **implicitly-universal variables
/// ∀-closed**, through the traits only.
///
/// This is the load-bearing definition/theorem symmetry: the statement is
/// parsed with the very same expression grammar a definition's `lhs = rhs` uses
/// (so `0 + m == m` is an [`Expr::BinOp`] with `==`), lowered by [`lower_expr`]
/// to a `bool` term, then the implicitly-universally-quantified variables (here
/// `m`) are each wrapped in a `∀`.
///
/// # Which variables are quantified
///
/// A statement's free identifiers fall into two classes, both typed by `env`:
///
/// - **theory operations** — the ambient signature (`ret` / `bind` / `map` /
///   `add`, …) a theorem is stated *against*. These stay **free constants** in
///   the proposition (they are the fixed vocabulary the proof also cites).
/// - **statement variables** — the implicitly-∀ ones (`m`, `n`, `f`, `a`).
///   These are ∀-closed.
///
/// The two are distinguished by the caller-supplied `quantify` set: every free
/// variable **in** it is ∀-closed; every other free variable stays a constant.
/// A free variable not typed by `env` is [`TypedError::UnboundVar`]. Closure is
/// applied in the **sorted** order of `quantify` (innermost binder last) so the
/// proposition is deterministic and a proof's conclusion checks against it by
/// α-equality.
pub fn lower_statement<H: Hol + Nat>(
    hol: &H,
    env: &Env<H>,
    stmt: &Expr,
    quantify: &BTreeSet<String>,
) -> Result<H::Term> {
    // Lower the equation body first (this also type-checks it: e.g. `==` builds
    // an `eq`, so the whole thing is `bool`).
    let body = lower_expr(hol, env, stmt)?;

    // ∀-close exactly the requested variables, in sorted order, innermost last.
    let mut prop = body;
    for name in quantify.iter().rev() {
        let ty = env
            .get(name)
            .ok_or_else(|| TypedError::UnboundVar(name.clone()))?
            .clone();
        prop = hol.forall(name, ty, prop)?;
    }
    Ok(prop)
}

/// Lower a top-level declaration `f p1 p2 = body` (with a signature) to a HOL
/// term, typing each parameter by peeling arrows off the signature and
/// abstracting them left-to-right. Returns the defined name and the lowered
/// term `λp1. λp2. body`.
///
/// Requires [`Decl::sig`] to be present and to have at least as many arrows as
/// the declaration has parameters.
pub fn lower_decl<H: Hol + Nat>(hol: &H, d: &Decl) -> Result<(String, H::Term)> {
    lower_decl_in(hol, &Env::new(), d)
}

/// Like [`lower_decl`], but under a caller-supplied **ambient** environment.
///
/// The ambient bindings type free variables the definition uses but does not
/// itself bind — most importantly a theory's abstract operations (e.g. the
/// monad's `ret : α → m` and `bind : m → (α → m) → m`), which are free
/// variables in the body. The declaration's own parameters shadow the ambient
/// env.
pub fn lower_decl_in<H: Hol + Nat>(
    hol: &H,
    ambient: &Env<H>,
    d: &Decl,
) -> Result<(String, H::Term)> {
    let sig = d.sig.as_ref().ok_or(TypedError::Unsupported(
        "definition without a type signature",
    ))?;

    // Peel one arrow per parameter to get each binder's type and the residual
    // body type.
    let mut param_tys: Vec<Ty> = Vec::with_capacity(d.params.len());
    let mut rest = sig.clone();
    for _ in &d.params {
        match rest {
            Ty::Fun(a, b) => {
                param_tys.push(*a);
                rest = *b;
            }
            _ => {
                return Err(TypedError::TooManyParams {
                    name: d.name.clone(),
                    params: d.params.len(),
                });
            }
        }
    }

    // Build the body under the ambient env extended with every parameter.
    let mut env = Env::new();
    for (k, v) in ambient.vars.iter() {
        env.vars.insert(k.clone(), v.clone());
    }
    let mut resolved: Vec<H::Type> = Vec::with_capacity(param_tys.len());
    for (p, ty) in d.params.iter().zip(&param_tys) {
        let rty = resolve_ty(hol, ty)?;
        env.bind(p, rty.clone());
        resolved.push(rty);
    }
    let mut term = lower_expr(hol, &env, &d.body)?;

    // Abstract the parameters, innermost last.
    for (p, rty) in d.params.iter().zip(resolved).rev() {
        term = hol.lam(p, rty, term);
    }
    Ok((d.name.clone(), term))
}

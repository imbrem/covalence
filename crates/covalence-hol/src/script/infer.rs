//! A small **type-inference elaborator**: surface terms with omitted
//! types → metavariables → unification → fully-typed kernel `Term`s.
//!
//! The kernel is fully explicit (every `Free` carries a `Type`, every
//! binder its domain, `=`/`ε` their element type). This module lets the
//! *surface* leave those implicit and recovers them by Hindley–Milner-style
//! unification (no let-generalisation — within one term a variable has one
//! type; the only polymorphism is per-occurrence instantiation of the
//! catalogue constants, e.g. `=` at a fresh element metavariable).
//!
//! What is inferred:
//! - **free variables** with no `fix`/annotation — a bare symbol that is
//!   neither in scope, a numeral, nor a catalogue constant becomes an
//!   implicit free variable with a fresh type metavariable;
//! - **binder domains** — `(forall (x) …)` / `(lam (x) …)` / bare
//!   `(forall x …)` infer `x`'s type from its body;
//! - **`=` element types** — `(= a b)` unifies both sides at a fresh α.
//!
//! Metavariables still unconstrained after solving are **generalised** to
//! fresh type variables (`'a`, `'b`, …), so a genuinely polymorphic
//! statement like `∀x. x = x` elaborates without any annotation.

use std::collections::HashMap;

use covalence_core::defs::{self, TypeSpec};
use covalence_core::{Term, Type, TypeKind, subst};
use covalence_sexp::{SExp, SExpr};

use super::ScriptError;
use super::env::{ConstDef, Env};
use super::scope::Scope;
use super::syntax::{arity, head_sym, parse_type, sym};
use crate::HolLightCtx;

type R<T> = Result<T, ScriptError>;

/// An elaboration-time type: a kernel type shape plus metavariables.
#[derive(Clone)]
enum ETy {
    Meta(usize),
    Bool,
    Nat,
    TFree(String),
    Fun(Box<ETy>, Box<ETy>),
    Spec(TypeSpec, Vec<ETy>),
    Tycon(String, Vec<ETy>),
}

/// An elaboration-time term: kernel term shape carrying `ETy`s, zonked to
/// a `Term` once the metavariables are solved.
enum ETerm {
    Free(String, ETy),
    Bound(u32),
    /// An already-typed leaf (numeral, catalogue operator, `true`/`false`).
    Lit(Term),
    App(Box<ETerm>, Box<ETerm>),
    /// Low-level de-Bruijn abstraction `(abs TYPE BODY)`.
    AbsRaw(ETy, Box<ETerm>),
    /// Named binders (closed by name at zonk time).
    Lam(String, ETy, Box<ETerm>),
    Forall(String, ETy, Box<ETerm>),
    Exists(String, ETy, Box<ETerm>),
    Select(String, ETy, Box<ETerm>),
    Eq(Box<ETerm>, Box<ETerm>),
}

enum BinderKind {
    Lam,
    Forall,
    Exists,
    Select,
}

struct Elab<'e> {
    env: &'e Env,
    subst: Vec<Option<ETy>>,
    /// Free variables (fix-declared + implicitly discovered), in order.
    frees: Vec<(String, ETy)>,
    /// Lexically-scoped binder variables.
    bound: Vec<(String, ETy)>,
    /// Metavariable → generalised type-variable name, assigned at zonk.
    gen_names: HashMap<usize, String>,
    gen_counter: usize,
}

impl<'e> Elab<'e> {
    fn new(env: &'e Env) -> Self {
        Elab {
            env,
            subst: Vec::new(),
            frees: Vec::new(),
            bound: Vec::new(),
            gen_names: HashMap::new(),
            gen_counter: 0,
        }
    }

    fn fresh(&mut self) -> ETy {
        let id = self.subst.len();
        self.subst.push(None);
        ETy::Meta(id)
    }

    fn lookup(&self, name: &str) -> Option<ETy> {
        self.bound
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .or_else(|| self.frees.iter().find(|(n, _)| n == name))
            .map(|(_, t)| t.clone())
    }

    /// Follow the metavariable chain at the head (children left as-is).
    fn prune(&self, t: &ETy) -> ETy {
        match t {
            ETy::Meta(i) => match &self.subst[*i] {
                Some(u) => self.prune(u),
                None => ETy::Meta(*i),
            },
            other => other.clone(),
        }
    }

    fn occurs(&self, i: usize, t: &ETy) -> bool {
        match self.prune(t) {
            ETy::Meta(j) => i == j,
            ETy::Fun(a, b) => self.occurs(i, &a) || self.occurs(i, &b),
            ETy::Spec(_, args) | ETy::Tycon(_, args) => args.iter().any(|a| self.occurs(i, a)),
            _ => false,
        }
    }

    fn bind(&mut self, i: usize, t: ETy) -> R<()> {
        if self.occurs(i, &t) {
            return Err(ScriptError::Syntax("infer: infinite type".into()));
        }
        self.subst[i] = Some(t);
        Ok(())
    }

    fn unify(&mut self, a: &ETy, b: &ETy) -> R<()> {
        match (self.prune(a), self.prune(b)) {
            (ETy::Meta(i), ETy::Meta(j)) if i == j => Ok(()),
            (ETy::Meta(i), t) | (t, ETy::Meta(i)) => self.bind(i, t),
            (ETy::Bool, ETy::Bool) | (ETy::Nat, ETy::Nat) => Ok(()),
            (ETy::TFree(x), ETy::TFree(y)) if x == y => Ok(()),
            (ETy::Fun(a1, b1), ETy::Fun(a2, b2)) => {
                self.unify(&a1, &a2)?;
                self.unify(&b1, &b2)
            }
            (ETy::Spec(s1, a1), ETy::Spec(s2, a2)) if s1.ptr_eq(&s2) && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(&a2) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (ETy::Tycon(n1, a1), ETy::Tycon(n2, a2)) if n1 == n2 && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(&a2) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (x, y) => Err(ScriptError::Syntax(format!(
                "infer: type mismatch — {} vs {}",
                self.show(&x),
                self.show(&y)
            ))),
        }
    }

    fn from_type(&mut self, ty: &Type) -> R<ETy> {
        Ok(match ty.kind() {
            TypeKind::TFree(n) => ETy::TFree(n.to_string()),
            TypeKind::Bool => ETy::Bool,
            TypeKind::Nat => ETy::Nat,
            TypeKind::Fun(a, b) => {
                ETy::Fun(Box::new(self.from_type(a)?), Box::new(self.from_type(b)?))
            }
            TypeKind::Spec(s, args) => ETy::Spec(
                s.clone(),
                args.iter()
                    .map(|a| self.from_type(a))
                    .collect::<R<Vec<_>>>()?,
            ),
            TypeKind::Tycon(n, args) => ETy::Tycon(
                n.to_string(),
                args.iter()
                    .map(|a| self.from_type(a))
                    .collect::<R<Vec<_>>>()?,
            ),
            other => {
                return Err(ScriptError::Syntax(format!(
                    "infer: unsupported type for inference: {other:?}"
                )));
            }
        })
    }

    fn gen_name(&mut self, i: usize) -> String {
        if let Some(n) = self.gen_names.get(&i) {
            return n.clone();
        }
        let k = self.gen_counter;
        self.gen_counter += 1;
        let name = if k < 26 {
            ((b'a' + k as u8) as char).to_string()
        } else {
            format!("t{k}")
        };
        self.gen_names.insert(i, name.clone());
        name
    }

    fn to_type(&mut self, t: &ETy) -> R<Type> {
        Ok(match self.prune(t) {
            ETy::Meta(i) => Type::tfree(self.gen_name(i)),
            ETy::Bool => Type::bool(),
            ETy::Nat => Type::nat(),
            ETy::TFree(n) => Type::tfree(n),
            ETy::Fun(a, b) => Type::fun(self.to_type(&a)?, self.to_type(&b)?),
            ETy::Spec(s, args) => {
                let a = args
                    .iter()
                    .map(|x| self.to_type(x))
                    .collect::<R<Vec<_>>>()?;
                Type::spec(s, a)
            }
            ETy::Tycon(n, args) => {
                let a = args
                    .iter()
                    .map(|x| self.to_type(x))
                    .collect::<R<Vec<_>>>()?;
                Type::tycon(n, a)
            }
        })
    }

    fn show(&self, t: &ETy) -> String {
        match self.prune(t) {
            ETy::Meta(i) => format!("?{i}"),
            ETy::Bool => "bool".into(),
            ETy::Nat => "nat".into(),
            ETy::TFree(n) => format!("'{n}"),
            ETy::Fun(a, b) => format!("({} -> {})", self.show(&a), self.show(&b)),
            ETy::Spec(s, _) => s.symbol().label().to_string(),
            ETy::Tycon(n, _) => n,
        }
    }

    // -- inference ---------------------------------------------------------

    fn infer(&mut self, s: &SExpr) -> R<(ETerm, ETy)> {
        match s {
            SExp::Atom(_) => {
                let n = sym(s, "term")?;
                if let Some(ety) = self.lookup(n) {
                    return Ok((ETerm::Free(n.into(), ety.clone()), ety));
                }
                if let Ok(k) = n.parse::<u64>() {
                    return Ok((ETerm::Lit(Term::nat_lit(k)), ETy::Nat));
                }
                match self.env.lookup_const(n) {
                    Some(ConstDef::Op(t)) => {
                        let ety = self.from_type(&t.type_of()?)?;
                        Ok((ETerm::Lit(t.clone()), ety))
                    }
                    Some(ConstDef::Eq) => {
                        Err(ScriptError::Syntax("infer: `=` needs two arguments".into()))
                    }
                    None => {
                        // implicit free variable
                        let m = self.fresh();
                        self.frees.push((n.into(), m.clone()));
                        Ok((ETerm::Free(n.into(), m.clone()), m))
                    }
                }
            }
            SExp::List(ch) => self.infer_list(ch),
        }
    }

    fn infer_list(&mut self, ch: &[SExpr]) -> R<(ETerm, ETy)> {
        match head_sym(ch)? {
            "free" => {
                arity(ch, 3, "free")?;
                let ety = self.from_type(&parse_type(&ch[2])?)?;
                Ok((
                    ETerm::Free(sym(&ch[1], "free name")?.into(), ety.clone()),
                    ety,
                ))
            }
            "const" => {
                arity(ch, 3, "const")?;
                let ty = parse_type(&ch[2])?;
                let ety = self.from_type(&ty)?;
                Ok((
                    ETerm::Lit(Term::const_(sym(&ch[1], "const name")?, ty)),
                    ety,
                ))
            }
            "bound" => {
                arity(ch, 2, "bound")?;
                let i = sym(&ch[1], "bound index")?
                    .parse::<u32>()
                    .map_err(|e| ScriptError::Syntax(format!("bound: {e}")))?;
                Ok((ETerm::Bound(i), self.fresh()))
            }
            "abs" => {
                arity(ch, 3, "abs")?;
                let dom = self.from_type(&parse_type(&ch[1])?)?;
                let (body, bty) = self.infer(&ch[2])?;
                Ok((
                    ETerm::AbsRaw(dom.clone(), Box::new(body)),
                    ETy::Fun(Box::new(dom), Box::new(bty)),
                ))
            }
            "app" => {
                if ch.len() < 3 {
                    return Err(ScriptError::Syntax("app: expected (app f x …)".into()));
                }
                let (mut acc, mut acc_ty) = self.infer(&ch[1])?;
                for a in &ch[2..] {
                    let (ea, ta) = self.infer(a)?;
                    let r = self.fresh();
                    self.unify(&acc_ty, &ETy::Fun(Box::new(ta), Box::new(r.clone())))?;
                    acc = ETerm::App(Box::new(acc), Box::new(ea));
                    acc_ty = r;
                }
                Ok((acc, acc_ty))
            }
            "lam" | "λ" => self.infer_binder(ch, BinderKind::Lam),
            "forall" | "∀" => self.infer_binder(ch, BinderKind::Forall),
            "exists" | "∃" => self.infer_binder(ch, BinderKind::Exists),
            "select" | "ε" => self.infer_binder(ch, BinderKind::Select),
            // Explicitly-typed quantifier *operators* (the bare `∀`/`∃`/`ε`
            // applied to a predicate, rather than the binder sugar) — needed
            // to name and unfold the quantifier definitions in proofs.
            "forall-op" => {
                arity(ch, 2, "forall-op")?;
                let op = defs::forall(parse_type(&ch[1])?);
                let ety = self.from_type(&op.type_of()?)?;
                Ok((ETerm::Lit(op), ety))
            }
            "exists-op" => {
                arity(ch, 2, "exists-op")?;
                let op = defs::exists(parse_type(&ch[1])?);
                let ety = self.from_type(&op.type_of()?)?;
                Ok((ETerm::Lit(op), ety))
            }
            "select-op" => {
                arity(ch, 2, "select-op")?;
                let op = Term::select_op(parse_type(&ch[1])?);
                let ety = self.from_type(&op.type_of()?)?;
                Ok((ETerm::Lit(op), ety))
            }
            // `natRec` at a result type: `'a → (nat → 'a → 'a) → nat → 'a`.
            "natrec-op" => {
                arity(ch, 2, "natrec-op")?;
                let op = defs::nat_rec(parse_type(&ch[1])?);
                let ety = self.from_type(&op.type_of()?)?;
                Ok((ETerm::Lit(op), ety))
            }
            "=" | "eq" => {
                arity(ch, 3, "eq")?;
                let alpha = self.fresh();
                let (ea, ta) = self.infer(&ch[1])?;
                let (eb, tb) = self.infer(&ch[2])?;
                self.unify(&ta, &alpha)?;
                self.unify(&tb, &alpha)?;
                Ok((ETerm::Eq(Box::new(ea), Box::new(eb)), ETy::Bool))
            }
            other => match self.env.lookup_const(other).cloned() {
                Some(ConstDef::Op(t)) => {
                    let mut acc_ty = self.from_type(&t.type_of()?)?;
                    let mut acc = ETerm::Lit(t);
                    for a in &ch[1..] {
                        let (ea, ta) = self.infer(a)?;
                        let r = self.fresh();
                        self.unify(&acc_ty, &ETy::Fun(Box::new(ta), Box::new(r.clone())))?;
                        acc = ETerm::App(Box::new(acc), Box::new(ea));
                        acc_ty = r;
                    }
                    Ok((acc, acc_ty))
                }
                Some(ConstDef::Eq) => {
                    arity(ch, 3, other)?;
                    let alpha = self.fresh();
                    let (ea, ta) = self.infer(&ch[1])?;
                    let (eb, tb) = self.infer(&ch[2])?;
                    self.unify(&ta, &alpha)?;
                    self.unify(&tb, &alpha)?;
                    Ok((ETerm::Eq(Box::new(ea), Box::new(eb)), ETy::Bool))
                }
                None => Err(ScriptError::Unbound(other.into())),
            },
        }
    }

    fn infer_binder(&mut self, ch: &[SExpr], kind: BinderKind) -> R<(ETerm, ETy)> {
        arity(ch, 3, "binder")?;
        let (name, ann) = parse_binder_spec(&ch[1])?;
        let dom = match ann {
            Some(t) => self.from_type(&t)?,
            None => self.fresh(),
        };
        self.bound.push((name.clone(), dom.clone()));
        let body = self.infer(&ch[2]);
        self.bound.pop();
        let (ebody, bty) = body?;
        Ok(match kind {
            BinderKind::Lam => (
                ETerm::Lam(name, dom.clone(), Box::new(ebody)),
                ETy::Fun(Box::new(dom), Box::new(bty)),
            ),
            BinderKind::Forall => {
                self.unify(&bty, &ETy::Bool)?;
                (ETerm::Forall(name, dom, Box::new(ebody)), ETy::Bool)
            }
            BinderKind::Exists => {
                self.unify(&bty, &ETy::Bool)?;
                (ETerm::Exists(name, dom, Box::new(ebody)), ETy::Bool)
            }
            BinderKind::Select => {
                // ε x. P x : the binder domain (P must be bool-valued).
                self.unify(&bty, &ETy::Bool)?;
                (ETerm::Select(name, dom.clone(), Box::new(ebody)), dom)
            }
        })
    }

    // -- zonking -----------------------------------------------------------

    fn zonk(&mut self, e: &ETerm) -> R<Term> {
        Ok(match e {
            ETerm::Free(n, ety) => Term::free(n.as_str(), self.to_type(ety)?),
            ETerm::Bound(i) => Term::bound(*i),
            ETerm::Lit(t) => t.clone(),
            ETerm::App(f, x) => Term::app(self.zonk(f)?, self.zonk(x)?),
            ETerm::AbsRaw(d, b) => Term::abs(self.to_type(d)?, self.zonk(b)?),
            ETerm::Lam(n, d, b) => {
                let dt = self.to_type(d)?;
                let bt = self.zonk(b)?;
                Term::abs(dt, subst::close(&bt, n))
            }
            ETerm::Forall(n, d, b) => {
                let dt = self.to_type(d)?;
                let bt = self.zonk(b)?;
                HolLightCtx::new().mk_forall(n, dt, bt)
            }
            ETerm::Exists(n, d, b) => {
                let dt = self.to_type(d)?;
                let bt = self.zonk(b)?;
                HolLightCtx::new().mk_exists(n, dt, bt)
            }
            ETerm::Select(n, d, b) => {
                let dt = self.to_type(d)?;
                let bt = self.zonk(b)?;
                HolLightCtx::new().mk_select(n, dt, bt)
            }
            ETerm::Eq(x, y) => HolLightCtx::new().mk_eq(self.zonk(x)?, self.zonk(y)?)?,
        })
    }
}

/// Parse a binder/`fix` variable specification: `(name type)`,
/// `(name)`, or a bare `name` (type inferred).
pub fn parse_binder_spec(s: &SExpr) -> R<(String, Option<Type>)> {
    match s {
        SExp::Atom(_) => Ok((sym(s, "variable")?.to_string(), None)),
        SExp::List(ch) => match ch.len() {
            1 => Ok((sym(&ch[0], "variable")?.to_string(), None)),
            2 => Ok((
                sym(&ch[0], "variable")?.to_string(),
                Some(parse_type(&ch[1])?),
            )),
            _ => Err(ScriptError::Syntax(
                "variable: expected name, (name), or (name type)".into(),
            )),
        },
    }
}

/// Elaborate a single term against a fully-typed scope. Implicit free
/// variables and binder domains are inferred; leftover metavariables are
/// generalised to type variables.
pub fn elaborate_term(s: &SExpr, scope: &Scope, env: &Env) -> R<Term> {
    let mut e = Elab::new(env);
    for (n, t) in scope.iter() {
        let ety = e.from_type(t)?;
        e.frees.push((n.clone(), ety));
    }
    let (et, _) = e.infer(s)?;
    e.zonk(&et)
}

/// Elaborate a conclusion: like [`elaborate_term`] but the result is
/// constrained to `bool`, and the inferred types of every free variable
/// (the `fix`-declared ones plus any discovered implicitly) are returned
/// so the proof can be elaborated against the same typing.
pub fn elaborate_concl(
    s: &SExpr,
    fix: &[(String, Option<Type>)],
    env: &Env,
) -> R<(Term, Vec<(String, Type)>)> {
    let mut e = Elab::new(env);
    for (n, t) in fix {
        let ety = match t {
            Some(t) => e.from_type(t)?,
            None => e.fresh(),
        };
        e.frees.push((n.clone(), ety));
    }
    let (et, ty) = e.infer(s)?;
    e.unify(&ty, &ETy::Bool)?;
    let term = e.zonk(&et)?;
    // Collect the (now-solved) types of all free variables, in order.
    let frees = e.frees.clone();
    let vars = frees
        .iter()
        .map(|(n, ety)| Ok((n.clone(), e.to_type(ety)?)))
        .collect::<R<Vec<_>>>()?;
    Ok((term, vars))
}

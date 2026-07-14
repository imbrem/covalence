//! User function definitions as **kernel hypotheses** (`hol` feature).
//!
//! This is the sound approach to recursion in a total HOL: a
//! `(defun f (x y) body)` never mints an *axiom* `⊢ f x y = body`. Instead it
//! introduces the **assumption**
//!
//! ```text
//!     {f = λx y. body} ⊢ f = λx y. body
//! ```
//!
//! via the kernel [`Thm::assume`] rule (an assumption theorem is `{p} ⊢ p`).
//! Reducing a call `(f a b)` is then the certified step
//!
//! ```text
//!     {f = λx y. body} ⊢ (f a b) = body[a/x][b/y]
//! ```
//!
//! obtained by congruence against the assumed equation (rewrite `f` in head
//! position) followed by β. Composed via [`Thm::trans`] into the reduction
//! chain, the REPL returns `definitions ⊢ program = value` — the `defun`
//! equations ride along as **hypotheses**. This is sound even for
//! non-terminating / ill-founded recursion: a conditional sequent
//! `{defs} ⊢ Q` is fine even if `defs` is inconsistent — the kernel never
//! mints a hypothesis-free falsehood, and divergence is caught by the
//! fuel-bounded driver, not a hang.
//!
//! No new trusted kernel rules are introduced: `assume`, `inst`/congruence,
//! and `beta_conv` are all existing sound primitives.

use std::collections::BTreeMap;
use std::rc::Rc;

use covalence_core::subst;
use covalence_hol_eval::EvalThm as Thm;
use covalence_init::init::inductive::carved::carved;
use covalence_init::{Term, Type};

use crate::hol::HolError;

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

/// A single user function definition, entered as a kernel hypothesis.
#[derive(Clone)]
pub struct LispDef {
    /// The function name (`f`).
    pub name: String,
    /// The formal parameters, in order.
    pub params: Vec<String>,
    /// The free-variable head term `f : sexpr → … → sexpr`.
    pub head: Term,
    /// `λparams. body` — the assumed right-hand side.
    pub lambda: Term,
    /// `{f = λparams. body} ⊢ f = λparams. body` — the assumption theorem
    /// carried into every unfold of this function.
    pub assumption: Thm,
}

/// The `name → definition` dictionary threaded through a session. Cheap to
/// clone (an `Rc` over the map) so a fresh [`LispSemantics`](crate::semantics::LispSemantics)
/// can be rebuilt per cell.
#[derive(Clone, Default)]
pub struct Defs {
    map: Rc<BTreeMap<String, LispDef>>,
}

impl Defs {
    /// The empty dictionary.
    pub fn new() -> Self {
        Defs::default()
    }

    /// Look up a definition by name.
    pub fn get(&self, name: &str) -> Option<&LispDef> {
        self.map.get(name)
    }

    /// Is `name` a defined function?
    pub fn contains(&self, name: &str) -> bool {
        self.map.contains_key(name)
    }

    /// Number of definitions.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Is the dictionary empty?
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Return a new dictionary with `def` inserted (functional update — the
    /// old dictionary is untouched, so previously-built semantics keep their
    /// view). A redefinition replaces the prior entry.
    pub fn with(&self, def: LispDef) -> Self {
        let mut map = (*self.map).clone();
        map.insert(def.name.clone(), def);
        Defs { map: Rc::new(map) }
    }

    /// Iterate over the definitions (name → def).
    pub fn iter(&self) -> impl Iterator<Item = (&String, &LispDef)> {
        self.map.iter()
    }
}

/// Build a [`LispDef`] from a name, its parameter names, and its compiled
/// body term (a term over the free `sexpr` variables `params` plus the
/// recursive head `name`).
///
/// The lambda `λparams. body` is assembled by de-Bruijn-closing the body over
/// each parameter (innermost-last), and the assumption `{f=λ} ⊢ f = λ` is
/// minted with [`Thm::assume`].
pub fn build_def(name: &str, params: &[String], body: Term) -> Result<LispDef, HolError> {
    let cs = carved().map_err(theory_err)?;
    let ret = body.type_of().unwrap_or_else(|_| cs.tau.clone());
    build_def_with_ret(name, params, body, &ret)
}

/// [`build_def`] with the return type `ret` given explicitly — the head is
/// `sexpr → … → ret`. Used to pre-register a recursive function's head with a
/// chosen return type before its body is compiled.
pub fn build_def_with_ret(
    name: &str,
    params: &[String],
    body: Term,
    ret: &Type,
) -> Result<LispDef, HolError> {
    let cs = carved().map_err(theory_err)?;
    let tau = cs.tau.clone();
    // f : sexpr → … → ret  (one `sexpr` arrow per parameter).
    let head_ty = fn_ty(&tau, ret, params.len());
    let head = Term::free(name, head_ty.clone());

    // λparams. body — close over the last parameter first so the outermost
    // binder is the first parameter.
    let mut lambda = body;
    for p in params.iter().rev() {
        let closed = subst::close(&lambda, p);
        lambda = Term::abs(tau.clone(), closed);
    }

    // The assumed equation `f = λparams. body : bool` and its assumption
    // theorem `{f=λ} ⊢ f = λparams. body`.
    let eq = mk_eq_term(&head, &lambda, &head_ty);
    let assumption = Thm::assume(eq).map_err(kernel_err)?;

    Ok(LispDef {
        name: name.to_string(),
        params: params.to_vec(),
        head,
        lambda,
        assumption,
    })
}

/// `sexpr → … → ret` with `n` `sexpr` arrows (n = 0 ⇒ just `ret`).
fn fn_ty(tau: &Type, ret: &Type, n: usize) -> Type {
    let mut ty = ret.clone();
    for _ in 0..n {
        ty = Type::fun(tau.clone(), ty);
    }
    ty
}

/// Build the `bool`-typed equation term `a = b` (both of element type
/// `elem_ty`) — the HOL `=` primitive at `elem_ty` applied to `a` then `b`.
pub fn mk_eq_term(a: &Term, b: &Term, elem_ty: &Type) -> Term {
    Term::app(
        Term::app(Term::eq_op(elem_ty.clone()), a.clone()),
        b.clone(),
    )
}

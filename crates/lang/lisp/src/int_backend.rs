//! The **integer backend** for the Lisp reduction relation — a trait that
//! abstracts *how integers are represented as sexpr values* and *how an
//! integer operation's result is backed by a kernel theorem*.
//!
//! It is the seam behind the two dialects (`sector ⊑ sector+int`, see
//! [`crate::relation::Dialect`]): `sector` has no integer backend at all, so
//! `(+ 2 2)` is a stuck sexpr; `sector+int` installs a backend and adds the
//! integer [`Step`](crate::relation) clauses.
//!
//! ## Multiple representations, one trait
//!
//! - [`IntVariant`] — the honest signed-integer dialect. `(int n)` carries a
//!   kernel `int` literal for any `n : Int`; `-` may go negative.
//! - [`NatVariant`] — the natural-number dialect. It uses the *same* `int`
//!   literals and the *same* kernel computation, but **rejects negative
//!   results**: building a literal for `n < 0`, or evaluating a subtraction
//!   whose difference is negative, is an error. This is where the two dialects
//!   genuinely diverge in behaviour.
//! - [`IntSymbolPayloadVariant`] — exact integers in the left arm of an
//!   `int ⊕ bytes` atom payload. Unlike the auxiliary `(int n)` head, these
//!   values can be nested directly inside quoted inductive data.
//!
//! ## Soundness: results are PROVED, never asserted
//!
//! An [`IntBackend`] never *claims* an arithmetic fact. Representation and the
//! op-term / clause-target builders are untrusted term construction; the one
//! place a fact is produced — [`IntBackend::prove_reduce`] — returns **kernel
//! theorems** (`⊢ int.add a b = c`, `⊢ int.le a b = T`, `⊢ cond … = t`)
//! obtained from [`TermExt::reduce`] (the existing int-computation equation)
//! and the kernel `cond` clause laws. The relation driver rewrites the
//! *instantiated* `Step` clause with those equations — never fabricating a
//! result — so `⊢ Step (+ (int 2)(int 2)) (int 4)` is genuine.
//!
//! No new trusted kernel rules are introduced.

use covalence_hol_eval::EvalThm as Thm;
use covalence_init::init::ext::TermExt;
use covalence_init::{Term, Type};
use covalence_types::Int;

use crate::hol::HolError;

/// The binary/comparison integer operations the relation supports.
///
/// `Add`/`Sub`/`Mul` are `int → int → int` (the reduced form is an integer
/// literal `(int c)`); `Le`/`Eq` are comparisons whose reduced form is an
/// sexpr truthiness value (`t` / `nil`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntOp {
    /// `+` — addition.
    Add,
    /// `-` — subtraction (the `nat` variant errors on a negative difference).
    Sub,
    /// `*` — multiplication.
    Mul,
    /// `<=` — less-or-equal, reducing to the sexpr `t` / `nil`.
    Le,
    /// `=` — integer equality, reducing to the sexpr `t` / `nil`.
    Eq,
}

impl IntOp {
    /// The operator symbol as read/printed (`"+"`, `"-"`, `"*"`, `"<="`, `"="`).
    pub fn symbol(self) -> &'static str {
        match self {
            IntOp::Add => "+",
            IntOp::Sub => "-",
            IntOp::Mul => "*",
            IntOp::Le => "<=",
            IntOp::Eq => "=",
        }
    }

    /// `true` for the comparison ops (`<=`, `=`) — their reduced form is an
    /// sexpr truthiness value rather than an `(int …)`.
    pub fn is_cmp(self) -> bool {
        matches!(self, IntOp::Le | IntOp::Eq)
    }

    /// Every op, in a stable order (used to lay out the `Step` clauses).
    pub const ALL: [IntOp; 5] = [IntOp::Add, IntOp::Sub, IntOp::Mul, IntOp::Le, IntOp::Eq];

    /// Parse an operator symbol back to its op (`"+"` → `Add`, …). `None` for
    /// anything that is not one of the five integer operators.
    pub fn from_symbol(s: &str) -> Option<IntOp> {
        IntOp::ALL.into_iter().find(|op| op.symbol() == s)
    }
}

/// The reduced result of an integer operation: either an integer (for the
/// ring ops) or an sexpr truthiness bool (for the comparisons).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OpResult {
    /// An integer literal result (`Add`/`Sub`/`Mul`).
    Int(Int),
    /// A boolean result (`Le`/`Eq`) — mapped to the sexpr `t` / `nil` value.
    Bool(bool),
}

/// How integers are represented as sexpr values and how their operations are
/// backed by kernel theorems.
///
/// An implementation fixes: (1) the sexpr encoding of an integer literal
/// ([`lit`](Self::lit)), (2) the operator-application term builders
/// ([`op_term`](Self::op_term)), (3) the **generic** `Step`-clause target
/// ([`clause_target`](Self::clause_target)) built from the kernel int
/// function, and (4) the *proved* normalisation of a closed redex
/// ([`prove_reduce`](Self::prove_reduce)). The trait carries no soundness
/// obligation beyond honesty about `prove_reduce`'s theorems, which the driver
/// rechecks by the kernel.
pub trait IntBackend {
    /// Build the sexpr **value** term for the integer literal `n`.
    ///
    /// The [`NatVariant`] returns an error for `n < 0` (naturals only). The
    /// encoding is a distinguished sexpr head carrying the kernel `int`
    /// literal (see [`int_head`]).
    fn lit(&self, n: &Int) -> Result<Term, HolError>;

    /// Build the sexpr injection `(int e)` of an arbitrary `int`-typed kernel
    /// term `e` — used to state the `∀a b:int. …`-quantified `Step` clause
    /// (where `e` is the bound variable `a`/`b`, not a concrete literal). No
    /// negativity check (the clause is generic; the driver guards concrete
    /// instances via [`prove_reduce`](Self::prove_reduce)).
    fn lit_var(&self, e: &Term) -> Result<Term, HolError>;

    /// Recognise an `(int n)` value term, returning `n`. `None` for anything
    /// that is not this backend's integer encoding.
    fn as_lit(&self, t: &Term) -> Option<Int>;

    /// Build the operator application `(op a b)` as an sexpr term, where `a`,
    /// `b` are already sexpr terms. The head is a stable sexpr-valued free
    /// variable (`+`, `-`, `*`, `<=`, `=`) — see [`op_head`].
    fn op_term(&self, op: IntOp, a: Term, b: Term) -> Result<Term, HolError>;

    /// The stable operator head term for `op` (so the driver can match a
    /// redex `(op _ _)` in a candidate term).
    fn op_head(&self, op: IntOp) -> Term;

    /// The **generic clause target** `TARGET a b` for `op`, given the two
    /// (possibly-`∀`-bound) `int` terms `a_lit`, `b_lit`:
    ///
    /// - ring op: `(int (int.<op> a b))` — the sexpr injection of the kernel
    ///   arithmetic result;
    /// - comparison: `cond sexpr (int.<cmp> a b) t nil` — the kernel `cond`
    ///   selecting the sexpr `t` / `nil` per the boolean comparison.
    ///
    /// The `Step` clause is `∀a b. Step (op (int a)(int b)) (TARGET a b)`; on
    /// concrete literals the driver rewrites `TARGET a b` to the reduced value
    /// with [`prove_reduce`](Self::prove_reduce)'s equations. `a_lit`/`b_lit`
    /// are the *kernel* `int` terms (`int` literals when concrete, `int`-typed
    /// free variables when building the `∀`-clause).
    fn clause_target(&self, op: IntOp, a_lit: &Term, b_lit: &Term) -> Result<Term, HolError>;

    /// Compute `op a b` at the value level (for the driver's redex search).
    ///
    /// The [`NatVariant`] errors when a subtraction would go negative. This is
    /// the value-level twin of [`prove_reduce`](Self::prove_reduce)'s theorem:
    /// both must agree, and the theorem is what the relation actually carries.
    fn eval_op(&self, op: IntOp, a: &Int, b: &Int) -> Result<OpResult, HolError>;

    /// **The proof.** Normalise the concrete clause target `TARGET a b` (for
    /// the two integer literals `a`, `b`) to the reduced sexpr value.
    ///
    /// Returns a [`ReduceProof`] carrying the reduced value `to` and the
    /// **kernel equations** the driver rewrites the instantiated `Step` clause
    /// with (`⊢ int.<op> a b = r`, and for comparisons also
    /// `⊢ cond sexpr r t nil = t/nil`).
    ///
    /// The [`NatVariant`] errors on a negative difference (sub) or a negative
    /// literal, matching [`eval_op`](Self::eval_op).
    fn prove_reduce(&self, op: IntOp, a: &Int, b: &Int) -> Result<ReduceProof, HolError>;
}

/// The result of [`IntBackend::prove_reduce`]: the reduced sexpr value and the
/// kernel equations that rewrite the instantiated `Step` clause's target down
/// to it (applied in order to the whole theorem conclusion).
pub struct ReduceProof {
    /// The reduced sexpr **value** (`(int c)`, or the sexpr `t` / `nil`).
    pub to: Term,
    /// The kernel rewrite equations, in order:
    /// - `⊢ int.<op> a b = r` (`r` an `int` literal for a ring op, a `bool`
    ///   literal for a comparison);
    /// - for comparisons, additionally `⊢ cond sexpr r t nil = t/nil`.
    pub eqs: Vec<Thm>,
}

fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

// ============================================================================
// Shared representation: `(int n)` as `int_head (mk_int n)`
// ============================================================================

/// The sexpr-valued integer-injection head `int : int → sexpr` — a stable
/// fresh free variable. `(int n)` is `int_head τ` applied to the kernel `int`
/// literal `mk_int n`; it is an sexpr **value** the relation can carry.
///
/// Both variants share this head (and hence the same kernel computation), so
/// the `nat` dialect is a genuine *restriction* of the `int` dialect: the same
/// `Step` clause fires, but the backend refuses to *produce* a negative
/// literal.
pub fn int_head(tau: &Type) -> Term {
    Term::free("lisp.rel.int", Type::fun(Type::int(), tau.clone()))
}

/// A stable sexpr-valued operator head `op : sexpr → sexpr → sexpr` (arity 2).
pub fn op_head(op: IntOp, tau: &Type) -> Term {
    let name = match op {
        IntOp::Add => "lisp.rel.+",
        IntOp::Sub => "lisp.rel.-",
        IntOp::Mul => "lisp.rel.*",
        IntOp::Le => "lisp.rel.<=",
        IntOp::Eq => "lisp.rel.=",
    };
    Term::free(
        name,
        Type::fun(tau.clone(), Type::fun(tau.clone(), tau.clone())),
    )
}

/// The kernel op for `op`: `int.add` / `int.sub` / `int.mul` (ring, `int →
/// int → int`) or `int.le` / `(=):int` (comparison, `int → int → bool`).
///
/// `pub(crate)`: the **value semantics** (`crate::semantics`) compiles its
/// integer forms directly onto these kernel operators (typed `int` terms, no
/// sexpr injection), so its redexes match the equations
/// [`IntBackend::prove_reduce`] returns.
pub(crate) fn kernel_op_term(op: IntOp) -> Term {
    use covalence_hol_eval::defs;
    match op {
        IntOp::Add => defs::int_add(),
        IntOp::Sub => defs::int_sub(),
        IntOp::Mul => defs::int_mul(),
        IntOp::Le => defs::int_le(),
        // Integer `=` is HOL equality at `int`; closed literals reduce via
        // the kernel literal-equality certificate.
        IntOp::Eq => Term::eq_op(Type::int()),
    }
}

/// `int.<op> a b` — the closed kernel redex for `op` on two `int` terms.
/// (`pub(crate)`: also the value semantics' compiled form of `(op a b)`.)
pub(crate) fn kernel_redex(op: IntOp, a: &Term, b: &Term) -> Result<Term, HolError> {
    kernel_op_term(op)
        .apply(a.clone())
        .map_err(kernel_err)?
        .apply(b.clone())
        .map_err(kernel_err)
}

/// The generic clause target for `op` over the kernel `int` terms `a`, `b`
/// and the sexpr `t` / `nil` truthiness values.
fn clause_target_of(
    tau: &Type,
    op: IntOp,
    a: &Term,
    b: &Term,
    inject: &dyn Fn(&Term) -> Result<Term, HolError>,
    t: &Term,
    nil: &Term,
) -> Result<Term, HolError> {
    let redex = kernel_redex(op, a, b)?;
    if op.is_cmp() {
        // cond sexpr (int.<cmp> a b) t nil.
        let cond = covalence_hol_eval::defs::cond(tau.clone());
        cond.apply(redex)
            .map_err(kernel_err)?
            .apply(t.clone())
            .map_err(kernel_err)?
            .apply(nil.clone())
            .map_err(kernel_err)
    } else {
        // The backend's exact injection of `int.<op> a b`.
        inject(&redex)
    }
}

/// Shared `prove_reduce` core: reduce the closed kernel redex, and (for a
/// comparison) select the sexpr truthiness value via the kernel `cond` clause.
/// Negative rejection (the `nat` variant) is applied by the caller *before*
/// this.
fn prove_reduce_shared(
    tau: &Type,
    op: IntOp,
    a: &Int,
    b: &Int,
    inj: &dyn Fn(&Int) -> Result<Term, HolError>,
    t: &Term,
    nil: &Term,
) -> Result<ReduceProof, HolError> {
    let a_lit = covalence_hol_eval::mk_int(a.clone());
    let b_lit = covalence_hol_eval::mk_int(b.clone());
    let redex = kernel_redex(op, &a_lit, &b_lit)?;
    // ⊢ int.<op> a b = <kernel literal> (int literal, or bool literal).
    let reduce_eq = redex.reduce().map_err(kernel_err)?;
    let (_lhs, r) = reduce_eq
        .concl()
        .as_eq()
        .ok_or_else(|| HolError::Kernel("int op did not reduce to an equation".into()))?;
    let r = r.clone();

    if op.is_cmp() {
        let b_val = covalence_hol_eval::as_bool(&r).ok_or_else(|| {
            HolError::Kernel(format!(
                "comparison `{}` did not reduce to a bool literal",
                op.symbol()
            ))
        })?;
        // ⊢ cond sexpr <bool-literal> t nil = (t if b_val else nil).
        let (to, cond_eq) = if b_val {
            (
                t.clone(),
                covalence_init::init::cond::cond_true(tau, t, nil).map_err(kernel_err)?,
            )
        } else {
            (
                nil.clone(),
                covalence_init::init::cond::cond_false(tau, t, nil).map_err(kernel_err)?,
            )
        };
        Ok(ReduceProof {
            to,
            eqs: vec![reduce_eq, cond_eq],
        })
    } else {
        let c = covalence_hol_eval::as_int(&r).ok_or_else(|| {
            HolError::Kernel(format!(
                "`{}` did not reduce to an int literal",
                op.symbol()
            ))
        })?;
        Ok(ReduceProof {
            to: inj(&c)?,
            eqs: vec![reduce_eq],
        })
    }
}

// ============================================================================
// The `int` variant — signed integers, sub may go negative
// ============================================================================

/// The honest signed-integer dialect: `(int n)` for any `n : Int`, `-` may go
/// negative.
pub struct IntVariant {
    tau: Type,
    /// The sexpr `t` / `nil` truthiness values (shared with the relation).
    t: Term,
    nil: Term,
}

impl IntVariant {
    /// Build the `int` backend over the sexpr carrier `tau`, with the
    /// relation's `t` / `nil` truthiness values.
    pub fn new(tau: Type, t: Term, nil: Term) -> Self {
        IntVariant { tau, t, nil }
    }

    fn inj(&self, n: &Int) -> Result<Term, HolError> {
        int_head(&self.tau)
            .apply(covalence_hol_eval::mk_int(n.clone()))
            .map_err(kernel_err)
    }
}

impl IntBackend for IntVariant {
    fn lit(&self, n: &Int) -> Result<Term, HolError> {
        self.inj(n)
    }

    fn lit_var(&self, e: &Term) -> Result<Term, HolError> {
        int_head(&self.tau).apply(e.clone()).map_err(kernel_err)
    }

    fn as_lit(&self, t: &Term) -> Option<Int> {
        as_int_value(&self.tau, t)
    }

    fn op_term(&self, op: IntOp, a: Term, b: Term) -> Result<Term, HolError> {
        apply_op(&self.tau, op, a, b)
    }

    fn op_head(&self, op: IntOp) -> Term {
        op_head(op, &self.tau)
    }

    fn clause_target(&self, op: IntOp, a_lit: &Term, b_lit: &Term) -> Result<Term, HolError> {
        clause_target_of(
            &self.tau,
            op,
            a_lit,
            b_lit,
            &|term| int_head(&self.tau).apply(term.clone()).map_err(kernel_err),
            &self.t,
            &self.nil,
        )
    }

    fn eval_op(&self, op: IntOp, a: &Int, b: &Int) -> Result<OpResult, HolError> {
        Ok(eval_op_int(op, a, b))
    }

    fn prove_reduce(&self, op: IntOp, a: &Int, b: &Int) -> Result<ReduceProof, HolError> {
        let inj = |n: &Int| self.inj(n);
        prove_reduce_shared(&self.tau, op, a, b, &inj, &self.t, &self.nil)
    }
}

// ============================================================================
// Exact `int ⊕ bytes` payload variant
// ============================================================================

/// Exact integer atoms inside a carved S-expression whose payload is
/// `int ⊕ bytes`.
///
/// Unlike [`IntVariant`], this is not an unconstrained auxiliary injection:
/// `n` is represented by the datatype constructor `atom (inl n)`. Integers
/// can therefore occur anywhere ordinary data can, including nested quoted
/// lists, while arithmetic still reuses the same kernel `int` theorems.
#[derive(Clone)]
pub struct IntSymbolPayloadVariant {
    tau: Type,
    atom: Term,
    t: Term,
    nil: Term,
}

impl IntSymbolPayloadVariant {
    pub fn new(tau: Type, atom: Term, t: Term, nil: Term) -> Self {
        Self { tau, atom, t, nil }
    }

    fn inj_term(&self, integer: &Term) -> Result<Term, HolError> {
        let payload = covalence_hol_eval::defs::inl(Type::int(), Type::bytes())
            .apply(integer.clone())
            .map_err(kernel_err)?;
        self.atom.clone().apply(payload).map_err(kernel_err)
    }

    fn inj(&self, integer: &Int) -> Result<Term, HolError> {
        self.inj_term(&covalence_hol_eval::mk_int(integer.clone()))
    }
}

impl IntBackend for IntSymbolPayloadVariant {
    fn lit(&self, n: &Int) -> Result<Term, HolError> {
        self.inj(n)
    }

    fn lit_var(&self, e: &Term) -> Result<Term, HolError> {
        self.inj_term(e)
    }

    fn as_lit(&self, term: &Term) -> Option<Int> {
        let (atom, payload) = term.as_app()?;
        if *atom != self.atom {
            return None;
        }
        let (injection, integer) = payload.as_app()?;
        if *injection != covalence_hol_eval::defs::inl(Type::int(), Type::bytes()) {
            return None;
        }
        covalence_hol_eval::as_int(integer)
    }

    fn op_term(&self, op: IntOp, a: Term, b: Term) -> Result<Term, HolError> {
        apply_op(&self.tau, op, a, b)
    }

    fn op_head(&self, op: IntOp) -> Term {
        op_head(op, &self.tau)
    }

    fn clause_target(&self, op: IntOp, a_lit: &Term, b_lit: &Term) -> Result<Term, HolError> {
        clause_target_of(
            &self.tau,
            op,
            a_lit,
            b_lit,
            &|integer| self.inj_term(integer),
            &self.t,
            &self.nil,
        )
    }

    fn eval_op(&self, op: IntOp, a: &Int, b: &Int) -> Result<OpResult, HolError> {
        Ok(eval_op_int(op, a, b))
    }

    fn prove_reduce(&self, op: IntOp, a: &Int, b: &Int) -> Result<ReduceProof, HolError> {
        prove_reduce_shared(
            &self.tau,
            op,
            a,
            b,
            &|integer| self.inj(integer),
            &self.t,
            &self.nil,
        )
    }
}

// ============================================================================
// The `nat` variant — naturals only, sub errors on a negative difference
// ============================================================================

/// The natural-number dialect: the same `int`-literal encoding and kernel
/// computation as [`IntVariant`], but **negatives are rejected** —
/// [`lit`](IntBackend::lit) errors for `n < 0`, and `-`/comparisons that would
/// require a negative literal error too.
pub struct NatVariant {
    tau: Type,
    t: Term,
    nil: Term,
}

impl NatVariant {
    /// Build the `nat` backend over the sexpr carrier `tau`.
    pub fn new(tau: Type, t: Term, nil: Term) -> Self {
        NatVariant { tau, t, nil }
    }

    fn inj(&self, n: &Int) -> Result<Term, HolError> {
        reject_negative(n)?;
        int_head(&self.tau)
            .apply(covalence_hol_eval::mk_int(n.clone()))
            .map_err(kernel_err)
    }

    /// Reject a ring op whose result is negative (`sub` going below zero).
    fn guard_result(&self, op: IntOp, a: &Int, b: &Int) -> Result<(), HolError> {
        if let OpResult::Int(ref n) = eval_op_int(op, a, b)
            && n < &Int::from(0i128)
        {
            return Err(HolError::Theory(format!(
                "nat dialect: `{}` of `{a}` `{b}` is negative (`{n}`)",
                op.symbol()
            )));
        }
        Ok(())
    }
}

impl IntBackend for NatVariant {
    fn lit(&self, n: &Int) -> Result<Term, HolError> {
        self.inj(n)
    }

    fn lit_var(&self, e: &Term) -> Result<Term, HolError> {
        int_head(&self.tau).apply(e.clone()).map_err(kernel_err)
    }

    fn as_lit(&self, t: &Term) -> Option<Int> {
        as_int_value(&self.tau, t)
    }

    fn op_term(&self, op: IntOp, a: Term, b: Term) -> Result<Term, HolError> {
        apply_op(&self.tau, op, a, b)
    }

    fn op_head(&self, op: IntOp) -> Term {
        op_head(op, &self.tau)
    }

    fn clause_target(&self, op: IntOp, a_lit: &Term, b_lit: &Term) -> Result<Term, HolError> {
        clause_target_of(
            &self.tau,
            op,
            a_lit,
            b_lit,
            &|term| int_head(&self.tau).apply(term.clone()).map_err(kernel_err),
            &self.t,
            &self.nil,
        )
    }

    fn eval_op(&self, op: IntOp, a: &Int, b: &Int) -> Result<OpResult, HolError> {
        self.guard_result(op, a, b)?;
        Ok(eval_op_int(op, a, b))
    }

    fn prove_reduce(&self, op: IntOp, a: &Int, b: &Int) -> Result<ReduceProof, HolError> {
        // Guard the negative case up front (matching `eval_op`), so the nat
        // dialect never emits a `Step … (int <negative>)`.
        self.guard_result(op, a, b)?;
        let inj = |n: &Int| self.inj(n);
        prove_reduce_shared(&self.tau, op, a, b, &inj, &self.t, &self.nil)
    }
}

// ============================================================================
// Shared value-level helpers
// ============================================================================

/// `(op a b)` as an sexpr term (both variants share the same heads).
fn apply_op(tau: &Type, op: IntOp, a: Term, b: Term) -> Result<Term, HolError> {
    op_head(op, tau)
        .apply(a)
        .map_err(kernel_err)?
        .apply(b)
        .map_err(kernel_err)
}

/// Error out for a negative integer (the `nat` dialect's literal guard).
fn reject_negative(n: &Int) -> Result<(), HolError> {
    if n < &Int::from(0i128) {
        return Err(HolError::Theory(format!(
            "nat dialect: cannot build negative integer literal `{n}`"
        )));
    }
    Ok(())
}

/// Value-level `op a b` on `Int` (no dialect restriction — the `nat` variant
/// layers its negativity check on top).
fn eval_op_int(op: IntOp, a: &Int, b: &Int) -> OpResult {
    match op {
        IntOp::Add => OpResult::Int(a.clone() + b.clone()),
        IntOp::Sub => OpResult::Int(a.clone() - b.clone()),
        IntOp::Mul => OpResult::Int(a.clone() * b.clone()),
        IntOp::Le => OpResult::Bool(a <= b),
        IntOp::Eq => OpResult::Bool(a == b),
    }
}

/// Recognise `int_head (mk_int n)` — the shared `(int n)` value encoding.
fn as_int_value(tau: &Type, t: &Term) -> Option<Int> {
    let (head, arg) = t.as_app()?;
    if *head != int_head(tau) {
        return None;
    }
    covalence_hol_eval::as_int(arg)
}

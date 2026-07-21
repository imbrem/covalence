//! **Kernel-term carriers for the abstract S-expression value algebra**
//! (`hol` feature) — the Layer-2 adapters of
//! `notes/vibes/lisp/abstract-sexpr-api.md` (§1.1, slice 1).
//!
//! [`KernelSExpr`] extends [`AbstractSExpr`] (values = kernel [`Term`]s) with
//! the **proved structural laws** of a carved carrier: projections, atom
//! injectivity, structural induction. Everything here is *delegation to
//! already-proved theorems* on the wrapped theory — the traits mint nothing.
//!
//! Two adapters:
//!
//! - [`CarvedCarrier`] — a carved [`CarvedSExpr`] instance (the flagship
//!   `bytes`-payload `sexpr`, or any further `build_with` instance) plus an
//!   optional [`IntBackend`] for the `(int n)` free-variable injection. One
//!   struct covers `sector`, `sector+int(int)`, `sector+int(nat)`, and the
//!   value semantics' data half, as *configurations*.
//!
//!   **Capability note (the `int_head` trap):** the backend's `(int n)` is an
//!   injection through an *unconstrained free variable head* — no ∀-lifted
//!   arithmetic facts range over it. It satisfies `atom`/`as_atom` like any
//!   payload, but nothing quantified transports through it. Only a genuine
//!   payload carrier (an `int`-payload carve, or [`Acl2Carrier`]) supports
//!   quantified arithmetic transport. Nothing generic may *prove* through
//!   this difference; it is a documented capability split.
//!
//! - [`Acl2Carrier`] — the ACL2 object universe `A` (payload
//!   `coprod int bytes`): integers are **genuine payload** (`aint`), symbols
//!   are `asym`, `nil` is the datatype leaf `anil`. `quote` overrides the
//!   default fold with ACL2's datum discipline (numerals → `aint`, `nil`/`t`
//!   any case → the canonical `anil` / `t` — never `asym "NIL"`, the
//!   representation contract).

use std::sync::{Arc, LazyLock};

use covalence_core::subst;
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{as_blob, as_int, defs, mk_blob, mk_bool, mk_int};
use covalence_init::init::acl2::carrier::{Acl2, acl2_payload};
use covalence_init::init::acl2::prims::{Prims, prims};
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, LeafKind, carved};
use covalence_init::init::lisp::Lisp as KernelLisp;
use covalence_init::{Term, Type};
use covalence_sexp::{AbstractSExpr, NumeralPolicy, PayloadLit, PayloadOwned, SExp, SExpr};
use covalence_types::Int;

use crate::hol::HolError;
use crate::int_backend::IntBackend;

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

/// A kernel-term S-expression carrier: the value algebra *plus* the proved
/// structural laws of the underlying carved theory.
///
/// Every method returning a [`Thm`] is pure delegation to theorems already
/// proved in `covalence-init` — implementations introduce no postulates and
/// no new trusted rules.
pub trait KernelSExpr: AbstractSExpr<Value = Term> {
    /// The carrier type (`sexpr`, or ACL2's `A`).
    fn tau(&self) -> Type;

    /// The projection operator term (`car` for `false`, `cdr` for `true`) —
    /// so callers can *state* the projection laws independently.
    fn proj_op(&self, take_cdr: bool) -> Term;

    /// The proved projection law at the value `v`:
    /// `⊢ car/cdr (cons h t) = h/t` on a cons cell, and the leaf defaults
    /// `⊢ car/cdr (atom b) = nil` / `⊢ car/cdr nil = nil`. Errors on a
    /// non-value (nothing is minted).
    fn proj(&self, take_cdr: bool, v: &Term) -> Result<Thm, Self::Error>;

    /// The proved atom-constructor injectivity at payload terms `b1`, `b2`:
    /// `⊢ (atom b1 = atom b2) ⟹ b1 = b2`.
    fn inj_atom(&self, b1: &Term, b2: &Term) -> Result<Thm, Self::Error>;

    /// The structural-induction seam (rule form, applied motives; the carved
    /// binder-hint names `b`/`h`/`t` are load-bearing): from `⊢ P (atom b)`,
    /// `⊢ P nil`, `⊢ P h ⟹ P t ⟹ P (cons h t)` conclude `⊢ ∀s. P s`.
    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm, Self::Error>;
}

/// The exact shared Lisp datum payload: integers on the left, symbol/string
/// bytes on the right.
pub fn int_symbol_payload() -> Type {
    defs::coprod(Type::int(), Type::bytes())
}

/// A carved inductive S-expression instance with exact integer-or-symbol
/// atoms. It is intentionally independent of ACL2's object universe: both
/// instantiate the same generic datatype API and can later be related by an
/// explicit morphism.
pub fn exact_datum_carved() -> Result<&'static CarvedSExpr, HolError> {
    static DATUM: LazyLock<std::result::Result<CarvedSExpr, String>> = LazyLock::new(|| {
        CarvedSExpr::build_with(int_symbol_payload(), "lisp.datum")
            .map_err(|error| error.to_string())
    });
    DATUM
        .as_ref()
        .map_err(|error| HolError::Theory(format!("exact Lisp datum build failed: {error}")))
}

/// Proof-producing operations specialized to exact `int ⊕ bytes` Lisp data.
///
/// This bundles the shared S-expression fixpoint, its ordinary Lisp
/// catamorphisms, and `integer?`, whose atom branch performs coproduct case
/// analysis. It is built once and introduces only conservative definitions.
pub struct ExactDatumTheory {
    pub sexpr: &'static CarvedSExpr,
    pub lisp: KernelLisp,
    integer_p: Term,
    integer_p_eq: Thm,
    integer_steps: [Term; 3],
}

/// Process-global exact datum theory used by Scheme and the exact relational
/// dialect. ACL2 retains its independently realized but isomorphic carrier.
pub fn exact_datum_theory() -> Result<&'static ExactDatumTheory, HolError> {
    static THEORY: LazyLock<std::result::Result<ExactDatumTheory, String>> =
        LazyLock::new(|| build_exact_datum_theory().map_err(|error| error.to_string()));
    THEORY
        .as_ref()
        .map_err(|error| HolError::Theory(format!("exact Lisp datum theory failed: {error}")))
}

fn build_exact_datum_theory() -> Result<ExactDatumTheory, HolError> {
    let sexpr = exact_datum_carved()?;
    let lisp = KernelLisp::build_with(sexpr, "lisp.datum.ops").map_err(theory_err)?;
    let payload = Term::free("__payload", int_symbol_payload());
    let on_int = Term::abs(Type::int(), mk_bool(true));
    let on_symbol = Term::abs(Type::bytes(), mk_bool(false));
    let dispatch =
        covalence_init::init::coprod::coprod_case(Type::int(), Type::bytes(), Type::bool())
            .apply(on_int)
            .map_err(kernel_err)?
            .apply(on_symbol)
            .map_err(kernel_err)?
            .apply(payload.clone())
            .map_err(kernel_err)?;
    let atom_step = Term::abs(int_symbol_payload(), subst::close(&dispatch, "__payload"));
    let false_value = mk_bool(false);
    let cons_step = Term::abs(
        sexpr.tau.clone(),
        Term::abs(
            sexpr.tau.clone(),
            Term::abs(Type::bool(), Term::abs(Type::bool(), false_value.clone())),
        ),
    );
    let integer_steps = [atom_step, false_value, cons_step];
    let body = sexpr
        .prec(&integer_steps, &Type::bool())
        .map_err(kernel_err)?;
    let integer_p_eq = Thm::define("lisp.datum.integer?", body).map_err(kernel_err)?;
    let integer_p = integer_p_eq
        .concl()
        .as_eq()
        .ok_or_else(|| HolError::Kernel("integer? definition is not an equation".into()))?
        .0
        .clone();
    Ok(ExactDatumTheory {
        sexpr,
        lisp,
        integer_p,
        integer_p_eq,
        integer_steps,
    })
}

impl ExactDatumTheory {
    pub fn integer_p(&self) -> &Term {
        &self.integer_p
    }

    /// Prove `integer? (atom payload)` by coproduct reduction.
    pub fn integer_atom(&self, payload: &Term) -> Result<Thm, HolError> {
        let atom = self
            .sexpr
            .atom
            .clone()
            .apply(payload.clone())
            .map_err(kernel_err)?;
        let unfold = self
            .integer_p_eq
            .clone()
            .cong_fn(atom)
            .map_err(kernel_err)?;
        let compute = self
            .sexpr
            .prec_eq(&self.integer_steps, 0, &Type::bool())
            .map_err(kernel_err)?
            .all_elim(payload.clone())
            .map_err(kernel_err)?;
        let mut theorem = unfold
            .trans(compute)
            .map_err(kernel_err)?
            .reduce_rhs()
            .map_err(kernel_err)?;
        if let Some((injection, value)) = payload.as_app() {
            let on_int = Term::abs(Type::int(), mk_bool(true));
            let on_symbol = Term::abs(Type::bytes(), mk_bool(false));
            let case = if *injection == defs::inl(Type::int(), Type::bytes()) {
                covalence_init::init::coprod::case_inl(
                    &Type::int(),
                    &Type::bytes(),
                    &Type::bool(),
                    &on_int,
                    &on_symbol,
                    value,
                )
            } else if *injection == defs::inr(Type::int(), Type::bytes()) {
                covalence_init::init::coprod::case_inr(
                    &Type::int(),
                    &Type::bytes(),
                    &Type::bool(),
                    &on_int,
                    &on_symbol,
                    value,
                )
            } else {
                return Err(HolError::Stuck(
                    "integer? atom has an unknown payload variant".into(),
                ));
            };
            theorem = theorem
                .trans(case.map_err(kernel_err)?)
                .map_err(kernel_err)?;
        }
        theorem.reduce_rhs().map_err(kernel_err)
    }

    pub fn integer_nil(&self) -> Result<Thm, HolError> {
        self.integer_p_eq
            .clone()
            .cong_fn(self.sexpr.snil.clone())
            .map_err(kernel_err)?
            .trans(
                self.sexpr
                    .prec_eq(&self.integer_steps, 1, &Type::bool())
                    .map_err(kernel_err)?,
            )
            .map_err(kernel_err)
    }

    pub fn integer_cons(&self, head: &Term, tail: &Term) -> Result<Thm, HolError> {
        let cons = self
            .sexpr
            .scons
            .clone()
            .apply(head.clone())
            .map_err(kernel_err)?
            .apply(tail.clone())
            .map_err(kernel_err)?;
        let unfold = self
            .integer_p_eq
            .clone()
            .cong_fn(cons)
            .map_err(kernel_err)?;
        let compute = self
            .sexpr
            .prec_eq(&self.integer_steps, 2, &Type::bool())
            .map_err(kernel_err)?
            .all_elim(head.clone())
            .map_err(kernel_err)?
            .all_elim(tail.clone())
            .map_err(kernel_err)?;
        unfold
            .trans(compute)
            .map_err(kernel_err)?
            .reduce_rhs()
            .map_err(kernel_err)
    }
}

// ============================================================================
// CarvedCarrier — any carved instance (+ optional int-injection backend)
// ============================================================================

/// An [`AbstractSExpr`]/[`KernelSExpr`] adapter over a carved
/// [`CarvedSExpr`] instance.
///
/// Payload handling is driven by the instance's payload type:
/// - `bytes` payload (the flagship `sexpr`): `Sym` atoms are blob payloads;
///   `Int` atoms go through the installed [`IntBackend`] (the `(int n)`
///   injection) or error when none is installed (the `sector` dialect's
///   honest "no integers").
/// - `int` payload: `Int` atoms are genuine payload; `Sym` atoms error.
/// - any other payload: both literal payload kinds error (build such values
///   with the instance's own constructors); the structural laws
///   (`proj`/`inj_atom`/`induct`) still apply.
#[derive(Clone)]
pub struct CarvedCarrier {
    cs: &'static CarvedSExpr,
    int: Option<Arc<dyn IntBackend + Send + Sync>>,
    quote_policy: NumeralPolicy,
    payload_layout: PayloadLayout,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PayloadLayout {
    Direct,
    IntOrSymbol,
}

impl CarvedCarrier {
    /// The `sector` configuration: the process-global `bytes`-payload
    /// carve, no integer atoms.
    pub fn sector() -> Result<Self, HolError> {
        Ok(Self::over(carved().map_err(theory_err)?))
    }

    /// The process-global `bytes`-payload carve with an [`IntBackend`]
    /// (the `sector+int` / value-semantics data configurations). The quote
    /// policy stays [`NumeralPolicy::Sym`] — today's dialects quote
    /// numerals-in-data as uninterpreted symbol atoms even when integer
    /// *expressions* are on; opt in to `Int` quoting explicitly via
    /// [`with_quote_policy`](Self::with_quote_policy).
    pub fn with_int(int: Arc<dyn IntBackend + Send + Sync>) -> Result<Self, HolError> {
        let mut c = Self::sector()?;
        c.int = Some(int);
        Ok(c)
    }

    /// An adapter over any carved instance (a further
    /// [`CarvedSExpr::build_with`] carrier — the "same proofs at another
    /// payload" seam), with no integer backend.
    pub fn over(cs: &'static CarvedSExpr) -> Self {
        CarvedCarrier {
            cs,
            int: None,
            quote_policy: NumeralPolicy::Sym,
            payload_layout: PayloadLayout::Direct,
        }
    }

    /// Exact `int ⊕ bytes` atoms over `cs`, with arithmetic supplied by the
    /// matching exact-payload integer backend.
    pub fn int_or_symbol(
        cs: &'static CarvedSExpr,
        int: Arc<dyn IntBackend + Send + Sync>,
    ) -> Result<Self, HolError> {
        if cs.payload != int_symbol_payload() {
            return Err(HolError::Theory(format!(
                "exact Lisp datum carrier expected payload `{}`, got `{}`",
                int_symbol_payload(),
                cs.payload
            )));
        }
        Ok(Self {
            cs,
            int: Some(int),
            quote_policy: NumeralPolicy::Int,
            payload_layout: PayloadLayout::IntOrSymbol,
        })
    }

    /// Override the [`quote`](AbstractSExpr::quote) numeral policy.
    pub fn with_quote_policy(mut self, policy: NumeralPolicy) -> Self {
        self.quote_policy = policy;
        self
    }

    /// The wrapped carved theory.
    pub fn theory(&self) -> &'static CarvedSExpr {
        self.cs
    }

    /// The **payload term** of an `atom b` value (syntactic observer; the
    /// raw kernel term, un-decoded). This is what the proof-side consumers
    /// (`proj_leaf`, `inj_atom`) take.
    pub fn as_atom_term(&self, v: &Term) -> Option<Term> {
        let (op, b) = v.as_app()?;
        (*op == self.cs.atom).then(|| b.clone())
    }

    /// The decoded bytes of a `bytes`-payload atom value.
    pub fn atom_bytes(&self, v: &Term) -> Option<Vec<u8>> {
        match self.as_atom(v)? {
            PayloadOwned::Sym(bytes) => Some(bytes),
            PayloadOwned::Int(_) => None,
            _ => None,
        }
    }

    /// The integer of an `(int n)` backend-injected value (`None` when no
    /// backend is installed or `v` is not that shape).
    pub fn as_int_lit(&self, v: &Term) -> Option<Int> {
        self.int.as_deref()?.as_lit(v)
    }
}

impl AbstractSExpr for CarvedCarrier {
    type Value = Term;
    type Error = HolError;

    fn nil(&self) -> Term {
        self.cs.snil.clone()
    }

    fn cons(&self, h: Term, t: Term) -> Result<Term, HolError> {
        self.cs
            .scons
            .clone()
            .apply(h)
            .map_err(kernel_err)?
            .apply(t)
            .map_err(kernel_err)
    }

    fn atom(&self, p: PayloadLit<'_>) -> Result<Term, HolError> {
        match p {
            PayloadLit::Sym(b) => {
                if self.payload_layout == PayloadLayout::IntOrSymbol {
                    let payload = defs::inr(Type::int(), Type::bytes())
                        .apply(mk_blob(b.to_vec()))
                        .map_err(kernel_err)?;
                    return self.cs.atom.clone().apply(payload).map_err(kernel_err);
                }
                if self.cs.payload != Type::bytes() {
                    return Err(HolError::Stuck(format!(
                        "this carrier's atom payload is `{}`, not `bytes` — no symbol atoms",
                        self.cs.payload
                    )));
                }
                self.cs
                    .atom
                    .clone()
                    .apply(mk_blob(b.to_vec()))
                    .map_err(kernel_err)
            }
            PayloadLit::Int(n) => {
                if let Some(be) = self.int.as_deref() {
                    return be.lit(n);
                }
                if self.cs.payload == Type::int() {
                    return self
                        .cs
                        .atom
                        .clone()
                        .apply(mk_int(n.clone()))
                        .map_err(kernel_err);
                }
                Err(HolError::Stuck(
                    "this dialect has no integer atoms (`sector`: numerals stay symbols)".into(),
                ))
            }
            // `PayloadLit` is non_exhaustive: a future payload kind is an
            // honest per-dialect error until this carrier supports it.
            _ => Err(HolError::Stuck(
                "unsupported atom payload kind for this carrier".into(),
            )),
        }
    }

    fn as_cons(&self, v: &Term) -> Option<(Term, Term)> {
        let (inner, t) = v.as_app()?;
        let (op, h) = inner.as_app()?;
        (*op == self.cs.scons).then(|| (h.clone(), t.clone()))
    }

    fn as_atom(&self, v: &Term) -> Option<PayloadOwned> {
        if let Some(n) = self.as_int_lit(v) {
            return Some(PayloadOwned::Int(n));
        }
        let p = self.as_atom_term(v)?;
        if self.payload_layout == PayloadLayout::IntOrSymbol
            && let Some((injection, bytes)) = p.as_app()
            && *injection == defs::inr(Type::int(), Type::bytes())
        {
            return as_blob(bytes).map(|bytes| PayloadOwned::Sym(bytes.to_vec()));
        }
        if self.cs.payload == Type::bytes() {
            return as_blob(&p).map(|b| PayloadOwned::Sym(b.to_vec()));
        }
        if self.cs.payload == Type::int() {
            return as_int(&p).map(PayloadOwned::Int);
        }
        None
    }

    fn is_nil(&self, v: &Term) -> bool {
        *v == self.cs.snil
    }

    fn numeral_policy(&self) -> NumeralPolicy {
        self.quote_policy
    }
}

impl KernelSExpr for CarvedCarrier {
    fn tau(&self) -> Type {
        self.cs.tau.clone()
    }

    fn proj_op(&self, take_cdr: bool) -> Term {
        if take_cdr {
            self.cs.cdr.clone()
        } else {
            self.cs.car.clone()
        }
    }

    fn proj(&self, take_cdr: bool, v: &Term) -> Result<Thm, HolError> {
        if let Some((h, t)) = self.as_cons(v) {
            return self.cs.proj_scons(take_cdr, &h, &t).map_err(kernel_err);
        }
        if let Some(b) = self.as_atom_term(v) {
            return self
                .cs
                .proj_leaf(take_cdr, LeafKind::Atom(&b))
                .map_err(kernel_err);
        }
        if self.is_nil(v) {
            return self
                .cs
                .proj_leaf(take_cdr, LeafKind::Nil)
                .map_err(kernel_err);
        }
        Err(HolError::Stuck(format!(
            "car/cdr law: `{v}` is not a carrier value"
        )))
    }

    fn inj_atom(&self, b1: &Term, b2: &Term) -> Result<Thm, HolError> {
        self.cs.inj_atom(b1, b2).map_err(kernel_err)
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm, HolError> {
        self.cs.induct(motive, cases).map_err(kernel_err)
    }
}

// ============================================================================
// Acl2Carrier — the ACL2 object universe (payload = coprod int bytes)
// ============================================================================

/// An [`AbstractSExpr`]/[`KernelSExpr`] adapter over the ACL2 carrier `A`.
///
/// Values follow the S1 conventions: integers are `aint i` (genuine payload
/// with the proved `init/int` theory behind it), symbols are `asym ⌜s⌝`,
/// `nil` is the leaf `anil`, and the canonical true value is the defined
/// constant `t` (= `asym "T"` by its defining equation), which
/// [`as_atom`](AbstractSExpr::as_atom) observes as the symbol payload `"T"`.
#[derive(Clone, Copy)]
pub struct Acl2Carrier {
    a: &'static Acl2,
    pr: &'static Prims,
}

impl Acl2Carrier {
    /// Bind the process-global ACL2 carrier + S1 primitive theories.
    pub fn new() -> Result<Self, HolError> {
        let pr = prims().map_err(theory_err)?;
        Ok(Acl2Carrier { a: pr.th, pr })
    }

    /// The wrapped S0 carrier theory.
    pub fn theory(&self) -> &'static Acl2 {
        self.a
    }

    /// The canonical ACL2 true value `t`.
    pub fn t(&self) -> Term {
        self.pr.t.clone()
    }

    /// The **payload term** of an `aatom l` value (the datatype-constructor
    /// form; the derived `aint i` / `asym s` forms are *not* matched here —
    /// they observe via [`as_atom`](AbstractSExpr::as_atom)).
    pub fn as_aatom_term(&self, v: &Term) -> Option<Term> {
        let (op, l) = v.as_app()?;
        (*op == self.a.atom).then(|| l.clone())
    }

    /// The integer payload term of `aint i`.
    fn as_aint_arg(&self, v: &Term) -> Option<Term> {
        let (f, i) = v.as_app()?;
        (*f == self.a.aint).then(|| i.clone())
    }

    /// The bytes payload term of `asym s`.
    fn as_asym_arg(&self, v: &Term) -> Option<Term> {
        let (f, s) = v.as_app()?;
        (*f == self.a.asym).then(|| s.clone())
    }
}

impl AbstractSExpr for Acl2Carrier {
    type Value = Term;
    type Error = HolError;

    fn nil(&self) -> Term {
        self.a.nil.clone()
    }

    fn cons(&self, h: Term, t: Term) -> Result<Term, HolError> {
        self.a
            .cons
            .clone()
            .apply(h)
            .map_err(kernel_err)?
            .apply(t)
            .map_err(kernel_err)
    }

    fn atom(&self, p: PayloadLit<'_>) -> Result<Term, HolError> {
        match p {
            PayloadLit::Sym(b) => {
                // Representation contract: never `asym "NIL"` — it would be
                // a junk value distinct from `anil`.
                if b.eq_ignore_ascii_case(b"nil") {
                    return Err(HolError::Stuck(
                        "ACL2 representation contract: `nil` is the leaf `anil`, never \
                         `asym \"NIL\"` — use `nil()`"
                            .into(),
                    ));
                }
                self.a.asym_lit(b).map_err(kernel_err)
            }
            PayloadLit::Int(n) => self.a.aint_at(&mk_int(n.clone())).map_err(kernel_err),
            // `PayloadLit` is non_exhaustive: a future payload kind is an
            // honest per-dialect error until this carrier supports it.
            _ => Err(HolError::Stuck(
                "unsupported atom payload kind for the ACL2 carrier".into(),
            )),
        }
    }

    fn as_cons(&self, v: &Term) -> Option<(Term, Term)> {
        let (inner, t) = v.as_app()?;
        let (op, h) = inner.as_app()?;
        (*op == self.a.cons).then(|| (h.clone(), t.clone()))
    }

    fn as_atom(&self, v: &Term) -> Option<PayloadOwned> {
        // The canonical `t` constant (= `asym "T"` by its defining equation).
        if *v == self.pr.t {
            return Some(PayloadOwned::Sym(b"T".to_vec()));
        }
        if let Some(i) = self.as_aint_arg(v) {
            return as_int(&i).map(PayloadOwned::Int);
        }
        if let Some(s) = self.as_asym_arg(v) {
            return as_blob(&s).map(|b| PayloadOwned::Sym(b.to_vec()));
        }
        // The raw datatype-constructor form `aatom (inl i | inr s)`.
        if let Some(l) = self.as_aatom_term(v)
            && let Some((f, x)) = l.as_app()
        {
            if *f == defs::inl(Type::int(), Type::bytes()) {
                return as_int(x).map(PayloadOwned::Int);
            }
            if *f == defs::inr(Type::int(), Type::bytes()) {
                return as_blob(x).map(|b| PayloadOwned::Sym(b.to_vec()));
            }
        }
        None
    }

    fn is_nil(&self, v: &Term) -> bool {
        *v == self.a.nil
    }

    fn numeral_policy(&self) -> NumeralPolicy {
        NumeralPolicy::Int
    }

    /// ACL2's datum discipline (mirrors the dialect's quoted-datum fold):
    /// numerals → `aint`, `nil`/`t` (any case) → the canonical `anil` / `t`,
    /// other symbols → `asym` of the bytes as written, proper lists →
    /// `acons` chains. String literals are not ACL2 objects — a clean error.
    fn quote(&self, data: &SExpr) -> Result<Term, HolError> {
        match data {
            SExp::Atom(covalence_sexp::Atom::Symbol(s)) => {
                let s = s.as_str();
                if let Ok(n) = s.parse::<Int>() {
                    return self.atom(PayloadLit::Int(&n));
                }
                if s.eq_ignore_ascii_case("nil") {
                    return Ok(self.nil());
                }
                if s.eq_ignore_ascii_case("t") {
                    return Ok(self.t());
                }
                self.atom(PayloadLit::Sym(s.as_bytes()))
            }
            SExp::Atom(covalence_sexp::Atom::Str { .. }) => Err(HolError::Stuck(
                "ACL2 datum: string literals are not ACL2 objects".into(),
            )),
            SExp::List(items) => {
                let mut acc = self.nil();
                for it in items.iter().rev() {
                    let h = self.quote(it)?;
                    acc = self.cons(h, acc)?;
                }
                Ok(acc)
            }
        }
    }
}

impl KernelSExpr for Acl2Carrier {
    fn tau(&self) -> Type {
        self.a.ty.clone()
    }

    fn proj_op(&self, take_cdr: bool) -> Term {
        if take_cdr {
            self.a.cdr.clone()
        } else {
            self.a.car.clone()
        }
    }

    fn proj(&self, take_cdr: bool, v: &Term) -> Result<Thm, HolError> {
        if let Some((h, t)) = self.as_cons(v) {
            return self.a.cs.proj_scons(take_cdr, &h, &t).map_err(kernel_err);
        }
        if self.is_nil(v) {
            return self
                .a
                .cs
                .proj_leaf(take_cdr, LeafKind::Nil)
                .map_err(kernel_err);
        }
        if let Some(l) = self.as_aatom_term(v) {
            return self
                .a
                .cs
                .proj_leaf(take_cdr, LeafKind::Atom(&l))
                .map_err(kernel_err);
        }
        // The derived payload forms: unfold `aint i` / `asym s` to the
        // `aatom` form (their defining equations), take the leaf law there,
        // and state the result about the *original* value by congruence:
        // `⊢ proj (aint i) = proj (aatom (inl i)) = anil`.
        let unfold_law = if let Some(i) = self.as_aint_arg(v) {
            Some((
                self.a.int_unfold(&i).map_err(kernel_err)?,
                defs::inl(Type::int(), Type::bytes())
                    .apply(i)
                    .map_err(kernel_err)?,
            ))
        } else if let Some(s) = self.as_asym_arg(v) {
            Some((
                self.a.sym_unfold(&s).map_err(kernel_err)?,
                defs::inr(Type::int(), Type::bytes())
                    .apply(s)
                    .map_err(kernel_err)?,
            ))
        } else {
            None
        };
        if let Some((unfold, payload)) = unfold_law {
            let leaf = self
                .a
                .cs
                .proj_leaf(take_cdr, LeafKind::Atom(&payload))
                .map_err(kernel_err)?;
            return unfold
                .cong_arg(self.proj_op(take_cdr))
                .map_err(kernel_err)?
                .trans(leaf)
                .map_err(kernel_err);
        }
        Err(HolError::Stuck(format!(
            "car/cdr law: `{v}` is not an ACL2 carrier value (note: the defined `t` \
             constant projects via its unfolding, not here)"
        )))
    }

    fn inj_atom(&self, b1: &Term, b2: &Term) -> Result<Thm, HolError> {
        self.a.atom_inj(b1, b2).map_err(kernel_err)
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm, HolError> {
        self.a.induct(motive, cases).map_err(kernel_err)
    }
}

/// The ACL2 payload type `coprod int bytes` (re-exported convenience for
/// carrier-generic callers stating payload-typed facts).
pub fn acl2_payload_ty() -> Type {
    acl2_payload()
}

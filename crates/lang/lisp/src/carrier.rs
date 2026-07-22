//! **Kernel-term carriers for the abstract S-expression value algebra**
//! (`hol` feature) — the Layer-2 adapters of
//! `notes/vibes/lisp/abstract-sexpr-api.md` (§1.1, slice 1).
//!
//! [`KernelSExpr`] extends [`SExprView`](BackendSExprView) (values = kernel [`Term`]s) with
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
use covalence_sexp::{SExp, SExpr};
use covalence_sexpr_api::{
    SExprF, SExprSyntax as BackendSExprSyntax, SExprView as BackendSExprView,
};
use covalence_types::Int;

use crate::hol::HolError;
use crate::int_backend::IntBackend;

/// Atom payload shared by proof-producing Lisp datum carriers.
///
/// String literals are interpreted by each surface dialect before reaching
/// this layer; the logical carriers currently distinguish exact integers from
/// uninterpreted symbol bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DatumPayload {
    Symbol(Vec<u8>),
    Integer(Int),
}

/// How a surface codec interprets numeral-shaped symbols in quoted data.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DatumNumerals {
    #[default]
    Symbols,
    Integers,
}

fn theory_err(e: impl core::fmt::Display) -> HolError {
    HolError::Theory(e.to_string())
}
fn kernel_err(e: impl core::fmt::Display) -> HolError {
    HolError::Kernel(e.to_string())
}

/// Language-layer codec between parsed proper-list syntax and a logical Lisp
/// datum carrier.
///
/// Constructor/view structure comes from `kernel/lisp/sexpr`; this layer owns
/// only surface policies such as numeral interpretation and ACL2's canonical
/// `nil`/`t` spellings.
pub trait LispDatum: BackendSExprView
where
    Self::Value: Clone,
{
    /// Interpret one parsed atom according to the surface dialect.
    fn lower_atom(&self, atom: &covalence_sexp::Atom) -> Result<Self::Value, Self::Error>;

    /// Render one decoded carrier payload. Returning `None` rejects payloads
    /// that have no surface representation in this dialect.
    fn render_payload(&self, payload: Self::Payload) -> Option<SExpr>;

    fn quote(&self, data: &SExpr) -> Result<Self::Value, Self::Error> {
        match data {
            SExp::Atom(atom) => self.lower_atom(atom),
            SExp::List(items) => {
                let mut result = BackendSExprSyntax::nil(self);
                for item in items.iter().rev() {
                    result = BackendSExprSyntax::cons(self, self.quote(item)?, result)?;
                }
                Ok(result)
            }
        }
    }

    fn render(&self, value: &Self::Value) -> Option<SExpr> {
        match BackendSExprView::view(self, value).ok()? {
            SExprF::Atom(payload) => self.render_payload(payload),
            SExprF::Nil => Some(SExp::List(Vec::new())),
            SExprF::Cons { .. } => {
                let mut items = Vec::new();
                let mut cursor = value.clone();
                loop {
                    match BackendSExprView::view(self, &cursor).ok()? {
                        SExprF::Nil => return Some(SExp::List(items)),
                        SExprF::Cons { head, tail } => {
                            items.push(self.render(&head)?);
                            cursor = tail;
                        }
                        SExprF::Atom(_) => return None,
                    }
                }
            }
        }
    }
}

/// A kernel-term S-expression carrier: the value algebra *plus* the proved
/// structural laws of the underlying carved theory.
///
/// Every method returning a [`Thm`] is pure delegation to theorems already
/// proved in `covalence-init` — implementations introduce no postulates and
/// no new trusted rules.
pub trait KernelSExpr:
    BackendSExprView<Payload = DatumPayload, Value = Term, Error = HolError>
{
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

/// An [`SExprView`](BackendSExprView)/[`KernelSExpr`] adapter over a carved
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
    quote_policy: DatumNumerals,
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
    /// policy stays [`DatumNumerals::Symbols`] — today's dialects quote
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
            quote_policy: DatumNumerals::Symbols,
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
            quote_policy: DatumNumerals::Integers,
            payload_layout: PayloadLayout::IntOrSymbol,
        })
    }

    /// Override the [`quote`](LispDatum::quote) numeral policy.
    pub fn with_quote_policy(mut self, policy: DatumNumerals) -> Self {
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
        match BackendSExprView::view(self, v).ok()? {
            SExprF::Atom(DatumPayload::Symbol(bytes)) => Some(bytes),
            _ => None,
        }
    }

    /// The integer of an `(int n)` backend-injected value (`None` when no
    /// backend is installed or `v` is not that shape).
    pub fn as_int_lit(&self, v: &Term) -> Option<Int> {
        self.int.as_deref()?.as_lit(v)
    }
}

impl BackendSExprSyntax for CarvedCarrier {
    type Payload = DatumPayload;
    type Value = Term;
    type Error = HolError;

    fn atom(&self, payload: Self::Payload) -> Result<Self::Value, Self::Error> {
        match payload {
            DatumPayload::Symbol(bytes) => {
                if self.payload_layout == PayloadLayout::IntOrSymbol {
                    let payload = defs::inr(Type::int(), Type::bytes())
                        .apply(mk_blob(bytes))
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
                    .apply(mk_blob(bytes))
                    .map_err(kernel_err)
            }
            DatumPayload::Integer(integer) => {
                if let Some(be) = self.int.as_deref() {
                    return be.lit(&integer);
                }
                if self.cs.payload == Type::int() {
                    return self
                        .cs
                        .atom
                        .clone()
                        .apply(mk_int(integer))
                        .map_err(kernel_err);
                }
                Err(HolError::Stuck(
                    "this dialect has no integer atoms (`sector`: numerals stay symbols)".into(),
                ))
            }
        }
    }

    fn nil(&self) -> Self::Value {
        self.cs.snil.clone()
    }

    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error> {
        self.cs
            .scons
            .clone()
            .apply(head)
            .map_err(kernel_err)?
            .apply(tail)
            .map_err(kernel_err)
    }
}

impl BackendSExprView for CarvedCarrier {
    fn view(&self, value: &Self::Value) -> Result<SExprF<Self::Payload, Self::Value>, Self::Error> {
        if *value == self.cs.snil {
            return Ok(SExprF::Nil);
        }
        if let Some((inner, tail)) = value.as_app()
            && let Some((operator, head)) = inner.as_app()
            && *operator == self.cs.scons
        {
            return Ok(SExprF::Cons {
                head: head.clone(),
                tail: tail.clone(),
            });
        }
        if let Some(integer) = self.as_int_lit(value) {
            return Ok(SExprF::Atom(DatumPayload::Integer(integer)));
        }
        let payload = self
            .as_atom_term(value)
            .ok_or_else(|| HolError::Stuck("term is not carved S-expression data".into()))?;
        if self.payload_layout == PayloadLayout::IntOrSymbol
            && let Some((injection, bytes)) = payload.as_app()
            && *injection == defs::inr(Type::int(), Type::bytes())
            && let Some(bytes) = as_blob(bytes)
        {
            return Ok(SExprF::Atom(DatumPayload::Symbol(bytes.to_vec())));
        }
        if self.cs.payload == Type::bytes()
            && let Some(bytes) = as_blob(&payload)
        {
            return Ok(SExprF::Atom(DatumPayload::Symbol(bytes.to_vec())));
        }
        if self.cs.payload == Type::int()
            && let Some(integer) = as_int(&payload)
        {
            return Ok(SExprF::Atom(DatumPayload::Integer(integer)));
        }
        Err(HolError::Stuck("unsupported carved atom payload".into()))
    }
}

impl LispDatum for CarvedCarrier {
    fn lower_atom(&self, atom: &covalence_sexp::Atom) -> Result<Term, HolError> {
        let payload = match atom {
            covalence_sexp::Atom::Symbol(symbol) => {
                if self.quote_policy == DatumNumerals::Integers
                    && let Ok(integer) = symbol.parse::<Int>()
                {
                    DatumPayload::Integer(integer)
                } else {
                    DatumPayload::Symbol(symbol.as_bytes().to_vec())
                }
            }
            covalence_sexp::Atom::Str { bytes, .. } => DatumPayload::Symbol(bytes.to_vec()),
        };
        BackendSExprSyntax::atom(self, payload)
    }

    fn render_payload(&self, payload: DatumPayload) -> Option<SExpr> {
        Some(match payload {
            DatumPayload::Integer(integer) => SExp::symbol(integer.to_string()),
            DatumPayload::Symbol(bytes) => match String::from_utf8(bytes) {
                Ok(symbol) => SExp::symbol(symbol),
                Err(error) => SExp::string("b", error.into_bytes()),
            },
        })
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
        if let Ok(SExprF::Cons { head: h, tail: t }) = BackendSExprView::view(self, v) {
            return self.cs.proj_scons(take_cdr, &h, &t).map_err(kernel_err);
        }
        if let Some(b) = self.as_atom_term(v) {
            return self
                .cs
                .proj_leaf(take_cdr, LeafKind::Atom(&b))
                .map_err(kernel_err);
        }
        if matches!(BackendSExprView::view(self, v), Ok(SExprF::Nil)) {
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

/// An [`SExprView`](BackendSExprView)/[`KernelSExpr`] adapter over the ACL2 carrier `A`.
///
/// Values follow the S1 conventions: integers are `aint i` (genuine payload
/// with the proved `init/int` theory behind it), symbols are `asym ⌜s⌝`,
/// `nil` is the leaf `anil`, and the canonical true value is the defined
/// constant `t` (= `asym "T"` by its defining equation), which
/// [`view`](BackendSExprView::view) observes as the symbol payload `"T"`.
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
    /// they observe via [`view`](BackendSExprView::view)).
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

impl BackendSExprSyntax for Acl2Carrier {
    type Payload = DatumPayload;
    type Value = Term;
    type Error = HolError;

    fn atom(&self, payload: Self::Payload) -> Result<Self::Value, Self::Error> {
        match payload {
            DatumPayload::Symbol(bytes) => {
                // Representation contract: never `asym "NIL"` — it would be
                // a junk value distinct from `anil`.
                if bytes.eq_ignore_ascii_case(b"nil") {
                    return Err(HolError::Stuck(
                        "ACL2 representation contract: `nil` is the leaf `anil`, never \
                         `asym \"NIL\"` — use `nil()`"
                            .into(),
                    ));
                }
                self.a.asym_lit(&bytes).map_err(kernel_err)
            }
            DatumPayload::Integer(integer) => self.a.aint_at(&mk_int(integer)).map_err(kernel_err),
        }
    }

    fn nil(&self) -> Self::Value {
        self.a.nil.clone()
    }

    fn cons(&self, head: Self::Value, tail: Self::Value) -> Result<Self::Value, Self::Error> {
        self.a
            .cons
            .clone()
            .apply(head)
            .map_err(kernel_err)?
            .apply(tail)
            .map_err(kernel_err)
    }
}

impl BackendSExprView for Acl2Carrier {
    fn view(&self, value: &Self::Value) -> Result<SExprF<Self::Payload, Self::Value>, Self::Error> {
        if *value == self.a.nil {
            return Ok(SExprF::Nil);
        }
        if let Some((inner, tail)) = value.as_app()
            && let Some((operator, head)) = inner.as_app()
            && *operator == self.a.cons
        {
            return Ok(SExprF::Cons {
                head: head.clone(),
                tail: tail.clone(),
            });
        }
        // The canonical `t` constant (= `asym "T"` by its defining equation).
        if *value == self.pr.t {
            return Ok(SExprF::Atom(DatumPayload::Symbol(b"T".to_vec())));
        }
        if let Some(integer) = self.as_aint_arg(value).and_then(|term| as_int(&term)) {
            return Ok(SExprF::Atom(DatumPayload::Integer(integer)));
        }
        if let Some(bytes) = self.as_asym_arg(value).and_then(|term| as_blob(&term)) {
            return Ok(SExprF::Atom(DatumPayload::Symbol(bytes.to_vec())));
        }
        // The raw datatype-constructor form `aatom (inl i | inr s)`.
        if let Some(l) = self.as_aatom_term(value)
            && let Some((f, x)) = l.as_app()
        {
            if *f == defs::inl(Type::int(), Type::bytes())
                && let Some(integer) = as_int(x)
            {
                return Ok(SExprF::Atom(DatumPayload::Integer(integer)));
            }
            if *f == defs::inr(Type::int(), Type::bytes())
                && let Some(bytes) = as_blob(x)
            {
                return Ok(SExprF::Atom(DatumPayload::Symbol(bytes.to_vec())));
            }
        }
        Err(HolError::Stuck("term is not ACL2 S-expression data".into()))
    }
}

impl LispDatum for Acl2Carrier {
    fn lower_atom(&self, atom: &covalence_sexp::Atom) -> Result<Term, HolError> {
        match atom {
            covalence_sexp::Atom::Symbol(symbol) => {
                if let Ok(integer) = symbol.parse::<Int>() {
                    return BackendSExprSyntax::atom(self, DatumPayload::Integer(integer));
                }
                if symbol.eq_ignore_ascii_case("nil") {
                    return Ok(BackendSExprSyntax::nil(self));
                }
                if symbol.eq_ignore_ascii_case("t") {
                    return Ok(self.t());
                }
                BackendSExprSyntax::atom(self, DatumPayload::Symbol(symbol.as_bytes().to_vec()))
            }
            covalence_sexp::Atom::Str { .. } => Err(HolError::Stuck(
                "ACL2 datum: string literals are not ACL2 objects".into(),
            )),
        }
    }

    fn render_payload(&self, payload: DatumPayload) -> Option<SExpr> {
        Some(match payload {
            DatumPayload::Integer(integer) => SExp::symbol(integer.to_string()),
            DatumPayload::Symbol(bytes) => match String::from_utf8(bytes) {
                Ok(symbol) => SExp::symbol(symbol),
                Err(error) => SExp::string("b", error.into_bytes()),
            },
        })
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
        if let Ok(SExprF::Cons { head: h, tail: t }) = BackendSExprView::view(self, v) {
            return self.a.cs.proj_scons(take_cdr, &h, &t).map_err(kernel_err);
        }
        if matches!(BackendSExprView::view(self, v), Ok(SExprF::Nil)) {
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

//! Python bindings for `covalence-pure`.
//!
//! Exposes `Type`, `Term`, `Thm` as pyclasses with smart constructors
//! and the LCF rule API.
//!
//! Observation handling is deferred: this MVP exposes the universal
//! subset (`NoObs`-style observations are not constructible from
//! Python). User code that wants observations can extend these
//! bindings with their own observer types via additional pyclasses.

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use covalence_core as cp;

fn err(e: cp::Error) -> PyErr {
    PyValueError::new_err(format!("{}", e))
}

// ============================================================================
// Type
// ============================================================================

#[pyclass(frozen, name = "Type", from_py_object)]
#[derive(Clone)]
pub struct PyType(pub cp::Type);

#[pymethods]
impl PyType {
    /// Type variable `'a`.
    #[staticmethod]
    fn tfree(name: &str) -> Self {
        PyType(cp::Type::tfree(name))
    }

    /// The kind of meta-propositions, `prop`.
    #[staticmethod]
    fn prop() -> Self {
        PyType(cp::Type::prop())
    }

    /// The type of blob literals.
    #[staticmethod]
    fn bytes() -> Self {
        PyType(cp::Type::bytes())
    }

    /// Canonical HOL `bool` type (the 0-ary `tycon("bool", [])`).
    #[staticmethod]
    fn bool() -> Self {
        PyType(cp::Type::bool())
    }

    /// Function type `τ ⇒ σ`.
    #[staticmethod]
    fn fun(dom: PyType, cod: PyType) -> Self {
        PyType(cp::Type::fun(dom.0, cod.0))
    }

    /// User-declared type constructor.
    #[staticmethod]
    fn tycon(name: &str, args: Vec<PyType>) -> Self {
        PyType(cp::Type::tycon(
            name,
            args.into_iter().map(|a| a.0).collect(),
        ))
    }

    /// Fresh-identity type constructor. Two calls — even with identical
    /// `hint` and `args` — produce **distinct** types (the freshness
    /// primitive `new_type_definition` uses internally). For Python
    /// callers, the only "observer" supported is `()` (unit); richer
    /// observers require Rust-side implementations.
    #[staticmethod]
    fn tycon_obs(hint: &str, args: Vec<PyType>) -> Self {
        PyType(cp::Type::tycon_obs(
            (),
            hint,
            args.into_iter().map(|a| a.0).collect(),
        ))
    }

    fn is_prop(&self) -> bool {
        self.0.is_prop()
    }

    fn __repr__(&self) -> String {
        format!("Type({})", self.0)
    }
    fn __str__(&self) -> String {
        format!("{}", self.0)
    }
    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }
    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        self.0.hash(&mut h);
        h.finish()
    }
}

// ============================================================================
// Term
// ============================================================================

#[pyclass(frozen, name = "Term", from_py_object)]
#[derive(Clone)]
pub struct PyTerm(pub cp::Term);

#[pymethods]
impl PyTerm {
    /// de Bruijn–indexed bound variable.
    #[staticmethod]
    fn bound(idx: u32) -> Self {
        PyTerm(cp::Term::bound(idx))
    }

    /// Free variable with declared type.
    #[staticmethod]
    fn free(name: &str, ty: PyType) -> Self {
        PyTerm(cp::Term::free(name, ty.0))
    }

    /// Declared/defined constant with instance type.
    #[staticmethod]
    #[pyo3(name = "const_")]
    fn const_(name: &str, ty: PyType) -> Self {
        PyTerm(cp::Term::const_(name, ty.0))
    }

    /// Application `f x`.
    #[staticmethod]
    fn app(fun: PyTerm, arg: PyTerm) -> Self {
        PyTerm(cp::Term::app(fun.0, arg.0))
    }

    /// Abstraction `λx:τ. body`.
    #[staticmethod]
    fn abs(hint: &str, ty: PyType, body: PyTerm) -> Self {
        PyTerm(cp::Term::abs(hint, ty.0, body.0))
    }

    /// Meta-implication `φ ⟹ ψ`.
    #[staticmethod]
    fn imp(lhs: PyTerm, rhs: PyTerm) -> Self {
        PyTerm(cp::Term::imp(lhs.0, rhs.0))
    }

    /// Meta-universal `⋀x:τ. body`.
    #[staticmethod]
    fn all(hint: &str, ty: PyType, body: PyTerm) -> Self {
        PyTerm(cp::Term::all(hint, ty.0, body.0))
    }

    /// Meta-equality `t ≡ u`.
    #[staticmethod]
    fn eq(lhs: PyTerm, rhs: PyTerm) -> Self {
        PyTerm(cp::Term::eq(lhs.0, rhs.0))
    }

    /// Built-in byte literal.
    #[staticmethod]
    fn blob(bytes: &[u8]) -> Self {
        PyTerm(cp::Term::blob(bytes::Bytes::copy_from_slice(bytes)))
    }

    /// Compute the type.
    fn type_of(&self) -> PyResult<PyType> {
        self.0.type_of().map(PyType).map_err(err)
    }

    /// True iff no Obs leaf appears anywhere in this term.
    fn has_no_obs(&self) -> bool {
        self.0.has_no_obs()
    }

    fn __repr__(&self) -> String {
        format!("Term({})", self.0)
    }
    fn __str__(&self) -> String {
        format!("{}", self.0)
    }
    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }
    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        self.0.hash(&mut h);
        h.finish()
    }
}

// ============================================================================
// Thm
// ============================================================================

#[pyclass(frozen, name = "Thm", from_py_object)]
#[derive(Clone)]
pub struct PyThm(pub cp::Thm);

#[pymethods]
impl PyThm {
    // ---- LF rules ----

    /// `{φ} ⊢ φ`.
    #[staticmethod]
    fn assume(phi: PyTerm) -> PyResult<Self> {
        cp::Thm::assume(phi.0).map(PyThm).map_err(err)
    }

    /// `Γ \ {φ} ⊢ φ ⟹ ψ`.
    fn imp_intro(&self, phi: &PyTerm) -> PyResult<Self> {
        self.0.clone().imp_intro(&phi.0).map(PyThm).map_err(err)
    }

    /// `Γ ∪ Γ' ⊢ ψ`.
    fn imp_elim(&self, hyp: &PyThm) -> PyResult<Self> {
        self.0
            .clone()
            .imp_elim(hyp.0.clone())
            .map(PyThm)
            .map_err(err)
    }

    /// `Γ ⊢ ⋀x:τ. φ`.
    fn all_intro(&self, name: &str, ty: PyType) -> PyResult<Self> {
        self.0.clone().all_intro(name, ty.0).map(PyThm).map_err(err)
    }

    /// `Γ ⊢ φ[t/0]`.
    fn all_elim(&self, witness: PyTerm) -> PyResult<Self> {
        self.0.clone().all_elim(witness.0).map(PyThm).map_err(err)
    }

    // ---- Equality rules ----

    /// `⊢ t ≡ t`.
    #[staticmethod]
    fn refl(t: PyTerm) -> PyResult<Self> {
        cp::Thm::refl(t.0).map(PyThm).map_err(err)
    }

    /// `Γ ∪ Γ' ⊢ t ≡ v`.
    fn trans(&self, other: &PyThm) -> PyResult<Self> {
        self.0
            .clone()
            .trans(other.0.clone())
            .map(PyThm)
            .map_err(err)
    }

    /// `Γ ⊢ u ≡ t`.
    fn sym(&self) -> PyResult<Self> {
        self.0.clone().sym().map(PyThm).map_err(err)
    }

    /// `Γ ∪ Γ' ⊢ f(s) ≡ g(t)`.
    fn cong_app(&self, arg: &PyThm) -> PyResult<Self> {
        self.0
            .clone()
            .cong_app(arg.0.clone())
            .map(PyThm)
            .map_err(err)
    }

    /// `Γ ⊢ (λy:τ. s) ≡ (λy:τ. t)`.
    fn cong_abs(&self, name: &str, ty: PyType) -> PyResult<Self> {
        self.0.clone().cong_abs(name, ty.0).map(PyThm).map_err(err)
    }

    /// Introduce a fresh defined constant: `⊢ Def(name, body) ≡ body`.
    /// Each call allocates a fresh `Def`, so two `define` calls with
    /// the same name produce distinct kernel constants.
    #[staticmethod]
    fn define(name: &str, body: PyTerm) -> PyResult<Self> {
        cp::Thm::define(name, body.0).map(PyThm).map_err(err)
    }

    /// `⊢ (λx:τ. body) arg ≡ body[arg/0]`.
    #[staticmethod]
    fn beta_conv(app: PyTerm) -> PyResult<Self> {
        cp::Thm::beta_conv(app.0).map(PyThm).map_err(err)
    }

    /// `⊢ (λx:τ. f x) ≡ f`.
    #[staticmethod]
    fn eta_conv(abs: PyTerm) -> PyResult<Self> {
        cp::Thm::eta_conv(abs.0).map(PyThm).map_err(err)
    }

    /// `Γ[α:=σ] ⊢ φ[α:=σ]`.
    fn inst_tfree(&self, name: &str, replacement: PyType) -> PyResult<Self> {
        self.0
            .clone()
            .inst_tfree(name, replacement.0)
            .map(PyThm)
            .map_err(err)
    }

    /// Introduce a fresh subtype τ ≤ α witnessed by the predicate `P`
    /// from the conclusion of `witness`. Returns a `TypeDef` bundle
    /// containing τ, the abs/rep constants, and three bijection
    /// theorems.
    #[staticmethod]
    fn new_type_definition(
        hint: &str,
        abs_hint: &str,
        rep_hint: &str,
        witness: &PyThm,
    ) -> PyResult<PyTypeDef> {
        cp::Thm::new_type_definition(hint, abs_hint, rep_hint, witness.0.clone())
            .map(PyTypeDef)
            .map_err(err)
    }

    // ---- Accessors ----

    /// Hypotheses (a tuple of terms, in BTreeSet order).
    fn hyps(&self) -> Vec<PyTerm> {
        self.0.hyps().iter().cloned().map(PyTerm).collect()
    }

    /// Conclusion.
    fn concl(&self) -> PyTerm {
        PyTerm(self.0.concl().clone())
    }

    /// True iff no Obs leaf appears in concl or any hyp.
    fn has_no_obs(&self) -> bool {
        self.0.has_no_obs()
    }

    fn __repr__(&self) -> String {
        format!("Thm({})", self.0)
    }
    fn __str__(&self) -> String {
        format!("{}", self.0)
    }
}

// ============================================================================
// TypeDef
// ============================================================================

#[pyclass(frozen, name = "TypeDef", from_py_object)]
#[derive(Clone)]
pub struct PyTypeDef(pub cp::TypeDef);

#[pymethods]
impl PyTypeDef {
    /// The freshly-introduced type τ.
    #[getter]
    fn tau(&self) -> PyType {
        PyType(self.0.tau.clone())
    }

    /// `abs : α → τ` — the fresh injection constant.
    #[getter]
    #[pyo3(name = "abs_")]
    fn abs_(&self) -> PyTerm {
        PyTerm(self.0.abs.clone())
    }

    /// `rep : τ → α` — the fresh projection constant.
    #[getter]
    fn rep(&self) -> PyTerm {
        PyTerm(self.0.rep.clone())
    }

    /// `⊢ ⋀a:τ. abs (rep a) ≡ a`.
    #[getter]
    fn abs_rep(&self) -> PyThm {
        PyThm(self.0.abs_rep.clone())
    }

    /// `⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r`.
    #[getter]
    fn rep_abs_fwd(&self) -> PyThm {
        PyThm(self.0.rep_abs_fwd.clone())
    }

    /// `⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r`.
    #[getter]
    fn rep_abs_back(&self) -> PyThm {
        PyThm(self.0.rep_abs_back.clone())
    }

    /// Sorted list of type-variable names α is parametric in. τ's
    /// arity equals `len(tvars)`.
    #[getter]
    fn tvars(&self) -> Vec<String> {
        self.0.tvars.iter().map(|s| s.to_string()).collect()
    }

    fn __repr__(&self) -> String {
        format!("TypeDef(tau={}, tvars={:?})", self.0.tau, self.tvars())
    }
}

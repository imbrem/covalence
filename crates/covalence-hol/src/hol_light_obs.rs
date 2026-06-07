//! HOL Light bootstrap on top of `covalence-pure`.
//!
//! ## What this module is
//!
//! A single Rust `enum` ([`HolLight`]) that carries every HOL Light
//! primitive — `bool`, `=`, `T`, `F`, `⟹`, `¬`, `∧`, `∨`, `↔`, `∀`,
//! `∃`, `ε`, plus `Trueprop` — as variants of one observer family.
//! Plus the polymorphic `eq_reflection` axiom that bridges HOL
//! bool-equality to Pure meta-equality. That's it.
//!
//! All observers and the `eq_reflection` axiom are process-global
//! lazy statics. [`HolLightCtx`] is a zero-sized handle over them —
//! constructing one is free.
//!
//! ## Mapping to Isabelle/HOL
//!
//! `covalence-pure` plays the role of Isabelle/Pure: the meta-logic
//! with `prop`, meta-`⋀`, meta-`⟹`, meta-`≡`, plus the standard
//! inference rules (`assume`, `imp_intro/elim`, `all_intro/elim`,
//! `refl`/`trans`/`sym`, `cong_app`/`cong_abs`, `beta_conv`,
//! `eta_conv`, `eq_mp`, `inst_tfree`).
//!
//! `covalence-hol` plays the role of Isabelle/HOL: HOL as a *theory*
//! built on top of the meta-logic. Standard Isabelle/HOL ships with:
//!
//! - `bool` as a separate type (we encode it as `TyConObs(Bool_obs, "bool", [])`).
//! - `Trueprop : bool ⇒ prop` as the explicit coercion (our [`HolLight::Trueprop`]).
//! - HOL `=` as a constant at `'a ⇒ 'a ⇒ bool` (our [`HolLight::Eq`]).
//! - One bridge axiom — `eq_reflection : (x = y) ⟹ (x ≡ y)` — that
//!   we mirror exactly in [`HolLightCtx::eq_reflection_axiom`].
//!
//! From the `eq_reflection` axiom plus Pure's primitives, every HOL
//! Light rule derives the way Isabelle does it. The audit-trail
//! discipline matches HOL Light's: any HOL theorem that relies on
//! `eq_reflection` carries it in the hypothesis set.
//!
//! ## Tarski-T encoding
//!
//! HOL judgements live in Pure as `⊢_Pure Trueprop p`. A HOL theorem
//! `Γ ⊢_HOL p` (with `p : bool` and each `h ∈ Γ : bool`) is the Pure
//! theorem
//!
//! ```text
//! {eq_reflection, ETA, SELECT, INFINITY, …} ∪ {Trueprop h | h ∈ Γ}
//!     ⊢_Pure Trueprop p
//! ```
//!
//! Pure's hypothesis set carries every axiom the conclusion depends
//! on (eq_reflection plus whichever standard HOL axioms apply) and
//! the HOL hypotheses lifted through Trueprop.
//!
//! ## The 10 HOL Light rules
//!
//! Status: all 10 derive via `eq_reflection` plus Pure's primitives.
//! The (forthcoming) `PureHol` kernel adapter wires each one up.
//!
//! | HOL Light rule    | Derived from                        |
//! |-------------------|-------------------------------------|
//! | REFL              | Pure `refl` + eq_reflection (bwd)   |
//! | TRANS             | eq_reflection (fwd) + Pure `trans` + eq_reflection (bwd) |
//! | MK_COMB           | eq_reflection (fwd) + Pure `cong_app` + eq_reflection (bwd) |
//! | ABS               | eq_reflection (fwd) + Pure `cong_abs` (checks "x not free in hyps") + eq_reflection (bwd) |
//! | BETA              | Pure `beta_conv` + eq_reflection (bwd) |
//! | ASSUME            | Pure `assume` on `Trueprop p` directly |
//! | EQ_MP at bool     | eq_reflection (fwd) + Pure `eq_mp` |
//! | DEDUCT_ANTISYM    | Pure `imp_intro` + iff_def (defined HOL constant) |
//! | INST              | Pure `all_intro` (checks "x not free in hyps") + `all_elim` |
//! | INST_TYPE         | Pure `inst_tfree` directly          |
//!
//! Pure's primitives already enforce the hypothesis-side-conditions
//! the conditioned HOL Light rules require (ABS, INST), and apply
//! substitutions uniformly across the hypothesis set (INST, INST_TYPE).
//! There's no soundness gap to engineer around.
//!
//! ## Why we don't use the "axiomless" approach
//!
//! An earlier version of this module attempted to avoid the
//! eq_reflection axiom by recognising HOL-Light-derivable shapes
//! directly in the [`covalence_pure::ObsTrue`] and
//! [`covalence_pure::ObsImp`] policies. The pattern looked appealing
//! — fewer hypotheses, no axiom to thread through — but the analysis
//! showed that ABS and INST cannot soundly fit. The pattern was
//! removed. See the project's `audit` commit for the analysis.

use std::fmt;
use std::sync::LazyLock;

use covalence_pure::{Object, Observer, Term, TermKind, Thm, Type};

// ============================================================================
// Process-global lazy statics
// ============================================================================
//
// One `Object` per HolLight variant, allocated on first access and reused
// for the whole process. [`HolLightCtx`] is a zero-sized handle on these
// globals — every `HolLightCtx` produces the same theory (the HOL Light
// theory, of which there is exactly one).

static BOOL_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Bool));
static EQ_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Eq));
static TRUE_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::True));
static FALSE_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::False));
static IMP_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Imp));
static NOT_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Not));
static AND_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::And));
static OR_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Or));
static IFF_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Iff));
static FORALL_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Forall));
static EXISTS_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Exists));
static SELECT_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Select));
static TRUEPROP_OBS: LazyLock<Object> = LazyLock::new(|| Object::new(HolLight::Trueprop));

/// `⋀x y : 'a. Trueprop (Eq x y) ≡ (x ≡ y)` — the polymorphic
/// `eq_reflection` axiom. Built lazily once via `Thm::assume`, reused
/// process-wide. See [`HolLightCtx::eq_reflection_axiom`].
static EQ_REFLECTION_AXIOM: LazyLock<Thm> = LazyLock::new(build_eq_reflection_axiom);

// ============================================================================
// The HolLight observer family
// ============================================================================

/// The HOL Light observer family. One Rust variant per HOL primitive.
/// Every variant lives behind a process-global `Object` (see the
/// `*_OBS` lazy statics above), so every use of e.g. HOL `=` through
/// [`HolLightCtx`] shares one Arc identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HolLight {
    // -- Type constructor --
    /// HOL `bool` — type of truth values. Distinct from Pure `prop`.
    Bool,

    // -- Equality --
    /// HOL `=` at polymorphic type `'a → 'a → bool`. The instance
    /// type is carried as the term's `Type` field.
    Eq,

    // -- Truth values --
    /// HOL `T : bool`.
    True,
    /// HOL `F : bool`.
    False,

    // -- Connectives --
    /// `⟹` (implication) at `bool → bool → bool`.
    Imp,
    /// `¬` (negation) at `bool → bool`.
    Not,
    /// `∧` (conjunction) at `bool → bool → bool`.
    And,
    /// `∨` (disjunction) at `bool → bool → bool`.
    Or,
    /// `⟺` (iff) at `bool → bool → bool`. Coincides with `Eq` at bool
    /// in the standard model; exposed separately as a distinct
    /// observer to match HOL Light's naming.
    Iff,

    // -- Quantifiers --
    /// `∀` at `('a → bool) → bool`.
    Forall,
    /// `∃` at `('a → bool) → bool`.
    Exists,
    /// `ε` (Hilbert's choice) at `('a → bool) → 'a`.
    Select,

    /// `Trueprop : bool → prop` — explicit coercion from HOL bool to
    /// Pure prop. A HOL theorem `⊢_HOL p` is the Pure theorem
    /// `⊢_Pure Trueprop p`. Mirrors Isabelle/HOL's `Trueprop`.
    Trueprop,
}

impl HolLight {
    /// Human-readable label used in display output. Matches HOL Light's
    /// printable surface forms (`=`, `==>`, `~`, `/\`, `\/`, `<=>`,
    /// `!`, `?`, `@`, `T`, `F`, `bool`).
    pub fn label(&self) -> &'static str {
        match self {
            HolLight::Bool => "bool",
            HolLight::Eq => "=",
            HolLight::True => "T",
            HolLight::False => "F",
            HolLight::Imp => "==>",
            HolLight::Not => "~",
            HolLight::And => "/\\",
            HolLight::Or => "\\/",
            HolLight::Iff => "<=>",
            HolLight::Forall => "!",
            HolLight::Exists => "?",
            HolLight::Select => "@",
            HolLight::Trueprop => "Trueprop",
        }
    }
}

impl fmt::Display for HolLight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

// ============================================================================
// HolLightCtx — zero-sized handle on the process-global HOL primitives
// ============================================================================

/// Zero-sized handle on the process-global HOL Light primitives.
/// Constructing one is free — there are no fields. Methods delegate
/// to the module-level `LazyLock` statics. Two `HolLightCtx` values
/// are interchangeable.
#[derive(Clone, Copy, Debug, Default)]
pub struct HolLightCtx;

impl HolLightCtx {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }

    // ---- HOL types ----

    /// HOL `bool` — `TyConObs(bool_obs, "bool", [])` over the global
    /// `BOOL_OBS`. Distinct from Pure `prop`.
    pub fn bool_type(&self) -> Type {
        Type::tycon_obs_from_dyn((*BOOL_OBS).clone(), "bool", vec![])
    }

    /// Pure function type α → β. HOL doesn't add a new function-type
    /// constructor; we re-use Pure's `Fun`.
    pub fn fun_type(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    // ---- HOL constants ----

    /// Construct a `Term::obs` at the given type over the given
    /// global observer. Used by every constant accessor below.
    fn obs_term(observer: &Object, ty: Type) -> Term {
        Term::obs_from_dyn(observer.clone(), ty)
    }

    /// HOL `=` instantiated at `α → α → bool`.
    pub fn eq_at(&self, alpha: Type) -> Term {
        let ty = Type::fun(alpha.clone(), Type::fun(alpha, self.bool_type()));
        Self::obs_term(&EQ_OBS, ty)
    }

    /// `t = u : bool`, given `t` and `u` of the same type α. Errors
    /// if `t` is ill-typed.
    pub fn mk_eq(&self, lhs: Term, rhs: Term) -> Result<Term, covalence_pure::Error> {
        let alpha = lhs.type_of()?;
        let eq = self.eq_at(alpha);
        Ok(Term::app(Term::app(eq, lhs), rhs))
    }

    /// HOL `T : bool`.
    pub fn t(&self) -> Term {
        Self::obs_term(&TRUE_OBS, self.bool_type())
    }

    /// HOL `F : bool`.
    pub fn f(&self) -> Term {
        Self::obs_term(&FALSE_OBS, self.bool_type())
    }

    /// HOL `==>` at `bool → bool → bool`.
    pub fn imp_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&IMP_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p ==> q`.
    pub fn mk_imp(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.imp_op(), p), q)
    }

    /// HOL `~` at `bool → bool`.
    pub fn not_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&NOT_OBS, Type::fun(b.clone(), b))
    }
    /// HOL `~ p`.
    pub fn mk_not(&self, p: Term) -> Term {
        Term::app(self.not_op(), p)
    }

    /// HOL `/\` at `bool → bool → bool`.
    pub fn and_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&AND_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p /\ q`.
    pub fn mk_and(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.and_op(), p), q)
    }

    /// HOL `\/` at `bool → bool → bool`.
    pub fn or_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&OR_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p \/ q`.
    pub fn mk_or(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.or_op(), p), q)
    }

    /// HOL `<=>` at `bool → bool → bool`.
    pub fn iff_op(&self) -> Term {
        let b = self.bool_type();
        Self::obs_term(&IFF_OBS, Type::fun(b.clone(), Type::fun(b.clone(), b)))
    }
    /// HOL `p <=> q`.
    pub fn mk_iff(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.iff_op(), p), q)
    }

    /// HOL `∀` at `(α → bool) → bool`.
    pub fn forall_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Self::obs_term(&FORALL_OBS, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∀x:α. body` — `Forall (λx:α. body)`.
    pub fn mk_forall(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.forall_at(alpha), lambda)
    }

    /// HOL `∃` at `(α → bool) → bool`.
    pub fn exists_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Self::obs_term(&EXISTS_OBS, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∃x:α. body` — `Exists (λx:α. body)`.
    pub fn mk_exists(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.exists_at(alpha), lambda)
    }

    /// HOL `ε` (Hilbert's choice) at `(α → bool) → α`.
    pub fn select_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha.clone(), self.bool_type());
        Self::obs_term(&SELECT_OBS, Type::fun(pred, alpha))
    }
    /// HOL `ε x:α. body` — `Select (λx:α. body)`.
    pub fn mk_select(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.select_at(alpha), lambda)
    }

    // ---- Trueprop coercion ----

    /// HOL `Trueprop` at type `bool → prop` — the explicit coercion
    /// from HOL bool to Pure prop. A HOL theorem `⊢_HOL p` becomes
    /// the Pure theorem `⊢_Pure Trueprop p`.
    pub fn trueprop(&self) -> Term {
        Self::obs_term(&TRUEPROP_OBS, Type::fun(self.bool_type(), Type::prop()))
    }

    /// `Trueprop p` — wrap a HOL bool term as a Pure prop. Errors if
    /// `p` is not bool-typed.
    pub fn mk_trueprop(&self, p: Term) -> Result<Term, covalence_pure::Error> {
        let p_ty = p.type_of()?;
        if p_ty != self.bool_type() {
            return Err(covalence_pure::Error::TypeMismatch {
                expected: self.bool_type(),
                got: p_ty,
            });
        }
        Ok(Term::app(self.trueprop(), p))
    }

    // ---- Identity check helpers ----

    fn term_obs_ptr_id(t: &Term) -> Option<usize> {
        match t.kind() {
            TermKind::Obs(o, _) => Some(o.ptr_id()),
            _ => None,
        }
    }

    /// `true` iff `t` is the HOL `True` observer (Arc identity).
    pub fn is_true(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(TRUE_OBS.ptr_id())
    }

    /// `true` iff `t` is the HOL `False` observer.
    pub fn is_false(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(FALSE_OBS.ptr_id())
    }

    /// `true` iff `t` is the HOL `Trueprop` observer.
    pub fn is_trueprop(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(TRUEPROP_OBS.ptr_id())
    }

    /// Pointer-id of the `Eq` observer — useful for inspection or
    /// cross-process equality checks.
    pub fn eq_obs_ptr_id(&self) -> usize {
        EQ_OBS.ptr_id()
    }

    /// Pointer-id of the `Trueprop` observer.
    pub fn trueprop_obs_ptr_id(&self) -> usize {
        TRUEPROP_OBS.ptr_id()
    }

    // ========================================================================
    // The eq_reflection axiom (Isabelle/HOL bridge)
    // ========================================================================

    /// The polymorphic `eq_reflection` axiom — the bridge between HOL
    /// bool-equality (`Eq`) and Pure meta-equality (`≡`):
    ///
    /// ```text
    /// ⋀x y : 'a. Trueprop (Eq x y) ≡ (x ≡ y)
    /// ```
    ///
    /// Same axiom name and shape Isabelle/HOL ships. From this axiom
    /// plus Pure's existing primitives (`refl`, `trans`, `sym`,
    /// `cong_app`, `cong_abs`, `beta_conv`, `eq_mp`, `assume`,
    /// `imp_intro`, `imp_elim`, `all_intro`, `all_elim`, `inst_tfree`)
    /// you can derive every HOL Light rule.
    ///
    /// ## Use pattern
    ///
    /// This is a [`Thm::assume`] axiom — it has itself as a single
    /// hypothesis, and every theorem derived from it carries that
    /// hypothesis. Like ETA / SELECT / INFINITY in HOL Light, the
    /// axiom-as-hypothesis is the audit trail.
    ///
    /// To instantiate at a specific type α:
    ///
    /// ```ignore
    /// let axiom = ctx.eq_reflection_axiom();
    /// let axiom_at_bool = axiom.inst_tfree("a", ctx.bool_type())?;
    /// ```
    ///
    /// Forward direction (HOL `=` → Pure `≡`):
    ///
    /// ```text
    /// axiom_at_bool                                  // ⊢ ⋀x y. Trueprop (Eq x y) ≡ (x ≡ y)
    ///     .all_elim(a)?                              // ⊢ ⋀y. Trueprop (Eq a y) ≡ (a ≡ y)
    ///     .all_elim(b)?                              // ⊢ Trueprop (Eq a b) ≡ (a ≡ b)
    ///     .eq_mp(source_thm)?                        // ⊢ a ≡ b   (given source: ⊢ Trueprop (Eq a b))
    /// ```
    ///
    /// Backward direction (Pure `≡` → HOL `=`):
    ///
    /// ```text
    /// axiom_at_bool.all_elim(a)?.all_elim(b)?        // ⊢ Trueprop (Eq a b) ≡ (a ≡ b)
    ///     .sym()?                                    // ⊢ (a ≡ b) ≡ Trueprop (Eq a b)
    ///     .eq_mp(meta_eq_thm)?                       // ⊢ Trueprop (Eq a b)
    /// ```
    pub fn eq_reflection_axiom(&self) -> Thm {
        (*EQ_REFLECTION_AXIOM).clone()
    }
}

/// Build `eq_reflection` — called once, lazily, by the
/// `EQ_REFLECTION_AXIOM` static initialiser.
fn build_eq_reflection_axiom() -> Thm {
    let ctx = HolLightCtx;
    let alpha = Type::tfree("a");
    // Inside two ⋀-binders: x = Bound(1), y = Bound(0) (both : 'a).
    let x = Term::bound(1);
    let y = Term::bound(0);
    // HOL: x = y  (at 'a, returns bool)
    let eq_at_alpha = ctx.eq_at(alpha.clone());
    let hol_eq_x_y = Term::app(Term::app(eq_at_alpha, x.clone()), y.clone());
    // Trueprop (x = y)  (returns prop)
    let trueprop_hol_eq = Term::app(ctx.trueprop(), hol_eq_x_y);
    // Pure: x ≡ y  (at 'a, returns prop)
    let pure_eq_x_y = Term::eq(x, y);
    // Trueprop (Eq x y) ≡ (x ≡ y)  (meta-eq between two props, returns prop)
    let body = Term::eq(trueprop_hol_eq, pure_eq_x_y);
    // Wrap in two ⋀-binders.
    let inner = Term::all("y", alpha.clone(), body);
    let outer = Term::all("x", alpha, inner);
    Thm::assume(outer).expect("eq_reflection_axiom: well-typed by construction")
}

/// Marker trait certifying that an observer is in the [`HolLight`]
/// family. Useful as a generic bound when threading HOL-specific
/// reasoning through code that's parametric over observer types.
pub trait IsHolLight: Observer {}
impl IsHolLight for HolLight {}

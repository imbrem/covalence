//! HOL Light observer family.
//!
//! `HolLight` is the single Rust observer type that backs every HOL
//! Light primitive — `bool`, `=`, `T`, `F`, `⟹`, `¬`, `∧`, `∨`, `↔`,
//! `∀`, `∃`, `ε`. Because they all share one Rust type, they share
//! one parametric-ε family, and `Thm::obs_eq` can relate them. This
//! is the unifying piece of the bootstrap: the kernel uses
//! `TypeKind::TyConObs` on the type side and `TermKind::Obs` on the
//! term side, and a single `HolLight` observer is the head of both.
//!
//! ## Cross-process identity
//!
//! Pure compares observers by `Arc` pointer identity, not by user
//! `Eq`. That means two independently-constructed `HolLight::Eq`
//! values are *not* the same observation. To make the HOL Light
//! API consistent — e.g., `mk_eq` should always produce the same
//! `=` head — we maintain a single `Arc` for each [`HolLight`]
//! variant inside a [`HolLightCtx`]. Cloning out of the context
//! preserves the `Arc` so users get stable identities across all
//! calls into the same `PureHol` kernel.
//!
//! ## What ObsEq does for HolLight
//!
//! The ObsEq policy is **conservative** by default — see the impl
//! for the precise rules. Only the kernel-derivable refl-style
//! facts are returned `true`:
//!
//! - `Eq a a ≡ True_bool` (refl at the HOL level)
//! - `Eq u v ≡ Eq v u` (sym)
//!
//! The harder identities (e.g., `T ≡ Eq F F`, definitional unfoldings,
//! axiom-conditioned facts) are *not* in the ObsEq impl. They're
//! derived from user-asserted axioms or `Thm::define`.

use std::any::Any;
use std::fmt;
use std::sync::LazyLock;

use covalence_pure::{ObsEq, ObsImp, ObsTrue, Object, Observer, Term, TermKind, Type, subst};

// ============================================================================
// Typed hints for HOL Light rules that take parameters
// ============================================================================

/// Hint for HOL Light's INST rule: substitutes the named term
/// variables in the source theorem. Each pair is `(var_name, replacement_term)`.
#[derive(Debug)]
pub struct InstHint {
    pub subs: Vec<(String, Term)>,
}

/// Hint for HOL Light's INST_TYPE rule: substitutes the named type
/// variables. Each pair is `(tvar_name, replacement_type)`.
#[derive(Debug)]
pub struct InstTypeHint {
    pub subs: Vec<(String, Type)>,
}

// ============================================================================
// Module-level lazy globals
// ============================================================================
//
// One `Object` per HolLight variant, allocated lazily at first access and
// reused process-wide. `HolLightCtx` is a zero-sized handle on these
// globals — constructing one is free.

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

// ============================================================================
// The HolLight observer family
// ============================================================================

/// The HOL Light observer family. One Rust type per HOL primitive,
/// distinguished by variant — all share the same ε-family so
/// `obs_eq` can relate them.
///
/// **Identity discipline.** Two independently constructed
/// `HolLight::Eq` values have *different* `Arc` identities (Pure
/// compares observers by Arc pointer). The kernel's [`HolLightCtx`]
/// owns one `Arc<HolLight>` per variant and hands clones out, so
/// every use of HOL `=` (via `HolLightCtx::eq()`) shares the same
/// identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HolLight {
    // -- Type constructors --
    /// HOL's `bool` — the type of truth values. Distinct from Pure's
    /// `prop` (which is the meta-kind).
    Bool,

    // -- Equality --
    /// HOL's `=` at polymorphic type `'a → 'a → bool`. The instance
    /// type is carried as the term's `Type` field.
    Eq,

    // -- Truth values --
    /// HOL's `T : bool`.
    True,
    /// HOL's `F : bool`.
    False,

    // -- Connectives (all `bool → bool → bool` except `Not : bool → bool`) --
    /// HOL's `==>` (implication).
    Imp,
    /// HOL's `~` (negation).
    Not,
    /// HOL's `/\` (conjunction).
    And,
    /// HOL's `\/` (disjunction).
    Or,
    /// HOL's `<=>` (iff). At type `bool → bool → bool`, this is `Eq`
    /// instantiated, but exposed as a separate name in HOL Light.
    Iff,

    // -- Quantifiers (`('a → bool) → bool` for forall/exists,
    //    `('a → bool) → 'a` for select) --
    /// HOL's `!` (universal).
    Forall,
    /// HOL's `?` (existential).
    Exists,
    /// HOL's `@` (Hilbert's ε / choice).
    Select,

    /// `Trueprop : bool → prop` — explicit coercion from HOL bool to
    /// Pure prop. A HOL theorem `⊢_HOL p` (p : bool) is internally
    /// the Pure theorem `⊢_Pure Trueprop p`. Mirrors Isabelle/HOL's
    /// `Trueprop`. This is what `Thm::obs_true::<HolLight>` produces.
    Trueprop,
}

impl HolLight {
    /// Human-readable label for display purposes.
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
// ObsEq policy
// ============================================================================

/// `obs_eq` policy for HolLight. **Soundness does not depend on this
/// impl** — Pure's parametric-ε model makes any policy sound. The
/// impl here returns `true` only for cases the kernel can derive
/// directly:
///
/// - `Eq a a ≡ True` (HOL refl at bool, structural a)
/// - `Eq u v ≡ Eq v u` (HOL sym at bool)
///
/// Everything else returns `false` — including definitional facts
/// like `T ≡ (λp:bool. p) = (λp:bool. p)`. Those need to come from
/// `Thm::define` or user-asserted axioms.
impl ObsEq for HolLight {
    fn obs_eq(
        &self,
        other: &Self,
        my_args: &[Term],
        other_args: &[Term],
        _hint: Option<&dyn covalence_pure::Hint>,
    ) -> bool {
        match (self, other) {
            // Eq a a ≡ True_bool  (HOL refl at bool, when arg structure matches)
            (HolLight::Eq, HolLight::True)
                if my_args.len() == 2 && other_args.is_empty() =>
            {
                my_args[0] == my_args[1]
            }
            (HolLight::True, HolLight::Eq)
                if my_args.is_empty() && other_args.len() == 2 =>
            {
                other_args[0] == other_args[1]
            }
            // Eq u v ≡ Eq v u  (HOL sym at bool)
            (HolLight::Eq, HolLight::Eq) if my_args.len() == 2 && other_args.len() == 2 => {
                my_args[0] == other_args[1] && my_args[1] == other_args[0]
            }
            _ => false,
        }
    }
}

// ============================================================================
// HolLightCtx — shared-identity context for HOL primitives
// ============================================================================

/// Caches one [`Object`] per [`HolLight`] variant so that every use
/// of e.g. HOL `=` through this context shares the same Arc identity.
///
/// Without this, two `mk_eq` calls would construct fresh `Object`
/// values with distinct Arcs, and the resulting `Term`s would not
/// compare equal even with the same arguments. `HolLightCtx::eq()`
/// always returns a `Term::obs` over the cached observer.
pub struct HolLightCtx {
    bool_obs: Object,
    eq_obs: Object,
    true_obs: Object,
    false_obs: Object,
    imp_obs: Object,
    not_obs: Object,
    and_obs: Object,
    or_obs: Object,
    iff_obs: Object,
    forall_obs: Object,
    exists_obs: Object,
    select_obs: Object,
}

impl HolLightCtx {
    /// Allocate one fresh `Object` per variant. Each `HolLightCtx`
    /// has *its own* set of HOL primitives — two contexts produce
    /// distinct HOL theories (with their own equalities, booleans,
    /// etc.). For a shared HOL theory across the whole process, use
    /// a single context.
    pub fn new() -> Self {
        Self {
            bool_obs: Object::new(HolLight::Bool),
            eq_obs: Object::new(HolLight::Eq),
            true_obs: Object::new(HolLight::True),
            false_obs: Object::new(HolLight::False),
            imp_obs: Object::new(HolLight::Imp),
            not_obs: Object::new(HolLight::Not),
            and_obs: Object::new(HolLight::And),
            or_obs: Object::new(HolLight::Or),
            iff_obs: Object::new(HolLight::Iff),
            forall_obs: Object::new(HolLight::Forall),
            exists_obs: Object::new(HolLight::Exists),
            select_obs: Object::new(HolLight::Select),
        }
    }

    // ---- HOL types ----

    /// The HOL `bool` type — `TyConObs(bool_obs, "bool", [])`.
    pub fn bool_type(&self) -> Type {
        Type::tycon_obs_from_dyn(self.bool_obs.clone(), "bool", vec![])
    }

    /// The HOL function type `α → β` — same as Pure's, no HOL-specific
    /// constructor needed.
    pub fn fun_type(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    // ---- HOL constants (term-level Obs leaves at appropriate types) ----

    fn obs_term(&self, observer: &Object, ty: Type) -> Term {
        Term::obs_from_dyn(observer.clone(), ty)
    }

    /// HOL `=` instantiated at `α → α → bool`.
    pub fn eq_at(&self, alpha: Type) -> Term {
        let ty = Type::fun(
            alpha.clone(),
            Type::fun(alpha, self.bool_type()),
        );
        self.obs_term(&self.eq_obs, ty)
    }

    /// `t = u : bool`, given `t` and `u` of the same type α. Asserts
    /// the equality at α via the cached `=` observer.
    pub fn mk_eq(&self, lhs: Term, rhs: Term) -> Result<Term, covalence_pure::Error> {
        let alpha = lhs.type_of()?;
        let eq = self.eq_at(alpha);
        Ok(Term::app(Term::app(eq, lhs), rhs))
    }

    /// HOL `T : bool`.
    pub fn t(&self) -> Term {
        self.obs_term(&self.true_obs, self.bool_type())
    }

    /// HOL `F : bool`.
    pub fn f(&self) -> Term {
        self.obs_term(&self.false_obs, self.bool_type())
    }

    /// HOL `==>` at `bool → bool → bool`.
    pub fn imp_op(&self) -> Term {
        let b = self.bool_type();
        let ty = Type::fun(b.clone(), Type::fun(b.clone(), b));
        self.obs_term(&self.imp_obs, ty)
    }

    /// HOL `p ==> q`.
    pub fn mk_imp(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.imp_op(), p), q)
    }

    /// HOL `~` at `bool → bool`.
    pub fn not_op(&self) -> Term {
        let b = self.bool_type();
        let ty = Type::fun(b.clone(), b);
        self.obs_term(&self.not_obs, ty)
    }

    /// HOL `~p`.
    pub fn mk_not(&self, p: Term) -> Term {
        Term::app(self.not_op(), p)
    }

    /// HOL `/\` at `bool → bool → bool`.
    pub fn and_op(&self) -> Term {
        let b = self.bool_type();
        let ty = Type::fun(b.clone(), Type::fun(b.clone(), b));
        self.obs_term(&self.and_obs, ty)
    }

    /// HOL `p /\ q`.
    pub fn mk_and(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.and_op(), p), q)
    }

    /// HOL `\/` at `bool → bool → bool`.
    pub fn or_op(&self) -> Term {
        let b = self.bool_type();
        let ty = Type::fun(b.clone(), Type::fun(b.clone(), b));
        self.obs_term(&self.or_obs, ty)
    }

    /// HOL `p \/ q`.
    pub fn mk_or(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.or_op(), p), q)
    }

    /// HOL `<=>` at `bool → bool → bool`.
    pub fn iff_op(&self) -> Term {
        let b = self.bool_type();
        let ty = Type::fun(b.clone(), Type::fun(b.clone(), b));
        self.obs_term(&self.iff_obs, ty)
    }

    /// HOL `p <=> q`.
    pub fn mk_iff(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.iff_op(), p), q)
    }

    /// HOL `∀` at `(α → bool) → bool`.
    pub fn forall_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        let ty = Type::fun(pred, self.bool_type());
        self.obs_term(&self.forall_obs, ty)
    }

    /// HOL `∀x:α. body` — encoded as `Forall (λx:α. body)`.
    pub fn mk_forall(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.forall_at(alpha), lambda)
    }

    /// HOL `∃` at `(α → bool) → bool`.
    pub fn exists_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        let ty = Type::fun(pred, self.bool_type());
        self.obs_term(&self.exists_obs, ty)
    }

    /// HOL `∃x:α. body` — encoded as `Exists (λx:α. body)`.
    pub fn mk_exists(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.exists_at(alpha), lambda)
    }

    /// HOL `ε` at `(α → bool) → α`.
    pub fn select_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha.clone(), self.bool_type());
        let ty = Type::fun(pred, alpha);
        self.obs_term(&self.select_obs, ty)
    }

    /// HOL `ε x:α. body` — `Select (λx:α. body)`.
    pub fn mk_select(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let lambda = Term::abs(hint, alpha.clone(), body);
        Term::app(self.select_at(alpha), lambda)
    }

    // ---- Trueprop coercion (process-global, via lazy static) ----

    /// HOL `Trueprop` at type `bool → prop` — the explicit coercion
    /// from HOL bool to Pure prop. A HOL theorem `⊢_HOL p` (p : bool)
    /// is internally the Pure theorem `⊢_Pure Trueprop p` — and this
    /// is exactly what [`Thm::obs_true::<HolLight>`] produces.
    ///
    /// The `Trueprop` observer is a process-global lazy static
    /// (`TRUEPROP_OBS`); this method just returns a `Term::obs` over
    /// it at the right Pure type.
    pub fn trueprop(&self) -> Term {
        Term::obs_from_dyn(
            (*TRUEPROP_OBS).clone(),
            Type::fun(self.bool_type(), Type::prop()),
        )
    }

    /// `Trueprop p` — wrap a HOL bool term as a Pure prop. Returns an
    /// error if `p` is not bool-typed.
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

    /// Pointer-id of the `Trueprop` observer (process-global).
    pub fn trueprop_obs_ptr_id(&self) -> usize {
        TRUEPROP_OBS.ptr_id()
    }

    // ---- Identity check helpers (Arc pointer comparison via ptr_id) ----

    fn term_obs_ptr_id(t: &Term) -> Option<usize> {
        match t.kind() {
            TermKind::Obs(o, _) => Some(o.ptr_id()),
            _ => None,
        }
    }

    /// `true` iff `t` is the HOL `True` of *this* context (Arc identity).
    pub fn is_true(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(self.true_obs.ptr_id())
    }

    /// `true` iff `t` is the HOL `False` of *this* context.
    pub fn is_false(&self, t: &Term) -> bool {
        Self::term_obs_ptr_id(t) == Some(self.false_obs.ptr_id())
    }

    /// Pointer-id of the `Eq` observer — useful for downstream
    /// inspection of `Eq` applications.
    pub fn eq_obs_ptr_id(&self) -> usize {
        self.eq_obs.ptr_id()
    }
}

impl Default for HolLightCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// Marker trait certifying that an observer is in the [`HolLight`]
/// family. Used as a generic bound so `Thm::obs_eq::<HolLight>` can
/// be called explicitly when threading HOL-specific reasoning.
pub trait IsHolLight: Observer {}
impl IsHolLight for HolLight {}

// ============================================================================
// ObsTrue policy — direct HOL truth (zero hypotheses)
// ============================================================================

/// `ObsTrue` policy for HolLight: declares unconditionally-true
/// HOL propositions. Two cases:
///
/// - **HOL refl**: `Trueprop (Eq a a)` for any term a (structural).
/// - **HOL beta**: `Trueprop (Eq ((λx. body) operand) (body[x:=operand]))`
///   structural β-reduction.
impl ObsTrue for HolLight {
    fn obs_true(&self, args: &[Term], _hint: Option<&dyn covalence_pure::Hint>) -> bool {
        if !matches!(self, HolLight::Trueprop) || args.len() != 1 {
            return false;
        }
        let concl_body = &args[0];
        if check_refl_pattern(concl_body) {
            return true;
        }
        if check_beta_pattern(concl_body) {
            return true;
        }
        false
    }
}

/// HOL refl: `Trueprop (Eq a a)`.
fn check_refl_pattern(concl_body: &Term) -> bool {
    decompose_hol_eq(concl_body)
        .map(|(a, b)| a == b)
        .unwrap_or(false)
}

/// HOL beta: `Eq ((λx. body) operand) (open body operand)`.
fn check_beta_pattern(concl_body: &Term) -> bool {
    let Some((lhs, rhs)) = decompose_hol_eq(concl_body) else {
        return false;
    };
    let TermKind::App(f, operand) = lhs.kind() else {
        return false;
    };
    let TermKind::Abs(_h, _ty, body) = f.kind() else {
        return false;
    };
    covalence_pure::subst::open(body, operand) == rhs
}

// ============================================================================
// ObsImp policy — lazy HOL Light derivation rules
// ============================================================================

/// `ObsImp` policy for HolLight. Mints lazy theorems of the form
/// `⊢ hyp[0] ⟹ … ⟹ hyp[n] ⟹ Trueprop (concl)`.
///
/// The shapes recognised are the standard HOL Light rules. Each is
/// a structural pattern over `(concl_args, hyps)`; the policy
/// returns true iff the pattern matches:
///
/// **HOL sym** (1 hyp): hyp=`Trueprop (Eq a b)`, concl=`Trueprop (Eq b a)`.
/// **HOL trans** (2 hyps): hyps=`Trueprop (Eq a b)`, `Trueprop (Eq b c)`,
///   concl=`Trueprop (Eq a c)`.
/// **HOL MK_COMB** (2 hyps): hyps=`Trueprop (Eq f g)`, `Trueprop (Eq x y)`,
///   concl=`Trueprop (Eq (App f x) (App g y))`.
/// **HOL EQ_MP** at bool (2 hyps): hyps=`Trueprop (Eq p q)`, `Trueprop p`,
///   concl=`Trueprop q`.
///
/// More rules (ABS, BETA, INST, INST_TYPE, DEDUCT_ANTISYM) can be
/// added as additional pattern arms — each is local and only adds
/// LoC, never risks unsoundness.
impl ObsImp for HolLight {
    fn obs_imp(
        &self,
        args: &[Term],
        hyps: &[Term],
        hint: Option<&dyn covalence_pure::Hint>,
    ) -> bool {
        // The only HolLight variant we mint lazy theorems for is
        // `Trueprop p` — i.e., a prop-typed obs application.
        if !matches!(self, HolLight::Trueprop) || args.len() != 1 {
            return false;
        }
        let concl_body = &args[0];

        match hyps.len() {
            1 => {
                check_sym_pattern(&hyps[0], concl_body)
                    || check_abs_pattern(&hyps[0], concl_body)
                    || check_inst_pattern(&hyps[0], concl_body, hint)
                    || check_inst_type_pattern(&hyps[0], concl_body, hint)
            }
            2 => {
                check_trans_pattern(&hyps[0], &hyps[1], concl_body)
                    || check_mk_comb_pattern(&hyps[0], &hyps[1], concl_body)
                    || check_eq_mp_pattern(&hyps[0], &hyps[1], concl_body)
            }
            _ => false,
        }
    }
}

/// HOL INST: hyp = `Trueprop p`, concl = `Trueprop p[subs]` for
/// hint-supplied term-variable substitutions.
fn check_inst_pattern(
    hyp: &Term,
    concl_body: &Term,
    hint: Option<&dyn covalence_pure::Hint>,
) -> bool {
    let Some(h) = hint else {
        return false;
    };
    let Some(inst_hint) = h.as_any().downcast_ref::<InstHint>() else {
        return false;
    };
    let Some(h_body) = unwrap_trueprop(hyp) else {
        return false;
    };
    // Apply each substitution in order.
    let mut current = h_body;
    for (var_name, replacement) in &inst_hint.subs {
        current = subst::subst_free(&current, var_name, replacement);
    }
    &current == concl_body
}

/// HOL INST_TYPE: hyp = `Trueprop p`, concl = `Trueprop p[T-subs]`
/// for hint-supplied type-variable substitutions.
fn check_inst_type_pattern(
    hyp: &Term,
    concl_body: &Term,
    hint: Option<&dyn covalence_pure::Hint>,
) -> bool {
    let Some(h) = hint else {
        return false;
    };
    let Some(inst_hint) = h.as_any().downcast_ref::<InstTypeHint>() else {
        return false;
    };
    let Some(h_body) = unwrap_trueprop(hyp) else {
        return false;
    };
    let mut current = h_body;
    for (tvar_name, replacement_ty) in &inst_hint.subs {
        current = subst::subst_tfree_in_term(&current, tvar_name, replacement_ty);
    }
    &current == concl_body
}

/// HOL ABS: hyp = `Trueprop (Eq s t)`, concl = `Eq (λx. s') (λx. t')`
/// where `open s' (Free x) = s` and `open t' (Free x) = t`. We use
/// the lambda's hint as the free-var name (Hint is α-transparent in
/// Pure, so the choice of binder name doesn't affect equality).
fn check_abs_pattern(hyp: &Term, concl_body: &Term) -> bool {
    let Some(h_body) = unwrap_trueprop(hyp) else {
        return false;
    };
    let (Some((s, t)), Some((lhs, rhs))) =
        (decompose_hol_eq(&h_body), decompose_hol_eq(concl_body))
    else {
        return false;
    };
    let (TermKind::Abs(h1, ty1, b1), TermKind::Abs(_h2, ty2, b2)) = (lhs.kind(), rhs.kind())
    else {
        return false;
    };
    if ty1 != ty2 {
        return false;
    }
    let var = Term::free(h1.as_str(), ty1.clone());
    covalence_pure::subst::open(b1, &var) == s
        && covalence_pure::subst::open(b2, &var) == t
}

/// HOL sym: hyp = `Trueprop (Eq a b)`, concl = `Eq b a`.
fn check_sym_pattern(hyp: &Term, concl_body: &Term) -> bool {
    let Some(hyp_body) = unwrap_trueprop(hyp) else {
        return false;
    };
    let (Some((a, b)), Some((b2, a2))) = (
        decompose_hol_eq(&hyp_body),
        decompose_hol_eq(concl_body),
    ) else {
        return false;
    };
    a == a2 && b == b2
}

/// HOL trans: hyp1 = `Trueprop (Eq a b)`, hyp2 = `Trueprop (Eq b c)`,
/// concl = `Eq a c`.
fn check_trans_pattern(hyp1: &Term, hyp2: &Term, concl_body: &Term) -> bool {
    let (Some(h1), Some(h2)) = (unwrap_trueprop(hyp1), unwrap_trueprop(hyp2)) else {
        return false;
    };
    let (Some((a, b1)), Some((b2, c)), Some((wa, wc))) = (
        decompose_hol_eq(&h1),
        decompose_hol_eq(&h2),
        decompose_hol_eq(concl_body),
    ) else {
        return false;
    };
    b1 == b2 && a == wa && c == wc
}

/// HOL MK_COMB: hyp1 = `Trueprop (Eq f g)`, hyp2 = `Trueprop (Eq x y)`,
/// concl = `Eq (App f x) (App g y)`.
fn check_mk_comb_pattern(hyp1: &Term, hyp2: &Term, concl_body: &Term) -> bool {
    let (Some(h1), Some(h2)) = (unwrap_trueprop(hyp1), unwrap_trueprop(hyp2)) else {
        return false;
    };
    let (Some((f, g)), Some((x, y)), Some((lhs, rhs))) = (
        decompose_hol_eq(&h1),
        decompose_hol_eq(&h2),
        decompose_hol_eq(concl_body),
    ) else {
        return false;
    };
    // lhs == App(f, x), rhs == App(g, y)
    let (TermKind::App(lf, lx), TermKind::App(rf, rx)) = (lhs.kind(), rhs.kind()) else {
        return false;
    };
    *lf == f && *lx == x && *rf == g && *rx == y
}

/// HOL EQ_MP at bool: hyp1 = `Trueprop (Eq p q)`, hyp2 = `Trueprop p`,
/// concl = `q`.
fn check_eq_mp_pattern(hyp1: &Term, hyp2: &Term, concl_body: &Term) -> bool {
    let (Some(h1), Some(h2_body)) = (unwrap_trueprop(hyp1), unwrap_trueprop(hyp2)) else {
        return false;
    };
    let Some((p, q)) = decompose_hol_eq(&h1) else {
        return false;
    };
    p == h2_body && q == *concl_body
}

/// If `t` is `App(App(HolEq, a), b)` with the `HolLight::Eq` observer
/// at the head, return `Some((a, b))`.
fn decompose_hol_eq(t: &Term) -> Option<(Term, Term)> {
    let TermKind::App(outer_fn, outer_arg) = t.kind() else {
        return None;
    };
    let TermKind::App(inner_fn, inner_arg) = outer_fn.kind() else {
        return None;
    };
    let TermKind::Obs(obs, _) = inner_fn.kind() else {
        return None;
    };
    obs.downcast::<HolLight>()
        .filter(|o| matches!(o, HolLight::Eq))?;
    Some((inner_arg.clone(), outer_arg.clone()))
}

/// If `t` is `App(Trueprop, body)` with the `HolLight::Trueprop`
/// observer at the head, return `Some(body)`.
fn unwrap_trueprop(t: &Term) -> Option<Term> {
    let TermKind::App(f, body) = t.kind() else {
        return None;
    };
    let TermKind::Obs(obs, _) = f.kind() else {
        return None;
    };
    obs.downcast::<HolLight>()
        .filter(|o| matches!(o, HolLight::Trueprop))?;
    Some(body.clone())
}

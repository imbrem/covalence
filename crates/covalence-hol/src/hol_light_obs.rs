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

use std::fmt;

use covalence_pure::{Object, ObsEq, Observer, Term, TermKind, Type};

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
        _hint: Option<&dyn std::any::Any>,
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
